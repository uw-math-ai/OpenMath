"""Phase 4a+: LLM-assisted reference extraction (redesigned prompt).

For each formal statement, sends:
- Target: full LaTeX body + full proof
- Catalog: named entities as one-liners; unnamed entities with body only

This gives DeepSeek focused information without overwhelming context.

Usage:
    python -m pipeline.extract_references_llm                    # Dry run
    python -m pipeline.extract_references_llm --run-api          # Full run
    python -m pipeline.extract_references_llm --run-api --limit 5
    python -m pipeline.extract_references_llm --run-api --resume
    python -m pipeline.extract_references_llm --dry-run          # Cost estimate
"""
from __future__ import annotations

import argparse
import json
import os
import re
import time
from pathlib import Path

from pipeline.config import RAW_TEXT_DIR

try:
    from dotenv import load_dotenv
    load_dotenv(RAW_TEXT_DIR.parent / ".env")
except ImportError:
    pass


# ── Prompt (documented in deepseek_prompts.md) ─────────────────────────

SYSTEM_PROMPT = """\
You are a mathematical dependency analyzer for a Lean 4 formalization \
project. Given a target theorem, definition, or lemma along with a catalog \
of available prior definitions and theorems, identify which ones are \
directly used or required to understand or prove the target.\
"""

USER_PROMPT = """\
# Target: {kind} {number}{name_suffix}

{full_latex}

# Catalog of available definitions and theorems

{catalog}

# Instructions

Identify the MINIMAL set of dependencies directly used by the target above. \
Be strict and conservative — include ONLY entities that are:
- Explicitly cited by name or number in the target
- Required to state the target (concepts appearing in the statement body)
- Required to prove the target (results used in the proof)

Do NOT include:
- The target itself
- Entities that merely discuss similar or related concepts
- Entities from the same subsection unless the target explicitly uses them
- Background material or general context

Most theorems have 0-5 direct dependencies. If you list more than 10, \
you are probably being too permissive.

Reply with ONLY a JSON array of IDs, e.g., ["def:110A", "thm:142C"].
If no dependencies, reply with: []
"""


# ── Helpers ────────────────────────────────────────────────────────────

def _make_id(kind: str, number: str) -> str:
    prefix = {"theorem": "thm", "definition": "def", "lemma": "lem", "corollary": "cor"}
    return f"{prefix.get(kind, kind[:3])}:{number}"


def _strip_proof(latex: str, kind: str) -> str:
    """Remove \\begin{proof}...\\end{proof} from a LaTeX block."""
    return re.sub(
        r"\\begin\{proof\}.*?\\end\{proof\}",
        "",
        latex,
        flags=re.DOTALL,
    ).strip()


def _extract_body_no_proof(latex: str, kind: str) -> str:
    """Get just the \\begin{kind}...\\end{kind} part without any proof."""
    m = re.search(
        r"\\begin\{" + re.escape(kind) + r"\}(?:\[[^\]]*\])?.*?\\end\{" + re.escape(kind) + r"\}",
        latex,
        re.DOTALL,
    )
    if m:
        return m.group(0)
    return _strip_proof(latex, kind)


def _build_catalog(
    target_id: str,
    statements: list[dict],
    latex_map: dict[str, str],
    names_map: dict[str, str],
) -> str:
    """Build the catalog of available entities.

    - Named entities: one-liner with ID, name, and concepts introduced
    - Unnamed entities: one-liner + full LaTeX body (no proof)
    """
    lines = []

    for stmt in statements:
        sid = _make_id(stmt["kind"], stmt["number"])
        if sid == target_id:
            continue

        name = names_map.get(f"{stmt['kind']}:{stmt['number']}", "")
        introduces = stmt.get("introduces", []) or []

        # Decide: named vs unnamed
        # "Named" means it has a meaningful name OR introduces concepts
        is_named = bool(name) or bool(introduces)

        if introduces:
            # Has introduced concepts — most concise form
            concept_str = ", ".join(f'"{c}"' for c in introduces[:3])
            lines.append(f"- {sid}: introduces {concept_str}")
        elif is_named:
            # Named but no concepts introduced
            lines.append(f"- {sid}: {name}")
        else:
            # Unnamed — include body (without proof)
            latex = latex_map.get(sid, "")
            if latex:
                body = _extract_body_no_proof(latex, stmt["kind"])
                # Truncate long bodies
                if len(body) > 500:
                    body = body[:500] + "..."
                lines.append(f"- {sid}:")
                lines.append(body)
            else:
                lines.append(f"- {sid}: (no content available)")

    return "\n".join(lines)


def call_deepseek(prompt: str, api_key: str) -> str:
    from openai import OpenAI
    client = OpenAI(api_key=api_key, base_url="https://api.deepseek.com")
    response = client.chat.completions.create(
        model="deepseek-chat",
        messages=[
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": prompt},
        ],
        temperature=0.1,
        max_tokens=500,
    )
    return response.choices[0].message.content


def parse_llm_response(response: str, source_id: str, known_ids: set[str]) -> list[dict]:
    """Parse the LLM response into edge dicts."""
    edges = []
    m = re.search(r"\[([^\]]*)\]", response)
    if not m:
        return edges
    try:
        ids = json.loads("[" + m.group(1) + "]")
    except json.JSONDecodeError:
        return edges

    for target_id in ids:
        target_id = str(target_id).strip()
        if target_id in known_ids and target_id != source_id:
            edges.append({
                "source": source_id,
                "target": target_id,
                "edge_type": "llm_dependency",
                "context": "LLM-identified",
            })
    return edges


def build_prompt(
    stmt: dict,
    latex_map: dict[str, str],
    names_map: dict[str, str],
    all_statements: list[dict],
) -> str:
    """Build the full user prompt for a target statement."""
    target_key = f"{stmt['kind']}:{stmt['number']}"
    target_id = _make_id(stmt["kind"], stmt["number"])
    name = names_map.get(target_key, "")
    name_suffix = f": {name}" if name else ""
    full_latex = latex_map.get(target_id, "")
    if not full_latex:
        # Fallback to raw text if no LaTeX
        full_latex = stmt.get("text", "")
        if stmt.get("proof_text"):
            full_latex += "\n\nProof:\n" + stmt["proof_text"]

    catalog = _build_catalog(target_id, all_statements, latex_map, names_map)

    return USER_PROMPT.format(
        kind=stmt["kind"],
        number=stmt["number"],
        name_suffix=name_suffix,
        full_latex=full_latex,
        catalog=catalog,
    )


# ── Main ───────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(
        description="LLM-assisted reference extraction"
    )
    parser.add_argument("--run-api", action="store_true")
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    print("Phase 4a+: LLM-assisted reference extraction (new prompt design) ...")

    # Load data
    with open(RAW_TEXT_DIR / "formal_statements.json") as f:
        statements = json.load(f)

    # Build latex map keyed by statement id (thm:101A)
    latex_map: dict[str, str] = {}
    with open(RAW_TEXT_DIR / "formal_statements_latex.json") as f:
        for s in json.load(f):
            if s.get("latex_status") == "completed" and s.get("latex"):
                sid = _make_id(s["kind"], s["number"])
                latex_map[sid] = s["latex"]

    # Names map keyed by "kind:number" (e.g., "theorem:101A")
    names_map: dict[str, str] = {}
    names_path = RAW_TEXT_DIR / "statement_names.json"
    if names_path.exists():
        with open(names_path) as f:
            names_map = json.load(f)

    known_ids = {_make_id(s["kind"], s["number"]) for s in statements}

    # Dry-run: estimate size
    if args.dry_run:
        sample_prompt = build_prompt(statements[0], latex_map, names_map, statements)
        est_chars = len(sample_prompt) * len(statements)
        est_tokens = est_chars / 4
        cost = (est_tokens / 1e6) * 0.27 + (est_tokens * 0.05 / 1e6) * 1.10
        print(f"  Statements: {len(statements)}")
        print(f"  Sample prompt size: {len(sample_prompt):,} chars")
        print(f"  Est. total tokens: {int(est_tokens):,}")
        print(f"  Est. cost: ${cost:.3f}")
        return

    if not args.run_api:
        print("  Use --run-api to call DeepSeek, --dry-run for cost estimate")
        return

    api_key = os.getenv("DEEPSEEK_API_KEY")
    if not api_key:
        print("  ERROR: DEEPSEEK_API_KEY not set")
        return

    # Load existing if resuming
    out_path = RAW_TEXT_DIR / "references_llm.json"
    existing_edges: list[dict] = []
    processed_ids: set[str] = set()
    if args.resume and out_path.exists():
        with open(out_path) as f:
            existing_edges = json.load(f)
        processed_ids = {e["source"] for e in existing_edges}
        print(f"  Resuming: {len(processed_ids)} already processed")

    to_process = statements[:args.limit] if args.limit else statements
    all_edges = list(existing_edges)

    for idx, stmt in enumerate(to_process):
        source_id = _make_id(stmt["kind"], stmt["number"])
        if source_id in processed_ids:
            continue

        prompt = build_prompt(stmt, latex_map, names_map, statements)

        print(f"  [{idx+1}/{len(to_process)}] {stmt['kind']} {stmt['number']} ...", end="", flush=True)

        try:
            response = call_deepseek(prompt, api_key)
            edges = parse_llm_response(response, source_id, known_ids)
            all_edges.extend(edges)
            print(f" {len(edges)} deps found")
        except Exception as e:
            print(f" ERROR: {e}")

        # Save incrementally
        out_path.write_text(
            json.dumps(all_edges, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )
        time.sleep(0.3)

    # Merge with regex/concept edges
    print("\n  Merging with references.json ...")
    with open(RAW_TEXT_DIR / "references.json") as f:
        regex_edges = json.load(f)

    existing_pairs = {(e["source"], e["target"]) for e in regex_edges}
    new_llm_edges = [e for e in all_edges if (e["source"], e["target"]) not in existing_pairs]

    merged = regex_edges + new_llm_edges
    merged_path = RAW_TEXT_DIR / "references_merged.json"
    merged_path.write_text(json.dumps(merged, indent=2, ensure_ascii=False), encoding="utf-8")

    print(f"  Regex edges: {len(regex_edges)}")
    print(f"  New LLM edges: {len(new_llm_edges)}")
    print(f"  Total merged: {len(merged)}")
    print(f"  Wrote {merged_path}")


if __name__ == "__main__":
    main()
