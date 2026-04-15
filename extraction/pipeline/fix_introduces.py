"""Fix the 'introduces' field on formal statements.

Two-method approach:
1. Method A (zero cost): Parse \\emph{} and \\textit{} from LaTeX bodies
2. Method B (DeepSeek): For definitions still missing introduces, ask the LLM

Usage:
    python -m pipeline.fix_introduces                  # Method A only
    python -m pipeline.fix_introduces --run-api        # Method A + B
    python -m pipeline.fix_introduces --run-api --limit 3  # Test
    python -m pipeline.fix_introduces --dry-run        # Cost estimate
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


# ── DeepSeek prompt (documented in deepseek_prompts.md) ────────────────

SYSTEM_PROMPT = """\
You are a mathematical terminology extractor. Given a definition or theorem \
from a numerical methods textbook, identify the named concepts or terms \
that it introduces or formally defines.\
"""

USER_PROMPT = """\
Below is {kind} {number} from Butcher's "Numerical Methods for ODEs":

{latex_body}

List the specific named concepts or terms that this {kind} introduces or \
formally defines. These are typically:
- Terms in single quotes ('term' or \u2018term\u2019)
- Terms in italic emphasis (\\emph{{term}} or \\textit{{term}})
- Proper names introduced by phrases like "is called X", "is said to be X", \
"we define X", "is symplectic", "is L-stable"

Do NOT include:
- General mathematical objects used but not defined (variables like f, y, A)
- Named theorems or references to other results
- Generic descriptive words (method, property, condition)
- Words that are used but not being defined here

Return a JSON array of strings. If none, return [].
Example: ["Lipschitz condition", "Lipschitz constant"]
"""


# ── Method A: LaTeX emphasis parsing ───────────────────────────────────

def _extract_body(latex: str, kind: str) -> str:
    """Extract body text between \\begin{kind} and \\end{kind} (excluding proof)."""
    m = re.search(
        r"\\begin\{" + re.escape(kind) + r"\}(?:\[[^\]]*\])?(.*?)\\end\{" + re.escape(kind) + r"\}",
        latex,
        re.DOTALL,
    )
    return m.group(1) if m else ""


def _extract_emphasis(latex_body: str) -> list[str]:
    """Extract terms from \\emph{...} and \\textit{...}."""
    terms = []
    for pattern in [r"\\emph\{([^}]+)\}", r"\\textit\{([^}]+)\}"]:
        for m in re.finditer(pattern, latex_body):
            term = m.group(1).strip()
            # Filter out math-like single tokens (e.g., \mathbb{R})
            if re.search(r"\\math|\\R|\\N|\\C|\\Z", term):
                continue
            # Strip LaTeX dashes
            term = term.replace("--", "\u2013")
            if 2 < len(term) < 80:
                terms.append(term)
    return terms


def method_a(stmt: dict, latex: str) -> list[str]:
    """Extract concepts using LaTeX emphasis markers."""
    body = _extract_body(latex, stmt["kind"])
    return _extract_emphasis(body)


# ── Method B: DeepSeek ─────────────────────────────────────────────────

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
        max_tokens=300,
    )
    return response.choices[0].message.content


def method_b(stmt: dict, latex: str, api_key: str) -> list[str]:
    """Use DeepSeek to extract concepts."""
    body = _extract_body(latex, stmt["kind"]) or stmt.get("text", "")
    prompt = USER_PROMPT.format(
        kind=stmt["kind"],
        number=stmt["number"],
        latex_body=body[:1500],
    )
    response = call_deepseek(prompt, api_key)
    try:
        # Extract JSON array from response
        m = re.search(r"\[([^\]]*)\]", response)
        if m:
            arr = json.loads("[" + m.group(1) + "]")
            return [str(x) for x in arr if x and len(str(x)) < 80]
    except json.JSONDecodeError:
        pass
    return []


# ── Deduplication ──────────────────────────────────────────────────────

def _dedupe(concepts: list[str]) -> list[str]:
    """Remove duplicates preserving order, case-insensitive."""
    seen = set()
    result = []
    for c in concepts:
        c = c.strip()
        if not c:
            continue
        key = c.lower()
        if key not in seen:
            seen.add(key)
            result.append(c)
    return result


# ── Main ───────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(description="Fix 'introduces' field on statements")
    parser.add_argument("--run-api", action="store_true",
                        help="Use DeepSeek for statements missing introduces")
    parser.add_argument("--limit", type=int, default=None,
                        help="Only process first N statements needing DeepSeek")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    print("Fixing 'introduces' field ...")

    stmts_path = RAW_TEXT_DIR / "formal_statements.json"
    latex_path = RAW_TEXT_DIR / "formal_statements_latex.json"

    with open(stmts_path) as f:
        statements = json.load(f)
    with open(latex_path) as f:
        latex_stmts = json.load(f)

    # Build latex map
    latex_map = {f"{s['kind']}:{s['number']}": s.get("latex", "") or ""
                 for s in latex_stmts}

    # Method A: LaTeX emphasis parsing
    method_a_added = 0
    for stmt in statements:
        key = f"{stmt['kind']}:{stmt['number']}"
        latex = latex_map.get(key, "")
        if not latex:
            continue
        existing = stmt.get("introduces", []) or []
        new_terms = method_a(stmt, latex)
        if new_terms:
            merged = _dedupe(existing + new_terms)
            if len(merged) > len(existing):
                method_a_added += len(merged) - len(existing)
            stmt["introduces"] = merged

    # Method B candidates: definitions still missing introduces
    method_b_candidates = [
        s for s in statements
        if s["kind"] == "definition" and not s.get("introduces")
    ]

    print(f"  Method A added {method_a_added} concepts via LaTeX emphasis")
    print(f"  Method B candidates: {len(method_b_candidates)} definitions")

    if args.dry_run:
        est_tokens = len(method_b_candidates) * 800
        cost = (est_tokens / 1e6) * 0.27 + (est_tokens * 0.2 / 1e6) * 1.10
        print(f"  Est. cost for Method B: ${cost:.4f}")
        return

    # Method B: DeepSeek for remaining
    if args.run_api:
        api_key = os.getenv("DEEPSEEK_API_KEY")
        if not api_key:
            print("  ERROR: DEEPSEEK_API_KEY not set")
            return

        to_process = method_b_candidates[:args.limit] if args.limit else method_b_candidates
        method_b_added = 0
        for idx, stmt in enumerate(to_process):
            key = f"{stmt['kind']}:{stmt['number']}"
            latex = latex_map.get(key, "")
            print(f"  [{idx+1}/{len(to_process)}] {key} ...", end="", flush=True)
            try:
                concepts = method_b(stmt, latex, api_key)
                stmt["introduces"] = _dedupe(concepts)
                method_b_added += len(concepts)
                print(f" OK: {concepts}")
            except Exception as e:
                print(f" ERROR: {e}")
            time.sleep(0.3)

        print(f"\n  Method B added concepts for {method_b_added} statements")

    # Save updated statements
    stmts_path.write_text(
        json.dumps(statements, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )

    # Final summary
    with_introduces = sum(1 for s in statements if s.get("introduces"))
    total_concepts = sum(len(s.get("introduces", [])) for s in statements)
    print(f"\n  Final: {with_introduces}/{len(statements)} statements have introduces")
    print(f"  Total concepts: {total_concepts}")
    print(f"  Saved to {stmts_path}")


if __name__ == "__main__":
    main()
