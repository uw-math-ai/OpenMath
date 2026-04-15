"""Phase 3b: Extract equation context and missing variable definitions.

For each formal statement, identifies:
1. Equations referenced but defined elsewhere — extracts their content
2. Variables/functions used but defined in preceding text (via DeepSeek)

Usage:
    python -m pipeline.extract_context                    # Equations only
    python -m pipeline.extract_context --run-api          # + DeepSeek context
    python -m pipeline.extract_context --run-api --limit 5  # Test
    python -m pipeline.extract_context --dry-run          # Cost estimate
"""
from __future__ import annotations

import argparse
import json
import os
import re
import time
from pathlib import Path

from pipeline.config import RAW_TEXT_DIR, EQUATION_TAG_RE

try:
    from dotenv import load_dotenv
    load_dotenv(RAW_TEXT_DIR.parent / ".env")
except ImportError:
    pass


# ── Part 1: Equation context extraction ────────────────────────────────

def extract_equation_context() -> dict[str, dict]:
    """Extract the text content of each equation from chapter files.

    Returns {eq_tag: {chapter, subsection, text, context}}.
    """
    eq_map: dict[str, dict] = {}

    for ch in range(1, 6):
        filepath = RAW_TEXT_DIR / f"ch{ch:02d}.txt"
        if not filepath.exists():
            continue
        lines = filepath.read_text(encoding="utf-8").split("\n")

        for i, line in enumerate(lines):
            for m in EQUATION_TAG_RE.finditer(line):
                tag = m.group(1)
                if tag in eq_map:
                    continue  # Keep first occurrence (definition site)

                # Collect context: 3 lines before + this line + 1 line after
                start = max(0, i - 3)
                end = min(len(lines), i + 2)
                context_lines = lines[start:end]
                context = "\n".join(l.rstrip() for l in context_lines)

                # The equation text is typically on the line before the tag
                eq_text = ""
                for k in range(i - 1, max(i - 4, -1), -1):
                    stripped = lines[k].strip()
                    if stripped and not stripped.startswith("("):
                        eq_text = stripped
                        break

                eq_map[tag] = {
                    "tag": tag,
                    "chapter": ch,
                    "subsection": tag[:3],
                    "equation_text": eq_text,
                    "context": context,
                    "line": i + 1,
                }

    return eq_map


# ── Part 2: DeepSeek-assisted context extraction ──────────────────────

# Prompt documented in deepseek_prompts.md
SYSTEM_PROMPT = """\
You are a mathematical context analyzer for a formalization project. \
Your task is to identify what external context is needed to understand \
a formal statement from a textbook.\
"""

USER_PROMPT = """\
Below is a formal {kind} from Butcher's "Numerical Methods for ODEs", \
along with the text that precedes it in the same subsection.

**Preceding text (last ~1500 chars before the statement):**
{preceding_text}

**{KIND} {number}:**
{statement_text}

Identify what context from the preceding text is needed to fully \
understand this statement. Return a JSON object with:

1. "variables": a list of objects, each with "name" and "definition" \
   for variables/functions used in the statement but defined in the \
   preceding text. Example: {{"name": "f", "definition": "f : [a,b] × R^N → R^N"}}

2. "equations": a list of objects, each with "tag" and "content" for \
   equation tags like (100a) that are referenced in the statement and \
   defined in the preceding text. Example: {{"tag": "100a", "content": "y'(x) = f(x, y(x))"}}

3. "preamble": a concise 1-3 sentence summary of the setup/notation \
   from the preceding text that is essential for understanding the statement.

If the statement is self-contained and needs no external context, return:
{{"variables": [], "equations": [], "preamble": ""}}

Output ONLY valid JSON, no markdown fences, no explanations.
"""


def _get_preceding_text(chapter: int, line_start: int, max_chars: int = 1500) -> str:
    """Get text preceding a statement from the chapter file."""
    filepath = RAW_TEXT_DIR / f"ch{chapter:02d}.txt"
    if not filepath.exists():
        return ""
    lines = filepath.read_text(encoding="utf-8").split("\n")
    # Collect lines before the statement
    end = max(0, line_start - 1)
    collected = []
    total = 0
    for i in range(end - 1, -1, -1):
        line = lines[i].rstrip()
        collected.insert(0, line)
        total += len(line) + 1
        if total >= max_chars:
            break
    return "\n".join(collected)


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
        max_tokens=1000,
    )
    return response.choices[0].message.content


def extract_context_llm(
    statements: list[dict],
    api_key: str,
    limit: int | None = None,
    resume: bool = False,
) -> list[dict]:
    """Use DeepSeek to extract missing context for each statement."""
    out_path = RAW_TEXT_DIR / "statement_context.json"
    existing: dict[str, dict] = {}
    if resume and out_path.exists():
        with open(out_path) as f:
            for item in json.load(f):
                existing[item.get("number", "")] = item
        print(f"  Resuming: {len(existing)} already processed")

    results = list(existing.values())
    to_process = statements[:limit] if limit else statements

    for idx, stmt in enumerate(to_process):
        if stmt["number"] in existing:
            continue

        preceding = _get_preceding_text(stmt["chapter"], stmt["line_start"])
        prompt = USER_PROMPT.format(
            kind=stmt["kind"],
            KIND=stmt["kind"].upper(),
            number=stmt["number"],
            statement_text=stmt["text"][:1000],
            preceding_text=preceding,
        )

        print(f"  [{idx+1}/{len(to_process)}] {stmt['kind']} {stmt['number']} ...", end="", flush=True)

        try:
            response = call_deepseek(prompt, api_key)
            # Parse JSON from response
            context = json.loads(response)
            context["number"] = stmt["number"]
            context["kind"] = stmt["kind"]
            results.append(context)
            print(f" OK (vars={len(context.get('variables',[]))}, eqs={len(context.get('equations',[]))})")
        except Exception as e:
            results.append({
                "number": stmt["number"],
                "kind": stmt["kind"],
                "variables": [],
                "equations": [],
                "preamble": "",
                "error": str(e),
            })
            print(f" ERROR: {e}")

        # Save incrementally
        out_path.write_text(json.dumps(results, indent=2, ensure_ascii=False), encoding="utf-8")
        time.sleep(0.3)

    return results


# ── Main ───────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Extract equation context and missing variable definitions"
    )
    parser.add_argument("--run-api", action="store_true",
                        help="Use DeepSeek for variable/function context extraction")
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    print("Phase 3b: Extracting context ...")

    # Part 1: Equation context (always runs, no API needed)
    eq_map = extract_equation_context()
    eq_path = RAW_TEXT_DIR / "equations_context.json"
    eq_path.write_text(json.dumps(list(eq_map.values()), indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"  Equation context: {len(eq_map)} equations extracted")
    print(f"  Wrote {eq_path}")

    # Part 2: DeepSeek context extraction
    if args.dry_run:
        with open(RAW_TEXT_DIR / "formal_statements.json") as f:
            stmts = json.load(f)
        est_tokens = len(stmts) * 2000  # ~2000 tokens per prompt
        cost = (est_tokens / 1e6) * 0.27 + (est_tokens * 0.3 / 1e6) * 1.10
        print(f"\n  DeepSeek cost estimate:")
        print(f"    Statements: {len(stmts)}")
        print(f"    Est. tokens: {est_tokens:,}")
        print(f"    Est. cost: ${cost:.2f}")
        return

    if args.run_api:
        api_key = os.getenv("DEEPSEEK_API_KEY")
        if not api_key:
            print("  ERROR: DEEPSEEK_API_KEY not set")
            return

        with open(RAW_TEXT_DIR / "formal_statements.json") as f:
            stmts = json.load(f)

        results = extract_context_llm(stmts, api_key, args.limit, args.resume)

        with_vars = sum(1 for r in results if r.get("variables"))
        with_eqs = sum(1 for r in results if r.get("equations"))
        with_preamble = sum(1 for r in results if r.get("preamble"))
        print(f"\n  Results: {len(results)} statements")
        print(f"    With variables: {with_vars}")
        print(f"    With equations: {with_eqs}")
        print(f"    With preamble: {with_preamble}")


if __name__ == "__main__":
    main()
