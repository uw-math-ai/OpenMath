"""Convert extracted context (preamble, variables, equations) to LaTeX.

Uses DeepSeek to convert the raw text context into plasTeX-compatible LaTeX.

Usage:
    python -m pipeline.convert_context_to_latex --run-api
    python -m pipeline.convert_context_to_latex --run-api --limit 5
    python -m pipeline.convert_context_to_latex --run-api --resume
    python -m pipeline.convert_context_to_latex --dry-run
"""
from __future__ import annotations

import argparse
import json
import os
import time
from pathlib import Path

from pipeline.config import RAW_TEXT_DIR

try:
    from dotenv import load_dotenv
    load_dotenv(RAW_TEXT_DIR.parent / ".env")
except ImportError:
    pass


SYSTEM_PROMPT = "You are a mathematical typesetting expert."

USER_PROMPT = """\
Convert the following context block for {kind} {number} into LaTeX.

The context contains:
- A preamble describing the setup/notation
- Variables and their definitions
- Referenced equations with their content

STRICT CONSTRAINTS (for plasTeX compatibility):
1. Do NOT use tikzpicture, figure, table, tabular, algorithm, verbatim
2. Do NOT use \\hline, \\cline, or | in array column specs
3. Use simple array environments: \\begin{{array}}{{ccc}} (no pipes)
4. Use standard AMS math: equation, align, gather, cases, pmatrix, bmatrix
5. Keep output CONCISE — under 1500 characters
6. Format as a single block that can be inserted before a theorem environment
7. Use \\paragraph{{Context}} as the header
8. Output ONLY the LaTeX code, no explanations or markdown fences

Context to convert:
---
Preamble: {preamble}

Variables:
{variables}

Referenced equations:
{equations}
---"""


def _format_variables(variables: list[dict]) -> str:
    if not variables:
        return "(none)"
    lines = []
    for v in variables:
        lines.append(f"- {v.get('name', '?')}: {v.get('definition', '?')}")
    return "\n".join(lines)


def _format_equations(equations: list[dict]) -> str:
    if not equations:
        return "(none)"
    lines = []
    for eq in equations:
        lines.append(f"- ({eq.get('tag', '?')}): {eq.get('content', '?')}")
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
        max_tokens=2000,
    )
    return response.choices[0].message.content


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Convert extracted context to LaTeX using DeepSeek"
    )
    parser.add_argument("--run-api", action="store_true")
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    print("Converting context to LaTeX ...")

    ctx_path = RAW_TEXT_DIR / "statement_context.json"
    with open(ctx_path) as f:
        contexts = json.load(f)

    # Filter to non-empty contexts
    to_convert = [c for c in contexts
                  if c.get("preamble") or c.get("variables") or c.get("equations")]
    print(f"  Non-empty contexts: {len(to_convert)}/{len(contexts)}")

    if args.dry_run:
        est_tokens = len(to_convert) * 800
        cost = (est_tokens / 1e6) * 0.27 + (est_tokens * 0.5 / 1e6) * 1.10
        print(f"  Est. cost: ${cost:.2f}")
        return

    if not args.run_api:
        print("  Use --run-api to call DeepSeek")
        return

    api_key = os.getenv("DEEPSEEK_API_KEY")
    if not api_key:
        print("  ERROR: DEEPSEEK_API_KEY not set")
        return

    # Load existing results if resuming
    out_path = RAW_TEXT_DIR / "context_latex.json"
    existing: dict[str, str] = {}
    if args.resume and out_path.exists():
        with open(out_path) as f:
            existing = json.load(f)
        print(f"  Resuming: {len(existing)} already converted")

    if args.limit:
        to_convert = to_convert[:args.limit]

    for idx, ctx in enumerate(to_convert):
        key = f"{ctx['kind']}:{ctx['number']}"
        if key in existing:
            continue

        prompt = USER_PROMPT.format(
            kind=ctx["kind"],
            number=ctx["number"],
            preamble=ctx.get("preamble", "(none)"),
            variables=_format_variables(ctx.get("variables", [])),
            equations=_format_equations(ctx.get("equations", [])),
        )

        print(f"  [{idx+1}/{len(to_convert)}] {key} ...", end="", flush=True)

        try:
            latex = call_deepseek(prompt, api_key)
            existing[key] = latex
            print(f" OK ({len(latex)} chars)")
        except Exception as e:
            existing[key] = f"% Error: {e}"
            print(f" ERROR: {e}")

        # Save incrementally
        out_path.write_text(json.dumps(existing, indent=2, ensure_ascii=False), encoding="utf-8")
        time.sleep(0.3)

    print(f"\n  Converted: {len(existing)}")
    print(f"  Wrote {out_path}")


if __name__ == "__main__":
    main()
