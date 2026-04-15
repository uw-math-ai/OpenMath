"""Phase 6: LLM-assisted LaTeX conversion of formal statements.

Uses DeepSeek API (OpenAI-compatible) to convert extracted formal
statement text from ASCII math to proper LaTeX.

Usage:
    python -m pipeline.convert_to_latex              # Prepare prompts only (no API calls)
    python -m pipeline.convert_to_latex --run-api     # Run full conversion
    python -m pipeline.convert_to_latex --run-api --limit 5   # Test with 5 statements
    python -m pipeline.convert_to_latex --run-api --resume    # Resume interrupted run
    python -m pipeline.convert_to_latex --dry-run     # Estimate cost without calling API
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path

from pipeline.config import RAW_TEXT_DIR

# Load .env if python-dotenv is available
try:
    from dotenv import load_dotenv
    load_dotenv(RAW_TEXT_DIR.parent / ".env")
except ImportError:
    pass


SYSTEM_PROMPT = """\
You are a mathematical typesetting expert specializing in numerical analysis. \
Your task is to convert text extracted from a PDF into clean LaTeX.\
"""

USER_PROMPT_TEMPLATE = """\
Convert the following {kind} statement (numbered {number}) from a numerical \
methods textbook into proper LaTeX. The text was extracted via pdftotext and \
contains ASCII representations of mathematical notation.

Rules:
1. Wrap the statement in the appropriate LaTeX environment \
(\\begin{{{kind}}} ... \\end{{{kind}}})
2. Convert all math to LaTeX: Greek letters, subscripts, superscripts, \
fractions, norms, integrals, summations, matrices, etc.
3. Use $...$ for inline math and \\[...\\] or equation environments for display math
4. Preserve the exact mathematical content — do not simplify or add content
5. Convert references: "Theorem 101A" -> Theorem~\\ref{{thm:101A}}, \
"(100a)" -> \\eqref{{eq:100a}}
6. Output ONLY the LaTeX code, no explanations or markdown fences

Statement text:
---
{text}
---
{proof_section}"""


def build_prompt(statement: dict) -> str:
    """Build the conversion prompt for a single statement."""
    proof_section = ""
    if statement.get("proof_text"):
        proof_section = (
            "\nAlso convert the following proof:\n---\n"
            + statement["proof_text"]
            + "\n---"
        )

    return USER_PROMPT_TEMPLATE.format(
        kind=statement["kind"],
        number=statement["number"],
        text=statement["text"],
        proof_section=proof_section,
    )


def call_deepseek(prompt: str, api_key: str, model: str = "deepseek-chat") -> str:
    """Call DeepSeek API and return the response text."""
    from openai import OpenAI

    client = OpenAI(
        api_key=api_key,
        base_url="https://api.deepseek.com",
    )

    response = client.chat.completions.create(
        model=model,
        messages=[
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": prompt},
        ],
        temperature=0.1,  # Low temperature for faithful conversion
        max_tokens=4096,
    )

    return response.choices[0].message.content


def estimate_cost(statements: list[dict]) -> None:
    """Estimate API cost for converting all statements."""
    total_input_chars = 0
    for s in statements:
        prompt = build_prompt(s)
        total_input_chars += len(prompt)

    # Rough token estimate: ~4 chars per token
    input_tokens = total_input_chars / 4
    # Assume output ~= input size
    output_tokens = input_tokens * 0.8

    # DeepSeek-chat pricing (as of 2025): $0.27/M input, $1.10/M output
    input_cost = (input_tokens / 1_000_000) * 0.27
    output_cost = (output_tokens / 1_000_000) * 1.10
    total_cost = input_cost + output_cost

    print(f"\n  Cost estimate (deepseek-chat):")
    print(f"    Statements: {len(statements)}")
    print(f"    Est. input tokens:  {int(input_tokens):,}")
    print(f"    Est. output tokens: {int(output_tokens):,}")
    print(f"    Est. cost: ${total_cost:.4f}")


def run_conversion(
    statements: list[dict],
    api_key: str,
    limit: int | None = None,
    resume: bool = False,
) -> list[dict]:
    """Run the API conversion for all (or a subset of) statements."""
    # Load existing results if resuming
    out_path = RAW_TEXT_DIR / "formal_statements_latex.json"
    existing: dict[str, dict] = {}
    if resume and out_path.exists():
        with open(out_path, encoding="utf-8") as f:
            for item in json.load(f):
                if item.get("latex_status") == "completed":
                    key = f"{item['kind']}:{item['number']}"
                    existing[key] = item
        print(f"  Resuming: {len(existing)} already completed")

    results = []
    to_process = statements[:limit] if limit else statements
    total = len(to_process)

    for idx, stmt in enumerate(to_process):
        key = f"{stmt['kind']}:{stmt['number']}"

        # Skip if already completed (resume mode)
        if key in existing:
            results.append(existing[key])
            continue

        prompt = build_prompt(stmt)

        print(f"  [{idx + 1}/{total}] Converting {stmt['kind']} {stmt['number']} ...", end="", flush=True)

        try:
            latex = call_deepseek(prompt, api_key)
            stmt["latex"] = latex
            stmt["latex_status"] = "completed"
            print(f" OK ({len(latex)} chars)")
        except Exception as e:
            stmt["latex"] = None
            stmt["latex_status"] = f"error: {e}"
            print(f" ERROR: {e}")

        # Remove prompt from output to save space
        stmt.pop("latex_prompt", None)
        results.append(stmt)

        # Save incrementally (so --resume works if interrupted)
        out_path.write_text(
            json.dumps(results, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )

        # Rate limiting: small delay between calls
        time.sleep(0.3)

    return results


def prepare_prompts(statements: list[dict]) -> list[dict]:
    """Prepare prompts without calling the API."""
    for s in statements:
        s["latex"] = None
        s["latex_prompt"] = build_prompt(s)
        s["latex_status"] = "pending"
    return statements


# ── Main ───────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Convert formal statements to LaTeX using DeepSeek API"
    )
    parser.add_argument(
        "--run-api", action="store_true",
        help="Actually call the DeepSeek API (default: prepare prompts only)",
    )
    parser.add_argument(
        "--resume", action="store_true",
        help="Resume from where a previous run left off",
    )
    parser.add_argument(
        "--limit", type=int, default=None,
        help="Only process the first N statements (for testing)",
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="Estimate cost without making API calls",
    )
    parser.add_argument(
        "--model", type=str, default="deepseek-chat",
        help="DeepSeek model to use (default: deepseek-chat)",
    )
    args = parser.parse_args()

    print("Phase 6: LLM-assisted LaTeX conversion ...")

    # Load formal statements
    with open(RAW_TEXT_DIR / "formal_statements.json", encoding="utf-8") as f:
        statements = json.load(f)

    print(f"  Loaded {len(statements)} statements")

    if args.dry_run:
        estimate_cost(statements)
        return

    if args.run_api:
        api_key = os.getenv("DEEPSEEK_API_KEY")
        if not api_key:
            print("  ERROR: DEEPSEEK_API_KEY not set.")
            print("  Set it in .env or export DEEPSEEK_API_KEY=sk-...")
            sys.exit(1)

        print(f"  Model: {args.model}")
        if args.limit:
            print(f"  Limit: {args.limit} statements")
        if args.resume:
            print(f"  Resume mode: ON")

        estimate_cost(statements[:args.limit] if args.limit else statements)
        print()

        results = run_conversion(
            statements,
            api_key,
            limit=args.limit,
            resume=args.resume,
        )

        completed = sum(1 for r in results if r.get("latex_status") == "completed")
        errors = sum(1 for r in results if r.get("latex_status", "").startswith("error"))
        print(f"\n  Completed: {completed}, Errors: {errors}")

    else:
        print("  Preparing prompts only (use --run-api to call DeepSeek)")
        results = prepare_prompts(statements)

    out_path = RAW_TEXT_DIR / "formal_statements_latex.json"
    out_path.write_text(
        json.dumps(results, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )
    print(f"  Wrote {out_path}")


if __name__ == "__main__":
    main()
