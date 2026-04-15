"""Phase 2b: Extract informal names for formal statements.

3-tier resolution:
1. Tier 1 — In-text names: use `introduces` field for definitions
2. Tier 2 — Subsection title: for statements that are the primary
   formal statement in their subsection
3. Tier 3 — DeepSeek inference: for remaining statements

Usage:
    python -m pipeline.extract_names                      # Tiers 1+2 only
    python -m pipeline.extract_names --run-api            # All 3 tiers
    python -m pipeline.extract_names --run-api --limit 5  # Test
    python -m pipeline.extract_names --run-api --resume   # Resume
    python -m pipeline.extract_names --dry-run            # Cost estimate
"""
from __future__ import annotations

import argparse
import json
import os
import time
from pathlib import Path
from collections import Counter

from pipeline.config import RAW_TEXT_DIR, SUBSECTION_TITLES

try:
    from dotenv import load_dotenv
    load_dotenv(RAW_TEXT_DIR.parent / ".env")
except ImportError:
    pass


# ── DeepSeek prompt (documented in deepseek_prompts.md) ────────────────

SYSTEM_PROMPT = """\
You are a mathematical terminology expert. Given a formal statement from \
a numerical methods textbook, propose a concise descriptive name.\
"""

USER_PROMPT = """\
Propose a short descriptive name (3-8 words) for this {kind} from Butcher's \
"Numerical Methods for ODEs". The name should capture the main result or \
concept, not restate the number.

**Subsection**: {subsection_title}

**{KIND} {number}**:
{statement_text}

Examples of good names:
- "Global truncation error bound"
- "Convergence iff consistency and stability"
- "Dahlquist equivalence theorem"
- "Existence and uniqueness of solutions"

Respond with ONLY the name, no punctuation, no quotes, no "Theorem" prefix.
"""


def call_deepseek(prompt: str, api_key: str) -> str:
    from openai import OpenAI
    client = OpenAI(api_key=api_key, base_url="https://api.deepseek.com")
    response = client.chat.completions.create(
        model="deepseek-chat",
        messages=[
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": prompt},
        ],
        temperature=0.3,  # slightly creative for naming
        max_tokens=100,
    )
    return response.choices[0].message.content.strip().strip('"').strip("'")


# ── Tier 1: In-text names ──────────────────────────────────────────────

def tier1_name(stmt: dict) -> str:
    """Extract name from the statement's `introduces` field (definitions only)."""
    if stmt.get("introduces"):
        # Pick the primary concept (usually the first, longest, most specific)
        concepts = stmt["introduces"]
        # Sort by length descending, take the longest as the primary concept
        primary = max(concepts, key=len)
        return primary
    return ""


# ── Tier 2: Subsection title ───────────────────────────────────────────

def tier2_name(stmt: dict, statements: list[dict]) -> str:
    """Use subsection title if this statement is primary in its subsection.

    A statement is 'primary' if it's the only formal statement in its
    subsection, or if it's the first theorem/definition of its subsection.
    """
    subsec_num = stmt["number"][:3]
    try:
        subsec_int = int(subsec_num)
    except ValueError:
        return ""

    title = SUBSECTION_TITLES.get(subsec_int, "")
    if not title:
        return ""

    # Find all statements in this subsection
    same_subsec = [s for s in statements if s["number"][:3] == subsec_num]

    # Use subsection title if:
    # (a) this is the only statement, OR
    # (b) this is the first statement (number ends in 'A')
    if len(same_subsec) == 1:
        return title
    if stmt["number"].endswith("A"):
        return title

    return ""


# ── Tier 3: DeepSeek inference ─────────────────────────────────────────

def tier3_name(stmt: dict, api_key: str) -> str:
    subsec_num = int(stmt["number"][:3])
    subsec_title = SUBSECTION_TITLES.get(subsec_num, "")
    prompt = USER_PROMPT.format(
        kind=stmt["kind"],
        KIND=stmt["kind"].upper(),
        number=stmt["number"],
        subsection_title=subsec_title or "(unknown)",
        statement_text=stmt["text"][:800],
    )
    return call_deepseek(prompt, api_key)


# ── Main ───────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(description="Extract names for formal statements")
    parser.add_argument("--run-api", action="store_true",
                        help="Use DeepSeek for Tier 3 inference")
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    print("Phase 2b: Extracting statement names ...")

    stmts_path = RAW_TEXT_DIR / "formal_statements.json"
    with open(stmts_path) as f:
        statements = json.load(f)

    # Load existing names if resuming
    names_path = RAW_TEXT_DIR / "statement_names.json"
    existing_names: dict[str, str] = {}
    if args.resume and names_path.exists():
        with open(names_path) as f:
            existing_names = json.load(f)
        print(f"  Resuming: {len(existing_names)} already named")

    # Apply tiers 1 and 2 (always, no API cost)
    names: dict[str, str] = dict(existing_names)
    tier1_count = 0
    tier2_count = 0
    tier3_needed = []

    for stmt in statements:
        key = f"{stmt['kind']}:{stmt['number']}"
        if key in names:
            continue

        # Tier 1
        name = tier1_name(stmt)
        if name:
            names[key] = name
            tier1_count += 1
            continue

        # Tier 2
        name = tier2_name(stmt, statements)
        if name:
            names[key] = name
            tier2_count += 1
            continue

        # Need Tier 3
        tier3_needed.append(stmt)

    print(f"  Tier 1 (in-text): {tier1_count} names")
    print(f"  Tier 2 (subsection): {tier2_count} names")
    print(f"  Tier 3 needed: {len(tier3_needed)} statements")

    if args.dry_run:
        est_tokens = len(tier3_needed) * 800
        cost = (est_tokens / 1e6) * 0.27 + (est_tokens * 0.05 / 1e6) * 1.10
        print(f"  Est. cost for Tier 3: ${cost:.3f}")
        return

    # Save tiers 1+2
    names_path.write_text(json.dumps(names, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"  Saved {len(names)} names to {names_path}")

    # Tier 3 (if requested)
    if args.run_api:
        api_key = os.getenv("DEEPSEEK_API_KEY")
        if not api_key:
            print("  ERROR: DEEPSEEK_API_KEY not set")
            return

        to_process = tier3_needed[:args.limit] if args.limit else tier3_needed

        for idx, stmt in enumerate(to_process):
            key = f"{stmt['kind']}:{stmt['number']}"
            print(f"  [{idx+1}/{len(to_process)}] {key} ...", end="", flush=True)
            try:
                name = tier3_name(stmt, api_key)
                names[key] = name
                print(f" OK: {name!r}")
            except Exception as e:
                print(f" ERROR: {e}")
                names[key] = ""

            # Save incrementally
            names_path.write_text(json.dumps(names, indent=2, ensure_ascii=False), encoding="utf-8")
            time.sleep(0.3)

        with_name = sum(1 for v in names.values() if v)
        print(f"\n  Final: {with_name}/{len(statements)} named")


if __name__ == "__main__":
    main()
