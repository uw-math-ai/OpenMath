#!/usr/bin/env python3
"""
Blind back-translation of Lean statements to natural language via the
Token Factory API (DeepSeek V4 Pro, OpenAI-compatible).

For each entry, the model is shown ONLY the Lean statement (plus its kind and
name) — never the textbook statement. It produces a faithful natural-language
rendering of what the Lean asserts. A human (or a follow-up judge) can then
compare this blind back-translation against the original textbook statement:
agreement  => the formalization is faithful;
divergence => the Lean says something materially different.

Usage:
    export TOKEN_FACTORY_API_KEY=<key>
    python extraction/back_translate.py [--input PATH] [--temperature T]

Appends `lean_back_translation` (and `lean_back_translation_model`) to each
entry in place. Idempotent: entries that already have a back-translation are
skipped, so reruns only fill gaps.

Supported input shapes:
  - audit_sample.json: a dict whose values include lists of entry dicts.
  - theorem_mapping.json: a flat dict mapping id -> entry dict.
"""

import argparse
import json
import os
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

try:
    from openai import OpenAI
except ImportError:
    sys.exit("openai package not found. Install with: pip install openai")

MODEL = "deepseek-ai/DeepSeek-V4-Pro"
DEFAULT_BASE_URL = "https://api.tokenfactory.nebius.com/v1"
DEFAULT_INPUT = Path("extraction/audit_sample.json")

SYSTEM_PROMPT = """\
You are a mathematician. You will be given a Lean 4 / Mathlib formal \
declaration (a definition, theorem, or lemma). Translate it into a clear, \
faithful natural-language mathematical statement, as it would appear in a \
textbook.

Rules:
- State the mathematics, NOT the Lean syntax. Do not mention Lean, Mathlib, \
or type-theoretic encodings (no "Filter.Tendsto", "ℝ≥0", etc. — write them \
as ordinary math).
- Be precise about every hypothesis, quantifier, and the conclusion. Do not \
drop or add hypotheses.
- For a definition, state what is being defined and the exact defining \
condition.
- For a theorem or lemma, state the hypotheses and the conclusion.
- You may use inline LaTeX math.
- Output ONLY the mathematical statement. No commentary, no preamble, and no \
explanation of your translation.
"""


def build_user_message(entry: dict) -> str:
    return "\n".join([
        f"KIND: {entry.get('kind', 'unknown')}",
        f"NAME: {entry.get('name', entry.get('id', 'unknown'))}",
        "",
        "LEAN 4 STATEMENT:",
        entry.get("lean_statement") or "(none)",
    ])


def collect_entries(data) -> list[dict]:
    """Return a list of entry dicts (by reference) regardless of file shape."""
    entries: list[dict] = []
    if isinstance(data, dict):
        list_values = [v for v in data.values() if isinstance(v, list)]
        if list_values:
            for lst in list_values:
                entries.extend(e for e in lst if isinstance(e, dict))
        else:
            entries.extend(
                v for v in data.values()
                if isinstance(v, dict) and v.get("lean_statement")
            )
    elif isinstance(data, list):
        entries.extend(e for e in data if isinstance(e, dict))
    return entries


def back_translate(client: OpenAI, entry: dict, temperature: float) -> str:
    response = client.chat.completions.create(
        model=MODEL,
        messages=[
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": build_user_message(entry)},
        ],
        temperature=temperature,
        max_tokens=600,
    )
    return (response.choices[0].message.content or "").strip()


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Blind back-translate Lean statements to natural language"
    )
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--temperature", type=float, default=0.0)
    parser.add_argument(
        "--force", action="store_true",
        help="Re-translate even entries that already have a back-translation"
    )
    args = parser.parse_args()

    api_key = os.environ.get("TOKEN_FACTORY_API_KEY")
    if not api_key:
        sys.exit("TOKEN_FACTORY_API_KEY environment variable not set.")

    base_url = os.environ.get("TOKEN_FACTORY_BASE_URL", DEFAULT_BASE_URL)
    client = OpenAI(api_key=api_key, base_url=base_url)

    data = json.loads(args.input.read_text(encoding="utf-8"))
    entries = collect_entries(data)

    todo = [
        e for e in entries
        if e.get("lean_statement")
        and (args.force or not e.get("lean_back_translation"))
    ]
    print(f"Entries total              : {len(entries)}")
    print(f"To back-translate this run : {len(todo)}")
    print(f"Model                      : {MODEL}")
    print(f"Temperature                : {args.temperature}")
    print()

    for i, entry in enumerate(todo):
        eid = entry.get("id", entry.get("name", "?"))
        print(f"[{i+1:3d}/{len(todo)}] {str(eid):<20s} ...", end=" ", flush=True)
        try:
            nl = back_translate(client, entry, args.temperature)
            entry["lean_back_translation"] = nl
            entry["lean_back_translation_model"] = MODEL
            # Persist after each call so an interruption keeps progress.
            args.input.write_text(
                json.dumps(data, indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
            preview = nl.replace("\n", " ")[:70]
            print(f"ok  {preview}")
        except Exception as exc:
            print(f"ERROR: {exc}")
            entry["lean_back_translation"] = None
            entry["lean_back_translation_error"] = str(exc)[:200]
            entry["lean_back_translation_at"] = datetime.now(timezone.utc).isoformat()
            args.input.write_text(
                json.dumps(data, indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
        time.sleep(0.5)

    print(f"\nDone. Updated {args.input}")


if __name__ == "__main__":
    main()
