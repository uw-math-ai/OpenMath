#!/usr/bin/env python3
"""
Judge Lean 4 formalizations against natural-language statements using two LLMs
via Token Factory API (OpenAI-compatible), alternating between Kimi 2.6 and DeepSeek-V4-Pro.

Usage:
    export TOKEN_FACTORY_API_KEY=<key>
    python extraction/judge_formalizations.py [--limit N] [--input PATH] [--output PATH]

Output: scores.jsonl — one JSON object per line, idempotent (reruns skip existing IDs).
"""

import argparse
import json
import os
import re
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

try:
    from openai import OpenAI
except ImportError:
    sys.exit("openai package not found. Install with: pip install openai")

RUBRIC_VERSION = "1.0"
MODELS = ["deepseek-ai/DeepSeek-V4-Pro"]

DEFAULT_BASE_URL = "https://api.tokenfactory.nebius.com/v1"
DEFAULT_INPUT = Path("extraction/theorem_mapping.json")
DEFAULT_OUTPUT = Path("extraction/scores.jsonl")

SYSTEM_PROMPT = """\
You are a judge evaluating the faithfulness of a Lean 4 formalization to a \
natural-language mathematical statement from J. C. Butcher's \
"Numerical Methods for Ordinary Differential Equations".

Score the Lean 4 statement against the natural-language original using this rubric:

SCORE 3 — VERBATIM: The Lean assertion is logically equivalent to the NL statement \
(each implies the other). Contrapositives, ε-δ vs. filter reformulations, and \
equivalent Mathlib idioms all count as 3. The Lean may use more abstract types \
(e.g., PseudoEMetricSpace instead of ℝ^N) as long as the NL statement is a direct \
specialization.

SCORE 2 — GENERALIZATION: The Lean is strictly stronger than the NL — Lean implies \
NL, but NL does not imply Lean. The generalization must be mathematically correct, \
and the NL must be recoverable by specializing the Lean (instantiating a type, \
restricting a domain, or adding back a hypothesis).

SCORE 1 — OTHER: Anything else, including:
- Strictly weaker (extra hypothesis in Lean, restricted domain, trivial disjunction \
in conclusion)
- Incomparable (neither direction implies the other)
- Vacuous (conclusion is trivially True or a tautology)
- Wrong object (e.g., function vs. relation, norm vs. semi-norm)
- Wrong Mathlib definition (similarly-named but mathematically non-equivalent)
- Statements false in the claimed setting

Respond with ONLY valid JSON and nothing else:
{"score": <1, 2, or 3>, "reason": "<10 words or fewer>"}
"""


def strip_outer_env(latex: str) -> str:
    s = latex.strip()
    s = re.sub(
        r"^\\begin\{(?:theorem|definition|lemma|corollary|proposition|remark|proof)[^}]*\}\s*",
        "", s, flags=re.IGNORECASE,
    )
    s = re.sub(
        r"\s*\\end\{(?:theorem|definition|lemma|corollary|proposition|remark|proof)\}\s*$",
        "", s, flags=re.IGNORECASE,
    )
    return s.strip()


def build_user_message(entry_id: str, entry: dict) -> str:
    nl = strip_outer_env(
        entry.get("statement_latex") or entry.get("statement_text") or ""
    )
    parts = [
        f"KIND: {entry.get('kind', 'unknown')}",
        f"NAME: {entry.get('name', entry_id)}",
        "",
        "NATURAL LANGUAGE (LaTeX):",
        nl,
        "",
        "LEAN 4 STATEMENT:",
        entry.get("lean_statement") or "(none)",
    ]
    if entry.get("preamble"):
        parts += ["", f"CONTEXT: {entry['preamble']}"]
    if entry.get("variables"):
        parts += ["", f"VARIABLES: {json.dumps(entry['variables'], ensure_ascii=False)}"]
    return "\n".join(parts)


def load_existing_ids(output_path: Path) -> set[str]:
    if not output_path.exists():
        return set()
    scored: set[str] = set()
    with output_path.open() as f:
        for line in f:
            line = line.strip()
            if line:
                try:
                    scored.add(json.loads(line)["id"])
                except (json.JSONDecodeError, KeyError):
                    pass
    return scored


def judge_entry(client: OpenAI, model: str, entry_id: str, entry: dict) -> dict:
    user_msg = build_user_message(entry_id, entry)
    response = client.chat.completions.create(
        model=model,
        messages=[
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": user_msg},
        ],
        temperature=0,
        max_tokens=512,
    )
    raw_text = response.choices[0].message.content or ""
    full_response = response.model_dump()

    try:
        # Try direct parse first, then strip markdown fences, then regex fallback
        text = raw_text.strip().removeprefix("```json").removeprefix("```").removesuffix("```").strip()
        try:
            data = json.loads(text)
        except json.JSONDecodeError:
            # Find the outermost {...} by tracking brace depth
            depth, start = 0, None
            for i, ch in enumerate(text):
                if ch == '{':
                    if depth == 0:
                        start = i
                    depth += 1
                elif ch == '}':
                    depth -= 1
                    if depth == 0 and start is not None:
                        data = json.loads(text[start:i+1])
                        break
            else:
                raise ValueError("no JSON object found")
        score = int(data["score"])
        if score not in (1, 2, 3):
            raise ValueError(f"score {score} out of range")
        reason = str(data.get("reason", ""))[:120]
    except Exception as exc:
        score = 1
        reason = f"parse error: {exc}"[:120]

    return {
        "id": entry_id,
        "score": score,
        "reason": reason,
        "model": model,
        "rubric_version": RUBRIC_VERSION,
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "full_response": full_response,
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Judge Lean 4 formalizations via Token Factory API"
    )
    parser.add_argument(
        "--limit", type=int, default=None,
        help="Score only the first N entries (for testing)"
    )
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    api_key = os.environ.get("TOKEN_FACTORY_API_KEY")
    if not api_key:
        sys.exit("TOKEN_FACTORY_API_KEY environment variable not set.")

    base_url = os.environ.get("TOKEN_FACTORY_BASE_URL", DEFAULT_BASE_URL)
    client = OpenAI(api_key=api_key, base_url=base_url)

    mapping: dict = json.loads(args.input.read_text())
    already_scored = load_existing_ids(args.output)

    entries = [
        (eid, e)
        for eid, e in sorted(mapping.items())
        if e.get("lean_statement")
    ]
    if args.limit:
        entries = entries[: args.limit]

    todo = [(eid, e) for eid, e in entries if eid not in already_scored]
    print(f"Entries with lean_statement : {len(entries)}")
    print(f"Already scored             : {len(already_scored)}")
    print(f"To score this run          : {len(todo)}")
    print(f"Base URL                   : {base_url}")
    print(f"Model rotation             : {MODELS}")
    print()

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("a") as out:
        for i, (eid, entry) in enumerate(todo):
            model = MODELS[i % len(MODELS)]
            print(f"[{i+1:3d}/{len(todo)}] {eid:<20s} {model} ...", end=" ", flush=True)
            try:
                record = judge_entry(client, model, eid, entry)
                out.write(json.dumps(record, ensure_ascii=False) + "\n")
                out.flush()
                print(f"score={record['score']}  {record['reason']}")
            except Exception as exc:
                print(f"ERROR: {exc}")
                out.write(json.dumps({
                    "id": eid,
                    "score": None,
                    "reason": f"api error: {str(exc)[:80]}",
                    "model": model,
                    "rubric_version": RUBRIC_VERSION,
                    "timestamp": datetime.now(timezone.utc).isoformat(),
                    "full_response": None,
                }, ensure_ascii=False) + "\n")
                out.flush()
            time.sleep(0.5)

    total = len(already_scored) + len(todo)
    print(f"\nDone. {total} total records in {args.output}")


if __name__ == "__main__":
    main()
