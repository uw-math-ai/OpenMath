#!/usr/bin/env python3
"""
Judge Lean 4 formalizations against natural-language statements using
DeepSeek V4 Pro via the Token Factory API (OpenAI-compatible).

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

RUBRIC_VERSION = "1.2"
MODELS = ["deepseek-ai/DeepSeek-V4-Pro"]

DEFAULT_BASE_URL = "https://api.tokenfactory.nebius.com/v1"
DEFAULT_INPUT = Path("extraction/theorem_mapping.json")
DEFAULT_OUTPUT = Path("extraction/scores.jsonl")

SYSTEM_PROMPT = """\
You are a judge evaluating the faithfulness of a Lean 4 formalization to a \
natural-language mathematical statement from J. C. Butcher's \
"Numerical Methods for Ordinary Differential Equations".

Before assigning a score, you MUST first answer two yes/no questions:

  Q1.  Does the Lean statement IMPLY the natural-language statement?
       That is: if the Lean theorem holds, does the textbook statement \
       follow as a logical consequence?  (Lean → NL)
  Q2.  Does the natural-language statement IMPLY the Lean statement?
       That is: if the textbook statement is true, does the Lean theorem \
       follow as a logical consequence?  (NL → Lean)

The score is then determined by this table:

  Q1=true  AND Q2=true    →  SCORE 3 (VERBATIM, logically equivalent)
  Q1=true  AND Q2=false   →  SCORE 2 (GENERALIZATION — Lean is strictly stronger)
  Q1=false                →  SCORE 1 (Lean does not capture the textbook),
                              UNLESS the case-split exception below applies.

CASE-SPLIT EXCEPTION:
If the LEAN 4 STATEMENT contains MULTIPLE concatenated declaration headers \
(e.g., two `theorem` keywords) that together form a case split of the \
textbook theorem — for example, separate theorems for x < 0 and x ≥ 0 \
covering NL's "for all x" — answer Q1 and Q2 for the LOGICAL UNION of the \
declarations rather than for any single one.
  - If the union covers the full textbook domain and Q1 holds for the union → \
    SCORE 3 (verbatim by case split).
  - If the union covers a proper subset of NL's domain (some cases are still \
    missing) and the cases shown are themselves faithful — SCORE 2 (PARTIAL \
    CASE-SPLIT COVERAGE). This is the ONLY way to reach SCORE 2 when Q1 is \
    false for the union.

IMPLICIT-CONTEXT EXCEPTION:
The user message may include a SURROUNDING CONTEXT block — the textbook \
prose immediately preceding the statement. When the natural-language \
statement is incomplete on its own and the context carries hypotheses, treat \
the relevant context as part of the natural-language hypotheses for Q1 and Q2. \
A Lean version that makes implicit context-hypotheses explicit (e.g., taking \
a Hamiltonian or a Lipschitz function as a hypothesis) should NOT cause Q2 \
to become false on that account — Lean must be explicit where the textbook \
is implicit.

COMMON MISTAKES TO AVOID (each of these is SCORE 1, NOT SCORE 2):
- Adding a hypothesis in Lean does NOT make Lean stronger; it makes Lean \
  WEAKER. Q1 is FALSE, Q2 is TRUE. → SCORE 1.
- Restricting a parameter in Lean (e.g., Lean proves only N=2 of an \
  N-dimensional textbook theorem) makes Lean WEAKER, not a generalization. \
  Q1 is FALSE for the full NL domain. → SCORE 1.
- Lean stating the conclusion with a different constant, different sum \
  structure, or different bound formula is NOT a generalization unless \
  Lean's bound is strictly tighter. → SCORE 1.
- A single Lean declaration missing a conjunct of the textbook (e.g., NL = \
  "exists ∧ unique", Lean only proves existence) is SCORE 1 — the case-split \
  exception requires MULTIPLE concatenated declarations.

Respond with ONLY valid JSON and nothing else:
{
  "lean_implies_nl": <true|false>,
  "nl_implies_lean": <true|false>,
  "score": <1, 2, or 3>,
  "reason": "<10 words or fewer>"
}
"""

CONTEXT_CHAR_CAP = 2000


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


def _truncate(s: str, cap: int) -> str:
    s = s.strip()
    if len(s) <= cap:
        return s
    return s[:cap].rstrip() + " […truncated]"


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
        parts += ["", f"PREAMBLE (short NL summary): {entry['preamble']}"]
    if entry.get("variables"):
        parts += ["", f"VARIABLES: {json.dumps(entry['variables'], ensure_ascii=False)}"]
    ctx = entry.get("context_latex")
    if ctx and ctx.strip():
        parts += [
            "",
            "SURROUNDING CONTEXT (textbook prose immediately before this statement;",
            "may carry hypotheses, may be background — apply per rubric instructions):",
            _truncate(ctx, CONTEXT_CHAR_CAP),
        ]
    return "\n".join(parts)


def count_existing_runs(output_path: Path) -> dict[str, int]:
    """Map entity id -> number of records already written for it."""
    counts: dict[str, int] = {}
    if not output_path.exists():
        return counts
    with output_path.open() as f:
        for line in f:
            line = line.strip()
            if line:
                try:
                    eid = json.loads(line)["id"]
                    counts[eid] = counts.get(eid, 0) + 1
                except (json.JSONDecodeError, KeyError):
                    pass
    return counts


def compute_averages(output_path: Path) -> dict[str, tuple[float, int]]:
    """For each id with at least one numeric score, return (mean, n)."""
    buckets: dict[str, list[int]] = {}
    if not output_path.exists():
        return {}
    with output_path.open() as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
            except json.JSONDecodeError:
                continue
            score = rec.get("score")
            if isinstance(score, int):
                buckets.setdefault(rec["id"], []).append(score)
    return {eid: (sum(s) / len(s), len(s)) for eid, s in buckets.items()}


def judge_entry(
    client: OpenAI,
    model: str,
    entry_id: str,
    entry: dict,
    temperature: float,
    run_idx: int,
) -> dict:
    user_msg = build_user_message(entry_id, entry)
    response = client.chat.completions.create(
        model=model,
        messages=[
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": user_msg},
        ],
        temperature=temperature,
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
        lean_implies_nl = data.get("lean_implies_nl")
        nl_implies_lean = data.get("nl_implies_lean")
    except Exception as exc:
        score = None
        reason = f"parse error: {exc}"[:120]
        lean_implies_nl = None
        nl_implies_lean = None

    return {
        "id": entry_id,
        "run": run_idx,
        "score": score,
        "lean_implies_nl": lean_implies_nl,
        "nl_implies_lean": nl_implies_lean,
        "reason": reason,
        "model": model,
        "temperature": temperature,
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
    parser.add_argument(
        "--runs", type=int, default=3,
        help="Independent judging runs per entry (default: 3)"
    )
    parser.add_argument(
        "--temperature", type=float, default=0.5,
        help="Sampling temperature for the judge (default: 0.5)"
    )
    parser.add_argument(
        "--ids", type=str, default=None,
        help="Optional comma-separated allowlist of entity ids to score"
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
    existing_runs = count_existing_runs(args.output)

    id_allowlist: set[str] | None = None
    if args.ids:
        id_allowlist = {s.strip() for s in args.ids.split(",") if s.strip()}

    entries = [
        (eid, e)
        for eid, e in sorted(mapping.items())
        if e.get("lean_statement") and (id_allowlist is None or eid in id_allowlist)
    ]
    if args.limit:
        entries = entries[: args.limit]

    todo: list[tuple[str, dict, int]] = []
    for eid, entry in entries:
        n_existing = existing_runs.get(eid, 0)
        for run_idx in range(n_existing, args.runs):
            todo.append((eid, entry, run_idx))

    fully_scored = sum(
        1 for eid, _ in entries if existing_runs.get(eid, 0) >= args.runs
    )
    print(f"Entries with lean_statement : {len(entries)}")
    print(f"Fully scored ({args.runs} runs)        : {fully_scored}")
    print(f"Records to write this run  : {len(todo)}")
    print(f"Base URL                   : {base_url}")
    print(f"Model                      : {MODELS[0]}")
    print(f"Temperature                : {args.temperature}")
    print(f"Runs per entry             : {args.runs}")
    print()

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("a") as out:
        for i, (eid, entry, run_idx) in enumerate(todo):
            model = MODELS[i % len(MODELS)]
            print(
                f"[{i+1:3d}/{len(todo)}] {eid:<20s} run={run_idx} {model} ...",
                end=" ", flush=True,
            )
            try:
                record = judge_entry(
                    client, model, eid, entry, args.temperature, run_idx
                )
                out.write(json.dumps(record, ensure_ascii=False) + "\n")
                out.flush()
                imp = f"L→NL={record['lean_implies_nl']} NL→L={record['nl_implies_lean']}"
                print(f"score={record['score']}  ({imp})  {record['reason']}")
            except Exception as exc:
                print(f"ERROR: {exc}")
                out.write(json.dumps({
                    "id": eid,
                    "run": run_idx,
                    "score": None,
                    "lean_implies_nl": None,
                    "nl_implies_lean": None,
                    "reason": f"api error: {str(exc)[:80]}",
                    "model": model,
                    "temperature": args.temperature,
                    "rubric_version": RUBRIC_VERSION,
                    "timestamp": datetime.now(timezone.utc).isoformat(),
                    "full_response": None,
                }, ensure_ascii=False) + "\n")
                out.flush()
            time.sleep(0.5)

    final_counts = count_existing_runs(args.output)
    print(f"\nDone. {sum(final_counts.values())} total records in {args.output}")

    averages = compute_averages(args.output)
    target_ids = [eid for eid, _ in entries]
    relevant = {eid: averages[eid] for eid in target_ids if eid in averages}
    if relevant:
        print(f"\nAverages over {args.runs} runs (numeric scores only):")
        for eid in sorted(relevant):
            avg, n = relevant[eid]
            print(f"  {eid:<20s} avg={avg:.2f}  n={n}")


if __name__ == "__main__":
    main()
