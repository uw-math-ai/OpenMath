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

The user message may include a SURROUNDING CONTEXT block — the textbook \
prose immediately preceding the statement. Sometimes it carries hypotheses \
the statement references implicitly ("the function f", "the system", "the \
dynamics"); sometimes it is purely motivational. When the natural-language \
statement is incomplete without it, treat the relevant context as part of \
the natural-language hypotheses. If the Lean version makes those \
implicit context-hypotheses explicit (e.g., taking a Hamiltonian or a \
Lipschitz function as a hypothesis), do NOT penalize this as "extra \
hypothesis" — Lean must be explicit where the textbook is implicit. Only \
score down for hypotheses that are absent from BOTH the statement AND the \
surrounding context.

Respond with ONLY valid JSON and nothing else:
{"score": <1, 2, or 3>, "reason": "<10 words or fewer>"}
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
    except Exception as exc:
        score = None
        reason = f"parse error: {exc}"[:120]

    return {
        "id": entry_id,
        "run": run_idx,
        "score": score,
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
                print(f"score={record['score']}  {record['reason']}")
            except Exception as exc:
                print(f"ERROR: {exc}")
                out.write(json.dumps({
                    "id": eid,
                    "run": run_idx,
                    "score": None,
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
