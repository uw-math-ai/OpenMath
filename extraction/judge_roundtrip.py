#!/usr/bin/env python3
"""
Round-trip judge: score how well a Lean formalization preserves the textbook
statement, by comparing the textbook's natural-language statement against a
blind back-translation of the Lean (produced by back_translate.py).

Inspired by extraction/judge_formalizations.py (Lean vs NL). Differences:
  - Both inputs are natural language, so the judge does not have to read Lean.
  - The asymmetry is explicit: Q1 (back → NL) is the PRIMARY criterion. If
    back fails to imply NL, the Lean is not strong enough to prove the
    textbook claim — that is the failure mode we most care about. A
    back-translation that is strictly stronger than NL (Q1=true, Q2=false)
    is acceptable — that's a sound generalization on the Lean side.
  - Provider is OpenAI (default model: gpt-4o), to avoid correlated blind
    spots with the DeepSeek-driven back-translator.

Usage:
    export OPENAI_API_KEY=<key>
    python extraction/judge_roundtrip.py [--input PATH] [--runs N]
                                          [--temperature T] [--model M]
                                          [--ids id1,id2,...]

Output: extraction/roundtrip_scores.jsonl — one JSON object per (id, run).
Idempotent: a (id, run) already in the output file is not redone unless
--force is passed. --runs N tops up missing runs to N for each id.
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

RUBRIC_VERSION = "rt-1.0"
DEFAULT_MODEL = "gpt-4o"

DEFAULT_INPUT = Path("extraction/theorem_mapping.json")
DEFAULT_OUTPUT = Path("extraction/roundtrip_scores.jsonl")

CONTEXT_CHAR_CAP = 2000

SYSTEM_PROMPT = """\
You are a judge evaluating whether a formalization of a mathematical statement \
preserves the meaning of the original. You will be given the ORIGINAL textbook \
statement (in natural language) and a BACK-TRANSLATION: a natural-language \
rendering of how the same statement was formalized in Lean 4. The \
back-translation was produced blind — the translator saw ONLY the Lean code, \
never the textbook — so any agreement is evidence of faithful formalization \
and any divergence is evidence the Lean says something different.

Before assigning a score, you MUST first answer two yes/no questions:

  Q1.  Does the BACK-TRANSLATION imply the ORIGINAL?  (back → NL)
       That is: if the back-translated statement is true, does the textbook \
       statement follow as a logical consequence?
       --- THIS IS THE PRIMARY CRITERION. If Q1 is false, the Lean is not \
       strong enough to prove the textbook claim. ---
  Q2.  Does the ORIGINAL imply the BACK-TRANSLATION?  (NL → back)
       That is: if the textbook statement is true, does the back-translated \
       statement follow as a logical consequence?

The score is then determined by this table:

  Q1=true  AND Q2=true   →  SCORE 3 (FAITHFUL — back ⇔ NL)
  Q1=true  AND Q2=false  →  SCORE 2 (back is strictly stronger — Lean is a \
                              sound generalization or strengthening; \
                              acceptable for a formalization)
  Q1=false               →  SCORE 1 (back does NOT imply NL — Lean is \
                              missing hypotheses, missing content, or \
                              proves a different claim), UNLESS the \
                              case-split exception below applies.

CASE-SPLIT EXCEPTION:
If the BACK-TRANSLATION describes MULTIPLE distinct statements that together \
form a case split of the textbook theorem (e.g., the textbook says "for all \
x, P(x)" and the back-translation gives separate statements for x < 0 and \
x ≥ 0 covering all x; or "exists a unique y" split as existence + uniqueness \
clauses), answer Q1 and Q2 for the LOGICAL UNION of the back-translated parts.
  - If the union covers the entire textbook domain and Q1 holds for the union \
    → SCORE 3 (faithful via case split).
  - If the union covers only some cases (some are still missing) and the \
    cases shown are themselves faithful → SCORE 2 (PARTIAL CASE-SPLIT \
    COVERAGE). This is the ONLY way to reach SCORE 2 when Q1 is false for \
    the union.

IMPLICIT-CONTEXT EXCEPTION:
The user message includes a SURROUNDING CONTEXT block — the textbook prose \
immediately preceding the original statement. Sometimes the textbook leaves \
hypotheses IMPLICIT in this surrounding prose (e.g., "the system is in \
Hamiltonian form", "the function f is Lipschitz"). If the back-translation \
makes those implicit context-hypotheses EXPLICIT, do NOT count this as a \
failure of Q2 — the back-translation is being more precise about what the \
textbook already assumed. Only score down for hypotheses absent from BOTH \
the statement AND the surrounding context.

COMMON MISTAKES TO AVOID (each of these is SCORE 1, not SCORE 2):
- A back-translation that ADDS hypotheses absent from both the textbook \
  statement and its surrounding context makes the back-translation WEAKER \
  than the textbook. Q1 is FALSE in that case. → SCORE 1.
- A back-translation that RESTRICTS the textbook's domain (e.g., textbook \
  is for all N, back is for N=2 only; textbook is general, back covers only \
  n ∈ {1,…,7}) is WEAKER. Q1 is FALSE. → SCORE 1.
- A back-translation that uses a different formula / different constants / \
  a different bound in the conclusion is NOT a generalization unless its \
  formula strictly entails the textbook formula. → SCORE 1.
- Notation differences (LaTeX symbols, variable renames, formally equivalent \
  reformulations such as ε-δ vs filter language) are NOT score-down items. \
  Judge based on meaning, not form.
- A back-translation using more abstract types where the textbook uses a \
  concrete type (e.g., a general normed space where the textbook uses ℝⁿ) \
  is a sound generalization. Q1=true, Q2=false. → SCORE 2.

Respond with ONLY valid JSON and nothing else:
{
  "back_implies_nl": <true|false>,
  "nl_implies_back": <true|false>,
  "score": <1, 2, or 3>,
  "reason": "<20 words or fewer>"
}
"""


def strip_outer_env(latex: str) -> str:
    s = (latex or "").strip()
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
    s = (s or "").strip()
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
        "ORIGINAL TEXTBOOK STATEMENT:",
        nl,
        "",
        "BACK-TRANSLATION (blind NL rendering of the Lean formalization):",
        entry.get("lean_back_translation") or "(none)",
    ]
    if entry.get("preamble"):
        parts += ["", f"PREAMBLE (short NL summary): {entry['preamble']}"]
    ctx = entry.get("context_latex")
    if ctx and ctx.strip():
        parts += [
            "",
            "SURROUNDING CONTEXT (textbook prose immediately before this statement;",
            "hypotheses here can be IMPLICIT in the original — apply per rubric instructions):",
            _truncate(ctx, CONTEXT_CHAR_CAP),
        ]
    return "\n".join(parts)


def count_existing_runs(output_path: Path) -> dict[str, int]:
    counts: dict[str, int] = {}
    if not output_path.exists():
        return counts
    for line in output_path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            eid = json.loads(line)["id"]
            counts[eid] = counts.get(eid, 0) + 1
        except (json.JSONDecodeError, KeyError):
            pass
    return counts


def compute_averages(output_path: Path) -> dict[str, tuple[float, int]]:
    buckets: dict[str, list[int]] = {}
    if not output_path.exists():
        return {}
    for line in output_path.read_text(encoding="utf-8").splitlines():
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
    seed: int | None = None,
) -> dict:
    user_msg = build_user_message(entry_id, entry)
    # GPT-5+ uses `max_completion_tokens` and only accepts temperature=1.
    is_gpt5 = model.startswith("gpt-5")
    # gpt-5+ are reasoning models — internal reasoning consumes completion
    # tokens, so the limit must be generous. Older models output ~60 tokens
    # of JSON so 512 is plenty.
    token_kwarg = (
        {"max_completion_tokens": 4096}
        if is_gpt5
        else {"max_tokens": 512}
    )
    effective_temp = 1.0 if is_gpt5 else temperature
    kwargs: dict = {
        "model": model,
        "messages": [
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": user_msg},
        ],
        "temperature": effective_temp,
        **token_kwarg,
    }
    if seed is not None:
        kwargs["seed"] = seed
    response = client.chat.completions.create(**kwargs)
    raw = (response.choices[0].message.content or "").strip()
    full = response.model_dump()

    score: int | None = None
    reason = ""
    back_implies_nl = None
    nl_implies_back = None
    try:
        text = raw.removeprefix("```json").removeprefix("```").removesuffix("```").strip()
        try:
            data = json.loads(text)
        except json.JSONDecodeError:
            depth, start = 0, None
            for i, ch in enumerate(text):
                if ch == '{':
                    if depth == 0:
                        start = i
                    depth += 1
                elif ch == '}':
                    depth -= 1
                    if depth == 0 and start is not None:
                        data = json.loads(text[start:i + 1])
                        break
            else:
                raise ValueError("no JSON object found")
        score = int(data["score"])
        if score not in (1, 2, 3):
            raise ValueError(f"score {score} out of range")
        reason = str(data.get("reason", ""))[:200]
        back_implies_nl = data.get("back_implies_nl")
        nl_implies_back = data.get("nl_implies_back")
    except Exception as exc:
        score = None
        reason = f"parse error: {exc}"[:200]

    return {
        "id": entry_id,
        "run": run_idx,
        "score": score,
        "back_implies_nl": back_implies_nl,
        "nl_implies_back": nl_implies_back,
        "reason": reason,
        "model": model,
        "temperature": temperature,
        "rubric_version": RUBRIC_VERSION,
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "full_response": full,
    }


def collect_entries(data) -> list[tuple[str, dict]]:
    """Return (id, entry) pairs from either an audit-sample-shaped JSON
    (dict containing lists of entry dicts) or a theorem_mapping.json shape
    (flat id -> entry dict)."""
    out: list[tuple[str, dict]] = []
    if isinstance(data, dict):
        list_values = [v for v in data.values() if isinstance(v, list)]
        if list_values:
            for lst in list_values:
                for e in lst:
                    if isinstance(e, dict):
                        eid = e.get("id") or e.get("name") or "?"
                        out.append((eid, e))
        else:
            for eid, e in sorted(data.items()):
                if isinstance(e, dict):
                    out.append((eid, e))
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Judge back-translation faithfulness against textbook NL"
    )
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--model", type=str, default=DEFAULT_MODEL)
    parser.add_argument(
        "--runs", type=int, default=1,
        help="Independent judging runs per entry (default: 1)"
    )
    parser.add_argument(
        "--temperature", type=float, default=0.0,
        help="Sampling temperature (default: 0.0 for reproducibility)"
    )
    parser.add_argument(
        "--ids", type=str, default=None,
        help="Comma-separated allowlist of entity ids"
    )
    parser.add_argument(
        "--seed", type=int, default=42,
        help="OpenAI 'seed' for best-effort reproducibility (default: 42)"
    )
    parser.add_argument(
        "--limit", type=int, default=None,
        help="Score only the first N entities (after id filter)"
    )
    parser.add_argument(
        "--force", action="store_true",
        help="Re-judge entries already present in the output file"
    )
    args = parser.parse_args()

    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        sys.exit("OPENAI_API_KEY environment variable not set.")

    client = OpenAI(api_key=api_key)

    data = json.loads(args.input.read_text(encoding="utf-8"))
    pairs = collect_entries(data)

    id_allowlist: set[str] | None = None
    if args.ids:
        id_allowlist = {s.strip() for s in args.ids.split(",") if s.strip()}

    pairs = [
        (eid, e) for (eid, e) in pairs
        if e.get("lean_back_translation")
        and (id_allowlist is None or eid in id_allowlist)
    ]
    if args.limit:
        pairs = pairs[: args.limit]

    existing_runs = {} if args.force else count_existing_runs(args.output)

    todo: list[tuple[str, dict, int]] = []
    for eid, e in pairs:
        n_existing = existing_runs.get(eid, 0)
        for run_idx in range(n_existing, args.runs):
            todo.append((eid, e, run_idx))

    is_gpt5 = args.model.startswith("gpt-5")
    effective_temp = 1.0 if is_gpt5 else args.temperature
    print(f"Eligible entries (have back-translation): {len(pairs)}")
    print(f"Records to write this run                : {len(todo)}")
    print(f"Model                                    : {args.model}")
    print(f"Temperature                              : {effective_temp}"
          + (" (forced — gpt-5+ rejects other values)" if is_gpt5 and args.temperature != 1.0 else ""))
    print(f"Seed                                     : {args.seed}")
    print(f"Runs per entry                           : {args.runs}")
    print()

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("a") as out:
        for i, (eid, entry, run_idx) in enumerate(todo):
            print(
                f"[{i+1:3d}/{len(todo)}] {eid:<20s} run={run_idx} ...",
                end=" ", flush=True,
            )
            try:
                record = judge_entry(
                    client, args.model, eid, entry, args.temperature, run_idx,
                    seed=args.seed,
                )
                out.write(json.dumps(record, ensure_ascii=False) + "\n")
                out.flush()
                imp = f"back→NL={record['back_implies_nl']} NL→back={record['nl_implies_back']}"
                print(f"score={record['score']}  ({imp})  {record['reason']}")
            except Exception as exc:
                print(f"ERROR: {exc}")
                out.write(json.dumps({
                    "id": eid,
                    "run": run_idx,
                    "score": None,
                    "back_implies_nl": None,
                    "nl_implies_back": None,
                    "reason": f"api error: {str(exc)[:160]}",
                    "model": args.model,
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
    target_ids = [eid for eid, _ in pairs]
    relevant = {eid: averages[eid] for eid in target_ids if eid in averages}
    if relevant and args.runs > 1:
        print(f"\nAverages over {args.runs} runs (numeric scores only):")
        for eid in sorted(relevant):
            avg, n = relevant[eid]
            print(f"  {eid:<20s} avg={avg:.2f}  n={n}")


if __name__ == "__main__":
    main()
