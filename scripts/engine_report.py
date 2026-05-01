#!/usr/bin/env python3
"""Aggregate .prover-state/history.jsonl by worker engine.

Usage:
  scripts/engine_report.py                 # all cycles
  scripts/engine_report.py --since 500     # cycles >= 500
  scripts/engine_report.py --last 50       # last 50 cycles
  scripts/engine_report.py --json          # machine-readable

Engine assignment is mechanical (even cycles -> claude, odd -> codex --
see get_worker_engine in autonomous_loop.py), so cycle counts are within
1 of each other when filtered. Differences in score / sorries-closed /
strategy-deviation rate reflect engine behavior, not workload skew.
"""

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path
from typing import Dict, List, Optional

ROOT = Path(__file__).resolve().parents[1]
HISTORY = ROOT / ".prover-state" / "history.jsonl"


def load_history(since, last):
    # type: (Optional[int], Optional[int]) -> List[dict]
    if not HISTORY.exists():
        sys.exit(f"history.jsonl not found at {HISTORY}")
    rows = [json.loads(l) for l in HISTORY.read_text().splitlines() if l.strip()]
    if since is not None:
        rows = [r for r in rows if r.get("cycle", 0) >= since]
    if last is not None:
        rows = rows[-last:]
    return rows


def aggregate(rows):
    # type: (List[dict]) -> Dict[str, dict]
    agg = defaultdict(lambda: {
        "cycles": 0,
        "score_sum": 0,
        "score_count": 0,           # cycles with numeric score
        "sorries_closed": 0,        # sum of (pre - post) when post < pre
        "sorries_opened": 0,        # sum of (post - pre) when post > pre
        "stuck_cycles": 0,          # cycles with non-empty stuck_on
        "deviation_cycles": 0,      # cycles with strategy_deviation
        "regressions": 0,           # score == -2
        "wins": 0,                  # score == +2
        "first_cycle": None,
        "last_cycle": None,
    })
    for r in rows:
        eng = r.get("engine", "unknown")
        s = agg[eng]
        cyc = r.get("cycle")
        s["cycles"] += 1
        if isinstance(r.get("progress_score"), int):
            s["score_sum"] += r["progress_score"]
            s["score_count"] += 1
            if r["progress_score"] == -2:
                s["regressions"] += 1
            elif r["progress_score"] == 2:
                s["wins"] += 1
        pre, post = r.get("pre_sorry_count", 0), r.get("post_sorry_count", 0)
        if post < pre:
            s["sorries_closed"] += pre - post
        elif post > pre:
            s["sorries_opened"] += post - pre
        if r.get("stuck_on"):
            s["stuck_cycles"] += 1
        if r.get("strategy_deviation"):
            s["deviation_cycles"] += 1
        if cyc is not None:
            if s["first_cycle"] is None or cyc < s["first_cycle"]:
                s["first_cycle"] = cyc
            if s["last_cycle"] is None or cyc > s["last_cycle"]:
                s["last_cycle"] = cyc
    return dict(agg)


def fmt_table(agg):
    # type: (Dict[str, dict]) -> str
    headers = ["engine", "cycles", "avg_score", "wins", "regr",
               "closed", "opened", "net", "stuck%", "dev%", "range"]
    rows = []
    for eng in sorted(agg.keys()):
        s = agg[eng]
        avg = s["score_sum"] / s["score_count"] if s["score_count"] else 0.0
        net = s["sorries_closed"] - s["sorries_opened"]
        stuck_pct = 100.0 * s["stuck_cycles"] / s["cycles"] if s["cycles"] else 0.0
        dev_pct = 100.0 * s["deviation_cycles"] / s["cycles"] if s["cycles"] else 0.0
        rng = (f"{s['first_cycle']}-{s['last_cycle']}"
               if s["first_cycle"] is not None else "-")
        rows.append([
            eng, str(s["cycles"]), f"{avg:+.2f}",
            str(s["wins"]), str(s["regressions"]),
            str(s["sorries_closed"]), str(s["sorries_opened"]),
            f"{net:+d}",
            f"{stuck_pct:.0f}", f"{dev_pct:.0f}", rng,
        ])
    widths = [max(len(h), *(len(r[i]) for r in rows)) for i, h in enumerate(headers)]
    sep = " | "
    out_lines = [sep.join(h.ljust(w) for h, w in zip(headers, widths))]
    out_lines.append("-+-".join("-" * w for w in widths))
    for r in rows:
        out_lines.append(sep.join(c.ljust(w) for c, w in zip(r, widths)))
    return "\n".join(out_lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--since", type=int, help="only cycles >= N")
    ap.add_argument("--last", type=int, help="only the last N cycles")
    ap.add_argument("--json", action="store_true", help="machine-readable JSON")
    args = ap.parse_args()

    rows = load_history(args.since, args.last)
    agg = aggregate(rows)

    if args.json:
        print(json.dumps(agg, indent=2))
        return

    if not rows:
        print("No matching cycles.")
        return

    first = min(r.get("cycle", 0) for r in rows)
    last = max(r.get("cycle", 0) for r in rows)
    print(f"# Engine contribution report — cycles {first}–{last} "
          f"({len(rows)} total)\n")
    print(fmt_table(agg))
    print()
    print("Columns:")
    print("  avg_score : mean evaluator progress score (-2..+2)")
    print("  wins      : cycles with score == +2")
    print("  regr      : cycles with score == -2 (revert/regression)")
    print("  closed    : sum of sorries closed (pre > post)")
    print("  opened    : sum of sorries opened (post > pre)")
    print("  net       : closed - opened")
    print("  stuck%    : % cycles with non-empty stuck_on")
    print("  dev%      : % cycles flagged for strategy deviation")


if __name__ == "__main__":
    main()
