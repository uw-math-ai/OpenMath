# Issue: tautology scanner over-fires on legitimate `:= h_*` / `exact h_*` closers

## Blocker

The "semantic sorry" / tautology scanner in `scripts/autonomous_loop.py`
(roughly lines 357–479) has two underlying bugs that produce
false-positive flags on legitimate Lean idioms. These false positives
have appeared in cycles 010, 013, 014, and 015, and each time the
worker has been forced to apply a cosmetic `h_<name>` → `h<name>`
rename (drop the underscore so the regex stops matching) instead of
fixing the scanner. The renames are α-equivalent and have no semantic
effect, but they accumulate and clutter the codebase.

## Context

### Bug D1 — block-comment line drift in `_strip_lean_comments`

`scripts/autonomous_loop.py:357-382` (`_strip_lean_comments`) deletes
characters of block comments **including their internal newlines**. The
caller at `scripts/autonomous_loop.py:472-479` then enumerates the
comment-stripped buffer's lines and reports the index `i` as the file
line number, while indexing into `raw_lines[i-1]` for the displayed
source.

If the file has a multi-line `/-! ... -/` or `/-- ... -/` block, the
reported line number under-counts the true file line and the displayed
source string is unrelated. This produced confusing reports like
"Section212.lean:138" pointing at a comment line, when the actual
matched closer was elsewhere in the file.

Concrete repro recorded in
`.prover-state/issues/consultant_advice_cycle_014.md` §A.

### Bug D2 — the heuristic flags legitimate "rewrite-then-exact" closers

`scripts/autonomous_loop.py:441-445` uses three regexes:

```python
TAUTOLOGY_PATTERNS = [
    (r':=\s*h_\w+\s*$',     "proof returns a hypothesis directly"),
    (r':=\s*id\s*$',         "proof is identity function"),
    (r'\bexact\s+h_\w+\s*$', "proof is 'exact <hypothesis>'"),
]
```

These match `:= h_<word>` / `exact h_<word>` whenever the hypothesis
name happens to start with `h_`. The patterns over-fire on the
standard Lean idiom of building up a hypothesis by rewriting and then
closing the sub-proof with `exact`:

```lean
have h_inner := some_construction
rw [h_eq] at h_inner
rw [h_combine] at h_inner
exact h_inner
```

This is doing real proof work — the `rw`s materially reshape the
hypothesis into the goal — but the scanner sees only `exact h_inner`
and flags it. They also fire on `obtain ⟨...⟩ := h_<name>`
destructurings and on `calc`-step `:= h_<name>` closers, neither of
which are vacuous proofs.

## What was tried

**Cycles 010, 014, 015 cosmetic workaround.** Renamed every flagged
`h_<name>` → `h<name>` (drop the underscore so the regex stops
matching). This works but does not fix the scanner; future cycles will
trip the same patterns whenever someone writes a legitimate
`:= h_<name>` closer.

**Cycle 014 consultant analysis.** Detailed in
`.prover-state/issues/consultant_advice_cycle_014.md` §A and §D, with
concrete fix recipes for both D1 and D2.

**Worker rule.** `CLAUDE.md` and the cycle-015 strategy explicitly
forbid worker edits to `scripts/autonomous_loop.py`, so this issue is
the loop maintainer's responsibility, not the worker's.

## Possible solutions

### Fix D1: preserve newlines in `_strip_lean_comments`

Replace block-comment characters with spaces (not deletions), but
**keep newlines**. The minimal patch (from the cycle-014 consultant
note §D1, option 1):

```python
while i < len(text):
    if text[i:i+2] == '/-':
        depth += 1; i += 2
    elif text[i:i+2] == '-/' and depth > 0:
        depth -= 1; i += 2
    elif depth == 0:
        result.append(text[i]); i += 1
    else:
        result.append('\n' if text[i] == '\n' else ' ')
        i += 1
```

This makes `enumerate(code_lines, 1)` emit accurate file line numbers,
and the displayed source line will match the location of the regex
hit.

### Fix D2: tighten the heuristic to skip nested closers

Two options, ordered by simplicity:

1. **Indent-based skip.** Require the matched line's indentation to
   be ≤ the column of the most recent `theorem`/`lemma`/`example`
   keyword. Inner `have` / `calc` bodies are always more indented and
   would be skipped. Catches the common case (vacuous top-level
   theorems) without false-positive churn.
2. **Rewrite-aware skip.** Track names that appear as the target of a
   `rw … at <name>` or `simp … at <name>` earlier in the same `:= by`
   block. Skip the closer if the matched name is one of those.

Either fix would have prevented all of the cycle-010/013/014/015 false
positives.

### Fix D3: regenerate "Suspected vacuous proofs" from HEAD, not from `attempts.md`

Even after D1+D2, the prompt-builder for the planner / worker should
not propagate scanner verdicts from `attempts.md` into the next
cycle's prompt. The evaluator already re-runs `get_tautology_locations`
against the post-commit tree (`scripts/autonomous_loop.py:1122`); only
those results should appear, and stale `attempts.md` rows from prior
cycles' evaluator output should be filtered.

## Severity

**Low** — workaround (rename) is mechanical and takes ~30s per cycle.
But it is repeated cosmetic churn caused by a fixable scanner bug, so
a one-time D1+D2 fix is well worth the maintainer's time.

## Cross-references

- `.prover-state/issues/consultant_advice_cycle_014.md` §A, §D — full
  diagnosis with concrete diff recipes.
- Cycle 014 task results — applied the cosmetic rename for
  `Section212.lean:138/144`.
- Cycle 015 task results — applied the cosmetic rename for
  `Section112.lean:126` (`h_inner` → `hinner`) and for the new
  Section212/Section213 off-step lemmas.

## Cycle 121 update

Cycle 121 applied the cosmetic rename workaround to
`aux_515D_iterated_V_bound` in `OpenMath/Chapter5/Section515.lean`
(lines 1900, 1908, 1918, 1921, 1922, 1923):
* `h_abs_sum` → `habs_sum`
* `h_sum_bd`  → `hsum_bd`
* `h_card`    → `hcard`

The bug-D1 (block-comment line drift) and bug-D2 (over-firing on
`:= h_<name>` / `exact h_<name>` calc-step closers) remain unfixed
in `scripts/autonomous_loop.py`. Each new helper introduced by
cycle ≥116 has had to apply this rename; aggregate maintenance
cost now exceeds the one-time D1+D2 fix. This is loop-maintainer
territory — workers do NOT edit `scripts/autonomous_loop.py`.
