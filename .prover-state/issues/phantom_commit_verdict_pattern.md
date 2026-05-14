# Issue: phantom "commit-not-reaching-repo" verdict propagated through cycles 176–179

## Blocker (loop-maintainer territory)

For four consecutive cycles (176, 177, 178, 179), the supervisor has issued
`score = −2` "commit-not-reaching-repo" verdicts against the cycle worker
asserting that `OpenMath/Chapter4/Section441.lean` was *not* present in the
cycle's commit. **All four verdicts are false alarms.** The git state
unambiguously contradicts each one.

The worker (cycle 180) followed the planner's mandatory Priority 0
verification step, ran `git show --stat <sha> -- OpenMath/Chapter4/Section441.lean`
on each of the four flagged commits, and obtained non-empty diffstats:

| cycle | commit    | Section441.lean diffstat                  |
| ----- | --------- | ----------------------------------------- |
| 176   | `0b171c9` | `1 file changed, 209 insertions(+), 1 deletion(-)` |
| 177   | `1f0b21c` | `1 file changed, 143 insertions(+)`       |
| 178   | `80a5865` | `1 file changed, 62 insertions(+)`        |
| 179   | `572f058` | `1 file changed, 32 insertions(+)`        |

Cumulative: **+446 insertions** to Section441.lean across cycles 176–179.

Phase B of `lem:441A` (`a₁ > 0` for stable preconsistent LMMs) is correctly
closed by these four cycles. The five Phase B landmark theorems are all
present in the file at HEAD (verified at cycle 180 start):

```
504  ρPoly_no_real_root_gt_one
599  ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent
707  ρPoly_pos_on_Ioi_one
767  ρPoly_deriv_eval_one_pos_of_stable_preconsistent
913  aPoly_coeff_one_pos_of_stable_preconsistent
```

`Section441.lean` is 932 LOC, sorry count 0, axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`).

This is the same false-alarm shape diagnosed in cycles 008, 014, 015,
035, 073, and 170 (see `consultant_advice_cycle_009.md` §A,
`consultant_advice_cycle_014.md`, `consultant_advice_cycle_015.md` §B,
and the cycle 171 entry in `attempts.md`). The pattern has now propagated
through **four consecutive cycles unfixed**, which is materially worse
than any prior occurrence.

## Context

Each cycle 176–179 worker correctly reported axiom-clean theorems landed
in `Section441.lean`. The supervisor's verdict in each case asserted
"Section441.lean absent from the diff" and reverted the cycle's score.
However, the corresponding `attempts.md` row for the *next* cycle was
auto-prepended with the false-positive diagnosis, which then leaked into
the next cycle's prompt as if it were established fact. The next cycle's
worker, seeing the propagated row, was then misled into either trying to
re-derive already-shipped Phase B work or wasting a cycle re-verifying.

The cycle 180 strategy correctly diagnoses this and instructs the worker
to (a) verify git state directly, (b) record the false-alarm pattern,
(c) escalate to the loop-maintainer via this issue file. **The worker
must NOT attempt to fix this from the worker side** — it is supervisor
prompt-builder / diff-detection logic, which lives in
`scripts/autonomous_loop.py` and is loop-maintainer territory.

## What was tried

This is the worker's first cycle of explicit verification. The strategy
file for cycle 180 contains the verification command set (`git show --stat`
+ landmark `grep -n`), which the worker ran and reproduced in
`task_results/cycle_180.md` and the `Cycle 180 confirmation` row of
`attempts.md`.

No worker-side fix was attempted (per planner instruction).

## Possible solutions (loop-maintainer)

The supervisor's diff-detection logic appears to be looking for the
wrong thing. Hypotheses (in priority order):

1. **Diff-extraction bug**: the supervisor parses `git diff` or
   `git show` output, but is checking a stale view (e.g. the index
   *before* the cycle's commit, or the working tree without staged
   changes), rather than `HEAD~1..HEAD` after the worker's commit
   has landed. A trivial reproducer: invoke the supervisor's
   "did the cycle commit Section441.lean?" check on commit `572f058`
   and see whether it returns the false negative.
2. **Path-matching bug**: the supervisor may be filtering diffs by
   a hard-coded list of Lean file roots that does not include
   `OpenMath/Chapter4/Section441.lean`. (§441 is a relatively new file
   created in cycle 171 — older path filters may not have been updated.)
3. **Prompt-builder propagation**: `attempts.md` rows are prepended
   into subsequent cycle prompts, and a single false-positive entry
   from one cycle gets re-cited by the next cycle's supervisor as
   "see, the previous cycle had the same problem", causing the false
   alarm to compound. This is the cycle-009 / cycle-015 diagnosis pattern.
4. **Hash collision**: the supervisor may be looking up a commit
   that does not exist (e.g. checking the *parent* of the cycle's
   commit, or a HEAD that has not yet advanced).

A quick sanity-check the loop-maintainer can run:

```bash
for sha in 0b171c9 1f0b21c 80a5865 572f058; do
  echo "== $sha =="
  git show --stat $sha | head -3
  git diff-tree --no-commit-id --name-only -r $sha | grep -F Section441.lean
done
```

All four iterations should print the same `OpenMath/Chapter4/Section441.lean`
line. If the supervisor's check disagrees, the supervisor's logic — not
the worker's commits — is the bug.

## Cross-references

- `consultant_advice_cycle_009.md` §A — first canonical diagnosis of
  the "commit-not-reaching-repo" false-positive shape (cycle 008).
- `consultant_advice_cycle_014.md` — second occurrence (cycle 014/015).
- `consultant_advice_cycle_015.md` §B — third occurrence + propagation
  warning.
- `tautology_scanner_false_positives.md` — sibling supervisor-prompt-builder
  bug already documented (different scanner, same systemic issue).
- `attempts.md` rows for cycles 8, 35, 73, 170, 176, 177, 178, 179 — each
  records a false positive of this shape.
- `attempts.md` cycle 171 row — first explicit refutation
  (cycle 170 phantom).
- `task_results/cycle_180.md` — worker's verification commands and outputs.

## Recommendation

Until the loop-maintainer audits and patches the supervisor's diff
detection, future workers in §441 (and any other newly-created Lean
file) should:

1. Run `git show --stat <prev-sha> -- <file>` at the start of each
   cycle for any flagged "missing" file.
2. Trust the git output, not propagated `attempts.md` rows.
3. Append a short "Cycle N confirmation" entry to `attempts.md` if a
   false positive is observed, citing this issue file.
4. Do **not** attempt to re-derive already-shipped work in response
   to a false alarm.

## Cycle 197 update — 9th confirmed false alarm (cycle 196 commit `2feee1d`)

The pattern has now propagated to **`Section381.lean`** (Chapter 3,
§380 — the deferred def:381E `reducedMethod` infrastructure path), in
addition to the historical `Section441.lean` (Chapter 4, §441) chain.
This widens the false-alarm surface beyond a single file and refutes
hypothesis #2 ("path-matching bug specific to §441") above.

Cycle 196 supervisor verdict (score = 0) reported: "Worker claims 9
axiom-clean destructor/spec/corollary declarations for
IsPReducible/IsZeroReducible plus 2 P2 example→theorem promotions in
Section381.lean, but commit 2feee1d contains only `.gitignore`,
`heartbeat.json`, `history.jsonl`, and `strategy.md` — no Lean file
changes appear in the git diff."

Cycle 197 worker verification (Priority 0):

```
$ git show --stat 2feee1d -- OpenMath/Chapter3/Section381.lean
 OpenMath/Chapter3/Section381.lean | 99 ++++++++++++++++++++++++++++++++++++++-
 1 file changed, 97 insertions(+), 2 deletions(-)

$ git rev-parse HEAD ; git rev-parse origin/butcher-experiments
2feee1d7af41682be39a6b92f64e9ae8ba321a95
2feee1d7af41682be39a6b92f64e9ae8ba321a95
```

Landmark grep at HEAD confirms all 6 promised theorems present:
`IsPReducible.sBar` @692, `IsPReducible.sBar_lt` @701,
`IsPReducible.partition` @708, `IsPReducible.partition_isPReducibleVia`
@716, `IsZeroReducible.inP1` @723, `IsZeroReducible.exists_inP1_false`
@733, plus P2 promotions
`paddedEuler_pReduced_pairPartition_eq_of_both_isIrreducible` @1493 and
`paddedEuler_pReducesTo_pReduced_via_pEquivalent_extraction` @1510.
Final file size: 1544 LOC; sorry count: 0.

### Updated false-alarm tally

| cycle | commit    | file              | diffstat                                        |
| ----- | --------- | ----------------- | ----------------------------------------------- |
| 176   | `0b171c9` | Section441.lean   | `1 file changed, 209 insertions(+), 1 deletion(-)` |
| 177   | `1f0b21c` | Section441.lean   | `1 file changed, 143 insertions(+)`             |
| 178   | `80a5865` | Section441.lean   | `1 file changed, 62 insertions(+)`              |
| 179   | `572f058` | Section441.lean   | `1 file changed, 32 insertions(+)`              |
| 196   | `2feee1d` | Section381.lean   | `1 file changed, 97 insertions(+), 2 deletions(-)` |

Plus the historical cycle-008 / cycle-035 / cycle-073 / cycle-170 entries
(see `attempts.md`), bringing the cumulative confirmed false-alarm count
to **9 occurrences** across at least two distinct files. The
loop-maintainer escalation remains in force.
