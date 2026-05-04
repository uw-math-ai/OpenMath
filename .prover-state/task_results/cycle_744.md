# Cycle 744 Results

## Worked on

- `plan.md` housekeeping: marked §336 DOPRI5 `[x]` in §33,
  removed §336 from the Backlog Queue and renumbered subsequent items,
  promoted §463 Milne device into `## Current Target`, and added a
  one-line cycle-744 entry to `## Active Frontier`.
- New file `OpenMath/MilneDevice.lean` — Butcher §463 Milne device for
  local error estimation (predictor / corrector pair, structural
  definitions plus concrete AB4 / AM3 instance).

## Approach

- Followed the cycle 744 strategy verbatim.
- Wrote the `MilneDevicePair sP sC p` structure with the six fields
  (`predictor`, `corrector`, two `HasOrder p` witnesses, and the
  explicit / implicit witnesses).
- Defined `MilneDevicePair.milneFactor` as `C^C / (C^P − C^C)` and
  `localErrorEstimate yP yC := milneFactor · (yC − yP)`.
- Built the concrete `milneAB4AM3 : MilneDevicePair 4 3 4` instance,
  reusing the already-landed Adams predicates in
  `OpenMath/AdamsMethods.lean`:
  `adamsBashforth4_order_four`, `adamsMoulton3_order_four`,
  `adamsBashforth4_explicit`, `adamsMoulton3_implicit`.
- Closed the three quantitative theorems
  `milneAB4AM3_milneFactor = -(19/270)`,
  `milneAB4AM3_localErrorEstimate = -(19/270) · (yC − yP)`, and
  `milneAB4AM3_milneFactor_neg`.

## Result

SUCCESS — `OpenMath/MilneDevice.lean` compiles cleanly with
`lake env lean OpenMath/MilneDevice.lean` (exit 0) and `lake build`
succeeds (8087 jobs, no errors). Zero `sorry` in the new file.

The strategy's anticipated `simp [adamsMoulton3]` recipe for closing
the corrector-implicit goal turned out to be unnecessary: the existing
top-level lemma `adamsMoulton3_implicit` (in `OpenMath/AdamsMethods.lean`
line 490) is exactly the proof obligation, so the field assignment
`corrector_implicit := adamsMoulton3_implicit` closes it directly.

## Dead ends

None. The strategy was concrete enough that the file landed on the
first attempt.

## Discovery

- `adamsMoulton3_implicit` was already in the repo since the AB / AM
  scaffold was built. The strategy suggested re-deriving it inside
  `MilneDevicePair`; reusing the named lemma keeps the file minimal
  (~70 lines vs. the strategy's draft ~80 lines).
- `lake build` re-uses cached `.olean`s and only rebuilt the new
  `MilneDevice.lean` plus its transitive frontier — no stale-cache
  issues from cycle 742's DOPRI5 work.

## Suggested next approach

Per the strategy's "What NOT to try", a quantitative
`LTE^C ≈ milneFactor · (yC − yP) + O(h^{p+2})` is deferred until the
§215 asymptotic-error machinery lands. The natural next textbook
deliverable to schedule is therefore one of:

1. Backlog item #1 — Butcher §510 / §513–§515 GLM Dahlquist
   equivalence chain. This is the largest remaining textbook gap.
2. Backlog item #3 — Butcher §215 asymptotic error formula for the
   Euler method. Smaller and self-contained; would unblock a future
   quantitative Milne LTE theorem.

If the worker is still drifting toward null cycles, prefer item #3
(§215) for the next cycle: it has a single concrete deliverable
(`OpenMath/EulerConvergence.lean` extension) and well-defined
infrastructure (`Iserles §1.2` style asymptotic expansion) that
mirrors the cycle 744 / cycle 742 closure templates.
