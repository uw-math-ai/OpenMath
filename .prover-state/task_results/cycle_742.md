# Cycle 742 Results

## Worked on

Backlog item #4 (post-renumber): **Butcher §336 — Dormand–Prince 5(4)
(DOPRI5) embedded pair**, plus `plan.md` housekeeping for the §111
closure on `main`.

## Approach

1. **`plan.md` housekeeping (Step 0).**
   - Marked §111 `[x]` in the §11 chapter list with the cycle 582
     `OpenMath/LinearODE.lean` headline.
   - Deleted the stale §111 entry from the Backlog Queue and renumbered
     items 4–11 down to 3–10 (so DOPRI5 is now Backlog #4).
   - Replaced the `## Current Target` body (§521 victory lap + §111
     pointer) with the DOPRI5 target body and the verbatim tableau the
     strategy supplied.

2. **DOPRI5 (Step 1).** Mirrored the cycle 494 `rkRKF45` block exactly:
   - New `noncomputable def rkDOPRI5 : EmbeddedRKPair 7` with the
     standard Dormand–Prince tableau (Hairer–Nørsett–Wanner Vol. I
     §II.5).
   - Added `private lemma sum_univ_seven` next to the `Fin 7 →`
     consumers, in a `rkDOPRI5Aux` namespace mirroring `rkRKF45Aux`.
   - All 9 deliverables landed sorry-free in one pass:
     * `rkDOPRI5_explicit` — `fin_cases i <;> fin_cases j <;> simp_all`.
     * `rkDOPRI5_consistent` — `IsConsistent` for both `mainMethod` and
       `embedMethod`, weights-sum + row-sum via `sum_univ_seven` +
       `norm_num`.
     * `rkDOPRI5_main_stifflyAccurate` and the FSAL packaging
       `rkDOPRI5_FSAL : EmbeddedRKPair.HasFSAL rkDOPRI5`.
     * `rkDOPRI5_errorWeights_sum` — one-liner via the existing
       `EmbeddedRKPair.errorWeights_sum_zero` consequence of
       `rkDOPRI5_consistent`.
     * `rkDOPRI5_embed_order4` (8 conditions) and
       `rkDOPRI5_embed_not_order5` (order5a fails for `bHat`).
     * `rkDOPRI5_main_order5` (17 conditions) and
       `rkDOPRI5_main_not_order6` (order6a fails for `b`).
   - Updated the bottom summary table to add the DOPRI5 row and the
     reference list to cite Dormand–Prince (1980).

## Result

**SUCCESS — full target landed (minimum + target + stretch).**

- `lake env lean OpenMath/EmbeddedRK.lean` — clean (only pre-existing
  warnings on lines 180–267, all in the older `rkHeunEuler21` /
  `rkBS32` blocks; no warnings or errors in the new DOPRI5 block).
- `lake build` — clean, 8087/8087 jobs.
- All 9 strategy deliverables closed sorry-free in one compile cycle:
  `rkDOPRI5_explicit`, `_consistent`, `_main_stifflyAccurate`, `_FSAL`,
  `_errorWeights_sum`, `_embed_order4`, `_embed_not_order5`,
  `_main_order5`, `_main_not_order6`.
- File grew from 509 to 730 lines — well under the 3000 cap.

The strategy budgeted `main_order5` as a stretch goal that might blow
heartbeats; it didn't. Each of the 17 main-order5 conditions and 8
embed-order4 conditions closed via the same
`simp [order_lemma, rkDOPRI5, EmbeddedRKPair.mainMethod,
sum_univ_seven]; norm_num` recipe (or the `simp only [order_lemma,
sum_univ_seven]` + `simp [...]; norm_num` two-step variant for the
nested-sum order conditions, exactly as RKF45 already does).

## Dead ends

None. The cycle 494 RKF45 template carried over verbatim with only
mechanical search-and-replace (`rkRKF45 → rkDOPRI5`,
`rkRKF45Aux → rkDOPRI5Aux`, `Fin 6 → Fin 7`, `sum_univ_six →
sum_univ_seven`, and the new tableau coefficients). No tactic surprises;
no heartbeat scaling needed.

## Discovery

- The "RKF45 template" really is mechanical for any explicit
  s-stage embedded pair where you have an `Fin.sum_univ_succ`-shaped
  sum-unfolding helper and the order-condition lemmas already
  enumerated. Future embedded pairs in the §33 family (e.g. a
  Cash–Karp 5(4), or a Verner 6(5) once order-6 conditions are needed)
  should slot in next to BS32/RKF45/DOPRI5 with the same recipe at
  roughly +200 lines per pair.
- `b 6 = 0` and `bHat 6 = 1/40` is exactly the FSAL pattern: the
  main method ignores the appended copy of the previous final stage,
  while the embedding consumes it. The stiffly-accurate condition `b i
  = A 6 i` falls out of the literal tableau by `fin_cases <;> simp`
  with no rational arithmetic — the only nontrivial entries to match
  are `b 0 = A 6 0 = 35/384`, `b 2 = A 6 2 = 500/1113`, etc., all
  literally identical because the strategy specified `b = A.row 6`.
- `simp [..., sum_univ_seven]; norm_num` did not need a heartbeat
  bump on any single condition, including the 4-deep nested order5i
  condition `∑∑∑ b·A·A·(∑ A·c) = 1/120`. The default 200 000
  heartbeat budget held.

## Suggested next approach

The next planner should pull a fresh top-of-queue item (post-renumber):

1. **Backlog #3 — Butcher §215 asymptotic Euler error formula.**
   `e_n ≈ h ψ(xₙ)` with `ψ` solving the variational ODE. Extends
   `OpenMath/EulerConvergence.lean`. Open and concrete; the
   variational ODE is already a thin generalization of the existing
   Gronwall-style bounds.

2. **Backlog #5 — Butcher §463 Milne device.** New file
   `OpenMath/MilneDevice.lean`. Predictor/corrector pair, local
   error from the difference, classical estimate. Requires a
   modest amount of new infrastructure but no Mathlib gap is
   foreseen — `OpenMath/MultistepMethods.lean` already gives the
   predictor and corrector building blocks.

3. (If both above are deferred) **Backlog #6 — §521 (b)/(c)
   follow-ups.** §522 Butcher–Chipman conjecture outline and §523
   nonlinear/algebraic GLM stability. Both feed the same A-stability
   surface that cycle 740 closed at the iff-bridge level.

The Backlog #4 slot vacated by DOPRI5 should be filled at the bottom
with whatever new chapter-3/5 target the planner notices is missing
(e.g. **§337 Cash–Karp 5(4)** or **§543 ARK structural conditions**),
keeping the queue ≥ 5 items as the rules require.
