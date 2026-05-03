# Cycle 706 Results

## Worked on
§521 Step C.19 — `toGLM_charpoly_eval_eq_zero_iff_of_bdf` in
`OpenMath/LMMAsGLM/StabilityCharpoly.lean`. Unified eval-form iff
combining cycle 702 (Step C.17, non-zero roots) and cycle 704
(Step C.18, ξ = 0 root) with no side condition on ξ.

## Approach
Followed the planner's preferred 3-line `rw` chain. Used the existing
IsRoot-form iff `toGLM_stabilityMatrix_eigenvalue_iff_of_bdf`
(`Stability.lean` line 1021) and bridged it to the eval form via
`Polynomial.IsRoot.def` (in the `← ` direction to take the goal
`eval ξ p = 0 → IsRoot p ξ`) and `stabilityPolyPoly_eval` (in the
`← ` direction to convert `m.stabilityPoly ξ z` back into
`(m.stabilityPolyPoly z).eval ξ`). Final proof:

```lean
  rw [← Polynomial.IsRoot.def,
      toGLM_stabilityMatrix_eigenvalue_iff_of_bdf m z hbdf hz,
      ← stabilityPolyPoly_eval]
```

## Result
SUCCESS. `lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean`
compiles with zero diagnostics. Only this file was modified
(`git diff --stat` shows 19 inserted lines).

## Dead ends
None. The 3-line proof shape worked on the first attempt. The
canonical `hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0` shape
matches the upstream IsRoot iff signature exactly, so no shape
conversion was needed. `[NeZero s]` was sufficient — no `0 < s`
hypothesis had to be threaded since the IsRoot iff handles the
ξ = 0 case internally via `pow_eq_zero_iff`.

## Discovery
The IsRoot-form iff (Stability.lean line 1021) is strictly more
general than the eval-form C.17 (StabilityCharpoly.lean line 1633):
its statement has no `ξ ≠ 0` side condition because `Polynomial.X^s`
contributes the `ξ = 0` root directly through `pow_eq_zero_iff`.
Anyone deriving an unrestricted eval-form iff under BDF should reach
for the IsRoot iff first; deriving from C.17 + C.18 by hand requires
a four-way case split on `ξ = 0` and is much heavier.

`Polynomial.IsRoot.def` is `IsRoot p a ↔ eval a p = 0`. To rewrite
`eval a p = 0` into `IsRoot p a` use the `← ` direction.

## Suggested next approach
The IsRoot/eval BDF chain is now complete:
- C.15 (consistency): cycle 700.
- C.16 (eval corollary): cycle 700.
- C.17 (non-zero-roots scalar iff): cycle 702.
- C.18 (ξ = 0 boundary): cycle 704.
- C.19 (unified eval-form iff): cycle 706 (this).

Stretch contrapositive `_ne_zero_iff_of_bdf` was not landed (planner
marked it optional and we chose to exit cleanly). Could be a one-line
follow-up next cycle if downstream root-counting actually needs it.

The planner-noted next architectural step is the *general* (non-BDF)
LMM iff bridge tracked in
`.prover-state/issues/lmm_toGLM_general_charpoly_rank_one.md`. That
needs the rank-one charpoly identity for the residual factor and is
out of scope for the §521 BDF chain. A separate cycle and strategy.

After C.19 the natural seam toward the headline `toGLM_isAStable_iff`
is to compose this iff with a unit-disk root-counting argument
(spurious `ξ = 0` is on the closed unit disk but the textbook
A-stability definition allows it / classifies it via `simple_root`
machinery). Worth a planner cycle to scope.
