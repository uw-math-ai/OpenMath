# Cycle 734 Results

## Worked on

§521 Step J ladder (generic-ξ closed forms) in
`OpenMath/LMMAsGLM/StabilityCharpoly.lean`.

All three mandatory targets (J.1, J.2, J.3) **and** the stretch
target (J.4 plus its private `rowFBetaPoly_eval_general` and
`toGLM_stabilityMatrixPY_zero_charpoly_eval_general` helpers)
landed sorry-free.

## Approach

Followed the planner's recipes verbatim with one-line adjustments
where Lean closed steps earlier than the recipe predicted.

- **J.1** (`rowFAlphaResidual_eval_closed_form`) — Direct port of
  H.2's proof body. Swapped the `rowFAlphaResidual_eval_one_eq_double_sum`
  rewrite for the private generic-ξ
  `rowFAlphaResidual_eval_eq_double_sum`, dropped the `one_pow` arg
  from the `hAdj` `rw`, and added the trailing `* ξ^(k:ℕ)` factor
  on each per-summand RHS. `push_cast; ring` and `ring` closed the
  inner and outer steps unchanged.
- **J.2** (`rowFAlphaPoly_eval_general`) — Three-line copy of
  D.10b's body. The existing `simp [Polynomial.eval_mul,
  Polynomial.eval_pow, Polynomial.eval_X]` set kept the `ξ^(l:ℕ)`
  factor at generic ξ exactly as predicted.
- **J.3** (`rowYQuot_eval_general`) — Five-line copy of F.3's
  (`rowYQuot_eval_one`) body. The `one_pow, mul_one` cleanup at
  the end of F.3 simply drops out at generic ξ — the `rw` chain
  closes the goal.
- **J.4** (`D_mul_toGLM_charpoly_eval_general`) — Stretch target.
  Substituted J.1, J.2, J.3, and the two new helpers into C.16.
  Used `set A`, `set B` to abstract the two scalar sums (the same
  cancellation algebra that drives H.3, lifted to ξ-graded form).
  After two `Finset.sum_congr` reshape rewrites (`hRes` and
  `hDiff`) the residual closes with a single `ring`.

## Result

**SUCCESS** — All four theorems compile cleanly via
`lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean` with no
errors and no sorrys introduced.

## Dead ends

Three trivial "no goals to be solved" warnings on the first
compile pass for J.4 (the trailing `ring` after a `simp` that
already closed; an explicit `show … rfl` after `Finset.sum_neg_distrib`
that already closed; and an `rfl` after `← Finset.mul_sum`). All
fixed by deleting the redundant tactic line.

No genuine dead ends.

## Discovery

- The planner's recipes were essentially executable — the only
  micro-adjustments were dropping closing tactics that Lean had
  already finished (`simp` and `Finset.sum_*` rewrites collapsing
  goals fully), exactly the cycle 732 I.2 takeaway flagged in the
  strategy.
- For the J.4 cancellation, abstracting both scalar sums via
  `set A` / `set B` *before* feeding the residual to `ring`
  works: the sums are then opaque field elements and `ring`
  cancels the (β_last A) cross-terms and the (-A B + A B) inner
  pair without needing manual `linear_combination`.
- The cycle 728 G.1 takeaway ("`ring` does not distribute over
  `Finset.sum` — pre-reshape with `Finset.sum_sub_distrib` /
  `← Finset.mul_sum` first") applied verbatim in the J.4 `hRes` /
  `hDiff` rewrites and was the reason J.4 closed at all.

## Suggested next approach

The §521 LMM iff bridge `LMM.toGLM_isAStable_iff` now sits one
step beyond J.4: lift the **scalar** identity J.4
`D · charpoly.eval ξ = ξ^s · stabilityPolyPoly.eval ξ` to the
**polynomial-level** divisibility statement
`D • charpoly = X^s · stabilityPolyPoly` (or, equivalently, prove
the C-coercion of J.4 holds at every coefficient — i.e. that
`toGLM_stabilityMatrix.charpoly` and `X^s · stabilityPolyPoly`
agree as polynomials, not just per-evaluation). Once that is
landed, the unit-disk root-counting argument can close the iff
bridge.

Concretely, the next planner should consider:

1. **K.1** — a `Polynomial.funext` / `Polynomial.eq_of_eval_eq`
   style lift of J.4 (since both sides are degree-≤ s polynomials
   in ξ, equality at countably many points or full eval-equality
   gives equality of polynomials).
2. **K.2** — apply the polynomial identity with the BDF / non-BDF
   distinction now collapsed to the unit-disk argument over
   `stabilityPolyPoly z`.

Note also: file is now **3149 lines** (was 2957 at start of
cycle). Soft cap (3000) crossed; hard cap (6000) untouched. The
planner may want to schedule a split in cycle 735 — natural seam
is "Section 521 endpoint identities (H, I)" vs "Section 521
generic-ξ identities (J)" since J adds ~190 cohesive lines.

## Hand-off

If the cycle-735 planner picks K (polynomial-level lift of J.4),
the next seam is one `Polynomial.funext`-style step plus the
unit-disk root-counting argument; **all** the load-bearing scalar
identities (H.3, I.3, J.4) are now in place at full generality
(no BDF hypothesis).
