# Cycle 702 Results

## Worked on
§521 Step C.17 — BDF non-zero-roots scalar bridge between
`(m.toGLM.stabilityMatrix z).charpoly.eval ξ` and
`(m.stabilityPolyPoly z).eval ξ`, plus its contrapositive
wrapper. Both added at the end of `OpenMath/LMMAsGLM/StabilityCharpoly.lean`
inside `namespace LMM`.

## Approach
Followed the strategy literally:

1. `congrArg (Polynomial.eval ξ)` applied to the cycle 643 BDF headline
   `D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf`.
2. `simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
   Polynomial.eval_X]` to obtain `D * charpoly.eval ξ = ξ^s * stabilityPolyPoly.eval ξ`.
3. Two iff branches each closed by substituting one side = 0 in the
   evaluated identity, then `mul_eq_zero.mp _ |>.resolve_left _` against
   `hξs : ξ^s ≠ 0` (resp. `hz`).
4. Contrapositive wrapper: `.not` on the iff.

## Result
SUCCESS — both theorems land sorry-free.

`lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean` returns 0
errors / 0 warnings. No `mul_eq_zero.resolve_left` elaboration issues
(the suggested fallback `rcases` plan was not needed).

Theorems landed:

- `LMM.toGLM_charpoly_eval_eq_zero_iff_stabilityPoly_of_bdf`
- `LMM.toGLM_charpoly_eval_ne_zero_iff_stabilityPoly_of_bdf`

## Dead ends
None — Step 1 went through on the first attempt with the suggested
proof skeleton. Step 2 was a one-liner via `Iff.not`.

## Discovery
The cycle-700 evaluation pattern (`congrArg Polynomial.eval` + scoped
`simp only [Polynomial.eval_mul, …]`) generalises cleanly to the BDF
case as long as we keep the lemma in `Polynomial.C D · charpoly =
X^s · stabilityPolyPoly` form (rather than expanded with the residual).
That makes the scalar mul_eq_zero argument trivial because there is no
residual to dispose of.

## Suggested next approach
Two narrow concrete next targets, in priority order:

1. **`ξ = 0` companion.** A `ξ = 0` evaluation of the cycle 643 BDF
   headline collapses `X^s · stabilityPolyPoly z` to `0` (since
   `s ≥ 1`), giving `D * (charpoly.eval 0) = 0` and hence
   `charpoly.eval 0 = 0`. The matching scalar fact is
   `(m.stabilityPolyPoly z).eval 0 = β_last_real - z * α_last_real` (or
   similar), so this branch is *not* an iff at `ξ = 0` in general — but
   it does give the constant-term identity needed for the unit-disk
   root-counting branch. A careful cycle could land
   `toGLM_charpoly_eval_zero_eq_of_bdf` as a one-direction
   `charpoly.eval 0 = 0` statement, conditional on `s ≥ 1`.

2. **Unit-disk universal bridge.** Combine cycle 702's non-zero-roots
   iff with the (yet-to-prove) `ξ = 0` companion to land
   `(∀ ξ, |ξ| ≤ 1 → charpoly.eval ξ = 0 → False) ↔ (∀ ξ, |ξ| ≤ 1 →
   stabilityPolyPoly.eval ξ = 0 → False)` under BDF. This is the
   final shape needed for `LMM.toGLM_isAStable_iff` (still
   distant — do not attempt in one cycle).

Do **not** attempt the general (non-BDF) version: the cycle 700
residual is non-zero and the iff fails as documented in the strategy.
