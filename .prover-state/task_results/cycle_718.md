# Cycle 718 Results

## Worked on
§521 Step D.11′ (substitution closures) and stretch Step D.12 (rowYQuot
`dif_neg` branch dischargers) in `OpenMath/LMMAsGLM/StabilityCharpoly.lean`.

Theorems landed (all five):
- `D_mul_toGLM_charpoly_eval_zero_substituted` (D.11a)
- `D_mul_toGLM_charpoly_eval_one_substituted` (D.11b)
- `D_mul_toGLM_charpoly_eval_one_substituted_of_bdf` (D.11c)
- `rowYQuot_eval_zero_eq` (D.12a, stretch)
- `rowYQuot_eval_one_eq` (D.12b, stretch)

## Approach
Pasted the strategy's pre-pruned proof skeletons verbatim immediately
before `end LMM`. D.11a/b are pure single `rw`-chains substituting the
cycle 716 D.10a / D.10b residual evaluations into the cycle 712 / 714
D.8 / D.9 closed forms. D.11c mirrors the cycle 714 BDF closure pattern
(Σβ(castSucc) = 0 ⇒ corrective product vanishes ⇒ ring).

D.12a / D.12b just unfold `rowYQuot` and rewrite the `dif_neg s = 0`
branch using `hs.ne'`.

## Result
SUCCESS. All five theorems compiled verbatim from the strategy's
skeletons. `lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean`
produces empty output. File grew from 2000 → 2090 lines (still well
under 3000-line cap).

## Dead ends
None — the strategy proofs were already pruned (no trailing
`push_cast; ring` after the substitution `rw`s, in line with the cycle
712 lesson). No edits needed.

## Discovery
- `rowYQuot` is defined as `if h : s = 0 then 0 else <det>` (line 521),
  so `dif_neg hs.ne'` cleanly discharges the active branch — no
  `Polynomial.eval` plumbing yet, just a definitional unfold. This
  means D.12a/b stop at `det.eval ξ` and do not touch the genuinely
  hard `eval ∘ det ∘ updateRow` distribution.
- D.11a/b/c expose the substituted RHS in terms of `rowFAlphaResidual
  m l . eval ξ` (`Matrix.vecMul` against `charmatrix.adjugate * map C`).
  This is precisely the residual shape cycle 716 noted is opaque to
  current tactics.

## Suggested next approach
Cycle 720 has two reasonable directions:
1. **`rowYQuot.det.eval` distribution**: push `Polynomial.eval ξ`
   through the `Matrix.det` of the `updateRow` shape from D.12a/b.
   Likely via `Matrix.det_eval` / `Polynomial.eval_det` or by
   expanding along the updated row (`Matrix.det_updateRow_eq_zero`-
   style cofactor expansion). The updated row is constant
   (`Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ)`), so cofactor
   expansion across that row gives `Σ_k C(-α k) * eval ξ of
   (s-1)-minor` — promising but needs a local helper.
2. **`rowFAlphaResidual.eval` distribution**: tackle the
   `vecMul ∘ adjugate ∘ map C` opaque path. Strategy explicitly
   defers this; needs a dedicated cycle with a focused helper for
   `eval ∘ adjugate` commutation.

Direction (1) is the lower-risk next cycle since cofactor expansion
along a `C`-constant row is a standard Mathlib pattern
(`Matrix.det_succ_row_zero` / `Matrix.det_updateRow_smul`).
