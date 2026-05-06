# Cycle 145 Results

## Worked on

Priority 1: `thm:550A` n = 4 stepping stone — added axiom-clean
`doublyCompanionMatrix_det_factorization_n_four` in
`OpenMath/Chapter5/Section550.lean`.

## Approach

Followed the cycle 144 n = 3 template verbatim:

1. Computed paper algebra first. The doubly companion matrix at n = 4 is
   ```
   X = !![−α 0, −α 1, −α 2, −α 3 − β 3;
          1,    0,    0,    −β 2;
          0,    1,    0,    −β 1;
          0,    0,    1,    −β 0]
   ```
   `1 − z·X` becomes
   ```
   !![1+z·α 0,  z·α 1,  z·α 2,  z·(α 3 + β 3);
      −z,       1,      0,      z·β 2;
      0,       −z,      1,      z·β 1;
      0,        0,     −z,      1+z·β 0]
   ```
   Expanding `det(1 − z·X)` via Laplace along row 0 (expand each 3×3 minor
   manually) gives a polynomial of degree exactly 4. The product
   `α(z)·β(z)` matches it through `z⁴` and adds four extra terms `z⁵..z⁸`.
   Hence the residue is `−z⁵·(a + z·b + z²·c + z³·d)` with
   * `a = α 0·β 3 + α 1·β 2 + α 2·β 1 + α 3·β 0` (textbook convolution)
   * `b = α 1·β 3 + α 2·β 2 + α 3·β 1`
   * `c = α 2·β 3 + α 3·β 2`
   * `d = α 3·β 3`

2. Lean encoding used the cycle 144 template:
   * `funext z; ext i j; fin_cases i <;> fin_cases j <;> simp [doublyCompanionMatrix]`
     to extract `X` as an explicit `!![…]` matrix.
   * Same trick to extract `1 − z·X` as an explicit `!![…]` matrix.
   * **Mathlib has no `Matrix.det_fin_four`** — only `det_fin_three` exists
     (verified by `Grep` over `Mathlib/LinearAlgebra/Matrix/Determinant`).
     Used `Matrix.det_succ_row_zero` to reduce the 4×4 determinant to a
     sum of four signed 3×3-minor determinants, then `simp` with
     `[Matrix.det_fin_three, Fin.sum_univ_four, …]` to evaluate; final
     `ring` closes the polynomial identity.
   * `IsBigO.of_bound` with constant `‖a‖+‖b‖+‖c‖+‖d‖`, localised by
     `Metric.eventually_nhds_iff` to `‖y‖ < 1`.
   * Inner-factor norm bound via `linarith` over three intermediate
     `norm_add_le` lemmas plus three `mul_le_of_le_one_left`-derived
     bounds on `‖y·b‖`, `‖y²·c‖`, `‖y³·d‖`.
   * Final calc multiplies through by `‖y⁵‖`, restructured per cycle 144
     dead end #3 to put the bound constant on the right via `_ = (…) *
     ‖y^5‖ := by ring`.

## Result

SUCCESS. The new theorem
`OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization_n_four`
compiles axiom-clean. `lean_verify` returns the standard kernel set
`[propext, Classical.choice, Quot.sound]` only. Sorry count remains 0.

## Faithfulness check

For the new theorem `doublyCompanionMatrix_det_factorization_n_four`:

* Entity ID: `thm:550A` (specialised to `n = 4`).
* Textbook statement (quoted from `formalization_data/entities/thm_550A.json`):
  > The coefficients in the characteristic polynomial of `X`,
  > `det(wI − X) = wⁿ + γ₁wⁿ⁻¹ + γ₂wⁿ⁻² + ⋯ + γₙ`, are given by
  > `1 + γ₁z + γ₂z² + ⋯ + γₙzⁿ = det(I − zX) = α(z)β(z) + O(zⁿ⁺¹)`.
* Lean statement captures: **same content** at the specialised `n = 4`.
  The Lean conclusion
  `(1 - z • doublyCompanionMatrix α β).det − alphaPoly α z * betaPoly β z =O[nhds 0] (z ↦ z^5)`
  is the textbook `det(I − zX) − α(z)β(z) = O(z^{n+1})` with `n + 1 = 5`.
* Hypothesis strength: only `α β : Fin 4 → ℂ`, the data of the doubly
  companion matrix construction. No extra hypotheses.
* Tautology check: conclusion is `IsBigO …`, never appears as a
  hypothesis (there are none beyond the data).
* Identity check: proof is multi-step (paper-algebra reduction +
  determinant expansion + asymptotic bound), not `exact h`.

## Dead ends

None this cycle — paper algebra was verified before touching Lean, and
the cycle 144 template ported on the first try. The strategy's
"fallback if `det_fin_four` is absent" was needed (it is absent), and
`Matrix.det_succ_row_zero` + `simp [Matrix.det_fin_three, …]` + `ring`
closed it cleanly without raising `maxHeartbeats`.

One minor cleanup: the initial `simp` set included an unused
`Matrix.head_cons` (linter caught it); removed in the final commit.

## Discovery

* `Matrix.det_succ_row_zero` + `Matrix.det_fin_three` + a sufficiently
  rich `simp` lemma set (including `Matrix.cons_val_zero`,
  `Matrix.cons_val_one`, `Matrix.submatrix_apply`, `Fin.succ_zero_eq_one`,
  `Matrix.cons_val_fin_one`, `Fin.succAbove`) is the template for
  expanding 4×4 determinants of explicit `!![…]` matrices when no
  `det_fin_four` is available. This generalises the cycle 144 template
  beyond `n = 3` by one more rung at modest LOC cost.
* Cycle 144's `IsBigO.of_bound` template extends transparently from a
  three-term inner factor `a + z·b + z²·c` to a four-term inner factor
  `a + z·b + z²·c + z³·d`: same `linarith` over `norm_add_le` lemmas,
  one extra `mul_le_of_le_one_left` bound, one extra `‖d‖` summand.
  This pattern should extend to general `r` terms straightforwardly.

## Suggested next approach

* **n = 5 stepping stone**: continuing the same template gives a fifth
  data point and would test whether the `simp` lemma set scales (5×5
  determinant via `Matrix.det_succ_row_zero` twice, or once + sum over
  five 4×4 minors closed by ourselves the same way). Estimated
  ~250 LOC, possibly approaching `maxHeartbeats` — the planner should
  weigh whether one more concrete-`n` point materially advances vs.
  the closure-infrastructure work needed for general `n`.
* **Alternative**: pivot to one of the open backup priorities for
  cycle 145 (def:530A r = 3 heterogeneous-stages witness, def:520F r = 2
  negative L-stable witness). Both are smaller and broaden negative
  /heterogeneous coverage in the §5.2/§5.3 stability theory.
* **General-n path**: the clean leading-coefficient pattern
  `−Σᵢ αᵢ·β_{n−i} z^{n+1}` is now confirmed at four data points; an
  approach via `Matrix.det_succ_row_zero` recursive induction on `n`
  with a row/column-swap reduction may be more productive than the
  cofactor-expansion induction proposed in the deferral issue. The
  Aristotle Job A cancellation evidence (cycle 141) suggests prover-only
  attempts are not viable; manual scaffolding remains the path.
