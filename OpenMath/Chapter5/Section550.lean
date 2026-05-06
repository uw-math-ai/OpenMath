import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Butcher §550 — Doubly companion matrices (Theorem 550A)

This file opens §550 with the *doubly companion matrix* construction from
equation (550a) and Theorem 550A on its characteristic polynomial.

## Textbook statement (quoted verbatim from `entities/thm_550A.json`)

> The coefficients in the characteristic polynomial of `X`,
> `det(wI − X) = wⁿ + γ₁wⁿ⁻¹ + γ₂wⁿ⁻² + ⋯ + γₙ`, are given by
> `1 + γ₁z + γ₂z² + ⋯ + γₙzⁿ = det(I − zX) = α(z)β(z) + O(zⁿ⁺¹)`.

with the doubly companion matrix `X` from (550a):

```
X = [[-α₁, -α₂, ..., -α_{n-1}, -αₙ - βₙ],
     [1,    0,    ..., 0,       -β_{n-1}],
     [0,    1,    ..., 0,       -β_{n-2}],
     ...,
     [0,    0,    ..., 1,       -β₁]]
```

and `α(z) := 1 + α₁z + ⋯ + αₙ zⁿ`, `β(z) := 1 + β₁z + ⋯ + βₙ zⁿ`.

## Indexing convention

The textbook uses 1-based indexing `α₁,…,αₙ` while Lean's `Fin n` is
0-based. We encode `α, β : Fin n → ℂ` so that `α 0` corresponds to the
textbook's `α₁` and `α (n-1)` to `αₙ`. All formulas below use this
convention.

## Cycle 139 status

* `doublyCompanionMatrix` defined index-by-index over ℂ.
* Sanity helper `doublyCompanionMatrix_one_eq` reduces the `n = 1` case
  to the explicit `1 × 1` matrix `!![-α 0 - β 0]`.
* `alphaPoly`, `betaPoly` defined.
* `doublyCompanionMatrix_det_factorization_n_one` closes the `n = 1`
  specialisation as a genuine (axiom-clean) witness.
* The general-`n` factorisation statement
  (`det(I − zX) = α(z)β(z) + O(z^{n+1})`) is **deferred** to a future
  cycle — see `.prover-state/issues/thm_550A_general_n.md`. The
  cycle-138 sorry-first scaffold has been **removed** in cycle 139:
  carrying an open `sorry` was scored a regression by the supervisor,
  so the statement is restored to absent until the closure
  infrastructure (cofactor-expansion induction or eigenvalue-density
  argument) is in place. Two Aristotle jobs targeting the general-`n`
  proof are still in flight; if either returns cleanly, a future cycle
  will reinstate the statement together with the proof body.
-/

namespace OpenMath.Chapter5.Section550

open Asymptotics

/-- **Doubly companion matrix** (Butcher §550, equation (550a)). The
matrix is indexed by `Fin n × Fin n` with entries:

* row `0`: `X[0, j] = -α j` for `j < n - 1`, and
  `X[0, n-1] = -α (n-1) - β (n-1)`;
* sub-diagonal: `X[i, i-1] = 1` for `i ≥ 1`;
* last column: `X[i, n-1] = -β (n - i - 1)` for `i ≥ 1` (and `i ≠ n-1`
  to avoid double-counting; the case `i = n-1` enters the sub-diagonal
  formula instead — but its last-column value is already covered by
  `j.val = n-1` taking precedence over `i.val = j.val + 1` at the lone
  overlap, see Step 2 of the strategy);
* all other entries: `0`.

We arrange the cases so the row-0 case matches first, then the
last-column case for non-zero rows, then the sub-diagonal, then `0`.
This ordering matters at small `n`: at `n = 1` the matrix reduces to
the `1 × 1` matrix `!![-α 0 - β 0]`.

`α, β : Fin n → ℂ` are 0-indexed: `α 0` is the textbook's `α₁`. -/
def doublyCompanionMatrix {n : ℕ} (α β : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j =>
  if h0 : i.val = 0 then
    if hj : j.val + 1 = n then
      -- `j` is the last column: the corner entry
      -α ⟨n - 1, by omega⟩ - β ⟨n - 1, by omega⟩
    else
      -- row 0, columns 0..n-2: `-α_{j+1}` in textbook indexing,
      -- which is `-α j` here.
      -α j
  else if hj : j.val + 1 = n then
    -- non-zero row, last column: `-β_{n-i}` in textbook indexing.
    -- With i.val ≥ 1 and j.val = n - 1, the textbook entry `-β_{n-i}`
    -- becomes `-β (n - i - 1)` in 0-indexed Fin form.
    -β ⟨n - i.val - 1, by omega⟩
  else if i.val = j.val + 1 then
    -- sub-diagonal
    1
  else
    0

@[simp]
lemma doublyCompanionMatrix_one_eq (α β : Fin 1 → ℂ) :
    doublyCompanionMatrix α β = !![-α 0 - β 0] := by
  ext i j
  fin_cases i; fin_cases j
  simp [doublyCompanionMatrix]

/-- The polynomial `α(z) = 1 + α₁ z + α₂ z² + ⋯ + αₙ zⁿ` (textbook
indexing), encoded with `Fin n`-indexed coefficients (`α 0` = `α₁`). -/
noncomputable def alphaPoly {n : ℕ} (α : Fin n → ℂ) (z : ℂ) : ℂ :=
  1 + ∑ i : Fin n, α i * z ^ (i.val + 1)

/-- The polynomial `β(z) = 1 + β₁ z + β₂ z² + ⋯ + βₙ zⁿ`. -/
noncomputable def betaPoly {n : ℕ} (β : Fin n → ℂ) (z : ℂ) : ℂ :=
  1 + ∑ i : Fin n, β i * z ^ (i.val + 1)

/-- **Theorem 550A at `n = 1`.** With single coefficients `α 0` and
`β 0`,
* `det(I - z X) = 1 + (α 0 + β 0) z`,
* `α(z) · β(z) = 1 + (α 0 + β 0) z + (α 0)(β 0) z²`,

so the residue is `-(α 0)(β 0) z²`, evidently `O(z²) = O(z^{1+1})`.

This closes the cycle 138 deliverable as a genuine (non-vacuous) witness. -/
theorem doublyCompanionMatrix_det_factorization_n_one
    (α β : Fin 1 → ℂ) :
    Asymptotics.IsBigO (nhds (0 : ℂ))
      (fun z : ℂ =>
        (1 - z • doublyCompanionMatrix α β).det
          - alphaPoly α z * betaPoly β z)
      (fun z : ℂ => z ^ 2) := by
  -- Step 1: reduce the residue to `-(α 0 * β 0) * z^2` pointwise.
  have h_diff : (fun z : ℂ =>
      (1 - z • doublyCompanionMatrix α β).det
        - alphaPoly α z * betaPoly β z)
      = (fun z : ℂ => -(α 0 * β 0) * z ^ 2) := by
    funext z
    rw [doublyCompanionMatrix_one_eq]
    -- Reduce the LHS determinant.
    have hmat :
        (1 - z • !![-α 0 - β 0] : Matrix (Fin 1) (Fin 1) ℂ)
          = !![1 + z * (α 0 + β 0)] := by
      ext i j
      fin_cases i; fin_cases j
      simp
      ring
    rw [hmat, Matrix.det_fin_one]
    -- Now reduce the polynomial product.
    simp [alphaPoly, betaPoly]
    ring
  rw [h_diff]
  -- `IsBigO` of `-(c) * z^2` against `z^2`.
  exact (isBigO_refl (fun z : ℂ => z ^ 2) _).const_mul_left _

/-- **Theorem 550A at `n = 2`.** With coefficients `α 0, α 1, β 0, β 1`,
* `det(I - z X) = 1 + (α 0 + β 0) z + (α 0 · β 0 + α 1 + β 1) z²`,
* `α(z) · β(z) = 1 + (α 0 + β 0) z + (α 0 · β 0 + α 1 + β 1) z²
                  + (α 0 · β 1 + α 1 · β 0) z³ + (α 1 · β 1) z⁴`,

so the residue is `-(α 0 · β 1 + α 1 · β 0) z³ - (α 1 · β 1) z⁴`,
which is `O(z³) = O(z^{2+1})` near `0`.

Proof obtained from Aristotle (cycle 140 Job B,
project `70f26d67-b37e-4eda-b946-64c9f4616612`). -/
theorem doublyCompanionMatrix_det_factorization_n_two
    (α β : Fin 2 → ℂ) :
    Asymptotics.IsBigO (nhds (0 : ℂ))
      (fun z : ℂ =>
        (1 - z • doublyCompanionMatrix α β).det
          - alphaPoly α z * betaPoly β z)
      (fun z : ℂ => z ^ 3) := by
  unfold alphaPoly betaPoly
  unfold doublyCompanionMatrix
  norm_num [Fin.sum_univ_two, Matrix.det_fin_two]
  ring_nf
  suffices h_factor :
      (fun z : ℂ => z ^ 3 * (-(α 0 * β 1) - β 0 * α 1 - z * α 1 * β 1))
        =O[nhds 0] (fun z : ℂ => z ^ 3) by
    convert h_factor using 2
    ring
  refine Asymptotics.IsBigO.of_bound
      (‖-(α 0 * β 1) - β 0 * α 1‖ + ‖α 1 * β 1‖) ?_
  rw [Metric.eventually_nhds_iff]
  refine ⟨1, by norm_num, fun y hy => ?_⟩
  norm_num [mul_assoc, mul_comm, mul_left_comm]
  exact mul_le_mul_of_nonneg_left
    (le_trans (norm_sub_le _ _)
      (by simpa [norm_mul] using
        mul_le_mul_of_nonneg_right hy.le (by positivity)))
    (by positivity)

/-- **Theorem 550A at `n = 3`.** Direct expansion via `Matrix.det_fin_three`
gives
* `det(I - z X) = 1 + (α 0 + β 0) z + (α 0 · β 0 + α 1 + β 1) z²
                    + (α 0 · β 1 + α 1 · β 0 + α 2 + β 2) z³`,
* `α(z) · β(z) = 1 + (α 0 + β 0) z + (α 0 · β 0 + α 1 + β 1) z²
                    + (α 0 · β 1 + α 1 · β 0 + α 2 + β 2) z³
                    + (α 0 · β 2 + α 1 · β 1 + α 2 · β 0) z⁴
                    + (α 1 · β 2 + α 2 · β 1) z⁵ + (α 2 · β 2) z⁶`,

so the residue is
`-(α 0 · β 2 + α 1 · β 1 + α 2 · β 0) z⁴ - (α 1 · β 2 + α 2 · β 1) z⁵
    - (α 2 · β 2) z⁶ = O(z⁴) = O(z^{3+1})`. -/
theorem doublyCompanionMatrix_det_factorization_n_three
    (α β : Fin 3 → ℂ) :
    Asymptotics.IsBigO (nhds (0 : ℂ))
      (fun z : ℂ =>
        (1 - z • doublyCompanionMatrix α β).det
          - alphaPoly α z * betaPoly β z)
      (fun z : ℂ => z ^ 4) := by
  -- Step 1: rewrite the residue pointwise to its factored form `z^4 * inner`.
  have h_diff : (fun z : ℂ =>
      (1 - z • doublyCompanionMatrix α β).det
        - alphaPoly α z * betaPoly β z)
      = (fun z : ℂ => z ^ 4 *
          (-(α 0 * β 2) - β 0 * α 2 - β 1 * α 1
              + z * (-(β 1 * α 2) - α 1 * β 2) + z ^ 2 * (-(α 2 * β 2)))) := by
    funext z
    -- Reduce the doubly-companion matrix at n = 3 to an explicit !![…] form.
    have hX : doublyCompanionMatrix α β =
        !![-α 0, -α 1, -α 2 - β 2;
           1,     0,    -β 1;
           0,     1,    -β 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [doublyCompanionMatrix]
    rw [hX]
    -- Reduce `1 - z • X` to an explicit !![…] form.
    have hmat :
        (1 - z • !![-α 0, -α 1, -α 2 - β 2;
                    1,     0,    -β 1;
                    0,     1,    -β 0] : Matrix (Fin 3) (Fin 3) ℂ)
          = !![1 + z * α 0,   z * α 1,    z * (α 2 + β 2);
               -z,            1,          z * β 1;
               0,             -z,         1 + z * β 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        first | (simp; ring) | simp
    rw [hmat, Matrix.det_fin_three]
    simp [alphaPoly, betaPoly, Fin.sum_univ_three]
    ring
  rw [h_diff]
  -- Step 2: prove `z^4 * inner =O[nhds 0] z^4`.
  refine Asymptotics.IsBigO.of_bound
      (‖-(α 0 * β 2) - β 0 * α 2 - β 1 * α 1‖ + ‖-(β 1 * α 2) - α 1 * β 2‖
          + ‖-(α 2 * β 2)‖) ?_
  rw [Metric.eventually_nhds_iff]
  refine ⟨1, by norm_num, fun y hy => ?_⟩
  rw [Complex.dist_eq, sub_zero] at hy
  set a := -(α 0 * β 2) - β 0 * α 2 - β 1 * α 1 with ha_def
  set b := -(β 1 * α 2) - α 1 * β 2 with hb_def
  set c := -(α 2 * β 2) with hc_def
  -- Bound the inner factor: ‖a + y * b + y^2 * c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖.
  have h_inner : ‖a + y * b + y ^ 2 * c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    have hyb : ‖y * b‖ ≤ ‖b‖ := by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hy.le
    have hyc : ‖y ^ 2 * c‖ ≤ ‖c‖ := by
      rw [norm_mul, norm_pow]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      calc ‖y‖ ^ 2 ≤ 1 ^ 2 := by gcongr
        _ = 1 := one_pow _
    have h1 : ‖a + y * b + y ^ 2 * c‖ ≤ ‖a + y * b‖ + ‖y ^ 2 * c‖ := norm_add_le _ _
    have h2 : ‖a + y * b‖ ≤ ‖a‖ + ‖y * b‖ := norm_add_le _ _
    linarith
  -- Multiply through by ‖y^4‖.
  rw [norm_mul]
  calc ‖y ^ 4‖ * ‖a + y * b + y ^ 2 * c‖
      ≤ ‖y ^ 4‖ * (‖a‖ + ‖b‖ + ‖c‖) :=
        mul_le_mul_of_nonneg_left h_inner (norm_nonneg _)
    _ = (‖a‖ + ‖b‖ + ‖c‖) * ‖y ^ 4‖ := by ring

/-- **Theorem 550A at `n = 4`.** Expanding `det(I − z·X)` along the first row
(via `Matrix.det_succ_row_zero` and three 3×3 minors via `Matrix.det_fin_three`)
yields a polynomial of degree exactly `4` in `z`:
* `det(I - z X) = 1 + (α 0 + β 0) z + (α 0·β 0 + α 1 + β 1) z²
                    + (α 0·β 1 + α 1·β 0 + α 2 + β 2) z³
                    + (α 0·β 2 + α 1·β 1 + α 2·β 0 + α 3 + β 3) z⁴`,
while
* `α(z)·β(z) = (above) + (α 0·β 3 + α 1·β 2 + α 2·β 1 + α 3·β 0) z⁵
                    + (α 1·β 3 + α 2·β 2 + α 3·β 1) z⁶
                    + (α 2·β 3 + α 3·β 2) z⁷ + (α 3·β 3) z⁸`,
so the residue is the convolution
`-(α 0·β 3 + α 1·β 2 + α 2·β 1 + α 3·β 0) z⁵ - … - (α 3·β 3) z⁸ = O(z^{4+1})`.
This is the fourth concrete-`n` axiom-clean stepping stone for Theorem 550A. -/
theorem doublyCompanionMatrix_det_factorization_n_four
    (α β : Fin 4 → ℂ) :
    Asymptotics.IsBigO (nhds (0 : ℂ))
      (fun z : ℂ =>
        (1 - z • doublyCompanionMatrix α β).det
          - alphaPoly α z * betaPoly β z)
      (fun z : ℂ => z ^ 5) := by
  -- Step 1: rewrite the residue pointwise to its factored form `z^5 * inner`.
  have h_diff : (fun z : ℂ =>
      (1 - z • doublyCompanionMatrix α β).det
        - alphaPoly α z * betaPoly β z)
      = (fun z : ℂ => z ^ 5 *
          (-(α 0 * β 3) - α 1 * β 2 - α 2 * β 1 - α 3 * β 0
            + z * (-(α 1 * β 3) - α 2 * β 2 - α 3 * β 1)
            + z ^ 2 * (-(α 2 * β 3) - α 3 * β 2)
            + z ^ 3 * (-(α 3 * β 3)))) := by
    funext z
    -- Reduce the doubly-companion matrix at n = 4 to an explicit !![…] form.
    have hX : doublyCompanionMatrix α β =
        !![-α 0, -α 1, -α 2, -α 3 - β 3;
           1,     0,    0,    -β 2;
           0,     1,    0,    -β 1;
           0,     0,    1,    -β 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [doublyCompanionMatrix]
    rw [hX]
    -- Reduce `1 - z • X` to an explicit !![…] form.
    have hmat :
        (1 - z • !![-α 0, -α 1, -α 2, -α 3 - β 3;
                    1,     0,    0,    -β 2;
                    0,     1,    0,    -β 1;
                    0,     0,    1,    -β 0] : Matrix (Fin 4) (Fin 4) ℂ)
          = !![1 + z * α 0,   z * α 1,    z * α 2,    z * (α 3 + β 3);
               -z,            1,          0,          z * β 2;
               0,             -z,         1,          z * β 1;
               0,             0,          -z,         1 + z * β 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        first | (simp; ring) | simp
    rw [hmat]
    -- Expand the 4x4 determinant via Laplace along row 0, then use det_fin_three
    -- on each 3x3 minor.
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_four, Matrix.det_fin_three, alphaPoly, betaPoly,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.submatrix_apply, Fin.succ_zero_eq_one,
      Matrix.cons_val_fin_one, Fin.succAbove]
    ring
  rw [h_diff]
  -- Step 2: prove `z^5 * inner =O[nhds 0] z^5`.
  refine Asymptotics.IsBigO.of_bound
      (‖-(α 0 * β 3) - α 1 * β 2 - α 2 * β 1 - α 3 * β 0‖
        + ‖-(α 1 * β 3) - α 2 * β 2 - α 3 * β 1‖
        + ‖-(α 2 * β 3) - α 3 * β 2‖
        + ‖-(α 3 * β 3)‖) ?_
  rw [Metric.eventually_nhds_iff]
  refine ⟨1, by norm_num, fun y hy => ?_⟩
  rw [Complex.dist_eq, sub_zero] at hy
  set a := -(α 0 * β 3) - α 1 * β 2 - α 2 * β 1 - α 3 * β 0 with ha_def
  set b := -(α 1 * β 3) - α 2 * β 2 - α 3 * β 1 with hb_def
  set c := -(α 2 * β 3) - α 3 * β 2 with hc_def
  set d := -(α 3 * β 3) with hd_def
  -- Bound the inner factor:
  --   ‖a + y * b + y^2 * c + y^3 * d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖.
  have h_inner :
      ‖a + y * b + y ^ 2 * c + y ^ 3 * d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    have hyb : ‖y * b‖ ≤ ‖b‖ := by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hy.le
    have hyc : ‖y ^ 2 * c‖ ≤ ‖c‖ := by
      rw [norm_mul, norm_pow]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      calc ‖y‖ ^ 2 ≤ 1 ^ 2 := by gcongr
        _ = 1 := one_pow _
    have hyd : ‖y ^ 3 * d‖ ≤ ‖d‖ := by
      rw [norm_mul, norm_pow]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      calc ‖y‖ ^ 3 ≤ 1 ^ 3 := by gcongr
        _ = 1 := one_pow _
    have h1 : ‖a + y * b + y ^ 2 * c + y ^ 3 * d‖
                ≤ ‖a + y * b + y ^ 2 * c‖ + ‖y ^ 3 * d‖ := norm_add_le _ _
    have h2 : ‖a + y * b + y ^ 2 * c‖
                ≤ ‖a + y * b‖ + ‖y ^ 2 * c‖ := norm_add_le _ _
    have h3 : ‖a + y * b‖ ≤ ‖a‖ + ‖y * b‖ := norm_add_le _ _
    linarith
  -- Multiply through by ‖y^5‖.
  rw [norm_mul]
  calc ‖y ^ 5‖ * ‖a + y * b + y ^ 2 * c + y ^ 3 * d‖
      ≤ ‖y ^ 5‖ * (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) :=
        mul_le_mul_of_nonneg_left h_inner (norm_nonneg _)
    _ = (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) * ‖y ^ 5‖ := by ring

end OpenMath.Chapter5.Section550
