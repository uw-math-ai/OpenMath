/-
Cycle 147 Aristotle job: close `doublyCompanionMatrix_det_factorization_n_five`,
i.e. Theorem 550A specialized at n = 5.

This is the fifth concrete-n axiom-clean stepping stone for thm:550A.
The n=1, 2, 3, 4 cases have already been closed in Section550.lean
(see the proofs included verbatim below as templates).

## Theorem statement at n = 5

For the doubly companion matrix X built from α, β : Fin 5 → ℂ, namely

    X = [[-α 0, -α 1, -α 2, -α 3, -α 4 - β 4],
         [1,    0,    0,    0,    -β 3      ],
         [0,    1,    0,    0,    -β 2      ],
         [0,    0,    1,    0,    -β 1      ],
         [0,    0,    0,    1,    -β 0      ]]

we expect (after `Matrix.det_succ_row_zero` twice + `Matrix.det_fin_three`)

    det(I - z X) = 1 + (α 0 + β 0) z + (α 0·β 0 + α 1 + β 1) z²
                     + (α 0·β 1 + α 1·β 0 + α 2 + β 2) z³
                     + (α 0·β 2 + α 1·β 1 + α 2·β 0 + α 3 + β 3) z⁴
                     + (α 0·β 3 + α 1·β 2 + α 2·β 1 + α 3·β 0 + α 4 + β 4) z⁵

while

    α(z)·β(z) = (above polynomial)
                  + (α 0·β 4 + α 1·β 3 + α 2·β 2 + α 3·β 1 + α 4·β 0) z⁶
                  + (α 1·β 4 + α 2·β 3 + α 3·β 2 + α 4·β 1) z⁷
                  + (α 2·β 4 + α 3·β 3 + α 4·β 2) z⁸
                  + (α 3·β 4 + α 4·β 3) z⁹
                  + (α 4·β 4) z¹⁰

So the residue is

  -[(α 0·β 4 + α 1·β 3 + α 2·β 2 + α 3·β 1 + α 4·β 0) z⁶
    + (α 1·β 4 + α 2·β 3 + α 3·β 2 + α 4·β 1) z⁷
    + (α 2·β 4 + α 3·β 3 + α 4·β 2) z⁸
    + (α 3·β 4 + α 4·β 3) z⁹
    + (α 4·β 4) z¹⁰]
 = O(z⁶) = O(z^{5+1}) as z → 0 in ℂ.

## Suggested proof structure (copy of cycle 145 n=4 template)

1. Pointwise rewrite the residue as `z^6 * inner_poly` via:
   (i)   Reduce `doublyCompanionMatrix α β` to an explicit `!![...]` 5×5 matrix.
   (ii)  Reduce `1 - z • X` to an explicit 5×5 `!![...]`.
   (iii) Expand the 5×5 determinant via `Matrix.det_succ_row_zero`,
         then expand each 4×4 minor via `Matrix.det_succ_row_zero` again,
         then use `Matrix.det_fin_three` for the 3×3 sub-determinants.
         Close with `simp` + `ring`.
2. Apply `Asymptotics.IsBigO.of_bound` with the sum of the absolute values
   of the five inner-polynomial coefficients (the convolutions above).
3. Bound `‖a + y·b + y²·c + y³·d + y⁴·e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖`
   for `‖y‖ ≤ 1` via `norm_add_le` cascade and `mul_le_of_le_one_left`.

For reference, the n=4 closed-form proof is included below.
-/

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

namespace OpenMath.Chapter5.Section550

open Asymptotics

def doublyCompanionMatrix {n : ℕ} (α β : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j =>
  if h0 : i.val = 0 then
    if hj : j.val + 1 = n then
      -α ⟨n - 1, by omega⟩ - β ⟨n - 1, by omega⟩
    else
      -α j
  else if hj : j.val + 1 = n then
    -β ⟨n - i.val - 1, by omega⟩
  else if i.val = j.val + 1 then
    1
  else
    0

noncomputable def alphaPoly {n : ℕ} (α : Fin n → ℂ) (z : ℂ) : ℂ :=
  1 + ∑ i : Fin n, α i * z ^ (i.val + 1)

noncomputable def betaPoly {n : ℕ} (β : Fin n → ℂ) (z : ℂ) : ℂ :=
  1 + ∑ i : Fin n, β i * z ^ (i.val + 1)

/-- The n=4 stepping stone — INCLUDED AS A TEMPLATE for the n=5 proof. -/
theorem doublyCompanionMatrix_det_factorization_n_four
    (α β : Fin 4 → ℂ) :
    Asymptotics.IsBigO (nhds (0 : ℂ))
      (fun z : ℂ =>
        (1 - z • doublyCompanionMatrix α β).det
          - alphaPoly α z * betaPoly β z)
      (fun z : ℂ => z ^ 5) := by
  have h_diff : (fun z : ℂ =>
      (1 - z • doublyCompanionMatrix α β).det
        - alphaPoly α z * betaPoly β z)
      = (fun z : ℂ => z ^ 5 *
          (-(α 0 * β 3) - α 1 * β 2 - α 2 * β 1 - α 3 * β 0
            + z * (-(α 1 * β 3) - α 2 * β 2 - α 3 * β 1)
            + z ^ 2 * (-(α 2 * β 3) - α 3 * β 2)
            + z ^ 3 * (-(α 3 * β 3)))) := by
    funext z
    have hX : doublyCompanionMatrix α β =
        !![-α 0, -α 1, -α 2, -α 3 - β 3;
           1,     0,    0,    -β 2;
           0,     1,    0,    -β 1;
           0,     0,    1,    -β 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [doublyCompanionMatrix]
    rw [hX]
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
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_four, Matrix.det_fin_three, alphaPoly, betaPoly,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.submatrix_apply, Fin.succ_zero_eq_one,
      Matrix.cons_val_fin_one, Fin.succAbove]
    ring
  rw [h_diff]
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
  rw [norm_mul]
  calc ‖y ^ 5‖ * ‖a + y * b + y ^ 2 * c + y ^ 3 * d‖
      ≤ ‖y ^ 5‖ * (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) :=
        mul_le_mul_of_nonneg_left h_inner (norm_nonneg _)
    _ = (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) * ‖y ^ 5‖ := by ring

/-- **Cycle 147 target — Theorem 550A at n = 5.** Close this `sorry`. -/
theorem doublyCompanionMatrix_det_factorization_n_five
    (α β : Fin 5 → ℂ) :
    Asymptotics.IsBigO (nhds (0 : ℂ))
      (fun z : ℂ =>
        (1 - z • doublyCompanionMatrix α β).det
          - alphaPoly α z * betaPoly β z)
      (fun z : ℂ => z ^ 6) := by
  sorry

end OpenMath.Chapter5.Section550
