import OpenMath.LMMTruncationOp
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAB12Convergence
import OpenMath.LMMAM11VectorConvergence

/-! ## Adams-Bashforth 12-step Vector Quantitative Convergence Chain (Iserles §1.2)

Finite-dimensional vector-valued analogue of the scalar AB12 quantitative
convergence chain in `OpenMath.LMMAB12Convergence`.
-/

namespace LMM

private lemma sum_univ_twelve_aux_vec {α : Type*} [AddCommMonoid α] (f : Fin 12 → α) :
    ∑ i : Fin 12, f i
      = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  simp [Fin.sum_univ_succ]
  ac_rfl

/-- AB12 vector iteration with twelve starting samples. -/
noncomputable def ab12IterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) : ℕ → E :=
  abIterVec 12 ab12GenericCoeff h f t₀
    ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁]

/-- Vector AB12 local truncation residual. -/
noncomputable def ab12VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 12 * h) - y (t + 11 * h)
    - h • ((4527766399 / 958003200 : ℝ) • deriv y (t + 11 * h)
          - (19433810163 / 958003200 : ℝ) • deriv y (t + 10 * h)
          + (61633227185 / 958003200 : ℝ) • deriv y (t + 9 * h)
          - (135579356757 / 958003200 : ℝ) • deriv y (t + 8 * h)
          + (214139355366 / 958003200 : ℝ) • deriv y (t + 7 * h)
          - (247741639374 / 958003200 : ℝ) • deriv y (t + 6 * h)
          + (211103573298 / 958003200 : ℝ) • deriv y (t + 5 * h)
          - (131365867290 / 958003200 : ℝ) • deriv y (t + 4 * h)
          + (58189107627 / 958003200 : ℝ) • deriv y (t + 3 * h)
          - (17410248271 / 958003200 : ℝ) • deriv y (t + 2 * h)
          + (3158642445 / 958003200 : ℝ) • deriv y (t + h)
          - (262747265 / 958003200 : ℝ) • deriv y t)

theorem ab12Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    ab12VecResidual h t y
      = y (t + 12 * h) - y (t + 11 * h)
          - h • ((4527766399 / 958003200 : ℝ) • deriv y (t + 11 * h)
                - (19433810163 / 958003200 : ℝ) • deriv y (t + 10 * h)
                + (61633227185 / 958003200 : ℝ) • deriv y (t + 9 * h)
                - (135579356757 / 958003200 : ℝ) • deriv y (t + 8 * h)
                + (214139355366 / 958003200 : ℝ) • deriv y (t + 7 * h)
                - (247741639374 / 958003200 : ℝ) • deriv y (t + 6 * h)
                + (211103573298 / 958003200 : ℝ) • deriv y (t + 5 * h)
                - (131365867290 / 958003200 : ℝ) • deriv y (t + 4 * h)
                + (58189107627 / 958003200 : ℝ) • deriv y (t + 3 * h)
                - (17410248271 / 958003200 : ℝ) • deriv y (t + 2 * h)
                + (3158642445 / 958003200 : ℝ) • deriv y (t + h)
                - (262747265 / 958003200 : ℝ) • deriv y t) := rfl

theorem ab12Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    abErrWindowVec (by norm_num : (1 : ℕ) ≤ 12) ab12GenericCoeff h f t₀
        ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] y (n + 1)
      ≤ (1 + h * ((443892 / 385) * L))
          * abErrWindowVec (by norm_num : (1 : ℕ) ≤ 12) ab12GenericCoeff h f t₀
              ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] y n
        + ‖abResidualVec 12 ab12GenericCoeff h y t₀ n‖ := by
  have hs : (1 : ℕ) ≤ 12 := by norm_num
  have hgeneric :=
    abIter_lipschitz_one_step_vec hs ab12GenericCoeff hh hL hf t₀
      ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] y hyf n
  rw [abLip_ab12GenericCoeff L] at hgeneric
  exact hgeneric

theorem ab12Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    abErrWindowVec (by norm_num : (1 : ℕ) ≤ 12) ab12GenericCoeff h f t₀
        ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] y (n + 1)
      ≤ (1 + h * ((443892 / 385) * L))
          * abErrWindowVec (by norm_num : (1 : ℕ) ≤ 12) ab12GenericCoeff h f t₀
              ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] y n
        + ‖abResidualVec 12 ab12GenericCoeff h y t₀ n‖ := by
  exact ab12Vec_one_step_lipschitz hh hL hf t₀
    y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y hyf n

/-- Packed Taylor polynomial for the y-remainder pattern in the AB12 vector proof. -/
private noncomputable def ab12Vec_yPoly13
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m h : ℝ) (d0 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t : E) : E :=
  (m * h) • d0
    + ((m * h) ^ 2 / 2) • d2t
    + ((m * h) ^ 3 / 6) • d3t
    + ((m * h) ^ 4 / 24) • d4t
    + ((m * h) ^ 5 / 120) • d5t
    + ((m * h) ^ 6 / 720) • d6t
    + ((m * h) ^ 7 / 5040) • d7t
    + ((m * h) ^ 8 / 40320) • d8t
    + ((m * h) ^ 9 / 362880) • d9t
    + ((m * h) ^ 10 / 3628800) • d10t
    + ((m * h) ^ 11 / 39916800) • d11t
    + ((m * h) ^ 12 / 479001600) • d12t

/-- Packed Taylor polynomial for the derivative-remainder pattern in the AB12 vector proof. -/
private noncomputable def ab12Vec_dPoly12
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m h : ℝ) (d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t : E) : E :=
  (m * h) • d2t
    + ((m * h) ^ 2 / 2) • d3t
    + ((m * h) ^ 3 / 6) • d4t
    + ((m * h) ^ 4 / 24) • d5t
    + ((m * h) ^ 5 / 120) • d6t
    + ((m * h) ^ 6 / 720) • d7t
    + ((m * h) ^ 7 / 5040) • d8t
    + ((m * h) ^ 8 / 40320) • d9t
    + ((m * h) ^ 9 / 362880) • d10t
    + ((m * h) ^ 10 / 3628800) • d11t
    + ((m * h) ^ 11 / 39916800) • d12t

private lemma ab12Vec_residual_alg_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y0 y11 y12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
        d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t : E) (h : ℝ)
    (A B C D F G I J K L P Q R : E)
    (hA : A = y12 - y0 - ab12Vec_yPoly13 12 h d0 d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hB : B = y11 - y0 - ab12Vec_yPoly13 11 h d0 d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hC : C = d11 - d0 - ab12Vec_dPoly12 11 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hD : D = d10 - d0 - ab12Vec_dPoly12 10 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hF : F = d9 - d0 - ab12Vec_dPoly12 9 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hG : G = d8 - d0 - ab12Vec_dPoly12 8 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hI : I = d7 - d0 - ab12Vec_dPoly12 7 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hJ : J = d6 - d0 - ab12Vec_dPoly12 6 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hK : K = d5 - d0 - ab12Vec_dPoly12 5 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hL : L = d4 - d0 - ab12Vec_dPoly12 4 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hP : P = d3 - d0 - ab12Vec_dPoly12 3 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hQ : Q = d2 - d0 - ab12Vec_dPoly12 2 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hR : R = d1 - d0 - ab12Vec_dPoly12 1 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t) :
    y12 - y11 - h • ((4527766399 / 958003200 : ℝ) • d11
                  - (19433810163 / 958003200 : ℝ) • d10
                  + (61633227185 / 958003200 : ℝ) • d9
                  - (135579356757 / 958003200 : ℝ) • d8
                  + (214139355366 / 958003200 : ℝ) • d7
                  - (247741639374 / 958003200 : ℝ) • d6
                  + (211103573298 / 958003200 : ℝ) • d5
                  - (131365867290 / 958003200 : ℝ) • d4
                  + (58189107627 / 958003200 : ℝ) • d3
                  - (17410248271 / 958003200 : ℝ) • d2
                  + (3158642445 / 958003200 : ℝ) • d1
                  - (262747265 / 958003200 : ℝ) • d0)
      = A - B
        - (4527766399 * h / 958003200 : ℝ) • C
        + (19433810163 * h / 958003200 : ℝ) • D
        - (61633227185 * h / 958003200 : ℝ) • F
        + (135579356757 * h / 958003200 : ℝ) • G
        - (214139355366 * h / 958003200 : ℝ) • I
        + (247741639374 * h / 958003200 : ℝ) • J
        - (211103573298 * h / 958003200 : ℝ) • K
        + (131365867290 * h / 958003200 : ℝ) • L
        - (58189107627 * h / 958003200 : ℝ) • P
        + (17410248271 * h / 958003200 : ℝ) • Q
        - (3158642445 * h / 958003200 : ℝ) • R := by
  subst hA; subst hB; subst hC; subst hD; subst hF; subst hG; subst hI
  subst hJ; subst hK; subst hL; subst hP; subst hQ; subst hR
  unfold ab12Vec_yPoly13 ab12Vec_dPoly12
  module

private lemma ab12Vec_residual_bound_alg_identity (M h : ℝ) :
    M / 6227020800 * (12 * h) ^ 13
      + M / 6227020800 * (11 * h) ^ 13
      + (4527766399 * h / 958003200) * (M / 479001600 * (11 * h) ^ 12)
      + (19433810163 * h / 958003200) * (M / 479001600 * (10 * h) ^ 12)
      + (61633227185 * h / 958003200) * (M / 479001600 * (9 * h) ^ 12)
      + (135579356757 * h / 958003200) * (M / 479001600 * (8 * h) ^ 12)
      + (214139355366 * h / 958003200) * (M / 479001600 * (7 * h) ^ 12)
      + (247741639374 * h / 958003200) * (M / 479001600 * (6 * h) ^ 12)
      + (211103573298 * h / 958003200) * (M / 479001600 * (5 * h) ^ 12)
      + (131365867290 * h / 958003200) * (M / 479001600 * (4 * h) ^ 12)
      + (58189107627 * h / 958003200) * (M / 479001600 * (3 * h) ^ 12)
      + (17410248271 * h / 958003200) * (M / 479001600 * (2 * h) ^ 12)
      + (3158642445 * h / 958003200) * (M / 479001600 * h ^ 12)
      = (171625746494360048711 / 1059216238080000 : ℝ) * M * h ^ 13 := by
  ring

private lemma ab12Vec_triangle_aux
    {E : Type*} [NormedAddCommGroup E]
    (A B C D F G I J K L P Q R : E) :
    ‖A - B - C + D - F + G - I + J - K + L - P + Q - R‖
      ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖F‖ + ‖G‖ + ‖I‖ + ‖J‖
          + ‖K‖ + ‖L‖ + ‖P‖ + ‖Q‖ + ‖R‖ := by
  have h1 : ‖A - B - C + D - F + G - I + J - K + L - P + Q - R‖
      ≤ ‖A - B - C + D - F + G - I + J - K + L - P + Q‖ + ‖R‖ := norm_sub_le _ _
  have h2 : ‖A - B - C + D - F + G - I + J - K + L - P + Q‖
      ≤ ‖A - B - C + D - F + G - I + J - K + L - P‖ + ‖Q‖ := norm_add_le _ _
  have h3 : ‖A - B - C + D - F + G - I + J - K + L - P‖
      ≤ ‖A - B - C + D - F + G - I + J - K + L‖ + ‖P‖ := norm_sub_le _ _
  have h4 : ‖A - B - C + D - F + G - I + J - K + L‖
      ≤ ‖A - B - C + D - F + G - I + J - K‖ + ‖L‖ := norm_add_le _ _
  have h5 : ‖A - B - C + D - F + G - I + J - K‖
      ≤ ‖A - B - C + D - F + G - I + J‖ + ‖K‖ := norm_sub_le _ _
  have h6 : ‖A - B - C + D - F + G - I + J‖
      ≤ ‖A - B - C + D - F + G - I‖ + ‖J‖ := norm_add_le _ _
  have h7 : ‖A - B - C + D - F + G - I‖
      ≤ ‖A - B - C + D - F + G‖ + ‖I‖ := norm_sub_le _ _
  have h8 : ‖A - B - C + D - F + G‖
      ≤ ‖A - B - C + D - F‖ + ‖G‖ := norm_add_le _ _
  have h9 : ‖A - B - C + D - F‖ ≤ ‖A - B - C + D‖ + ‖F‖ := norm_sub_le _ _
  have h10 : ‖A - B - C + D‖ ≤ ‖A - B - C‖ + ‖D‖ := norm_add_le _ _
  have h11 : ‖A - B - C‖ ≤ ‖A - B‖ + ‖C‖ := norm_sub_le _ _
  have h12 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  linarith

private lemma ab12Vec_residual_thirteen_term_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D F G I J K L P Q R : E) (h : ℝ) (hh : 0 ≤ h) :
    ‖A - B - (4527766399 * h / 958003200 : ℝ) • C
        + (19433810163 * h / 958003200 : ℝ) • D
        - (61633227185 * h / 958003200 : ℝ) • F
        + (135579356757 * h / 958003200 : ℝ) • G
        - (214139355366 * h / 958003200 : ℝ) • I
        + (247741639374 * h / 958003200 : ℝ) • J
        - (211103573298 * h / 958003200 : ℝ) • K
        + (131365867290 * h / 958003200 : ℝ) • L
        - (58189107627 * h / 958003200 : ℝ) • P
        + (17410248271 * h / 958003200 : ℝ) • Q
        - (3158642445 * h / 958003200 : ℝ) • R‖
      ≤ ‖A‖ + ‖B‖ + (4527766399 * h / 958003200) * ‖C‖
          + (19433810163 * h / 958003200) * ‖D‖
          + (61633227185 * h / 958003200) * ‖F‖
          + (135579356757 * h / 958003200) * ‖G‖
          + (214139355366 * h / 958003200) * ‖I‖
          + (247741639374 * h / 958003200) * ‖J‖
          + (211103573298 * h / 958003200) * ‖K‖
          + (131365867290 * h / 958003200) * ‖L‖
          + (58189107627 * h / 958003200) * ‖P‖
          + (17410248271 * h / 958003200) * ‖Q‖
          + (3158642445 * h / 958003200) * ‖R‖ := by
  have hcC_nn : 0 ≤ (4527766399 * h / 958003200 : ℝ) := by linarith
  have hcD_nn : 0 ≤ (19433810163 * h / 958003200 : ℝ) := by linarith
  have hcF_nn : 0 ≤ (61633227185 * h / 958003200 : ℝ) := by linarith
  have hcG_nn : 0 ≤ (135579356757 * h / 958003200 : ℝ) := by linarith
  have hcI_nn : 0 ≤ (214139355366 * h / 958003200 : ℝ) := by linarith
  have hcJ_nn : 0 ≤ (247741639374 * h / 958003200 : ℝ) := by linarith
  have hcK_nn : 0 ≤ (211103573298 * h / 958003200 : ℝ) := by linarith
  have hcL_nn : 0 ≤ (131365867290 * h / 958003200 : ℝ) := by linarith
  have hcP_nn : 0 ≤ (58189107627 * h / 958003200 : ℝ) := by linarith
  have hcQ_nn : 0 ≤ (17410248271 * h / 958003200 : ℝ) := by linarith
  have hcR_nn : 0 ≤ (3158642445 * h / 958003200 : ℝ) := by linarith
  have hC_norm :
      ‖(4527766399 * h / 958003200 : ℝ) • C‖
        = (4527766399 * h / 958003200) * ‖C‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcC_nn]
  have hD_norm :
      ‖(19433810163 * h / 958003200 : ℝ) • D‖
        = (19433810163 * h / 958003200) * ‖D‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcD_nn]
  have hF_norm :
      ‖(61633227185 * h / 958003200 : ℝ) • F‖
        = (61633227185 * h / 958003200) * ‖F‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcF_nn]
  have hG_norm :
      ‖(135579356757 * h / 958003200 : ℝ) • G‖
        = (135579356757 * h / 958003200) * ‖G‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcG_nn]
  have hI_norm :
      ‖(214139355366 * h / 958003200 : ℝ) • I‖
        = (214139355366 * h / 958003200) * ‖I‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcI_nn]
  have hJ_norm :
      ‖(247741639374 * h / 958003200 : ℝ) • J‖
        = (247741639374 * h / 958003200) * ‖J‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcJ_nn]
  have hK_norm :
      ‖(211103573298 * h / 958003200 : ℝ) • K‖
        = (211103573298 * h / 958003200) * ‖K‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcK_nn]
  have hL_norm :
      ‖(131365867290 * h / 958003200 : ℝ) • L‖
        = (131365867290 * h / 958003200) * ‖L‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcL_nn]
  have hP_norm :
      ‖(58189107627 * h / 958003200 : ℝ) • P‖
        = (58189107627 * h / 958003200) * ‖P‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcP_nn]
  have hQ_norm :
      ‖(17410248271 * h / 958003200 : ℝ) • Q‖
        = (17410248271 * h / 958003200) * ‖Q‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcQ_nn]
  have hR_norm :
      ‖(3158642445 * h / 958003200 : ℝ) • R‖
        = (3158642445 * h / 958003200) * ‖R‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcR_nn]
  have htri := ab12Vec_triangle_aux A B
    ((4527766399 * h / 958003200 : ℝ) • C)
    ((19433810163 * h / 958003200 : ℝ) • D)
    ((61633227185 * h / 958003200 : ℝ) • F)
    ((135579356757 * h / 958003200 : ℝ) • G)
    ((214139355366 * h / 958003200 : ℝ) • I)
    ((247741639374 * h / 958003200 : ℝ) • J)
    ((211103573298 * h / 958003200 : ℝ) • K)
    ((131365867290 * h / 958003200 : ℝ) • L)
    ((58189107627 * h / 958003200 : ℝ) • P)
    ((17410248271 * h / 958003200 : ℝ) • Q)
    ((3158642445 * h / 958003200 : ℝ) • R)
  rw [hC_norm, hD_norm, hF_norm, hG_norm, hI_norm, hJ_norm, hK_norm, hL_norm,
    hP_norm, hQ_norm, hR_norm] at htri
  exact htri

private lemma ab12Vec_residual_combine_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D F G I J K L P Q R : E) (M h : ℝ) (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (hA_bd : ‖A‖ ≤ M / 6227020800 * (12 * h) ^ 13)
    (hB_bd : ‖B‖ ≤ M / 6227020800 * (11 * h) ^ 13)
    (hC_bd : ‖C‖ ≤ M / 479001600 * (11 * h) ^ 12)
    (hD_bd : ‖D‖ ≤ M / 479001600 * (10 * h) ^ 12)
    (hF_bd : ‖F‖ ≤ M / 479001600 * (9 * h) ^ 12)
    (hG_bd : ‖G‖ ≤ M / 479001600 * (8 * h) ^ 12)
    (hI_bd : ‖I‖ ≤ M / 479001600 * (7 * h) ^ 12)
    (hJ_bd : ‖J‖ ≤ M / 479001600 * (6 * h) ^ 12)
    (hK_bd : ‖K‖ ≤ M / 479001600 * (5 * h) ^ 12)
    (hL_bd : ‖L‖ ≤ M / 479001600 * (4 * h) ^ 12)
    (hP_bd : ‖P‖ ≤ M / 479001600 * (3 * h) ^ 12)
    (hQ_bd : ‖Q‖ ≤ M / 479001600 * (2 * h) ^ 12)
    (hR_bd : ‖R‖ ≤ M / 479001600 * h ^ 12) :
    ‖A - B - (4527766399 * h / 958003200 : ℝ) • C
        + (19433810163 * h / 958003200 : ℝ) • D
        - (61633227185 * h / 958003200 : ℝ) • F
        + (135579356757 * h / 958003200 : ℝ) • G
        - (214139355366 * h / 958003200 : ℝ) • I
        + (247741639374 * h / 958003200 : ℝ) • J
        - (211103573298 * h / 958003200 : ℝ) • K
        + (131365867290 * h / 958003200 : ℝ) • L
        - (58189107627 * h / 958003200 : ℝ) • P
        + (17410248271 * h / 958003200 : ℝ) • Q
        - (3158642445 * h / 958003200 : ℝ) • R‖
      ≤ 162031 * M * h ^ 13 := by
  have htri := ab12Vec_residual_thirteen_term_triangle A B C D F G I J K L P Q R h hh
  have hcC_nn : 0 ≤ 4527766399 * h / 958003200 := by linarith
  have hcD_nn : 0 ≤ 19433810163 * h / 958003200 := by linarith
  have hcF_nn : 0 ≤ 61633227185 * h / 958003200 := by linarith
  have hcG_nn : 0 ≤ 135579356757 * h / 958003200 := by linarith
  have hcI_nn : 0 ≤ 214139355366 * h / 958003200 := by linarith
  have hcJ_nn : 0 ≤ 247741639374 * h / 958003200 := by linarith
  have hcK_nn : 0 ≤ 211103573298 * h / 958003200 := by linarith
  have hcL_nn : 0 ≤ 131365867290 * h / 958003200 := by linarith
  have hcP_nn : 0 ≤ 58189107627 * h / 958003200 := by linarith
  have hcQ_nn : 0 ≤ 17410248271 * h / 958003200 := by linarith
  have hcR_nn : 0 ≤ 3158642445 * h / 958003200 := by linarith
  have hCbd_s : (4527766399 * h / 958003200) * ‖C‖
      ≤ (4527766399 * h / 958003200) * (M / 479001600 * (11 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hC_bd hcC_nn
  have hDbd_s : (19433810163 * h / 958003200) * ‖D‖
      ≤ (19433810163 * h / 958003200) * (M / 479001600 * (10 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hD_bd hcD_nn
  have hFbd_s : (61633227185 * h / 958003200) * ‖F‖
      ≤ (61633227185 * h / 958003200) * (M / 479001600 * (9 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hF_bd hcF_nn
  have hGbd_s : (135579356757 * h / 958003200) * ‖G‖
      ≤ (135579356757 * h / 958003200) * (M / 479001600 * (8 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hG_bd hcG_nn
  have hIbd_s : (214139355366 * h / 958003200) * ‖I‖
      ≤ (214139355366 * h / 958003200) * (M / 479001600 * (7 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hI_bd hcI_nn
  have hJbd_s : (247741639374 * h / 958003200) * ‖J‖
      ≤ (247741639374 * h / 958003200) * (M / 479001600 * (6 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hJ_bd hcJ_nn
  have hKbd_s : (211103573298 * h / 958003200) * ‖K‖
      ≤ (211103573298 * h / 958003200) * (M / 479001600 * (5 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hK_bd hcK_nn
  have hLbd_s : (131365867290 * h / 958003200) * ‖L‖
      ≤ (131365867290 * h / 958003200) * (M / 479001600 * (4 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hL_bd hcL_nn
  have hPbd_s : (58189107627 * h / 958003200) * ‖P‖
      ≤ (58189107627 * h / 958003200) * (M / 479001600 * (3 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hP_bd hcP_nn
  have hQbd_s : (17410248271 * h / 958003200) * ‖Q‖
      ≤ (17410248271 * h / 958003200) * (M / 479001600 * (2 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hQ_bd hcQ_nn
  have hRbd_s : (3158642445 * h / 958003200) * ‖R‖
      ≤ (3158642445 * h / 958003200) * (M / 479001600 * h ^ 12) :=
    mul_le_mul_of_nonneg_left hR_bd hcR_nn
  have hbound_alg := ab12Vec_residual_bound_alg_identity M h
  have hh13_nn : 0 ≤ h ^ 13 := by positivity
  have hMh13_nn : 0 ≤ M * h ^ 13 := mul_nonneg hMnn hh13_nn
  have hslack : (171625746494360048711 / 1059216238080000 : ℝ) * M * h ^ 13
      ≤ 162031 * M * h ^ 13 := by
    rw [mul_assoc, mul_assoc (162031 : ℝ)]
    have hle : (171625746494360048711 / 1059216238080000 : ℝ) ≤ 162031 := by
      norm_num
    exact mul_le_mul_of_nonneg_right hle hMh13_nn
  linarith [htri, hbound_alg, hslack, hA_bd, hB_bd, hCbd_s, hDbd_s, hFbd_s,
    hGbd_s, hIbd_s, hJbd_s, hKbd_s, hLbd_s, hPbd_s, hQbd_s, hRbd_s]

theorem ab12Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 13 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 13 y t‖ ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (ht6h : t + 6 * h ∈ Set.Icc a b)
    (ht7h : t + 7 * h ∈ Set.Icc a b)
    (ht8h : t + 8 * h ∈ Set.Icc a b)
    (ht9h : t + 9 * h ∈ Set.Icc a b)
    (ht10h : t + 10 * h ∈ Set.Icc a b)
    (ht11h : t + 11 * h ∈ Set.Icc a b)
    (ht12h : t + 12 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖ab12VecResidual h t y‖ ≤ (162031 : ℝ) * M * h ^ 13 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  have h8h : 0 ≤ 8 * h := by linarith
  have h9h : 0 ≤ 9 * h := by linarith
  have h10h : 0 ≤ 10 * h := by linarith
  have h11h : 0 ≤ 11 * h := by linarith
  have h12h : 0 ≤ 12 * h := by linarith
  have hRy11 :=
    y_thirteenth_order_taylor_remainder_vec hy hbnd ht ht11h h11h
  have hRy12 :=
    y_thirteenth_order_taylor_remainder_vec hy hbnd ht ht12h h12h
  have hRyp1 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht hth hh
  have hRyp2 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht7h h7h
  have hRyp8 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht8h h8h
  have hRyp9 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht9h h9h
  have hRyp10 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht10h h10h
  have hRyp11 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht11h h11h
  unfold ab12VecResidual
  set y0 : E := y t with hy0_def
  set y11 : E := y (t + 11 * h) with hy11_def
  set y12 : E := y (t + 12 * h) with hy12_def
  set d0 : E := deriv y t with hd0_def
  set d1 : E := deriv y (t + h) with hd1_def
  set d2 : E := deriv y (t + 2 * h) with hd2_def
  set d3 : E := deriv y (t + 3 * h) with hd3_def
  set d4 : E := deriv y (t + 4 * h) with hd4_def
  set d5 : E := deriv y (t + 5 * h) with hd5_def
  set d6 : E := deriv y (t + 6 * h) with hd6_def
  set d7 : E := deriv y (t + 7 * h) with hd7_def
  set d8 : E := deriv y (t + 8 * h) with hd8_def
  set d9 : E := deriv y (t + 9 * h) with hd9_def
  set d10 : E := deriv y (t + 10 * h) with hd10_def
  set d11 : E := deriv y (t + 11 * h) with hd11_def
  set d2t : E := iteratedDeriv 2 y t with hd2t_def
  set d3t : E := iteratedDeriv 3 y t with hd3t_def
  set d4t : E := iteratedDeriv 4 y t with hd4t_def
  set d5t : E := iteratedDeriv 5 y t with hd5t_def
  set d6t : E := iteratedDeriv 6 y t with hd6t_def
  set d7t : E := iteratedDeriv 7 y t with hd7t_def
  set d8t : E := iteratedDeriv 8 y t with hd8t_def
  set d9t : E := iteratedDeriv 9 y t with hd9t_def
  set d10t : E := iteratedDeriv 10 y t with hd10t_def
  set d11t : E := iteratedDeriv 11 y t with hd11t_def
  set d12t : E := iteratedDeriv 12 y t with hd12t_def
  clear_value y0 y11 y12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
    d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t
  set A : E := y12 - y0 - ab12Vec_yPoly13 12 h d0 d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hA_def
  set B : E := y11 - y0 - ab12Vec_yPoly13 11 h d0 d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hB_def
  set C : E := d11 - d0 - ab12Vec_dPoly12 11 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hC_def
  set D : E := d10 - d0 - ab12Vec_dPoly12 10 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hD_def
  set F : E := d9 - d0 - ab12Vec_dPoly12 9 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hF_def
  set G : E := d8 - d0 - ab12Vec_dPoly12 8 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hG_def
  set I : E := d7 - d0 - ab12Vec_dPoly12 7 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hI_def
  set J : E := d6 - d0 - ab12Vec_dPoly12 6 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hJ_def
  set K : E := d5 - d0 - ab12Vec_dPoly12 5 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hK_def
  set L : E := d4 - d0 - ab12Vec_dPoly12 4 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hL_def
  set P : E := d3 - d0 - ab12Vec_dPoly12 3 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hP_def
  set Q : E := d2 - d0 - ab12Vec_dPoly12 2 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hQ_def
  set R : E := d1 - d0 - ab12Vec_dPoly12 1 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hR_def
  have hLTE_eq :=
    ab12Vec_residual_alg_identity y0 y11 y12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
      d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t h A B C D F G I J K L P Q R
      hA_def hB_def hC_def hD_def hF_def hG_def hI_def hJ_def hK_def hL_def
      hP_def hQ_def hR_def
  rw [hLTE_eq]
  have hA_bd : ‖A‖ ≤ M / 6227020800 * (12 * h) ^ 13 := by
    rw [hA_def]; unfold ab12Vec_yPoly13
    convert hRy12 using 2; module
  have hB_bd : ‖B‖ ≤ M / 6227020800 * (11 * h) ^ 13 := by
    rw [hB_def]; unfold ab12Vec_yPoly13
    convert hRy11 using 2; module
  have hC_bd : ‖C‖ ≤ M / 479001600 * (11 * h) ^ 12 := by
    rw [hC_def]; unfold ab12Vec_dPoly12
    convert hRyp11 using 2; module
  have hD_bd : ‖D‖ ≤ M / 479001600 * (10 * h) ^ 12 := by
    rw [hD_def]; unfold ab12Vec_dPoly12
    convert hRyp10 using 2; module
  have hF_bd : ‖F‖ ≤ M / 479001600 * (9 * h) ^ 12 := by
    rw [hF_def]; unfold ab12Vec_dPoly12
    convert hRyp9 using 2; module
  have hG_bd : ‖G‖ ≤ M / 479001600 * (8 * h) ^ 12 := by
    rw [hG_def]; unfold ab12Vec_dPoly12
    convert hRyp8 using 2; module
  have hI_bd : ‖I‖ ≤ M / 479001600 * (7 * h) ^ 12 := by
    rw [hI_def]; unfold ab12Vec_dPoly12
    convert hRyp7 using 2; module
  have hJ_bd : ‖J‖ ≤ M / 479001600 * (6 * h) ^ 12 := by
    rw [hJ_def]; unfold ab12Vec_dPoly12
    convert hRyp6 using 2; module
  have hK_bd : ‖K‖ ≤ M / 479001600 * (5 * h) ^ 12 := by
    rw [hK_def]; unfold ab12Vec_dPoly12
    convert hRyp5 using 2; module
  have hL_bd : ‖L‖ ≤ M / 479001600 * (4 * h) ^ 12 := by
    rw [hL_def]; unfold ab12Vec_dPoly12
    convert hRyp4 using 2; module
  have hP_bd : ‖P‖ ≤ M / 479001600 * (3 * h) ^ 12 := by
    rw [hP_def]; unfold ab12Vec_dPoly12
    convert hRyp3 using 2; module
  have hQ_bd : ‖Q‖ ≤ M / 479001600 * (2 * h) ^ 12 := by
    rw [hQ_def]; unfold ab12Vec_dPoly12
    convert hRyp2 using 2; module
  have hR_bd : ‖R‖ ≤ M / 479001600 * h ^ 12 := by
    rw [hR_def]; unfold ab12Vec_dPoly12
    convert hRyp1 using 2; module
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  clear_value A B C D F G I J K L P Q R
  exact ab12Vec_residual_combine_aux A B C D F G I J K L P Q R M h hh hMnn
    hA_bd hB_bd hC_bd hD_bd hF_bd hG_bd hI_bd hJ_bd hK_bd hL_bd hP_bd hQ_bd hR_bd

theorem ab12Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 13 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 12) * h ≤ T →
        ‖ab12VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 13 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_thirteen_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(162031 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh _hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 12) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 7 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht8h_mem : t + 8 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 8 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht9h_mem : t + 9 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 9 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht10h_mem : t + 10 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 10 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht11h_mem : t + 11 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 11 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht12h_mem : t + 12 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 12 * h = ((n : ℝ) + 12) * h := by ring
    linarith
  show ‖ab12VecResidual h t y‖ ≤ 162031 * M * h ^ 13
  exact ab12Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem ht9h_mem
    ht10h_mem ht11h_mem ht12h_mem hh.le

lemma ab12GenericCoeffVec :
    (fun j : Fin 12 => ab12GenericCoeff j) = ab12GenericCoeff := rfl

lemma abLip_ab12GenericCoeffVec (L : ℝ) :
    abLip 12 (fun j : Fin 12 => ab12GenericCoeff j) L = (443892 / 385) * L := by
  simpa using abLip_ab12GenericCoeff L

lemma ab12IterVec_eq_abIterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) (n : ℕ) :
    ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ n
      = abIterVec 12 ab12GenericCoeff h f t₀
          ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] n := rfl

lemma ab12VecResidual_eq_abResidualVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (y : ℝ → E) (t₀ : ℝ) (n : ℕ) :
    ab12VecResidual h (t₀ + (n : ℝ) * h) y
      = abResidualVec 12 ab12GenericCoeff h y t₀ n := by
  unfold ab12VecResidual abResidualVec
  rw [sum_univ_twelve_aux_vec, ab12GenericCoeff_zero, ab12GenericCoeff_one,
    ab12GenericCoeff_two, ab12GenericCoeff_three, ab12GenericCoeff_four,
    ab12GenericCoeff_five, ab12GenericCoeff_six, ab12GenericCoeff_seven,
    ab12GenericCoeff_eight, ab12GenericCoeff_nine, ab12GenericCoeff_ten,
    ab12GenericCoeff_eleven]
  have eA : t₀ + (n : ℝ) * h + 12 * h = t₀ + ((n + 12 : ℕ) : ℝ) * h := by
    push_cast; ring
  have eB :
      t₀ + (n : ℝ) * h + 11 * h = t₀ + ((n + 12 - 1 : ℕ) : ℝ) * h := by
    have hsub : (n + 12 - 1 : ℕ) = n + 11 := by omega
    rw [hsub]; push_cast; ring
  have eC : t₀ + (n : ℝ) * h
      = t₀ + ((n + ((0 : Fin 12) : ℕ) : ℕ) : ℝ) * h := by
    simp
  have eD : t₀ + (n : ℝ) * h + h
      = t₀ + ((n + ((1 : Fin 12) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eE : t₀ + (n : ℝ) * h + 2 * h
      = t₀ + ((n + ((2 : Fin 12) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eF : t₀ + (n : ℝ) * h + 3 * h
      = t₀ + ((n + ((3 : Fin 12) : ℕ) : ℕ) : ℝ) * h := by
    have : ((3 : Fin 12) : ℕ) = 3 := rfl
    rw [this]; push_cast; ring
  have eG : t₀ + (n : ℝ) * h + 4 * h
      = t₀ + ((n + ((4 : Fin 12) : ℕ) : ℕ) : ℝ) * h := by
    have : ((4 : Fin 12) : ℕ) = 4 := rfl
    rw [this]; push_cast; ring
  have eH : t₀ + (n : ℝ) * h + 5 * h
      = t₀ + ((n + ((5 : Fin 12) : ℕ) : ℕ) : ℝ) * h := by
    have : ((5 : Fin 12) : ℕ) = 5 := rfl
    rw [this]; push_cast; ring
  have eI : t₀ + (n : ℝ) * h + 6 * h
      = t₀ + ((n + ((6 : Fin 12) : ℕ) : ℕ) : ℝ) * h := by
    have : ((6 : Fin 12) : ℕ) = 6 := rfl
    rw [this]; push_cast; ring
  have eJ : t₀ + (n : ℝ) * h + 7 * h
      = t₀ + ((n + ((7 : Fin 12) : ℕ) : ℕ) : ℝ) * h := by
    have : ((7 : Fin 12) : ℕ) = 7 := rfl
    rw [this]; push_cast; ring
  have eK : t₀ + (n : ℝ) * h + 8 * h
      = t₀ + ((n + ((8 : Fin 12) : ℕ) : ℕ) : ℝ) * h := by
    have : ((8 : Fin 12) : ℕ) = 8 := rfl
    rw [this]; push_cast; ring
  have eL : t₀ + (n : ℝ) * h + 9 * h
      = t₀ + ((n + ((9 : Fin 12) : ℕ) : ℕ) : ℝ) * h := by
    have : ((9 : Fin 12) : ℕ) = 9 := rfl
    rw [this]; push_cast; ring
  have eM : t₀ + (n : ℝ) * h + 10 * h
      = t₀ + ((n + ((10 : Fin 12) : ℕ) : ℕ) : ℝ) * h := by
    have : ((10 : Fin 12) : ℕ) = 10 := rfl
    rw [this]; push_cast; ring
  have eN : t₀ + (n : ℝ) * h + 11 * h
      = t₀ + ((n + ((11 : Fin 12) : ℕ) : ℕ) : ℝ) * h := by
    have : ((11 : Fin 12) : ℕ) = 11 := rfl
    rw [this]; push_cast; ring
  rw [← eA, ← eB, ← eC, ← eD, ← eE, ← eF, ← eG, ← eH, ← eI, ← eJ, ← eK,
    ← eL, ← eM, ← eN]
  rw [show (-(262747265 : ℝ) / 958003200) • deriv y (t₀ + (n : ℝ) * h)
        = -((262747265 / 958003200 : ℝ) • deriv y (t₀ + (n : ℝ) * h)) by
    rw [show (-(262747265 : ℝ) / 958003200) = -(262747265 / 958003200 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(17410248271 : ℝ) / 958003200) • deriv y (t₀ + (n : ℝ) * h + 2 * h)
        = -((17410248271 / 958003200 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 2 * h)) by
    rw [show (-(17410248271 : ℝ) / 958003200) = -(17410248271 / 958003200 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(131365867290 : ℝ) / 958003200) • deriv y (t₀ + (n : ℝ) * h + 4 * h)
        = -((131365867290 / 958003200 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 4 * h)) by
    rw [show (-(131365867290 : ℝ) / 958003200) = -(131365867290 / 958003200 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(247741639374 : ℝ) / 958003200) • deriv y (t₀ + (n : ℝ) * h + 6 * h)
        = -((247741639374 / 958003200 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 6 * h)) by
    rw [show (-(247741639374 : ℝ) / 958003200) = -(247741639374 / 958003200 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(135579356757 : ℝ) / 958003200) • deriv y (t₀ + (n : ℝ) * h + 8 * h)
        = -((135579356757 / 958003200 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 8 * h)) by
    rw [show (-(135579356757 : ℝ) / 958003200) = -(135579356757 / 958003200 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(19433810163 : ℝ) / 958003200) • deriv y (t₀ + (n : ℝ) * h + 10 * h)
        = -((19433810163 / 958003200 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 10 * h)) by
    rw [show (-(19433810163 : ℝ) / 958003200) = -(19433810163 / 958003200 : ℝ) by ring]
    exact neg_smul _ _]
  abel_nf

theorem ab12Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 13 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E} {ε₀ : ℝ}, 0 ≤ ε₀ →
      ‖y₀ - y t₀‖ ≤ ε₀ →
      ‖y₁ - y (t₀ + h)‖ ≤ ε₀ →
      ‖y₂ - y (t₀ + 2 * h)‖ ≤ ε₀ →
      ‖y₃ - y (t₀ + 3 * h)‖ ≤ ε₀ →
      ‖y₄ - y (t₀ + 4 * h)‖ ≤ ε₀ →
      ‖y₅ - y (t₀ + 5 * h)‖ ≤ ε₀ →
      ‖y₆ - y (t₀ + 6 * h)‖ ≤ ε₀ →
      ‖y₇ - y (t₀ + 7 * h)‖ ≤ ε₀ →
      ‖y₈ - y (t₀ + 8 * h)‖ ≤ ε₀ →
      ‖y₉ - y (t₀ + 9 * h)‖ ≤ ε₀ →
      ‖y₁₀ - y (t₀ + 10 * h)‖ ≤ ε₀ →
      ‖y₁₁ - y (t₀ + 11 * h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 11) * h ≤ T →
      ‖ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ N
          - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((443892 / 385) * L * T) * ε₀ + K * h ^ 12 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab12Vec_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((443892 / 385) * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ ε₀ hε₀
    he0_bd he1_bd he2_bd he3_bd he4_bd he5_bd he6_bd he7_bd he8_bd he9_bd
    he10_bd he11_bd N hNh
  set α : Fin 12 → ℝ := ab12GenericCoeff with hα_def
  set y₀_non : Fin 12 → E := ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁]
    with hy_non_def
  have hs : (1 : ℕ) ≤ 12 := by norm_num
  haveI : Nonempty (Fin 12) := ⟨⟨0, hs⟩⟩
  have hstart : abErrWindowVec hs α h f t₀ y₀_non y 0 ≤ ε₀ := by
    unfold abErrWindowVec
    apply Finset.sup'_le
    intro j _
    unfold abErrVec
    fin_cases j <;> simp [abIterVec, hy_non_def] <;> assumption
  have hres_gen : ∀ n : ℕ, n < N →
      ‖abResidualVec 12 α h y t₀ n‖ ≤ C * h ^ (12 + 1) := by
    intro n hn_lt
    have hcast : (n : ℝ) + 12 ≤ (N : ℝ) + 11 := by
      have : (n : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      linarith
    have hn12_le : ((n : ℝ) + 12) * h ≤ T := by
      have hmul : ((n : ℝ) + 12) * h ≤ ((N : ℝ) + 11) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith
    have hres := hresidual hh hδ_le n hn12_le
    rw [hα_def, ← ab12VecResidual_eq_abResidualVec (E := E) h y t₀ n]
    simpa using hres
  have hNh' : (N : ℝ) * h ≤ T := by
    have hmono : (N : ℝ) * h ≤ ((N : ℝ) + 11) * h := by
      have h1 : (N : ℝ) ≤ (N : ℝ) + 11 := by linarith
      exact mul_le_mul_of_nonneg_right h1 hh.le
    linarith
  have hgeneric :=
    ab_global_error_bound_generic_vec (p := 12) hs α hh.le hL hC_nn hf t₀
      y₀_non y hyf hε₀ hstart N hNh' hres_gen
  rw [show abLip 12 α L = (443892 / 385) * L from by
    rw [hα_def]; exact abLip_ab12GenericCoeff L] at hgeneric
  have hwindow_ge : abErrVec 12 α h f t₀ y₀_non y N
      ≤ abErrWindowVec hs α h f t₀ y₀_non y N := by
    show abErrVec 12 α h f t₀ y₀_non y (N + ((⟨0, hs⟩ : Fin 12) : ℕ))
        ≤ abErrWindowVec hs α h f t₀ y₀_non y N
    unfold abErrWindowVec
    exact Finset.le_sup' (b := ⟨0, hs⟩)
      (f := fun j : Fin 12 => abErrVec 12 α h f t₀ y₀_non y (N + (j : ℕ)))
      (Finset.mem_univ _)
  have hbridge :
      abIterVec 12 α h f t₀ y₀_non N
        = ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ N := by
    rw [hα_def, hy_non_def]
    rfl
  have habsErr :
      abErrVec 12 α h f t₀ y₀_non y N
        = ‖ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ N
            - y (t₀ + (N : ℝ) * h)‖ := by
    show ‖abIterVec 12 α h f t₀ y₀_non N - y (t₀ + (N : ℝ) * h)‖
        = ‖ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ N
            - y (t₀ + (N : ℝ) * h)‖
    rw [hbridge]
  show ‖ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ N
        - y (t₀ + (N : ℝ) * h)‖
      ≤ Real.exp ((443892 / 385) * L * T) * ε₀
        + T * Real.exp ((443892 / 385) * L * T) * C * h ^ 12
  linarith [hwindow_ge, hgeneric, habsErr.symm.le, habsErr.le]

end LMM
