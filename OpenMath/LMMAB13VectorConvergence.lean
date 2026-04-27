import OpenMath.LMMTruncationOp
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAB13Convergence
import OpenMath.LMMAM12VectorConvergence

/-! ## Adams-Bashforth 13-step Vector Quantitative Convergence Chain (Iserles §1.2)

Finite-dimensional vector-valued analogue of the scalar AB13 quantitative
convergence chain in `OpenMath.LMMAB13Convergence`.
-/

namespace LMM

private lemma sum_univ_thirteen_aux_vec {α : Type*} [AddCommMonoid α] (f : Fin 13 → α) :
    ∑ i : Fin 13, f i
      = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10
          + f 11 + f 12 := by
  simp [Fin.sum_univ_succ]
  ac_rfl

/-- AB13 vector iteration with thirteen starting samples. -/
noncomputable def ab13IterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : E) : ℕ → E :=
  abIterVec 13 ab13GenericCoeff h f t₀
    ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂]

/-- Vector AB13 local truncation residual. -/
noncomputable def ab13VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 13 * h) - y (t + 12 * h)
    - h • ((13064406523627 / 2615348736000 : ℝ) • deriv y (t + 12 * h)
          - (61497552797274 / 2615348736000 : ℝ) • deriv y (t + 11 * h)
          + (214696591002612 / 2615348736000 : ℝ) • deriv y (t + 10 * h)
          - (524924579905150 / 2615348736000 : ℝ) • deriv y (t + 9 * h)
          + (932884546055895 / 2615348736000 : ℝ) • deriv y (t + 8 * h)
          - (1233589244941764 / 2615348736000 : ℝ) • deriv y (t + 7 * h)
          + (1226443086129408 / 2615348736000 : ℝ) • deriv y (t + 6 * h)
          - (915883387152444 / 2615348736000 : ℝ) • deriv y (t + 5 * h)
          + (507140369728425 / 2615348736000 : ℝ) • deriv y (t + 4 * h)
          - (202322913738370 / 2615348736000 : ℝ) • deriv y (t + 3 * h)
          + (55060974662412 / 2615348736000 : ℝ) • deriv y (t + 2 * h)
          - (9160551085734 / 2615348736000 : ℝ) • deriv y (t + h)
          + (703604254357 / 2615348736000 : ℝ) • deriv y t)

theorem ab13Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    ab13VecResidual h t y
      = y (t + 13 * h) - y (t + 12 * h)
          - h • ((13064406523627 / 2615348736000 : ℝ) • deriv y (t + 12 * h)
                - (61497552797274 / 2615348736000 : ℝ) • deriv y (t + 11 * h)
                + (214696591002612 / 2615348736000 : ℝ) • deriv y (t + 10 * h)
                - (524924579905150 / 2615348736000 : ℝ) • deriv y (t + 9 * h)
                + (932884546055895 / 2615348736000 : ℝ) • deriv y (t + 8 * h)
                - (1233589244941764 / 2615348736000 : ℝ) • deriv y (t + 7 * h)
                + (1226443086129408 / 2615348736000 : ℝ) • deriv y (t + 6 * h)
                - (915883387152444 / 2615348736000 : ℝ) • deriv y (t + 5 * h)
                + (507140369728425 / 2615348736000 : ℝ) • deriv y (t + 4 * h)
                - (202322913738370 / 2615348736000 : ℝ) • deriv y (t + 3 * h)
                + (55060974662412 / 2615348736000 : ℝ) • deriv y (t + 2 * h)
                - (9160551085734 / 2615348736000 : ℝ) • deriv y (t + h)
                + (703604254357 / 2615348736000 : ℝ) • deriv y t) := rfl

theorem ab13Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    abErrWindowVec (by norm_num : (1 : ℕ) ≤ 13) ab13GenericCoeff h f t₀
        ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂] y (n + 1)
      ≤ (1 + h * ((1439788039057 / 638512875) * L))
          * abErrWindowVec (by norm_num : (1 : ℕ) ≤ 13) ab13GenericCoeff h f t₀
              ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂] y n
        + ‖abResidualVec 13 ab13GenericCoeff h y t₀ n‖ := by
  have hs : (1 : ℕ) ≤ 13 := by norm_num
  have hgeneric :=
    abIter_lipschitz_one_step_vec hs ab13GenericCoeff hh hL hf t₀
      ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂] y hyf n
  rw [abLip_ab13GenericCoeff L] at hgeneric
  exact hgeneric

theorem ab13Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    abErrWindowVec (by norm_num : (1 : ℕ) ≤ 13) ab13GenericCoeff h f t₀
        ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂] y (n + 1)
      ≤ (1 + h * ((1439788039057 / 638512875) * L))
          * abErrWindowVec (by norm_num : (1 : ℕ) ≤ 13) ab13GenericCoeff h f t₀
              ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂] y n
        + ‖abResidualVec 13 ab13GenericCoeff h y t₀ n‖ := by
  exact ab13Vec_one_step_lipschitz hh hL hf t₀
    y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y hyf n

/-! ### Packed-polynomial AB13 vector residual algebra -/

private noncomputable def ab13Vec_yPoly14
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m h : ℝ) (d0 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t : E) : E :=
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
    + ((m * h) ^ 13 / 6227020800) • d13t

private noncomputable def ab13Vec_dPoly13
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m h : ℝ) (d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t : E) : E :=
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
    + ((m * h) ^ 12 / 479001600) • d13t

private lemma ab13Vec_residual_alg_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y0 y12 y13 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12
      d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t : E) (h : ℝ)
    (A B C D F G H I J K P Q R S : E)
    (hA : A = y13 - y0 - ab13Vec_yPoly14 13 h d0 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hB : B = y12 - y0 - ab13Vec_yPoly14 12 h d0 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hC : C = d12 - d0 - ab13Vec_dPoly13 12 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hD : D = d11 - d0 - ab13Vec_dPoly13 11 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hF : F = d10 - d0 - ab13Vec_dPoly13 10 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hG : G = d9 - d0 - ab13Vec_dPoly13 9 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hH : H = d8 - d0 - ab13Vec_dPoly13 8 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hI : I = d7 - d0 - ab13Vec_dPoly13 7 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hJ : J = d6 - d0 - ab13Vec_dPoly13 6 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hK : K = d5 - d0 - ab13Vec_dPoly13 5 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hP : P = d4 - d0 - ab13Vec_dPoly13 4 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hQ : Q = d3 - d0 - ab13Vec_dPoly13 3 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hR : R = d2 - d0 - ab13Vec_dPoly13 2 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hS : S = d1 - d0 - ab13Vec_dPoly13 1 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t) :
    y13 - y12 - h • ((13064406523627 / 2615348736000 : ℝ) • d12
                  - (61497552797274 / 2615348736000 : ℝ) • d11
                  + (214696591002612 / 2615348736000 : ℝ) • d10
                  - (524924579905150 / 2615348736000 : ℝ) • d9
                  + (932884546055895 / 2615348736000 : ℝ) • d8
                  - (1233589244941764 / 2615348736000 : ℝ) • d7
                  + (1226443086129408 / 2615348736000 : ℝ) • d6
                  - (915883387152444 / 2615348736000 : ℝ) • d5
                  + (507140369728425 / 2615348736000 : ℝ) • d4
                  - (202322913738370 / 2615348736000 : ℝ) • d3
                  + (55060974662412 / 2615348736000 : ℝ) • d2
                  - (9160551085734 / 2615348736000 : ℝ) • d1
                  + (703604254357 / 2615348736000 : ℝ) • d0)
      = A - B
        - (13064406523627 * h / 2615348736000 : ℝ) • C
        + (61497552797274 * h / 2615348736000 : ℝ) • D
        - (214696591002612 * h / 2615348736000 : ℝ) • F
        + (524924579905150 * h / 2615348736000 : ℝ) • G
        - (932884546055895 * h / 2615348736000 : ℝ) • H
        + (1233589244941764 * h / 2615348736000 : ℝ) • I
        - (1226443086129408 * h / 2615348736000 : ℝ) • J
        + (915883387152444 * h / 2615348736000 : ℝ) • K
        - (507140369728425 * h / 2615348736000 : ℝ) • P
        + (202322913738370 * h / 2615348736000 : ℝ) • Q
        - (55060974662412 * h / 2615348736000 : ℝ) • R
        + (9160551085734 * h / 2615348736000 : ℝ) • S := by
  simp +decide [*, ab13Vec_yPoly14, ab13Vec_dPoly13, smul_smul]
  module

private lemma ab13Vec_residual_bound_alg_identity (M h : ℝ) :
    M / 87178291200 * (13 * h) ^ 14
      + M / 87178291200 * (12 * h) ^ 14
      + (13064406523627 * h / 2615348736000) * (M / 6227020800 * (12 * h) ^ 13)
      + (61497552797274 * h / 2615348736000) * (M / 6227020800 * (11 * h) ^ 13)
      + (214696591002612 * h / 2615348736000) * (M / 6227020800 * (10 * h) ^ 13)
      + (524924579905150 * h / 2615348736000) * (M / 6227020800 * (9 * h) ^ 13)
      + (932884546055895 * h / 2615348736000) * (M / 6227020800 * (8 * h) ^ 13)
      + (1233589244941764 * h / 2615348736000) * (M / 6227020800 * (7 * h) ^ 13)
      + (1226443086129408 * h / 2615348736000) * (M / 6227020800 * (6 * h) ^ 13)
      + (915883387152444 * h / 2615348736000) * (M / 6227020800 * (5 * h) ^ 13)
      + (507140369728425 * h / 2615348736000) * (M / 6227020800 * (4 * h) ^ 13)
      + (202322913738370 * h / 2615348736000) * (M / 6227020800 * (3 * h) ^ 13)
      + (55060974662412 * h / 2615348736000) * (M / 6227020800 * (2 * h) ^ 13)
      + (9160551085734 * h / 2615348736000) * (M / 6227020800 * h ^ 13)
      = (5616577262114645115720677 / 10602754543180800000 : ℝ) * M * h ^ 14 := by
  ring

private lemma ab13Vec_triangle_aux
    {E : Type*} [NormedAddCommGroup E]
    (A B C D F G H I J K P Q R S : E) :
    ‖A - B - C + D - F + G - H + I - J + K - P + Q - R + S‖
      ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖F‖ + ‖G‖ + ‖H‖ + ‖I‖
          + ‖J‖ + ‖K‖ + ‖P‖ + ‖Q‖ + ‖R‖ + ‖S‖ := by
  simp_all +decide [sub_eq_add_neg, add_assoc]
  refine' le_trans (norm_add_le _ _) ?_
  refine' add_le_add le_rfl ?_
  simp_all +decide [← add_assoc]
  convert norm_sum_le (Finset.range 13)
      (fun i =>
        if i = 0 then -B else if i = 1 then -C else if i = 2 then D
        else if i = 3 then -F else if i = 4 then G else if i = 5 then -H
        else if i = 6 then I else if i = 7 then -J else if i = 8 then K
        else if i = 9 then -P else if i = 10 then Q else if i = 11 then -R
        else S) using 1 <;>
    simp +decide [Finset.sum_range_succ]

private lemma ab13Vec_residual_fourteen_term_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D F G H I J K P Q R S : E) (h : ℝ) (hh : 0 ≤ h) :
    ‖A - B - (13064406523627 * h / 2615348736000 : ℝ) • C
        + (61497552797274 * h / 2615348736000 : ℝ) • D
        - (214696591002612 * h / 2615348736000 : ℝ) • F
        + (524924579905150 * h / 2615348736000 : ℝ) • G
        - (932884546055895 * h / 2615348736000 : ℝ) • H
        + (1233589244941764 * h / 2615348736000 : ℝ) • I
        - (1226443086129408 * h / 2615348736000 : ℝ) • J
        + (915883387152444 * h / 2615348736000 : ℝ) • K
        - (507140369728425 * h / 2615348736000 : ℝ) • P
        + (202322913738370 * h / 2615348736000 : ℝ) • Q
        - (55060974662412 * h / 2615348736000 : ℝ) • R
        + (9160551085734 * h / 2615348736000 : ℝ) • S‖
      ≤ ‖A‖ + ‖B‖ + (13064406523627 * h / 2615348736000) * ‖C‖
          + (61497552797274 * h / 2615348736000) * ‖D‖
          + (214696591002612 * h / 2615348736000) * ‖F‖
          + (524924579905150 * h / 2615348736000) * ‖G‖
          + (932884546055895 * h / 2615348736000) * ‖H‖
          + (1233589244941764 * h / 2615348736000) * ‖I‖
          + (1226443086129408 * h / 2615348736000) * ‖J‖
          + (915883387152444 * h / 2615348736000) * ‖K‖
          + (507140369728425 * h / 2615348736000) * ‖P‖
          + (202322913738370 * h / 2615348736000) * ‖Q‖
          + (55060974662412 * h / 2615348736000) * ‖R‖
          + (9160551085734 * h / 2615348736000) * ‖S‖ := by
  convert ab13Vec_triangle_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ using 1
  simp +decide [norm_smul, abs_of_nonneg, hh]

private lemma ab13Vec_residual_combine_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D F G H I J K P Q R S : E) {M h : ℝ} (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (hA_bd : ‖A‖ ≤ M / 87178291200 * (13 * h) ^ 14)
    (hB_bd : ‖B‖ ≤ M / 87178291200 * (12 * h) ^ 14)
    (hC_bd : ‖C‖ ≤ M / 6227020800 * (12 * h) ^ 13)
    (hD_bd : ‖D‖ ≤ M / 6227020800 * (11 * h) ^ 13)
    (hF_bd : ‖F‖ ≤ M / 6227020800 * (10 * h) ^ 13)
    (hG_bd : ‖G‖ ≤ M / 6227020800 * (9 * h) ^ 13)
    (hH_bd : ‖H‖ ≤ M / 6227020800 * (8 * h) ^ 13)
    (hI_bd : ‖I‖ ≤ M / 6227020800 * (7 * h) ^ 13)
    (hJ_bd : ‖J‖ ≤ M / 6227020800 * (6 * h) ^ 13)
    (hK_bd : ‖K‖ ≤ M / 6227020800 * (5 * h) ^ 13)
    (hP_bd : ‖P‖ ≤ M / 6227020800 * (4 * h) ^ 13)
    (hQ_bd : ‖Q‖ ≤ M / 6227020800 * (3 * h) ^ 13)
    (hR_bd : ‖R‖ ≤ M / 6227020800 * (2 * h) ^ 13)
    (hS_bd : ‖S‖ ≤ M / 6227020800 * h ^ 13) :
    ‖A - B - (13064406523627 * h / 2615348736000 : ℝ) • C
        + (61497552797274 * h / 2615348736000 : ℝ) • D
        - (214696591002612 * h / 2615348736000 : ℝ) • F
        + (524924579905150 * h / 2615348736000 : ℝ) • G
        - (932884546055895 * h / 2615348736000 : ℝ) • H
        + (1233589244941764 * h / 2615348736000 : ℝ) • I
        - (1226443086129408 * h / 2615348736000 : ℝ) • J
        + (915883387152444 * h / 2615348736000 : ℝ) • K
        - (507140369728425 * h / 2615348736000 : ℝ) • P
        + (202322913738370 * h / 2615348736000 : ℝ) • Q
        - (55060974662412 * h / 2615348736000 : ℝ) • R
        + (9160551085734 * h / 2615348736000 : ℝ) • S‖
      ≤ (529729 : ℝ) * M * h ^ 14 := by
  refine' le_trans _ (le_trans (ab13Vec_residual_bound_alg_identity M h |> le_of_eq) _)
  · refine' le_trans
      (ab13Vec_residual_fourteen_term_triangle A B C D F G H I J K P Q R S _ hh) ?_
    gcongr
  · gcongr
    norm_num

theorem ab13Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 14 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 14 y t‖ ≤ M)
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
    (ht13h : t + 13 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖ab13VecResidual h t y‖ ≤ (529729 : ℝ) * M * h ^ 14 := by
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
  have h13h : 0 ≤ 13 * h := by linarith
  have hRy12 :=
    y_fourteenth_order_taylor_remainder_vec hy hbnd ht ht12h h12h
  have hRy13 :=
    y_fourteenth_order_taylor_remainder_vec hy hbnd ht ht13h h13h
  have hRyp1 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht hth hh
  have hRyp2 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht7h h7h
  have hRyp8 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht8h h8h
  have hRyp9 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht9h h9h
  have hRyp10 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht10h h10h
  have hRyp11 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht11h h11h
  have hRyp12 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht12h h12h
  unfold ab13VecResidual
  set y0 : E := y t with hy0_def
  set y12 : E := y (t + 12 * h) with hy12_def
  set y13 : E := y (t + 13 * h) with hy13_def
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
  set d12 : E := deriv y (t + 12 * h) with hd12_def
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
  set d13t : E := iteratedDeriv 13 y t with hd13t_def
  clear_value y0 y12 y13 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12
    d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t
  set A : E := y13 - y0 - ab13Vec_yPoly14 13 h d0 d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hA_def
  set B : E := y12 - y0 - ab13Vec_yPoly14 12 h d0 d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hB_def
  set C : E := d12 - d0 - ab13Vec_dPoly13 12 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hC_def
  set D : E := d11 - d0 - ab13Vec_dPoly13 11 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hD_def
  set F : E := d10 - d0 - ab13Vec_dPoly13 10 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hF_def
  set G : E := d9 - d0 - ab13Vec_dPoly13 9 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hG_def
  set H : E := d8 - d0 - ab13Vec_dPoly13 8 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hH_def
  set I : E := d7 - d0 - ab13Vec_dPoly13 7 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hI_def
  set J : E := d6 - d0 - ab13Vec_dPoly13 6 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hJ_def
  set K : E := d5 - d0 - ab13Vec_dPoly13 5 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hK_def
  set P : E := d4 - d0 - ab13Vec_dPoly13 4 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hP_def
  set Q : E := d3 - d0 - ab13Vec_dPoly13 3 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hQ_def
  set R : E := d2 - d0 - ab13Vec_dPoly13 2 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hR_def
  set S : E := d1 - d0 - ab13Vec_dPoly13 1 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hS_def
  have hLTE_eq :=
    ab13Vec_residual_alg_identity y0 y12 y13 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
      d11 d12 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t h
      A B C D F G H I J K P Q R S hA_def hB_def hC_def hD_def hF_def hG_def
      hH_def hI_def hJ_def hK_def hP_def hQ_def hR_def hS_def
  rw [hLTE_eq]
  have hA_bd : ‖A‖ ≤ M / 87178291200 * (13 * h) ^ 14 := by
    rw [hA_def]; unfold ab13Vec_yPoly14
    convert hRy13 using 2; module
  have hB_bd : ‖B‖ ≤ M / 87178291200 * (12 * h) ^ 14 := by
    rw [hB_def]; unfold ab13Vec_yPoly14
    convert hRy12 using 2; module
  have hC_bd : ‖C‖ ≤ M / 6227020800 * (12 * h) ^ 13 := by
    rw [hC_def]; unfold ab13Vec_dPoly13
    convert hRyp12 using 2; module
  have hD_bd : ‖D‖ ≤ M / 6227020800 * (11 * h) ^ 13 := by
    rw [hD_def]; unfold ab13Vec_dPoly13
    convert hRyp11 using 2; module
  have hF_bd : ‖F‖ ≤ M / 6227020800 * (10 * h) ^ 13 := by
    rw [hF_def]; unfold ab13Vec_dPoly13
    convert hRyp10 using 2; module
  have hG_bd : ‖G‖ ≤ M / 6227020800 * (9 * h) ^ 13 := by
    rw [hG_def]; unfold ab13Vec_dPoly13
    convert hRyp9 using 2; module
  have hH_bd : ‖H‖ ≤ M / 6227020800 * (8 * h) ^ 13 := by
    rw [hH_def]; unfold ab13Vec_dPoly13
    convert hRyp8 using 2; module
  have hI_bd : ‖I‖ ≤ M / 6227020800 * (7 * h) ^ 13 := by
    rw [hI_def]; unfold ab13Vec_dPoly13
    convert hRyp7 using 2; module
  have hJ_bd : ‖J‖ ≤ M / 6227020800 * (6 * h) ^ 13 := by
    rw [hJ_def]; unfold ab13Vec_dPoly13
    convert hRyp6 using 2; module
  have hK_bd : ‖K‖ ≤ M / 6227020800 * (5 * h) ^ 13 := by
    rw [hK_def]; unfold ab13Vec_dPoly13
    convert hRyp5 using 2; module
  have hP_bd : ‖P‖ ≤ M / 6227020800 * (4 * h) ^ 13 := by
    rw [hP_def]; unfold ab13Vec_dPoly13
    convert hRyp4 using 2; module
  have hQ_bd : ‖Q‖ ≤ M / 6227020800 * (3 * h) ^ 13 := by
    rw [hQ_def]; unfold ab13Vec_dPoly13
    convert hRyp3 using 2; module
  have hR_bd : ‖R‖ ≤ M / 6227020800 * (2 * h) ^ 13 := by
    rw [hR_def]; unfold ab13Vec_dPoly13
    convert hRyp2 using 2; module
  have hS_bd : ‖S‖ ≤ M / 6227020800 * h ^ 13 := by
    rw [hS_def]; unfold ab13Vec_dPoly13
    convert hRyp1 using 2; module
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  clear_value A B C D F G H I J K P Q R S
  exact ab13Vec_residual_combine_aux A B C D F G H I J K P Q R S hh hMnn
    hA_bd hB_bd hC_bd hD_bd hF_bd hG_bd hH_bd hI_bd hJ_bd hK_bd hP_bd hQ_bd
    hR_bd hS_bd

theorem ab13Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 14 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 13) * h ≤ T →
        ‖ab13VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 14 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_fourteen_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(529729 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh _hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 13) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 13) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 13) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 13) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 13) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 13) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 13) * h := by nlinarith
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 7 * h ≤ ((n : ℝ) + 13) * h := by nlinarith
    linarith
  have ht8h_mem : t + 8 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 8 * h ≤ ((n : ℝ) + 13) * h := by nlinarith
    linarith
  have ht9h_mem : t + 9 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 9 * h ≤ ((n : ℝ) + 13) * h := by nlinarith
    linarith
  have ht10h_mem : t + 10 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 10 * h ≤ ((n : ℝ) + 13) * h := by nlinarith
    linarith
  have ht11h_mem : t + 11 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 11 * h ≤ ((n : ℝ) + 13) * h := by nlinarith
    linarith
  have ht12h_mem : t + 12 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 12 * h ≤ ((n : ℝ) + 13) * h := by nlinarith
    linarith
  have ht13h_mem : t + 13 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 13 * h ≤ ((n : ℝ) + 13) * h := by nlinarith
    linarith
  show ‖ab13VecResidual h t y‖ ≤ 529729 * M * h ^ 14
  exact ab13Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem ht3h_mem
    ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem ht9h_mem ht10h_mem ht11h_mem
    ht12h_mem ht13h_mem hh.le

lemma ab13GenericCoeffVec :
    (fun j : Fin 13 => ab13GenericCoeff j) = ab13GenericCoeff := rfl

lemma abLip_ab13GenericCoeffVec (L : ℝ) :
    abLip 13 (fun j : Fin 13 => ab13GenericCoeff j) L
      = (1439788039057 / 638512875) * L := by
  simpa using abLip_ab13GenericCoeff L

lemma ab13IterVec_eq_abIterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : E) (n : ℕ) :
    ab13IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ n
      = abIterVec 13 ab13GenericCoeff h f t₀
          ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂] n := by
  rfl

lemma ab13VecResidual_eq_abResidualVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (y : ℝ → E) (t₀ : ℝ) (n : ℕ) :
    ab13VecResidual h (t₀ + (n : ℝ) * h) y
      = abResidualVec 13 ab13GenericCoeff h y t₀ n := by
  unfold ab13VecResidual abResidualVec
  rw [sum_univ_thirteen_aux_vec, ab13GenericCoeff_zero, ab13GenericCoeff_one,
    ab13GenericCoeff_two, ab13GenericCoeff_three, ab13GenericCoeff_four,
    ab13GenericCoeff_five, ab13GenericCoeff_six, ab13GenericCoeff_seven,
    ab13GenericCoeff_eight, ab13GenericCoeff_nine, ab13GenericCoeff_ten,
    ab13GenericCoeff_eleven, ab13GenericCoeff_twelve]
  have eA : t₀ + (n : ℝ) * h + 13 * h = t₀ + ((n + 13 : ℕ) : ℝ) * h := by
    push_cast; ring
  have eB :
      t₀ + (n : ℝ) * h + 12 * h = t₀ + ((n + 13 - 1 : ℕ) : ℝ) * h := by
    have hsub : (n + 13 - 1 : ℕ) = n + 12 := by omega
    rw [hsub]; push_cast; ring
  have eC : t₀ + (n : ℝ) * h
      = t₀ + ((n + ((0 : Fin 13) : ℕ) : ℕ) : ℝ) * h := by
    simp
  have eD : t₀ + (n : ℝ) * h + h
      = t₀ + ((n + ((1 : Fin 13) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eE : t₀ + (n : ℝ) * h + 2 * h
      = t₀ + ((n + ((2 : Fin 13) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eF : t₀ + (n : ℝ) * h + 3 * h
      = t₀ + ((n + ((3 : Fin 13) : ℕ) : ℕ) : ℝ) * h := by
    have : ((3 : Fin 13) : ℕ) = 3 := rfl
    rw [this]; push_cast; ring
  have eG : t₀ + (n : ℝ) * h + 4 * h
      = t₀ + ((n + ((4 : Fin 13) : ℕ) : ℕ) : ℝ) * h := by
    have : ((4 : Fin 13) : ℕ) = 4 := rfl
    rw [this]; push_cast; ring
  have eH : t₀ + (n : ℝ) * h + 5 * h
      = t₀ + ((n + ((5 : Fin 13) : ℕ) : ℕ) : ℝ) * h := by
    have : ((5 : Fin 13) : ℕ) = 5 := rfl
    rw [this]; push_cast; ring
  have eI : t₀ + (n : ℝ) * h + 6 * h
      = t₀ + ((n + ((6 : Fin 13) : ℕ) : ℕ) : ℝ) * h := by
    have : ((6 : Fin 13) : ℕ) = 6 := rfl
    rw [this]; push_cast; ring
  have eJ : t₀ + (n : ℝ) * h + 7 * h
      = t₀ + ((n + ((7 : Fin 13) : ℕ) : ℕ) : ℝ) * h := by
    have : ((7 : Fin 13) : ℕ) = 7 := rfl
    rw [this]; push_cast; ring
  have eK : t₀ + (n : ℝ) * h + 8 * h
      = t₀ + ((n + ((8 : Fin 13) : ℕ) : ℕ) : ℝ) * h := by
    have : ((8 : Fin 13) : ℕ) = 8 := rfl
    rw [this]; push_cast; ring
  have eL : t₀ + (n : ℝ) * h + 9 * h
      = t₀ + ((n + ((9 : Fin 13) : ℕ) : ℕ) : ℝ) * h := by
    have : ((9 : Fin 13) : ℕ) = 9 := rfl
    rw [this]; push_cast; ring
  have eM : t₀ + (n : ℝ) * h + 10 * h
      = t₀ + ((n + ((10 : Fin 13) : ℕ) : ℕ) : ℝ) * h := by
    have : ((10 : Fin 13) : ℕ) = 10 := rfl
    rw [this]; push_cast; ring
  have eN : t₀ + (n : ℝ) * h + 11 * h
      = t₀ + ((n + ((11 : Fin 13) : ℕ) : ℕ) : ℝ) * h := by
    have : ((11 : Fin 13) : ℕ) = 11 := rfl
    rw [this]; push_cast; ring
  have eO : t₀ + (n : ℝ) * h + 12 * h
      = t₀ + ((n + ((12 : Fin 13) : ℕ) : ℕ) : ℝ) * h := by
    have : ((12 : Fin 13) : ℕ) = 12 := rfl
    rw [this]; push_cast; ring
  rw [← eA, ← eB, ← eC, ← eD, ← eE, ← eF, ← eG, ← eH, ← eI, ← eJ, ← eK,
    ← eL, ← eM, ← eN, ← eO]
  rw [show (-(9160551085734 : ℝ) / 2615348736000) •
        deriv y (t₀ + (n : ℝ) * h + h)
        = -((9160551085734 / 2615348736000 : ℝ) •
            deriv y (t₀ + (n : ℝ) * h + h)) by
    rw [show (-(9160551085734 : ℝ) / 2615348736000)
        = -(9160551085734 / 2615348736000 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(202322913738370 : ℝ) / 2615348736000) •
        deriv y (t₀ + (n : ℝ) * h + 3 * h)
        = -((202322913738370 / 2615348736000 : ℝ) •
            deriv y (t₀ + (n : ℝ) * h + 3 * h)) by
    rw [show (-(202322913738370 : ℝ) / 2615348736000)
        = -(202322913738370 / 2615348736000 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(915883387152444 : ℝ) / 2615348736000) •
        deriv y (t₀ + (n : ℝ) * h + 5 * h)
        = -((915883387152444 / 2615348736000 : ℝ) •
            deriv y (t₀ + (n : ℝ) * h + 5 * h)) by
    rw [show (-(915883387152444 : ℝ) / 2615348736000)
        = -(915883387152444 / 2615348736000 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(1233589244941764 : ℝ) / 2615348736000) •
        deriv y (t₀ + (n : ℝ) * h + 7 * h)
        = -((1233589244941764 / 2615348736000 : ℝ) •
            deriv y (t₀ + (n : ℝ) * h + 7 * h)) by
    rw [show (-(1233589244941764 : ℝ) / 2615348736000)
        = -(1233589244941764 / 2615348736000 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(524924579905150 : ℝ) / 2615348736000) •
        deriv y (t₀ + (n : ℝ) * h + 9 * h)
        = -((524924579905150 / 2615348736000 : ℝ) •
            deriv y (t₀ + (n : ℝ) * h + 9 * h)) by
    rw [show (-(524924579905150 : ℝ) / 2615348736000)
        = -(524924579905150 / 2615348736000 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(61497552797274 : ℝ) / 2615348736000) •
        deriv y (t₀ + (n : ℝ) * h + 11 * h)
        = -((61497552797274 / 2615348736000 : ℝ) •
            deriv y (t₀ + (n : ℝ) * h + 11 * h)) by
    rw [show (-(61497552797274 : ℝ) / 2615348736000)
        = -(61497552797274 / 2615348736000 : ℝ) by ring]
    exact neg_smul _ _]
  abel_nf

theorem ab13Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 14 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : E} {ε₀ : ℝ}, 0 ≤ ε₀ →
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
      ‖y₁₂ - y (t₀ + 12 * h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 12) * h ≤ T →
      ‖ab13IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ N
          - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((1439788039057 / 638512875) * L * T) * ε₀ + K * h ^ 13 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab13Vec_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((1439788039057 / 638512875) * L * T) * C, δ,
    ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ ε₀ hε₀
    he0_bd he1_bd he2_bd he3_bd he4_bd he5_bd he6_bd he7_bd he8_bd he9_bd
    he10_bd he11_bd he12_bd N hNh
  set α : Fin 13 → ℝ := ab13GenericCoeff with hα_def
  set y₀_non : Fin 13 → E :=
    ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂]
    with hy_non_def
  have hs : (1 : ℕ) ≤ 13 := by norm_num
  haveI : Nonempty (Fin 13) := ⟨⟨0, hs⟩⟩
  have hstart : abErrWindowVec hs α h f t₀ y₀_non y 0 ≤ ε₀ := by
    unfold abErrWindowVec
    apply Finset.sup'_le
    intro j _
    unfold abErrVec
    fin_cases j <;> simp [abIterVec, hy_non_def] <;> assumption
  have hres_gen : ∀ n : ℕ, n < N →
      ‖abResidualVec 13 α h y t₀ n‖ ≤ C * h ^ (13 + 1) := by
    intro n hn_lt
    have hcast : (n : ℝ) + 13 ≤ (N : ℝ) + 12 := by
      have : (n : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      linarith
    have hn13_le : ((n : ℝ) + 13) * h ≤ T := by
      have hmul : ((n : ℝ) + 13) * h ≤ ((N : ℝ) + 12) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith
    have hres := hresidual hh hδ_le n hn13_le
    rw [hα_def, ← ab13VecResidual_eq_abResidualVec (E := E) h y t₀ n]
    have hpow : C * h ^ (13 + 1) = C * h ^ 14 := by norm_num
    rwa [hpow]
  have hNh' : (N : ℝ) * h ≤ T := by
    have hmono : (N : ℝ) * h ≤ ((N : ℝ) + 12) * h := by
      have h1 : (N : ℝ) ≤ (N : ℝ) + 12 := by linarith
      exact mul_le_mul_of_nonneg_right h1 hh.le
    linarith
  have hgeneric :=
    ab_global_error_bound_generic_vec (p := 13) hs α hh.le hL hC_nn hf t₀
      y₀_non y hyf hε₀ hstart N hNh' hres_gen
  rw [show abLip 13 α L = (1439788039057 / 638512875) * L from by
    rw [hα_def]; exact abLip_ab13GenericCoeff L] at hgeneric
  have hwindow_ge : abErrVec 13 α h f t₀ y₀_non y N
      ≤ abErrWindowVec hs α h f t₀ y₀_non y N := by
    show abErrVec 13 α h f t₀ y₀_non y (N + ((⟨0, hs⟩ : Fin 13) : ℕ))
        ≤ abErrWindowVec hs α h f t₀ y₀_non y N
    unfold abErrWindowVec
    exact Finset.le_sup' (b := ⟨0, hs⟩)
      (f := fun j : Fin 13 => abErrVec 13 α h f t₀ y₀_non y (N + (j : ℕ)))
      (Finset.mem_univ _)
  have hbridge :
      abIterVec 13 α h f t₀ y₀_non N
        = ab13IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ N := by
    rw [hα_def, hy_non_def]
    rfl
  have habsErr :
      abErrVec 13 α h f t₀ y₀_non y N
        = ‖ab13IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ N
            - y (t₀ + (N : ℝ) * h)‖ := by
    show ‖abIterVec 13 α h f t₀ y₀_non N - y (t₀ + (N : ℝ) * h)‖
        = ‖ab13IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ N
            - y (t₀ + (N : ℝ) * h)‖
    rw [hbridge]
  show ‖ab13IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ N
        - y (t₀ + (N : ℝ) * h)‖
      ≤ Real.exp ((1439788039057 / 638512875) * L * T) * ε₀
        + T * Real.exp ((1439788039057 / 638512875) * L * T) * C * h ^ 13
  linarith [hwindow_ge, hgeneric, habsErr.symm.le, habsErr.le]

end LMM
