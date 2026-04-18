import OpenMath.StiffEquations

/-!
# Theorem 357C: Algebraic stability implies BN-stability

Formalization of the BN-stability direction in Iserles, Theorem 357C.
-/

open Finset

noncomputable section

namespace ButcherTableau

variable {s : ℕ}

/-- A vector field is dissipative if its one-sided inner product is nonpositive. -/
def IsDissipative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℝ → E → E) : Prop :=
  ∀ x u v, @inner ℝ E _ (f x u - f x v) (u - v) ≤ 0

/-- Data for one implicit RK step, including stages and stage derivatives. -/
def SatisfiesRKStep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ButcherTableau s) (f : ℝ → E → E) (x h : ℝ)
    (y₀ : E) (Y F : Fin s → E) (y₁ : E) : Prop :=
  (∀ i, Y i = y₀ + h • ∑ j : Fin s, (t.A i j) • F j) ∧
  (∀ i, F i = f (x + h * t.c i) (Y i)) ∧
  y₁ = y₀ + h • ∑ i : Fin s, (t.b i) • F i

/-- BN-stability: one RK step is contractive on dissipative problems. -/
def IsBNStable (t : ButcherTableau s) : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℝ → E → E),
    IsDissipative f →
    ∀ x h, 0 ≤ h →
    ∀ y₀ z₀ y₁ z₁ : E,
    ∀ Y Z F G : Fin s → E,
    SatisfiesRKStep t f x h y₀ Y F y₁ →
    SatisfiesRKStep t f x h z₀ Z G z₁ →
    ‖y₁ - z₁‖ ≤ ‖y₀ - z₀‖

lemma rk_stage_difference_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ButcherTableau s) (x h : ℝ) (f : ℝ → E → E)
    (y₀ z₀ y₁ z₁ : E) (Y Z F G : Fin s → E)
    (hy : SatisfiesRKStep t f x h y₀ Y F y₁)
    (hz : SatisfiesRKStep t f x h z₀ Z G z₁) :
    ∀ i : Fin s, Y i - Z i = (y₀ - z₀) + h • ∑ j : Fin s, (t.A i j) • (F j - G j) := by
  intro i; obtain ⟨hY, _, _⟩ := hy; obtain ⟨hZ, _, _⟩ := hz
  simp only [hY i, hZ i, smul_sub, Finset.sum_sub_distrib]; abel

lemma rk_output_difference_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ButcherTableau s) (x h : ℝ) (f : ℝ → E → E)
    (y₀ z₀ y₁ z₁ : E) (Y Z F G : Fin s → E)
    (hy : SatisfiesRKStep t f x h y₀ Y F y₁)
    (hz : SatisfiesRKStep t f x h z₀ Z G z₁) :
    y₁ - z₁ = (y₀ - z₀) + h • ∑ i : Fin s, (t.b i) • (F i - G i) := by
  obtain ⟨_, _, hy₁⟩ := hy; obtain ⟨_, _, hz₁⟩ := hz
  simp only [hy₁, hz₁, smul_sub, Finset.sum_sub_distrib]; abel

/-- PSD matrix applied to inner product vectors is nonneg.
If M is PSD (∀ v, v'Mv ≥ 0) and U_1,...,U_s are vectors in an inner product space,
then ∑ M_{ij} ⟨U_i, U_j⟩ ≥ 0. -/
lemma algStabMatrix_inner_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {t : ButcherTableau s} (ht : t.IsAlgStable) (U : Fin s → E) :
    0 ≤ ∑ i : Fin s, ∑ j : Fin s, t.algStabMatrix i j * @inner ℝ E _ (U i) (U j) := by
  -- Work in the finite-dimensional span of {U_i}
  set V := Submodule.span ℝ (Set.range U)
  haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range U)
  have hU : ∀ i, U i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  set U' : Fin s → V := fun i => ⟨U i, hU i⟩
  set b := stdOrthonormalBasis ℝ V
  -- Parseval: ⟨U_i, U_j⟩_E = ∑_k ⟨U_i, b_k⟩_E * ⟨U_j, b_k⟩_E
  have hP : ∀ i j, @inner ℝ E _ (U i) (U j) =
      ∑ k, @inner ℝ E _ (U i) (↑(b k)) * @inner ℝ E _ (U j) (↑(b k)) := by
    intro i j
    have h := b.sum_inner_mul_inner (U' i) (U' j)
    rw [Submodule.coe_inner] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro k _
    rw [Submodule.coe_inner, Submodule.coe_inner,
      real_inner_comm (↑(b k) : E) (↑(U' j) : E)]
  simp_rw [hP, Finset.mul_sum]
  -- Swap sums: ∑ i, ∑ j, ∑ k → ∑ k, ∑ i, ∑ j
  have h_swap : ∀ (g : Fin s → Fin s → Fin (Module.finrank ℝ V) → ℝ),
      (∑ i : Fin s, ∑ j : Fin s, ∑ k, g i j k) =
      ∑ k, ∑ i : Fin s, ∑ j : Fin s, g i j k := by
    intro g
    trans ∑ i : Fin s, ∑ k, ∑ j : Fin s, g i j k
    · congr 1; ext i; exact Finset.sum_comm
    · exact Finset.sum_comm
  rw [h_swap]
  -- Each summand is ∑ i, ∑ j, v i * M i j * v j where v i = ⟨U i, b k⟩
  apply Finset.sum_nonneg
  intro k _
  simp_rw [show ∀ i j : Fin s, t.algStabMatrix i j *
      (@inner ℝ E _ (U i) (↑(b k)) * @inner ℝ E _ (U j) (↑(b k))) =
      @inner ℝ E _ (U i) (↑(b k)) * t.algStabMatrix i j *
      @inner ℝ E _ (U j) (↑(b k)) from fun i j => by ring]
  exact ht.posdef_M _

/-- The norm-squared identity for BN-stability (corrected from (357e)):
  ‖y₁-z₁‖² - ‖y₀-z₀‖² = 2h ∑ bᵢ⟨Yᵢ-Zᵢ, Fᵢ-Gᵢ⟩ - h² ∑ M_{ij}⟨Fᵢ-Gᵢ, Fⱼ-Gⱼ⟩ -/
lemma rk_step_norm_sq_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : ButcherTableau s) (x h : ℝ) (f : ℝ → E → E)
    (y₀ z₀ y₁ z₁ : E) (Y Z F G : Fin s → E)
    (hy : SatisfiesRKStep t f x h y₀ Y F y₁)
    (hz : SatisfiesRKStep t f x h z₀ Z G z₁) :
    ‖y₁ - z₁‖ ^ 2 - ‖y₀ - z₀‖ ^ 2 =
      2 * h * ∑ i : Fin s, t.b i * @inner ℝ E _ (Y i - Z i) (F i - G i)
        - h ^ 2 *
          ∑ i : Fin s, ∑ j : Fin s,
            t.algStabMatrix i j * @inner ℝ E _ (F i - G i) (F j - G j) := by
  set d := y₀ - z₀ with hd_def
  set w := ∑ i : Fin s, (t.b i) • (F i - G i) with hw_def
  have h_out : y₁ - z₁ = d + h • w := rk_output_difference_eq t x h f y₀ z₀ y₁ z₁ Y Z F G hy hz
  have h_stg := rk_stage_difference_eq t x h f y₀ z₀ y₁ z₁ Y Z F G hy hz
  -- LHS = 2h⟨d,w⟩ + h²‖w‖²
  have h_lhs : ‖y₁ - z₁‖ ^ 2 - ‖d‖ ^ 2 =
      2 * h * @inner ℝ E _ d w + h ^ 2 * ‖w‖ ^ 2 := by
    rw [h_out, norm_add_sq_real, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs]; ring
  rw [h_lhs]
  -- Define S = ∑ᵢ∑ⱼ bᵢAᵢⱼ⟨Fⱼ-Gⱼ, Fᵢ-Gᵢ⟩
  set S := ∑ i : Fin s, ∑ j : Fin s,
    t.b i * t.A i j * @inner ℝ E _ (F j - G j) (F i - G i) with hS_def
  -- Lemma 1: ∑bᵢ⟨Yᵢ-Zᵢ, Fᵢ-Gᵢ⟩ = ⟨d,w⟩ + h*S
  have h_lem1 : ∑ i : Fin s, t.b i * @inner ℝ E _ (Y i - Z i) (F i - G i) =
      @inner ℝ E _ d w + h * S := by
    simp_rw [h_stg, inner_add_left, real_inner_smul_left, sum_inner,
      real_inner_smul_left, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    have h1 : ∑ x : Fin s, t.b x * @inner ℝ E _ (y₀ - z₀) (F x - G x) =
        @inner ℝ E _ d w := by
      simp only [← real_inner_smul_right, ← inner_sum]; rfl
    have h2 : ∑ x : Fin s, ∑ i : Fin s,
        t.b x * (h * (t.A x i * @inner ℝ E _ (F i - G i) (F x - G x))) = h * S := by
      simp only [show ∀ (x i : Fin s),
        t.b x * (h * (t.A x i * @inner ℝ E _ (F i - G i) (F x - G x))) =
        h * (t.b x * t.A x i * @inner ℝ E _ (F i - G i) (F x - G x))
        from fun x i => by ring]
      simp only [← Finset.mul_sum]; rfl
    linarith [h1, h2]
  -- Lemma 2: ∑Mᵢⱼ⟨Fᵢ-Gᵢ, Fⱼ-Gⱼ⟩ = 2S - ‖w‖²
  have h_lem2 : ∑ i : Fin s, ∑ j : Fin s,
      t.algStabMatrix i j * @inner ℝ E _ (F i - G i) (F j - G j) =
      2 * S - ‖w‖ ^ 2 := by
    simp only [algStabMatrix]
    simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hT1 : ∑ i : Fin s, ∑ j : Fin s, t.b i * t.A i j * @inner ℝ E _ (F i - G i) (F j - G j) = S := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [real_inner_comm]
    have hT2 : ∑ i : Fin s, ∑ j : Fin s, t.b j * t.A j i * @inner ℝ E _ (F i - G i) (F j - G j) = S := by
      rw [Finset.sum_comm]
    have hT3 : ∑ i : Fin s, ∑ j : Fin s, t.b i * t.b j * @inner ℝ E _ (F i - G i) (F j - G j) = ‖w‖ ^ 2 := by
      rw [← @real_inner_self_eq_norm_sq E]
      simp only [hw_def, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [real_inner_comm]; ring
    linarith [hT1, hT2, hT3]
  rw [h_lem1, h_lem2]; ring

/-- **Theorem 357C**: algebraic stability implies BN-stability. -/
theorem alg_stable_implies_bn_stable {t : ButcherTableau s}
    (ht : t.IsAlgStable) : t.IsBNStable := by
  intro E _ _ f hf x h hh y₀ z₀ y₁ z₁ Y Z F G hy hz
  -- Use the norm-squared identity
  have h_id := rk_step_norm_sq_identity t x h f y₀ z₀ y₁ z₁ Y Z F G hy hz
  -- The dissipative inner product sum is nonpositive
  have h_diss : ∑ i : Fin s, t.b i * @inner ℝ E _ (Y i - Z i) (F i - G i) ≤ 0 := by
    apply Finset.sum_nonpos; intro i _
    apply mul_nonpos_of_nonneg_of_nonpos (ht.nonneg_weights i)
    obtain ⟨_, hF, _⟩ := hy; obtain ⟨_, hG, _⟩ := hz
    rw [hF i, hG i, real_inner_comm]; exact hf _ _ _
  -- The PSD quadratic form is nonneg
  have h_psd := algStabMatrix_inner_nonneg ht (fun i => F i - G i)
  -- Therefore ‖y₁ - z₁‖² ≤ ‖y₀ - z₀‖²
  have hsq : ‖y₁ - z₁‖ ^ 2 ≤ ‖y₀ - z₀‖ ^ 2 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ 2 * h) h_diss,
               mul_nonneg (sq_nonneg h) h_psd]
  exact le_of_sq_le_sq hsq (norm_nonneg _)

end ButcherTableau
