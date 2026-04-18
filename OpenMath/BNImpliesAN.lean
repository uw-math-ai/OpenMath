import OpenMath.ANStability
import OpenMath.BNStability

/-!
# Theorem 357D: BN-stability implies AN-stability

For an irreducible non-confluent Runge–Kutta method, BN-stability implies AN-stability.
This closes the equivalence chain:
  AN-stable ⟹ algebraically stable (356C) ⟹ BN-stable (357C) ⟹ AN-stable (357D).

The proof constructs a dissipative vector field on ℂ (as a real inner product space)
from the AN-stability test data z : Fin s → ℂ with Re(zᵢ) ≤ 0. Applying BN-stability
to an RK step starting from y₀ = 1 and z₀ = 0 gives |R(z)| ≤ 1.

Reference: Iserles, Theorem 357D, p. 273.
-/

open Finset Complex

noncomputable section

namespace ButcherTableau

variable {s : ℕ}

/-- A Runge–Kutta method is **non-confluent** if all abscissae are distinct. -/
def IsNonConfluent (t : ButcherTableau s) : Prop := Function.Injective t.c

/-! ### Stage multiplier: assigns z_i at abscissa c_i -/

/-- Multiplier function mapping each abscissa cᵢ to zᵢ and all other points to 0.
    Used to construct the dissipative field for the BN→AN reduction. -/
def stageMultiplier (t : ButcherTableau s) (z : Fin s → ℂ) : ℝ → ℂ :=
  fun τ => if h : ∃ i : Fin s, τ = t.c i then z h.choose else 0

lemma stageMultiplier_at_stage (t : ButcherTableau s) (z : Fin s → ℂ)
    (hc : t.IsNonConfluent) (i : Fin s) :
    stageMultiplier t z (t.c i) = z i := by
  simp only [stageMultiplier]
  have hex : ∃ j : Fin s, t.c i = t.c j := ⟨i, rfl⟩
  rw [dif_pos hex]
  exact congr_arg z (hc hex.choose_spec).symm

lemma stageMultiplier_re_nonpos (t : ButcherTableau s) (z : Fin s → ℂ)
    (hz : ∀ i, (z i).re ≤ 0) :
    ∀ τ, (stageMultiplier t z τ).re ≤ 0 := by
  intro τ; simp only [stageMultiplier]; split_ifs with h
  · exact hz _
  · simp

/-! ### Dissipative test field -/

/-- The linear test field f(τ, w) = g(τ) · w where g is the stage multiplier. -/
def anTestField (t : ButcherTableau s) (z : Fin s → ℂ) : ℝ → ℂ → ℂ :=
  fun τ w => stageMultiplier t z τ * w

/-- Key inner product identity: ⟨g·d, d⟩_ℝ = Re(g) · ‖d‖² for g, d : ℂ. -/
lemma inner_mul_self_re (g d : ℂ) :
    @inner ℝ ℂ _ (g * d) d = g.re * (‖d‖ ^ 2) := by
  simp [Complex.inner, Complex.sq_norm, Complex.normSq_apply]; ring

/-- The test field is dissipative: ⟨f(τ,u) - f(τ,v), u-v⟩_ℝ = Re(g(τ)) · ‖u-v‖² ≤ 0. -/
lemma anTestField_dissipative (t : ButcherTableau s) (z : Fin s → ℂ)
    (hz : ∀ i, (z i).re ≤ 0) :
    IsDissipative (anTestField t z) := by
  intro τ u v
  have hsub : anTestField t z τ u - anTestField t z τ v =
      stageMultiplier t z τ * (u - v) := by
    simp [anTestField, mul_sub]
  rw [hsub, inner_mul_self_re]
  exact mul_nonpos_of_nonpos_of_nonneg (stageMultiplier_re_nonpos t z hz τ) (sq_nonneg _)

/-! ### Stage values and stability function correspondence -/

/-- Resolved stage values: Y = (I - Aℂ · diag(z))⁻¹ · 𝟏. -/
def resolvedStages (t : ButcherTableau s) (z : Fin s → ℂ) : Fin s → ℂ :=
  (1 - t.Aℂ * Matrix.diagonal z)⁻¹.mulVec (fun _ => 1)

/-- Stage derivatives: Fᵢ = zᵢ · Yᵢ. -/
def stageDerivs (t : ButcherTableau s) (z : Fin s → ℂ) : Fin s → ℂ :=
  fun i => z i * resolvedStages t z i

/-- The resolved stages satisfy the implicit stage equation:
    Yᵢ = 1 + ∑ⱼ Aᵢⱼ · zⱼ · Yⱼ. -/
lemma resolvedStages_eq (t : ButcherTableau s) (z : Fin s → ℂ)
    (hdet : (1 - t.Aℂ * Matrix.diagonal z).det ≠ 0) (i : Fin s) :
    resolvedStages t z i =
      1 + ∑ j : Fin s, t.Aℂ i j * z j * resolvedStages t z j := by
  unfold resolvedStages
  set M := (1 - t.Aℂ * Matrix.diagonal z)
  set x := M⁻¹.mulVec (fun _ => (1 : ℂ))
  have hMx : M.mulVec x = fun _ => 1 := by
    simp only [x, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hdet.isUnit, Matrix.one_mulVec]
  have hi := congr_fun hMx i
  simp only [M, Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.one_apply,
    Matrix.mul_diagonal] at hi
  have key : ∑ x_1 : Fin s, ((if i = x_1 then 1 else 0) - t.Aℂ i x_1 * z x_1) * x x_1 =
      x i - ∑ j, t.Aℂ i j * z j * x j := by
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    congr 1
    simp_rw [ite_mul, one_mul, zero_mul, @eq_comm _ i]; simp
  rw [key] at hi
  exact sub_eq_iff_eq_add.mp hi

/-- The stability function equals the RK output:
    R(z) = 1 + ∑ᵢ bᵢ · zᵢ · Yᵢ. -/
lemma stabilityFnDiag_eq_output (t : ButcherTableau s) (z : Fin s → ℂ)
    (_hdet : (1 - t.Aℂ * Matrix.diagonal z).det ≠ 0) :
    t.stabilityFnDiag z =
      1 + ∑ i : Fin s, t.bℂ i * (z i * resolvedStages t z i) := by
  simp only [stabilityFnDiag, resolvedStages, bℂ, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Matrix.diagonal_apply, mul_one]
  congr 1; apply Finset.sum_congr rfl; intro i _
  congr 1
  simp_rw [@eq_comm _ i, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp [Finset.mul_sum]

/-! ### RK step construction -/

/-- The nonzero-start RK step (y₀ = 1) matches the stability function computation. -/
lemma satisfiesRKStep_an (t : ButcherTableau s) (z : Fin s → ℂ)
    (hc : t.IsNonConfluent)
    (hdet : (1 - t.Aℂ * Matrix.diagonal z).det ≠ 0) :
    SatisfiesRKStep t (anTestField t z) 0 1 (1 : ℂ)
      (resolvedStages t z) (stageDerivs t z) (t.stabilityFnDiag z) := by
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · -- Stage equation: Yᵢ = 1 + 1 • ∑ⱼ aᵢⱼ • Fⱼ
    rw [resolvedStages_eq t z hdet i]
    simp only [stageDerivs, one_smul]
    congr 1; apply Finset.sum_congr rfl; intro j _
    simp [Aℂ]; ring
  · -- Stage derivative: Fᵢ = f(0 + 1 * cᵢ, Yᵢ) = zᵢ * Yᵢ
    simp only [stageDerivs, anTestField, zero_add, one_mul]
    rw [stageMultiplier_at_stage t z hc i]
  · -- Output: y₁ = R(z) = 1 + 1 • ∑ᵢ bᵢ • Fᵢ
    rw [stabilityFnDiag_eq_output t z hdet]
    simp only [stageDerivs, one_smul, bℂ, Complex.real_smul]

/-- The zero-start RK step is trivial: starting from 0 stays at 0. -/
lemma satisfiesRKStep_zero (t : ButcherTableau s) (z : Fin s → ℂ) :
    SatisfiesRKStep t (anTestField t z) 0 1 (0 : ℂ)
      (fun _ => 0) (fun _ => 0) (0 : ℂ) := by
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · simp [smul_zero, Finset.sum_const_zero]
  · simp [anTestField, mul_zero]
  · simp [smul_zero, Finset.sum_const_zero]

/-! ### Main theorem -/

/-- **Theorem 357D**: An irreducible non-confluent BN-stable method is AN-stable.

    Proof: For z with Re(zᵢ) ≤ 0, construct a dissipative field on ℂ (as ℝ²)
    and apply BN-stability to the RK step from y₀=1 and z₀=0. Contractivity
    gives |R(z)| = ‖R(z)-0‖ ≤ ‖1-0‖ = 1. -/
theorem bnStable_implies_anStable {t : ButcherTableau s}
    (hBN : IsBNStable.{0} t) (_hirr : ButcherTableau.IsDJIrreducible t)
    (hnc : t.IsNonConfluent) :
    t.IsANStable := by
  intro z hz hdet
  have hdiss := anTestField_dissipative t z hz
  have hstep := satisfiesRKStep_an t z hnc hdet
  have hstep0 := satisfiesRKStep_zero t z
  -- Apply BN-stability with E = ℂ to get contractivity
  have hcontr := hBN (anTestField t z) hdiss 0 1 zero_le_one
    1 0 (t.stabilityFnDiag z) 0
    (resolvedStages t z) (fun _ => 0)
    (stageDerivs t z) (fun _ => 0)
    hstep hstep0
  simp only [sub_zero, norm_one] at hcontr
  exact hcontr

end ButcherTableau
