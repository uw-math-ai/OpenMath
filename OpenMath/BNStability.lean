import OpenMath.StiffEquations

/-!
# Theorem 357C: Algebraic stability implies BN-stability

Sorry-first staging file for the BN-stability direction in Iserles, Theorem 357C.
This file is intentionally isolated from `OpenMath/ANStability.lean` because the
AN-stability file is currently under repair in cycle 115.
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

/-- The algebraic identity `(357e)` for the difference of two RK solutions. -/
lemma rk_stage_difference_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ButcherTableau s) (x h : ℝ) (f : ℝ → E → E)
    (y₀ z₀ y₁ z₁ : E) (Y Z F G : Fin s → E)
    (hy : SatisfiesRKStep t f x h y₀ Y F y₁)
    (hz : SatisfiesRKStep t f x h z₀ Z G z₁) :
    ∀ i : Fin s, Y i - Z i = (y₀ - z₀) + h • ∑ j : Fin s, (t.A i j) • (F j - G j) := by
  sorry

lemma rk_output_difference_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ButcherTableau s) (x h : ℝ) (f : ℝ → E → E)
    (y₀ z₀ y₁ z₁ : E) (Y Z F G : Fin s → E)
    (hy : SatisfiesRKStep t f x h y₀ Y F y₁)
    (hz : SatisfiesRKStep t f x h z₀ Z G z₁) :
    y₁ - z₁ = (y₀ - z₀) + h • ∑ i : Fin s, (t.b i) • (F i - G i) := by
  sorry

lemma algStabMatrix_inner_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {t : ButcherTableau s} (ht : t.IsAlgStable) (U : Fin s → E) :
    0 ≤ ∑ i : Fin s, ∑ j : Fin s, t.algStabMatrix i j * @inner ℝ E _ (U i) (U j) := by
  sorry

lemma rk_step_diff_norm_sq_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : ButcherTableau s) (x h : ℝ) (f : ℝ → E → E)
    (y₀ z₀ y₁ z₁ : E) (Y Z F G : Fin s → E)
    (hy : SatisfiesRKStep t f x h y₀ Y F y₁)
    (hz : SatisfiesRKStep t f x h z₀ Z G z₁) :
    ‖(y₁ - z₁) - (y₀ - z₀)‖ ^ 2 =
      2 * h * ∑ i : Fin s, t.b i * @inner ℝ E _ (Y i - Z i) (F i - G i)
        - h ^ 2 *
          ∑ i : Fin s, ∑ j : Fin s,
            t.algStabMatrix i j * @inner ℝ E _ (F i - G i) (F j - G j) := by
  sorry

/-- **Theorem 357C**: algebraic stability implies BN-stability. -/
theorem alg_stable_implies_bn_stable {t : ButcherTableau s}
    (ht : t.IsAlgStable) : t.IsBNStable := by
  intro E _ _ f hf x h hh y₀ z₀ y₁ z₁ Y Z F G hy hz
  sorry

end ButcherTableau
