import OpenMath.Basic

/-!
# Section 1.2: Linear Multistep Methods

Definitions and basic properties of linear multistep methods (LMMs) for ODEs.

A linear s-step method computes:
  ∑_{j=0}^{s} α_j y_{n+j} = h ∑_{j=0}^{s} β_j f(t_{n+j}, y_{n+j})
with normalization α_s = 1.

The first and second characteristic polynomials are:
  ρ(ξ) = ∑ α_j ξ^j,   σ(ξ) = ∑ β_j ξ^j.

A method is consistent if ρ(1) = 0 and ρ'(1) = σ(1).

Reference: Iserles, *A First Course in the Numerical Analysis of Differential Equations*,
Section 1.2.
-/

open Finset Real

/-! ## Definition of Linear Multistep Methods -/

/-- A linear s-step method for ODEs.
The method computes: ∑_{j=0}^{s} α_j y_{n+j} = h ∑_{j=0}^{s} β_j f(t_{n+j}, y_{n+j}).
Normalization: the leading coefficient α_s = 1. -/
structure LMM (s : ℕ) where
  /-- Coefficients of the solution values y_{n+j}. -/
  α : Fin (s + 1) → ℝ
  /-- Coefficients of the right-hand side evaluations f(t_{n+j}, y_{n+j}). -/
  β : Fin (s + 1) → ℝ
  /-- The leading coefficient is normalized to 1. -/
  normalized : α (Fin.last s) = 1

namespace LMM

variable {s : ℕ}

/-! ### Characteristic Polynomials -/

/-- First characteristic polynomial: ρ(ξ) = ∑_{j=0}^{s} α_j ξ^j. -/
noncomputable def rho (m : LMM s) (ξ : ℝ) : ℝ :=
  ∑ j : Fin (s + 1), m.α j * ξ ^ (j : ℕ)

/-- Second characteristic polynomial: σ(ξ) = ∑_{j=0}^{s} β_j ξ^j. -/
noncomputable def sigma (m : LMM s) (ξ : ℝ) : ℝ :=
  ∑ j : Fin (s + 1), m.β j * ξ ^ (j : ℕ)

/-- ρ(1) simplifies to ∑ α_j (since 1^j = 1 for all j). -/
theorem rho_one (m : LMM s) : m.rho 1 = ∑ j : Fin (s + 1), m.α j := by
  simp [rho]

/-- σ(1) simplifies to ∑ β_j. -/
theorem sigma_one (m : LMM s) : m.sigma 1 = ∑ j : Fin (s + 1), m.β j := by
  simp [sigma]

/-! ### Consistency -/

/-- A linear multistep method is **consistent** if:
1. ρ(1) = 0 (equivalently, ∑ α_j = 0), and
2. ρ'(1) = σ(1) (equivalently, ∑ j·α_j = ∑ β_j).

These ensure the method exactly reproduces constant and linear solutions. -/
structure IsConsistent (m : LMM s) : Prop where
  /-- The sum of α-coefficients is zero: ρ(1) = 0. -/
  sum_α_eq_zero : m.rho 1 = 0
  /-- The derivative condition: ρ'(1) = σ(1), i.e., ∑ j·α_j = ∑ β_j. -/
  deriv_match : (∑ j : Fin (s + 1), (j : ℝ) * m.α j) = m.sigma 1

/-- An explicit method has β_s = 0 (no implicit dependence on y_{n+s}). -/
def IsExplicit (m : LMM s) : Prop :=
  m.β (Fin.last s) = 0

/-- An implicit method has β_s ≠ 0. -/
def IsImplicit (m : LMM s) : Prop :=
  m.β (Fin.last s) ≠ 0

end LMM

/-! ## Standard Methods -/

/-- **Forward Euler** as a 1-step LMM: y_{n+1} = y_n + h·f(t_n, y_n).
Coefficients: α = [-1, 1], β = [1, 0]. -/
noncomputable def forwardEuler : LMM 1 where
  α := ![-1, 1]
  β := ![1, 0]
  normalized := by simp [Fin.last]

/-- **Backward Euler** as a 1-step LMM: y_{n+1} = y_n + h·f(t_{n+1}, y_{n+1}).
Coefficients: α = [-1, 1], β = [0, 1]. -/
noncomputable def backwardEuler : LMM 1 where
  α := ![-1, 1]
  β := ![0, 1]
  normalized := by simp [Fin.last]

/-- **Trapezoidal rule** as a 1-step LMM:
y_{n+1} = y_n + (h/2)·(f(t_n, y_n) + f(t_{n+1}, y_{n+1})).
Coefficients: α = [-1, 1], β = [1/2, 1/2]. -/
noncomputable def trapezoidalRule : LMM 1 where
  α := ![-1, 1]
  β := ![1/2, 1/2]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 2-step** method:
y_{n+2} = y_{n+1} + h·(3/2·f_{n+1} - 1/2·f_n).
Coefficients: α = [0, -1, 1], β = [-1/2, 3/2, 0]. -/
noncomputable def adamsBashforth2 : LMM 2 where
  α := ![0, -1, 1]
  β := ![-1/2, 3/2, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 2-step** method:
y_{n+2} = y_{n+1} + h·(5/12·f_{n+2} + 8/12·f_{n+1} - 1/12·f_n).
Coefficients: α = [0, -1, 1], β = [-1/12, 8/12, 5/12].
This is an implicit method of order 3.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsMoulton2 : LMM 2 where
  α := ![0, -1, 1]
  β := ![-1/12, 8/12, 5/12]
  normalized := by simp [Fin.last]

/-! ## Properties of Standard Methods -/

/-- Forward Euler is consistent. -/
theorem forwardEuler_consistent : forwardEuler.IsConsistent :=
  ⟨by simp [LMM.rho, forwardEuler, Fin.sum_univ_two],
   by simp [LMM.sigma, forwardEuler, Fin.sum_univ_two]⟩

/-- Forward Euler is explicit (β₁ = 0). -/
theorem forwardEuler_explicit : forwardEuler.IsExplicit := by
  simp [LMM.IsExplicit, forwardEuler, Fin.last]

/-- Backward Euler is consistent. -/
theorem backwardEuler_consistent : backwardEuler.IsConsistent :=
  ⟨by simp [LMM.rho, backwardEuler, Fin.sum_univ_two],
   by simp [LMM.sigma, backwardEuler, Fin.sum_univ_two]⟩

/-- Backward Euler is implicit (β₁ ≠ 0). -/
theorem backwardEuler_implicit : backwardEuler.IsImplicit := by
  simp [LMM.IsImplicit, backwardEuler, Fin.last]

/-- The trapezoidal rule is consistent. -/
theorem trapezoidalRule_consistent : trapezoidalRule.IsConsistent :=
  ⟨by simp [LMM.rho, trapezoidalRule, Fin.sum_univ_two],
   by simp [LMM.sigma, trapezoidalRule, Fin.sum_univ_two]; norm_num⟩

/-- The trapezoidal rule is implicit (β₁ ≠ 0). -/
theorem trapezoidalRule_implicit : trapezoidalRule.IsImplicit := by
  simp [LMM.IsImplicit, trapezoidalRule, Fin.last]

/-- Adams–Bashforth 2-step is consistent. -/
theorem adamsBashforth2_consistent : adamsBashforth2.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth2, Fin.sum_univ_three],
   by simp [LMM.sigma, adamsBashforth2, Fin.sum_univ_three]; norm_num⟩

/-- Adams–Bashforth 2-step is explicit (β₂ = 0). -/
theorem adamsBashforth2_explicit : adamsBashforth2.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth2, Fin.last]

/-- Adams–Moulton 2-step is consistent. -/
theorem adamsMoulton2_consistent : adamsMoulton2.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton2, Fin.sum_univ_three],
   by simp [LMM.sigma, adamsMoulton2, Fin.sum_univ_three]; norm_num⟩

/-- Adams–Moulton 2-step is implicit (β₂ = 5/12 ≠ 0). -/
theorem adamsMoulton2_implicit : adamsMoulton2.IsImplicit := by
  simp [LMM.IsImplicit, adamsMoulton2, Fin.last]

/-! ## Order of a Linear Multistep Method

The order of an LMM is defined via error constants. The q-th order condition value is:
  V_q = ∑_j j^q α_j - q · ∑_j j^{q-1} β_j
(unnormalized; the actual error constant is C_q = V_q / q!).

A method has order p if V_0 = ... = V_p = 0 and V_{p+1} ≠ 0.
Consistency (ρ(1) = 0 and ρ'(1) = σ(1)) is equivalent to V_0 = V_1 = 0,
so every consistent method has at least order 1.

Reference: Iserles, Section 1.2.
-/

namespace LMM

variable {s : ℕ}

/-- The q-th order condition value (unnormalized error constant) of an LMM:
  V_q = ∑_j j^q α_j - q · ∑_j j^{q-1} β_j.
  The actual error constant is C_q = V_q / q!.
  The method satisfies the q-th order condition when V_q = 0. -/
noncomputable def orderCondVal (m : LMM s) (q : ℕ) : ℝ :=
  (∑ j : Fin (s + 1), (j : ℝ) ^ q * m.α j) -
  (q : ℝ) * (∑ j : Fin (s + 1), (j : ℝ) ^ (q - 1) * m.β j)

/-- A linear multistep method has **order** p ≥ 1 if the first p+1 order conditions
  are satisfied (C_0 = ... = C_p = 0) and C_{p+1} ≠ 0. -/
structure HasOrder (m : LMM s) (p : ℕ) : Prop where
  /-- The first p+1 order conditions hold. -/
  conditions_hold : ∀ q, q ≤ p → m.orderCondVal q = 0
  /-- The (p+1)-th order condition fails. -/
  next_nonzero : m.orderCondVal (p + 1) ≠ 0

/-- The zeroth order condition value equals ρ(1). -/
theorem orderCondVal_zero (m : LMM s) : m.orderCondVal 0 = m.rho 1 := by
  simp [orderCondVal, rho]

/-- The first order condition value equals ρ'(1) - σ(1). -/
theorem orderCondVal_one (m : LMM s) :
    m.orderCondVal 1 = (∑ j : Fin (s + 1), (j : ℝ) * m.α j) - m.sigma 1 := by
  simp [orderCondVal, sigma]

/-- Consistency is equivalent to the first two order conditions holding. -/
theorem isConsistent_iff_orderCond (m : LMM s) :
    m.IsConsistent ↔ m.orderCondVal 0 = 0 ∧ m.orderCondVal 1 = 0 := by
  rw [orderCondVal_zero, orderCondVal_one, sub_eq_zero]
  constructor
  · intro ⟨h0, h1⟩; exact ⟨h0, h1⟩
  · intro ⟨h0, h1⟩; exact ⟨h0, h1⟩

/-- A method of order p ≥ 1 is consistent. -/
theorem HasOrder.isConsistent {m : LMM s} {p : ℕ} (h : m.HasOrder p) (hp : 1 ≤ p) :
    m.IsConsistent := by
  rw [isConsistent_iff_orderCond]
  exact ⟨h.conditions_hold 0 (Nat.zero_le _), h.conditions_hold 1 hp⟩

end LMM

/-! ### Order of Standard Methods -/

/-- Forward Euler has order 1. -/
theorem forwardEuler_order_one : forwardEuler.HasOrder 1 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;> simp [LMM.orderCondVal, forwardEuler, Fin.sum_univ_two]
  · simp [LMM.orderCondVal, forwardEuler, Fin.sum_univ_two]

/-- Backward Euler has order 1. -/
theorem backwardEuler_order_one : backwardEuler.HasOrder 1 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;> simp [LMM.orderCondVal, backwardEuler, Fin.sum_univ_two]
  · simp [LMM.orderCondVal, backwardEuler, Fin.sum_univ_two]; norm_num

/-- The trapezoidal rule has order 2. -/
theorem trapezoidalRule_order_two : trapezoidalRule.HasOrder 2 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q
    all_goals simp [LMM.orderCondVal, trapezoidalRule, Fin.sum_univ_two]
    all_goals norm_num
  · simp [LMM.orderCondVal, trapezoidalRule, Fin.sum_univ_two]; norm_num

/-- Adams–Bashforth 2-step has order 2. -/
theorem adamsBashforth2_order_two : adamsBashforth2.HasOrder 2 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;> simp [LMM.orderCondVal, adamsBashforth2, Fin.sum_univ_three] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth2, Fin.sum_univ_three]; norm_num

/-- Adams–Moulton 2-step has order 3. -/
theorem adamsMoulton2_order_three : adamsMoulton2.HasOrder 3 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton2, Fin.sum_univ_three] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton2, Fin.sum_univ_three]; norm_num

/-! ## Zero-Stability

A linear multistep method is zero-stable if all roots of its first characteristic
polynomial ρ lie in the closed unit disk, and any root on the unit circle is simple
(the root condition).

Reference: Iserles, *A First Course in the Numerical Analysis of Differential Equations*,
Section 1.5.
-/

namespace LMM

variable {s : ℕ}

/-- The first characteristic polynomial evaluated over ℂ:
  ρ_ℂ(ξ) = ∑_{j=0}^{s} α_j ξ^j where α_j are cast from ℝ to ℂ. -/
noncomputable def rhoC (m : LMM s) (ξ : ℂ) : ℂ :=
  ∑ j : Fin (s + 1), (m.α j : ℂ) * ξ ^ (j : ℕ)

/-- The formal derivative of ρ evaluated over ℂ:
  ρ'_ℂ(ξ) = ∑_{j=0}^{s} j · α_j · ξ^{j-1}. -/
noncomputable def rhoCDeriv (m : LMM s) (ξ : ℂ) : ℂ :=
  ∑ j : Fin (s + 1), ((j : ℕ) : ℂ) * (m.α j : ℂ) * ξ ^ ((j : ℕ) - 1)

/-- A linear multistep method is **zero-stable** if all roots of ρ (over ℂ) lie in the
closed unit disk, and roots on the unit circle are simple (ρ'(ξ) ≠ 0 there).
This is the "root condition" (Iserles, Section 1.5). -/
structure IsZeroStable (m : LMM s) : Prop where
  /-- All roots of ρ lie in the closed unit disk. -/
  roots_in_disk : ∀ ξ : ℂ, m.rhoC ξ = 0 → ‖ξ‖ ≤ 1
  /-- Roots on the unit circle are simple. -/
  unit_roots_simple : ∀ ξ : ℂ, m.rhoC ξ = 0 → ‖ξ‖ = 1 → m.rhoCDeriv ξ ≠ 0

end LMM

/-! ### Zero-Stability of Standard Methods -/

/-- Forward Euler is zero-stable: ρ(ξ) = ξ - 1 has sole root ξ = 1, which is simple. -/
theorem forwardEuler_zeroStable : forwardEuler.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, forwardEuler, Fin.sum_univ_two] at hξ
    have h : ξ = 1 := by linear_combination hξ
    rw [h]; simp
  unit_roots_simple := by
    intro ξ hξ _
    simp [LMM.rhoCDeriv, forwardEuler, Fin.sum_univ_two]

/-- Backward Euler is zero-stable: ρ(ξ) = ξ - 1 has sole root ξ = 1, which is simple. -/
theorem backwardEuler_zeroStable : backwardEuler.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, backwardEuler, Fin.sum_univ_two] at hξ
    have h : ξ = 1 := by linear_combination hξ
    rw [h]; simp
  unit_roots_simple := by
    intro ξ hξ _
    simp [LMM.rhoCDeriv, backwardEuler, Fin.sum_univ_two]

/-- The trapezoidal rule is zero-stable: ρ(ξ) = ξ - 1 has sole root ξ = 1, which is simple. -/
theorem trapezoidalRule_zeroStable : trapezoidalRule.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, trapezoidalRule, Fin.sum_univ_two] at hξ
    have h : ξ = 1 := by linear_combination hξ
    rw [h]; simp
  unit_roots_simple := by
    intro ξ hξ _
    simp [LMM.rhoCDeriv, trapezoidalRule, Fin.sum_univ_two]

/-- Adams–Bashforth 2-step is zero-stable: ρ(ξ) = ξ² - ξ has roots 0 and 1,
both in the closed unit disk, and the unit root ξ = 1 is simple (ρ'(1) = 1 ≠ 0). -/
theorem adamsBashforth2_zeroStable : adamsBashforth2.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, adamsBashforth2, Fin.sum_univ_three] at hξ
    have h : ξ * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · rw [h0]; simp
    · have : ξ = 1 := by linear_combination h1
      rw [this]; simp
  unit_roots_simple := by
    intro ξ hξ habs
    simp [LMM.rhoCDeriv, adamsBashforth2, Fin.sum_univ_three]
    simp [LMM.rhoC, adamsBashforth2, Fin.sum_univ_three] at hξ
    have h : ξ * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · rw [h0] at habs; simp at habs
    · have h1' : ξ = 1 := by linear_combination h1
      rw [h1']; norm_num

/-- Adams–Moulton 2-step is zero-stable: ρ(ξ) = ξ² - ξ has roots 0 and 1
(same as Adams–Bashforth 2-step). -/
theorem adamsMoulton2_zeroStable : adamsMoulton2.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, adamsMoulton2, Fin.sum_univ_three] at hξ
    have h : ξ * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · rw [h0]; simp
    · have : ξ = 1 := by linear_combination h1
      rw [this]; simp
  unit_roots_simple := by
    intro ξ hξ habs
    simp [LMM.rhoCDeriv, adamsMoulton2, Fin.sum_univ_three]
    simp [LMM.rhoC, adamsMoulton2, Fin.sum_univ_three] at hξ
    have h : ξ * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · rw [h0] at habs; simp at habs
    · have h1' : ξ = 1 := by linear_combination h1
      rw [h1']; norm_num

/-! ## Stability Polynomial and A-Stability

The stability polynomial for the test equation y' = λy is:
  π(ξ, z) = ρ(ξ) - z · σ(ξ), where z = hλ.

A method is A-stable if its stability region contains the closed left half-plane.

Reference: Iserles, *A First Course in the Numerical Analysis of Differential Equations*,
Chapter 3.
-/

namespace LMM

variable {s : ℕ}

/-- Second characteristic polynomial over ℂ:
  σ_ℂ(ξ) = ∑_{j=0}^{s} β_j ξ^j where β_j are cast from ℝ to ℂ. -/
noncomputable def sigmaC (m : LMM s) (ξ : ℂ) : ℂ :=
  ∑ j : Fin (s + 1), (m.β j : ℂ) * ξ ^ (j : ℕ)

/-- Stability polynomial for the test equation y' = λy:
  π(ξ, z) = ρ(ξ) - z · σ(ξ) where z = hλ ∈ ℂ. -/
noncomputable def stabilityPoly (m : LMM s) (ξ z : ℂ) : ℂ :=
  m.rhoC ξ - z * m.sigmaC ξ

/-- A value z ∈ ℂ is in the **stability region** of the method if all roots of the
stability polynomial π(·, z) lie in the closed unit disk. -/
def InStabilityRegion (m : LMM s) (z : ℂ) : Prop :=
  ∀ ξ : ℂ, m.stabilityPoly ξ z = 0 → ‖ξ‖ ≤ 1

/-- An LMM is **A-stable** if its stability region contains the entire closed left
half-plane {z ∈ ℂ : Re(z) ≤ 0}.
A-stable methods can handle stiff equations without step-size restrictions.
Reference: Iserles, Definition 3.3. -/
def IsAStable (m : LMM s) : Prop :=
  ∀ z : ℂ, z.re ≤ 0 → m.InStabilityRegion z

end LMM

/-! ### A-Stability of Standard Methods -/

/-- Backward Euler is A-stable: the amplification factor 1/(1-z) has |·| ≤ 1
when Re(z) ≤ 0, since |1-z| ≥ 1. -/
theorem backwardEuler_aStable : backwardEuler.IsAStable := by
  intro z hz ξ hξ
  simp only [LMM.stabilityPoly, LMM.rhoC, LMM.sigmaC, backwardEuler] at hξ
  simp [Fin.sum_univ_two] at hξ ⊢
  have key : ξ * (1 - z) = 1 := by linear_combination hξ
  have hnorm : ‖ξ‖ * ‖(1 : ℂ) - z‖ = 1 := by
    rw [← norm_mul, key, norm_one]
  have h1z_ge : 1 ≤ ‖(1 : ℂ) - z‖ := by
    have h1 := Complex.abs_re_le_norm ((1 : ℂ) - z)
    simp [Complex.sub_re] at h1
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - z.re)] at h1
    linarith
  nlinarith [norm_nonneg ξ, norm_nonneg ((1 : ℂ) - z)]

/-- The trapezoidal rule is A-stable: the amplification factor (2+z)/(2-z) has |·| ≤ 1
when Re(z) ≤ 0, since |2+z| ≤ |2-z|. -/
theorem trapezoidalRule_aStable : trapezoidalRule.IsAStable := by
  intro z hz ξ hξ
  simp only [LMM.stabilityPoly, LMM.rhoC, LMM.sigmaC, trapezoidalRule] at hξ
  simp [Fin.sum_univ_two] at hξ ⊢
  have key : (2 - z) * ξ = 2 + z := by linear_combination 2 * hξ
  have hnorm : ‖(2 : ℂ) - z‖ * ‖ξ‖ = ‖(2 : ℂ) + z‖ := by
    rw [← norm_mul, key]
  have h_denom_ne : (2 : ℂ) - z ≠ 0 := by
    intro h; have : ((2 : ℂ) - z).re = 0 := by rw [h]; simp
    simp at this; linarith
  have h_denom_pos : (0 : ℝ) < ‖(2 : ℂ) - z‖ := norm_pos_iff.mpr h_denom_ne
  have h_nsq_le : ‖(2 : ℂ) + z‖ ^ 2 ≤ ‖(2 : ℂ) - z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im]
    norm_num
    nlinarith
  have h_num_le : ‖(2 : ℂ) + z‖ ≤ ‖(2 : ℂ) - z‖ := by
    nlinarith [norm_nonneg ((2 : ℂ) + z), norm_nonneg ((2 : ℂ) - z),
               sq_nonneg (‖(2 : ℂ) - z‖ - ‖(2 : ℂ) + z‖)]
  nlinarith [norm_nonneg ξ]

/-- Forward Euler is **not** A-stable: z = -3 gives amplification factor |1+z| = 2 > 1. -/
theorem forwardEuler_not_aStable : ¬forwardEuler.IsAStable := by
  intro h
  have h1 := h ((-3 : ℝ) : ℂ) (by simp) ((-2 : ℝ) : ℂ) (by
    simp only [LMM.stabilityPoly, LMM.rhoC, LMM.sigmaC, forwardEuler]
    simp [Fin.sum_univ_two]; norm_num)
  norm_num at h1

/-! ## BDF2 (Backward Differentiation Formula, 2-step)

The BDF2 method: y_{n+2} - (4/3)y_{n+1} + (1/3)y_n = (2/3)h·f_{n+2}.
It is implicit, A-stable, and has order 2.

Reference: Iserles, Section 3.3.
-/

/-- **BDF2** (Backward Differentiation Formula, 2-step):
  y_{n+2} - (4/3)y_{n+1} + (1/3)y_n = (2/3)h·f_{n+2}.
  Coefficients: α = [1/3, -4/3, 1], β = [0, 0, 2/3]. -/
noncomputable def bdf2 : LMM 2 where
  α := ![1/3, -4/3, 1]
  β := ![0, 0, 2/3]
  normalized := by simp [Fin.last]

/-- BDF2 is consistent. -/
theorem bdf2_consistent : bdf2.IsConsistent :=
  ⟨by simp [LMM.rho, bdf2, Fin.sum_univ_three]; norm_num,
   by simp [LMM.sigma, bdf2, Fin.sum_univ_three]; norm_num⟩

/-- BDF2 has order 2. -/
theorem bdf2_order_two : bdf2.HasOrder 2 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, bdf2, Fin.sum_univ_three] <;> norm_num
  · simp [LMM.orderCondVal, bdf2, Fin.sum_univ_three]; norm_num

/-- BDF2 is implicit (β₂ = 2/3 ≠ 0). -/
theorem bdf2_implicit : bdf2.IsImplicit := by
  simp [LMM.IsImplicit, bdf2, Fin.last]

/-- BDF2 is zero-stable: ρ(ξ) = ξ² - (4/3)ξ + 1/3 = (ξ-1)(ξ-1/3)
has roots 1 and 1/3, both in the closed unit disk,
and the unit root ξ = 1 is simple (ρ'(1) = 2/3 ≠ 0). -/
theorem bdf2_zeroStable : bdf2.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp only [LMM.rhoC, bdf2] at hξ
    simp [Fin.sum_univ_three] at hξ
    have h : (ξ - 1) * (ξ - 1/3) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have : ξ = 1 := by linear_combination h0
      rw [this]; simp
    · have : ξ = 1/3 := by linear_combination h1
      rw [this]; simp; norm_num
  unit_roots_simple := by
    intro ξ hξ habs
    simp only [LMM.rhoCDeriv, bdf2]
    simp only [LMM.rhoC, bdf2] at hξ
    simp [Fin.sum_univ_three] at hξ
    have h : (ξ - 1) * (ξ - 1/3) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ1 : ξ = 1 := by linear_combination h0
      rw [hξ1]
      simp [Fin.sum_univ_three]; norm_num
    · have hξ13 : ξ = 1/3 := by linear_combination h1
      rw [hξ13] at habs; norm_num at habs

/-! ## Dahlquist's Second Barrier

No A-stable LMM can have order greater than 2. The trapezoidal rule achieves this bound.

The proof uses the boundary locus method:
1. A-stability implies all roots of ρ lie in the closed unit disk (from z = 0).
2. The E-function E(ζ) = σ(ζ)/ρ(ζ) has Re(E(e^{iθ})) ≥ 0 for all θ where ρ(e^{iθ}) ≠ 0.
3. For a method of order p ≥ 3, the function G(ζ) = E(ζ) - 1/(ζ-1) - 1/2 is analytic
   at ζ = 1 and vanishes there. Since Re(G(e^{iθ})) = Re(E(e^{iθ})) ≥ 0 and G(1) = 0,
   this contradicts the maximum principle for harmonic functions.

Reference: Iserles, Theorem 3.4.
-/

namespace LMM

variable {s : ℕ}

/-- A-stability implies all roots of ρ lie in the closed unit disk.
This follows directly by evaluating the A-stability condition at z = 0. -/
theorem IsAStable.rho_roots_in_disk (m : LMM s) (ha : m.IsAStable) :
    ∀ ξ : ℂ, m.rhoC ξ = 0 → ‖ξ‖ ≤ 1 := by
  intro ξ hξ
  apply ha 0 (le_refl _)
  simp [stabilityPoly, hξ]

/-- Key lemma (boundary locus analysis): For an A-stable method, the E-function
E(ζ) = σ(ζ)/ρ(ζ) satisfies Re(E(e^{iθ})) ≥ 0 on the unit circle away from roots of ρ.
This encodes the fact that the boundary of the stability region lies in the closed right
half-plane. The proof requires careful analysis of the stability polynomial roots as z
varies along the imaginary axis.
Reference: Iserles, proof of Theorem 3.4, step 1. -/
theorem IsAStable.E_nonneg_re (m : LMM s) (ha : m.IsAStable)
    (θ : ℝ) (hρ : m.rhoC (Complex.exp (↑θ * Complex.I)) ≠ 0)
    (hσ : m.sigmaC (Complex.exp (↑θ * Complex.I)) ≠ 0) :
    0 ≤ (m.sigmaC (Complex.exp (↑θ * Complex.I)) /
         m.rhoC (Complex.exp (↑θ * Complex.I))).re := by
  -- Proof by contradiction using the boundary locus method.
  -- If Re(σ/ρ) < 0 at ζ = e^{iθ}, then Re(ρ/σ) < 0. By continuity, Re(ρ/σ) < 0
  -- for r·ζ with r slightly > 1. But |r·ζ| > 1 and A-stability forces Re(ρ/σ) > 0
  -- at such points — contradiction.
  by_contra h_neg
  push_neg at h_neg
  set ζ := Complex.exp (↑θ * Complex.I) with hζ_def
  -- Step 1: Re(σ/ρ) < 0 implies Re(ρ/σ) < 0 (reciprocal preserves sign of Re)
  have hE_ne : m.sigmaC ζ / m.rhoC ζ ≠ 0 := div_ne_zero hσ hρ
  have h_rho_sigma_neg : (m.rhoC ζ / m.sigmaC ζ).re < 0 := by
    have h_eq : m.rhoC ζ / m.sigmaC ζ = (m.sigmaC ζ / m.rhoC ζ)⁻¹ := by
      field_simp
    rw [h_eq, Complex.inv_re]
    exact div_neg_of_neg_of_pos h_neg (Complex.normSq_pos.mpr hE_ne)
  -- Step 2: For r > 1 with σ(r·ζ) ≠ 0, A-stability forces ¬(Re(ρ(r·ζ)/σ(r·ζ)) ≤ 0)
  -- Because r·ζ is a root of π(·, z) with |r·ζ| = r > 1.
  have key : ∀ r : ℝ, 1 < r → m.sigmaC ((r : ℂ) * ζ) ≠ 0 →
      ¬(m.rhoC ((r : ℂ) * ζ) / m.sigmaC ((r : ℂ) * ζ)).re ≤ 0 := by
    intro r hr hσr hle
    have h_stab : m.stabilityPoly ((r : ℂ) * ζ)
        (m.rhoC ((r : ℂ) * ζ) / m.sigmaC ((r : ℂ) * ζ)) = 0 := by
      simp only [stabilityPoly, sub_eq_zero]
      exact (div_mul_cancel₀ (m.rhoC ((r : ℂ) * ζ)) hσr).symm
    have h_le := ha _ hle _ h_stab
    have h_norm : ‖(↑r : ℂ) * ζ‖ = r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith : (0 : ℝ) < r),
          hζ_def, Complex.norm_exp_ofReal_mul_I, mul_one]
    linarith
  -- Step 3: Continuity of ρ and σ as functions of r
  have hσ_cont : Continuous (fun r : ℝ => m.sigmaC ((r : ℂ) * ζ)) := by
    unfold sigmaC; apply continuous_finset_sum; intro j _
    exact continuous_const.mul ((Complex.continuous_ofReal.mul continuous_const).pow _)
  have hρ_cont : Continuous (fun r : ℝ => m.rhoC ((r : ℂ) * ζ)) := by
    unfold rhoC; apply continuous_finset_sum; intro j _
    exact continuous_const.mul ((Complex.continuous_ofReal.mul continuous_const).pow _)
  -- Step 4: The quotient Re(ρ/σ) is continuous at r = 1 (since σ(ζ) ≠ 0)
  have hσ1 : m.sigmaC ((1 : ℂ) * ζ) ≠ 0 := by rwa [one_mul]
  have hquot_cont : ContinuousAt
      (fun r : ℝ => m.rhoC ((r : ℂ) * ζ) / m.sigmaC ((r : ℂ) * ζ)) 1 :=
    hρ_cont.continuousAt.div hσ_cont.continuousAt hσ1
  have hre_cont : ContinuousAt
      (fun r : ℝ => (m.rhoC ((r : ℂ) * ζ) / m.sigmaC ((r : ℂ) * ζ)).re) 1 :=
    Complex.continuous_re.continuousAt.comp hquot_cont
  -- Step 5: f(1) = Re(ρ(ζ)/σ(ζ)) < 0
  have hf1_neg : (fun r : ℝ =>
      (m.rhoC ((r : ℂ) * ζ) / m.sigmaC ((r : ℂ) * ζ)).re) 1 < 0 := by
    simp only [Complex.ofReal_one, one_mul]; exact h_rho_sigma_neg
  -- Step 6: By continuity, Re(ρ(r·ζ)/σ(r·ζ)) < 0 in a neighborhood of r = 1
  have h_ev := hre_cont.eventually (Iio_mem_nhds hf1_neg)
  -- Step 7: Extract r > 1 from the neighborhood
  rw [Filter.eventually_iff_exists_mem] at h_ev
  obtain ⟨U, hU_nhds, hU⟩ := h_ev
  rw [Metric.mem_nhds_iff] at hU_nhds
  obtain ⟨ε, hε_pos, hε_ball⟩ := hU_nhds
  have hr_mem : 1 + ε / 2 ∈ U := by
    apply hε_ball; rw [Metric.mem_ball, Real.dist_eq]
    rw [show 1 + ε / 2 - 1 = ε / 2 from by ring, abs_of_pos (by linarith)]; linarith
  have hf_neg := hU _ hr_mem
  -- σ(r·ζ) ≠ 0 (if σ = 0 then ρ/σ = 0 and Re(0) = 0, contradicting Re < 0)
  have hσr_ne : m.sigmaC (((1 + ε / 2 : ℝ) : ℂ) * ζ) ≠ 0 := by
    intro heq; rw [heq, div_zero, Complex.zero_re] at hf_neg; linarith
  -- Contradiction: key says ¬(Re ≤ 0), but hf_neg says Re < 0
  exact key (1 + ε / 2) (by linarith) hσr_ne (le_of_lt hf_neg)

/-- Key lemma (order constraint): For a method of order p ≥ 3, the modified E-function
G(ζ) = E(ζ) - 1/(ζ-1) - 1/2 vanishes at ζ = 1 (i.e., G is analytic at ζ = 1 with G(1) = 0).
Combined with Re(G(e^{iθ})) ≥ 0 from A-stability and the fact that Re(1/(e^{iθ}-1)+1/2) = 0,
this gives a non-negative harmonic function vanishing at a point, which by the minimum principle
for harmonic functions must be identically zero — contradicting G being a non-trivial
rational function.
Reference: Iserles, proof of Theorem 3.4, step 2. -/
theorem order_ge_three_not_aStable (m : LMM s) (p : ℕ) (hp : m.HasOrder p) (hp3 : 3 ≤ p)
    (ha : m.IsAStable) : False := by
  sorry

/-- **Dahlquist's Second Barrier** (Iserles, Theorem 3.4):
An A-stable linear multistep method has order at most 2. -/
theorem dahlquist_second_barrier {s : ℕ} (m : LMM s) (p : ℕ)
    (hp : m.HasOrder p) (ha : m.IsAStable) : p ≤ 2 := by
  by_contra h
  push_neg at h
  exact order_ge_three_not_aStable m p hp h ha

end LMM
