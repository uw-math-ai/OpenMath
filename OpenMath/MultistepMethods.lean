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

/-- On the unit circle, Re(1/(e^{iθ}-1)) = -1/2 when e^{iθ} ≠ 1.
Proof: 1/(e^{iθ}-1) = ((cos θ - 1) - i sin θ)/(2 - 2cos θ),
so Re = (cos θ - 1)/(2 - 2cos θ) = -1/2. -/
theorem re_inv_exp_sub_one (θ : ℝ) (hne : Complex.exp (↑θ * Complex.I) ≠ 1) :
    (1 / (Complex.exp (↑θ * Complex.I) - 1)).re = -1/2 := by
  set ζ := Complex.exp (↑θ * Complex.I)
  have hζ_nsq : Complex.normSq ζ = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; norm_num
  have hne_sub : ζ - 1 ≠ 0 := sub_ne_zero.mpr hne
  rw [one_div, Complex.inv_re]
  have h_nsq : Complex.normSq (ζ - 1) = 2 - 2 * ζ.re := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
        Complex.one_im, sub_zero]
    have : ζ.re * ζ.re + ζ.im * ζ.im = 1 := by rw [← Complex.normSq_apply, hζ_nsq]
    nlinarith
  rw [h_nsq, Complex.sub_re, Complex.one_re]
  have hre_ne : ζ.re ≠ 1 := by
    intro h; apply hne_sub
    rw [Complex.normSq_apply] at hζ_nsq
    have him : ζ.im = 0 := by nlinarith
    exact Complex.ext (by simp [Complex.sub_re, h]) (by simp [Complex.sub_im, him])
  have hd_ne : 2 - 2 * ζ.re ≠ 0 := by intro h; apply hre_ne; linarith
  rw [div_eq_iff hd_ne]; linarith

/-- ρ_ℂ(1) equals ρ(1) cast to ℂ. -/
theorem rhoC_one_cast (m : LMM s) : m.rhoC 1 = (m.rho 1 : ℂ) := by
  simp [rhoC, rho]

/-- For a consistent method, ρ_ℂ(1) = 0. -/
theorem IsConsistent.rhoC_one (m : LMM s) (hc : m.IsConsistent) : m.rhoC 1 = 0 := by
  rw [rhoC_one_cast, hc.sum_α_eq_zero, Complex.ofReal_zero]

/-- The "modified numerator": N(ζ) = 2·σ(ζ)·(ζ-1) - ρ(ζ)·(ζ+1).
When σ/ρ = 1/(ζ-1) + 1/2, this is zero. The order conditions force N to vanish
at ζ = 1 to a specific order. -/
noncomputable def modifiedNumeratorC (m : LMM s) (ζ : ℂ) : ℂ :=
  2 * m.sigmaC ζ * (ζ - 1) - m.rhoC ζ * (ζ + 1)

/-- For order ≥ 1 (consistency), N(1) = 0.
Proof: N(1) = 2σ(1)·0 - ρ(1)·2 = -2ρ(1) = 0. -/
theorem modifiedNumeratorC_one (m : LMM s) {p : ℕ} (hp : m.HasOrder p) (hp1 : 1 ≤ p) :
    m.modifiedNumeratorC 1 = 0 := by
  have hρ1 := (hp.isConsistent hp1).rhoC_one m
  simp [modifiedNumeratorC, hρ1]

/-- For a consistent method, σ_ℂ(1) = ρ'_ℂ(1).
This is the complex version of the consistency condition ρ'(1) = σ(1). -/
theorem IsConsistent.sigmaC_one_eq_rhoCDeriv_one (m : LMM s)
    (hc : m.IsConsistent) : m.sigmaC 1 = m.rhoCDeriv 1 := by
  simp only [sigmaC, rhoCDeriv, one_pow, mul_one]
  have h := hc.deriv_match
  rw [sigma_one] at h
  -- ∑ (m.β j : ℂ) = ∑ ((j:ℕ):ℂ) * (m.α j : ℂ)
  -- follows from h : ∑ (j:ℝ) * m.α j = ∑ m.β j by casting to ℂ
  have hc := congr_arg (Complex.ofReal) h
  push_cast at hc ⊢
  exact hc.symm

/-- For a zero-stable, consistent method, σ_ℂ(1) ≠ 0.
Proof: σ_ℂ(1) = ρ'_ℂ(1) ≠ 0 (simple root from zero-stability). -/
theorem IsConsistent.sigmaC_one_ne_zero (m : LMM s) (hc : m.IsConsistent)
    (hzs : m.IsZeroStable) : m.sigmaC 1 ≠ 0 := by
  rw [hc.sigmaC_one_eq_rhoCDeriv_one]
  exact hzs.unit_roots_simple 1 (hc.rhoC_one m) (by simp)

/-- ρ_ℂ commutes with complex conjugation: ρ_ℂ(conj z) = conj(ρ_ℂ(z)).
This holds because ρ has real coefficients. -/
theorem rhoC_conj (m : LMM s) (z : ℂ) :
    m.rhoC (starRingEnd ℂ z) = starRingEnd ℂ (m.rhoC z) := by
  simp only [rhoC, map_sum, map_mul, map_pow, Complex.conj_ofReal]

/-- σ_ℂ commutes with complex conjugation: σ_ℂ(conj z) = conj(σ_ℂ(z)).
This holds because σ has real coefficients. -/
theorem sigmaC_conj (m : LMM s) (z : ℂ) :
    m.sigmaC (starRingEnd ℂ z) = starRingEnd ℂ (m.sigmaC z) := by
  simp only [sigmaC, map_sum, map_mul, map_pow, Complex.conj_ofReal]

/-- On the unit circle, the E-function σ/ρ satisfies Re(σ(ζ⁻¹)/ρ(ζ⁻¹)) = Re(σ(ζ)/ρ(ζ)),
because σ(ζ⁻¹)/ρ(ζ⁻¹) = conj(σ(ζ)/ρ(ζ)) when |ζ| = 1 (since the coefficients are real
and ζ⁻¹ = conj(ζ) on the unit circle). -/
theorem E_re_inv_eq (m : LMM s) (ζ : ℂ) (habs : ‖ζ‖ = 1) :
    (m.sigmaC ζ⁻¹ / m.rhoC ζ⁻¹).re = (m.sigmaC ζ / m.rhoC ζ).re := by
  -- ζ⁻¹ = conj(ζ) on the unit circle
  have hinv : ζ⁻¹ = starRingEnd ℂ ζ := by
    have hne : ζ ≠ 0 := by intro h; simp [h] at habs
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, habs]; simp
  rw [hinv, m.sigmaC_conj, m.rhoC_conj, ← map_div₀, Complex.conj_re]

/-- The "cross-energy" Re(σ(ζ)·conj(ρ(ζ))) is non-negative on the unit circle
for A-stable methods. This follows from Re(σ/ρ) ≥ 0 and |ρ|² ≥ 0. -/
theorem cross_energy_nonneg (m : LMM s) (ha : m.IsAStable)
    (θ : ℝ) :
    0 ≤ (m.sigmaC (Complex.exp (↑θ * Complex.I)) *
         starRingEnd ℂ (m.rhoC (Complex.exp (↑θ * Complex.I)))).re := by
  set ζ := Complex.exp (↑θ * Complex.I)
  by_cases hρ : m.rhoC ζ = 0
  · simp [hρ]
  · by_cases hσ : m.sigmaC ζ = 0
    · rw [hσ, zero_mul, Complex.zero_re]
    · -- Re(σ·conj(ρ)) = Re(σ/ρ · |ρ|²) = Re(σ/ρ) · |ρ|²
      have h_eq : (m.sigmaC ζ * starRingEnd ℂ (m.rhoC ζ)).re =
          (m.sigmaC ζ / m.rhoC ζ).re * Complex.normSq (m.rhoC ζ) := by
        conv_lhs => rw [show m.sigmaC ζ = (m.sigmaC ζ / m.rhoC ζ) * m.rhoC ζ from
          (div_mul_cancel₀ _ hρ).symm]
        rw [mul_assoc, Complex.mul_conj, Complex.mul_re,
            Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [h_eq]
      exact mul_nonneg (IsAStable.E_nonneg_re m ha θ hρ hσ) (Complex.normSq_nonneg _)

/-! ### Minimum Principle for Harmonic Functions

The minimum principle for the real part of an analytic function, proved via
the maximum modulus principle. Used in the proof of Dahlquist's second barrier. -/

/-- **Minimum principle for Re of analytic functions on a bounded domain**:
If `f` is differentiable on `U` and continuous on `closure U`, and `Re(f) ≥ 0`
on the frontier of `U`, then `Re(f) ≥ 0` on `closure U`.

Proof via the maximum modulus principle applied to `exp(-f)`:
- `‖exp(-f(z))‖ = exp(-Re(f(z))) ≤ 1` on the frontier (since `Re(f) ≥ 0`)
- By the maximum modulus principle, `‖exp(-f(z))‖ ≤ 1` on the closure
- Hence `Re(f(z)) ≥ 0` on the closure -/
theorem re_nonneg_of_frontier_re_nonneg {U : Set ℂ}
    (hU : Bornology.IsBounded U)
    (f : ℂ → ℂ) (hf : DiffContOnCl ℂ f U)
    (hbd : ∀ z ∈ frontier U, 0 ≤ (f z).re) :
    ∀ z ∈ closure U, 0 ≤ (f z).re := by
  intro z hz
  -- Consider g(z) = exp(-f(z))
  set g : ℂ → ℂ := fun w => Complex.exp (-f w)
  -- g is DiffContOnCl on U
  have hg : DiffContOnCl ℂ g U := ⟨hf.1.neg.cexp, hf.2.neg.cexp⟩
  -- On frontier U, ‖g(z)‖ = exp(-Re(f(z))) ≤ exp(0) = 1
  have hg_bd : ∀ w ∈ frontier U, ‖g w‖ ≤ 1 := by
    intro w hw
    simp only [g, Complex.norm_exp, Complex.neg_re]
    have : 0 ≤ (f w).re := hbd w hw
    linarith [Real.exp_le_one_iff.mpr (by linarith : -(f w).re ≤ 0)]
  -- By the maximum modulus principle: ‖g(z)‖ ≤ 1 on closure U
  have hmm := Complex.norm_le_of_forall_mem_frontier_norm_le hU hg hg_bd hz
  -- Unpack: exp(-Re(f(z))) ≤ 1, so -Re(f(z)) ≤ 0, so Re(f(z)) ≥ 0
  simp only [g, Complex.norm_exp, Complex.neg_re] at hmm
  linarith [Real.exp_le_one_iff.mp hmm]

/-- On the unit circle, Re(1/(ζ-1)) = -1/2 when ζ ≠ 1 (abstract version).
This is the same computation as `re_inv_exp_sub_one` but stated for any ζ with ‖ζ‖ = 1. -/
theorem re_inv_sub_one_of_norm_one (ζ : ℂ) (habs : ‖ζ‖ = 1) (hne : ζ ≠ 1) :
    (1 / (ζ - 1)).re = -1/2 := by
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff ζ).mp habs
  rw [← hθ]
  exact re_inv_exp_sub_one θ (by rwa [hθ])

/-- On the unit circle, Re((ζ+1)/(2(ζ-1))) = 0 when ζ ≠ 1.
Proof: (ζ+1)/(2(ζ-1)) = 1/2 + 1/(ζ-1), and Re(1/(ζ-1)) = -1/2. -/
theorem re_half_plus_inv_sub_one_eq_zero (ζ : ℂ) (habs : ‖ζ‖ = 1) (hne : ζ ≠ 1) :
    ((ζ + 1) / (2 * (ζ - 1))).re = 0 := by
  have hsub : ζ - 1 ≠ 0 := sub_ne_zero.mpr hne
  have h2ne : (2 : ℂ) * (ζ - 1) ≠ 0 := mul_ne_zero two_ne_zero hsub
  -- (ζ+1)/(2(ζ-1)) = 1/2 + 1/(ζ-1)
  have h_eq : (ζ + 1) / (2 * (ζ - 1)) = 1/2 + 1 / (ζ - 1) := by
    rw [div_add_div _ _ (two_ne_zero' ℂ) hsub]
    congr 1
    ring
  rw [h_eq, Complex.add_re, re_inv_sub_one_of_norm_one ζ habs hne]
  simp
  norm_num

/-- Re(σ(ζ)/ρ(ζ)) ≥ 0 on the unit circle for A-stable methods (for any ζ with ‖ζ‖ = 1).
Handles both the σ = 0 case (Re = 0) and the σ ≠ 0 case (from E_nonneg_re). -/
theorem IsAStable.E_nonneg_re_unit_circle (m : LMM s) (ha : m.IsAStable)
    (ζ : ℂ) (habs : ‖ζ‖ = 1) (hρ : m.rhoC ζ ≠ 0) :
    0 ≤ (m.sigmaC ζ / m.rhoC ζ).re := by
  by_cases hσ : m.sigmaC ζ = 0
  · rw [hσ, zero_div, Complex.zero_re]
  · obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff ζ).mp habs
    rw [← hθ] at hρ hσ ⊢
    exact IsAStable.E_nonneg_re m ha θ hρ hσ

/-- Core analytical lemma for the Dahlquist barrier: if the cross-energy
Re(σ(e^{iθ})·conj(ρ(e^{iθ}))) ≥ 0 for all θ (from A-stability), the E-function
has specific structure from the order conditions, the order is ≥ 3, and ρ has a
simple root at ζ = 1 (zero-stability), we get False.

The proof uses the minimum principle for harmonic functions: the modified E-function
G(ζ) = σ(ζ)/ρ(ζ) - 1/(ζ-1) - 1/2 satisfies Re(G) ≥ 0 on the unit circle
(since Re(1/(e^{iθ}-1)+1/2) = 0) and G(1) = 0 (from order ≥ 3 + simple root).
G'(1) = -1/12. Via conformal map w = 1/ζ, G̃(w) = G(1/w) is analytic in
{|w| < 1} with Re(G̃) ≥ 0 on the boundary. The minimum principle gives
Re(G̃) ≥ 0 inside, but G̃(1-ε) ≈ -ε/12 < 0 for small ε > 0 — contradiction.

NOTE: Without zero-stability (ρ'(1) ≠ 0), this theorem is FALSE.
See `dahlquistCounterexample` below for a method with order 3 that is A-stable
but not zero-stable (ρ = (ζ-1)², a double root). -/
theorem order_ge_three_not_aStable_core (m : LMM s) (p : ℕ) (hp : m.HasOrder p)
    (hp3 : 3 ≤ p) (ha : m.IsAStable)
    -- Zero-stability gives a simple root at ζ = 1:
    (hρ_simple : m.rhoCDeriv 1 ≠ 0)
    -- The established facts:
    (hE_nonneg : ∀ θ : ℝ, ∀ hρ : m.rhoC (Complex.exp (↑θ * Complex.I)) ≠ 0,
      ∀ hσ : m.sigmaC (Complex.exp (↑θ * Complex.I)) ≠ 0,
      0 ≤ (m.sigmaC (Complex.exp (↑θ * Complex.I)) /
           m.rhoC (Complex.exp (↑θ * Complex.I))).re)
    (hRe_inv : ∀ θ : ℝ, ∀ hne : Complex.exp (↑θ * Complex.I) ≠ 1,
      (1 / (Complex.exp (↑θ * Complex.I) - 1)).re = -1/2) :
    False := by
  /- Proof structure (via minimum principle, now proved as `re_nonneg_of_frontier_re_nonneg`):

  1. ALGEBRAIC SETUP:
     - Consistency (order ≥ 1) gives ρ(1) = 0, σ(1) = ρ'(1).
     - Zero-stability gives ρ'(1) ≠ 0, hence σ(1) ≠ 0.
     - Define G(ζ) = σ(ζ)/ρ(ζ) - (ζ+1)/(2(ζ-1)) = N(ζ)/(2ρ(ζ)(ζ-1))
       where N = 2σ(ζ-1) - ρ(ζ+1) is `modifiedNumeratorC`.
     - Order ≥ 3 gives N(1) = N'(1) = N''(1) = 0, so N = (ζ-1)³·Q(ζ).
       With ρ = (ζ-1)·R(ζ) (simple root), G = (ζ-1)Q(ζ)/(2R(ζ)).
     - G(1) = 0, G'(1) = Q(1)/(2R(1)) = -σ(1)/(12ρ'(1)) = -1/12.

  2. BOUNDARY NON-NEGATIVITY:
     Re(G(e^{iθ})) = Re(σ/ρ) - Re(1/(ζ-1) + 1/2) = Re(σ/ρ) ≥ 0
     (from hE_nonneg and hRe_inv).

  3. CONFORMAL MAP & MINIMUM PRINCIPLE:
     Via w = 1/ζ, G̃(w) = G(1/w) is DiffContOnCl on ball(0,1) with
     Re(G̃) ≥ 0 on sphere(0,1). By `re_nonneg_of_frontier_re_nonneg`,
     Re(G̃) ≥ 0 on closedBall(0,1).

  4. CONTRADICTION:
     G̃(1) = 0, G̃'(1) = 1/12. So G̃(1-ε) ≈ -ε/12 < 0 for small ε > 0,
     but 1-ε ∈ ball(0,1), contradicting Re(G̃) ≥ 0.

  The remaining sorry captures step 1 (polynomial algebra on the E-function),
  step 2 (connecting hE_nonneg/hRe_inv to G̃ on the boundary), step 3 (showing
  G̃ is DiffContOnCl), and step 4 (the derivative/continuity argument for G̃). -/
  -- Once Gtilde : ℂ → ℂ is constructed with:
  --   (a) DiffContOnCl ℂ Gtilde (Metric.ball 0 1)
  --   (b) ∀ z ∈ Metric.sphere 0 1, 0 ≤ (Gtilde z).re
  --   (c) ∃ w₀ ∈ Metric.ball 0 1, (Gtilde w₀).re < 0
  -- the minimum principle (re_nonneg_of_frontier_re_nonneg) gives the contradiction.
  suffices h : ∃ (Gtilde : ℂ → ℂ), DiffContOnCl ℂ Gtilde (Metric.ball 0 1) ∧
      (∀ z ∈ Metric.sphere (0 : ℂ) 1, 0 ≤ (Gtilde z).re) ∧
      (∃ w₀ ∈ Metric.ball (0 : ℂ) 1, (Gtilde w₀).re < 0) by
    obtain ⟨Gt, hGt_dcl, hGt_bd, w₀, hw₀, hGt_neg⟩ := h
    have hGt_min := re_nonneg_of_frontier_re_nonneg Metric.isBounded_ball Gt hGt_dcl
      (by rwa [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)])
    have hw₀_cl : w₀ ∈ closure (Metric.ball (0 : ℂ) 1) := by
      rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
      exact Metric.ball_subset_closedBall hw₀
    exact absurd (hGt_min w₀ hw₀_cl) (not_le.mpr hGt_neg)
  -- Step A: Extract consistency facts from order hypotheses.
  have hcons := hp.isConsistent (by omega : 1 ≤ p)
  have hρ1 : m.rhoC 1 = 0 := hcons.rhoC_one m
  have hσ1_eq : m.sigmaC 1 = m.rhoCDeriv 1 := hcons.sigmaC_one_eq_rhoCDeriv_one
  have hσ1_ne : m.sigmaC 1 ≠ 0 := by rw [hσ1_eq]; exact hρ_simple
  -- Step B: Define the reversed polynomials.
  -- ρ̃(w) = w^s · ρ(1/w) is a polynomial; σ̃(w) = w^s · σ(1/w) is a polynomial.
  -- For |w| < 1: ρ̃(w) ≠ 0 (A-stability puts roots of ρ in |ζ| ≤ 1, so 1/w with |w| < 1
  -- gives |1/w| > 1, outside the root region; at w = 0, ρ̃(0) = α_s = 1).
  -- The function G̃(w) = σ̃(w)/ρ̃(w) - (1+w)/(2(1-w)) is well-defined for w ∈ ball(0,1).
  -- It has a removable singularity at w = 1 (from order ≥ 3 and simple root).
  -- After removal: G̃(1) = 0, G̃'(1) = 1/12.

  -- Step C: Construct Gtilde and prove the three properties via sub-lemmas.
  -- We decompose into three independent claims:
  --   (a) DiffContOnCl (hardest — requires removable singularity argument)
  --   (b) Boundary non-negativity (from hE_nonneg and hRe_inv)
  --   (c) Interior negative point (from derivative computation at w = 1)

  -- For now, we define Gtilde and prove (b) directly, leaving (a) and (c) as sorry.
  -- Define Gtilde piecewise: at w ≠ 0, 1 use the formula; at w = 0 and w = 1 use limits.
  -- The key formula: for w on the unit circle with w ≠ 1,
  --   Re(Gtilde(w)) = Re(σ(1/w)/ρ(1/w)) - Re((1/w+1)/(2(1/w-1)))
  --                  = Re(σ(1/w)/ρ(1/w)) - 0 ≥ 0
  -- because (1/w+1)/(2(1/w-1)) = (1+w)/(2(1-w)) is purely imaginary on |w| = 1.

  -- Sub-lemma: cross-energy gives Re(σ(ζ)·conj(ρ(ζ))) ≥ 0 everywhere on the unit circle
  have hce := cross_energy_nonneg m ha

  -- The construction requires substantial complex analysis infrastructure.
  -- We decompose into two sorry-marked goals:
  --   (1) Construction of Gt with DiffContOnCl, boundary Re ≥ 0, Gt(1) = 0, and HasDerivAt
  --   (2) Interior negative point from HasDerivAt (pure analysis, proved below)
  suffices h_dcl : ∃ (Gt : ℂ → ℂ),
      DiffContOnCl ℂ Gt (Metric.ball 0 1) ∧
      Gt 1 = 0 ∧
      (∀ z ∈ Metric.sphere (0 : ℂ) 1, 0 ≤ (Gt z).re) ∧
      HasDerivAt Gt (1/12 : ℂ) 1 by
    obtain ⟨Gt, hGt_dcl, hGt_one, hGt_bd, hGt_deriv⟩ := h_dcl
    refine ⟨Gt, hGt_dcl, hGt_bd, ?_⟩
    -- (c) Interior negative point: from HasDerivAt at w = 1 with derivative 1/12
    -- Gt(1) = 0 and Gt'(1) = 1/12 (as a complex number). For real t < 1 close to 1:
    -- Gt(t) = Gt(1) + (t-1)·(1/12) + o(t-1) = (t-1)/12 + o(t-1)
    -- Re(Gt(t)) ≈ (t-1)/12 < 0 for t < 1.
    -- We use the ε-δ definition of HasDerivAt with ε = 1/24.
    rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hGt_deriv
    have hε : (0 : ℝ) < 1/24 := by norm_num
    obtain ⟨U, hU_nhds, hU⟩ := (hGt_deriv hε).exists_mem
    rw [Metric.mem_nhds_iff] at hU_nhds
    obtain ⟨δ, hδ_pos, hδ_ball⟩ := hU_nhds
    -- Choose w₀ = 1 - min(δ/2, 1/2) ∈ (0, 1) ∩ ball(1, δ)
    set ε₀ := min (δ / 2) (1/2) with hε₀_def
    have hε₀_pos : 0 < ε₀ := lt_min (by linarith) (by norm_num)
    have hε₀_le : ε₀ ≤ 1/2 := min_le_right _ _
    have hε₀_lt_δ : ε₀ < δ := by linarith [min_le_left (δ/2) (1/2 : ℝ)]
    set w₀ : ℂ := (1 : ℂ) - (ε₀ : ℂ) with hw₀_def
    have hw₀_sub : w₀ - 1 = -(ε₀ : ℂ) := by rw [hw₀_def]; ring
    have h_norm_diff : ‖w₀ - (1 : ℂ)‖ = ε₀ := by
      rw [hw₀_sub]; simp [Complex.norm_real, abs_of_pos hε₀_pos]
    refine ⟨w₀, ?_, ?_⟩
    · -- w₀ ∈ ball(0, 1): |1 - ε₀| < 1 since 0 < ε₀ ≤ 1/2
      rw [Metric.mem_ball, dist_zero_right, hw₀_def]
      rw [show (1 : ℂ) - (ε₀ : ℂ) = ((1 - ε₀ : ℝ) : ℂ) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · -- Re(Gt(w₀)) < 0: from the derivative approximation
      -- w₀ ∈ U (within δ of 1)
      have hw₀_mem : w₀ ∈ U := by
        apply hδ_ball; rw [Metric.mem_ball, dist_eq_norm, h_norm_diff]
        exact hε₀_lt_δ
      -- Apply the little-o estimate
      have h_est := hU w₀ hw₀_mem
      rw [hGt_one, sub_zero, hw₀_sub, smul_eq_mul] at h_est
      -- ‖-ε₀‖ = ε₀
      simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε₀_pos] at h_est
      -- (-ε₀) * (1/12) = ↑(-ε₀/12)
      have h_smul : -(ε₀ : ℂ) * ((1 : ℂ) / 12) = ((- ε₀ / 12 : ℝ) : ℂ) := by push_cast; ring
      rw [h_smul] at h_est
      -- |Re(Gt(w₀)) - (-ε₀/12)| ≤ ‖Gt(w₀) - ↑(-ε₀/12)‖ ≤ ε₀/24
      have h_combined : |(Gt w₀).re - (-ε₀/12)| ≤ ε₀/24 := by
        calc |(Gt w₀).re - (-ε₀/12)|
            = |(Gt w₀ - ((- ε₀ / 12 : ℝ) : ℂ)).re| := by rw [Complex.sub_re, Complex.ofReal_re]
          _ ≤ ‖Gt w₀ - ((- ε₀ / 12 : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
          _ ≤ 1/24 * ε₀ := h_est
          _ = ε₀/24 := by ring
      -- Re(Gt(w₀)) ≤ -ε₀/12 + ε₀/24 = -ε₀/24 < 0
      linarith [abs_le.mp h_combined]
  -- =========================================================================
  -- MAIN CONSTRUCTION: existence of Gt satisfying the four properties.
  --
  -- Strategy: Define Gt(w) = σ̃(w)/ρ̃(w) - (1+w)/(2(1-w)) where σ̃, ρ̃ are reversed
  -- polynomials, with the removable singularity at w = 1 filled in by Gt(1) = 0.
  --
  -- The reversed polynomials are:
  --   ρ̃(w) = Σ α_{s-j} w^j = w^s · ρ(1/w)  (for w ≠ 0)
  --   σ̃(w) = Σ β_{s-j} w^j = w^s · σ(1/w)  (for w ≠ 0)
  --
  -- Key facts:
  --   ρ̃(0) = α_s = 1 ≠ 0, ρ̃(1) = ρ(1) = 0
  --   For |w| < 1: ρ̃(w) ≠ 0 (roots of ρ at |ζ| ≤ 1 map to |1/ζ| ≥ 1)
  --   On |w| = 1: σ̃/ρ̃ = σ(1/w)/ρ(1/w), so Re(σ̃/ρ̃) = Re(E(1/w)) ≥ 0 by A-stability
  --   Re((w+1)/(2(1-w))) = 0 on |w| = 1 (from re_half_plus_inv_sub_one_eq_zero)
  -- Define the reversed polynomials
  let σ_rev : ℂ → ℂ := fun w => ∑ j : Fin (s + 1), (m.β (Fin.rev j) : ℂ) * w ^ (j : ℕ)
  let ρ_rev : ℂ → ℂ := fun w => ∑ j : Fin (s + 1), (m.α (Fin.rev j) : ℂ) * w ^ (j : ℕ)
  -- Key identity: reversed polynomials relate to rhoC/sigmaC via ρ̃(w) = w^s · ρ(1/w)
  have h_rev_identity : ∀ (c : Fin (s + 1) → ℝ) (z : ℂ), z ≠ 0 →
      (∑ j : Fin (s + 1), (c (Fin.rev j) : ℂ) * z ^ (j : ℕ)) =
      z ^ s * ∑ j : Fin (s + 1), (c j : ℂ) * z⁻¹ ^ (j : ℕ) := by
    intro c z hz
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by
      simp only [Fin.revPerm_apply]
      have hj : (j : ℕ) + (Fin.rev j : ℕ) = s := by rw [Fin.val_rev]; omega
      have key : z ^ (j : ℕ) = z ^ s * z⁻¹ ^ (Fin.rev j : ℕ) := by
        have h1 : z ^ (j : ℕ) * z ^ (Fin.rev j : ℕ) = z ^ s := by rw [← pow_add, hj]
        rw [inv_pow, ← h1, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hz), mul_one]
      rw [key, ← mul_assoc, mul_comm _ (z ^ s), mul_assoc])
  have h_rho_rev : ∀ z : ℂ, z ≠ 0 → ρ_rev z = z ^ s * m.rhoC z⁻¹ := by
    intro z hz; exact h_rev_identity m.α z hz
  have h_sigma_rev : ∀ z : ℂ, z ≠ 0 → σ_rev z = z ^ s * m.sigmaC z⁻¹ := by
    intro z hz; exact h_rev_identity m.β z hz
  -- Define Gt: formula at w ≠ 1, removable singularity value 0 at w = 1
  let Gt : ℂ → ℂ := fun w =>
    if w = 1 then 0 else σ_rev w / ρ_rev w - (w + 1) / (2 * (1 - w))
  refine ⟨Gt, ?_, ?_, ?_, ?_⟩
  · -- (a) DiffContOnCl ℂ Gt (Metric.ball 0 1)
    -- Part 1: DifferentiableOn ℂ Gt (Metric.ball 0 1)
    --   For |w| < 1: w ≠ 1 (since |1| = 1), so Gt(w) = σ̃/ρ̃ - (w+1)/(2(1-w)).
    --   ρ̃(w) ≠ 0 for |w| < 1 (roots of ρ̃ correspond to 1/ζ for roots ζ of ρ;
    --   A-stability puts roots of ρ in |ζ| ≤ 1, so roots of ρ̃ have |·| ≥ 1).
    --   1-w ≠ 0 for w ≠ 1. So Gt is a ratio of differentiable functions with
    --   non-zero denominators, hence differentiable.
    --
    -- Part 2: ContinuousOn Gt (closure (Metric.ball 0 1))
    --   At |w| < 1: follows from Part 1.
    --   At |w| = 1, w ≠ 1: need ρ̃(w) ≠ 0, i.e., ρ has no unit-circle roots
    --   other than ζ = 1. This may need zero-stability (or A-stability argument).
    --   NOTE: If ρ has other unit-circle roots, Gt has poles on the boundary
    --   and DiffContOnCl fails. The textbook proof implicitly assumes this.
    --   At w = 1: REMOVABLE SINGULARITY. The combined fraction
    --     G = [2σ̃(1-w) - ρ̃(w+1)] / [2ρ̃(1-w)]
    --   has numerator vanishing to order 3 and denominator to order 2 at w=1
    --   (N(1)=N'(1)=N''(1)=0, D(1)=D'(1)=0, D''(1)=4ρ'(1)≠0).
    --   This uses: C₀: ρ(1)=0, C₁: σ(1)=ρ'(1), C₂: ρ''(1)=2σ'(1)-ρ'(1).
    --   So Gt = -(w-1)Q/(2R) with R(1)=ρ'(1)≠0, giving Gt(1) = 0 and
    --   continuity at w = 1. [Polynomial factoring + Filter.Tendsto]
    sorry
  · -- (b) Gt 1 = 0 (by definition)
    simp only [Gt, if_pos rfl]
  · -- (c) Boundary non-negativity: ∀ z ∈ sphere(0,1), Re(Gt(z)) ≥ 0
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    by_cases h1 : z = 1
    · simp only [Gt, h1, if_pos rfl, Complex.zero_re]; exact le_refl 0
    · simp only [Gt, if_neg h1]
      -- Re(σ̃(z)/ρ̃(z) - (z+1)/(2(1-z))) = Re(σ̃/ρ̃) - Re((z+1)/(2(1-z)))
      -- Re((z+1)/(2(1-z))) = 0 on the unit circle
      -- Re(σ̃/ρ̃) ≥ 0 (from A-stability via reversed polynomial identity)
      have hz_ne : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; norm_num at hz
      -- σ̃/ρ̃ = σ(z⁻¹)/ρ(z⁻¹) (z^s cancels)
      have h_quot : σ_rev z / ρ_rev z = m.sigmaC z⁻¹ / m.rhoC z⁻¹ := by
        rw [h_sigma_rev z hz_ne, h_rho_rev z hz_ne]
        rw [mul_div_mul_left _ _ (pow_ne_zero s hz_ne)]
      rw [h_quot]
      -- Re((z+1)/(2(1-z))) = -Re((z+1)/(2(z-1))) = 0
      have h_re_zero : ((z + 1) / (2 * (1 - z))).re = 0 := by
        rw [show 2 * (1 - z) = -(2 * (z - 1)) from by ring,
            div_neg, Complex.neg_re, neg_eq_zero]
        exact re_half_plus_inv_sub_one_eq_zero z hz h1
      -- Re(σ(z⁻¹)/ρ(z⁻¹)) ≥ 0
      have hz_inv_norm : ‖z⁻¹‖ = 1 := by rw [norm_inv, hz, inv_one]
      have h_re_nonneg : 0 ≤ (m.sigmaC z⁻¹ / m.rhoC z⁻¹).re := by
        by_cases hρz : m.rhoC z⁻¹ = 0
        · rw [hρz, div_zero, Complex.zero_re]
        · exact IsAStable.E_nonneg_re_unit_circle m ha z⁻¹ hz_inv_norm hρz
      linarith [Complex.sub_re (m.sigmaC z⁻¹ / m.rhoC z⁻¹) ((z + 1) / (2 * (1 - z)))]
  · -- (d) HasDerivAt Gt (1/12) 1
    -- Combined fraction: Gt(w) = N̄(w)/D̄(w) where:
    --   N̄(w) = 2σ̃(w)(1-w) - ρ̃(w)(w+1)  (polynomial, degree ≤ s+1)
    --   D̄(w) = 2ρ̃(w)(1-w)               (polynomial, degree ≤ s+1)
    --
    -- At w = 1: N̄ has triple zero, D̄ has double zero (using order ≥ 2):
    --   N̄(1) = 0 (ρ̃(1) = ρ(1) = 0)
    --   N̄'(1) = 0 (uses σ(1) = ρ'(1))
    --   N̄''(1) = 0 (uses ρ''(1) = 2σ'(1) - ρ'(1) from C₂)
    --   N̄'''(1) = -ρ'(1) (uses C₃: ρ'''(1) = 3σ''(1) - 3σ'(1) + 2ρ'(1))
    --   D̄''(1) = 4ρ'(1) ≠ 0
    --
    -- Factor: N̄(w) = (w-1)³ Q̄(w), D̄(w) = (w-1)² · (-2R̃(w)) where ρ̃(w) = (w-1)R̃(w).
    -- Then Gt(w) = -(w-1)Q̄(w)/(2R̃(w)) for w ≠ 1.
    -- Q̄(1) = N̄'''(1)/6 = -ρ'(1)/6, R̃(1) = -ρ'(1).
    -- So Gt'(1) = -Q̄(1)/(2R̃(1)) = ρ'(1)/(6 · 2 · (-ρ'(1))) · (-1)
    --           = 1/12.
    --
    -- Equivalently: G(ζ) = N(ζ)/D(ζ) in the original variable gives
    --   G'(1) = -1/12. Via Gt(w) = G(1/w): Gt'(1) = -G'(1)·(-1) = -(-1/12) · (-1) = 1/12.
    --   Wait: Gt'(w) = G'(1/w)·(-1/w²), so Gt'(1) = G'(1)·(-1) = (-1/12)·(-1) = 1/12. ✓
    sorry

/-- For a zero-stable, A-stable LMM of order ≥ 3, derive False.
Combines `E_nonneg_re`, `re_inv_exp_sub_one`, and the zero-stability condition
(simple root of ρ at ζ = 1) to invoke `order_ge_three_not_aStable_core`.
Reference: Iserles, proof of Theorem 3.4. -/
theorem order_ge_three_not_aStable (m : LMM s) (p : ℕ) (hp : m.HasOrder p) (hp3 : 3 ≤ p)
    (ha : m.IsAStable) (hzs : m.IsZeroStable) : False := by
  have hρ1 : m.rhoC 1 = 0 := (hp.isConsistent (by omega)).rhoC_one m
  exact order_ge_three_not_aStable_core m p hp hp3 ha
    (hzs.unit_roots_simple 1 hρ1 (by simp))
    (fun θ hρ hσ => IsAStable.E_nonneg_re m ha θ hρ hσ)
    (fun θ hne => re_inv_exp_sub_one θ hne)

/-- **Dahlquist's Second Barrier** (Iserles, Theorem 3.4):
An A-stable, zero-stable linear multistep method has order at most 2.

NOTE: Zero-stability is necessary. See `dahlquistCounterexample` for a method
that is A-stable with order 3 but not zero-stable (ρ has a double root at ζ = 1).
The standard textbook statement "A-stable ⟹ order ≤ 2" implicitly assumes
zero-stability (which is needed for convergence anyway). -/
theorem dahlquist_second_barrier {s : ℕ} (m : LMM s) (p : ℕ)
    (hp : m.HasOrder p) (ha : m.IsAStable) (hzs : m.IsZeroStable) : p ≤ 2 := by
  by_contra h
  push_neg at h
  exact order_ge_three_not_aStable m p hp h ha hzs

/-! ## Counterexample: A-stable order-3 method without zero-stability

The method ρ(ζ) = (ζ-1)², σ(ζ) = (ζ²-1)/2 has σ/ρ = (ζ+1)/(2(ζ-1)) (same
as the trapezoidal rule), but because ρ has a double root at ζ = 1, the order
conditions V₀ = V₁ = V₂ = V₃ = 0 are all satisfied. It is A-stable because
the stability polynomial factors as (ξ-1)[(ξ-1) - z(ξ+1)/2], giving roots
ξ = 1 and ξ = (2+z)/(2-z), both in the closed unit disk for Re(z) ≤ 0.
However, the double root violates zero-stability (ρ'(1) = 0), and the
method diverges for the trivial equation y' = 0 (parasitic solution y_n = c·n).

This demonstrates that the Dahlquist barrier requires zero-stability. -/

/-- Counterexample: a 2-step method with ρ(ζ) = (ζ-1)² and σ(ζ) = (ζ²-1)/2.
Has order 3, is A-stable, but is NOT zero-stable. -/
noncomputable def dahlquistCounterexample : LMM 2 where
  α := ![1, -2, 1]
  β := ![-1/2, 0, 1/2]
  normalized := by simp [Fin.last]

/-- The counterexample has order 3: V₀ = V₁ = V₂ = V₃ = 0 and V₄ = -2 ≠ 0. -/
theorem dahlquistCounterexample_order_three : dahlquistCounterexample.HasOrder 3 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [orderCondVal, dahlquistCounterexample, Fin.sum_univ_three] <;> norm_num
  · simp [orderCondVal, dahlquistCounterexample, Fin.sum_univ_three]; norm_num

/-- The counterexample is A-stable: the stability polynomial factors as
(ξ-1)[(ξ-1) - z(ξ+1)/2], with roots ξ = 1 and ξ = (2+z)/(2-z).
For Re(z) ≤ 0: |1| ≤ 1 and |2+z| ≤ |2-z|, so both roots are in the closed unit disk. -/
theorem dahlquistCounterexample_aStable : dahlquistCounterexample.IsAStable := by
  intro z hz ξ hξ
  simp only [stabilityPoly, rhoC, sigmaC, dahlquistCounterexample] at hξ
  simp [Fin.sum_univ_three] at hξ
  have factor : (ξ - 1) * ((ξ - 1) - z * (ξ + 1) / 2) = 0 := by
    linear_combination hξ
  rcases mul_eq_zero.mp factor with h1 | h2
  · have : ξ = 1 := by linear_combination h1
    rw [this]; simp
  · have key : ξ * (2 - z) = 2 + z := by linear_combination 2 * h2
    have h_denom_ne : (2 : ℂ) - z ≠ 0 := by
      intro h; have : ((2 : ℂ) - z).re = 0 := by rw [h]; simp
      simp at this; linarith
    have h_denom_pos : (0 : ℝ) < ‖(2 : ℂ) - z‖ := norm_pos_iff.mpr h_denom_ne
    have hnorm : ‖ξ‖ * ‖(2 : ℂ) - z‖ = ‖(2 : ℂ) + z‖ := by
      rw [← norm_mul, key]
    have h_nsq_le : ‖(2 : ℂ) + z‖ ^ 2 ≤ ‖(2 : ℂ) - z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re,
                 Complex.add_im, Complex.sub_im]
      norm_num; nlinarith
    have h_num_le : ‖(2 : ℂ) + z‖ ≤ ‖(2 : ℂ) - z‖ := by
      nlinarith [norm_nonneg ((2 : ℂ) + z), norm_nonneg ((2 : ℂ) - z),
                 sq_nonneg (‖(2 : ℂ) - z‖ - ‖(2 : ℂ) + z‖)]
    nlinarith [norm_nonneg ξ]

/-- The counterexample is NOT zero-stable: ρ'(1) = 0 (ζ = 1 is a double root). -/
theorem dahlquistCounterexample_not_zeroStable :
    ¬dahlquistCounterexample.IsZeroStable := by
  intro ⟨_, h_simple⟩
  have hρ1 : dahlquistCounterexample.rhoC 1 = 0 := by
    simp [rhoC, dahlquistCounterexample, Fin.sum_univ_three]; norm_num
  have h := h_simple 1 hρ1 (by simp)
  simp [rhoCDeriv, dahlquistCounterexample, Fin.sum_univ_three] at h

end LMM
