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
