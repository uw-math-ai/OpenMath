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

/-- **Adams–Bashforth 3-step** method:
y_{n+3} = y_{n+2} + h·(23/12·f_{n+2} - 16/12·f_{n+1} + 5/12·f_n).
Coefficients: α = [0, 0, -1, 1], β = [5/12, -16/12, 23/12, 0].
This is an explicit method of order 3.
Reference: Iserles, Section 1.3. -/
noncomputable def adamsBashforth3 : LMM 3 where
  α := ![0, 0, -1, 1]
  β := ![5/12, -16/12, 23/12, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 3-step** method:
y_{n+3} = y_{n+2} + h·(9/24·f_{n+3} + 19/24·f_{n+2}
  - 5/24·f_{n+1} + 1/24·f_n).
Coefficients: α = [0, 0, -1, 1], β = [1/24, -5/24, 19/24, 9/24].
This is an implicit method of order 4.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsMoulton3 : LMM 3 where
  α := ![0, 0, -1, 1]
  β := ![1/24, -5/24, 19/24, 9/24]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 4-step** method:
y_{n+4} = y_{n+3} + h·(55/24·f_{n+3} - 59/24·f_{n+2}
  + 37/24·f_{n+1} - 9/24·f_n).
Coefficients: α = [0, 0, 0, -1, 1], β = [-9/24, 37/24, -59/24, 55/24, 0].
This is an explicit method of order 4.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsBashforth4 : LMM 4 where
  α := ![0, 0, 0, -1, 1]
  β := ![-9/24, 37/24, -59/24, 55/24, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 4-step** method:
y_{n+4} = y_{n+3} + h·(251/720·f_{n+4} + 646/720·f_{n+3}
  - 264/720·f_{n+2} + 106/720·f_{n+1} - 19/720·f_n).
Coefficients: α = [0, 0, 0, -1, 1], β = [-19/720, 106/720, -264/720, 646/720, 251/720].
This is an implicit method of order 5.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsMoulton4 : LMM 4 where
  α := ![0, 0, 0, -1, 1]
  β := ![-19/720, 106/720, -264/720, 646/720, 251/720]
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

/-- Adams–Bashforth 3-step is consistent. -/
theorem adamsBashforth3_consistent : adamsBashforth3.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth3, Fin.sum_univ_four],
   by simp [LMM.sigma, adamsBashforth3, Fin.sum_univ_four]; norm_num⟩

/-- Adams–Bashforth 3-step is explicit (β₃ = 0). -/
theorem adamsBashforth3_explicit : adamsBashforth3.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth3, Fin.last]

/-- Adams–Moulton 3-step is consistent. -/
theorem adamsMoulton3_consistent : adamsMoulton3.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton3, Fin.sum_univ_four],
   by simp [LMM.sigma, adamsMoulton3, Fin.sum_univ_four]; norm_num⟩

/-- Adams–Moulton 3-step is implicit (β₃ = 9/24 ≠ 0). -/
theorem adamsMoulton3_implicit : adamsMoulton3.IsImplicit := by
  simp [LMM.IsImplicit, adamsMoulton3, Fin.last]

/-- Adams–Bashforth 4-step is consistent. -/
theorem adamsBashforth4_consistent : adamsBashforth4.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth4, Fin.sum_univ_five],
   by simp [LMM.sigma, adamsBashforth4, Fin.sum_univ_five]; norm_num⟩

/-- Adams–Bashforth 4-step is explicit (β₄ = 0). -/
theorem adamsBashforth4_explicit : adamsBashforth4.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth4, Fin.last]

/-- Adams–Moulton 4-step is consistent. -/
theorem adamsMoulton4_consistent : adamsMoulton4.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton4, Fin.sum_univ_five],
   by simp [LMM.sigma, adamsMoulton4, Fin.sum_univ_five]; norm_num⟩

/-- Adams–Moulton 4-step is implicit (β₄ = 251/720 ≠ 0). -/
theorem adamsMoulton4_implicit : adamsMoulton4.β 4 ≠ 0 := by
  change (251 / 720 : ℝ) ≠ 0
  norm_num

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

/-- Adams–Bashforth 3-step has order 3. -/
theorem adamsBashforth3_order_three : adamsBashforth3.HasOrder 3 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth3, Fin.sum_univ_four] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth3, Fin.sum_univ_four]; norm_num

/-- Adams–Moulton 3-step has order 4. -/
theorem adamsMoulton3_order_four : adamsMoulton3.HasOrder 4 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton3, Fin.sum_univ_four] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton3, Fin.sum_univ_four]; norm_num

/-- Adams–Bashforth 4-step has order 4. -/
theorem adamsBashforth4_order_four : adamsBashforth4.HasOrder 4 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth4, Fin.sum_univ_five] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth4, Fin.sum_univ_five]; norm_num

/-- Adams–Moulton 4-step has order 5. -/
theorem adamsMoulton4_order_five : adamsMoulton4.HasOrder 5 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton4, Fin.sum_univ_five] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton4, Fin.sum_univ_five]; norm_num

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

/-- Adams–Bashforth 3-step is zero-stable: ρ(ξ) = ξ³ - ξ² = ξ²(ξ - 1) has a double
root at 0 (interior to the unit disk) and a simple root at 1 (on the unit circle,
with ρ'(1) = 1 ≠ 0). -/
theorem adamsBashforth3_zeroStable : adamsBashforth3.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, adamsBashforth3, Fin.sum_univ_four] at hξ
    have h : ξ ^ 2 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 2) (a := ξ) (by norm_num : (2 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0]; simp
    · have : ξ = 1 := by linear_combination h1
      rw [this]; simp
  unit_roots_simple := by
    intro ξ hξ habs
    simp [LMM.rhoCDeriv, adamsBashforth3, Fin.sum_univ_four]
    simp [LMM.rhoC, adamsBashforth3, Fin.sum_univ_four] at hξ
    have h : ξ ^ 2 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 2) (a := ξ) (by norm_num : (2 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0] at habs; simp at habs
    · have h1' : ξ = 1 := by linear_combination h1
      rw [h1']; norm_num

/-- Adams–Moulton 3-step is zero-stable: it has the same first characteristic
polynomial as Adams–Bashforth 3-step. -/
theorem adamsMoulton3_zeroStable : adamsMoulton3.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, adamsMoulton3, Fin.sum_univ_four] at hξ
    have h : ξ ^ 2 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 2) (a := ξ) (by norm_num : (2 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0]; simp
    · have : ξ = 1 := by linear_combination h1
      rw [this]; simp
  unit_roots_simple := by
    intro ξ hξ habs
    simp [LMM.rhoCDeriv, adamsMoulton3, Fin.sum_univ_four]
    simp [LMM.rhoC, adamsMoulton3, Fin.sum_univ_four] at hξ
    have h : ξ ^ 2 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 2) (a := ξ) (by norm_num : (2 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0] at habs; simp at habs
    · have h1' : ξ = 1 := by linear_combination h1
      rw [h1']; norm_num

/-- Adams–Bashforth 4-step is zero-stable: ρ(ξ) = ξ⁴ - ξ³ = ξ³(ξ - 1) has a triple
root at 0 (interior to the unit disk) and a simple root at 1 (on the unit circle,
with ρ'(1) = 1 ≠ 0). -/
theorem adamsBashforth4_zeroStable : adamsBashforth4.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, adamsBashforth4, Fin.sum_univ_five] at hξ
    have h : ξ ^ 3 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 3) (a := ξ) (by norm_num : (3 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0]; simp
    · have : ξ = 1 := by linear_combination h1
      rw [this]; simp
  unit_roots_simple := by
    intro ξ hξ habs
    simp [LMM.rhoCDeriv, adamsBashforth4, Fin.sum_univ_five]
    simp [LMM.rhoC, adamsBashforth4, Fin.sum_univ_five] at hξ
    have h : ξ ^ 3 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 3) (a := ξ) (by norm_num : (3 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0] at habs; simp at habs
    · have h1' : ξ = 1 := by linear_combination h1
      rw [h1']; norm_num

/-- Adams–Moulton 4-step is zero-stable: ρ(ξ) = ξ⁴ - ξ³ = ξ³(ξ - 1) has a triple
root at 0 (interior to the unit disk) and a simple root at 1 (on the unit circle,
with ρ'(1) = 1 ≠ 0). -/
theorem adamsMoulton4_zeroStable : adamsMoulton4.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, adamsMoulton4, Fin.sum_univ_five] at hξ
    have h : ξ ^ 3 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 3) (a := ξ) (by norm_num : (3 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0]; simp
    · have : ξ = 1 := by linear_combination h1
      rw [this]; simp
  unit_roots_simple := by
    intro ξ hξ habs
    simp [LMM.rhoCDeriv, adamsMoulton4, Fin.sum_univ_five]
    simp [LMM.rhoC, adamsMoulton4, Fin.sum_univ_five] at hξ
    have h : ξ ^ 3 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 3) (a := ξ) (by norm_num : (3 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0] at habs; simp at habs
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

/-! ## BDF3 (Backward Differentiation Formula, 3-step)

The BDF3 method: y_{n+3} - (18/11)y_{n+2} + (9/11)y_{n+1} - (2/11)y_n = (6/11)h·f_{n+3}.
It is implicit, has order 3, and is zero-stable.
Roots of ρ: ξ = 1 (simple) and roots of 11ξ² - 7ξ + 2 = 0 with |ξ|² = 2/11 < 1.

Reference: Iserles, Section 4.5.
-/

/-- **BDF3** (Backward Differentiation Formula, 3-step):
  y_{n+3} - (18/11)y_{n+2} + (9/11)y_{n+1} - (2/11)y_n = (6/11)h·f_{n+3}.
  Coefficients: α = [-2/11, 9/11, -18/11, 1], β = [0, 0, 0, 6/11]. -/
noncomputable def bdf3 : LMM 3 where
  α := ![-2/11, 9/11, -18/11, 1]
  β := ![0, 0, 0, 6/11]
  normalized := by simp [Fin.last]

/-- BDF3 is consistent. -/
theorem bdf3_consistent : bdf3.IsConsistent :=
  ⟨by simp [LMM.rho, bdf3, Fin.sum_univ_four]; norm_num,
   by simp [LMM.sigma, bdf3, Fin.sum_univ_four]; norm_num⟩

/-- BDF3 has order 3. -/
theorem bdf3_order_three : bdf3.HasOrder 3 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, bdf3, Fin.sum_univ_four] <;> norm_num
  · simp [LMM.orderCondVal, bdf3, Fin.sum_univ_four]; norm_num

/-- BDF3 is implicit (β₃ = 6/11 ≠ 0). -/
theorem bdf3_implicit : bdf3.IsImplicit := by
  simp [LMM.IsImplicit, bdf3, Fin.last]

/-- BDF3 is zero-stable: ρ(ξ) = ξ³ - (18/11)ξ² + (9/11)ξ - 2/11.
  Factoring: 11·ρ(ξ) = (ξ-1)(11ξ² - 7ξ + 2).
  Root ξ = 1 is simple (ρ'(1) = 6/11 ≠ 0).
  Roots of 11ξ² - 7ξ + 2 = 0 satisfy |ξ|² = 2/11 < 1
  (triangle inequality: 11‖ξ‖² = ‖7ξ-2‖ ≤ 7‖ξ‖+2, but 11t²-7t-2 > 0 for t ≥ 1). -/
theorem bdf3_zeroStable : bdf3.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp only [LMM.rhoC, bdf3] at hξ
    simp [Fin.sum_univ_four] at hξ
    -- 11·ρ(ξ) = (ξ-1)(11ξ²-7ξ+2) = 0
    have h11 : (ξ - 1) * (11 * ξ ^ 2 - 7 * ξ + 2) = 0 := by linear_combination 11 * hξ
    rcases mul_eq_zero.mp h11 with h0 | h1
    · -- ξ = 1
      have : ξ = 1 := by linear_combination h0
      rw [this]; simp
    · -- 11ξ²-7ξ+2 = 0 ⟹ ‖ξ‖ < 1
      -- From h1: 11*ξ² = 7*ξ - 2
      have h_eq : (11 : ℂ) * ξ ^ 2 = 7 * ξ - 2 := by linear_combination h1
      -- 11*‖ξ‖² = ‖11*ξ²‖ = ‖7*ξ - 2‖ ≤ 7*‖ξ‖ + 2 by triangle inequality
      have h_norm_eq : 11 * ‖ξ‖ ^ 2 = ‖7 * ξ - 2‖ := by
        have := congr_arg norm h_eq
        rwa [norm_mul, norm_pow, show ‖(11 : ℂ)‖ = 11 from by norm_num] at this
      have h_tri : ‖(7 : ℂ) * ξ - 2‖ ≤ 7 * ‖ξ‖ + 2 :=
        calc ‖(7 : ℂ) * ξ - 2‖ ≤ ‖(7 : ℂ) * ξ‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
          _ = 7 * ‖ξ‖ + 2 := by
              rw [norm_mul]; norm_num
      -- So 11*‖ξ‖² ≤ 7*‖ξ‖ + 2
      have h_ineq : 11 * ‖ξ‖ ^ 2 ≤ 7 * ‖ξ‖ + 2 := by linarith
      -- For t = ‖ξ‖ ≥ 0, 11t²-7t-2 ≤ 0 implies t < 1 (since 11-7-2=2>0)
      by_contra h_gt
      push_neg at h_gt
      nlinarith [norm_nonneg ξ]
  unit_roots_simple := by
    intro ξ hξ habs
    simp only [LMM.rhoCDeriv, bdf3]
    simp only [LMM.rhoC, bdf3] at hξ
    simp [Fin.sum_univ_four] at hξ
    have h11 : (ξ - 1) * (11 * ξ ^ 2 - 7 * ξ + 2) = 0 := by linear_combination 11 * hξ
    rcases mul_eq_zero.mp h11 with h0 | h1
    · -- ξ = 1, show ρ'(1) = 6/11 ≠ 0
      have hξ1 : ξ = 1 := by linear_combination h0
      rw [hξ1]
      simp [Fin.sum_univ_four]; norm_num
    · -- other roots have |ξ|² = 2/11 < 1, contradicts |ξ| = 1
      exfalso
      have h_eq : (11 : ℂ) * ξ ^ 2 = 7 * ξ - 2 := by linear_combination h1
      have h_norm_eq : 11 * ‖ξ‖ ^ 2 = ‖7 * ξ - 2‖ := by
        have := congr_arg norm h_eq
        rwa [norm_mul, norm_pow, show ‖(11 : ℂ)‖ = 11 from by norm_num] at this
      rw [habs] at h_norm_eq
      simp at h_norm_eq
      -- 11 = ‖7*ξ - 2‖, but ‖7*ξ - 2‖ ≤ 9
      have h_tri : ‖(7 : ℂ) * ξ - 2‖ ≤ 7 * ‖ξ‖ + 2 :=
        calc ‖(7 : ℂ) * ξ - 2‖ ≤ ‖(7 : ℂ) * ξ‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
          _ = 7 * ‖ξ‖ + 2 := by rw [norm_mul]; norm_num
      rw [habs] at h_tri
      linarith

/-! ## BDF4 (Backward Differentiation Formula, 4-step)

The BDF4 method: y_{n+4} - (48/25)y_{n+3} + (36/25)y_{n+2} - (16/25)y_{n+1} + (3/25)y_n
  = (12/25)h·f_{n+4}.
It is implicit, has order 4, and is zero-stable.

Reference: Iserles, Section 4.5.
-/

/-- **BDF4** (Backward Differentiation Formula, 4-step):
  y_{n+4} - (48/25)y_{n+3} + (36/25)y_{n+2} - (16/25)y_{n+1} + (3/25)y_n = (12/25)h·f_{n+4}.
  Coefficients: α = [3/25, -16/25, 36/25, -48/25, 1], β = [0, 0, 0, 0, 12/25]. -/
noncomputable def bdf4 : LMM 4 where
  α := ![3/25, -16/25, 36/25, -48/25, 1]
  β := ![0, 0, 0, 0, 12/25]
  normalized := by simp [Fin.last]

/-- BDF4 is consistent. -/
theorem bdf4_consistent : bdf4.IsConsistent :=
  ⟨by simp [LMM.rho, bdf4, Fin.sum_univ_five]; norm_num,
   by simp [LMM.sigma, bdf4, Fin.sum_univ_five]; norm_num⟩

/-- BDF4 has order 4. -/
theorem bdf4_order_four : bdf4.HasOrder 4 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, bdf4, Fin.sum_univ_five] <;> norm_num
  · simp [LMM.orderCondVal, bdf4, Fin.sum_univ_five]; norm_num

/-- BDF4 is implicit (β₄ = 12/25 ≠ 0). -/
theorem bdf4_implicit : bdf4.IsImplicit := by
  simp [LMM.IsImplicit, bdf4, Fin.last]

/-- BDF4 is zero-stable: ρ(ξ) = ξ⁴ - (48/25)ξ³ + (36/25)ξ² - (16/25)ξ + 3/25.
  Factoring: 25·ρ(ξ) = (ξ-1)(25ξ³ - 23ξ² + 13ξ - 3).
  Root ξ = 1 is simple (ρ'(1) = 12/25 ≠ 0).
  The cubic 25ξ³ - 23ξ² + 13ξ - 3 has all roots strictly inside the unit disk:
  - Real roots: p is strictly increasing (p' has Δ < 0), p(0) < 0, p(1) > 0 → real root ∈ (0,1).
  - Complex roots: conjugate pair with |ξ|² = 3/(25r) < 1 since r > 3/25.
  - No roots on unit circle: eliminating between p(ξ)=0 and p(1/ξ̄)=0 yields
    32z²-67z+77=0 whose roots have |z|² = 77/32 ≠ 1, contradiction. -/
theorem bdf4_zeroStable : bdf4.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp only [LMM.rhoC, bdf4] at hξ
    simp [Fin.sum_univ_five] at hξ
    have h25 : (ξ - 1) * (25 * ξ ^ 3 - 23 * ξ ^ 2 + 13 * ξ - 3) = 0 := by
      linear_combination 25 * hξ
    rcases mul_eq_zero.mp h25 with h0 | h1
    · have : ξ = 1 := by linear_combination h0
      rw [this]; simp
    · -- Cubic 25ξ³-23ξ²+13ξ-3=0: all roots are inside unit disk.
      -- Proof: decompose ξ = ⟨a,b⟩, extract real/imaginary parts, show a²+b² ≤ 1.
      -- Real case (b=0): p is strictly increasing, p(-1)<0<p(1), so root ∈ (-1,1).
      -- Complex case (b≠0): from Im=0 get b²=(75a²-46a+13)/25, then cubic in a.
      -- Polynomial division shows 100a²-46a-12 < 0 when a < 2/5 (from cubic bound).
      set a := ξ.re; set b := ξ.im
      have hξ_eq : ξ = ⟨a, b⟩ := (Complex.eta ξ).symm
      rw [hξ_eq] at h1
      suffices h_sq : a ^ 2 + b ^ 2 ≤ 1 by
        rw [hξ_eq, Complex.norm_def, Complex.normSq_mk,
            show a * a + b * b = a ^ 2 + b ^ 2 from by ring]
        exact Real.sqrt_le_one.mpr h_sq
      have hp2 : (⟨a, b⟩ : ℂ) ^ 2 = ⟨a * a - b * b, a * b + b * a⟩ := by rw [sq]; rfl
      have hp3 : (⟨a, b⟩ : ℂ) ^ 3 = ⟨(a * a - b * b) * a - (a * b + b * a) * b,
          (a * a - b * b) * b + (a * b + b * a) * a⟩ := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hp2]; rfl
      obtain ⟨h_re, h_im⟩ := Complex.ext_iff.mp h1
      simp only [Complex.zero_re, Complex.zero_im] at h_re h_im
      rw [hp2, hp3] at h_re h_im; simp at h_re h_im
      rcases eq_or_ne b 0 with hb0 | hb_ne
      · -- Real case: b = 0
        rw [hb0]; simp
        rw [hb0] at h_re; simp at h_re
        rw [abs_le]; constructor
        · by_contra h; push_neg at h; nlinarith [sq_nonneg (a + 1), sq_nonneg a]
        · by_contra h; push_neg at h; nlinarith [sq_nonneg (a - 1), sq_nonneg a]
      · -- Complex case: b ≠ 0
        have h_quad_b : 75 * a ^ 2 - 25 * b ^ 2 - 46 * a + 13 = 0 := by
          have : b * (75 * a ^ 2 - 25 * b ^ 2 - 46 * a + 13) = 0 := by nlinarith
          exact (mul_eq_zero.mp this).resolve_left hb_ne
        have hb_sq : b ^ 2 = (75 * a ^ 2 - 46 * a + 13) / 25 := by linarith
        have h_cubic_a : 1250 * a ^ 3 - 1150 * a ^ 2 + 427 * a - 56 = 0 := by
          nlinarith [sq_nonneg a, sq_nonneg b]
        have ha_lt : a < 2 / 5 := by
          by_contra h; push_neg at h
          nlinarith [sq_nonneg a, sq_nonneg (a - 2 / 5)]
        have h_target : 100 * a ^ 2 - 46 * a - 12 < 0 := by
          have h_div : (100 * a ^ 2 - 46 * a - 12) * (50 * a - 23) = 500 - 1250 * a := by
            nlinarith
          by_contra h_ge; push_neg at h_ge; nlinarith
        rw [hb_sq]; linarith
  unit_roots_simple := by
    intro ξ hξ habs
    simp only [LMM.rhoCDeriv, bdf4]
    simp only [LMM.rhoC, bdf4] at hξ
    simp [Fin.sum_univ_five] at hξ
    have h25 : (ξ - 1) * (25 * ξ ^ 3 - 23 * ξ ^ 2 + 13 * ξ - 3) = 0 := by
      linear_combination 25 * hξ
    rcases mul_eq_zero.mp h25 with h0 | h1
    · have hξ1 : ξ = 1 := by linear_combination h0
      rw [hξ1]
      simp [Fin.sum_univ_five]; norm_num
    · -- Cubic has no roots on the unit circle: conjugate elimination proof.
      -- From p(ξ)=0 and |ξ|=1, derive reversed equation, combine to get ξ²=1,
      -- then check ξ=±1 both give p(ξ)≠0.
      exfalso
      have hξ_ne : ξ ≠ 0 := by intro h; rw [h] at habs; simp at habs
      have h_nsq : Complex.normSq ξ = 1 := by
        rw [Complex.normSq_eq_norm_sq, habs]; norm_num
      have h_mc : ξ * starRingEnd ℂ ξ = 1 := by
        rw [Complex.mul_conj, ← Complex.ofReal_one, Complex.ofReal_inj]; exact h_nsq
      have h_conj_eq : starRingEnd ℂ ξ = ξ⁻¹ := eq_inv_of_mul_eq_one_right h_mc
      -- Conjugate h1 and substitute conj ξ = ξ⁻¹
      have h1_conj : 25 * ξ⁻¹ ^ 3 - 23 * ξ⁻¹ ^ 2 + 13 * ξ⁻¹ - 3 = 0 := by
        have := congr_arg (starRingEnd ℂ) h1
        simp only [map_sub, map_mul, map_pow, map_add, map_ofNat, map_zero] at this
        rwa [h_conj_eq] at this
      -- Multiply by ξ³ to get reversed polynomial
      have h_rev : -3 * ξ ^ 3 + 13 * ξ ^ 2 - 23 * ξ + 25 = 0 := by
        have h := congr_arg (starRingEnd ℂ) h1
        simp only [map_sub, map_mul, map_pow, map_add, map_ofNat, map_zero] at h
        rw [h_conj_eq] at h; field_simp at h; linear_combination h
      -- Combine to eliminate ξ³: 32ξ²-67ξ+77=0
      have h_quad : 32 * ξ ^ 2 - 67 * ξ + 77 = 0 := by
        linear_combination 3 / 8 * h1 + 25 / 8 * h_rev
      -- Reverse the quadratic: 77ξ²-67ξ+32=0
      have h_quad_rev : 77 * ξ ^ 2 - 67 * ξ + 32 = 0 := by
        have h := congr_arg (starRingEnd ℂ) h_quad
        simp only [map_sub, map_mul, map_pow, map_add, map_ofNat, map_zero] at h
        rw [h_conj_eq] at h; field_simp at h; linear_combination h
      -- Subtract: ξ²=1
      have h_sq : ξ ^ 2 = 1 := by
        have : -45 * ξ ^ 2 + 45 = 0 := by linear_combination h_quad - h_quad_rev
        linear_combination -this / 45
      -- Substitute ξ²=1 into h1: 38ξ-26=0, ξ=13/19
      have hξ_val : ξ = 13 / 19 := by
        have : 25 * ξ * ξ ^ 2 - 23 * ξ ^ 2 + 13 * ξ - 3 = 0 := by ring_nf; linear_combination h1
        rw [h_sq] at this; linear_combination this / 38
      -- But (13/19)²≠1
      rw [hξ_val] at h_sq; norm_num at h_sq

/-! ## BDF5 (Backward Differentiation Formula, 5-step)

The BDF5 method:
  y_{n+5} - (300/137)y_{n+4} + (300/137)y_{n+3} - (200/137)y_{n+2}
  + (75/137)y_{n+1} - (12/137)y_n = (60/137)h·f_{n+5}.

It is implicit, has order 5, and is zero-stable (the last stable BDF method
that is also A(α)-stable with α ≈ 51.8°).

Reference: Iserles, Section 4.5; Hairer–Wanner, Section V.1.
-/

/-- **BDF5** (Backward Differentiation Formula, 5-step):
  y_{n+5} - (300/137)y_{n+4} + ... = (60/137)h·f_{n+5}.
  Coefficients: α = [-12/137, 75/137, -200/137, 300/137, -300/137, 1],
  β = [0, 0, 0, 0, 0, 60/137]. -/
noncomputable def bdf5 : LMM 5 where
  α := ![-12/137, 75/137, -200/137, 300/137, -300/137, 1]
  β := ![0, 0, 0, 0, 0, 60/137]
  normalized := by simp [Fin.last]

/-- BDF5 is consistent. -/
theorem bdf5_consistent : bdf5.IsConsistent :=
  ⟨by simp [LMM.rho, bdf5, Fin.sum_univ_succ]; norm_num,
   by simp [LMM.sigma, bdf5, Fin.sum_univ_succ]; norm_num⟩

/-- BDF5 has order 5. -/
theorem bdf5_order_five : bdf5.HasOrder 5 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, bdf5, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, bdf5, Fin.sum_univ_succ]; norm_num

/-- BDF5 is implicit (β₅ = 60/137 ≠ 0). -/
theorem bdf5_implicit : bdf5.IsImplicit := by
  simp [LMM.IsImplicit, bdf5, Fin.last]

/-- If `ξ` satisfies the BDF5 quartic factor and the auxiliary quadratic factor,
then `ξ = 5 / 4`. -/
private lemma bdf5_quartic_eq_five_fourths (ξ : ℂ)
    (hq : 125 * ξ ^ 2 - 100 * ξ + 125 = 0)
    (h1 : 137 * ξ ^ 4 - 163 * ξ ^ 3 + 137 * ξ ^ 2 - 63 * ξ + 12 = 0) :
    ξ = 5 / 4 := by
  have h4 : 125 * ξ ^ 4 - 100 * ξ ^ 3 + 125 * ξ ^ 2 = 0 := by
    linear_combination ξ ^ 2 * hq
  have h3 : 125 * ξ ^ 3 - 100 * ξ ^ 2 + 125 * ξ = 0 := by
    linear_combination ξ * hq
  have hlin : (136800 : ℂ) * ξ = 171000 := by
    linear_combination (-3125 : ℂ) * h1 + 3425 * h4 + (-1335) * h3 + (-1068) * hq
  have h136800 : (136800 : ℂ) ≠ 0 := by
    norm_num
  exact mul_left_cancel₀ h136800 <| by
    linear_combination hlin

/-- BDF5 is zero-stable: `ρ(ξ) = ξ⁵ - (300/137)ξ⁴ + (300/137)ξ³ - (200/137)ξ²
  + (75/137)ξ - 12/137`.
  Factoring: `137·ρ(ξ) = (ξ - 1) (137ξ⁴ - 163ξ³ + 137ξ² - 63ξ + 12)`.
  Root `ξ = 1` is simple. The quartic factor has all roots strictly inside the unit disk,
  so every root of `ρ` lies in `‖ξ‖ ≤ 1` and every unit root is simple. -/
theorem bdf5_zeroStable : bdf5.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp only [LMM.rhoC, bdf5] at hξ
    simp [Fin.sum_univ_succ] at hξ
    have h137 : (ξ - 1) * (137 * ξ ^ 4 - 163 * ξ ^ 3 + 137 * ξ ^ 2 - 63 * ξ + 12) = 0 := by
      linear_combination 137 * hξ
    rcases mul_eq_zero.mp h137 with h0 | h1
    · have : ξ = 1 := by
        linear_combination h0
      rw [this]
      simp
    ·
      norm_num [Complex.ext_iff, pow_succ] at *
      norm_num [Complex.normSq, Complex.norm_def]
      by_cases h_im : ξ.im = 0
      · norm_num [h_im] at *
        nlinarith [sq_nonneg (ξ.re - 1 / 2), sq_nonneg (ξ.re - 1), sq_nonneg (ξ.re - 3 / 2)]
      · by_contra h_contra
        nlinarith [mul_self_pos.mpr h_im,
          mul_le_mul_of_nonneg_left (le_of_not_ge h_contra) (sq_nonneg ξ.re),
          mul_le_mul_of_nonneg_left (le_of_not_ge h_contra) (sq_nonneg ξ.im),
          mul_le_mul_of_nonneg_left (le_of_not_ge h_contra) (sq_nonneg (ξ.re ^ 2)),
          mul_le_mul_of_nonneg_left (le_of_not_ge h_contra) (sq_nonneg (ξ.im ^ 2))]
  unit_roots_simple := by
    intro ξ hξ habs
    simp only [LMM.rhoCDeriv, bdf5]
    simp only [LMM.rhoC, bdf5] at hξ
    simp [Fin.sum_univ_succ] at hξ
    have h137 : (ξ - 1) * (137 * ξ ^ 4 - 163 * ξ ^ 3 + 137 * ξ ^ 2 - 63 * ξ + 12) = 0 := by
      linear_combination 137 * hξ
    rcases mul_eq_zero.mp h137 with h0 | h1
    · have hξ1 : ξ = 1 := by
        linear_combination h0
      rw [hξ1]
      simp [Fin.sum_univ_succ]
      norm_num
    · -- Quartic has no roots on the unit circle: conjugate elimination proof.
      exfalso
      have hξ_ne : ξ ≠ 0 := by
        intro h
        rw [h] at habs
        simp at habs
      have h_nsq : Complex.normSq ξ = 1 := by
        rw [Complex.normSq_eq_norm_sq, habs]
        norm_num
      have h_mc : ξ * starRingEnd ℂ ξ = 1 := by
        rw [Complex.mul_conj, ← Complex.ofReal_one, Complex.ofReal_inj]
        exact h_nsq
      have h_conj_eq : starRingEnd ℂ ξ = ξ⁻¹ := eq_inv_of_mul_eq_one_right h_mc
      have h_rev : 12 * ξ ^ 4 - 63 * ξ ^ 3 + 137 * ξ ^ 2 - 163 * ξ + 137 = 0 := by
        have h := congr_arg (starRingEnd ℂ) h1
        simp only [map_sub, map_mul, map_pow, map_add, map_ofNat, map_zero] at h
        rw [h_conj_eq] at h
        field_simp at h
        linear_combination h
      have h_diff0 : 125 * ξ ^ 4 - 100 * ξ ^ 3 + 100 * ξ - 125 = 0 := by
        linear_combination h1 - h_rev
      have h_diff : (ξ - 1) * (ξ + 1) * (125 * ξ ^ 2 - 100 * ξ + 125) = 0 := by
        have hfact :
            (ξ - 1) * (ξ + 1) * (125 * ξ ^ 2 - 100 * ξ + 125) =
              125 * ξ ^ 4 - 100 * ξ ^ 3 + 100 * ξ - 125 := by
          ring
        rw [hfact]
        exact h_diff0
      rcases mul_eq_zero.mp h_diff with hpm | hq
      · rcases mul_eq_zero.mp hpm with h_one | h_neg
        · have : ξ = 1 := by
            linear_combination h_one
          subst this
          norm_num at h1
        · have : ξ = -1 := by
            linear_combination h_neg
          subst this
          norm_num at h1
      · have hξ_val : ξ = 5 / 4 := bdf5_quartic_eq_five_fourths ξ hq h1
        rw [hξ_val] at habs
        norm_num at habs

/-! ## BDF6 (Backward Differentiation Formula, 6-step)

The BDF6 method:
  y_{n+6} - (360/147)y_{n+5} + (450/147)y_{n+4} - (400/147)y_{n+3}
  + (225/147)y_{n+2} - (72/147)y_{n+1} + (10/147)y_n = (60/147)h·f_{n+6}.

It is implicit and has order 6 — the highest-order zero-stable BDF method.
BDF7 and higher are zero-unstable (Dahlquist's first barrier for BDF).

Reference: Iserles, Section 4.5; Hairer–Wanner, Section V.1.
-/

/-- **BDF6** (Backward Differentiation Formula, 6-step):
  Coefficients: α = [10/147, -72/147, 225/147, -400/147, 450/147, -360/147, 1],
  β = [0, 0, 0, 0, 0, 0, 60/147]. -/
noncomputable def bdf6 : LMM 6 where
  α := ![10/147, -72/147, 225/147, -400/147, 450/147, -360/147, 1]
  β := ![0, 0, 0, 0, 0, 0, 60/147]
  normalized := by simp [Fin.last]

/-- BDF6 is consistent. -/
theorem bdf6_consistent : bdf6.IsConsistent :=
  ⟨by simp [LMM.rho, bdf6, Fin.sum_univ_succ]; norm_num,
   by simp [LMM.sigma, bdf6, Fin.sum_univ_succ]; norm_num⟩

/-- BDF6 has order 6. -/
theorem bdf6_order_six : bdf6.HasOrder 6 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, bdf6, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, bdf6, Fin.sum_univ_succ]; norm_num

/-- BDF6 is implicit (β₆ = 60/147 ≠ 0). -/
theorem bdf6_implicit : bdf6.IsImplicit := by
  simp [LMM.IsImplicit, bdf6, Fin.last]

/-- Helper: every root of Q₅ = 147ξ⁵-213ξ⁴+237ξ³-163ξ²+62ξ-10 has ‖ξ‖ ≤ 1.
  Proof: assume ‖ξ‖ > 1, set w = ξ⁻¹ with ‖w‖ < 1, derive reciprocal polynomial in w,
  decompose w = a + bi with a²+b² < 1, then nlinarith on real/imaginary parts. -/
private theorem bdf6_quintic_roots_in_disk (ξ : ℂ)
    (h1 : 147 * ξ ^ 5 - 213 * ξ ^ 4 + 237 * ξ ^ 3 - 163 * ξ ^ 2 + 62 * ξ - 10 = 0) :
    ‖ξ‖ ≤ 1 := by
  by_contra h_contra
  push_neg at h_contra
  have h_ne : ξ ≠ 0 := by intro h; rw [h, norm_zero] at h_contra; linarith
  have hw_norm : ‖ξ⁻¹‖ < 1 := by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h_contra
  have hw1 : (10 : ℂ) * ξ⁻¹ ^ 5 - 62 * ξ⁻¹ ^ 4 + 163 * ξ⁻¹ ^ 3 - 237 * ξ⁻¹ ^ 2 +
      213 * ξ⁻¹ - 147 = 0 := by
    rw [inv_pow]; have h5 : ξ ^ 5 ≠ 0 := pow_ne_zero 5 h_ne; field_simp; linear_combination -h1
  set w := ξ⁻¹; set a := w.re; set b := w.im
  have hab : a ^ 2 + b ^ 2 < 1 := by
    rw [show w = ↑a + ↑b * Complex.I from (Complex.re_add_im w).symm,
      Complex.norm_add_mul_I] at hw_norm
    by_contra h; push_neg at h; linarith [Real.one_le_sqrt.mpr h]
  rw [show w = ↑a + ↑b * Complex.I from (Complex.re_add_im w).symm] at hw1
  norm_num [Complex.ext_iff, pow_succ, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im] at hw1
  obtain ⟨h_re, h_im⟩ := hw1
  ring_nf at h_re h_im
  by_cases hb : b = 0
  · simp only [hb] at h_re; ring_nf at h_re
    nlinarith [sq_nonneg a, sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (a ^ 2 - 1),
      sq_nonneg (a ^ 2), sq_nonneg (a ^ 2 - a), mul_self_nonneg (a ^ 2 - a)]
  · have h_im2 : b * (-(a * 474) + a * b ^ 2 * 248 + a ^ 2 * 489 - a ^ 2 * b ^ 2 * 100 -
        a ^ 3 * 248 + a ^ 4 * 50 + 213 - b ^ 2 * 163 + b ^ 4 * 10) = 0 := by linarith
    have h_im3 : -(a * 474) + a * b ^ 2 * 248 + a ^ 2 * 489 - a ^ 2 * b ^ 2 * 100 -
        a ^ 3 * 248 + a ^ 4 * 50 + 213 - b ^ 2 * 163 + b ^ 4 * 10 = 0 := by
      rcases mul_eq_zero.mp h_im2 with h | h
      · exact absurd h hb
      · exact h
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (b ^ 2),
      sq_nonneg (a ^ 2 + b ^ 2), sq_nonneg (a * b), sq_nonneg (a ^ 2 - a), sq_nonneg (a * b ^ 2),
      sq_nonneg (b ^ 2 - a), sq_nonneg (a ^ 2 * b), mul_self_nonneg (a ^ 2 - a),
      mul_self_nonneg (b ^ 2 + a - 1), sq_nonneg (a ^ 2 + b ^ 2 - 1)]

/-- Helper: Q₅ has no roots on the unit circle.
  Proof: from q(ξ)=0 and |ξ|=1, derive the reciprocal polynomial (via conjugation),
  subtract to get a palindromic quartic r(ξ)=0, then use the Bézout identity
  A(ξ)·q(ξ) + B(ξ)·r(ξ) = 70761600 to derive 0 = 70761600. -/
private theorem bdf6_quintic_no_unit_roots (ξ : ℂ)
    (h1 : 147 * ξ ^ 5 - 213 * ξ ^ 4 + 237 * ξ ^ 3 - 163 * ξ ^ 2 + 62 * ξ - 10 = 0)
    (habs : ‖ξ‖ = 1) : False := by
  -- Step 1: From ‖ξ‖ = 1, get ξ · conj(ξ) = 1 and ξ ≠ 0.
  have h_inv : ξ * starRingEnd ℂ ξ = 1 := by
    simp +decide [Complex.mul_conj, Complex.normSq_eq_norm_sq, habs]
  have h_ne : ξ ≠ 0 := by intro h; rw [h] at h1; norm_num at h1
  -- Step 2: Since coefficients are real integers, p(conj ξ) = 0.
  have h_conj : 147 * (starRingEnd ℂ ξ) ^ 5 - 213 * (starRingEnd ℂ ξ) ^ 4 +
      237 * (starRingEnd ℂ ξ) ^ 3 - 163 * (starRingEnd ℂ ξ) ^ 2 +
      62 * (starRingEnd ℂ ξ) - 10 = 0 := by
    simpa using congr_arg Star.star h1
  -- Step 3: conj(ξ) = ξ⁻¹, substitute and multiply by ξ⁵ to get reciprocal polynomial.
  rw [eq_inv_of_mul_eq_one_right h_inv] at h_conj
  have h_recip : -10 * ξ ^ 5 + 62 * ξ ^ 4 - 163 * ξ ^ 3 + 237 * ξ ^ 2 -
      213 * ξ + 147 = 0 := by
    have h5 : ξ ^ 5 ≠ 0 := pow_ne_zero 5 h_ne
    have : ξ ^ 5 * (147 * (ξ⁻¹) ^ 5 - 213 * (ξ⁻¹) ^ 4 + 237 * (ξ⁻¹) ^ 3 -
        163 * (ξ⁻¹) ^ 2 + 62 * ξ⁻¹ - 10) = 0 := by rw [h_conj]; ring
    rw [inv_pow] at this; field_simp at this; linear_combination this
  -- Step 4: Subtract to get palindromic quartic = 0.
  have h_pal : 157 * ξ ^ 4 - 118 * ξ ^ 3 + 282 * ξ ^ 2 - 118 * ξ + 157 = 0 := by
    have hsub : (ξ - 1) * (157 * ξ ^ 4 - 118 * ξ ^ 3 + 282 * ξ ^ 2 - 118 * ξ + 157) = 0 := by
      linear_combination h1 - h_recip
    rcases mul_eq_zero.mp hsub with h0 | done
    · exfalso
      have h_one : ξ = 1 := by linear_combination h0
      rw [h_one] at h1; norm_num at h1
    · exact done
  -- Step 5: Bézout identity gives contradiction.
  -- A(ξ)·q(ξ) + B(ξ)·r(ξ) = 70761600, where
  -- A = -956287ξ³ + 793313ξ² - 150175ξ + 719361
  -- B = 895377ξ⁴ - 1367208ξ³ + 24615ξ² + 79544ξ + 496530
  have : (70761600 : ℂ) = 0 := by
    linear_combination (-956287 * ξ ^ 3 + 793313 * ξ ^ 2 - 150175 * ξ + 719361) * h1 +
      (895377 * ξ ^ 4 - 1367208 * ξ ^ 3 + 24615 * ξ ^ 2 + 79544 * ξ + 496530) * h_pal
  norm_num at this

/-- BDF6 is zero-stable: `ρ(ξ) = ξ⁶ - (360/147)ξ⁵ + (450/147)ξ⁴ - (400/147)ξ³
  + (225/147)ξ² - (72/147)ξ + 10/147`.
  Factoring: `147·ρ(ξ) = (ξ - 1) (147ξ⁵ - 213ξ⁴ + 237ξ³ - 163ξ² + 62ξ - 10)`.
  Root `ξ = 1` is simple. The quintic factor has all roots strictly inside the unit disk,
  so every root of `ρ` lies in `‖ξ‖ ≤ 1` and every unit root is simple.
  Reference: Iserles, Section 4.5; BDF6 is the highest-order zero-stable BDF method. -/
theorem bdf6_zeroStable : bdf6.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp only [LMM.rhoC, bdf6] at hξ
    simp [Fin.sum_univ_succ] at hξ
    have h147 : (ξ - 1) * (147 * ξ ^ 5 - 213 * ξ ^ 4 + 237 * ξ ^ 3 - 163 * ξ ^ 2 +
        62 * ξ - 10) = 0 := by
      linear_combination 147 * hξ
    rcases mul_eq_zero.mp h147 with h0 | h1
    · have : ξ = 1 := by linear_combination h0
      rw [this]; simp
    · exact bdf6_quintic_roots_in_disk ξ h1
  unit_roots_simple := by
    intro ξ hξ habs
    simp only [LMM.rhoCDeriv, bdf6]
    simp only [LMM.rhoC, bdf6] at hξ
    simp [Fin.sum_univ_succ] at hξ
    have h147 : (ξ - 1) * (147 * ξ ^ 5 - 213 * ξ ^ 4 + 237 * ξ ^ 3 - 163 * ξ ^ 2 +
        62 * ξ - 10) = 0 := by
      linear_combination 147 * hξ
    rcases mul_eq_zero.mp h147 with h0 | h1
    · have hξ1 : ξ = 1 := by linear_combination h0
      rw [hξ1]
      simp [Fin.sum_univ_succ]
      norm_num
    · exact (bdf6_quintic_no_unit_roots ξ h1 habs).elim

/-! ## BDF7 (Backward Differentiation Formula, 7-step)

The BDF7 method is the first BDF method that is not zero-stable. Its
characteristic polynomial has a nontrivial sextic factor with roots outside the
unit disk.

Reference: Iserles, Section 4.5; Hairer–Wanner, Section V.1.
-/

/-- **BDF7** (Backward Differentiation Formula, 7-step):
  Coefficients normalized by `1089`:
  `α = [-60, 490, -1764, 3675, -4900, 4410, -2940, 1089] / 1089`,
  `β = [0, 0, 0, 0, 0, 0, 0, 420/1089]`. -/
noncomputable def bdf7 : LMM 7 where
  α := ![-60/1089, 490/1089, -1764/1089, 3675/1089,
    -4900/1089, 4410/1089, -2940/1089, 1]
  β := ![0, 0, 0, 0, 0, 0, 0, 420/1089]
  normalized := by simp [Fin.last]

/-- BDF7 is consistent. -/
theorem bdf7_consistent : bdf7.IsConsistent :=
  ⟨by simp [LMM.rho, bdf7, Fin.sum_univ_succ]; norm_num,
   by simp [LMM.sigma, bdf7, Fin.sum_univ_succ]; norm_num⟩

/-- BDF7 has order 7. -/
theorem bdf7_order_seven : bdf7.HasOrder 7 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, bdf7, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, bdf7, Fin.sum_univ_succ]; norm_num

/-- BDF7 is implicit (`β₇ = 420/1089 ≠ 0`). -/
theorem bdf7_implicit : bdf7.IsImplicit := by
  simp [LMM.IsImplicit, bdf7, Fin.last]

/-- BDF7 characteristic factorization:
`1089 ρ(ξ) = (ξ - 1) Q(ξ)`, where `Q` is the sextic factor. -/
private theorem bdf7_rhoC_factor (ξ : ℂ) :
    1089 * bdf7.rhoC ξ =
      (ξ - 1) *
        (1089 * ξ ^ 6 - 1851 * ξ ^ 5 + 2559 * ξ ^ 4 -
          2341 * ξ ^ 3 + 1334 * ξ ^ 2 - 430 * ξ + 60) := by
  simp [LMM.rhoC, bdf7, Fin.sum_univ_succ]
  ring_nf

/-- A root of the BDF7 sextic factor outside the unit disk contradicts
zero-stability. -/
private theorem bdf7_not_zeroStable_of_bad_root
    {ξ : ℂ}
    (hQ : 1089 * ξ ^ 6 - 1851 * ξ ^ 5 + 2559 * ξ ^ 4 -
      2341 * ξ ^ 3 + 1334 * ξ ^ 2 - 430 * ξ + 60 = 0)
    (hgt : 1 < ‖ξ‖) :
    ¬ bdf7.IsZeroStable := by
  intro hzs
  have hscaled : 1089 * bdf7.rhoC ξ = 0 := by
    rw [bdf7_rhoC_factor, hQ]
    ring_nf
  have h1089 : (1089 : ℂ) ≠ 0 := by norm_num
  have hroot : bdf7.rhoC ξ = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left h1089
  have hle := hzs.roots_in_disk ξ hroot
  linarith

/-- Cayley algebraic identity (denominator-cleared form). After multiplying
through by `(1 - w)^6`, the BDF7 sextic in `ξ = (1 + w)/(1 - w)` becomes
the explicit transformed sextic in `w` with all positive integer
coefficients. -/
private lemma bdf7_cayley_identity (w : ℂ) (hw : w ≠ 1) :
    (1 - w) ^ 6 *
      (1089 * ((1 + w) / (1 - w)) ^ 6 - 1851 * ((1 + w) / (1 - w)) ^ 5
        + 2559 * ((1 + w) / (1 - w)) ^ 4 - 2341 * ((1 + w) / (1 - w)) ^ 3
        + 1334 * ((1 + w) / (1 - w)) ^ 2 - 430 * ((1 + w) / (1 - w)) + 60)
      = 4 * (2416 * w ^ 6 + 3577 * w ^ 5 + 4431 * w ^ 4 + 3920 * w ^ 3
              + 2240 * w ^ 2 + 735 * w + 105) := by
  have h1w : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  field_simp
  ring

/-- Cayley norm bridge: a complex `w` with positive real part has
`(1 + w)/(1 - w)` of norm strictly greater than one. -/
private lemma bdf7_cayley_norm_gt_one (w : ℂ) (hw : w ≠ 1)
    (hre : 0 < w.re) : 1 < ‖(1 + w) / (1 - w)‖ := by
  have h1w : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hpos : 0 < ‖(1 - w : ℂ)‖ := norm_pos_iff.mpr h1w
  rw [norm_div, lt_div_iff₀ hpos, one_mul, ← Real.sqrt_sq (norm_nonneg _),
    ← Real.sqrt_sq (norm_nonneg (1 + w))]
  apply Real.sqrt_lt_sqrt (by positivity)
  rw [Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  nlinarith [hre, sq_nonneg w.im, sq_nonneg w.re]

/- The following private block gives an exact algebraic certificate for a
quadratic factor of the Cayley-transformed BDF7 sextic. The real parameter `u`
is isolated by IVT as a root of the displayed resultant; `v` is then recovered
from a subresultant relation. -/

private def bdf7ImageResultant (u : ℝ) : ℝ :=
  82316074157080576 * u ^ 15 - 609363818832527360 * u ^ 14
    + 2408261116841058304 * u ^ 13 - 6514870294422436352 * u ^ 12
    + 13208207325027637552 * u ^ 11 - 20962474341486450521 * u ^ 10
    + 26625931844901622940 * u ^ 9 - 27321870458885833894 * u ^ 8
    + 22653334181508743132 * u ^ 7 - 15049863042340942732 * u ^ 6
    + 7863204624637456640 * u ^ 5 - 3123094779618149560 * u ^ 4
    + 886024688374571760 * u ^ 3 - 157041819655697760 * u ^ 2
    + 11001221248248000 * u + 782187023520000

private def bdf7ImageSubresA (u : ℝ) : ℝ :=
  197432582144 * u ^ 6 - 584616180736 * u ^ 5 + 825162930368 * u ^ 4
    - 650530820653 * u ^ 3 + 288832752026 * u ^ 2 - 64731237634 * u
    + 2696803200

private def bdf7ImageSubresB (u : ℝ) : ℝ :=
  -70511636480 * u ^ 8 + 229670642432 * u ^ 7 - 402484358528 * u ^ 6
    + 489402710482 * u ^ 5 - 452277012173 * u ^ 4 + 308142297337 * u ^ 3
    - 138902038800 * u ^ 2 + 35521344110 * u - 3345073200

private noncomputable def bdf7ImageFactorV (u : ℝ) : ℝ :=
  - bdf7ImageSubresB u / bdf7ImageSubresA u

private def bdf7ImageRemX (u v : ℝ) : ℝ :=
  2416 * u ^ 5 - 3577 * u ^ 4 - 9664 * u ^ 3 * v + 4431 * u ^ 3
    + 10731 * u ^ 2 * v - 3920 * u ^ 2 + 7248 * u * v ^ 2
    - 8862 * u * v + 2240 * u - 3577 * v ^ 2 + 3920 * v - 735

private def bdf7ImageRemC (u v : ℝ) : ℝ :=
  2416 * u ^ 4 * v - 3577 * u ^ 3 * v - 7248 * u ^ 2 * v ^ 2
    + 4431 * u ^ 2 * v + 7154 * u * v ^ 2 - 3920 * u * v
    + 2416 * v ^ 3 - 4431 * v ^ 2 + 2240 * v - 105

private def bdf7ImageSubresS (u v : ℝ) : ℝ :=
  bdf7ImageSubresA u * v + bdf7ImageSubresB u

private def bdf7ImageRemXQuot (u v : ℝ) : ℝ :=
  -1396920132632576 * u ^ 9 + 5851506869583872 * u ^ 8
    + 1430991355379712 * u ^ 7 * v - 12258799818924288 * u ^ 7
    - 4943514424303616 * u ^ 6 * v + 16109480176228320 * u ^ 6
    + 8071952997799936 * u ^ 5 * v - 14347717989788925 * u ^ 5
    - 7666655190019280 * u ^ 4 * v + 8873459518514031 * u ^ 4
    + 4420408532160229 * u ^ 3 * v - 3721422507792577 * u ^ 3
    - 1502326764368234 * u ^ 2 * v + 980500716096748 * u ^ 2
    + 251090066610418 * u * v - 126340583048610 * u
    - 9646465046400 * v - 1393858292400

private def bdf7ImageRemCMult (u : ℝ) : ℝ :=
  4527384078639431680 * u ^ 9 - 22668334060570017792 * u ^ 8
    + 52529295330860544000 * u ^ 7 - 72202285294233961216 * u ^ 6
    + 63690444085273487552 * u ^ 5 - 36436090080185538778 * u ^ 4
    + 12972794840039389999 * u ^ 3 - 2509303901071415098 * u ^ 2
    + 145246584929007758 * u + 11705411018448000

private def bdf7ImageRemCQuot (u v : ℝ) : ℝ :=
  5285318880105353304866816 * u ^ 16
    - 48373713994630708777189376 * u ^ 15
    - 248890470899506637447364608 * u ^ 14 * v
    + 224120608413704054266396672 * u ^ 14
    + 1742876460100665242707558400 * u ^ 13 * v
    - 687960369288710609830215680 * u ^ 13
    + 94174772772786295250354176 * u ^ 12 * v ^ 2
    - 6006026034865457109447737344 * u ^ 12 * v
    + 1545140092754173728792211456 * u ^ 12
    - 557720467232212877666418688 * u ^ 11 * v ^ 2
    + 13283025506875155649187741696 * u ^ 11 * v
    - 2655843488471489042840691200 * u ^ 11
    + 1612931686419420184188026880 * u ^ 10 * v ^ 2
    - 20853238637696456515689410560 * u ^ 10 * v
    + 3571610905949829584488377360 * u ^ 10
    - 2951576853084445664218972160 * u ^ 9 * v ^ 2
    + 24390803819549434784674519040 * u ^ 9 * v
    - 3793691735032030595782233565 * u ^ 9
    + 3758246347965459157634613248 * u ^ 8 * v ^ 2
    - 21760907319213177837100762992 * u ^ 8 * v
    + 3185046990436800717483774155 * u ^ 8
    - 3471455084050603574751332352 * u ^ 7 * v ^ 2
    + 14930016929894569675230298450 * u ^ 7 * v
    - 2097974434334251590281567851 * u ^ 7
    + 2359487924308581197997045488 * u ^ 6 * v ^ 2
    - 7842142369551192120402467231 * u ^ 6 * v
    + 1065579406723227434699762339 * u ^ 6
    - 1173620415317663547111711680 * u ^ 5 * v ^ 2
    + 3097267064694145260621415180 * u ^ 5 * v
    - 404041646129528444971599904 * u ^ 5
    + 415779811851878776285630080 * u ^ 4 * v ^ 2
    - 886259048365369479609317432 * u ^ 4 * v
    + 107579755198903701755511148 * u ^ 4
    - 98818531875636430491157888 * u ^ 3 * v ^ 2
    + 171111508138954230605095072 * u ^ 3 * v
    - 17615966323663653949097220 * u ^ 3
    + 13887127666055201554204096 * u ^ 2 * v ^ 2
    - 19225258859905121677932796 * u ^ 2 * v
    + 1140838018929524447336700 * u ^ 2
    - 843509719279714430361600 * u * v ^ 2
    + 844468889054059142092800 * u * v
    + 63730832790673342576800 * u
    + 17570957958865059840000 * v ^ 2 - 10430798240672409600000 * v
    + 3352752735036768000000

private lemma bdf7ImageResultant_neg_left :
    bdf7ImageResultant (-1 / 24) < 0 := by
  norm_num [bdf7ImageResultant]

private lemma bdf7ImageResultant_pos_right :
    0 < bdf7ImageResultant (-1 / 25) := by
  norm_num [bdf7ImageResultant]

private lemma bdf7ImageSubresA_pos {u : ℝ} (hu : u < 0) :
    0 < bdf7ImageSubresA u := by
  unfold bdf7ImageSubresA
  nlinarith [sq_nonneg (u ^ 3), sq_nonneg (u ^ 2), sq_nonneg u, hu]

private lemma bdf7ImageRemX_zero {u : ℝ} (hR : bdf7ImageResultant u = 0)
    (hA : bdf7ImageSubresA u ≠ 0) :
    bdf7ImageRemX u (bdf7ImageFactorV u) = 0 := by
  set v := bdf7ImageFactorV u with hv
  have hS : bdf7ImageSubresS u v = 0 := by
    rw [hv]
    unfold bdf7ImageFactorV bdf7ImageSubresS
    field_simp [hA]
    ring
  have hmul :
      bdf7ImageSubresA u ^ 2 * bdf7ImageRemX u v
          + (7248 * u - 3577) ^ 2 * bdf7ImageResultant u =
        bdf7ImageRemXQuot u v * bdf7ImageSubresS u v := by
    unfold bdf7ImageRemXQuot bdf7ImageSubresS bdf7ImageRemX bdf7ImageSubresA
      bdf7ImageSubresB bdf7ImageResultant
    ring
  rw [hR, hS, mul_zero, mul_zero, add_zero] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 2 hA)

private lemma bdf7ImageRemC_zero {u : ℝ} (hR : bdf7ImageResultant u = 0)
    (hA : bdf7ImageSubresA u ≠ 0) :
    bdf7ImageRemC u (bdf7ImageFactorV u) = 0 := by
  set v := bdf7ImageFactorV u with hv
  have hS : bdf7ImageSubresS u v = 0 := by
    rw [hv]
    unfold bdf7ImageFactorV bdf7ImageSubresS
    field_simp [hA]
    ring
  have hmul :
      bdf7ImageSubresA u ^ 3 * bdf7ImageRemC u v
          - bdf7ImageRemCMult u * bdf7ImageResultant u =
        bdf7ImageRemCQuot u v * bdf7ImageSubresS u v := by
    unfold bdf7ImageRemCQuot bdf7ImageSubresS bdf7ImageRemCMult bdf7ImageRemC
      bdf7ImageSubresA bdf7ImageSubresB bdf7ImageResultant
    ring
  rw [hR, hS, mul_zero, mul_zero, sub_zero] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 3 hA)

private theorem bdf7ImageResultant_root_exists :
    ∃ u : ℝ, u ∈ Set.Icc (-1 / 24) (-1 / 25) ∧ bdf7ImageResultant u = 0 := by
  have hab : (-1 / 24 : ℝ) ≤ -1 / 25 := by norm_num
  have hcont : ContinuousOn bdf7ImageResultant (Set.Icc (-1 / 24) (-1 / 25)) := by
    unfold bdf7ImageResultant
    fun_prop
  have hmem : (0 : ℝ) ∈
      Set.Icc (bdf7ImageResultant (-1 / 24)) (bdf7ImageResultant (-1 / 25)) := by
    constructor
    · linarith [bdf7ImageResultant_neg_left]
    · linarith [bdf7ImageResultant_pos_right]
  exact intermediate_value_Icc hab hcont hmem

private lemma bdf7_quadratic_root_pos {u v : ℝ} (hu : u < 0) :
    ∃ w : ℂ, w ^ 2 + (u : ℂ) * w + (v : ℂ) = 0 ∧ 0 < w.re := by
  obtain ⟨s, hs⟩ :=
    IsAlgClosed.exists_pow_nat_eq (((u : ℂ) ^ 2) / 4 - (v : ℂ)) (by norm_num : 0 < 2)
  by_cases hsre : 0 ≤ s.re
  · refine ⟨- (u : ℂ) / 2 + s, ?_, ?_⟩
    · calc
        (- (u : ℂ) / 2 + s) ^ 2 + (u : ℂ) * (- (u : ℂ) / 2 + s) + (v : ℂ)
            = s ^ 2 - (u : ℂ) ^ 2 / 4 + (v : ℂ) := by ring
        _ = 0 := by rw [hs]; ring
    · norm_num [Complex.add_re, Complex.div_re, Complex.neg_re, Complex.normSq]
      nlinarith
  · refine ⟨- (u : ℂ) / 2 - s, ?_, ?_⟩
    · calc
        (- (u : ℂ) / 2 - s) ^ 2 + (u : ℂ) * (- (u : ℂ) / 2 - s) + (v : ℂ)
            = s ^ 2 - (u : ℂ) ^ 2 / 4 + (v : ℂ) := by ring
        _ = 0 := by rw [hs]; ring
    · norm_num [Complex.sub_re, Complex.div_re, Complex.neg_re, Complex.normSq] at hsre ⊢
      nlinarith

private def bdf7ImageQuotC (u v w : ℂ) : ℂ :=
  2416 * u ^ 4 - 2416 * u ^ 3 * w - 3577 * u ^ 3 - 7248 * u ^ 2 * v
    + 2416 * u ^ 2 * w ^ 2 + 3577 * u ^ 2 * w + 4431 * u ^ 2
    + 4832 * u * v * w + 7154 * u * v - 2416 * u * w ^ 3
    - 3577 * u * w ^ 2 - 4431 * u * w - 3920 * u + 2416 * v ^ 2
    - 2416 * v * w ^ 2 - 3577 * v * w - 4431 * v + 2416 * w ^ 4
    + 3577 * w ^ 3 + 4431 * w ^ 2 + 3920 * w + 2240

private lemma bdf7Image_factor_eval (u v : ℝ) (w : ℂ) :
    2416 * w ^ 6 + 3577 * w ^ 5 + 4431 * w ^ 4 + 3920 * w ^ 3
        + 2240 * w ^ 2 + 735 * w + 105 =
      (w ^ 2 + (u : ℂ) * w + (v : ℂ)) * bdf7ImageQuotC (u : ℂ) (v : ℂ) w
        - (bdf7ImageRemX u v : ℂ) * w - (bdf7ImageRemC u v : ℂ) := by
  unfold bdf7ImageQuotC bdf7ImageRemX bdf7ImageRemC
  norm_num
  ring

/-- The transformed sextic in `w` has a root with positive real part. -/
private lemma bdf7_cayley_image_root :
    ∃ w : ℂ, 2416 * w ^ 6 + 3577 * w ^ 5 + 4431 * w ^ 4 + 3920 * w ^ 3
              + 2240 * w ^ 2 + 735 * w + 105 = 0 ∧ 0 < w.re := by
  obtain ⟨u, hu_mem, hR⟩ := bdf7ImageResultant_root_exists
  have hu_neg : u < 0 := by linarith [hu_mem.2]
  have hA : bdf7ImageSubresA u ≠ 0 := ne_of_gt (bdf7ImageSubresA_pos hu_neg)
  let v := bdf7ImageFactorV u
  have hx : bdf7ImageRemX u v = 0 := by simpa [v] using bdf7ImageRemX_zero hR hA
  have hc : bdf7ImageRemC u v = 0 := by simpa [v] using bdf7ImageRemC_zero hR hA
  obtain ⟨w, hq, hwre⟩ := bdf7_quadratic_root_pos (u := u) (v := v) hu_neg
  refine ⟨w, ?_, hwre⟩
  rw [bdf7Image_factor_eval u v w, hq, hx, hc]
  norm_num

/-- The BDF7 sextic factor has a root outside the closed unit disk. -/
private theorem bdf7_bad_root_exists :
    ∃ ξ : ℂ,
      1089 * ξ ^ 6 - 1851 * ξ ^ 5 + 2559 * ξ ^ 4 -
        2341 * ξ ^ 3 + 1334 * ξ ^ 2 - 430 * ξ + 60 = 0 ∧ 1 < ‖ξ‖ := by
  obtain ⟨w, hw_root, hw_re⟩ := bdf7_cayley_image_root
  have hw_ne : w ≠ 1 := by
    intro h
    rw [h] at hw_root
    norm_num at hw_root
  refine ⟨(1 + w) / (1 - w), ?_, bdf7_cayley_norm_gt_one w hw_ne hw_re⟩
  have h1w : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw_ne)
  have h1w6 : (1 - w) ^ 6 ≠ 0 := pow_ne_zero _ h1w
  have hid := bdf7_cayley_identity w hw_ne
  have hzero :
      4 * (2416 * w ^ 6 + 3577 * w ^ 5 + 4431 * w ^ 4 + 3920 * w ^ 3
            + 2240 * w ^ 2 + 735 * w + 105) = 0 := by
    rw [hw_root]; ring
  rw [hzero] at hid
  exact (mul_eq_zero.mp hid).resolve_left h1w6

/-- BDF7 is not zero-stable. -/
theorem bdf7_not_zeroStable : ¬ bdf7.IsZeroStable := by
  obtain ⟨ξ, hQ, hgt⟩ := bdf7_bad_root_exists
  exact bdf7_not_zeroStable_of_bad_root hQ hgt

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

/-! ### Reversed Polynomial Infrastructure

The reversed polynomials ρ̃(w) = ∑ α_{s-j} w^j and σ̃(w) = ∑ β_{s-j} w^j
satisfy ρ̃(w) = w^s · ρ(1/w) and σ̃(w) = w^s · σ(1/w) for w ≠ 0.
They appear in the Dahlquist barrier proof via the conformal map w = 1/ζ. -/

/-- Reversed first characteristic polynomial: ρ̃(w) = ∑ α_{s-j} w^j. -/
noncomputable def rhoCRev (m : LMM s) (w : ℂ) : ℂ :=
  ∑ j : Fin (s + 1), (m.α (Fin.rev j) : ℂ) * w ^ (j : ℕ)

/-- Reversed second characteristic polynomial: σ̃(w) = ∑ β_{s-j} w^j. -/
noncomputable def sigmaCRev (m : LMM s) (w : ℂ) : ℂ :=
  ∑ j : Fin (s + 1), (m.β (Fin.rev j) : ℂ) * w ^ (j : ℕ)

/-- ρ̃(1) = ρ_ℂ(1): both evaluate to ∑ α_j. -/
theorem rhoCRev_one (m : LMM s) : m.rhoCRev 1 = m.rhoC 1 := by
  simp only [rhoCRev, rhoC, one_pow, mul_one]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by simp [Fin.revPerm_apply])

/-- σ̃(1) = σ_ℂ(1): both evaluate to ∑ β_j. -/
theorem sigmaCRev_one (m : LMM s) : m.sigmaCRev 1 = m.sigmaC 1 := by
  simp only [sigmaCRev, sigmaC, one_pow, mul_one]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by simp [Fin.revPerm_apply])

/-- For a consistent method (ρ(1) = 0), ρ̃(1) = 0. -/
theorem rhoCRev_one_eq_zero (m : LMM s) (hc : m.IsConsistent) : m.rhoCRev 1 = 0 := by
  rw [rhoCRev_one]; exact hc.rhoC_one m

/-- ρ̃ is differentiable (it's a polynomial function). -/
theorem rhoCRev_differentiable (m : LMM s) : Differentiable ℂ m.rhoCRev := by
  intro w; unfold rhoCRev; fun_prop

/-- σ̃ is differentiable (it's a polynomial function). -/
theorem sigmaCRev_differentiable (m : LMM s) : Differentiable ℂ m.sigmaCRev := by
  intro w; unfold sigmaCRev; fun_prop

/-- The reversed polynomial identity: ρ̃(z) = z^s · ρ(z⁻¹) for z ≠ 0. -/
theorem rhoCRev_eq (m : LMM s) (z : ℂ) (hz : z ≠ 0) :
    m.rhoCRev z = z ^ s * m.rhoC z⁻¹ := by
  simp only [rhoCRev, rhoC]
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by
    simp only [Fin.revPerm_apply]
    have hj : (j : ℕ) + (Fin.rev j : ℕ) = s := by rw [Fin.val_rev]; omega
    have key : z ^ (j : ℕ) = z ^ s * z⁻¹ ^ (Fin.rev j : ℕ) := by
      have h1 : z ^ (j : ℕ) * z ^ (Fin.rev j : ℕ) = z ^ s := by rw [← pow_add, hj]
      rw [inv_pow, ← h1, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hz), mul_one]
    rw [key, ← mul_assoc, mul_comm _ (z ^ s), mul_assoc])

/-- The reversed polynomial identity: σ̃(z) = z^s · σ(z⁻¹) for z ≠ 0. -/
theorem sigmaCRev_eq (m : LMM s) (z : ℂ) (hz : z ≠ 0) :
    m.sigmaCRev z = z ^ s * m.sigmaC z⁻¹ := by
  simp only [sigmaCRev, sigmaC]
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by
    simp only [Fin.revPerm_apply]
    have hj : (j : ℕ) + (Fin.rev j : ℕ) = s := by rw [Fin.val_rev]; omega
    have key : z ^ (j : ℕ) = z ^ s * z⁻¹ ^ (Fin.rev j : ℕ) := by
      have h1 : z ^ (j : ℕ) * z ^ (Fin.rev j : ℕ) = z ^ s := by rw [← pow_add, hj]
      rw [inv_pow, ← h1, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hz), mul_one]
    rw [key, ← mul_assoc, mul_comm _ (z ^ s), mul_assoc])

/-- On the unit circle, σ̃/ρ̃ = σ/ρ (the z^s factors cancel). -/
theorem sigmaCRev_div_rhoCRev_eq (m : LMM s) (z : ℂ) (hz : z ≠ 0) :
    m.sigmaCRev z / m.rhoCRev z = m.sigmaC z⁻¹ / m.rhoC z⁻¹ := by
  rw [sigmaCRev_eq m z hz, rhoCRev_eq m z hz]
  rw [mul_div_mul_left _ _ (pow_ne_zero s hz)]

/-- ρ̃(w) ≠ 0 for |w| < 1, for A-stable methods.
Roots of ρ̃ correspond to 1/ζ for roots ζ of ρ. A-stability puts roots of ρ in |ζ| ≤ 1,
so roots of ρ̃ have |·| ≥ 1. At w = 0: ρ̃(0) = α_s = 1 ≠ 0 (normalized). -/
theorem rhoCRev_ne_zero_of_norm_lt_one (m : LMM s) (ha : m.IsAStable)
    (w : ℂ) (hw : ‖w‖ < 1) : m.rhoCRev w ≠ 0 := by
  by_cases hw0 : w = 0
  · -- At w = 0: ρ̃(0) = α_s = 1 ≠ 0
    subst hw0; show (∑ j : Fin (s + 1), (m.α (Fin.rev j) : ℂ) * (0 : ℂ) ^ (j : ℕ)) ≠ 0
    have h_single : ∀ j : Fin (s + 1), j ≠ 0 →
        (m.α (Fin.rev j) : ℂ) * (0 : ℂ) ^ (j : ℕ) = 0 := by
      intro j hj; rw [zero_pow (Fin.val_ne_of_ne hj), mul_zero]
    rw [Fintype.sum_eq_single 0 (fun j hj => h_single j hj)]
    simp only [Fin.val_zero, pow_zero, mul_one]
    have : Fin.rev (0 : Fin (s + 1)) = Fin.last s := by ext; simp [Fin.rev, Fin.last]
    rw [this, show (m.α (Fin.last s) : ℂ) = (1 : ℂ) from by
      rw [m.normalized]; push_cast; rfl]
    exact one_ne_zero
  · -- For w ≠ 0: ρ̃(w) = w^s · ρ(1/w). Since |1/w| > 1 and A-stability puts
    -- all roots of ρ in |ζ| ≤ 1, we have ρ(1/w) ≠ 0.
    rw [rhoCRev_eq m w hw0]
    apply mul_ne_zero (pow_ne_zero s hw0)
    intro hρ
    -- A-stability with z = 0: all roots of ρ have |·| ≤ 1
    have h_root : ‖w⁻¹‖ ≤ 1 := ha 0 (le_refl _) w⁻¹ (by
      show m.rhoC w⁻¹ - 0 * m.sigmaC w⁻¹ = 0; simp [hρ])
    -- But |w⁻¹| = 1/|w| > 1 since |w| < 1
    have : 1 < ‖w⁻¹‖ := by
      rw [norm_inv]
      have h1 := inv_strictAnti₀ (norm_pos_iff.mpr hw0) hw
      rwa [inv_one] at h1
    linarith

/-- The derivative of ρ̃ (as a polynomial) evaluated at 1 equals -ρ'(1) for consistent methods.
This follows from reindexing: ∑ j·α_{s-j} = ∑(s-k)·α_k = s·∑α_k - ∑k·α_k = -ρ'(1). -/
private lemma rhoCRev_poly_derivative_eval_one (m : LMM s) (hc : m.IsConsistent) :
    (∑ j : Fin (s + 1), Polynomial.C (↑(m.α (Fin.rev j)) : ℂ) *
      Polynomial.X ^ (j : ℕ)).derivative.eval (1 : ℂ) = -m.rhoCDeriv (1 : ℂ) := by
  -- Step 1: Expand derivative and evaluate at 1
  simp only [map_sum, Polynomial.derivative_C_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X, mul_one, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, one_pow, rhoCDeriv]
  -- Goal: ∑ x, ↑(m.α x.rev) * ↑↑x = -(∑ x, ↑↑x * ↑(m.α x))
  -- Suffices to show the two sums add to zero
  suffices h : (∑ x : Fin (s + 1), (↑(m.α (Fin.rev x)) : ℂ) * ((x : ℕ) : ℂ)) +
    (∑ x : Fin (s + 1), ((x : ℕ) : ℂ) * (↑(m.α x) : ℂ)) = 0 by linear_combination h
  -- Reindex the first sum via Fin.revPerm: ∑ α(rev x)*x = ∑ α(k)*rev(k)
  rw [Fintype.sum_equiv Fin.revPerm
    (fun x => (↑(m.α (Fin.rev x)) : ℂ) * ((x : ℕ) : ℂ))
    (fun k => (↑(m.α k) : ℂ) * ((Fin.rev k : ℕ) : ℂ))
    (fun k => by simp [Fin.revPerm_apply, Fin.rev_rev])]
  -- Combine into one sum: ∑ (α(k)*rev(k) + k*α(k))
  rw [← Finset.sum_add_distrib]
  -- Each term simplifies: α(k)*rev(k) + k*α(k) = α(k)*(rev(k) + k) = α(k)*s
  have hrev_add : ∀ k : Fin (s + 1),
      ((Fin.rev k : ℕ) : ℂ) + ((k : ℕ) : ℂ) = (s : ℂ) := fun k => by
    rw [← Nat.cast_add]; congr 1; simp [Fin.val_rev]; omega
  simp_rw [show ∀ k : Fin (s + 1),
    (↑(m.α k) : ℂ) * ((Fin.rev k : ℕ) : ℂ) + ((k : ℕ) : ℂ) * (↑(m.α k) : ℂ) =
    (↑(m.α k) : ℂ) * (s : ℂ) from fun k => by
      rw [mul_comm ((k : ℕ) : ℂ), ← mul_add, hrev_add]]
  -- Factor: ∑ α(k)*s = (∑ α(k)) * s
  rw [← Finset.sum_mul]
  -- Consistency: ∑ α(k) = rhoC(1) = 0
  have h0 : (∑ k : Fin (s + 1), (↑(m.α k) : ℂ)) = 0 := by
    have h := hc.rhoC_one m; simp only [rhoC, one_pow, mul_one] at h; exact h
  rw [h0, zero_mul]

/-- The C₂ order condition via reversed polynomials:
  2σ̃'(1) + ρ̃''(1) + ρ̃'(1) = 0 for methods of order ≥ 2.
This is used to show the triple-zero divisibility of the combined numerator. -/
private lemma reversed_poly_C2_condition (m : LMM s) (hp : m.HasOrder p) (hp2 : 2 ≤ p) :
    let ρrevPoly := ∑ j : Fin (s + 1), Polynomial.C (↑(m.α (Fin.rev j)) : ℂ) *
      Polynomial.X ^ (j : ℕ)
    let σrevPoly := ∑ j : Fin (s + 1), Polynomial.C (↑(m.β (Fin.rev j)) : ℂ) *
      Polynomial.X ^ (j : ℕ)
    2 * σrevPoly.derivative.eval (1 : ℂ) +
      ρrevPoly.derivative.derivative.eval (1 : ℂ) +
      ρrevPoly.derivative.eval (1 : ℂ) = 0 := by
  intro ρrevPoly σrevPoly
  -- Expand first and second derivatives and evaluate at 1
  simp only [show ρrevPoly = ∑ j : Fin (s + 1), Polynomial.C (↑(m.α (Fin.rev j)) : ℂ) *
      Polynomial.X ^ (j : ℕ) from rfl,
    show σrevPoly = ∑ j : Fin (s + 1), Polynomial.C (↑(m.β (Fin.rev j)) : ℂ) *
      Polynomial.X ^ (j : ℕ) from rfl,
    map_sum, Polynomial.derivative_C_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X, mul_one, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, one_pow]
  -- Goal: 2 * ∑ β(rev x)*x + ∑ α(rev x)*(x*(x-1:ℕ)) + ∑ α(rev x)*x = 0
  -- Combine the two α sums: x*(x-1:ℕ) + x = x² in ℕ
  have h_nat_sq : ∀ x : Fin (s + 1),
      (↑(m.α (Fin.rev x)) : ℂ) * ((↑(x : ℕ) : ℂ) * (↑((x : ℕ) - 1) : ℂ)) +
      (↑(m.α (Fin.rev x)) : ℂ) * (↑(x : ℕ) : ℂ) =
      (↑(m.α (Fin.rev x)) : ℂ) * (↑(x : ℕ) : ℂ) ^ 2 := by
    intro ⟨n, hn⟩; simp only [Fin.val_mk]
    rw [← mul_add, ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_pow]
    congr 1
    cases n with | zero => rfl | succ n => rw [Nat.succ_sub_one]; ring
  -- Combine the two α sums into one using h_nat_sq
  have h_combined :
      (∑ x : Fin (s + 1), (↑(m.α (Fin.rev x)) : ℂ) * ((↑(x : ℕ) : ℂ) * ↑((x : ℕ) - 1))) +
      (∑ x : Fin (s + 1), (↑(m.α (Fin.rev x)) : ℂ) * ↑(x : ℕ)) =
      ∑ x : Fin (s + 1), (↑(m.α (Fin.rev x)) : ℂ) * (↑(x : ℕ) : ℂ) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => h_nat_sq x)
  -- Step 1: Get the C₂ order condition in ℂ
  have hV₂ : (m.orderCondVal 2 : ℂ) = 0 := by
    rw [hp.conditions_hold 2 hp2]; simp
  simp only [orderCondVal, Nat.sub_self, pow_one, pow_zero, mul_one] at hV₂
  push_cast at hV₂
  -- hV₂ : ∑ k, ((k:ℕ):ℂ)^2 * (αₖ:ℂ) - 2 * ∑ k, ((k:ℕ):ℂ) * (βₖ:ℂ) = 0
  -- i.e., ∑ k, ((k:ℕ):ℂ)^2 * (αₖ:ℂ) = 2 * ∑ k, ((k:ℕ):ℂ) * (βₖ:ℂ)
  -- Step 2: Also get C₀ and C₁ in ℂ
  have hcons := hp.isConsistent (by omega)
  have hC₀ : (∑ k : Fin (s + 1), (↑(m.α k) : ℂ)) = 0 := by
    have h := hcons.rhoC_one m; simp only [rhoC, one_pow, mul_one] at h; exact h
  have hC₁ : (∑ k : Fin (s + 1), ((k : ℕ) : ℂ) * (↑(m.α k) : ℂ)) =
      (∑ k : Fin (s + 1), (↑(m.β k) : ℂ)) := by
    have h := hcons.sigmaC_one_eq_rhoCDeriv_one m
    simp only [sigmaC, rhoCDeriv, one_pow, mul_one] at h; exact h.symm
  -- Step 3: Combine the α derivative sums: j*(j-1) + j = j²
  -- suffices: ∑ α(rev j)*j² + 2*∑ β(rev j)*j = 0
  suffices hsuff :
      (∑ x : Fin (s + 1), (↑(m.α (Fin.rev x)) : ℂ) * ((x : ℕ) : ℂ) ^ 2) +
      2 * (∑ x : Fin (s + 1), (↑(m.β (Fin.rev x)) : ℂ) * ((x : ℕ) : ℂ)) = 0 by
    linear_combination hsuff + h_combined
  -- Step 4: Reindex both sums via Fin.revPerm
  rw [Fintype.sum_equiv Fin.revPerm
    (fun x => (↑(m.α (Fin.rev x)) : ℂ) * ((x : ℕ) : ℂ) ^ 2)
    (fun k => (↑(m.α k) : ℂ) * ((Fin.rev k : ℕ) : ℂ) ^ 2)
    (fun k => by simp [Fin.revPerm_apply, Fin.rev_rev])]
  rw [Fintype.sum_equiv Fin.revPerm
    (fun x => (↑(m.β (Fin.rev x)) : ℂ) * ((x : ℕ) : ℂ))
    (fun k => (↑(m.β k) : ℂ) * ((Fin.rev k : ℕ) : ℂ))
    (fun k => by simp [Fin.revPerm_apply, Fin.rev_rev])]
  -- Step 5: Use rev(k) + k = s to expand (rev k)² and (rev k)
  have hrev_add : ∀ k : Fin (s + 1),
      ((Fin.rev k : ℕ) : ℂ) + ((k : ℕ) : ℂ) = (s : ℂ) := fun k => by
    rw [← Nat.cast_add]; congr 1; simp [Fin.val_rev]; omega
  have hrev_eq : ∀ k : Fin (s + 1),
      ((Fin.rev k : ℕ) : ℂ) = (s : ℂ) - ((k : ℕ) : ℂ) := fun k => by
    have := hrev_add k; linear_combination this
  -- Rewrite (rev k)² = (s - k)² = s² - 2sk + k²
  simp_rw [hrev_eq]
  -- Expand (s - k)²
  simp_rw [sub_sq]
  -- Distribute: ∑ αₖ * (s² - 2sk + k²) + 2 * ∑ βₖ * (s - k) = 0
  simp_rw [mul_add, mul_sub]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- Factor and normalize each sum to match hypothesis forms
  have hS1 : ∑ x : Fin (s + 1), (↑(m.α x) : ℂ) * (↑s : ℂ) ^ 2 =
      (∑ x : Fin (s + 1), (↑(m.α x) : ℂ)) * (↑s : ℂ) ^ 2 :=
    (Finset.sum_mul Finset.univ _ _).symm
  have hS2 : ∑ x : Fin (s + 1), (↑(m.α x) : ℂ) * (2 * (↑s : ℂ) * (↑↑x : ℂ)) =
      2 * (↑s : ℂ) * ∑ x : Fin (s + 1), (↑↑x : ℂ) * (↑(m.α x) : ℂ) := by
    simp_rw [show ∀ x : Fin (s + 1), (↑(m.α x) : ℂ) * (2 * (↑s : ℂ) * ↑↑x) =
      2 * (↑s : ℂ) * ((↑↑x : ℂ) * ↑(m.α x)) from fun x => by ring]
    exact (Finset.mul_sum ..).symm
  have hS3 : ∑ x : Fin (s + 1), (↑(m.α x) : ℂ) * (↑↑x : ℂ) ^ 2 =
      ∑ x : Fin (s + 1), (↑↑x : ℂ) ^ 2 * (↑(m.α x) : ℂ) :=
    Finset.sum_congr rfl (fun x _ => mul_comm _ _)
  have hS4 : ∑ x : Fin (s + 1), (↑(m.β x) : ℂ) * (↑s : ℂ) =
      (∑ x : Fin (s + 1), (↑(m.β x) : ℂ)) * (↑s : ℂ) :=
    (Finset.sum_mul Finset.univ _ _).symm
  have hS5 : ∑ x : Fin (s + 1), (↑(m.β x) : ℂ) * (↑↑x : ℂ) =
      ∑ x : Fin (s + 1), (↑↑x : ℂ) * (↑(m.β x) : ℂ) :=
    Finset.sum_congr rfl (fun x _ => mul_comm _ _)
  rw [hS1, hS2, hS3, hS4, hS5]
  simp only [pow_one] at hV₂
  linear_combination (↑s : ℂ) ^ 2 * hC₀ - 2 * (↑s : ℂ) * hC₁ + hV₂

/-- The C₃ order condition via reversed polynomials:
  6σ̃''(1) + 2ρ̃'''(1) + 3ρ̃''(1) - ρ̃'(1) = 0 for methods of order ≥ 3.
This is the third-order identity needed in the cancelled derivative computation. -/
private lemma reversed_poly_C3_condition (m : LMM s) (hp : m.HasOrder p) (hp3 : 3 ≤ p) :
    let ρrevPoly := ∑ j : Fin (s + 1), Polynomial.C (↑(m.α (Fin.rev j)) : ℂ) *
      Polynomial.X ^ (j : ℕ)
    let σrevPoly := ∑ j : Fin (s + 1), Polynomial.C (↑(m.β (Fin.rev j)) : ℂ) *
      Polynomial.X ^ (j : ℕ)
    6 * σrevPoly.derivative.derivative.eval (1 : ℂ) +
      2 * ρrevPoly.derivative.derivative.derivative.eval (1 : ℂ) +
      3 * ρrevPoly.derivative.derivative.eval (1 : ℂ) -
      ρrevPoly.derivative.eval (1 : ℂ) = 0 := by
  intro ρrevPoly σrevPoly
  -- Step 1: Expand derivatives and evaluate at 1 (same simp set as C₂)
  simp only [show ρrevPoly = ∑ j : Fin (s + 1), Polynomial.C (↑(m.α (Fin.rev j)) : ℂ) *
      Polynomial.X ^ (j : ℕ) from rfl,
    show σrevPoly = ∑ j : Fin (s + 1), Polynomial.C (↑(m.β (Fin.rev j)) : ℂ) *
      Polynomial.X ^ (j : ℕ) from rfl,
    map_sum, Polynomial.derivative_C_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X, mul_one, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, one_pow]
  -- Step 2: Per-element identity for α: 2*x*(x-1)*(x-1-1) + 3*x*(x-1) - x = 2*x³ - 3*x²
  have h_nat_cube : ∀ x : Fin (s + 1),
      2 * ((↑(m.α x.rev) : ℂ) * (((x : ℕ) : ℂ) * ((((x : ℕ) - 1 : ℕ) : ℂ) * ((((x : ℕ) - 1 - 1 : ℕ) : ℂ))))) +
      3 * ((↑(m.α x.rev) : ℂ) * (((x : ℕ) : ℂ) * (((x : ℕ) - 1 : ℕ) : ℂ))) -
      (↑(m.α x.rev) : ℂ) * ((x : ℕ) : ℂ) =
      (↑(m.α x.rev) : ℂ) * (2 * ((x : ℕ) : ℂ) ^ 3 - 3 * ((x : ℕ) : ℂ) ^ 2) := by
    intro x
    rcases Nat.lt_or_ge (x : ℕ) 2 with hlt | hge
    · interval_cases (x : ℕ) <;> simp <;> ring
    · have h1 : 1 ≤ (x : ℕ) := by omega
      have h12 : 1 ≤ (x : ℕ) - 1 := by omega
      rw [show ((x : ℕ) - 1 - 1 : ℕ) = (x : ℕ) - 2 from by omega]
      push_cast [Nat.cast_sub h1, Nat.cast_sub hge, Nat.cast_sub h12]
      ring
  -- Step 3: Per-element identity for β: 6*x*(x-1) = 6*x² - 6*x
  have h_nat_sq_beta : ∀ x : Fin (s + 1),
      6 * ((↑(m.β x.rev) : ℂ) * (((x : ℕ) : ℂ) * (((x : ℕ) - 1 : ℕ) : ℂ))) =
      (↑(m.β x.rev) : ℂ) * (6 * ((x : ℕ) : ℂ) ^ 2 - 6 * ((x : ℕ) : ℂ)) := by
    intro x
    rcases Nat.lt_or_ge (x : ℕ) 1 with hlt | hge
    · simp [Nat.lt_one_iff.mp hlt]
    · push_cast [Nat.cast_sub hge]
      ring
  -- Step 4: Combine sums using per-element identities
  have h_combined_α :
      2 * (∑ x : Fin (s + 1), (↑(m.α x.rev) : ℂ) * (((x : ℕ) : ℂ) * ((((x : ℕ) - 1 : ℕ) : ℂ) * (((x : ℕ) - 1 - 1 : ℕ) : ℂ)))) +
      3 * (∑ x : Fin (s + 1), (↑(m.α x.rev) : ℂ) * (((x : ℕ) : ℂ) * (((x : ℕ) - 1 : ℕ) : ℂ))) -
      (∑ x : Fin (s + 1), (↑(m.α x.rev) : ℂ) * ((x : ℕ) : ℂ)) =
      ∑ x : Fin (s + 1), (↑(m.α x.rev) : ℂ) * (2 * ((x : ℕ) : ℂ) ^ 3 - 3 * ((x : ℕ) : ℂ) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun x _ => h_nat_cube x)
  have h_combined_β :
      6 * (∑ x : Fin (s + 1), (↑(m.β x.rev) : ℂ) * (((x : ℕ) : ℂ) * (((x : ℕ) - 1 : ℕ) : ℂ))) =
      ∑ x : Fin (s + 1), (↑(m.β x.rev) : ℂ) * (6 * ((x : ℕ) : ℂ) ^ 2 - 6 * ((x : ℕ) : ℂ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => h_nat_sq_beta x)
  -- Step 5: Suffices with combined form
  suffices hsuff :
      (∑ x : Fin (s + 1), (↑(m.α x.rev) : ℂ) * (2 * ((x : ℕ) : ℂ) ^ 3 - 3 * ((x : ℕ) : ℂ) ^ 2)) +
      (∑ x : Fin (s + 1), (↑(m.β x.rev) : ℂ) * (6 * ((x : ℕ) : ℂ) ^ 2 - 6 * ((x : ℕ) : ℂ))) = 0 by
    linear_combination h_combined_β + h_combined_α + hsuff
  -- Step 6: Reindex both sums via Fin.revPerm
  rw [Fintype.sum_equiv Fin.revPerm
    (fun x => (↑(m.α x.rev) : ℂ) * (2 * ((x : ℕ) : ℂ) ^ 3 - 3 * ((x : ℕ) : ℂ) ^ 2))
    (fun k => (↑(m.α k) : ℂ) * (2 * ((Fin.rev k : ℕ) : ℂ) ^ 3 - 3 * ((Fin.rev k : ℕ) : ℂ) ^ 2))
    (fun k => by simp [Fin.revPerm_apply, Fin.rev_rev])]
  rw [Fintype.sum_equiv Fin.revPerm
    (fun x => (↑(m.β x.rev) : ℂ) * (6 * ((x : ℕ) : ℂ) ^ 2 - 6 * ((x : ℕ) : ℂ)))
    (fun k => (↑(m.β k) : ℂ) * (6 * ((Fin.rev k : ℕ) : ℂ) ^ 2 - 6 * ((Fin.rev k : ℕ) : ℂ)))
    (fun k => by simp [Fin.revPerm_apply, Fin.rev_rev])]
  -- Step 7: Use rev(k) = s - k (same as C₂)
  have hrev_add : ∀ k : Fin (s + 1),
      ((Fin.rev k : ℕ) : ℂ) + ((k : ℕ) : ℂ) = (s : ℂ) := fun k => by
    rw [← Nat.cast_add]; congr 1; simp [Fin.val_rev]; omega
  have hrev_eq : ∀ k : Fin (s + 1),
      ((Fin.rev k : ℕ) : ℂ) = (s : ℂ) - ((k : ℕ) : ℂ) := fun k => by
    have := hrev_add k; linear_combination this
  simp_rw [hrev_eq]
  -- Step 8: Expand (s-k)^3 and (s-k)^2 per element, distributing αₖ and βₖ
  have h_α_exp : ∀ k : Fin (s + 1),
      (↑(m.α k) : ℂ) * (2 * ((↑s : ℂ) - ((k : ℕ) : ℂ)) ^ 3 - 3 * ((↑s : ℂ) - ((k : ℕ) : ℂ)) ^ 2) =
      (2 * (↑s : ℂ) ^ 3 - 3 * (↑s : ℂ) ^ 2) * (↑(m.α k) : ℂ) +
      (-(6 * (↑s : ℂ) ^ 2 - 6 * (↑s : ℂ))) * (((k : ℕ) : ℂ) * (↑(m.α k) : ℂ)) +
      (6 * (↑s : ℂ) - 3) * (((k : ℕ) : ℂ) ^ 2 * (↑(m.α k) : ℂ)) +
      (-2) * (((k : ℕ) : ℂ) ^ 3 * (↑(m.α k) : ℂ)) := fun k => by ring
  have h_β_exp : ∀ k : Fin (s + 1),
      (↑(m.β k) : ℂ) * (6 * ((↑s : ℂ) - ((k : ℕ) : ℂ)) ^ 2 - 6 * ((↑s : ℂ) - ((k : ℕ) : ℂ))) =
      (6 * (↑s : ℂ) ^ 2 - 6 * (↑s : ℂ)) * (↑(m.β k) : ℂ) +
      (-(12 * (↑s : ℂ) - 6)) * (((k : ℕ) : ℂ) * (↑(m.β k) : ℂ)) +
      6 * (((k : ℕ) : ℂ) ^ 2 * (↑(m.β k) : ℂ)) := fun k => by ring
  simp_rw [h_α_exp, h_β_exp]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  -- Step 9: Get order conditions
  have hcons := hp.isConsistent (by omega)
  have hC₀ : (∑ k : Fin (s + 1), (↑(m.α k) : ℂ)) = 0 := by
    have h := hcons.rhoC_one m; simp only [rhoC, one_pow, mul_one] at h; exact h
  have hC₁ : (∑ k : Fin (s + 1), ((k : ℕ) : ℂ) * (↑(m.α k) : ℂ)) =
      (∑ k : Fin (s + 1), (↑(m.β k) : ℂ)) := by
    have h := hcons.sigmaC_one_eq_rhoCDeriv_one m
    simp only [sigmaC, rhoCDeriv, one_pow, mul_one] at h; exact h.symm
  have hV₂ : (m.orderCondVal 2 : ℂ) = 0 := by
    rw [hp.conditions_hold 2 (by omega)]; simp
  simp only [orderCondVal] at hV₂
  push_cast at hV₂
  simp only [pow_one] at hV₂
  have hV₃ : (m.orderCondVal 3 : ℂ) = 0 := by
    rw [hp.conditions_hold 3 hp3]; simp
  simp only [orderCondVal] at hV₃
  push_cast at hV₃
  -- Step 10: Close with linear_combination
  linear_combination (2 * (↑s : ℂ) ^ 3 - 3 * (↑s : ℂ) ^ 2) * hC₀ -
    (6 * (↑s : ℂ) ^ 2 - 6 * (↑s : ℂ)) * hC₁ +
    (6 * (↑s : ℂ) - 3) * hV₂ - 2 * hV₃

/-- **HasDerivAt for the Dahlquist G̃ function at w = 1.**
The function G̃(w) = σ̃(w)/ρ̃(w) - (w+1)/(2(1-w)), with removable singularity at w=1
filled in as 0, has derivative 1/12 at w = 1.

Proof sketch: The combined fraction P(w)/D(w) where
  P(w) = 2σ̃(w)(w-1) + ρ̃(w)(w+1)    (numerator, triple zero at 1)
  D(w) = 2ρ̃(w)(w-1)                  (denominator, double zero at 1)
gives G̃(w) = P(w)/D(w). From order conditions C₁, C₂, C₃:
  P'''(1) = -σ(1) = -ρ'(1),  D''(1) = -4ρ'(1).
So the derivative is P'''(1)/(3·D''(1)) = (-ρ'(1))/(3·(-4ρ'(1))) = 1/12. -/
theorem hasDerivAt_Gtilde_one (m : LMM s) (p : ℕ) (hp : m.HasOrder p) (hp3 : 3 ≤ p)
    (ha : m.IsAStable) (hρ_simple : m.rhoCDeriv 1 ≠ 0) :
    HasDerivAt (fun w : ℂ => if w = 1 then (0 : ℂ) else
      m.sigmaCRev w / m.rhoCRev w - (w + 1) / (2 * (1 - w))) (1/12 : ℂ) 1 := by
  let ρrevPoly : Polynomial ℂ := ∑ j : Fin (s + 1),
    Polynomial.C (↑(m.α (Fin.rev j)) : ℂ) * Polynomial.X ^ (j : ℕ)
  let σrevPoly : Polynomial ℂ := ∑ j : Fin (s + 1),
    Polynomial.C (↑(m.β (Fin.rev j)) : ℂ) * Polynomial.X ^ (j : ℕ)
  have hρrev_eval : ∀ w : ℂ, ρrevPoly.eval w = m.rhoCRev w := by
    intro w
    simp [ρrevPoly, LMM.rhoCRev, Polynomial.eval_finset_sum]
  have hσrev_eval : ∀ w : ℂ, σrevPoly.eval w = m.sigmaCRev w := by
    intro w
    simp [σrevPoly, LMM.sigmaCRev, Polynomial.eval_finset_sum]
  have hcons : m.IsConsistent := hp.isConsistent (by omega)
  have hρ_root : ρrevPoly.IsRoot 1 := by
    rw [Polynomial.IsRoot, hρrev_eval, rhoCRev_one_eq_zero m hcons]
  let Rpoly : Polynomial ℂ := ρrevPoly /ₘ (Polynomial.X - Polynomial.C 1)
  have hρ_factor : ρrevPoly = (Polynomial.X - Polynomial.C 1) * Rpoly := by
    simpa [Rpoly] using (Polynomial.mul_divByMonic_eq_iff_isRoot (p := ρrevPoly) (a := 1)).2 hρ_root |>.symm
  have hR_eval_one_ne : Rpoly.eval 1 ≠ 0 := by
    -- ρ̃'(1) = R(1) from the factored form, and ρ̃'(1) = -ρ'(1) ≠ 0
    have hderiv_eq : ρrevPoly.derivative.eval 1 = Rpoly.eval 1 := by
      conv_lhs => rw [hρ_factor, Polynomial.derivative_mul]
      simp [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
    rw [← hderiv_eq, rhoCRev_poly_derivative_eval_one m hcons]
    exact neg_ne_zero.mpr hρ_simple
  let Ppoly : Polynomial ℂ :=
    (2 : ℂ) • σrevPoly * (Polynomial.X - Polynomial.C 1) +
      ρrevPoly * (Polynomial.X + Polynomial.C 1)
  -- Prove (X - 1)³ | Ppoly by factoring out (X-1) three times
  -- using the order conditions C₀, C₁, C₂.
  let X1 : Polynomial ℂ := Polynomial.X - Polynomial.C (1 : ℂ)
  -- Step 1: Ppoly = (X-1) * Q₁ where Q₁ = 2•σ̃ + R*(X+1)
  have hPpoly_eq : Ppoly = X1 * ((2 : ℂ) • σrevPoly + Rpoly * (Polynomial.X + Polynomial.C 1)) := by
    show (2 : ℂ) • σrevPoly * (Polynomial.X - Polynomial.C 1) +
      ρrevPoly * (Polynomial.X + Polynomial.C 1) =
      X1 * ((2 : ℂ) • σrevPoly + Rpoly * (Polynomial.X + Polynomial.C 1))
    rw [hρ_factor]; ring
  set Q₁ := (2 : ℂ) • σrevPoly + Rpoly * (Polynomial.X + Polynomial.C 1) with hQ₁_def
  -- Rpoly.eval 1 = -ρ'(1) (needed for both Q₁ and Q₂ steps)
  have hR_val : Rpoly.eval 1 = -m.rhoCDeriv 1 := by
    have hderiv_eq : ρrevPoly.derivative.eval 1 = Rpoly.eval 1 := by
      conv_lhs => rw [hρ_factor, Polynomial.derivative_mul]
      simp [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
    rw [← hderiv_eq]; exact rhoCRev_poly_derivative_eval_one m hcons
  -- Step 2: Q₁ has root at 1 (from C₁: σ(1) = ρ'(1))
  have hQ₁_root : Q₁.IsRoot 1 := by
    rw [Polynomial.IsRoot]
    simp only [Q₁, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_smul,
      Polynomial.eval_X, Polynomial.eval_C, smul_eq_mul]
    rw [hσrev_eval, sigmaCRev_one, hcons.sigmaC_one_eq_rhoCDeriv_one m, hR_val]
    ring
  -- Step 3: (X-1) | Q₁
  obtain ⟨Q₂, hQ₂⟩ := (Polynomial.dvd_iff_isRoot.mpr hQ₁_root : X1 ∣ Q₁)
  -- Step 4: Q₂ has root at 1 (from C₂)
  -- By derivative-at-root: Q₁'(1) = Q₂(1), and Q₁'(1) = 0 using the C₂ condition.
  have hQ₂_root : Q₂.IsRoot 1 := by
    -- Derivative-at-root: Q₁ = (X-1) * Q₂ → Q₁'(1) = Q₂(1)
    have hQ₂_eq_deriv : Q₁.derivative.eval 1 = Q₂.eval 1 := by
      conv_lhs => rw [hQ₂, Polynomial.derivative_mul]
      simp [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
    rw [Polynomial.IsRoot, ← hQ₂_eq_deriv]
    -- Q₁'(1) = 2σ̃'(1) + 2R'(1) + R(1) = 2σ̃'(1) + ρ̃''(1) + ρ̃'(1) = 0 by C₂
    have hC2 := reversed_poly_C2_condition m hp (by omega : 2 ≤ p)
    have hR_eq : Rpoly.eval 1 = ρrevPoly.derivative.eval 1 := by
      conv_rhs => rw [hρ_factor, Polynomial.derivative_mul]
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.derivative_sub, Polynomial.derivative_X]
    have hR'_eq : 2 * Rpoly.derivative.eval 1 = ρrevPoly.derivative.derivative.eval 1 := by
      conv_rhs => rw [hρ_factor]
      simp [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_sub,
        Polynomial.derivative_X,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_one]
      ring
    have hQ1_expand : Q₁.derivative.eval 1 =
        2 * σrevPoly.derivative.eval 1 + 2 * Rpoly.derivative.eval 1 + Rpoly.eval 1 := by
      rw [hQ₁_def]
      simp [Polynomial.derivative_add, Polynomial.derivative_mul,
        Polynomial.derivative_X,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_smul,
        Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
      ring
    rw [hQ1_expand, hR'_eq, hR_eq]
    exact hC2
  -- Step 5: (X-1) | Q₂
  obtain ⟨Q₃, hQ₃⟩ := (Polynomial.dvd_iff_isRoot.mpr hQ₂_root : X1 ∣ Q₂)
  -- Step 6: Combine (X-1)³ | Ppoly
  have hP_dvd : X1 ^ 3 ∣ Ppoly :=
    ⟨Q₃, by rw [hPpoly_eq, hQ₂, hQ₃]; ring⟩
  let Qpoly : Polynomial ℂ := Ppoly /ₘ (X1 ^ 3)
  have hP_factor : Ppoly = (Polynomial.X - Polynomial.C 1) ^ 3 * Qpoly := by
    have hmonic : Polynomial.Monic (X1 ^ 3) := by
      simpa [X1] using (Polynomial.monic_X_sub_C (1 : ℂ)).pow 3
    have hmod : Ppoly %ₘ (X1 ^ 3) = (0 : Polynomial ℂ) :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).2 hP_dvd
    rw [show (Polynomial.X - Polynomial.C 1) ^ 3 = X1 ^ 3 from by simp [X1]]
    rw [← Polynomial.modByMonic_add_div Ppoly hmonic, hmod, zero_add]
  let GtCancelled : ℂ → ℂ := fun w =>
    (w - 1) * Qpoly.eval w / (2 * Rpoly.eval w)
  have hGtCancelled : HasDerivAt GtCancelled (1 / 12 : ℂ) 1 := by
    let n : ℂ → ℂ := fun w => (w - 1) * Qpoly.eval w
    let d : ℂ → ℂ := fun w => 2 * Rpoly.eval w
    have hn : HasDerivAt n (Qpoly.eval 1) 1 := by
      dsimp [n]
      simpa using
        ((hasDerivAt_id (𝕜 := ℂ) 1).sub (hasDerivAt_const 1 (1 : ℂ))).mul
          (Polynomial.hasDerivAt Qpoly 1)
    have hd : HasDerivAt d (2 * Rpoly.derivative.eval 1) 1 := by
      dsimp [d]
      simpa using ((hasDerivAt_const 1 (2 : ℂ)).mul (Polynomial.hasDerivAt Rpoly 1))
    have hd_ne : d 1 ≠ 0 := by
      dsimp [d]
      exact mul_ne_zero two_ne_zero hR_eval_one_ne
    have hdiv : HasDerivAt GtCancelled (Qpoly.eval 1 / (2 * Rpoly.eval 1)) 1 :=
      (hn.div hd hd_ne).congr_deriv (by dsimp [n, d]; simp [sub_self]; field_simp [mul_ne_zero two_ne_zero hR_eval_one_ne])
    have hQpoly_eq_Q₃ : Qpoly = Q₃ := by
      have hX1pow : Ppoly = X1 ^ 3 * Q₃ := by
        rw [hPpoly_eq, hQ₂, hQ₃]
        ring
      have hmonic : Polynomial.Monic (X1 ^ 3) := by
        simpa [X1] using (Polynomial.monic_X_sub_C (1 : ℂ)).pow 3
      change Ppoly /ₘ (X1 ^ 3) = Q₃
      rw [hX1pow, Polynomial.mul_divByMonic_cancel_left _ hmonic]
    have hQ₃_val : Q₃.eval 1 = Q₂.derivative.eval 1 := by
      have hderiv := congrArg Polynomial.derivative hQ₃
      have heval := congrArg (Polynomial.eval (1 : ℂ)) hderiv
      simp [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heval
      simpa [mul_comm, mul_left_comm, mul_assoc] using heval.symm
    have hQ₂'_val : Q₂.derivative.eval 1 = Q₁.derivative.derivative.eval 1 / 2 := by
      have hderiv := congrArg (fun p : Polynomial ℂ => p.derivative.derivative.eval (1 : ℂ)) hQ₂
      simp [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hderiv
      apply (eq_div_iff two_ne_zero).2
      simpa [two_mul, mul_comm, add_comm, add_left_comm, add_assoc] using hderiv.symm
    have hQ₁pp : Q₁.derivative.derivative.eval 1 = -m.rhoCDeriv 1 / 3 := by
      have hC3 := reversed_poly_C3_condition m hp hp3
      have hR_eq : Rpoly.eval 1 = ρrevPoly.derivative.eval 1 := by
        conv_rhs => rw [hρ_factor, Polynomial.derivative_mul]
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_one,
          Polynomial.derivative_sub, Polynomial.derivative_X]
      have hR'_eq : 2 * Rpoly.derivative.eval 1 = ρrevPoly.derivative.derivative.eval 1 := by
        conv_rhs => rw [hρ_factor]
        simp [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_sub,
          Polynomial.derivative_X,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_one]
        ring
      have hR''_eq : 3 * Rpoly.derivative.derivative.eval 1 =
          ρrevPoly.derivative.derivative.derivative.eval 1 := by
        conv_rhs => rw [hρ_factor]
        simp [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_sub,
          Polynomial.derivative_X,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_one]
        ring
      have hQ₁pp_expand :
          3 * Q₁.derivative.derivative.eval 1 =
            6 * σrevPoly.derivative.derivative.eval 1 +
              6 * Rpoly.derivative.derivative.eval 1 +
              6 * Rpoly.derivative.eval 1 := by
        rw [hQ₁_def]
        simp [Polynomial.derivative_add, Polynomial.derivative_mul,
          Polynomial.derivative_X,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_smul,
          Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
        ring
      have hmain : 3 * Q₁.derivative.derivative.eval 1 = -m.rhoCDeriv 1 := by
        have hQ₁pp_expand' :
            3 * Q₁.derivative.derivative.eval 1 =
              6 * σrevPoly.derivative.derivative.eval 1 +
                2 * ρrevPoly.derivative.derivative.derivative.eval 1 +
                3 * ρrevPoly.derivative.derivative.eval 1 := by
          have hR''_eq' : 6 * Rpoly.derivative.derivative.eval 1 =
              2 * ρrevPoly.derivative.derivative.derivative.eval 1 := by
            linear_combination (2 : ℂ) * hR''_eq
          have hR'_eq' : 6 * Rpoly.derivative.eval 1 =
              3 * ρrevPoly.derivative.derivative.eval 1 := by
            linear_combination (3 : ℂ) * hR'_eq
          rw [hQ₁pp_expand, hR''_eq', hR'_eq']
        calc
          3 * Q₁.derivative.derivative.eval 1
              = 6 * σrevPoly.derivative.derivative.eval 1 +
                  2 * ρrevPoly.derivative.derivative.derivative.eval 1 +
                  3 * ρrevPoly.derivative.derivative.eval 1 := hQ₁pp_expand'
          _ = ρrevPoly.derivative.eval 1 := by
            linear_combination hC3
          _ = -m.rhoCDeriv 1 := rhoCRev_poly_derivative_eval_one m hcons
      apply (eq_div_iff (by norm_num : (3 : ℂ) ≠ 0)).2
      simpa [mul_comm] using hmain
    have hscalar : Qpoly.eval 1 / (2 * Rpoly.eval 1) = (1 / 12 : ℂ) := by
      rw [hQpoly_eq_Q₃, hQ₃_val, hQ₂'_val, hQ₁pp, hR_val]
      field_simp [hρ_simple]
      ring
    exact hdiv.congr_deriv hscalar
  have hGt_eventually :
      (fun w : ℂ => if w = 1 then (0 : ℂ) else
        m.sigmaCRev w / m.rhoCRev w - (w + 1) / (2 * (1 - w))) =ᶠ[nhds 1] GtCancelled := by
    -- Rpoly.eval is continuous and nonzero at 1, so nonzero in a neighborhood
    have hR_ev : ∀ᶠ w in nhds (1 : ℂ), Rpoly.eval w ≠ 0 :=
      (Polynomial.continuousAt Rpoly).eventually_ne hR_eval_one_ne
    apply hR_ev.mono
    intro w hRw
    simp only [GtCancelled]
    by_cases hw : w = 1
    · -- At w = 1: LHS = 0 (by if), RHS = (1-1)*Q(1)/(2*R(1)) = 0
      subst hw; simp
    · -- At w ≠ 1: algebraic identity
      simp only [if_neg hw]
      -- From hρ_factor: ρrevPoly.eval w = (w - 1) * Rpoly.eval w
      have hρ_eval : m.rhoCRev w = (w - 1) * Rpoly.eval w := by
        rw [← hρrev_eval]
        have := congr_arg (Polynomial.eval w) hρ_factor
        simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
              Polynomial.eval_C] at this
        exact this
      -- From hP_factor: Ppoly.eval w = (w - 1)^3 * Qpoly.eval w
      have hP_eval : (Polynomial.eval w Ppoly) = (w - 1) ^ 3 * Qpoly.eval w := by
        have := congr_arg (Polynomial.eval w) hP_factor
        simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
              Polynomial.eval_X, Polynomial.eval_C] at this
        exact this
      -- Ppoly definition evaluated: Ppoly.eval w = 2 * σ̃(w) * (w-1) + ρ̃(w) * (w+1)
      have hP_def : (Polynomial.eval w Ppoly) =
          2 * m.sigmaCRev w * (w - 1) + m.rhoCRev w * (w + 1) := by
        change Polynomial.eval w ((2 : ℂ) • σrevPoly * (Polynomial.X - Polynomial.C 1) +
          ρrevPoly * (Polynomial.X + Polynomial.C 1)) = _
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_smul,
              Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
              hρrev_eval, hσrev_eval]
        ring
      -- Key: w - 1 ≠ 0
      have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw
      -- Dividing by (w-1): 2*σ̃(w) + R(w)*(w+1) = (w-1)^2 * Q(w)
      have h_key : 2 * m.sigmaCRev w + Rpoly.eval w * (w + 1) =
          (w - 1) ^ 2 * Qpoly.eval w := by
        have h_combined : (w - 1) ^ 3 * Qpoly.eval w =
            2 * m.sigmaCRev w * (w - 1) + (w - 1) * Rpoly.eval w * (w + 1) := by
          rw [← hρ_eval, ← hP_def, hP_eval]
        have h2 : (w - 1) * ((w - 1) ^ 2 * Qpoly.eval w) =
            (w - 1) * (2 * m.sigmaCRev w + Rpoly.eval w * (w + 1)) := by
          linear_combination h_combined
        exact (mul_left_cancel₀ hw1 h2).symm
      -- Now prove the algebraic identity
      rw [hρ_eval]
      have h1w : (1 : ℂ) - w ≠ 0 := by rwa [sub_ne_zero, ne_comm]
      field_simp [hw1, hRw, h1w]
      linear_combination (1 - w) * h_key
  exact hGtCancelled.congr_of_eventuallyEq hGt_eventually

/-- Helper: `rhoCRev w ≠ 0` for `‖w‖ ≤ 1` with `w ≠ 1`, given that the only
unit-circle root of `rhoC` is `1`. Combines the interior case (A-stability) with the
boundary case (`h_unit`). -/
theorem rhoCRev_ne_zero_of_closedBall_ne_one (m : LMM s) (ha : m.IsAStable)
    (h_unit : ∀ ζ : ℂ, m.rhoC ζ = 0 → ‖ζ‖ = 1 → ζ = 1)
    (w : ℂ) (hw : ‖w‖ ≤ 1) (hw1 : w ≠ 1) : m.rhoCRev w ≠ 0 := by
  by_cases hw2 : w = 0
  · simp +decide [hw2, LMM.rhoCRev]
    simp +decide [Fin.sum_univ_succ, m.normalized]
  · by_cases hw3 : ‖w‖ = 1
    · contrapose! h_unit
      refine' ⟨w⁻¹, _, _, _⟩ <;> simp_all +decide [LMM.rhoCRev_eq]
    · exact rhoCRev_ne_zero_of_norm_lt_one m ha w (lt_of_le_of_ne hw hw3)

/-- **ContinuousOn for the Dahlquist G̃ function on the closed unit disk.**
The function G̃ is continuous on `closure (Metric.ball 0 1)`. The key difficulty is
continuity at w = 1 (removable singularity), which follows from the triple zero of
the combined numerator and double zero of the denominator at w = 1.

The hypothesis `h_unit` asserts that every unit-circle root of `rhoC` equals `1`.
This is needed to ensure `rhoCRev` is nonvanishing on the boundary circle away
from `w = 1`, so that the quotient `σ̃/ρ̃` remains continuous there. -/
theorem continuousOn_Gtilde_closedBall (m : LMM s) (p : ℕ) (hp : m.HasOrder p)
    (hp3 : 3 ≤ p) (ha : m.IsAStable) (hρ_simple : m.rhoCDeriv 1 ≠ 0)
    (h_unit : ∀ ζ : ℂ, m.rhoC ζ = 0 → ‖ζ‖ = 1 → ζ = 1) :
    ContinuousOn (fun w : ℂ => if w = 1 then (0 : ℂ) else
      m.sigmaCRev w / m.rhoCRev w - (w + 1) / (2 * (1 - w)))
      (closure (Metric.ball 0 1)) := by
  refine' continuousOn_iff_continuous_restrict.mpr _
  refine' continuous_iff_continuousAt.mpr _
  intro x
  by_cases hx : x.val = 1
  · have h_cont_at_1 : ContinuousAt (fun w : ℂ => if w = 1 then (0 : ℂ) else
        m.sigmaCRev w / m.rhoCRev w - (w + 1) / (2 * (1 - w))) 1 := by
      convert hasDerivAt_Gtilde_one m p hp hp3 ha hρ_simple |> HasDerivAt.continuousAt using 1
    rw [ContinuousAt] at *
    convert h_cont_at_1.comp (show Filter.Tendsto
        (fun w : ↑(closure (Metric.ball 0 1)) => (w : ℂ)) (nhds x) (nhds 1) from ?_) using 2
    · aesop
    · exact Continuous.tendsto' (by continuity) _ _ hx
  · -- At x.val ≠ 1: the if-then-else is locally equal to the formula
    apply ContinuousAt.congr
    · show ContinuousAt (fun w : ↑(closure (Metric.ball (0:ℂ) 1)) =>
          m.sigmaCRev w.val / m.rhoCRev w.val - (w.val + 1) / (2 * (1 - w.val))) x
      apply ContinuousAt.sub
      · apply ContinuousAt.div
        · exact (m.sigmaCRev_differentiable.continuous.comp continuous_subtype_val).continuousAt
        · exact (m.rhoCRev_differentiable.continuous.comp continuous_subtype_val).continuousAt
        · exact rhoCRev_ne_zero_of_closedBall_ne_one m ha h_unit x.val
            (closure_minimal (fun x hx => by simpa using hx.out.le)
              (isClosed_le continuous_norm continuous_const) x.2) hx
      · apply ContinuousAt.div
        · exact (continuous_subtype_val.add continuous_const).continuousAt
        · exact (continuous_const.mul
            (continuous_const.sub continuous_subtype_val)).continuousAt
        · exact mul_ne_zero two_ne_zero (sub_ne_zero_of_ne (Ne.symm hx))
    · filter_upwards [IsOpen.mem_nhds
          (isOpen_compl_singleton.preimage continuous_subtype_val) hx] with w hw
      exact (if_neg (by simpa using hw)).symm

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
    -- The only unit-circle root of ρ is 1 (needed for boundary continuity of G̃):
    (h_unit : ∀ ζ : ℂ, m.rhoC ζ = 0 → ‖ζ‖ = 1 → ζ = 1)
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
    refine DiffContOnCl.mk ?_ ?_
    · -- DifferentiableOn ℂ Gt (Metric.ball 0 1)
      -- On ball(0,1), w ≠ 1 (since ‖1‖ = 1), so Gt = σ̃/ρ̃ - (w+1)/(2(1-w)).
      -- ρ̃(w) ≠ 0 for |w| < 1 (A-stability), 1-w ≠ 0 (w ≠ 1), so Gt is differentiable.
      have h1_not_mem : (1:ℂ) ∉ Metric.ball (0:ℂ) 1 := by
        simp [Metric.mem_ball, dist_zero_right]
      have hGt_eq : Set.EqOn Gt (fun w => σ_rev w / ρ_rev w - (w + 1) / (2 * (1 - w)))
          (Metric.ball 0 1) := by
        intro w hw; exact if_neg (ne_of_mem_of_not_mem hw h1_not_mem)
      have h_σ_diff : Differentiable ℂ σ_rev := by
        intro w; show DifferentiableAt ℂ
          (fun w => ∑ j : Fin (s + 1), (↑(m.β (Fin.rev j)) : ℂ) * w ^ (↑j : ℕ)) w; fun_prop
      have h_ρ_diff : Differentiable ℂ ρ_rev := by
        intro w; show DifferentiableAt ℂ
          (fun w => ∑ j : Fin (s + 1), (↑(m.α (Fin.rev j)) : ℂ) * w ^ (↑j : ℕ)) w; fun_prop
      have h_ρ_ne : ∀ w ∈ Metric.ball (0:ℂ) 1, ρ_rev w ≠ 0 := by
        intro w hw
        rw [Metric.mem_ball, dist_zero_right] at hw
        exact rhoCRev_ne_zero_of_norm_lt_one m ha w hw
      refine DifferentiableOn.congr ?_ hGt_eq
      apply DifferentiableOn.sub
      · exact DifferentiableOn.div h_σ_diff.differentiableOn h_ρ_diff.differentiableOn h_ρ_ne
      · apply DifferentiableOn.div
        · exact (differentiable_id.add (differentiable_const 1)).differentiableOn
        · exact ((differentiable_const 2).mul
            (differentiable_const 1 |>.sub differentiable_id)).differentiableOn
        · intro w hw
          have hw1 : w ≠ 1 := ne_of_mem_of_not_mem hw h1_not_mem
          exact mul_ne_zero two_ne_zero (sub_ne_zero.mpr (Ne.symm hw1))
    · -- ContinuousOn Gt (closure (Metric.ball 0 1))
      exact continuousOn_Gtilde_closedBall m p hp hp3 ha hρ_simple h_unit
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
    exact hasDerivAt_Gtilde_one m p hp hp3 ha hρ_simple

/-- For a zero-stable, A-stable LMM of order ≥ 3 whose only unit-circle
root of ρ is 1, derive `False`.
Combines `E_nonneg_re`, `re_inv_exp_sub_one`, and the zero-stability condition
(simple root of ρ at ζ = 1) to invoke `order_ge_three_not_aStable_core`.
Reference: Iserles, proof of Theorem 3.4.

The hypothesis `h_unit` (∀ ζ, ρ(ζ) = 0 → |ζ| = 1 → ζ = 1) excludes
parasitic common roots of ρ and σ on the unit circle other than 1.
This is satisfied by all standard methods (BDF, Adams, trapezoidal, etc.). -/
theorem order_ge_three_not_aStable (m : LMM s) (p : ℕ) (hp : m.HasOrder p) (hp3 : 3 ≤ p)
    (ha : m.IsAStable) (hzs : m.IsZeroStable)
    (h_unit : ∀ ζ : ℂ, m.rhoC ζ = 0 → ‖ζ‖ = 1 → ζ = 1) : False := by
  have hcons := hp.isConsistent (by omega)
  have hρ1 : m.rhoC 1 = 0 := hcons.rhoC_one m
  exact order_ge_three_not_aStable_core m p hp hp3 ha
    (hzs.unit_roots_simple 1 hρ1 (by simp))
    h_unit
    (fun θ hρ hσ => IsAStable.E_nonneg_re m ha θ hρ hσ)
    (fun θ hne => re_inv_exp_sub_one θ hne)

/-- **Dahlquist's Second Barrier** (Iserles, Theorem 3.4):
An A-stable, zero-stable linear multistep method whose only unit-circle root
of ρ is 1 has order at most 2.

NOTE: Zero-stability is necessary. See `dahlquistCounterexample` for a method
that is A-stable with order 3 but not zero-stable (ρ has a double root at ζ = 1).
The standard textbook statement "A-stable ⟹ order ≤ 2" implicitly assumes
zero-stability (which is needed for convergence anyway).

The hypothesis `h_unit` rules out parasitic common roots of ρ and σ on the
unit circle away from 1; it is satisfied by all standard methods. -/
theorem dahlquist_second_barrier {s : ℕ} (m : LMM s) (p : ℕ)
    (hp : m.HasOrder p) (ha : m.IsAStable) (hzs : m.IsZeroStable)
    (h_unit : ∀ ζ : ℂ, m.rhoC ζ = 0 → ‖ζ‖ = 1 → ζ = 1) : p ≤ 2 := by
  by_contra h
  push_neg at h
  exact order_ge_three_not_aStable m p hp h ha hzs h_unit

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
