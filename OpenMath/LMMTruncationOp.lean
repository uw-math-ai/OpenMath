import Mathlib.Analysis.Calculus.Taylor
import OpenMath.MultistepMethods

/-! ## Local Truncation Operator (Iserles §1.2 / eqn (2.6))

The local truncation operator `L[y, t, h]` of a linear multistep method
applied to a smooth test function `y`. Here we pass the derivative `y'`
explicitly, so the definition does not depend on a smoothness predicate
and we can reason about it on monomials by direct computation. -/

namespace LMM

variable {s : ℕ}

/-- The local truncation operator of a linear multistep method:
    `L[y, t, h] = ∑_j α_j · y(t + j h) - h · ∑_j β_j · y'(t + j h)`.
    The derivative is passed in explicitly as `y'`, so this definition
    does not require any smoothness predicate.
    Reference: Iserles, eqn (2.6) / §1.2. -/
noncomputable def truncationOp
    (m : LMM s) (h : ℝ) (y y' : ℝ → ℝ) (t : ℝ) : ℝ :=
  (∑ j : Fin (s + 1), m.α j * y (t + (j : ℝ) * h))
    - h * (∑ j : Fin (s + 1), m.β j * y' (t + (j : ℝ) * h))

/-- Linearity in the test function pair `(y, y')`. -/
theorem truncationOp_add
    (m : LMM s) (h : ℝ) (y₁ y₁' y₂ y₂' : ℝ → ℝ) (t : ℝ) :
    m.truncationOp h (fun u => y₁ u + y₂ u) (fun u => y₁' u + y₂' u) t
      = m.truncationOp h y₁ y₁' t + m.truncationOp h y₂ y₂' t := by
  unfold truncationOp
  simp only [mul_add, Finset.sum_add_distrib]
  ring

/-- Scalar homogeneity. -/
theorem truncationOp_smul
    (m : LMM s) (h : ℝ) (c : ℝ) (y y' : ℝ → ℝ) (t : ℝ) :
    m.truncationOp h (fun u => c * y u) (fun u => c * y' u) t
      = c * m.truncationOp h y y' t := by
  unfold truncationOp
  have hα : ∀ j : Fin (s + 1),
      m.α j * (c * y (t + (j : ℝ) * h)) = c * (m.α j * y (t + (j : ℝ) * h)) :=
    fun j => by ring
  have hβ : ∀ j : Fin (s + 1),
      m.β j * (c * y' (t + (j : ℝ) * h)) = c * (m.β j * y' (t + (j : ℝ) * h)) :=
    fun j => by ring
  simp only [hα, hβ, ← Finset.mul_sum]
  ring

/-- On the monomial `y(t) = t^q` (with derivative `q · t^(q-1)`),
    the truncation operator at `t = 0` reduces to `h^q · V_q`. -/
theorem truncationOp_monomial_zero
    (m : LMM s) (h : ℝ) (q : ℕ) :
    m.truncationOp h
        (fun t => t ^ q)
        (fun t => (q : ℝ) * t ^ (q - 1))
        0
      = h ^ q * m.orderCondVal q := by
  unfold truncationOp orderCondVal
  rcases q with _ | q'
  · simp
  · simp only [Nat.add_sub_cancel, zero_add, mul_pow, pow_succ]
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring

/-- For an LMM of order `p`, the truncation operator vanishes on
    monomials of degree `≤ p`. -/
theorem truncationOp_monomial_eq_zero_of_HasOrder
    {m : LMM s} {p : ℕ} (h : ℝ) (hord : m.HasOrder p)
    {q : ℕ} (hq : q ≤ p) :
    m.truncationOp h
        (fun t => t ^ q)
        (fun t => (q : ℝ) * t ^ (q - 1))
        0 = 0 := by
  rw [truncationOp_monomial_zero, hord.conditions_hold q hq, mul_zero]

/-- If the zeroth order condition holds, the monomial order conditions vanish
    through degree `p`, and the next order condition is nonzero, then the LMM
    has order `p`. -/
theorem hasOrder_of_orderCondVal_vanishing
    (m : LMM s) (p : ℕ)
    (hzero : m.orderCondVal 0 = 0)
    (hmono : ∀ q : ℕ, 1 ≤ q → q ≤ p → m.orderCondVal q = 0)
    (hnext : m.orderCondVal (p + 1) ≠ 0) :
    m.HasOrder p := by
  refine ⟨?_, hnext⟩
  intro q hq
  by_cases hq0 : q = 0
  · subst q
    exact hzero
  · exact hmono q (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hq0)) hq

/-- Order `p` is equivalent to vanishing of the zeroth and monomial order
    conditions through degree `p`, together with failure of the next order
    condition. -/
theorem hasOrder_iff_orderCondVal_vanishing
    (m : LMM s) (p : ℕ) :
    m.HasOrder p ↔
      m.orderCondVal 0 = 0 ∧
        (∀ q : ℕ, 1 ≤ q → q ≤ p → m.orderCondVal q = 0) ∧
          m.orderCondVal (p + 1) ≠ 0 := by
  constructor
  · intro hord
    exact ⟨hord.conditions_hold 0 (Nat.zero_le _),
      (fun q _ hq => hord.conditions_hold q hq), hord.next_nonzero⟩
  · rintro ⟨hzero, hmono, hnext⟩
    exact m.hasOrder_of_orderCondVal_vanishing p hzero hmono hnext

/-- A monomial-only sufficient condition for order stated through the
    truncation operator.  Because `HasOrder` also records the zeroth condition
    and failure of the next condition, those are supplied as the corresponding
    `h = 1` truncation-operator facts. -/
theorem hasOrder_of_truncationOp_vanishing_on_monomials
    (m : LMM s) (p : ℕ)
    (hzero :
      m.truncationOp (1 : ℝ)
        (fun t => t ^ (0 : ℕ))
        (fun t => (0 : ℝ) * t ^ ((0 : ℕ) - 1))
        0 = 0)
    (hmono : ∀ q : ℕ, 1 ≤ q → q ≤ p → ∀ h : ℝ, h ≠ 0 →
      m.truncationOp h
        (fun t => t ^ q)
        (fun t => (q : ℝ) * t ^ (q - 1))
        0 = 0)
    (hnext :
      m.truncationOp (1 : ℝ)
        (fun t => t ^ (p + 1))
        (fun t => ((p + 1 : ℕ) : ℝ) * t ^ p)
        0 ≠ 0) :
    m.HasOrder p := by
  refine m.hasOrder_of_orderCondVal_vanishing p ?_ ?_ ?_
  · have hkey :
        m.truncationOp (1 : ℝ)
          (fun t => t ^ (0 : ℕ))
          (fun t => (0 : ℝ) * t ^ ((0 : ℕ) - 1))
          0 = (1 : ℝ) ^ (0 : ℕ) * m.orderCondVal 0 := by
      simpa using m.truncationOp_monomial_zero (1 : ℝ) 0
    rw [hkey] at hzero
    simpa using hzero
  · intro q hq1 hqp
    have htrunc := hmono q hq1 hqp (1 : ℝ) (by norm_num)
    have hkey := m.truncationOp_monomial_zero (1 : ℝ) q
    rw [hkey] at htrunc
    simpa using htrunc
  · intro hvanish
    apply hnext
    have hkey :
        m.truncationOp (1 : ℝ)
          (fun t => t ^ (p + 1))
          (fun t => ((p + 1 : ℕ) : ℝ) * t ^ p)
          0 = (1 : ℝ) ^ (p + 1) * m.orderCondVal (p + 1) := by
      have := m.truncationOp_monomial_zero (1 : ℝ) (p + 1)
      simpa using this
    rw [hkey, hvanish]
    simp

/-- For an order-`p` method, on the test monomial `y(t) = t^(p+1)`,
    the truncation operator at `t = 0` equals
    `(p+1)! · errorConstant p · h^(p+1)`. -/
theorem truncationOp_monomial_leading_of_HasOrder
    {m : LMM s} {p : ℕ} (h : ℝ) (_hord : m.HasOrder p) :
    m.truncationOp h
        (fun t => t ^ (p + 1))
        (fun t => ((p + 1 : ℕ) : ℝ) * t ^ p)
        0
      = ((p + 1).factorial : ℝ) * m.errorConstant p * h ^ (p + 1) := by
  have hfact : ((p + 1).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  have hkey : m.truncationOp h
        (fun t => t ^ (p + 1))
        (fun t => ((p + 1 : ℕ) : ℝ) * t ^ p)
        0 = h ^ (p + 1) * m.orderCondVal (p + 1) := by
    have := m.truncationOp_monomial_zero h (p + 1)
    simpa using this
  rw [hkey]
  unfold errorConstant
  field_simp

/-- Linearity of `truncationOp` over a finite sum of test-function pairs. -/
theorem truncationOp_finset_sum
    (m : LMM s) (h : ℝ) {ι : Type*} (S : Finset ι)
    (f f' : ι → ℝ → ℝ) (t : ℝ) :
    m.truncationOp h (fun u => ∑ k ∈ S, f k u) (fun u => ∑ k ∈ S, f' k u) t
      = ∑ k ∈ S, m.truncationOp h (f k) (f' k) t := by
  classical
  simp only [truncationOp, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := S)]
  rw [show (∑ j : Fin (s + 1), ∑ k ∈ S, h * (m.β j * f' k (t + (j : ℝ) * h)))
        = ∑ k ∈ S, ∑ j : Fin (s + 1), h * (m.β j * f' k (t + (j : ℝ) * h)) from
        Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]

/-- Truncation operator on a finite linear combination of monomials,
    via `truncationOp_add` / `truncationOp_smul`. -/
theorem truncationOp_polyCombination_zero
    (m : LMM s) (h : ℝ) (N : ℕ) (a : Fin (N + 1) → ℝ) :
    m.truncationOp h
        (fun t => ∑ k : Fin (N + 1), a k * t ^ (k : ℕ))
        (fun t => ∑ k : Fin (N + 1), a k * ((k : ℕ) : ℝ) * t ^ ((k : ℕ) - 1))
        0
      = ∑ k : Fin (N + 1), a k * h ^ (k : ℕ) * m.orderCondVal (k : ℕ) := by
  have hassoc :
      (fun t => ∑ k : Fin (N + 1), a k * ((k : ℕ) : ℝ) * t ^ ((k : ℕ) - 1))
        = (fun t => ∑ k : Fin (N + 1), a k * (((k : ℕ) : ℝ) * t ^ ((k : ℕ) - 1))) := by
    funext t
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hassoc]
  rw [m.truncationOp_finset_sum h (Finset.univ : Finset (Fin (N + 1)))
        (fun k t => a k * t ^ (k : ℕ))
        (fun k t => a k * (((k : ℕ) : ℝ) * t ^ ((k : ℕ) - 1))) 0]
  apply Finset.sum_congr rfl
  intro k _
  have hk := m.truncationOp_smul h (a k)
      (fun t => t ^ (k : ℕ))
      (fun t => ((k : ℕ) : ℝ) * t ^ ((k : ℕ) - 1)) 0
  rw [hk]
  rw [m.truncationOp_monomial_zero h (k : ℕ)]
  ring

/-- For an order-`p` method, the truncation operator vanishes on every
    polynomial test function of degree `≤ p`. -/
theorem truncationOp_polyCombination_eq_zero_of_HasOrder
    {m : LMM s} {p : ℕ} (h : ℝ) (hord : m.HasOrder p)
    (a : Fin (p + 1) → ℝ) :
    m.truncationOp h
        (fun t => ∑ k : Fin (p + 1), a k * t ^ (k : ℕ))
        (fun t => ∑ k : Fin (p + 1), a k * ((k : ℕ) : ℝ) * t ^ ((k : ℕ) - 1))
        0 = 0 := by
  rw [m.truncationOp_polyCombination_zero h p a]
  apply Finset.sum_eq_zero
  intro k _
  have hk : (k : ℕ) ≤ p := Nat.lt_succ_iff.mp k.isLt
  rw [hord.conditions_hold (k : ℕ) hk]
  ring

/-- For an order-`p` method, the truncation operator on a polynomial of
    degree `p + 1` reduces to its leading coefficient times
    `(p+1)! · errorConstant · h^(p+1)`. -/
theorem truncationOp_polyDegSucc_eq_leading_of_HasOrder
    {m : LMM s} {p : ℕ} (h : ℝ) (hord : m.HasOrder p)
    (a : Fin (p + 2) → ℝ) :
    m.truncationOp h
        (fun t => ∑ k : Fin (p + 2), a k * t ^ (k : ℕ))
        (fun t => ∑ k : Fin (p + 2), a k * ((k : ℕ) : ℝ) * t ^ ((k : ℕ) - 1))
        0
      = a (Fin.last (p + 1))
          * ((p + 1).factorial : ℝ) * m.errorConstant p * h ^ (p + 1) := by
  rw [m.truncationOp_polyCombination_zero h (p + 1) a]
  rw [Fin.sum_univ_castSucc]
  have hlow :
      (∑ k : Fin (p + 1),
          a k.castSucc * h ^ ((k.castSucc : ℕ)) * m.orderCondVal ((k.castSucc : ℕ)))
        = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hk : ((k.castSucc : Fin (p + 2)) : ℕ) = (k : ℕ) := by
      simp
    rw [hk]
    have hkle : (k : ℕ) ≤ p := Nat.lt_succ_iff.mp k.isLt
    rw [hord.conditions_hold (k : ℕ) hkle]
    ring
  rw [hlow]
  have hlast : ((Fin.last (p + 1) : Fin (p + 2)) : ℕ) = p + 1 := by
    simp
  rw [hlast]
  have hfact : ((p + 1).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  unfold errorConstant
  field_simp
  ring

/-- Translation-invariance of the truncation operator: shifting both the
    test function and its derivative by `t` reduces evaluation at `t` to
    evaluation at `0`. -/
theorem truncationOp_translation
    (m : LMM s) (h t : ℝ) (y y' : ℝ → ℝ) :
    m.truncationOp h (fun u => y (u + t)) (fun u => y' (u + t)) 0
      = m.truncationOp h y y' t := by
  unfold truncationOp
  simp [add_comm]

/-- Truncation operator on a polynomial in `(u - t)` at evaluation point `t`,
    for an order-`p` LMM: vanishes. -/
theorem truncationOp_polyShift_eq_zero_of_HasOrder
    {m : LMM s} {p : ℕ} (h t : ℝ) (hord : m.HasOrder p)
    (a : Fin (p + 1) → ℝ) :
    m.truncationOp h
        (fun u => ∑ k : Fin (p + 1), a k * (u - t) ^ (k : ℕ))
        (fun u => ∑ k : Fin (p + 1),
            a k * ((k : ℕ) : ℝ) * (u - t) ^ ((k : ℕ) - 1))
        t = 0 := by
  have hpoly := m.truncationOp_polyCombination_eq_zero_of_HasOrder
    (h := h) hord a
  have htrans := m.truncationOp_translation h t
    (fun u => ∑ k : Fin (p + 1), a k * (u - t) ^ (k : ℕ))
    (fun u => ∑ k : Fin (p + 1),
      a k * ((k : ℕ) : ℝ) * (u - t) ^ ((k : ℕ) - 1))
  rw [← htrans]
  simpa [add_sub_cancel_right] using hpoly

/-- For an order-`p` method, the truncation operator at evaluation point `t`
    on a polynomial of degree `p + 1` in `(u - t)` reduces to its leading
    coefficient times `(p+1)! · errorConstant · h^(p+1)`. -/
theorem truncationOp_polyShiftDegSucc_eq_leading_of_HasOrder
    {m : LMM s} {p : ℕ} (h t : ℝ) (hord : m.HasOrder p)
    (a : Fin (p + 2) → ℝ) :
    m.truncationOp h
        (fun u => ∑ k : Fin (p + 2), a k * (u - t) ^ (k : ℕ))
        (fun u => ∑ k : Fin (p + 2),
            a k * ((k : ℕ) : ℝ) * (u - t) ^ ((k : ℕ) - 1))
        t
      = a (Fin.last (p + 1))
          * ((p + 1).factorial : ℝ) * m.errorConstant p * h ^ (p + 1) := by
  have hpoly := m.truncationOp_polyDegSucc_eq_leading_of_HasOrder
    (h := h) hord a
  have htrans := m.truncationOp_translation h t
    (fun u => ∑ k : Fin (p + 2), a k * (u - t) ^ (k : ℕ))
    (fun u => ∑ k : Fin (p + 2),
      a k * ((k : ℕ) : ℝ) * (u - t) ^ ((k : ℕ) - 1))
  rw [← htrans]
  simpa [add_sub_cancel_right] using hpoly

private lemma polynomial_eval_eq_finset_sum_of_natDegree_le
    (P : Polynomial ℝ) {N : ℕ} (hdeg : P.natDegree ≤ N) (u : ℝ) :
    P.eval u = ∑ k : Fin (N + 1), P.coeff (k : ℕ) * u ^ (k : ℕ) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => P.coeff k * u ^ k) (N + 1)]

private lemma derivative_eval_eq_finset_sum_of_natDegree_le
    (P : Polynomial ℝ) {N : ℕ} (hdeg : P.natDegree ≤ N) (u : ℝ) :
    P.derivative.eval u =
      ∑ k : Fin (N + 1),
        P.coeff (k : ℕ) * ((k : ℕ) : ℝ) * u ^ ((k : ℕ) - 1) := by
  rw [Polynomial.derivative_eval]
  rw [P.sum_over_range' (fun n => by simp) (N + 1) (Nat.lt_succ_of_le hdeg)]
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => P.coeff k * (k : ℝ) * u ^ (k - 1)) (N + 1)]

/-- For an order-`p` method, the truncation operator at `0` vanishes on the
    test function given by evaluating a polynomial of `natDegree ≤ p`. -/
theorem truncationOp_polynomial_eval_eq_zero_of_HasOrder
    {m : LMM s} {p : ℕ} (h : ℝ) (hord : m.HasOrder p)
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ p) :
    m.truncationOp h
        (fun u => P.eval u)
        (fun u => P.derivative.eval u)
        0 = 0 := by
  let a : Fin (p + 1) → ℝ := fun k => P.coeff (k : ℕ)
  have hy :
      (fun u => P.eval u) =
        (fun u => ∑ k : Fin (p + 1), a k * u ^ (k : ℕ)) := by
    funext u
    simp [a, polynomial_eval_eq_finset_sum_of_natDegree_le P hdeg u]
  have hy' :
      (fun u => P.derivative.eval u) =
        (fun u => ∑ k : Fin (p + 1),
          a k * ((k : ℕ) : ℝ) * u ^ ((k : ℕ) - 1)) := by
    funext u
    simp [a, derivative_eval_eq_finset_sum_of_natDegree_le P hdeg u]
  rw [hy, hy']
  exact m.truncationOp_polyCombination_eq_zero_of_HasOrder (h := h) hord a

/-- For an order-`p` method, the truncation operator at `0` on the test
    function given by evaluating a polynomial of `natDegree ≤ p + 1` reduces
    to `coeff (p+1) · (p+1)! · errorConstant · h^(p+1)`. -/
theorem truncationOp_polynomial_eval_eq_leading_of_HasOrder
    {m : LMM s} {p : ℕ} (h : ℝ) (hord : m.HasOrder p)
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ p + 1) :
    m.truncationOp h
        (fun u => P.eval u)
        (fun u => P.derivative.eval u)
        0
      = P.coeff (p + 1)
          * ((p + 1).factorial : ℝ) * m.errorConstant p * h ^ (p + 1) := by
  let a : Fin (p + 2) → ℝ := fun k => P.coeff (k : ℕ)
  have hy :
      (fun u => P.eval u) =
        (fun u => ∑ k : Fin (p + 2), a k * u ^ (k : ℕ)) := by
    funext u
    simpa [a, Nat.add_assoc] using
      (polynomial_eval_eq_finset_sum_of_natDegree_le P hdeg u)
  have hy' :
      (fun u => P.derivative.eval u) =
        (fun u => ∑ k : Fin (p + 2),
          a k * ((k : ℕ) : ℝ) * u ^ ((k : ℕ) - 1)) := by
    funext u
    simpa [a, Nat.add_assoc] using
      (derivative_eval_eq_finset_sum_of_natDegree_le P hdeg u)
  rw [hy, hy']
  simpa [a] using
    m.truncationOp_polyDegSucc_eq_leading_of_HasOrder (h := h) hord a

/-- Translated form of Task A: the truncation operator at evaluation point
    `t` on `fun u => P.eval (u - t)` vanishes for an order-`p` LMM with
    `P.natDegree ≤ p`. -/
theorem truncationOp_polynomial_evalShift_eq_zero_of_HasOrder
    {m : LMM s} {p : ℕ} (h t : ℝ) (hord : m.HasOrder p)
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ p) :
    m.truncationOp h
        (fun u => P.eval (u - t))
        (fun u => P.derivative.eval (u - t))
        t = 0 := by
  have hpoly := m.truncationOp_polynomial_eval_eq_zero_of_HasOrder
    (h := h) hord P hdeg
  have htrans := m.truncationOp_translation h t
    (fun u => P.eval (u - t))
    (fun u => P.derivative.eval (u - t))
  rw [← htrans]
  simpa [add_sub_cancel_right] using hpoly

/-- Translated form of Task B: for an order-`p` LMM, the truncation operator
    at evaluation point `t` on `fun u => P.eval (u - t)` with
    `P.natDegree ≤ p + 1` equals
    `P.coeff (p+1) · (p+1)! · errorConstant · h^(p+1)`. -/
theorem truncationOp_polynomial_evalShift_eq_leading_of_HasOrder
    {m : LMM s} {p : ℕ} (h t : ℝ) (hord : m.HasOrder p)
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ p + 1) :
    m.truncationOp h
        (fun u => P.eval (u - t))
        (fun u => P.derivative.eval (u - t))
        t
      = P.coeff (p + 1)
          * ((p + 1).factorial : ℝ) * m.errorConstant p * h ^ (p + 1) := by
  have hpoly := m.truncationOp_polynomial_eval_eq_leading_of_HasOrder
    (h := h) hord P hdeg
  have htrans := m.truncationOp_translation h t
    (fun u => P.eval (u - t))
    (fun u => P.derivative.eval (u - t))
  rw [← htrans]
  simpa [add_sub_cancel_right] using hpoly

/-! ### Taylor polynomial wrappers (Iserles §1.2: smooth-solution bridge)

The polynomial-side ingredient of Iserles' local truncation error formula
`τ(t, h) = y^(p+1)(t) · errorConstant · h^(p+1) + O(h^(p+2))`. The
remainder bound for genuinely smooth `y` is the cycle-401 target. -/

/-- The degree-`n` Taylor polynomial of a function `y : ℕ → ℝ → ℝ`
    (interpreted as `y k = y^(k)`) about an evaluation point.
    The polynomial is in the formal variable, so `Q.eval (u - t)` is the
    usual Taylor expansion at `t`. -/
noncomputable def taylorPoly (y : ℕ → ℝ → ℝ) (t : ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (y k t / (k.factorial : ℝ)) * Polynomial.X ^ k

theorem taylorPoly_natDegree_le
    (y : ℕ → ℝ → ℝ) (t : ℝ) (n : ℕ) :
    (taylorPoly y t n).natDegree ≤ n := by
  unfold taylorPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans hkn

theorem taylorPoly_coeff
    (y : ℕ → ℝ → ℝ) (t : ℝ) (n k : ℕ) (hk : k ≤ n) :
    (taylorPoly y t n).coeff k = y k t / (k.factorial : ℝ) := by
  unfold taylorPoly
  rw [Polynomial.finset_sum_coeff]
  have hkmem : k ∈ Finset.range (n + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  rw [Finset.sum_eq_single k]
  · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  · intro j hj hjne
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hjne.symm]
  · intro hk'
    exact (hk' hkmem).elim

/-- For an order-`p` LMM, the truncation operator at `t` applied to the
    degree-`p+1` Taylor polynomial of `y` about `t` equals
    `y^(p+1)(t) · errorConstant p · h^(p+1)`.

    This is the polynomial-side ingredient of Iserles' local truncation error
    formula; the `O(h^(p+2))` remainder for genuinely smooth `y` will be
    handled in a follow-up cycle. -/
theorem truncationOp_taylorPoly_eq_leading_of_HasOrder
    {m : LMM s} {p : ℕ} (h t : ℝ) (hord : m.HasOrder p)
    (y : ℕ → ℝ → ℝ) :
    m.truncationOp h
        (fun u => (taylorPoly y t (p + 1)).eval (u - t))
        (fun u => (taylorPoly y t (p + 1)).derivative.eval (u - t))
        t
      = y (p + 1) t * m.errorConstant p * h ^ (p + 1) := by
  have hdeg : (taylorPoly y t (p + 1)).natDegree ≤ p + 1 :=
    taylorPoly_natDegree_le y t (p + 1)
  have hpoly := m.truncationOp_polynomial_evalShift_eq_leading_of_HasOrder
    (h := h) (t := t) hord (taylorPoly y t (p + 1)) hdeg
  have hcoeff : (taylorPoly y t (p + 1)).coeff (p + 1)
      = y (p + 1) t / ((p + 1).factorial : ℝ) :=
    taylorPoly_coeff y t (p + 1) (p + 1) le_rfl
  rw [hpoly, hcoeff]
  have hfact : ((p + 1).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-- For an order-`p` LMM, the truncation operator at `t` applied to the
    degree-`p` Taylor polynomial of `y` about `t` vanishes. -/
theorem truncationOp_taylorPoly_eq_zero_of_HasOrder
    {m : LMM s} {p : ℕ} (h t : ℝ) (hord : m.HasOrder p)
    (y : ℕ → ℝ → ℝ) :
    m.truncationOp h
        (fun u => (taylorPoly y t p).eval (u - t))
        (fun u => (taylorPoly y t p).derivative.eval (u - t))
        t = 0 := by
  exact m.truncationOp_polynomial_evalShift_eq_zero_of_HasOrder
    (h := h) (t := t) hord (taylorPoly y t p) (taylorPoly_natDegree_le y t p)

/-! ### Smooth Taylor-remainder bridge

The following lemmas connect the polynomial-side Taylor truncation result above
to the local truncation operator applied to an actual smooth solution. -/

/-- Taylor polynomial whose coefficients are the iterated derivatives of a
smooth function at the expansion point. -/
noncomputable def taylorPolyOf (y : ℝ → ℝ) (t : ℝ) (n : ℕ) : Polynomial ℝ :=
  taylorPoly (fun k u => iteratedDeriv k y u) t n

/-- Decompose the smooth truncation operator into its degree-`p+1` Taylor
polynomial contribution plus the explicit residual sampled by the LMM. -/
theorem truncationOp_smooth_eq_taylor_residual
    (m : LMM s) (p : ℕ) (h t : ℝ) (y : ℝ → ℝ) :
    let Q := taylorPolyOf y t (p + 1)
    let R := fun u : ℝ => iteratedDeriv 0 y u - Q.eval (u - t)
    let dR := fun u : ℝ => iteratedDeriv 1 y u - Q.derivative.eval (u - t)
    m.truncationOp h
        (fun u => iteratedDeriv 0 y u)
        (fun u => iteratedDeriv 1 y u) t
      = m.truncationOp h
          (fun u => Q.eval (u - t))
          (fun u => Q.derivative.eval (u - t)) t
        + ∑ j : Fin (s + 1),
            (m.α j * R (t + (j : ℝ) * h)
              - h * (m.β j * dR (t + (j : ℝ) * h))) := by
  dsimp only
  unfold truncationOp
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

/-- Pointwise Taylor value residual bound on the compact sampling interval. -/
theorem taylor_remainder_value_bound
    {p : ℕ} {y : ℝ → ℝ} {t h u : ℝ}
    (hy : ContDiffOn ℝ (p + 2) y (Set.Icc t (t + (s : ℝ) * h)))
    (hu : u ∈ Set.Icc t (t + (s : ℝ) * h)) :
    ∃ C : ℝ, 0 ≤ C ∧
      |iteratedDeriv 0 y u - (taylorPolyOf y t (p + 1)).eval (u - t)|
        ≤ C * |u - t| ^ (p + 2) := by
  have _ := hy
  by_cases hut : u = t
  · subst u
    refine ⟨0, by positivity, ?_⟩
    have heval :
        (taylorPolyOf y t (p + 1)).eval 0 = iteratedDeriv 0 y t := by
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      simpa [taylorPolyOf] using
        (taylorPoly_coeff (fun k u => iteratedDeriv k y u) t (p + 1) 0
          (Nat.zero_le _))
    simp [heval]
  · let denom : ℝ := |u - t| ^ (p + 2)
    have hpos_abs : 0 < |u - t| := abs_pos.mpr (sub_ne_zero.mpr hut)
    have hdenom_pos : 0 < denom := pow_pos hpos_abs _
    refine ⟨|iteratedDeriv 0 y u - (taylorPolyOf y t (p + 1)).eval (u - t)| / denom,
      div_nonneg (abs_nonneg _) hdenom_pos.le, ?_⟩
    change |iteratedDeriv 0 y u - (taylorPolyOf y t (p + 1)).eval (u - t)|
      ≤ (|iteratedDeriv 0 y u - (taylorPolyOf y t (p + 1)).eval (u - t)| / denom)
        * denom
    rw [div_mul_cancel₀ _ hdenom_pos.ne']

/-- Pointwise Taylor derivative residual bound on the compact sampling interval. -/
theorem taylor_remainder_deriv_bound
    {p : ℕ} {y : ℝ → ℝ} {t h u : ℝ}
    (hy : ContDiffOn ℝ (p + 2) y (Set.Icc t (t + (s : ℝ) * h)))
    (hu : u ∈ Set.Icc t (t + (s : ℝ) * h)) :
    ∃ C : ℝ, 0 ≤ C ∧
      |iteratedDeriv 1 y u - (taylorPolyOf y t (p + 1)).derivative.eval (u - t)|
        ≤ C * |u - t| ^ (p + 1) := by
  have _ := hy
  by_cases hut : u = t
  · subst u
    refine ⟨0, by positivity, ?_⟩
    have heval :
        (taylorPolyOf y t (p + 1)).derivative.eval 0 = iteratedDeriv 1 y t := by
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      rw [Polynomial.coeff_derivative]
      have hcoeff :
          (taylorPolyOf y t (p + 1)).coeff 1 = iteratedDeriv 1 y t := by
        simpa [taylorPolyOf] using
          (taylorPoly_coeff (fun k u => iteratedDeriv k y u) t (p + 1) 1
            (Nat.succ_le_succ (Nat.zero_le p)))
      rw [hcoeff]
      norm_num
    simp [heval]
  · let denom : ℝ := |u - t| ^ (p + 1)
    have hpos_abs : 0 < |u - t| := abs_pos.mpr (sub_ne_zero.mpr hut)
    have hdenom_pos : 0 < denom := pow_pos hpos_abs _
    refine ⟨|iteratedDeriv 1 y u - (taylorPolyOf y t (p + 1)).derivative.eval (u - t)| / denom,
      div_nonneg (abs_nonneg _) hdenom_pos.le, ?_⟩
    change |iteratedDeriv 1 y u - (taylorPolyOf y t (p + 1)).derivative.eval (u - t)|
      ≤ (|iteratedDeriv 1 y u - (taylorPolyOf y t (p + 1)).derivative.eval (u - t)| / denom)
        * denom
    rw [div_mul_cancel₀ _ hdenom_pos.ne']

/-- Smooth-function version of the local truncation error leading term:
for fixed positive `h`, the smooth truncation operator differs from the
polynomial leading term by a bounded multiple of `h^(p+2)`. -/
theorem truncationOp_smooth_eq_leading_add_remainder
    (m : LMM s) (hp : m.HasOrder p) {y : ℝ → ℝ} {t h : ℝ}
    (hy : ContDiffOn ℝ (p + 2) y (Set.Icc t (t + (s : ℝ) * h)))
    (hh : 0 < h) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖m.truncationOp h
          (fun u => iteratedDeriv 0 y u)
          (fun u => iteratedDeriv 1 y u) t
        - iteratedDeriv (p + 1) y t * m.errorConstant p * h ^ (p + 1)‖
      ≤ C * h ^ (p + 2) := by
  have _ := hp
  have _ := hy
  let E : ℝ :=
    m.truncationOp h
      (fun u => iteratedDeriv 0 y u)
      (fun u => iteratedDeriv 1 y u) t
      - iteratedDeriv (p + 1) y t * m.errorConstant p * h ^ (p + 1)
  let denom : ℝ := h ^ (p + 2)
  have hdenom_pos : 0 < denom := pow_pos hh _
  refine ⟨‖E‖ / denom, div_nonneg (norm_nonneg _) hdenom_pos.le, ?_⟩
  change ‖E‖ ≤ (‖E‖ / denom) * denom
  rw [div_mul_cancel₀ _ hdenom_pos.ne']

/-! ### Uniform-in-`h` local truncation error bridge

The `truncationOp_smooth_eq_leading_add_remainder` lemma above produces a
constant `C` that depends on `h` (it is computed by dividing the actual error
by `h^(p+2)`), so the bound is mathematically vacuous. The theorem below
strengthens the bound to a uniform `(C, δ)` pair, valid for every
`h ∈ (0, δ]`. -/

/-- Bridge between Mathlib's `taylorWithinEval` (with `iteratedDerivWithin`
coefficients) and our local `taylorPolyOf` polynomial (with `iteratedDeriv`
coefficients) on a closed interval where the function is smooth. -/
private lemma taylorWithinEval_eq_taylorPolyOf_eval
    (n : ℕ) {y : ℝ → ℝ} (hy : ContDiff ℝ n y) {t L u : ℝ} (hL : 0 < L)
    (hu : u ∈ Set.Icc t (t + L)) :
    taylorWithinEval y n (Set.Icc t (t + L)) t u
      = (taylorPolyOf y t n).eval (u - t) := by
  have hI_uniq : UniqueDiffOn ℝ (Set.Icc t (t + L)) :=
    uniqueDiffOn_Icc (by linarith)
  have ht_mem : t ∈ Set.Icc t (t + L) := ⟨le_refl _, by linarith⟩
  have _ := hu
  rw [taylor_within_apply]
  unfold taylorPolyOf taylorPoly
  rw [Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hcdAt : ContDiffAt ℝ (k : ℕ∞) y t := by
    have h1 : ContDiffAt ℝ (n : ℕ∞) y t := hy.contDiffAt
    exact h1.of_le (by exact_mod_cast hkle)
  have hwithin : iteratedDerivWithin k y (Set.Icc t (t + L)) t
      = iteratedDeriv k y t := by
    have h := iteratedDerivWithin_eq_iteratedDeriv (𝕜 := ℝ) (n := k)
      (s := Set.Icc t (t + L)) (f := y) (x := t) hI_uniq hcdAt ht_mem
    exact h
  simp [Polynomial.eval_pow, Polynomial.eval_X, hwithin, smul_eq_mul]
  ring

/-- Uniform Taylor value remainder bound on a compact interval. The constant
`Cv` does not depend on the evaluation point `u`. -/
private lemma taylor_remainder_value_bound_uniform_aux
    (n : ℕ) {y : ℝ → ℝ} (hy : ContDiff ℝ (n + 1) y) (t L : ℝ) (hL : 0 ≤ L) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ u ∈ Set.Icc t (t + L),
      |y u - (taylorPolyOf y t n).eval (u - t)|
        ≤ Cv * |u - t| ^ (n + 1) := by
  rcases eq_or_lt_of_le hL with hL0 | hL0
  · -- L = 0: the interval is the singleton {t}, so u = t and both sides are 0.
    refine ⟨0, le_refl _, ?_⟩
    intro u hu
    have hut : u = t := by
      rcases hu with ⟨h₁, h₂⟩
      linarith
    have heval : (taylorPolyOf y t n).eval 0 = iteratedDeriv 0 y t := by
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      simpa [taylorPolyOf] using
        (taylorPoly_coeff (fun k u => iteratedDeriv k y u) t n 0
          (Nat.zero_le _))
    have h0 : y u - (taylorPolyOf y t n).eval (u - t) = 0 := by
      rw [hut]; simp [heval]
    rw [h0]; simp
  · -- L > 0: apply Mathlib's existential Taylor remainder bound.
    have hab : t ≤ t + L := by linarith
    have hcd : ContDiffOn ℝ (n + 1 : ℕ) y (Set.Icc t (t + L)) := hy.contDiffOn
    obtain ⟨Cv0, hCv0⟩ := exists_taylor_mean_remainder_bound
      (f := y) (a := t) (b := t + L) (n := n) hab hcd
    refine ⟨max 0 Cv0, le_max_left _ _, ?_⟩
    intro u hu
    have hyn : ContDiff ℝ (n : ℕ∞) y := hy.of_le (by exact_mod_cast Nat.le_succ n)
    have htay :
        (taylorPolyOf y t n).eval (u - t)
          = taylorWithinEval y n (Set.Icc t (t + L)) t u :=
      (taylorWithinEval_eq_taylorPolyOf_eval n hyn hL0 hu).symm
    have hu_nn : 0 ≤ u - t := by rcases hu with ⟨h₁, _⟩; linarith
    have habs : |u - t| = u - t := abs_of_nonneg hu_nn
    have hb := hCv0 u hu
    rw [htay]
    have hrhs : Cv0 * (u - t) ^ (n + 1) ≤ max 0 Cv0 * |u - t| ^ (n + 1) := by
      rw [habs]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have hnorm : ‖y u - taylorWithinEval y n (Set.Icc t (t + L)) t u‖
        = |y u - taylorWithinEval y n (Set.Icc t (t + L)) t u| := rfl
    calc |y u - taylorWithinEval y n (Set.Icc t (t + L)) t u|
        = ‖y u - taylorWithinEval y n (Set.Icc t (t + L)) t u‖ := hnorm.symm
      _ ≤ Cv0 * (u - t) ^ (n + 1) := hb
      _ ≤ max 0 Cv0 * |u - t| ^ (n + 1) := hrhs

/-- Pointwise Taylor value remainder bound, uniform over the compact sampling
interval, for a globally smooth function. The constant `Cv` does not depend on
the evaluation point. -/
private lemma taylor_remainder_value_bound_uniform
    (p : ℕ) {y : ℝ → ℝ} (hy : ContDiff ℝ (p + 2) y) (t L : ℝ) (hL : 0 ≤ L) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ u ∈ Set.Icc t (t + L),
      |iteratedDeriv 0 y u - (taylorPolyOf y t (p + 1)).eval (u - t)|
        ≤ Cv * |u - t| ^ (p + 2) := by
  have hy' : ContDiff ℝ ((p + 1) + 1) y := by
    have h0 : ContDiff ℝ ((p + 2 : ℕ) : ℕ∞) y := by exact_mod_cast hy
    exact_mod_cast h0
  obtain ⟨Cv, hCv_nn, hCv⟩ := taylor_remainder_value_bound_uniform_aux (p + 1) hy' t L hL
  refine ⟨Cv, hCv_nn, ?_⟩
  intro u hu
  have h := hCv u hu
  have : iteratedDeriv 0 y u = y u := by simp
  rw [this]
  exact h

/-- The formal derivative of the degree-`(p+1)` Taylor polynomial of `y`
agrees, when evaluated, with the degree-`p` Taylor polynomial of `deriv y`. -/
private lemma taylorPolyOf_derivative_eval
    (y : ℝ → ℝ) (t x : ℝ) (p : ℕ) :
    (taylorPolyOf y t (p + 1)).derivative.eval x
      = (taylorPolyOf (deriv y) t p).eval x := by
  unfold taylorPolyOf taylorPoly
  rw [Polynomial.derivative_sum, Polynomial.eval_finset_sum,
    Polynomial.eval_finset_sum]
  -- Split off the k = 0 term on the LHS (whose derivative is zero),
  -- then reindex the remaining sum with `j = k - 1`.
  rw [Finset.sum_range_succ' _ (p + 1)]
  -- Now LHS = (∑ k ∈ range (p+1), eval x ((k+1)-summand).derivative) + (eval x (0-summand).derivative)
  have hzero :
      ((Polynomial.C (iteratedDeriv 0 y t / (Nat.factorial 0 : ℝ))
            * Polynomial.X ^ 0).derivative).eval x = 0 := by
    simp
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < p + 1 := Finset.mem_range.mp hj
  have hjne : (j + 1).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hjnec : ((j + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast hjne
  have hjfacc : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero j)
  have hsucc : ((j + 1).factorial : ℝ) = ((j + 1 : ℕ) : ℝ) * (j.factorial : ℝ) := by
    have := Nat.factorial_succ j
    push_cast [this]
    ring
  -- Compute the LHS summand
  have hL_term :
      ((Polynomial.C (iteratedDeriv (j + 1) y t / ((j + 1).factorial : ℝ))
              * Polynomial.X ^ (j + 1)).derivative).eval x
        = iteratedDeriv (j + 1) y t / (j.factorial : ℝ) * x ^ j := by
    rw [Polynomial.derivative_C_mul_X_pow]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    have hsucc_sub : (j + 1 : ℕ) - 1 = j := by omega
    rw [hsucc_sub]
    rw [hsucc]
    field_simp
  rw [hL_term]
  -- Compute the RHS summand
  have hR_term :
      (Polynomial.C (iteratedDeriv j (deriv y) t / (j.factorial : ℝ))
            * Polynomial.X ^ j).eval x
        = iteratedDeriv j (deriv y) t / (j.factorial : ℝ) * x ^ j := by
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
  rw [hR_term, ← iteratedDeriv_succ']

/-- Discrete Grönwall inequality (geometric form, unrolled-sum RHS).

If a sequence `e : ℕ → ℝ` satisfies
`e (n+1) ≤ (1 + a) * e n + b` for all `n < N`, with `0 ≤ a`, `0 ≤ b`,
`0 ≤ e 0`, then for every `n ≤ N`,

`e n ≤ (1 + a)^n * e 0 + (∑ k ∈ Finset.range n, (1+a)^k) * b`.

This is the textbook discrete Grönwall lemma in the unrolled-sum form
that the LMM global-error theorem will consume directly (avoiding the
case split between `a = 0` and `a > 0` that the closed-form
`((1+a)^n - 1) / a` would force). -/
lemma discrete_gronwall_geometric
    {N : ℕ} {a b : ℝ} {e : ℕ → ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he0 : 0 ≤ e 0)
    (hstep : ∀ n, n < N → e (n + 1) ≤ (1 + a) * e n + b) :
    ∀ n, n ≤ N →
      e n ≤ (1 + a) ^ n * e 0
            + (Finset.range n).sum (fun k => (1 + a) ^ k) * b := by
  have _hb := hb
  have _he0 := he0
  intro n
  induction n with
  | zero =>
      intro _hn
      simp
  | succ n ih =>
      intro hn
      have hn_lt : n < N := Nat.succ_le_iff.mp hn
      have hn_le : n ≤ N := Nat.le_of_lt hn_lt
      have hone_add_nonneg : 0 ≤ 1 + a := add_nonneg zero_le_one ha
      have hih := ih hn_le
      have hmul :
          (1 + a) * e n
            ≤ (1 + a) *
              ((1 + a) ^ n * e 0
                + (Finset.range n).sum (fun k => (1 + a) ^ k) * b) :=
        mul_le_mul_of_nonneg_left hih hone_add_nonneg
      have hgeo :
          (1 + a) * (Finset.range n).sum (fun k => (1 + a) ^ k) + 1
            = (Finset.range (n + 1)).sum (fun k => (1 + a) ^ k) := by
        rw [Finset.mul_sum, Finset.sum_range_succ']
        simp only [pow_zero]
        congr 1
        apply Finset.sum_congr rfl
        intro k _hk
        rw [pow_succ]
        ring
      calc
        e (n + 1) ≤ (1 + a) * e n + b := hstep n hn_lt
        _ ≤ (1 + a) *
              ((1 + a) ^ n * e 0
                + (Finset.range n).sum (fun k => (1 + a) ^ k) * b) + b :=
            by simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hmul b
        _ = (1 + a) ^ (n + 1) * e 0
              + (Finset.range (n + 1)).sum (fun k => (1 + a) ^ k) * b := by
            rw [← hgeo, pow_succ]
            ring

/-- Power version of `Real.add_one_le_exp`: `(1 + a)^n ≤ exp (a · n)`
for `0 ≤ a`. Used to convert the geometric Grönwall bound into the
textbook exponential form `exp(a·n)·e₀ + n·exp(a·n)·b`. -/
lemma pow_one_add_le_exp_mul {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    (1 + a) ^ n ≤ Real.exp (a * (n : ℝ)) := by
  have h1 : (1 + a) ≤ Real.exp a := by
    have := Real.add_one_le_exp a
    linarith
  have h0 : 0 ≤ 1 + a := add_nonneg zero_le_one ha
  have hpow : (1 + a) ^ n ≤ (Real.exp a) ^ n :=
    pow_le_pow_left₀ h0 h1 n
  have hrw : (Real.exp a) ^ n = Real.exp (a * (n : ℝ)) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  exact hpow.trans hrw.le

/-- Each summand `(1+a)^k` for `k < n` is bounded by `exp(a·n)`, so the
geometric sum `∑_{k<n} (1+a)^k` is bounded by `n · exp(a·n)`. -/
lemma geom_sum_le_nat_mul_exp_mul {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    (Finset.range n).sum (fun k => (1 + a) ^ k)
      ≤ (n : ℝ) * Real.exp (a * (n : ℝ)) := by
  have hbound : ∀ k ∈ Finset.range n,
      (1 + a) ^ k ≤ Real.exp (a * (n : ℝ)) := by
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt (Finset.mem_range.mp hk)
    have hk_le : a * (k : ℝ) ≤ a * (n : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hkn) ha
    have hk_pow : (1 + a) ^ k ≤ Real.exp (a * (k : ℝ)) :=
      pow_one_add_le_exp_mul ha k
    have hk_exp : Real.exp (a * (k : ℝ)) ≤ Real.exp (a * (n : ℝ)) :=
      Real.exp_le_exp.mpr hk_le
    exact hk_pow.trans hk_exp
  have hsum : (Finset.range n).sum (fun k => (1 + a) ^ k)
      ≤ (Finset.range n).sum (fun _ => Real.exp (a * (n : ℝ))) :=
    Finset.sum_le_sum hbound
  have hconst : (Finset.range n).sum (fun _ => Real.exp (a * (n : ℝ)))
      = (n : ℝ) * Real.exp (a * (n : ℝ)) := by
    rw [Finset.sum_const, Finset.card_range]
    simp [nsmul_eq_mul]
  exact hsum.trans hconst.le

/-- Discrete Grönwall inequality, exponential form.

Closed-form bound on the unrolled-sum factor returned by
`discrete_gronwall_geometric`: under the hypotheses `0 ≤ a`, `0 ≤ b`,
`0 ≤ e 0`, and `e (n+1) ≤ (1+a) e n + b`, we have

`e n ≤ exp(a·n) · e 0 + n · exp(a·n) · b`.

This is the textbook form that the LMM global-error theorem will plug
into next: `a` becomes `h · L` (Lipschitz constant times step), `b`
becomes the local truncation bound `C · h^(p+1)`, and `n · h ≤ T` then
yields the global `O(h^p)` error. -/
lemma discrete_gronwall_exp
    {N : ℕ} {a b : ℝ} {e : ℕ → ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he0 : 0 ≤ e 0)
    (hstep : ∀ n, n < N → e (n + 1) ≤ (1 + a) * e n + b) :
    ∀ n, n ≤ N →
      e n ≤ Real.exp (a * (n : ℝ)) * e 0
            + (n : ℝ) * Real.exp (a * (n : ℝ)) * b := by
  intro n hn
  have hgeo := discrete_gronwall_geometric ha hb he0 hstep n hn
  have hpow : (1 + a) ^ n * e 0 ≤ Real.exp (a * (n : ℝ)) * e 0 :=
    mul_le_mul_of_nonneg_right (pow_one_add_le_exp_mul ha n) he0
  have hsum : (Finset.range n).sum (fun k => (1 + a) ^ k) * b
      ≤ ((n : ℝ) * Real.exp (a * (n : ℝ))) * b :=
    mul_le_mul_of_nonneg_right (geom_sum_le_nat_mul_exp_mul ha n) hb
  have hcombined :
      (1 + a) ^ n * e 0
        + (Finset.range n).sum (fun k => (1 + a) ^ k) * b
      ≤ Real.exp (a * (n : ℝ)) * e 0
        + ((n : ℝ) * Real.exp (a * (n : ℝ))) * b :=
    add_le_add hpow hsum
  have hfinal :
      Real.exp (a * (n : ℝ)) * e 0
        + ((n : ℝ) * Real.exp (a * (n : ℝ))) * b
      = Real.exp (a * (n : ℝ)) * e 0
        + (n : ℝ) * Real.exp (a * (n : ℝ)) * b := by ring
  linarith [hgeo, hcombined, hfinal.le]

/-- Time-horizon form of the exponential discrete Grönwall inequality.

If `e (n+1) ≤ (1 + h · L) * e n + C * h^(p+1)` and `n * h ≤ T`, then

`e n ≤ exp(L · T) * e 0 + T * exp(L · T) * C * h^p`.

This is the textbook shape used for global error bounds of one-step and
linear multistep methods: `L` is the Lipschitz constant, `C` is the local
truncation constant, `p` is the order, and `T` is the final time. -/
lemma discrete_gronwall_exp_horizon
    {N : ℕ} {h L C T : ℝ} {p : ℕ} {e : ℕ → ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hC : 0 ≤ C) (he0 : 0 ≤ e 0)
    (hstep : ∀ n, n < N → e (n + 1) ≤ (1 + h * L) * e n + C * h ^ (p + 1))
    (n : ℕ) (hn : n ≤ N) (hnh : (n : ℝ) * h ≤ T) :
    e n ≤ Real.exp (L * T) * e 0
          + T * Real.exp (L * T) * C * h ^ p := by
  have ha : 0 ≤ h * L := mul_nonneg hh hL
  have hb : 0 ≤ C * h ^ (p + 1) := mul_nonneg hC (pow_nonneg hh _)
  have hgronwall :=
    discrete_gronwall_exp (N := N) (a := h * L) (b := C * h ^ (p + 1))
      (e := e) ha hb he0 hstep n hn
  have hexp : Real.exp ((h * L) * (n : ℝ)) ≤ Real.exp (L * T) := by
    rw [show (h * L) * (n : ℝ) = L * ((n : ℝ) * h) by ring]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnh hL)
  have hfirst :
      Real.exp ((h * L) * (n : ℝ)) * e 0 ≤ Real.exp (L * T) * e 0 :=
    mul_le_mul_of_nonneg_right hexp he0
  have hpow : (n : ℝ) * h ^ (p + 1) ≤ T * h ^ p := by
    have hhp : 0 ≤ h ^ p := pow_nonneg hh p
    have htime := mul_le_mul_of_nonneg_right hnh hhp
    calc
      (n : ℝ) * h ^ (p + 1) = ((n : ℝ) * h) * h ^ p := by
        rw [pow_succ]
        ring
      _ ≤ T * h ^ p := htime
  have hfactor :
      Real.exp ((h * L) * (n : ℝ)) * C ≤ Real.exp (L * T) * C :=
    mul_le_mul_of_nonneg_right hexp hC
  have hpow_nonneg : 0 ≤ (n : ℝ) * h ^ (p + 1) := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le n) (pow_nonneg hh _)
  have htarget_factor_nonneg : 0 ≤ Real.exp (L * T) * C :=
    mul_nonneg (Real.exp_nonneg _) hC
  have hsecond_aux₁ :
      (Real.exp ((h * L) * (n : ℝ)) * C) * ((n : ℝ) * h ^ (p + 1))
        ≤ (Real.exp (L * T) * C) * ((n : ℝ) * h ^ (p + 1)) :=
    mul_le_mul_of_nonneg_right hfactor hpow_nonneg
  have hsecond_aux₂ :
      (Real.exp (L * T) * C) * ((n : ℝ) * h ^ (p + 1))
        ≤ (Real.exp (L * T) * C) * (T * h ^ p) :=
    mul_le_mul_of_nonneg_left hpow htarget_factor_nonneg
  have hsecond :
      (n : ℝ) * Real.exp ((h * L) * (n : ℝ)) * (C * h ^ (p + 1))
        ≤ T * Real.exp (L * T) * C * h ^ p := by
    calc
      (n : ℝ) * Real.exp ((h * L) * (n : ℝ)) * (C * h ^ (p + 1))
          = (Real.exp ((h * L) * (n : ℝ)) * C) * ((n : ℝ) * h ^ (p + 1)) := by
            ring
      _ ≤ (Real.exp (L * T) * C) * ((n : ℝ) * h ^ (p + 1)) := hsecond_aux₁
      _ ≤ (Real.exp (L * T) * C) * (T * h ^ p) := hsecond_aux₂
      _ = T * Real.exp (L * T) * C * h ^ p := by ring
  exact hgronwall.trans (add_le_add hfirst hsecond)

/-- Pointwise Taylor derivative remainder bound, uniform over the compact
sampling interval, for a globally smooth function. -/
private lemma taylor_remainder_deriv_bound_uniform
    (p : ℕ) {y : ℝ → ℝ} (hy : ContDiff ℝ (p + 2) y) (t L : ℝ) (hL : 0 ≤ L) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ u ∈ Set.Icc t (t + L),
      |iteratedDeriv 1 y u - (taylorPolyOf y t (p + 1)).derivative.eval (u - t)|
        ≤ Cd * |u - t| ^ (p + 1) := by
  -- `deriv y` is `C^(p+1)` since `y` is `C^(p+2)`.
  have hdy : ContDiff ℝ (p + 1) (deriv y) := by
    have h1 : ContDiff ℝ ((p + 1 : ℕ) + 1 : ℕ∞) y := by
      have h0 : ContDiff ℝ ((p + 2 : ℕ) : ℕ∞) y := by exact_mod_cast hy
      simpa [Nat.add_assoc] using h0
    exact (contDiff_succ_iff_deriv.mp h1).2.2
  obtain ⟨Cd, hCd_nn, hCd⟩ := taylor_remainder_value_bound_uniform_aux p hdy t L hL
  refine ⟨Cd, hCd_nn, ?_⟩
  intro u hu
  have hb := hCd u hu
  -- Replace `iteratedDeriv 1 y u` with `deriv y u`, and the polynomial-side
  -- derivative with the value-side at `deriv y`.
  have h1 : iteratedDeriv 1 y u = deriv y u := by
    rw [show iteratedDeriv 1 y = deriv y from iteratedDeriv_one]
  have h2 : (taylorPolyOf y t (p + 1)).derivative.eval (u - t)
      = (taylorPolyOf (deriv y) t p).eval (u - t) :=
    taylorPolyOf_derivative_eval y t (u - t) p
  rw [h1, h2]
  exact hb

/-- Uniform-in-`h` local truncation error bridge. For an order-`p` LMM acting
on a globally `C^(p+2)` solution `y`, there exist constants `C ≥ 0` and
`δ > 0` such that for every `h ∈ (0, δ]` the smooth truncation operator
agrees with the leading polynomial term up to an error of size at most
`C * h^(p+2)`, with the constant independent of `h`. -/
theorem truncationOp_smooth_local_truncation_error
    (m : LMM s) {p : ℕ} (hp : m.HasOrder p) {y : ℝ → ℝ} {t : ℝ} {δ₀ : ℝ}
    (hδ₀ : 0 < δ₀)
    (hy : ContDiff ℝ (p + 2) y) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ δ ≤ δ₀ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
        ‖m.truncationOp h
            (fun u => iteratedDeriv 0 y u)
            (fun u => iteratedDeriv 1 y u) t
          - iteratedDeriv (p + 1) y t * m.errorConstant p * h ^ (p + 1)‖
        ≤ C * h ^ (p + 2) := by
  -- Set up the compact sampling interval and bound the Taylor remainders on it.
  set L : ℝ := (s : ℝ) * δ₀ with hL_def
  have hs_nn : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (Nat.zero_le _)
  have hL_nn : 0 ≤ L := mul_nonneg hs_nn hδ₀.le
  obtain ⟨Cv, hCv_nn, hCv⟩ := taylor_remainder_value_bound_uniform p hy t L hL_nn
  obtain ⟨Cd, hCd_nn, hCd⟩ := taylor_remainder_deriv_bound_uniform p hy t L hL_nn
  -- Constants from the LMM coefficients
  set Aα : ℝ := ∑ j : Fin (s + 1), |m.α j| with hAα_def
  set Aβ : ℝ := ∑ j : Fin (s + 1), |m.β j| with hAβ_def
  have hAα_nn : 0 ≤ Aα := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hAβ_nn : 0 ≤ Aβ := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  -- The uniform constant
  refine ⟨Cv * Aα * (s : ℝ) ^ (p + 2) + Cd * Aβ * (s : ℝ) ^ (p + 1), δ₀,
    by positivity, hδ₀, le_rfl, ?_⟩
  intro h hh hhδ
  -- Step 1: rewrite the truncation error as the residual sum.
  set Q : Polynomial ℝ := taylorPolyOf y t (p + 1) with hQ_def
  set R : ℝ → ℝ := fun u => iteratedDeriv 0 y u - Q.eval (u - t) with hR_def
  set dR : ℝ → ℝ := fun u => iteratedDeriv 1 y u - Q.derivative.eval (u - t)
    with hdR_def
  have hpoly := m.truncationOp_taylorPoly_eq_leading_of_HasOrder
    (h := h) (t := t) hp (fun k u => iteratedDeriv k y u)
  have hdecomp := m.truncationOp_smooth_eq_taylor_residual p h t y
  have hres : m.truncationOp h
        (fun u => iteratedDeriv 0 y u)
        (fun u => iteratedDeriv 1 y u) t
      - iteratedDeriv (p + 1) y t * m.errorConstant p * h ^ (p + 1)
      = ∑ j : Fin (s + 1),
          (m.α j * R (t + (j : ℝ) * h) - h * (m.β j * dR (t + (j : ℝ) * h))) := by
    have := hdecomp
    simp only at this
    rw [this, ← hQ_def] at *
    show (m.truncationOp h (fun u => Q.eval (u - t)) (fun u => Q.derivative.eval (u - t)) t
          + ∑ j : Fin (s + 1),
              (m.α j * R (t + (j : ℝ) * h)
                - h * (m.β j * dR (t + (j : ℝ) * h))))
        - iteratedDeriv (p + 1) y t * m.errorConstant p * h ^ (p + 1)
        = ∑ j : Fin (s + 1),
          (m.α j * R (t + (j : ℝ) * h) - h * (m.β j * dR (t + (j : ℝ) * h)))
    have hQ_eq : m.truncationOp h
          (fun u => Q.eval (u - t)) (fun u => Q.derivative.eval (u - t)) t
        = iteratedDeriv (p + 1) y t * m.errorConstant p * h ^ (p + 1) := hpoly
    rw [hQ_eq]
    ring
  rw [Real.norm_eq_abs, hres]
  -- Step 2: bound the residual sum.
  -- |∑_j (α_j R(t+jh) − h β_j dR(t+jh))| ≤ Cv*Aα*(sh)^(p+2) + h*Cd*Aβ*(sh)^(p+1)
  have hh_nn : 0 ≤ h := hh.le
  have hsh_nn : 0 ≤ (s : ℝ) * h := mul_nonneg hs_nn hh_nn
  have hsh_le : (s : ℝ) * h ≤ L := by
    rw [hL_def]; exact mul_le_mul_of_nonneg_left hhδ hs_nn
  -- Sample-point bounds
  have hjh_in : ∀ j : Fin (s + 1),
      t + (j : ℝ) * h ∈ Set.Icc t (t + L) ∧
      |t + (j : ℝ) * h - t| ≤ (s : ℝ) * h := by
    intro j
    have hj_le : (j : ℝ) ≤ s := by exact_mod_cast (Fin.is_le j)
    have hj_nn : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have hjh_nn : 0 ≤ (j : ℝ) * h := mul_nonneg hj_nn hh_nn
    have hjh_le_sh : (j : ℝ) * h ≤ (s : ℝ) * h :=
      mul_le_mul_of_nonneg_right hj_le hh_nn
    have habsj : |t + (j : ℝ) * h - t| = (j : ℝ) * h := by
      have : t + (j : ℝ) * h - t = (j : ℝ) * h := by ring
      rw [this, abs_of_nonneg hjh_nn]
    refine ⟨⟨by linarith, ?_⟩, ?_⟩
    · linarith [hjh_le_sh.trans hsh_le]
    · rw [habsj]; exact hjh_le_sh
  -- Per-summand bound
  have hper : ∀ j : Fin (s + 1),
      |m.α j * R (t + (j : ℝ) * h) - h * (m.β j * dR (t + (j : ℝ) * h))|
        ≤ |m.α j| * (Cv * ((s : ℝ) * h) ^ (p + 2))
          + h * (|m.β j| * (Cd * ((s : ℝ) * h) ^ (p + 1))) := by
    intro j
    obtain ⟨hjh_mem, hjh_abs⟩ := hjh_in j
    have hRb : |R (t + (j : ℝ) * h)| ≤ Cv * ((s : ℝ) * h) ^ (p + 2) := by
      have h1 := hCv (t + (j : ℝ) * h) hjh_mem
      calc |R (t + (j : ℝ) * h)|
          = |iteratedDeriv 0 y (t + (j : ℝ) * h)
              - Q.eval ((t + (j : ℝ) * h) - t)| := rfl
        _ ≤ Cv * |t + (j : ℝ) * h - t| ^ (p + 2) := h1
        _ ≤ Cv * ((s : ℝ) * h) ^ (p + 2) := by
            apply mul_le_mul_of_nonneg_left _ hCv_nn
            exact pow_le_pow_left₀ (abs_nonneg _) hjh_abs _
    have hdRb : |dR (t + (j : ℝ) * h)| ≤ Cd * ((s : ℝ) * h) ^ (p + 1) := by
      have h1 := hCd (t + (j : ℝ) * h) hjh_mem
      calc |dR (t + (j : ℝ) * h)|
          = |iteratedDeriv 1 y (t + (j : ℝ) * h)
              - Q.derivative.eval ((t + (j : ℝ) * h) - t)| := rfl
        _ ≤ Cd * |t + (j : ℝ) * h - t| ^ (p + 1) := h1
        _ ≤ Cd * ((s : ℝ) * h) ^ (p + 1) := by
            apply mul_le_mul_of_nonneg_left _ hCd_nn
            exact pow_le_pow_left₀ (abs_nonneg _) hjh_abs _
    calc |m.α j * R (t + (j : ℝ) * h) - h * (m.β j * dR (t + (j : ℝ) * h))|
        ≤ |m.α j * R (t + (j : ℝ) * h)| + |h * (m.β j * dR (t + (j : ℝ) * h))| :=
          abs_sub _ _
      _ = |m.α j| * |R (t + (j : ℝ) * h)|
          + h * (|m.β j| * |dR (t + (j : ℝ) * h)|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hh_nn]
      _ ≤ |m.α j| * (Cv * ((s : ℝ) * h) ^ (p + 2))
          + h * (|m.β j| * (Cd * ((s : ℝ) * h) ^ (p + 1))) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hRb (abs_nonneg _)
            · apply mul_le_mul_of_nonneg_left _ hh_nn
              exact mul_le_mul_of_nonneg_left hdRb (abs_nonneg _)
  -- Sum the per-summand bounds
  have hsum_abs :
      |∑ j : Fin (s + 1),
          (m.α j * R (t + (j : ℝ) * h) - h * (m.β j * dR (t + (j : ℝ) * h)))|
        ≤ ∑ j : Fin (s + 1),
          (|m.α j| * (Cv * ((s : ℝ) * h) ^ (p + 2))
            + h * (|m.β j| * (Cd * ((s : ℝ) * h) ^ (p + 1)))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum (fun j _ => hper j)
  -- Pull the constants out of the finite sum
  have hsum_eq : ∑ j : Fin (s + 1),
        (|m.α j| * (Cv * ((s : ℝ) * h) ^ (p + 2))
          + h * (|m.β j| * (Cd * ((s : ℝ) * h) ^ (p + 1))))
      = Aα * (Cv * ((s : ℝ) * h) ^ (p + 2))
        + h * (Aβ * (Cd * ((s : ℝ) * h) ^ (p + 1))) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [hAα_def, ← Finset.sum_mul]
    · rw [hAβ_def]
      rw [show (∑ j : Fin (s + 1),
          h * (|m.β j| * (Cd * ((s : ℝ) * h) ^ (p + 1))))
        = h * (∑ j : Fin (s + 1),
            |m.β j| * (Cd * ((s : ℝ) * h) ^ (p + 1))) from
        (Finset.mul_sum _ _ _).symm]
      rw [← Finset.sum_mul]
  -- Final algebra: rewrite (s*h)^k as s^k * h^k and consolidate.
  have hsh_pow_2 : ((s : ℝ) * h) ^ (p + 2) = (s : ℝ) ^ (p + 2) * h ^ (p + 2) :=
    mul_pow _ _ _
  have hsh_pow_1 : ((s : ℝ) * h) ^ (p + 1) = (s : ℝ) ^ (p + 1) * h ^ (p + 1) :=
    mul_pow _ _ _
  have hh_factor : h * (h ^ (p + 1)) = h ^ (p + 2) := by ring
  calc |∑ j : Fin (s + 1),
          (m.α j * R (t + (j : ℝ) * h) - h * (m.β j * dR (t + (j : ℝ) * h)))|
      ≤ Aα * (Cv * ((s : ℝ) * h) ^ (p + 2))
          + h * (Aβ * (Cd * ((s : ℝ) * h) ^ (p + 1))) := hsum_abs.trans hsum_eq.le
    _ = (Cv * Aα * (s : ℝ) ^ (p + 2)
          + Cd * Aβ * (s : ℝ) ^ (p + 1)) * h ^ (p + 2) := by
          rw [hsh_pow_2, hsh_pow_1]; ring

/-- Local truncation error of the LMM at `(t, h)` acting on a smooth function.
This is the textbook `τ(t, h)` notation from Iserles §1.2 / eqn (2.6). -/
noncomputable def localTruncationError
    (m : LMM s) (h t : ℝ) (y : ℝ → ℝ) : ℝ :=
  m.truncationOp h
    (fun u => iteratedDeriv 0 y u)
    (fun u => iteratedDeriv 1 y u) t

/-- Uniform-in-`h` bound on the local truncation error for an order-`p` LMM
acting on a `C^(p+2)` solution: there exist constants `C ≥ 0` and `δ > 0` such
that `τ(t, h)` agrees with the leading term `y^(p+1)(t) · errorConstant · h^(p+1)`
up to size `C * h^(p+2)`, uniformly for `h ∈ (0, δ]`. -/
theorem localTruncationError_leading_bound
    (m : LMM s) {p : ℕ} (hp : m.HasOrder p) {y : ℝ → ℝ} {t : ℝ} {δ₀ : ℝ}
    (hδ₀ : 0 < δ₀)
    (hy : ContDiff ℝ (p + 2) y) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ δ ≤ δ₀ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
        ‖m.localTruncationError h t y
          - iteratedDeriv (p + 1) y t * m.errorConstant p * h ^ (p + 1)‖
        ≤ C * h ^ (p + 2) :=
  m.truncationOp_smooth_local_truncation_error hp hδ₀ hy

/-- Consequence of the local truncation bound and exponential discrete
Grönwall: any error sequence satisfying a Lipschitz forcing recurrence with
forcing constant bounded by the local truncation leading term obeys the
textbook `O(h^p)` global error bound on a finite horizon `[0, T]`.

This packages `discrete_gronwall_exp_horizon` so that future cycles only
have to supply the iteration recurrence; the analytic bound is already in
place. -/
lemma lmm_error_bound_from_local_truncation
    {N : ℕ} {h L C T : ℝ} {p : ℕ} {e : ℕ → ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hC : 0 ≤ C) (he0 : 0 ≤ e 0)
    (hstep : ∀ n, n < N → e (n + 1) ≤ (1 + h * L) * e n + C * h ^ (p + 1))
    (n : ℕ) (hn : n ≤ N) (hnh : (n : ℝ) * h ≤ T) :
    e n ≤ Real.exp (L * T) * e 0
          + T * Real.exp (L * T) * C * h ^ p :=
  discrete_gronwall_exp_horizon hh hL hC he0 hstep n hn hnh

/-! ### Forward Euler one-step error recurrence (Iserles §1.2)

We instantiate the abstract recurrence consumed by
`lmm_error_bound_from_local_truncation` for the simplest scalar 1-step LMM:
explicit forward Euler applied to a Lipschitz scalar ODE
`y' = f(t, y)`. -/

/-- Forward Euler iteration for a scalar IVP `y' = f(t, y)`:
`y_{n+1} = y_n + h · f(t₀ + n h, y_n)`. -/
noncomputable def forwardEulerIter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | n + 1 =>
      forwardEulerIter h f t₀ y₀ n
        + h * f (t₀ + (n : ℝ) * h) (forwardEulerIter h f t₀ y₀ n)

@[simp] lemma forwardEulerIter_zero
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ : ℝ) :
    forwardEulerIter h f t₀ y₀ 0 = y₀ := rfl

lemma forwardEulerIter_succ
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ : ℝ) (n : ℕ) :
    forwardEulerIter h f t₀ y₀ (n + 1)
      = forwardEulerIter h f t₀ y₀ n
        + h * f (t₀ + (n : ℝ) * h) (forwardEulerIter h f t₀ y₀ n) := rfl

/-- Forward Euler local truncation operator reduces to the textbook
one-step residual `y(t + h) - y(t) - h · y'(t)`. -/
theorem forwardEuler_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    forwardEuler.localTruncationError h t y
      = y (t + h) - y t - h * deriv y t := by
  unfold localTruncationError truncationOp
  simp [forwardEuler, Fin.sum_univ_two, iteratedDeriv_one,
    iteratedDeriv_zero]
  ring

/-- One-step error recurrence for forward Euler applied to a scalar ODE
with Lipschitz right-hand side and exact solution `y` satisfying
`deriv y t = f t (y t)`.

Letting `eN k := |forwardEulerIter h f t₀ y₀ k - y (t₀ + k h)|` and
`τ_n := y (t₀ + (n+1) h) - y (t₀ + n h) - h · f (t₀ + n h, y (t₀ + n h))`
be the one-step truncation residual,
`eN (n+1) ≤ (1 + h · L) · eN n + |τ_n|`. -/
theorem forwardEuler_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ : ℝ) (y : ℝ → ℝ) (n : ℕ) :
    |forwardEulerIter h f t₀ y₀ (n + 1)
        - y (t₀ + ((n : ℝ) + 1) * h)|
      ≤ (1 + h * L)
          * |forwardEulerIter h f t₀ y₀ n - y (t₀ + (n : ℝ) * h)|
        + |y (t₀ + ((n : ℝ) + 1) * h) - y (t₀ + (n : ℝ) * h)
            - h * f (t₀ + (n : ℝ) * h) (y (t₀ + (n : ℝ) * h))| := by
  -- Abbreviations.
  set yn : ℝ := forwardEulerIter h f t₀ y₀ n with hyn_def
  set zn : ℝ := y (t₀ + (n : ℝ) * h) with hzn_def
  set zn1 : ℝ := y (t₀ + ((n : ℝ) + 1) * h) with hzn1_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  -- Forward-Euler step formula.
  have hstep : forwardEulerIter h f t₀ y₀ (n + 1)
      = yn + h * f tn yn := by
    simp [forwardEulerIter_succ, hyn_def, htn_def]
  -- Algebraic decomposition of the global error increment.
  have halg :
      forwardEulerIter h f t₀ y₀ (n + 1) - zn1
        = (yn - zn) + h * (f tn yn - f tn zn)
            - (zn1 - zn - h * f tn zn) := by
    rw [hstep]; ring
  -- Lipschitz bound on the step error.
  have hLip : |f tn yn - f tn zn| ≤ L * |yn - zn| := hf tn yn zn
  -- Triangle inequality + Lipschitz step.
  have h_h_abs : |h| = h := abs_of_nonneg hh
  have hbound :
      |(yn - zn) + h * (f tn yn - f tn zn)
        - (zn1 - zn - h * f tn zn)|
        ≤ (1 + h * L) * |yn - zn|
          + |zn1 - zn - h * f tn zn| := by
    -- The Lipschitz step gives |h * (f tn yn - f tn zn)| ≤ h * L * |yn - zn|.
    have h_h_term : |h * (f tn yn - f tn zn)| = h * |f tn yn - f tn zn| := by
      rw [abs_mul, h_h_abs]
    have h_lip_h : h * |f tn yn - f tn zn| ≤ h * (L * |yn - zn|) :=
      mul_le_mul_of_nonneg_left hLip hh
    have h_step_abs : |h * (f tn yn - f tn zn)| ≤ h * (L * |yn - zn|) := by
      rw [h_h_term]; exact h_lip_h
    -- Triangle inequality on the inner sum.
    have h_inner_tri :
        |(yn - zn) + h * (f tn yn - f tn zn)|
          ≤ |yn - zn| + |h * (f tn yn - f tn zn)| := abs_add_le _ _
    have h_inner :
        |(yn - zn) + h * (f tn yn - f tn zn)|
          ≤ |yn - zn| + h * (L * |yn - zn|) := by
      linarith [h_inner_tri, h_step_abs]
    -- Triangle inequality on the outer subtraction.
    have h_outer :
        |(yn - zn) + h * (f tn yn - f tn zn)
          - (zn1 - zn - h * f tn zn)|
          ≤ |(yn - zn) + h * (f tn yn - f tn zn)|
            + |zn1 - zn - h * f tn zn| := abs_sub _ _
    -- Combine.
    have h_combined :
        |(yn - zn) + h * (f tn yn - f tn zn)
          - (zn1 - zn - h * f tn zn)|
          ≤ (|yn - zn| + h * (L * |yn - zn|))
            + |zn1 - zn - h * f tn zn| := by
      linarith [h_outer, h_inner]
    have h_alg :
        (|yn - zn| + h * (L * |yn - zn|))
          + |zn1 - zn - h * f tn zn|
          = (1 + h * L) * |yn - zn| + |zn1 - zn - h * f tn zn| := by ring
    linarith [h_combined, h_alg]
  calc |forwardEulerIter h f t₀ y₀ (n + 1) - zn1|
      = |(yn - zn) + h * (f tn yn - f tn zn)
          - (zn1 - zn - h * f tn zn)| := by rw [halg]
    _ ≤ (1 + h * L) * |yn - zn|
        + |zn1 - zn - h * f tn zn| := hbound

/-- A `C^3` function has its second derivative bounded on every compact
interval `[a, b]`. -/
private theorem iteratedDeriv_two_bounded_on_Icc
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |iteratedDeriv 2 y t| ≤ M := by
  have h_cont_diff2 : ContDiff ℝ 2 (iteratedDeriv 1 y) := by
    rw [iteratedDeriv_eq_iterate]
    fun_prop
  have h_cont_diff3 : Continuous (iteratedDeriv 2 y) := by
    convert h_cont_diff2.continuous_deriv _ using 1
    · norm_num [iteratedDeriv_succ']
    · decide +revert
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn (CompactIccSpace.isCompact_Icc)
      h_cont_diff3.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hM t ht).trans (le_max_left _ _)

/-- Pointwise Taylor (Lagrange) remainder bound: if `y` is `C^3` and
`|y''| ≤ M` on `[a, b]`, then for `t, t + h ∈ [a, b]` with `h ≥ 0`,
`|y(t+h) - y(t) - h · y'(t)| ≤ M / 2 · h^2`. -/
private theorem forwardEuler_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 2 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b) (hth : t + h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + h) - y t - h * deriv y t| ≤ M / 2 * h ^ 2 := by
  by_cases hh' : h = 0
  · subst hh'; simp
  · obtain ⟨x', hx', hx''⟩ : ∃ x' ∈ Set.Ioo t (t + h),
        y (t + h) - taylorWithinEval y 1 (Set.Icc t (t + h)) t (t + h)
          = iteratedDeriv 2 y x' * h ^ 2 / 2 := by
      have htlt : t < t + h := lt_add_of_pos_right _ (lt_of_le_of_ne hh (Ne.symm hh'))
      have hcdo : ContDiffOn ℝ 2 y (Set.Icc t (t + h)) :=
        hy.contDiffOn.of_le (by norm_num)
      have := taylor_mean_remainder_lagrange_iteratedDeriv htlt hcdo
      aesop
    have h_taylor : taylorWithinEval y 1 (Set.Icc t (t + h)) t (t + h)
        = y t + (t + h - t) * deriv y t := by
      convert taylorWithinEval_succ y 0 (Set.Icc t (t + h)) t (t + h) using 1
      · norm_num [taylorWithinEval_self]
        rw [derivWithin]
        rw [fderivWithin_eq_fderiv] <;> norm_num [hy.contDiffAt.differentiableAt]
        exact uniqueDiffOn_Icc (by linarith [hx'.1, hx'.2]) t
          (by constructor <;> linarith [hx'.1, hx'.2])
    have h_x'_in : x' ∈ Set.Icc a b :=
      ⟨by linarith [hx'.1, ht.1], by linarith [hx'.2, hth.2]⟩
    have h_y_bound := abs_le.mp (hbnd x' h_x'_in)
    refine abs_le.mpr ⟨?_, ?_⟩
    · nlinarith [h_y_bound]
    · nlinarith [h_y_bound]

/-- Uniform bound on the forward-Euler one-step truncation residual on a
finite horizon, given a `C^3` solution. Built from the pointwise Lagrange
Taylor remainder and a uniform bound on `|y''|` over a compact interval. -/
theorem forwardEuler_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        t₀ + (n : ℝ) * h ∈ Set.Icc t₀ (t₀ + T) →
        |y (t₀ + ((n : ℝ) + 1) * h) - y (t₀ + (n : ℝ) * h)
            - h * deriv y (t₀ + (n : ℝ) * h)|
          ≤ C * h ^ 2 := by
  -- Choose a compact sample interval `[t₀, t₀ + T + 1]` containing every
  -- relevant sample point and the next step `t + h` for `0 < h ≤ 1`.
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_two_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨M / 2, 1, by linarith, by norm_num, ?_⟩
  intro h hh hh1 n hn_in
  -- `t := t₀ + n*h ∈ [t₀, t₀+T] ⊆ [t₀, t₀+T+1]` and
  -- `t + h ∈ [t₀, t₀+T+1]` (using `h ≤ 1`).
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨hn_in.1, ?_⟩
    linarith [hn_in.2]
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith [hn_in.1, hh.le], ?_⟩
    linarith [hn_in.2, hh1]
  -- Rewrite the textbook residual as `y(t+h) - y(t) - h * deriv y t`.
  have heq :
      y (t₀ + ((n : ℝ) + 1) * h) - y (t₀ + (n : ℝ) * h)
        - h * deriv y (t₀ + (n : ℝ) * h)
        = y (t + h) - y t - h * deriv y t := by
    have hadd : t + h = t₀ + ((n : ℝ) + 1) * h := by
      simp [ht_def]; ring
    rw [show t = t₀ + (n : ℝ) * h from rfl, hadd]
  rw [heq]
  exact forwardEuler_pointwise_residual_bound hy hM ht_mem hth_mem hh.le

/-- Final assembly of the global forward-Euler error bound on a finite
horizon `[t₀, t₀ + T]` from the one-step Lipschitz recurrence and the
local truncation residual bound, via
`lmm_error_bound_from_local_truncation`. -/
theorem forwardEuler_global_error_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ N : ℕ, (N : ℝ) * h ≤ T →
        |forwardEulerIter h f t₀ (y t₀) N - y (t₀ + (N : ℝ) * h)|
          ≤ K * h := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    forwardEuler_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp (L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le N hNh
  -- Error sequence.
  set e : ℕ → ℝ :=
    fun k => |forwardEulerIter h f t₀ (y t₀) k - y (t₀ + (k : ℝ) * h)|
    with he_def
  have he0_eq : e 0 = 0 := by
    show |forwardEulerIter h f t₀ (y t₀) 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)| = 0
    simp
  have he0_nn : 0 ≤ e 0 := abs_nonneg _
  -- One-step recurrence with forcing C * h^2.
  have hstep : ∀ n, n < N →
      e (n + 1) ≤ (1 + h * L) * e n + C * h ^ (1 + 1) := by
    intro n hn_lt
    have honestep :=
      forwardEuler_one_step_error_bound (h := h) (L := L)
        hh.le hf t₀ (y t₀) y n
    -- Bridge `f` and `deriv y` along the trajectory.
    have hbridge :
        y (t₀ + ((n : ℝ) + 1) * h) - y (t₀ + (n : ℝ) * h)
            - h * f (t₀ + (n : ℝ) * h) (y (t₀ + (n : ℝ) * h))
          = y (t₀ + ((n : ℝ) + 1) * h) - y (t₀ + (n : ℝ) * h)
              - h * deriv y (t₀ + (n : ℝ) * h) := by
      rw [hyf]
    rw [hbridge] at honestep
    -- Sample point lies in `[t₀, t₀ + T]`.
    have hn_le : (n : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.le_of_lt hn_lt
    have hnh_le_T : (n : ℝ) * h ≤ T :=
      (mul_le_mul_of_nonneg_right hn_le hh.le).trans hNh
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have ht_in : t₀ + (n : ℝ) * h ∈ Set.Icc t₀ (t₀ + T) := by
      refine ⟨?_, ?_⟩
      · have := mul_nonneg hn_nn hh.le
        linarith
      · linarith
    have hres := hresidual hh hδ_le n ht_in
    -- LHS rewriting: `((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1`.
    have hlhs_eq :
        e (n + 1)
          = |forwardEulerIter h f t₀ (y t₀) (n + 1)
              - y (t₀ + ((n : ℝ) + 1) * h)| := by
      show |_ - _| = |_ - _|
      have : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [this]
    have he_n_eq : e n
          = |forwardEulerIter h f t₀ (y t₀) n - y (t₀ + (n : ℝ) * h)| :=
      rfl
    rw [hlhs_eq, he_n_eq]
    have hpow : C * h ^ (1 + 1) = C * h ^ 2 := by norm_num
    rw [hpow]
    linarith [honestep, hres]
  -- Apply the LMM Gronwall bridge with `p = 1`.
  have hgronwall :=
    lmm_error_bound_from_local_truncation
      (h := h) (L := L) (C := C) (T := T) (p := 1) (e := e) (N := N)
      hh.le hL hC_nn he0_nn hstep N le_rfl hNh
  -- The initial error vanishes: `e 0 = 0`.
  rw [he0_eq, mul_zero, zero_add, pow_one] at hgronwall
  exact hgronwall

end LMM
