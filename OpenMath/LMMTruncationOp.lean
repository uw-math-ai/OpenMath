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

end LMM
