import Mathlib

/-!
# Theorem 212A: Global Truncation Error Bound for the Euler Method

We formalize Theorem 212A from Butcher's *Numerical Methods for Ordinary Differential
Equations* (2nd ed., Section 212, pp. 66–68).

The theorem bounds the global error of the Euler method for an ODE `y' = f(x, y)` where `f`
satisfies a Lipschitz condition with constant `L`. The bound is expressed in terms of the
initial error, the Lipschitz constant, and a uniform bound on the local truncation error.

The mathematical core is a discrete Gronwall-type inequality: given a nonneg sequence `a`
satisfying `a(i+1) ≤ (1 + h(i) * L) * a(i) + h(i) * C`, we bound `a(n)` by
`gronwallBound (a 0) L C (∑ h(i))`.
-/

open Finset Real

/-- Geometric recurrence bound: if `b(i+1) ≤ c(i) * b(i)` with nonneg sequences,
then `b(n) ≤ (∏ c(i)) * b(0)`. -/
lemma seq_le_prod_mul (b c : ℕ → ℝ) (n : ℕ)
    (hb_nonneg : ∀ i, i ≤ n → 0 ≤ b i)
    (hc_nonneg : ∀ i, i < n → 0 ≤ c i)
    (hrec : ∀ i, i < n → b (i + 1) ≤ c i * b i) :
    b n ≤ (∏ i ∈ range n, c i) * b 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' : b n ≤ (∏ i ∈ range n, c i) * b 0 :=
      ih (fun i hi => hb_nonneg i (Nat.le_succ_of_le hi))
        (fun i hi => hc_nonneg i (Nat.lt_succ_of_lt hi))
        (fun i hi => hrec i (Nat.lt_succ_of_lt hi))
    calc b (n + 1)
        ≤ c n * b n := hrec n (Nat.lt_succ_iff.mpr le_rfl)
      _ ≤ c n * ((∏ i ∈ range n, c i) * b 0) :=
          mul_le_mul_of_nonneg_left ih' (hc_nonneg n (Nat.lt_succ_iff.mpr le_rfl))
      _ = (∏ i ∈ range (n + 1), c i) * b 0 := by
          rw [prod_range_succ]; ring

/-- **Theorem 212A, Case L = 0**: When the Lipschitz constant is zero, the global error
grows at most linearly in the total step length. -/
theorem euler_error_bound_L_eq_zero
    (a h : ℕ → ℝ) (C : ℝ) (n : ℕ)
    (hrec : ∀ i, i < n → a (i + 1) ≤ a i + h i * C) :
    a n ≤ a 0 + C * ∑ i ∈ range n, h i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' : a n ≤ a 0 + C * ∑ i ∈ range n, h i :=
      ih (fun i hi => hrec i (Nat.lt_succ_of_lt hi))
    calc a (n + 1)
        ≤ a n + h n * C := hrec n (Nat.lt_succ_iff.mpr le_rfl)
      _ ≤ (a 0 + C * ∑ i ∈ range n, h i) + h n * C := by linarith
      _ = a 0 + C * ∑ i ∈ range (n + 1), h i := by
          rw [sum_range_succ]; ring

/-- **Theorem 212A, Case L > 0**: When the Lipschitz constant is positive, the global error
grows at most exponentially. The bound uses `gronwallBound` from Mathlib. -/
theorem euler_error_bound_L_pos
    (a h : ℕ → ℝ) (L C : ℝ) (n : ℕ)
    (ha_nonneg : ∀ i, i ≤ n → 0 ≤ a i)
    (hh_nonneg : ∀ i, 0 ≤ h i)
    (hC_nonneg : 0 ≤ C)
    (hL_pos : 0 < L)
    (hrec : ∀ i, i < n → a (i + 1) ≤ (1 + h i * L) * a i + h i * C) :
    a n ≤ a 0 * exp (L * ∑ i ∈ range n, h i) +
          C / L * (exp (L * ∑ i ∈ range n, h i) - 1) := by
  -- Transform using b(i) = a(i) + C/L, which satisfies b(i+1) ≤ (1 + h(i)*L) * b(i)
  suffices a n + C / L ≤ exp (L * ∑ i ∈ range n, h i) * (a 0 + C / L) by
    nlinarith [mul_comm (a 0) (exp (L * ∑ i ∈ range n, h i))]
  -- Define auxiliary sequences
  set b : ℕ → ℝ := fun i => a i + C / L
  set c : ℕ → ℝ := fun i => 1 + h i * L
  -- b(i) ≥ 0
  have hb_nonneg : ∀ i, i ≤ n → 0 ≤ b i := fun i hi =>
    add_nonneg (ha_nonneg i hi) (div_nonneg hC_nonneg (le_of_lt hL_pos))
  -- c(i) ≥ 0
  have hc_nonneg : ∀ i, i < n → 0 ≤ c i := fun i _ =>
    le_trans zero_le_one (le_add_of_nonneg_right (mul_nonneg (hh_nonneg i) (le_of_lt hL_pos)))
  -- b(i+1) ≤ c(i) * b(i)
  have hb_rec : ∀ i, i < n → b (i + 1) ≤ c i * b i := by
    intro i hi
    show a (i + 1) + C / L ≤ (1 + h i * L) * (a i + C / L)
    have ha_rec := hrec i hi
    have hL_ne : L ≠ 0 := ne_of_gt hL_pos
    have key : (1 + h i * L) * (a i + C / L) =
               (1 + h i * L) * a i + C / L + h i * C := by
      field_simp; ring
    linarith
  -- Product bound: b(n) ≤ (∏ c(i)) * b(0)
  have hb_bound := seq_le_prod_mul b c n hb_nonneg hc_nonneg hb_rec
  -- Product ≤ exp(sum): ∏(1 + h(i)*L) ≤ exp(∑ h(i)*L) = exp(L * ∑ h(i))
  have hprod_le : ∏ i ∈ range n, c i ≤ exp (L * ∑ i ∈ range n, h i) :=
    calc ∏ i ∈ range n, c i
        ≤ ∏ i ∈ range n, exp (h i * L) := by
          apply prod_le_prod
          · intro i _; linarith [mul_nonneg (hh_nonneg i) (le_of_lt hL_pos)]
          · intro i _; linarith [add_one_le_exp (h i * L)]
      _ = exp (∑ i ∈ range n, h i * L) := (exp_sum _ _).symm
      _ = exp (L * ∑ i ∈ range n, h i) := by
          congr 1; rw [Finset.mul_sum]; congr 1; ext i; ring
  -- Combine
  calc a n + C / L = b n := rfl
    _ ≤ (∏ i ∈ range n, c i) * b 0 := hb_bound
    _ ≤ exp (L * ∑ i ∈ range n, h i) * b 0 :=
        mul_le_mul_of_nonneg_right hprod_le (hb_nonneg 0 (Nat.zero_le n))
    _ = exp (L * ∑ i ∈ range n, h i) * (a 0 + C / L) := rfl

/-- **Theorem 212A (Global Error Bound for the Euler Method).**

If a nonneg sequence `a` satisfies the recurrence
`a(i+1) ≤ (1 + h(i) * L) * a(i) + h(i) * C` where `L ≥ 0` is the Lipschitz constant
and `C ≥ 0` bounds the local truncation error, then:
- When `L = 0`: `a(n) ≤ a(0) + C * ∑ h(i)` (linear growth).
- When `L > 0`: `a(n) ≤ exp(L·S)·a(0) + (exp(L·S) - 1)/L · C` (exponential growth).

This matches Mathlib's `gronwallBound` definition. -/
theorem theorem_212A (a h : ℕ → ℝ) (L C : ℝ) (n : ℕ)
    (ha_nonneg : ∀ i, i ≤ n → 0 ≤ a i)
    (hh_nonneg : ∀ i, 0 ≤ h i)
    (hC_nonneg : 0 ≤ C)
    (hL_nonneg : 0 ≤ L)
    (hrec : ∀ i, i < n → a (i + 1) ≤ (1 + h i * L) * a i + h i * C) :
    a n ≤ gronwallBound (a 0) L C (∑ i ∈ range n, h i) := by
  rcases eq_or_lt_of_le hL_nonneg with rfl | hL_pos
  · -- Case L = 0
    simp only [gronwallBound, ite_true]
    exact euler_error_bound_L_eq_zero a h C n
      (by simpa using hrec)
  · -- Case L > 0
    simp only [gronwallBound, ne_of_gt hL_pos, ite_false]
    exact euler_error_bound_L_pos a h L C n ha_nonneg hh_nonneg hC_nonneg hL_pos hrec
