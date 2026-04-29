import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import OpenMath.Chapter1.Section140

/-!
# Butcher §141 — Constant coefficients

This file formalizes Butcher §141, which solves the scalar
order-`k` constant-coefficient inhomogeneous linear difference
equation

  `y_n = α_1 y_{n-1} + α_2 y_{n-2} + ⋯ + α_k y_{n-k} + ψ_n`        (141a)

with given initial values `y_0, …, y_{k-1}`. The closed-form solution
(141c) is

  `y_n = Σ_{i=0}^{k-1} θ_{n-i} y'_i  +  Σ_{i=k}^{n} θ_{n-i} ψ_i`,

where `θ` is the *canonical impulse response* (the solution with
`θ_0 = 1`, `θ_m = 0` for `m < 0`) and `y'_i` are transformed initial
values via the upper-triangular system (141b).

## Index-mechanics note

In Butcher, `θ_m = 0` for `m < 0` by convention, so the upper limit
`i = k - 1` in `Σ_{i=0}^{k-1} θ_{n-i} y'_i` is "always safe" — the
extra terms vanish. With ℕ-indexed `θ`, however, `n - i = 0` for
`i ≥ n`, where `θ 0 = 1`, not `0`. To stay faithful to the textbook
statement under ℕ indexing, we replace the upper limit `k - 1` with
`min (k - 1) n`, equivalently summing over `range (min k (n + 1))`.
This is mathematically identical to Butcher's formula in the
overlapping range `0 ≤ i ≤ k - 1, i ≤ n`; for `i > n`, the textbook's
`θ_{n-i}` would be `0`, contributing nothing.
-/

namespace OpenMath.Chapter1.Section141

open Finset

variable {R : Type*} [Ring R]

/-- The scalar order-`k` constant-coefficient inhomogeneous recurrence
(141a): `y_n = α_1 y_{n-1} + ⋯ + α_k y_{n-k} + ψ_n` for `n ≥ k`,
with prescribed initial values `y_i = y₀init i` for `i : Fin k`.

`α j = α_{j+1}` (so `α : Fin k → R` carries the `k` coefficients
`α_1, …, α_k`); `ψ : ℕ → R` is the inhomogeneous input. -/
noncomputable def linRec (k : ℕ) (α : Fin k → R) (y₀init : Fin k → R)
    (ψ : ℕ → R) : ℕ → R
  | n =>
    if h : n < k then y₀init ⟨n, h⟩
    else (∑ j : Fin k, α j * linRec k α y₀init ψ (n - 1 - j.val)) + ψ n
termination_by n => n
decreasing_by
  have _hk : k ≤ n := Nat.le_of_not_lt h
  have _hj : j.val < k := j.isLt
  omega

/-- The canonical impulse response `θ : ℕ → R`. By convention
`θ_m = 0` for `m < 0` (not modeled here — see file docstring), and:
`θ_0 = 1`; for `n ≥ 1`,
`θ_n = α_1 θ_{n-1} + α_2 θ_{n-2} + ⋯ + α_{min(n,k)} θ_{n-min(n,k)}`.

We encode the convention `θ_m = 0` for `m < 0` by guarding each
α-coefficient term with the predicate `j.val ≤ n` in the recurrence:
when `j.val > n`, the corresponding `θ_{n - j}` would be at a
negative index in the textbook, so we contribute `0`. -/
noncomputable def theta (k : ℕ) (α : Fin k → R) : ℕ → R
  | 0     => 1
  | n + 1 => ∑ j : Fin k, if j.val ≤ n then α j * theta k α (n - j.val) else 0
termination_by n => n
decreasing_by
  omega

/-- Transformed initial data `y'` defined recursively from the
upper-triangular system (141b):
`y'_0 = y_0`, `y'_m = y_m - Σ_{i=0}^{m-1} θ_{m-i} y'_i`.

We extend by zero for `m ≥ k`; only `m : Fin k` is mathematically
meaningful. -/
noncomputable def yPrime (k : ℕ) (α : Fin k → R) (y₀init : Fin k → R) :
    ℕ → R
  | m =>
    if h : m < k then
      y₀init ⟨m, h⟩ -
        ∑ i : Fin m, theta k α (m - i.val) * yPrime k α y₀init i.val
    else 0
termination_by m => m
decreasing_by
  exact i.isLt

/-- The recurrence (141a) at indices `i < k`: `linRec` returns the
prescribed initial value `y₀init ⟨i, h⟩`. -/
@[simp]
lemma linRec_of_lt (k : ℕ) (α : Fin k → R) (y₀init : Fin k → R)
    (ψ : ℕ → R) (i : ℕ) (h : i < k) :
    linRec k α y₀init ψ i = y₀init ⟨i, h⟩ := by
  rw [linRec]
  exact dif_pos h

/-- The recurrence (141a) at indices `n ≥ k`. -/
lemma linRec_of_ge (k : ℕ) (α : Fin k → R) (y₀init : Fin k → R)
    (ψ : ℕ → R) (n : ℕ) (h : k ≤ n) :
    linRec k α y₀init ψ n
      = (∑ j : Fin k, α j * linRec k α y₀init ψ (n - 1 - j.val)) + ψ n := by
  rw [linRec]
  exact dif_neg (Nat.not_lt.mpr h)

@[simp]
lemma theta_zero (k : ℕ) (α : Fin k → R) : theta k α 0 = 1 := by
  rw [theta]

lemma theta_succ (k : ℕ) (α : Fin k → R) (n : ℕ) :
    theta k α (n + 1)
      = ∑ j : Fin k, if j.val ≤ n then α j * theta k α (n - j.val) else 0 := by
  rw [theta]

/-- Equation lemma for `yPrime` at indices `m < k`. -/
lemma yPrime_of_lt (k : ℕ) (α : Fin k → R) (y₀init : Fin k → R)
    (m : ℕ) (h : m < k) :
    yPrime k α y₀init m
      = y₀init ⟨m, h⟩ -
        ∑ i : Fin m, theta k α (m - i.val) * yPrime k α y₀init i.val := by
  rw [yPrime]
  exact dif_pos h

/-- For indices `m ≥ k`, `yPrime` is zero (extension by zero). -/
lemma yPrime_of_ge (k : ℕ) (α : Fin k → R) (y₀init : Fin k → R)
    (m : ℕ) (h : k ≤ m) : yPrime k α y₀init m = 0 := by
  rw [yPrime]
  exact dif_neg (Nat.not_lt.mpr h)

/-- The (141b) recovery identity: for each `m < k`, the original
initial value `y_m` is recovered from `y'_0, …, y'_m` via
`y_m = Σ_{i=0}^{m} θ_{m-i} y'_i`. -/
lemma yPrime_recover (k : ℕ) (α : Fin k → R) (y₀init : Fin k → R)
    (m : ℕ) (h : m < k) :
    y₀init ⟨m, h⟩
      = ∑ i ∈ Finset.range (m + 1),
          theta k α (m - i) * yPrime k α y₀init i := by
  rw [Finset.sum_range_succ, Nat.sub_self, theta_zero, one_mul,
      ← Fin.sum_univ_eq_sum_range
        (fun i => theta k α (m - i) * yPrime k α y₀init i) m,
      yPrime_of_lt k α y₀init m h]
  abel

/-- The `n < k` case of `linRec_closed_form` (i.e., the initial-value
range): `linRec` returns `y₀init ⟨n, hn⟩`, which by the (141b)
recovery identity equals the truncated first sum. The second sum is
empty since `Icc k n = ∅` for `n < k`. -/
private lemma linRec_closed_form_lt
    (k : ℕ) (α : Fin k → R) (y₀init : Fin k → R) (ψ : ℕ → R)
    (n : ℕ) (hn : n < k) :
    linRec k α y₀init ψ n
      = (∑ i ∈ Finset.range (min k (n + 1)),
            theta k α (n - i) * yPrime k α y₀init i)
        + ∑ i ∈ Finset.Icc k n, theta k α (n - i) * ψ i := by
  rw [linRec_of_lt k α y₀init ψ n hn]
  have hicc : Finset.Icc k n = (∅ : Finset ℕ) :=
    Finset.Icc_eq_empty (by omega)
  rw [hicc, Finset.sum_empty, add_zero]
  have hmin : min k (n + 1) = n + 1 := by omega
  rw [hmin]
  exact yPrime_recover k α y₀init n hn

/-- The "inner sum" identity: for any `m ≥ 1`,
`Σ j : Fin k, [j ≤ m-1] α j θ_{m-1-j} = θ_m`. This is just
`theta_succ` applied at index `(m - 1) + 1 = m`. -/
private lemma theta_inner_sum
    (k : ℕ) (α : Fin k → R) (m : ℕ) (hm : 1 ≤ m) :
    (∑ j : Fin k, if j.val ≤ m - 1 then α j * theta k α (m - 1 - j.val)
                    else 0)
      = theta k α m := by
  conv_rhs => rw [show m = (m - 1) + 1 from (Nat.sub_add_cancel hm).symm]
  rw [theta_succ]

/-- The "shifted recurrence" form of `theta_succ`: for any `n` and
`i < n`, the inner sum
`Σ j : Fin k, [j + i < n] α j θ_{n-1-i-j}` equals `θ_{n-i}`.

This is `theta_inner_sum` applied at index `m = n - i`, after
recognizing that `j + i < n ↔ j ≤ (n-i) - 1 = n - 1 - i` and
`n - 1 - i - j.val = (n - i) - 1 - j.val`. -/
private lemma theta_recurrence_at
    (k : ℕ) (α : Fin k → R) (n i : ℕ) (hi : i < n) :
    (∑ j : Fin k, if j.val + i < n then
                    α j * theta k α (n - 1 - i - j.val) else 0)
      = theta k α (n - i) := by
  have h1 : 1 ≤ n - i := by omega
  rw [← theta_inner_sum k α (n - i) h1]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hcond : j.val + i < n
  · have hcond2 : j.val ≤ n - i - 1 := by omega
    rw [if_pos hcond, if_pos hcond2]
    congr 2
    omega
  · have hcond2 : ¬ j.val ≤ n - i - 1 := by omega
    rw [if_neg hcond, if_neg hcond2]

/-- For `k = 0`, `theta 0 α m` is `1` at `m = 0` and `0` for `m ≥ 1`. -/
private lemma theta_k_zero_eq (α : Fin 0 → R) (m : ℕ) :
    theta 0 α m = if m = 0 then 1 else 0 := by
  cases m with
  | zero => simp
  | succ m =>
    rw [theta_succ]
    simp [Finset.univ_eq_empty]

/-- For `k = 0`, the closed-form equals `ψ n` since the first sum is
empty and the second sum collapses (only `i = n` contributes a
nonzero `θ_{n-i} = θ_0 = 1`). -/
private lemma linRec_closed_form_k_zero
    (α : Fin 0 → R) (y₀init : Fin 0 → R) (ψ : ℕ → R) (n : ℕ) :
    linRec 0 α y₀init ψ n
      = (∑ i ∈ Finset.range (min 0 (n + 1)),
            theta 0 α (n - i) * yPrime 0 α y₀init i)
        + ∑ i ∈ Finset.Icc 0 n, theta 0 α (n - i) * ψ i := by
  have hzero : min 0 (n + 1) = 0 := Nat.min_eq_left (Nat.zero_le _)
  rw [hzero, Finset.range_zero, Finset.sum_empty, zero_add]
  -- Show linRec 0 ... n = ψ n
  have hlin : linRec 0 α y₀init ψ n = ψ n := by
    rw [linRec_of_ge 0 α y₀init ψ n (Nat.zero_le _)]
    simp
  rw [hlin]
  -- Show Σ i ∈ Icc 0 n, theta 0 α (n - i) * ψ i = ψ n
  have hicc_range : Finset.Icc 0 n = Finset.range (n + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_range, Nat.zero_le, true_and]
    omega
  rw [hicc_range]
  rw [Finset.sum_eq_single n]
  · simp
  · intro i hi hi_ne
    rw [Finset.mem_range] at hi
    have hne : n - i ≠ 0 := by omega
    rw [theta_k_zero_eq, if_neg hne, zero_mul]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.lt_succ_self n))).elim

/-- Swap helper for the `y'` part. For `0 < k ≤ n`,
`Σ j : Fin k, α j * Σ_{i ∈ range (min k (n - j.val))} θ_{m_j-i} y'_i
  = Σ_{i ∈ range k} θ_{n-i} y'_i`. -/
private lemma sum_swap_yprime
    (k : ℕ) (α : Fin k → R) (y₀init : Fin k → R)
    (n : ℕ) (_hkpos : 0 < k) (hn : k ≤ n) :
    (∑ j : Fin k, α j *
        ∑ i ∈ Finset.range (min k (n - 1 - j.val + 1)),
          theta k α (n - 1 - j.val - i) * yPrime k α y₀init i)
      = ∑ i ∈ Finset.range k, theta k α (n - i) * yPrime k α y₀init i := by
  -- Step 1: Distribute α j into the inner sum.
  simp_rw [Finset.mul_sum]
  -- Step 2: Replace each inner range-sum with a Fin k filtered sum.
  have step2 : ∀ j : Fin k,
      (∑ i ∈ Finset.range (min k (n - 1 - j.val + 1)),
            α j * (theta k α (n - 1 - j.val - i) * yPrime k α y₀init i))
        = ∑ i : Fin k,
            if i.val + j.val < n then
              α j * (theta k α (n - 1 - j.val - i.val) * yPrime k α y₀init i.val)
            else 0 := by
    intro j
    have hj : j.val < k := j.isLt
    rw [show Finset.range (min k (n - 1 - j.val + 1))
          = (Finset.range k).filter (fun i => i + j.val < n) from by
        ext i
        simp only [Finset.mem_range, Finset.mem_filter, Nat.lt_min]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
        · intro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; omega]
    rw [Finset.sum_filter]
    rw [← Fin.sum_univ_eq_sum_range
        (fun i => if i + j.val < n then α j *
            (theta k α (n - 1 - j.val - i) * yPrime k α y₀init i)
          else 0) k]
  simp_rw [step2]
  -- Step 3: Swap the two sums.
  rw [Finset.sum_comm]
  -- Goal: ∑ i : Fin k, ∑ j : Fin k, (if cond then α j * (θ * y') else 0) = …
  -- Step 4: For each i, factor out y'_i and apply theta_recurrence_at.
  rw [← Fin.sum_univ_eq_sum_range
      (fun i => theta k α (n - i) * yPrime k α y₀init i) k]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hi : i.val < k := i.isLt
  have hi_lt_n : i.val < n := lt_of_lt_of_le hi hn
  -- Inner j-sum: extract y'_i to the right of the sum.
  rw [show (∑ j : Fin k, if i.val + j.val < n then
            α j * (theta k α (n - 1 - j.val - i.val) * yPrime k α y₀init i.val)
          else 0)
        = (∑ j : Fin k, if i.val + j.val < n then
            α j * theta k α (n - 1 - j.val - i.val) else 0)
            * yPrime k α y₀init i.val from by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      split_ifs with h
      · rw [← mul_assoc]
      · rw [zero_mul]]
  -- Now match theta_recurrence_at form: (j + i < n, arg = n-1-i-j).
  rw [show (∑ j : Fin k, if i.val + j.val < n then
              α j * theta k α (n - 1 - j.val - i.val) else 0)
        = ∑ j : Fin k, if j.val + i.val < n then
              α j * theta k α (n - 1 - i.val - j.val) else 0 from by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have h_cond : (i.val + j.val < n) ↔ (j.val + i.val < n) := by omega
      have h_arg : n - 1 - j.val - i.val = n - 1 - i.val - j.val := by omega
      by_cases h : i.val + j.val < n
      · rw [if_pos h, if_pos (h_cond.mp h), h_arg]
      · rw [if_neg h, if_neg (mt h_cond.mpr h)]]
  rw [theta_recurrence_at k α n i.val hi_lt_n]

/-- Swap helper for the `ψ` part. For `0 < k ≤ n`,
`Σ j : Fin k, α j * Σ_{i ∈ Icc k m_j} θ_{m_j-i} ψ_i
  = Σ_{i ∈ Icc k (n - 1)} θ_{n-i} ψ_i`. -/
private lemma sum_swap_psi
    (k : ℕ) (α : Fin k → R) (ψ : ℕ → R)
    (n : ℕ) (hkpos : 0 < k) (hn : k ≤ n) :
    (∑ j : Fin k, α j *
        ∑ i ∈ Finset.Icc k (n - 1 - j.val),
          theta k α (n - 1 - j.val - i) * ψ i)
      = ∑ i ∈ Finset.Icc k (n - 1), theta k α (n - i) * ψ i := by
  -- Step 1: Distribute α j.
  simp_rw [Finset.mul_sum]
  -- Step 2: Replace each inner Icc-sum with the unified Icc k (n-1) sum.
  have step2 : ∀ j : Fin k,
      (∑ i ∈ Finset.Icc k (n - 1 - j.val),
            α j * (theta k α (n - 1 - j.val - i) * ψ i))
        = ∑ i ∈ Finset.Icc k (n - 1),
            if i + j.val < n then
              α j * (theta k α (n - 1 - j.val - i) * ψ i)
            else 0 := by
    intro j
    have hj : j.val < k := j.isLt
    rw [show Finset.Icc k (n - 1 - j.val)
          = (Finset.Icc k (n - 1)).filter (fun i => i + j.val < n) from by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_filter]
        omega]
    rw [Finset.sum_filter]
  simp_rw [step2]
  -- Step 3: Swap.
  rw [Finset.sum_comm]
  -- Step 4: For each i ∈ Icc k (n-1), factor out ψ_i and apply theta_recurrence_at.
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_Icc] at hi
  have hi_lt_n : i < n := by omega
  -- Factor out ψ_i.
  rw [show (∑ j : Fin k, if i + j.val < n then
            α j * (theta k α (n - 1 - j.val - i) * ψ i) else 0)
        = (∑ j : Fin k, if i + j.val < n then
            α j * theta k α (n - 1 - j.val - i) else 0)
            * ψ i from by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      split_ifs with h
      · rw [← mul_assoc]
      · rw [zero_mul]]
  -- Match theta_recurrence_at form.
  rw [show (∑ j : Fin k, if i + j.val < n then
              α j * theta k α (n - 1 - j.val - i) else 0)
        = ∑ j : Fin k, if j.val + i < n then
              α j * theta k α (n - 1 - i - j.val) else 0 from by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have h_cond : (i + j.val < n) ↔ (j.val + i < n) := by omega
      have h_arg : n - 1 - j.val - i = n - 1 - i - j.val := by omega
      by_cases h : i + j.val < n
      · rw [if_pos h, if_pos (h_cond.mp h), h_arg]
      · rw [if_neg h, if_neg (mt h_cond.mpr h)]]
  rw [theta_recurrence_at k α n i hi_lt_n]

theorem linRec_closed_form
    (k : ℕ) (α : Fin k → R) (y₀init : Fin k → R) (ψ : ℕ → R) (n : ℕ) :
    linRec k α y₀init ψ n
      = (∑ i ∈ Finset.range (min k (n + 1)),
            theta k α (n - i) * yPrime k α y₀init i)
        + ∑ i ∈ Finset.Icc k n, theta k α (n - i) * ψ i := by
  -- Handle k = 0 specially since helpers require k ≥ 1.
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact linRec_closed_form_k_zero α y₀init ψ n
  -- Now k ≥ 1.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < k
    · exact linRec_closed_form_lt k α y₀init ψ n hn
    push_neg at hn
    -- Case n ≥ k ≥ 1, so n ≥ 1.
    have hn_pos : 1 ≤ n := le_trans hkpos hn
    rw [linRec_of_ge k α y₀init ψ n hn]
    -- Apply IH for each j : Fin k.
    have hkn : ∀ j : Fin k, n - 1 - j.val < n := by
      intro j
      have hj : j.val < k := j.isLt
      omega
    have hIH : ∀ j : Fin k,
        linRec k α y₀init ψ (n - 1 - j.val) =
          (∑ i ∈ Finset.range (min k (n - 1 - j.val + 1)),
              theta k α (n - 1 - j.val - i) * yPrime k α y₀init i)
            + ∑ i ∈ Finset.Icc k (n - 1 - j.val),
                theta k α (n - 1 - j.val - i) * ψ i := by
      intro j
      exact ih (n - 1 - j.val) (hkn j)
    simp_rw [hIH]
    -- Distribute α and split into y'-part and ψ-part.
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [sum_swap_yprime k α y₀init n hkpos hn,
        sum_swap_psi k α ψ n hkpos hn]
    -- Goal: firstSum_range_k(n) + secondSum_Icc_(n-1)(n) + ψ n
    --     = firstSum_range_(min k (n+1))(n) + secondSum_Icc_n(n)
    -- For n ≥ k, min k (n+1) = k.
    have hmin : min k (n + 1) = k := by omega
    rw [hmin]
    -- Split off the top of the Icc k n sum.
    have hn_eq : n = (n - 1) + 1 := by omega
    conv_rhs => rw [hn_eq]
    rw [Finset.sum_Icc_succ_top (by omega : k ≤ n - 1 + 1)]
    rw [show (n - 1 + 1 : ℕ) = n from hn_eq.symm]
    rw [Nat.sub_self, theta_zero, one_mul]
    abel

end OpenMath.Chapter1.Section141
