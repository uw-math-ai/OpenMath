import OpenMath.Adjoint

/-!
# Reflected Runge–Kutta Methods

This file formalizes the reflected tableau from Iserles, Section 4.2
(equation (343a)) and its transfer properties for the simplifying
assumptions `B`, `C`, `D`, `E`.
-/

open Finset Real

namespace ButcherTableau

variable {s : ℕ}

@[ext] theorem ext {t t' : ButcherTableau s}
    (hA : ∀ i j, t.A i j = t'.A i j)
    (hb : ∀ i, t.b i = t'.b i)
    (hc : ∀ i, t.c i = t'.c i) : t = t' := by
  cases t
  cases t'
  simp at hA hb hc
  simp [ButcherTableau.mk.injEq, funext_iff, hA, hb, hc]

/-- The reflected Runge–Kutta tableau `(1 - c, b - A, b)`. -/
def reflect (t : ButcherTableau s) : ButcherTableau s where
  c := fun i => 1 - t.c i
  A := fun i j => t.b j - t.A i j
  b := t.b

@[simp] theorem reflect_c (t : ButcherTableau s) (i : Fin s) :
    t.reflect.c i = 1 - t.c i := rfl

@[simp] theorem reflect_A (t : ButcherTableau s) (i j : Fin s) :
    t.reflect.A i j = t.b j - t.A i j := rfl

@[simp] theorem reflect_b (t : ButcherTableau s) (i : Fin s) :
    t.reflect.b i = t.b i := rfl

@[simp] theorem reflect_reflect (t : ButcherTableau s) :
    t.reflect.reflect = t := by
  refine ButcherTableau.ext ?_ ?_ ?_
  · intro i j
    simp [reflect]
  · intro i
    simp [reflect]
  · intro i
    simp [reflect]

/-- Reflection preserves the weight-sum condition `B(1)`. -/
theorem reflect_order1 (t : ButcherTableau s) :
    t.reflect.order1 ↔ t.order1 := by
  simp [ButcherTableau.order1, reflect]

/-- If `t` satisfies the row-sum condition and `B(1)`, then its reflection does too. -/
theorem reflect_rowSum (t : ButcherTableau s) (hB1 : t.SatisfiesB 1)
    (hrow : t.IsRowSumConsistent) : t.reflect.IsRowSumConsistent := by
  intro i
  have hweights : ∑ j : Fin s, t.b j = 1 := (satisfiesB_one_iff t).mp hB1
  calc
    t.reflect.c i = 1 - t.c i := by simp [reflect]
    _ = (∑ j : Fin s, t.b j) - ∑ j : Fin s, t.A i j := by rw [hweights, hrow i]
    _ = ∑ j : Fin s, (t.b j - t.A i j) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ j : Fin s, t.reflect.A i j := by simp [reflect]

/-- Reflection preserves consistency. -/
theorem reflect_consistent (t : ButcherTableau s) (h : t.IsConsistent) :
    t.reflect.IsConsistent := by
  refine ⟨?_, ?_⟩
  · simpa [reflect, ButcherTableau.order1] using h.weights_sum
  · exact reflect_rowSum t ((satisfiesB_one_iff t).mpr h.weights_sum) h.row_sum

/-! ## Combinatorial helper lemmas for reflected-method transfer -/

/-- `C(n,k)/(k+1) = C(n+1,k+1)/(n+1)` over ℝ. -/
private lemma choose_div_succ' (n k : ℕ) :
    (n.choose k : ℝ) / ((k : ℝ) + 1) = ((n + 1).choose (k + 1) : ℝ) / ((n : ℝ) + 1) := by
  rw [div_eq_div_iff (by positivity : (k : ℝ) + 1 ≠ 0) (by positivity : (n : ℝ) + 1 ≠ 0)]
  have : (n.choose k * (n + 1) : ℕ) = ((n + 1).choose (k + 1) * (k + 1) : ℕ) := by
    linarith [Nat.add_one_mul_choose_eq n k]
  exact_mod_cast this

/-- Shifted alternating sum of binomial coefficients equals 1. -/
private lemma alternating_choose_shift' (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (((n + 1).choose (k + 1) : ℤ) * (-1) ^ k) = 1 := by
  have := @Int.alternating_sum_range_choose (n + 1)
  simp_all +decide [mul_comm, pow_succ, Finset.sum_range_succ']
  linarith

/-- Core identity: `∑_{k=0}^n C(n,k)(-1)^k/(k+1) = 1/(n+1)`. -/
private lemma alternating_binom_div_succ (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (-1) ^ k / ((k : ℝ) + 1) =
      1 / ((n : ℝ) + 1) := by
  have h1 : ∀ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * (-1) ^ k / ((k : ℝ) + 1) =
        ((n + 1).choose (k + 1) : ℝ) * (-1) ^ k / ((n : ℝ) + 1) := by
    intro k _
    rw [show (n.choose k : ℝ) * (-1) ^ k / ((k : ℝ) + 1) =
        ((n.choose k : ℝ) / ((k : ℝ) + 1)) * (-1) ^ k from by ring, choose_div_succ' n k]
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_div]
  congr 1
  have h2 := alternating_choose_shift' n
  have h3 : (↑(∑ k ∈ Finset.range (n + 1),
      ((n + 1).choose (k + 1) : ℤ) * (-1) ^ k) : ℝ) = 1 := by exact_mod_cast h2
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast] at h3
  convert h3 using 1

/-- The reflected tableau preserves `B`. Textbook Theorem 343B, equation (343d). -/
theorem reflect_satisfiesB {t : ButcherTableau s} {η : ℕ}
    (hB : t.SatisfiesB η) : t.reflect.SatisfiesB η := by
  intro q hq₁ hq₂
  simp only [reflect_b, reflect_c]
  -- Goal: ∑ i, t.b i * (1 - t.c i) ^ (q - 1) = 1 / (q : ℝ)
  -- Step 1: Expand (1 - c i)^(q-1) via binomial theorem
  have h_expand : ∀ i : Fin s, (1 - t.c i) ^ (q - 1) =
      ∑ k ∈ Finset.range q,
        ((q - 1).choose k : ℝ) * (-1) ^ k * t.c i ^ k := by
    intro i
    rw [show (1 : ℝ) - t.c i = -t.c i + 1 from by ring, add_pow]
    simp only [one_pow, mul_one, Nat.sub_add_cancel hq₁]
    apply Finset.sum_congr rfl
    intro m _
    rw [show -t.c i = (-1 : ℝ) * t.c i from by ring, mul_pow]
    ring
  -- Step 2: Swap sums
  simp_rw [h_expand, Finset.mul_sum, Finset.sum_comm (s := Finset.univ)]
  -- Goal: ∑ k in range q, ∑ i, t.b i * (C * (-1)^k * c^k) = 1 / q
  -- Rearrange each term
  conv_lhs =>
    arg 2; ext k; arg 2; ext i
    rw [show t.b i * (((q - 1).choose k : ℝ) * (-1) ^ k * t.c i ^ k) =
        ((q - 1).choose k : ℝ) * (-1) ^ k * (t.b i * t.c i ^ k) from by ring]
  simp_rw [← Finset.mul_sum]
  -- Goal: ∑ k in range q, C(q-1,k) * (-1)^k * (∑ i, b i * c i ^ k) = 1 / q
  -- Step 3: Apply hB to each inner sum
  have h_apply : ∀ k ∈ Finset.range q,
      ((q - 1).choose k : ℝ) * (-1) ^ k * (∑ i : Fin s, t.b i * t.c i ^ k) =
        ((q - 1).choose k : ℝ) * (-1) ^ k / ((k : ℝ) + 1) := by
    intro k hk
    have hk_lt : k < q := Finset.mem_range.mp hk
    have hB_k := hB (k + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hB_k
    rw [hB_k]; push_cast; ring
  rw [Finset.sum_congr rfl h_apply]
  have hq_eq : q - 1 + 1 = q := Nat.sub_add_cancel hq₁
  rw [show Finset.range q = Finset.range (q - 1 + 1) from by rw [hq_eq]]
  rw [alternating_binom_div_succ (q - 1)]
  congr 1; exact_mod_cast hq_eq

/-- `C(k-1,m)/(m+1) = C(k,m+1)/k` over ℝ when `k ≥ 1`. -/
private lemma choose_div_cast (k m : ℕ) (hk : 1 ≤ k) :
    ((k - 1).choose m : ℝ) / ((m : ℝ) + 1) = (k.choose (m + 1) : ℝ) / (k : ℝ) := by
  have h := choose_div_succ' (k - 1) m
  rwa [show k - 1 + 1 = k from Nat.sub_add_cancel hk,
       show ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) from by exact_mod_cast Nat.sub_add_cancel hk] at h

/-- `∑_{m=0}^{k-1} C(k,m+1)(-1)^m = 1` over ℝ, for `k ≥ 1`. -/
private lemma alternating_shifted_binom_sum (k : ℕ) (hk : 1 ≤ k) :
    ∑ m ∈ Finset.range k, (k.choose (m + 1) : ℝ) * (-1 : ℝ) ^ m = 1 := by
  have h := @Int.alternating_sum_range_choose k
  simp only [show k ≠ 0 from by omega, ↓reduceIte] at h
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.choose_zero_right, pow_zero, one_mul, Nat.cast_one] at h
  have h_cast : (↑(∑ m ∈ Finset.range k,
      (-1 : ℤ) ^ (m + 1) * ↑(k.choose (m + 1))) : ℝ) = -1 := by
    exact_mod_cast (show ∑ m ∈ Finset.range k,
      (-1 : ℤ) ^ (m + 1) * ↑(k.choose (m + 1)) = -1 from by linarith)
  push_cast at h_cast
  have : ∑ m ∈ Finset.range k, (k.choose (m + 1) : ℝ) * (-1 : ℝ) ^ m =
    -(∑ m ∈ Finset.range k, (-1 : ℝ) ^ (m + 1) * ↑(k.choose (m + 1))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro m _; ring
  linarith

/-- `∑_{m=0}^{k-1} C(k,m+1)(-1)^m x^{m+1} = 1 - (1-x)^k`. -/
private lemma weighted_binom_sum (k : ℕ) (x : ℝ) :
    ∑ m ∈ Finset.range k,
      (Nat.choose k (m + 1) : ℝ) * (-1 : ℝ) ^ m * x ^ (m + 1) =
        1 - (1 - x) ^ k := by
  simp +decide [sub_eq_neg_add, add_pow, mul_comm]
  rw [Finset.sum_range_succ']
  norm_num [mul_assoc, mul_comm, mul_left_comm, pow_succ]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Combined identity: `∑_{m=0}^{k-1} C(k-1,m)(-1)^m (1-x^{m+1})/(m+1) = (1-x)^k/k`. -/
private lemma binom_one_sub_pow_div (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    ∑ m ∈ Finset.range k,
      ((k - 1).choose m : ℝ) * (-1) ^ m * ((1 - x ^ (m + 1)) / ((m : ℝ) + 1)) =
        (1 - x) ^ k / (k : ℝ) := by
  have h_eq : ∀ m ∈ Finset.range k,
      ((k - 1).choose m : ℝ) * (-1) ^ m * ((1 - x ^ (m + 1)) / ((m : ℝ) + 1)) =
        (k.choose (m + 1) : ℝ) * (-1) ^ m * (1 - x ^ (m + 1)) / (k : ℝ) := by
    intro m _
    rw [show ((k - 1).choose m : ℝ) * (-1) ^ m * ((1 - x ^ (m + 1)) / ((m : ℝ) + 1)) =
        (((k - 1).choose m : ℝ) / ((m : ℝ) + 1)) * ((-1) ^ m * (1 - x ^ (m + 1))) from by ring,
      choose_div_cast k m hk]
    ring
  rw [Finset.sum_congr rfl h_eq, ← Finset.sum_div]
  congr 1
  simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [alternating_shifted_binom_sum k hk, weighted_binom_sum k x]
  ring

/-! ## Helper lemmas combining simplifying assumptions -/

/-- Combining B and C: `∑ j (b_j - A_{i,j}) c_j^m = (1 - c_i^{m+1}) / (m+1)`. -/
private lemma bc_combined {t : ButcherTableau s} {η : ℕ}
    (hB : t.SatisfiesB η) (hC : t.SatisfiesC η)
    {m : ℕ} (hm : m + 1 ≤ η) (i : Fin s) :
    ∑ j : Fin s, (t.b j - t.A i j) * t.c j ^ m =
      (1 - t.c i ^ (m + 1)) / ((m : ℝ) + 1) := by
  have hB' := hB (m + 1) (by omega) hm
  have hC' := hC (m + 1) (by omega) hm i
  simp only [Nat.add_sub_cancel] at hB' hC'
  rw [show ∑ j : Fin s, (t.b j - t.A i j) * t.c j ^ m =
    ∑ j, t.b j * t.c j ^ m - ∑ j, t.A i j * t.c j ^ m from by
    rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring]
  rw [hB', hC']; push_cast; ring

/-- `∑_{m=0}^{k-1} C(k-1,m)(-1)^m x^{m+1}/(m+1) = (1-(1-x)^k)/k`. -/
private lemma binom_pow_div (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    ∑ m ∈ Finset.range k,
      ((k - 1).choose m : ℝ) * (-1) ^ m * (x ^ (m + 1) / ((m : ℝ) + 1)) =
        (1 - (1 - x) ^ k) / (k : ℝ) := by
  have h_eq : ∀ m ∈ Finset.range k,
      ((k - 1).choose m : ℝ) * (-1) ^ m * (x ^ (m + 1) / ((m : ℝ) + 1)) =
        (k.choose (m + 1) : ℝ) * (-1) ^ m * x ^ (m + 1) / (k : ℝ) := by
    intro m _
    rw [show ((k - 1).choose m : ℝ) * (-1) ^ m * (x ^ (m + 1) / ((m : ℝ) + 1)) =
        (((k - 1).choose m : ℝ) / ((m : ℝ) + 1)) * ((-1) ^ m * x ^ (m + 1)) from by ring,
      choose_div_cast k m hk]
    ring
  rw [Finset.sum_congr rfl h_eq, ← Finset.sum_div]
  congr 1
  exact weighted_binom_sum k x

/-! ## Transfer theorems -/

/-- Expand `(1 - x)^(k-1)` as a binomial sum, with `range k`. -/
private lemma one_sub_pow_expand (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    (1 - x) ^ (k - 1) =
      ∑ m ∈ Finset.range k, ((k - 1).choose m : ℝ) * (-1) ^ m * x ^ m := by
  rw [show (1 : ℝ) - x = -x + 1 from by ring, add_pow]
  simp only [one_pow, mul_one, Nat.sub_add_cancel hk]
  apply Finset.sum_congr rfl
  intro m _
  rw [show -x = (-1 : ℝ) * x from by ring, mul_pow]; ring

/-- The reflected tableau preserves `C` under `B ∧ C`.
Textbook Theorem 343B, equation (343e). -/
theorem reflect_satisfiesC {t : ButcherTableau s} {η : ℕ}
    (hB : t.SatisfiesB η) (hC : t.SatisfiesC η) : t.reflect.SatisfiesC η := by
  intro k hk hkη i
  simp only [reflect_A, reflect_c]
  -- Goal: ∑ j, (b j - A i j) * (1 - c j)^{k-1} = (1 - c i)^k / k
  -- Step 1: Expand (1 - c j)^(k-1)
  simp_rw [one_sub_pow_expand k hk, Finset.mul_sum, Finset.sum_comm (s := Finset.univ)]
  -- Step 2: Rearrange
  conv_lhs =>
    arg 2; ext m; arg 2; ext j
    rw [show (t.b j - t.A i j) * (((k - 1).choose m : ℝ) * (-1) ^ m * t.c j ^ m) =
        ((k - 1).choose m : ℝ) * (-1) ^ m * ((t.b j - t.A i j) * t.c j ^ m) from by ring]
  simp_rw [← Finset.mul_sum]
  -- Step 3: Apply bc_combined to each inner sum
  have h_bc : ∀ m ∈ Finset.range k,
      ((k - 1).choose m : ℝ) * (-1) ^ m *
        (∑ j : Fin s, (t.b j - t.A i j) * t.c j ^ m) =
      ((k - 1).choose m : ℝ) * (-1) ^ m *
        ((1 - t.c i ^ (m + 1)) / ((m : ℝ) + 1)) := by
    intro m hm
    have hm_lt := Finset.mem_range.mp hm
    rw [bc_combined hB hC (by omega) i]
  rw [Finset.sum_congr rfl h_bc]
  -- Step 4: Apply binom_one_sub_pow_div
  exact binom_one_sub_pow_div k hk (t.c i)

/-- The reflected tableau preserves `D` under `B ∧ D`.
Textbook Theorem 343B, equation (343f). -/
theorem reflect_satisfiesD {t : ButcherTableau s} {η : ℕ}
    (hB : t.SatisfiesB η) (hD : t.SatisfiesD η) : t.reflect.SatisfiesD η := by
  intro k hk hkη j
  simp only [reflect_A, reflect_b, reflect_c]
  -- Goal: ∑ i, b i * (1-c i)^{k-1} * (b j - A i j) = b j / k * (1 - (1-c j)^k)
  -- Suffices to show the second sum
  suffices h_second : ∑ i : Fin s, t.b i * (1 - t.c i) ^ (k - 1) * t.A i j =
      t.b j * (1 - t.c j) ^ k / (k : ℝ) by
    have hB_refl : ∑ i : Fin s, t.b i * (1 - t.c i) ^ (k - 1) = 1 / (k : ℝ) := by
      have := reflect_satisfiesB hB k hk hkη
      simpa only [reflect_b, reflect_c] using this
    have h_split : ∑ i : Fin s, t.b i * (1 - t.c i) ^ (k - 1) * (t.b j - t.A i j) =
        t.b j * (∑ i : Fin s, t.b i * (1 - t.c i) ^ (k - 1)) -
          ∑ i : Fin s, t.b i * (1 - t.c i) ^ (k - 1) * t.A i j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [h_split, hB_refl, h_second]; ring
  -- Prove: ∑ i, b_i (1-c_i)^{k-1} A_{i,j} = b_j (1-c_j)^k / k
  -- Expand (1-c_i)^{k-1}
  simp_rw [one_sub_pow_expand k hk]
  -- Rearrange: b_i * (∑ m, ...) * A_{i,j} = ∑ m, C*(-1)^m*(b_i*c_i^m*A_{i,j})
  simp_rw [show ∀ (i : Fin s), t.b i * (∑ m ∈ Finset.range k,
      ((k - 1).choose m : ℝ) * (-1) ^ m * t.c i ^ m) * t.A i j =
    ∑ m ∈ Finset.range k,
      ((k - 1).choose m : ℝ) * (-1) ^ m * (t.b i * t.c i ^ m * t.A i j) from
    fun i => by rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro m _; ring]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  -- Apply hD to each inner sum
  have h_hD : ∀ m ∈ Finset.range k,
      ((k - 1).choose m : ℝ) * (-1) ^ m *
        (∑ i : Fin s, t.b i * t.c i ^ m * t.A i j) =
      t.b j * (((k - 1).choose m : ℝ) * (-1) ^ m *
        ((1 - t.c j ^ (m + 1)) / ((m : ℝ) + 1))) := by
    intro m hm
    have hm_lt := Finset.mem_range.mp hm
    have hD_m := hD (m + 1) (by omega) (by omega) j
    simp only [Nat.add_sub_cancel] at hD_m
    rw [hD_m]; push_cast; ring
  rw [Finset.sum_congr rfl h_hD, ← Finset.mul_sum, binom_one_sub_pow_div k hk (t.c j),
    mul_div_assoc]

/-! ## ℚ combinatorial identities for cross-term evaluation -/

/-- Generalized alternating binomial sum over ℚ:
  `∑_{m=0}^n C(n,m)(-1)^m/(m+a) = n!*(a-1)!/(n+a)!` for `a ≥ 1`. -/
private lemma gen_alt_binom_sum_Q (n a : ℕ) (ha : 0 < a) :
    ∑ m ∈ Finset.range (n + 1),
      (n.choose m : ℚ) * (-1) ^ m / ((m : ℚ) + (a : ℚ)) =
      ↑(n.factorial) * ↑((a - 1).factorial) / ↑((n + a).factorial) := by
  induction' n with n ih generalizing a
  · cases a <;> norm_num [Nat.factorial] at *
    rw [inv_eq_one_div, div_eq_div_iff] <;> ring <;> positivity
  · have h_split : ∑ m ∈ Finset.range (n + 2),
        Nat.choose (n + 1) m * (-1 : ℚ) ^ m / (m + a : ℚ) =
      ∑ m ∈ Finset.range (n + 1), Nat.choose n m * (-1 : ℚ) ^ m / (m + a : ℚ) +
      ∑ m ∈ Finset.range (n + 1),
        Nat.choose n m * (-1 : ℚ) ^ (m + 1) / (m + a + 1 : ℚ) := by
      rw [Finset.sum_range_succ']
      rw [Finset.sum_range_succ]
      norm_num [Nat.choose_succ_succ, add_comm, add_left_comm, add_assoc]
      rw [Finset.sum_range_succ']
      norm_num [Finset.sum_range_succ, pow_succ, div_eq_mul_inv]
      ring
      simpa only [Finset.sum_add_distrib] using by ring
    have := ih (a + 1) (Nat.succ_pos _)
    simp_all +decide [Finset.sum_add_distrib, add_assoc, pow_succ', div_eq_mul_inv]
    rcases a <;> simp_all +decide [Nat.factorial, add_comm, add_left_comm, add_assoc]
    grind

/-- Partial alternating sum of binomial coefficients over ℚ:
  `∑_{j=0}^k C(n,j)(-1)^j = (-1)^k * C(n-1,k)` for `n ≥ 1`, `k < n`. -/
private lemma partial_alt_binom_sum_Q (n : ℕ) (k : ℕ) (hn : 0 < n) (hk : k < n) :
    ∑ j ∈ Finset.range (k + 1),
      (n.choose j : ℚ) * (-1 : ℚ) ^ j = (-1 : ℚ) ^ k * ((n - 1).choose k : ℚ) := by
  induction' n with n ih generalizing k
  · contradiction
  · induction' k with k ihk <;>
      simp_all +decide [Finset.sum_range_succ, pow_succ', Nat.choose_succ_succ]
    linear_combination ihk hk.le

/-- The double binomial sum identity over ℚ:
  `∑_{α<r} ∑_{β<q} C(r-1,α)(-1)^α C(q-1,β)(-1)^β / ((β+1)(α+β+2)) = 1/(r(q+r))`. -/
private lemma double_binom_sum_Q (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    ∑ α ∈ Finset.range r, ∑ β ∈ Finset.range q,
      ((r - 1).choose α : ℚ) * (-1 : ℚ) ^ α *
      (((q - 1).choose β : ℚ) * (-1 : ℚ) ^ β) /
      (((β : ℚ) + 1) * ((α : ℚ) + (β : ℚ) + 2)) =
    1 / ((r : ℚ) * ((q : ℚ) + (r : ℚ))) := by
  have h_inner : ∀ β ∈ Finset.range q,
      ∑ α ∈ Finset.range r, (Nat.choose (r - 1) α : ℚ) * (-1 : ℚ) ^ α /
        ((α + β + 2) : ℚ) =
      (Nat.factorial (r - 1) * Nat.factorial (β + 1)) / (Nat.factorial (r + β + 1)) := by
    intro β hβ
    have := gen_alt_binom_sum_Q (r - 1) (β + 2) (by linarith)
    cases r <;> simp_all +decide [add_assoc, Nat.factorial]
    norm_num [add_comm, add_left_comm, add_assoc, Nat.factorial]
  have h_double_sum :
      ∑ β ∈ Finset.range q, ∑ α ∈ Finset.range r,
        (Nat.choose (r - 1) α : ℚ) * (-1 : ℚ) ^ α *
        (Nat.choose (q - 1) β : ℚ) * (-1 : ℚ) ^ β /
        ((β + 1) * (α + β + 2)) =
      ∑ β ∈ Finset.range q,
        (Nat.choose (q - 1) β : ℚ) * (-1 : ℚ) ^ β / (β + 1) *
        (Nat.factorial (r - 1) * Nat.factorial (β + 1)) /
        (Nat.factorial (r + β + 1)) := by
    refine Finset.sum_congr rfl fun β hβ => ?_
    convert congr_arg (fun x : ℚ => (Nat.choose (q - 1) β : ℚ) * (-1) ^ β / (β + 1) * x)
      (h_inner β hβ) using 1 <;> ring
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_; ring
    grind
  have h_simplify :
      ∑ β ∈ Finset.range q,
        (Nat.choose (q - 1) β : ℚ) * (-1 : ℚ) ^ β / (β + 1) *
        (Nat.factorial (r - 1) * Nat.factorial (β + 1)) /
        (Nat.factorial (r + β + 1)) =
      (Nat.factorial (q - 1) * Nat.factorial (r - 1)) / (Nat.factorial (q + r)) *
      (-1 : ℚ) ^ (q - 1) *
      ∑ j ∈ Finset.range q, (Nat.choose (q + r) j : ℚ) * (-1 : ℚ) ^ j := by
    have h_simplify : ∀ β ∈ Finset.range q,
        (Nat.choose (q - 1) β : ℚ) * (-1 : ℚ) ^ β / (β + 1) *
        (Nat.factorial (r - 1) * Nat.factorial (β + 1)) /
        (Nat.factorial (r + β + 1)) =
      (Nat.factorial (q - 1) * Nat.factorial (r - 1)) / (Nat.factorial (q + r)) *
      (-1 : ℚ) ^ (q - 1) *
      (Nat.choose (q + r) (q - 1 - β) : ℚ) * (-1 : ℚ) ^ (q - 1 - β) := by
      intro β hβ; rw [Nat.cast_choose, Nat.cast_choose]
      · field_simp
        rw [show q + r - (q - 1 - β) = r + β + 1 by
          exact Nat.sub_eq_of_eq_add <| by
            linarith [Nat.sub_add_cancel <| show β ≤ q - 1 from
              Nat.le_sub_one_of_lt <| Finset.mem_range.mp hβ,
              Nat.sub_add_cancel <| show 1 ≤ q from hq]]
        norm_num [Nat.factorial_succ]; ring
        rw [show (-1 : ℚ) ^ (q - 1) = (-1 : ℚ) ^ (q - 1 - β) * (-1 : ℚ) ^ β by
          rw [← pow_add, Nat.sub_add_cancel (show β ≤ q - 1 from
            Nat.le_sub_one_of_lt (Finset.mem_range.mp hβ))]]
        ring
        norm_num [pow_mul']
      · omega
      · exact Nat.le_pred_of_lt <| Finset.mem_range.mp hβ
    rw [Finset.mul_sum, Finset.sum_congr rfl h_simplify]
    rw [← Finset.sum_range_reflect]
    exact Finset.sum_congr rfl fun x hx => by
      rw [tsub_tsub_cancel_of_le
        (Nat.le_sub_one_of_lt (Finset.mem_range.mp hx))]; ring
  have h_partial_sum :
      ∑ j ∈ Finset.range q, (Nat.choose (q + r) j : ℚ) * (-1 : ℚ) ^ j =
      (-1 : ℚ) ^ (q - 1) * (Nat.choose (q + r - 1) (q - 1) : ℚ) := by
    convert partial_alt_binom_sum_Q (q + r) (q - 1) (by linarith) (by omega) using 1
    cases q <;> aesop
  convert h_double_sum.trans (h_simplify.trans (congr_arg _ h_partial_sum)) using 1
  · exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
  · rw [Nat.cast_choose] <;> try omega
    field_simp
    rcases q with (_ | q) <;> rcases r with (_ | r) <;> norm_num [Nat.factorial] at *
    norm_num [add_assoc, add_tsub_assoc_of_le]; ring
    norm_num [Nat.add_comm 1, Nat.add_assoc, Nat.factorial_succ]; ring

/-- Cast the ℚ double binomial sum identity to ℝ. -/
private lemma double_binom_sum_real (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    ∑ α ∈ Finset.range r, ∑ β ∈ Finset.range q,
      ((r - 1).choose α : ℝ) * (-1 : ℝ) ^ α *
      (((q - 1).choose β : ℝ) * (-1 : ℝ) ^ β) /
      (((β : ℝ) + 1) * ((α : ℝ) + (β : ℝ) + 2)) =
    1 / ((r : ℝ) * ((q : ℝ) + (r : ℝ))) := by
  have hQ := double_binom_sum_Q q r hq hr
  have cast_eq := congr_arg (Rat.cast (K := ℝ)) hQ
  push_cast at cast_eq
  convert cast_eq using 2

/-- The reflected tableau preserves `E` under `B ∧ E`.
Textbook Theorem 343B, equation (343g). -/
theorem reflect_satisfiesE {t : ButcherTableau s} {η ζ : ℕ}
    (hB : t.SatisfiesB (η + ζ)) (hE : t.SatisfiesE η ζ) :
    t.reflect.SatisfiesE η ζ := by
  intro k l hk hκη hl hlζ
  simp only [reflect_b, reflect_A, reflect_c]
  have hB_refl : t.reflect.SatisfiesB (η + ζ) := reflect_satisfiesB hB
  have h_expand_i : ∀ i : Fin s,
      (1 - t.c i) ^ (k - 1) =
        ∑ a ∈ Finset.range k, ((k - 1).choose a : ℝ) * (-1) ^ a * t.c i ^ a :=
    by
      intro i
      simpa using one_sub_pow_expand k hk (t.c i)
  have h_expand_j : ∀ j : Fin s,
      (1 - t.c j) ^ (l - 1) =
        ∑ b ∈ Finset.range l, ((l - 1).choose b : ℝ) * (-1) ^ b * t.c j ^ b :=
    by
      intro j
      simpa using one_sub_pow_expand l hl (t.c j)
  have h_split :
      ∑ i : Fin s, ∑ j : Fin s,
          t.b i * (1 - t.c i) ^ (k - 1) * (t.b j - t.A i j) * (1 - t.c j) ^ (l - 1) =
        (∑ i : Fin s, ∑ j : Fin s,
          t.b i * (1 - t.c i) ^ (k - 1) * t.b j * (1 - t.c j) ^ (l - 1)) -
        (∑ i : Fin s, ∑ j : Fin s,
          t.b i * (1 - t.c i) ^ (k - 1) * t.A i j * (1 - t.c j) ^ (l - 1)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have h_b_term :
      ∑ i : Fin s, ∑ j : Fin s,
          t.b i * (1 - t.c i) ^ (k - 1) * t.b j * (1 - t.c j) ^ (l - 1) =
        1 / ((k : ℝ) * (l : ℝ)) := by
    have hkB : ∑ i : Fin s, t.b i * (1 - t.c i) ^ (k - 1) = 1 / (k : ℝ) := by
      simpa only [reflect_b, reflect_c] using hB_refl k hk (by omega)
    have hlB : ∑ j : Fin s, t.b j * (1 - t.c j) ^ (l - 1) = 1 / (l : ℝ) := by
      simpa only [reflect_b, reflect_c] using hB_refl l hl (by omega)
    have hfactor :
        ∀ i : Fin s,
          ∑ j : Fin s, t.b i * (1 - t.c i) ^ (k - 1) * t.b j * (1 - t.c j) ^ (l - 1) =
            (t.b i * (1 - t.c i) ^ (k - 1)) *
              (∑ j : Fin s, t.b j * (1 - t.c j) ^ (l - 1)) := by
      intro i
      conv_lhs =>
        arg 2
        ext j
        rw [show t.b i * (1 - t.c i) ^ (k - 1) * t.b j * (1 - t.c j) ^ (l - 1) =
          (t.b i * (1 - t.c i) ^ (k - 1)) * (t.b j * (1 - t.c j) ^ (l - 1)) from by ring]
      rw [← Finset.mul_sum]
    calc
      ∑ i : Fin s, ∑ j : Fin s,
          t.b i * (1 - t.c i) ^ (k - 1) * t.b j * (1 - t.c j) ^ (l - 1)
          = (∑ i : Fin s, t.b i * (1 - t.c i) ^ (k - 1)) *
              (∑ j : Fin s, t.b j * (1 - t.c j) ^ (l - 1)) := by
              rw [Finset.sum_congr rfl (fun i _ => hfactor i), ← Finset.sum_mul]
      _ = (1 / (k : ℝ)) * (1 / (l : ℝ)) := by rw [hkB, hlB]
      _ = 1 / ((k : ℝ) * (l : ℝ)) := by ring
  have h_A_term :
      ∑ i : Fin s, ∑ j : Fin s,
          t.b i * (1 - t.c i) ^ (k - 1) * t.A i j * (1 - t.c j) ^ (l - 1) =
        1 / ((k : ℝ) * (l : ℝ)) - 1 / ((l : ℝ) * ((k + l : ℕ) : ℝ)) := by
    -- Suffices to show LHS = double binomial sum, then evaluate
    suffices h_eq : ∑ i : Fin s, ∑ j : Fin s,
        t.b i * (1 - t.c i) ^ (k - 1) * t.A i j * (1 - t.c j) ^ (l - 1) =
      ∑ α ∈ Finset.range k, ∑ β ∈ Finset.range l,
        ((k - 1).choose α : ℝ) * (-1 : ℝ) ^ α *
        (((l - 1).choose β : ℝ) * (-1 : ℝ) ^ β) /
        (((β : ℝ) + 1) * ((α : ℝ) + (β : ℝ) + 2)) by
      rw [h_eq, double_binom_sum_real l k hl hk]
      have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hl_ne : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp; push_cast; ring
    -- Reduce to double binomial sum: expand, swap sums, apply hE
    have h_inner : ∀ (a : ℕ), a < k → ∀ (b : ℕ), b < l →
        ∑ i : Fin s, ∑ j : Fin s,
          t.b i * t.c i ^ a * t.A i j * t.c j ^ b =
        1 / (((b : ℝ) + 1) * ((a : ℝ) + (b : ℝ) + 2)) := by
      intro a ha b hb
      have h_E := hE (a + 1) (b + 1) (by omega) (by omega) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at h_E
      convert h_E using 2 <;> push_cast <;> ring
    -- Phase 1: expand (1-c_i)^(k-1) and pull ∑_α outside
    simp_rw [h_expand_i]
    conv_lhs =>
      arg 2; ext i; arg 2; ext j
      rw [show t.b i * (∑ a ∈ Finset.range k,
          ((k - 1).choose a : ℝ) * (-1) ^ a * t.c i ^ a) *
          t.A i j * (1 - t.c j) ^ (l - 1) =
        ∑ a ∈ Finset.range k, ((k - 1).choose a : ℝ) * (-1) ^ a *
          (t.b i * t.c i ^ a * t.A i j * (1 - t.c j) ^ (l - 1)) from by
        rw [Finset.mul_sum]; simp_rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun a _ => by ring)]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range k)]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range k)]
    simp_rw [← Finset.mul_sum]
    -- Phase 2: for each α, expand (1-c_j)^(l-1) and pull ∑_β outside
    refine Finset.sum_congr rfl fun α hα => ?_
    have hα' := Finset.mem_range.mp hα
    -- Phase 2: expand (1-c_j)^(l-1) inside, swap sums, apply hE
    -- Work on the inner sum (after the scalar C_α*(-1)^α)
    simp_rw [h_expand_j]
    conv_lhs =>
      arg 2; arg 2; ext i; arg 2; ext j
      rw [show t.b i * t.c i ^ α * t.A i j *
          (∑ b ∈ Finset.range l,
            ((l - 1).choose b : ℝ) * (-1) ^ b * t.c j ^ b) =
        ∑ b ∈ Finset.range l, ((l - 1).choose b : ℝ) * (-1) ^ b *
          (t.b i * t.c i ^ α * t.A i j * t.c j ^ b) from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by ring)]
    -- Swap sums: pull ∑_β outside ∑_i and ∑_j
    conv_lhs =>
      arg 2; arg 2; ext i; rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range l)]
    conv_lhs => arg 2; rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range l)]
    simp_rw [← Finset.mul_sum]
    -- Apply h_inner to evaluate ∑_i ∑_j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    have hβ' := Finset.mem_range.mp hβ
    rw [h_inner α hα' β hβ']
    ring
  calc
    ∑ i : Fin s, ∑ j : Fin s,
        t.b i * (1 - t.c i) ^ (k - 1) * (t.b j - t.A i j) * (1 - t.c j) ^ (l - 1)
        = (∑ i : Fin s, ∑ j : Fin s,
            t.b i * (1 - t.c i) ^ (k - 1) * t.b j * (1 - t.c j) ^ (l - 1)) -
          (∑ i : Fin s, ∑ j : Fin s,
            t.b i * (1 - t.c i) ^ (k - 1) * t.A i j * (1 - t.c j) ^ (l - 1)) := h_split
    _ = 1 / ((k : ℝ) * (l : ℝ)) -
          (1 / ((k : ℝ) * (l : ℝ)) - 1 / ((l : ℝ) * ((k + l : ℕ) : ℝ))) := by
            rw [h_b_term, h_A_term]
    _ = 1 / ((l : ℝ) * ((k + l : ℕ) : ℝ)) := by
          ring

end ButcherTableau

/-! ## Concrete reflected tableaux -/

/-- Forward Euler reflects to backward Euler. -/
theorem rkEuler_reflect_eq_implicitEuler : rkEuler.reflect = rkImplicitEuler := by
  refine ButcherTableau.ext ?_ ?_ ?_
  · intro i j
    fin_cases i
    fin_cases j
    simp [ButcherTableau.reflect, rkEuler, rkImplicitEuler]
  · intro i
    fin_cases i
    simp [ButcherTableau.reflect, rkEuler, rkImplicitEuler]
  · intro i
    fin_cases i
    simp [ButcherTableau.reflect, rkEuler, rkImplicitEuler]
