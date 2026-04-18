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

/-- The reflected tableau preserves `E` under `B ∧ E`.
Textbook Theorem 343B, equation (343g). -/
theorem reflect_satisfiesE {t : ButcherTableau s} {η ζ : ℕ}
    (hB : t.SatisfiesB (η + ζ)) (hE : t.SatisfiesE η ζ) :
    t.reflect.SatisfiesE η ζ := by
  sorry

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
