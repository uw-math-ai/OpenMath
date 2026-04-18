import OpenMath.Adjoint

open Finset

namespace ButcherTableau

variable {s : ℕ}

def reflect (t : ButcherTableau s) : ButcherTableau s where
  c := fun i => 1 - t.c i
  A := fun i j => t.b j - t.A i j
  b := t.b

/-! ## Combinatorial identity

The core identity needed: for n ≥ 0,
  ∑ k ∈ range (n+1), C(n,k) * (-1)^k / (k+1 : ℚ) = 1 / (n+1 : ℚ)

Proof idea: C(n,k)/(k+1) = C(n+1,k+1)/(n+1), so the sum becomes
  1/(n+1) * ∑ k ∈ range (n+1), C(n+1,k+1) * (-1)^k
  = 1/(n+1) * 1  (using the alternating sum of binomial coefficients = 0 for n+1 ≥ 1)
-/

/-
Key relation: C(n,k) / (k+1) = C(n+1,k+1) / (n+1) over ℚ.
-/
lemma choose_div_succ (n k : ℕ) (_hk : k ≤ n) :
    (n.choose k : ℚ) / (k + 1) = ((n + 1).choose (k + 1) : ℚ) / (n + 1) := by
  rw [ div_eq_div_iff ] <;> norm_cast ; linarith [ Nat.add_one_mul_choose_eq n k, Nat.choose_succ_succ n k ]

/-
Shifted alternating sum of binomial coefficients:
    ∑ k ∈ range (n+1), C(n+1,k+1) * (-1)^k = 1 for all n.
-/
lemma alternating_choose_shift (n : ℕ) :
    ∑ k ∈ range (n + 1), (((n + 1).choose (k + 1) : ℤ) * (-1) ^ k) = 1 := by
  have := @Int.alternating_sum_range_choose ( n + 1 );
  simp_all +decide [ mul_comm, pow_succ, Finset.sum_range_succ' ];
  linarith

/-
The core combinatorial identity over ℚ:
    ∑ k ∈ range (n+1), C(n,k) * (-1)^k / (↑(k+1)) = 1 / (↑(n+1)).
-/
lemma alternating_binom_div_succ (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℚ) * (-1) ^ k / (↑(k + 1)) = 1 / (↑(n + 1)) := by
  convert congr_arg ( fun x : ℚ => x / ( n + 1 ) ) ( show ( ∑ k ∈ Finset.range ( n + 1 ), ( Nat.choose ( n + 1 ) ( k + 1 ) : ℚ ) * ( -1 : ℚ ) ^ k ) = 1 from ?_ ) using 1;
  · rw [ Finset.sum_div _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ Nat.cast_choose, Nat.cast_choose ] <;> try linarith [ Finset.mem_range.mp hx ];
    field_simp;
    simpa [ Nat.factorial, Nat.succ_sub ( Finset.mem_range_succ_iff.mp hx ) ] using by ring;
  · norm_cast;
  · exact_mod_cast alternating_choose_shift n

/-! ## Main theorem -/

theorem reflect_satisfiesB_aristotle {t : ButcherTableau s} {η : ℕ}
    (hB : t.SatisfiesB η) : t.reflect.SatisfiesB η := by
  intro q hq₁ hq₂;
  -- Expand $(1 - c_i)^{q-1}$ using the binomial theorem.
  have h_expand : ∀ i, (1 - t.c i) ^ (q - 1) = ∑ k ∈ Finset.range (q), Nat.choose (q - 1) k * (-1 : ℚ) ^ k * (t.c i) ^ k := by
    intro i; rw [ sub_eq_add_neg, add_comm, add_pow ] ; cases q <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.sum_range_succ ] ;
    exact congrArg₂ _ ( Finset.sum_congr rfl fun _ _ => by ring ) ( by ring );
  -- Substitute the expansion into the sum.
  have h_subst : ∑ i, t.b i * (1 - t.c i) ^ (q - 1) = ∑ k ∈ Finset.range q, Nat.choose (q - 1) k * (-1 : ℚ) ^ k * (∑ i, t.b i * (t.c i) ^ k) := by
    simp +decide only [h_expand, Finset.mul_sum _ _ _, mul_left_comm];
    exact Finset.sum_comm;
  -- Apply the hypothesis `hB` to each term in the sum.
  have h_apply_hB : ∀ k ∈ Finset.range q, ∑ i, t.b i * (t.c i) ^ k = 1 / (k + 1 : ℚ) := by
    exact fun k hk => by simpa using hB ( k + 1 ) ( by linarith ) ( by linarith [ Finset.mem_range.mp hk ] ) ;
  convert h_subst using 1;
  convert ( alternating_binom_div_succ ( q - 1 ) ) |> Eq.symm using 1;
  · rw [ Nat.sub_add_cancel hq₁ ];
  · rw [ Nat.sub_add_cancel hq₁ ] ; exact Finset.sum_congr rfl fun x hx => by rw [ h_apply_hB x hx ] ; push_cast ; ring;

end ButcherTableau