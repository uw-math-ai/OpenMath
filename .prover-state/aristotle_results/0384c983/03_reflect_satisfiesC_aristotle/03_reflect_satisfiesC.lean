import Mathlib

/-! # Butcher Tableaux and the Reflected-Method C-Transfer Theorem

A Butcher tableau encodes the coefficients of an s-stage Runge–Kutta method.
We define the simplifying assumptions B(η) and C(η), the reflected (adjoint)
tableau, and prove that B(η) ∧ C(η) for the original tableau implies C(η)
for the reflected tableau.
-/

variable {F : Type*} [Field F] [CharZero F]

namespace ButcherTableau

/-- An `s`-stage Butcher tableau over a field `F`. -/
structure _root_.ButcherTableau (s : ℕ) (F : Type*) [Field F] where
  /-- Nodes -/
  c : Fin s → F
  /-- RK matrix -/
  A : Fin s → Fin s → F
  /-- Weights -/
  b : Fin s → F

variable {s : ℕ}

/-- Simplifying assumption B(η): the quadrature condition
    `∑ i, b i * c i ^ (k-1) = 1 / k` for `k = 1, …, η`. -/
def SatisfiesB (t : ButcherTableau s F) (η : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ η →
    ∑ i : Fin s, t.b i * t.c i ^ (k - 1) = 1 / (k : F)

/-- Simplifying assumption C(η): the row simplifying condition
    `∑ j, A i j * c j ^ (k-1) = c i ^ k / k` for `k = 1, …, η` and all `i`. -/
def SatisfiesC (t : ButcherTableau s F) (η : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ η → ∀ i : Fin s,
    ∑ j : Fin s, t.A i j * t.c j ^ (k - 1) = t.c i ^ k / (k : F)

/-- The reflected (adjoint) Butcher tableau. -/
def reflect (t : ButcherTableau s F) : ButcherTableau s F where
  c := fun i => 1 - t.c i
  A := fun i j => t.b j - t.A i j
  b := t.b

/-! ## Helper lemmas -/

lemma bc_combined {t : ButcherTableau s F} {η : ℕ}
    (hB : t.SatisfiesB η) (hC : t.SatisfiesC η)
    (m : ℕ) (hm : m + 1 ≤ η) (i : Fin s) :
    ∑ j : Fin s, (t.b j - t.A i j) * t.c j ^ m =
      (1 - t.c i ^ (m + 1)) / ((m + 1 : ℕ) : F) := by
  have hB' := hB (m + 1) (by omega) hm
  have hC' := hC (m + 1) (by omega) hm i
  simp only [Nat.add_sub_cancel] at hB' hC'
  have : ∑ j : Fin s, (t.b j - t.A i j) * t.c j ^ m =
    ∑ j, t.b j * t.c j ^ m - ∑ j, t.A i j * t.c j ^ m := by
    rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring
  rw [this, hB', hC']; ring

/-
Binomial expansion of `(1 - x)^n` as a finite sum.
-/
lemma one_sub_pow_eq_sum (x : F) (n : ℕ) :
    (1 - x) ^ n = ∑ m ∈ Finset.range (n + 1),
      (Nat.choose n m : F) * (-1 : F) ^ m * x ^ m := by
  rw [ sub_eq_add_neg, add_comm, add_pow ] ; congr ; ext ; ring

/-
The identity `C(k-1,m) / (m+1) = C(k,m+1) / k` for `m < k` and `k ≥ 1`,
    stated as a product identity to avoid division.
-/
lemma choose_div_identity (k m : ℕ) (hk : 1 ≤ k) (hm : m < k) :
    (Nat.choose (k - 1) m : F) * (k : F) =
      (Nat.choose k (m + 1) : F) * ((m + 1 : ℕ) : F) := by
  norm_cast ; cases k <;> cases m <;> norm_num at *;
  grind +suggestions

/-
Key binomial sum identity: `∑_{m=0}^{k-1} C(k, m+1) * (-1)^m = 1` for `k ≥ 1`.
-/
lemma sum_choose_neg_one (k : ℕ) (hk : 1 ≤ k) :
    ∑ m ∈ Finset.range k,
      (Nat.choose k (m + 1) : F) * (-1 : F) ^ m = 1 := by
  have h_binom : ∑ m ∈ Finset.range (k + 1), (k.choose m : F) * (-1) ^ m = 0 := by
    have := add_pow ( -1 : F ) 1 k;
    simpa [ mul_comm ] using this.symm.trans ( by rw [ neg_add_cancel, zero_pow ( by positivity ) ] );
  rw [ Finset.sum_range_succ' ] at h_binom;
  simp_all +decide [ pow_succ', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
  linear_combination -h_binom

/-
Binomial sum identity with `x`:
    `∑_{m=0}^{k-1} C(k,m+1) * (-1)^m * x^(m+1) = 1 - (1-x)^k`.
-/
lemma sum_choose_neg_one_mul (k : ℕ) (hk : 1 ≤ k) (x : F) :
    ∑ m ∈ Finset.range k,
      (Nat.choose k (m + 1) : F) * (-1 : F) ^ m * x ^ (m + 1) =
        1 - (1 - x) ^ k := by
  simp +decide [ sub_eq_neg_add, add_pow, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
  rw [ Finset.sum_range_succ' ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, pow_succ ];
  exact Finset.sum_congr rfl fun _ _ => by ring;

/-! ## Main theorem -/

theorem reflect_satisfiesC_aristotle {t : ButcherTableau s F} {η : ℕ}
    (hB : t.SatisfiesB η) (hC : t.SatisfiesC η) : t.reflect.SatisfiesC η := by
  intro k hk hk' i;
  -- Apply the binomial expansion to $(1 - c_j)^{k-1}$.
  have h_binom : ∑ j : Fin s, (t.b j - t.A i j) * (1 - t.c j) ^ (k - 1) =
    ∑ m ∈ Finset.range k, (Nat.choose (k - 1) m : F) * (-1 : F) ^ m * ∑ j : Fin s, (t.b j - t.A i j) * t.c j ^ m := by
      have h_expand : ∀ j : Fin s, (1 - t.c j) ^ (k - 1) = ∑ m ∈ Finset.range k, (Nat.choose (k - 1) m : F) * (-1 : F) ^ m * t.c j ^ m := by
        intro j
        rw [sub_eq_add_neg, add_comm, add_pow]
        simp [mul_assoc, mul_comm, mul_left_comm];
        exact Eq.symm ( by rw [ Nat.sub_add_cancel hk ] ; exact Finset.sum_congr rfl fun _ _ => by ring );
      simp +decide only [h_expand, Finset.mul_sum _ _ _, mul_left_comm];
      exact Finset.sum_comm;
  -- Apply the bc_combined lemma to each inner sum.
  have h_inner : ∑ m ∈ Finset.range k, (Nat.choose (k - 1) m : F) * (-1 : F) ^ m * ((1 - t.c i ^ (m + 1)) / (m + 1 : F)) =
    (1 / (k : F)) * (∑ m ∈ Finset.range k, (Nat.choose k (m + 1) : F) * (-1 : F) ^ m * (1 - t.c i ^ (m + 1))) := by
      rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun m hm => _ ; rw [ show ( Nat.choose k ( m + 1 ) : F ) = ( Nat.choose ( k - 1 ) m : F ) * k / ( m + 1 ) from _ ] ; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Nat.cast_add_one_ne_zero ] ;
      · simp +decide [ ← mul_assoc, ne_of_gt ( zero_lt_one.trans_le hk ) ];
      · rw [ eq_div_iff ] <;> norm_cast ; cases k <;> simp_all +decide [ Nat.add_one_mul_choose_eq ];
        nlinarith [ Nat.add_one_mul_choose_eq ‹_› m, Nat.choose_succ_succ ‹_› m ];
  convert h_inner using 1;
  · convert h_binom using 2;
    rw [ bc_combined hB hC _ ( by linarith [ Finset.mem_range.mp ‹_› ] ) ];
    norm_cast;
  · simp +decide [ div_eq_inv_mul, mul_sub, Finset.mul_sum _ _ _, Finset.sum_mul, sum_choose_neg_one_mul k hk ];
    rw [ ← Finset.mul_sum _ _ _, sum_choose_neg_one k hk ] ; ring;
    rfl

end ButcherTableau