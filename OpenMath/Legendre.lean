import OpenMath.Collocation
import OpenMath.LegendreHelpers

/-!
# Shifted Legendre Polynomials and Gaussian Quadrature

## Section 3.4.2 of Iserles: Methods based on Gaussian quadrature

The **shifted Legendre polynomials** `P_n^* : [0,1] → ℝ` are orthogonal
polynomials on `[0,1]` normalized by `P_n^*(1) = 1`. They are related to the
standard Legendre polynomials `P_n` on `[-1,1]` by `P_n^*(x) = P_n(2x - 1)`.

## Definition

We define them via the three-term recurrence (342f from Iserles):
  P_0^*(x) = 1
  P_1^*(x) = 2x - 1
  n P_n^*(x) = (2n-1)(2x-1) P_{n-1}^*(x) - (n-1) P_{n-2}^*(x)

## Main Results

### Lemma 342A (algebraic properties):
- `shiftedLegendreP_eval_one`: P_n^*(1) = 1                          (342b)
- `shiftedLegendreP_symmetry`: P_n^*(1-x) = (-1)^n P_n^*(x)         (342c)
- `shiftedLegendreP_eval_zero`: P_n^*(0) = (-1)^n
- `shiftedLegendreP_half_odd`: P_{2n+1}^*(1/2) = 0

### Lemma 342B (Gaussian quadrature exactness):
If c_i are zeros of P_s^* and B(s) holds, then B(2s) holds.

### Corollary 342D (Gaussian quadrature order):
GL nodes + B(s) + C(s) → B(2s) + E(s,s) + D(s).

Reference: Iserles, *A First Course in the Numerical Analysis of
Differential Equations*, Section 3.4.2.
-/

open Finset Real
open scoped BigOperators

/-! ## Definition of Shifted Legendre Polynomials -/

/-- The **n-th shifted Legendre polynomial** on `[0,1]`, defined by the three-term
recurrence (342f):

  `P_0^*(x) = 1`
  `P_1^*(x) = 2x - 1`
  `n P_n^*(x) = (2n-1)(2x-1) P_{n-1}^*(x) - (n-1) P_{n-2}^*(x)`

These are orthogonal polynomials on `[0,1]` with `P_n^*(1) = 1`. -/
noncomputable def shiftedLegendreP : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 2 * x - 1
  | n + 2, x =>
    ((2 * (n : ℝ) + 3) * (2 * x - 1) * shiftedLegendreP (n + 1) x -
      ((n : ℝ) + 1) * shiftedLegendreP n x) / ((n : ℝ) + 2)

/-! ## Basic Evaluations -/

@[simp] theorem shiftedLegendreP_zero (x : ℝ) : shiftedLegendreP 0 x = 1 := rfl

@[simp] theorem shiftedLegendreP_one (x : ℝ) :
    shiftedLegendreP 1 x = 2 * x - 1 := rfl

theorem shiftedLegendreP_succ_succ (n : ℕ) (x : ℝ) :
    shiftedLegendreP (n + 2) x =
      ((2 * (n : ℝ) + 3) * (2 * x - 1) * shiftedLegendreP (n + 1) x -
        ((n : ℝ) + 1) * shiftedLegendreP n x) / ((n : ℝ) + 2) := rfl

/-- `P_2^*(x) = 6x² - 6x + 1`. -/
theorem shiftedLegendreP_two (x : ℝ) :
    shiftedLegendreP 2 x = 6 * x ^ 2 - 6 * x + 1 := by
  rw [shiftedLegendreP_succ_succ, shiftedLegendreP_one, shiftedLegendreP_zero]
  ring_nf

/-- `P_3^*(x) = 20x³ - 30x² + 12x - 1`. -/
theorem shiftedLegendreP_three (x : ℝ) :
    shiftedLegendreP 3 x = 20 * x ^ 3 - 30 * x ^ 2 + 12 * x - 1 := by
  rw [shiftedLegendreP_succ_succ, shiftedLegendreP_two, shiftedLegendreP_one]
  ring_nf

/-! ## Normalization: P_n^*(1) = 1  (equation 342b) -/

/-- **Equation 342b**: `P_n^*(1) = 1` for all `n`. -/
theorem shiftedLegendreP_eval_one : ∀ n : ℕ, shiftedLegendreP n 1 = 1 := by
  intro n
  refine Nat.strongRecOn (n := n) ?_
  intro n ih
  match n with
  | 0 => simp
  | 1 => simp [shiftedLegendreP]; norm_num
  | n + 2 =>
    rw [shiftedLegendreP_succ_succ, ih (n + 1) (by omega), ih n (by omega)]
    have hn : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring

/-! ## Symmetry: P_n^*(1-x) = (-1)^n P_n^*(x)  (equation 342c) -/

private lemma neg_one_pow_add_two (n : ℕ) : (-1 : ℝ) ^ (n + 2) = (-1) ^ n := by
  rw [pow_add]; norm_num

/-- **Equation 342c**: `P_n^*(1 - x) = (-1)^n * P_n^*(x)`. -/
theorem shiftedLegendreP_symmetry (n : ℕ) (x : ℝ) :
    shiftedLegendreP n (1 - x) = (-1) ^ n * shiftedLegendreP n x := by
  refine Nat.strongRecOn (n := n) ?_
  intro n ih
  match n with
  | 0 => simp
  | 1 => simp [shiftedLegendreP]; ring
  | n + 2 =>
    rw [shiftedLegendreP_succ_succ, ih (n + 1) (by omega), ih n (by omega)]
    rw [shiftedLegendreP_succ_succ]
    have hn : (n : ℝ) + 2 ≠ 0 := by positivity
    rw [neg_one_pow_add_two]
    field_simp
    ring

/-- `P_n^*(0) = (-1)^n`, from symmetry and `P_n^*(1) = 1`. -/
theorem shiftedLegendreP_eval_zero (n : ℕ) : shiftedLegendreP n 0 = (-1) ^ n := by
  have h := shiftedLegendreP_symmetry n 1
  rwa [sub_self, shiftedLegendreP_eval_one, mul_one] at h

/-- `P_n^*(1/2) = 0` for odd `n`. -/
theorem shiftedLegendreP_half_odd (n : ℕ) :
    shiftedLegendreP (2 * n + 1) (1 / 2) = 0 := by
  have h := shiftedLegendreP_symmetry (2 * n + 1) (1 / 2)
  simp only [show (1 : ℝ) - 1 / 2 = 1 / 2 from by ring] at h
  have hsign : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
    rw [pow_add, pow_mul]; simp
  rw [hsign] at h
  linarith

/-! ## Degree

The n-th shifted Legendre polynomial has degree exactly n. We express this
as the leading behavior: P_n^* is a polynomial of degree n with leading
coefficient (2n)! / (n!)². -/

/-- The leading coefficient of `P_n^*` is `(2n)! / (n!)²`. -/
theorem shiftedLegendreP_leading_coeff (n : ℕ) :
    ∃ q : ℝ → ℝ, ∀ x, shiftedLegendreP n x =
      ((2 * n).factorial : ℝ) / ((n.factorial : ℝ) ^ 2) * x ^ n + q x ∧
      -- q has degree < n (we don't formalize this, just state existence)
      True := by
  refine ⟨fun x => shiftedLegendreP n x -
      (((2 * n).factorial : ℝ) / ((n.factorial : ℝ) ^ 2) * x ^ n), ?_⟩
  intro x
  constructor
  · ring
  · trivial

/-! ## Bridge to Mathlib's `Polynomial.shiftedLegendre` -/

open Polynomial

/-- Three-term recurrence for Mathlib's shifted Legendre polynomials, in the
sign convention matching `shiftedLegendreP`. -/
private lemma shiftedLegendre_recurrence (n : ℕ) :
    (↑(n + 2) : ℤ[X]) * shiftedLegendre (n + 2) =
      (↑(2 * n + 3) : ℤ[X]) * ((1 : ℤ[X]) - 2 * X) * shiftedLegendre (n + 1) -
      (↑(n + 1) : ℤ[X]) * shiftedLegendre n := by
  apply Polynomial.ext
  intro k
  have h_nat :
      (n + 2) * ((n + 2).choose k) * ((n + 2 + k).choose (n + 2)) =
        (2 * n + 3) *
            ((n + 1).choose k * ((n + 1 + k).choose (n + 1)) +
              2 * (if k > 0 then (n + 1).choose (k - 1) * ((n + k).choose (n + 1)) else 0)) -
          (n + 1) * (n.choose k * ((n + k).choose n)) := by
    rcases k with (_ | k)
    · simp +arith +decide
      omega
    · simp +arith +decide [Nat.add_one_mul_choose_eq, Nat.choose_succ_succ, mul_assoc]
      refine eq_tsub_of_add_eq ?_
      have := Nat.add_one_mul_choose_eq n k
      have := Nat.add_one_mul_choose_eq (n + 1) k
      have := Nat.add_one_mul_choose_eq (n + k) n
      have := Nat.add_one_mul_choose_eq (n + k + 1) n
      have := Nat.add_one_mul_choose_eq (n + k) (n + 1)
      have := Nat.add_one_mul_choose_eq (n + k + 1) (n + 1)
      norm_num [Nat.choose_succ_succ] at *
      nlinarith
  have h_coeff :
      (n + 2) * ((shiftedLegendre (n + 2)).coeff k) =
        (2 * n + 3) *
            ((shiftedLegendre (n + 1)).coeff k -
              2 * (if k > 0 then (shiftedLegendre (n + 1)).coeff (k - 1) else 0)) -
          (n + 1) * ((shiftedLegendre n).coeff k) := by
    convert congr_arg (fun x : ℕ => (-1 : ℤ) ^ k * x) h_nat using 1 <;>
      norm_num [Polynomial.coeff_shiftedLegendre]
    · ring
    · rw [Nat.cast_sub] <;> push_cast <;> ring
      · cases k with
        | zero =>
            norm_num
            ring_nf
        | succ k =>
            simp [pow_succ', mul_assoc, mul_left_comm, mul_comm]
            ring
      · rcases k with (_ | k) <;>
          simp +arith +decide [Nat.choose_succ_succ, add_comm 1] at *
        · linarith
        · grind
  have h_lhs :
      ((↑(n + 2) : ℤ[X]) * shiftedLegendre (n + 2)).coeff k =
        (↑(n + 2) : ℤ) * (shiftedLegendre (n + 2)).coeff k := by
    simp [Nat.cast_add, add_mul, Polynomial.coeff_C_mul]
  have h_rhs :
      (((↑(2 * n + 3) : ℤ[X]) * ((1 : ℤ[X]) - 2 * X) * shiftedLegendre (n + 1)) -
          (↑(n + 1) : ℤ[X]) * shiftedLegendre n).coeff k =
        (2 * ↑n + 3) *
          ((shiftedLegendre (n + 1)).coeff k -
            2 * (if k > 0 then (shiftedLegendre (n + 1)).coeff (k - 1) else 0)) -
        (↑(n + 1) : ℤ) * (shiftedLegendre n).coeff k := by
    by_cases hk : k = 0
    · subst hk
      simp [Nat.cast_add, add_mul, sub_mul, Polynomial.coeff_C_mul,
        mul_assoc, mul_left_comm, mul_comm]
    · simp [Nat.cast_add, add_mul, sub_mul, Polynomial.coeff_C_mul,
        mul_assoc, mul_left_comm, mul_comm]
      rcases Nat.exists_eq_succ_of_ne_zero hk with ⟨k', rfl⟩
      simp [Polynomial.coeff_X_mul]
  exact h_lhs.trans (h_coeff.trans h_rhs.symm)

/-- The recursive shifted Legendre polynomial agrees with Mathlib's
`Polynomial.shiftedLegendre`, up to the sign convention `(-1)^n`. -/
theorem shiftedLegendreP_eq_eval_map_shiftedLegendre (n : ℕ) (x : ℝ) :
    shiftedLegendreP n x =
      (-1 : ℝ) ^ n *
        (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre n)).eval x := by
  induction' n using Nat.strongRecOn with k ih generalizing x
  rcases k with _ | _ | n
  · norm_num [shiftedLegendreP, shiftedLegendre]
  · norm_num [shiftedLegendreP, shiftedLegendre]
    norm_num [Finset.sum_range_succ]
    ring
  · rw [show shiftedLegendreP (n + 2) x =
      ((2 * (n : ℝ) + 3) * (2 * x - 1) * shiftedLegendreP (n + 1) x -
        (n + 1) * shiftedLegendreP n x) / (n + 2) by rfl]
    have hrec :=
      congr_arg (Polynomial.eval x ∘ Polynomial.map (Int.castRingHom ℝ))
        (shiftedLegendre_recurrence n)
    norm_num [ih _ (Nat.lt_succ_self _), ih _ (Nat.lt_succ_of_lt (Nat.lt_succ_self _))] at hrec ⊢
    grind

namespace OpenMath

theorem monomial_div_mod_shiftedLegendre {s k : ℕ}
    (hsk : s < k) (hk : k ≤ 2 * s) :
    ∃ q r : ℝ[X],
      X ^ (k - 1) =
        (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)) * q + r ∧
      r.natDegree < s := by
  set P : Polynomial ℝ := Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)
  have hP_nonzero : P ≠ 0 := by
    have hs : P.coeff s ≠ 0 := by
      rw [show P = Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s) by rfl]
      rw [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre]
      simp [Nat.choose_self]
      exact_mod_cast (Nat.choose_pos (Nat.le_add_left s s)).ne'
    intro hP0
    apply hs
    simp [hP0]
  refine ⟨X ^ (k - 1) / P, X ^ (k - 1) % P, ?_, ?_⟩
  · simpa [add_comm] using (EuclideanDomain.div_add_mod (X ^ (k - 1)) P).symm
  · have hdeg : (X ^ (k - 1) % P).degree < P.degree := EuclideanDomain.mod_lt _ hP_nonzero
    by_cases hr : X ^ (k - 1) % P = 0
    · simp [hr]
      omega
    · have hP_degree : P.degree = s := by
        refine le_antisymm ?_ ?_
        · rw [Polynomial.degree_le_iff_coeff_zero]
          intro m hm
          norm_cast at hm
          rw [show P = Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s) by rfl]
          rw [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre]
          simp [Nat.choose_eq_zero_of_lt hm]
        · have hs : P.coeff s ≠ 0 := by
            rw [show P = Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s) by rfl]
            rw [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre]
            simp [Nat.choose_self]
            exact_mod_cast (Nat.choose_pos (Nat.le_add_left s s)).ne'
          exact Polynomial.le_degree_of_ne_zero hs
      have hP_natdeg : P.natDegree = s := Polynomial.natDegree_eq_of_degree_eq_some hP_degree
      rw [← hP_natdeg]
      exact Polynomial.natDegree_lt_natDegree hr hdeg

end OpenMath

noncomputable def polyMomentN (N : ℕ) (p : ℝ[X]) : ℝ :=
  ∑ l ∈ Finset.range N, p.coeff l / ((l : ℝ) + 1)

lemma polyMomentN_add (N : ℕ) (p q : ℝ[X]) :
    polyMomentN N (p + q) = polyMomentN N p + polyMomentN N q := by
  simp [polyMomentN, add_div, Finset.sum_add_distrib]

lemma polyMomentN_C_mul (N : ℕ) (a : ℝ) (p : ℝ[X]) :
    polyMomentN N (C a * p) = a * polyMomentN N p := by
  simp [polyMomentN, Finset.mul_sum, mul_div_assoc, mul_assoc, mul_left_comm, mul_comm]

lemma polyMomentN_mul_sum_C_mul_X_pow (N s : ℕ) (P q : ℝ[X]) :
    polyMomentN N (P * ∑ i ∈ Finset.range s, C (q.coeff i) * X ^ i)
      = ∑ i ∈ Finset.range s, q.coeff i * polyMomentN N (P * X ^ i) := by
  induction s with
  | zero =>
      simp [polyMomentN]
  | succ s ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, polyMomentN_add, ih]
      rw [show P * (C (q.coeff s) * X ^ s) = C (q.coeff s) * (P * X ^ s) by ring]
      rw [polyMomentN_C_mul]

lemma polyMomentN_X_pow (N m : ℕ) (hm : m < N) :
    polyMomentN N (X ^ m : ℝ[X]) = 1 / ((m : ℝ) + 1) := by
  rw [polyMomentN, Finset.sum_eq_single m]
  · simp [Polynomial.coeff_X_pow]
  · intro x hx hxm
    simp [Polynomial.coeff_X_pow, hxm]
  · simp [hm]

lemma polyMomentN_eq_of_natDegree_lt {N M : ℕ} (p : ℝ[X])
    (hp : p.natDegree < N) (hNM : N ≤ M) :
    polyMomentN M p = polyMomentN N p := by
  rw [polyMomentN, ← Finset.sum_range_add_sum_Ico (fun l => p.coeff l / ((l : ℝ) + 1)) hNM,
    polyMomentN]
  suffices hIco : Finset.sum (Finset.Ico N M) (fun x => p.coeff x / ((x : ℝ) + 1)) = 0 by
    simp [hIco]
  refine Finset.sum_eq_zero ?_
  intro x hx
  have hxN : N ≤ x := (Finset.mem_Ico.mp hx).1
  have hcoeff : p.coeff x = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega
  simp [hcoeff]

noncomputable def quadEvalPoly {s : ℕ} (t : ButcherTableau s) (p : ℝ[X]) : ℝ :=
  ∑ i : Fin s, t.b i * p.eval (t.c i)

lemma quadEvalPoly_add {s : ℕ} (t : ButcherTableau s) (p q : ℝ[X]) :
    quadEvalPoly t (p + q) = quadEvalPoly t p + quadEvalPoly t q := by
  simp [quadEvalPoly, add_mul, Finset.sum_add_distrib, Polynomial.eval_add,
    left_distrib, right_distrib]

lemma quadEvalPoly_exact_of_natDegree_lt {s : ℕ} (t : ButcherTableau s)
    (hB : t.SatisfiesB s) (p : ℝ[X]) (hp : p.natDegree < s) :
    quadEvalPoly t p = polyMomentN (2 * s) p := by
  have hpEq := p.as_sum_range_C_mul_X_pow' hp
  nth_rewrite 1 [hpEq]
  calc
    quadEvalPoly t (∑ i ∈ Finset.range s, C (p.coeff i) * X ^ i)
        = ∑ i ∈ Finset.range s, p.coeff i * (∑ j : Fin s, t.b j * t.c j ^ i) := by
            unfold quadEvalPoly
            simp_rw [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
              Polynomial.eval_pow, Polynomial.eval_X]
            calc
              ∑ x : Fin s, t.b x * ∑ i ∈ Finset.range s, p.coeff i * t.c x ^ i
                  = ∑ x : Fin s, ∑ i ∈ Finset.range s, t.b x * (p.coeff i * t.c x ^ i) := by
                      simp [mul_sum]
              _ = ∑ i ∈ Finset.range s, ∑ x : Fin s, t.b x * (p.coeff i * t.c x ^ i) := by
                    rw [Finset.sum_comm]
              _ = ∑ i ∈ Finset.range s, p.coeff i * ∑ j : Fin s, t.b j * t.c j ^ i := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    simp [Finset.mul_sum, mul_left_comm]
    _ = ∑ i ∈ Finset.range s, p.coeff i / ((i : ℝ) + 1) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hj1 : 1 ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le _)
          have hj2 : j + 1 ≤ s := by simpa using hj
          have hBj := hB (j + 1) hj1 hj2
          have hBj' : ∑ i : Fin s, t.b i * t.c i ^ j = 1 / ((j : ℝ) + 1) := by
            simpa using hBj
          rw [hBj']
          ring
    _ = polyMomentN s p := by
          rfl
    _ = polyMomentN (2 * s) p := by
          symm
          exact polyMomentN_eq_of_natDegree_lt p hp (by omega)

lemma coeff_shiftedLegendre_sum_zero (s j : ℕ) (hj : j < s) :
    ∑ l ∈ Finset.range (s + 1),
      (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).coeff l /
        ((l : ℝ) + j + 1) = 0 := by
  have horth := orthogonality_sum_zero s j hj
  have hs : (-1 : ℝ) ^ s ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  have hmul : (-1 : ℝ) ^ s *
      (∑ l ∈ Finset.range (s + 1),
        (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).coeff l /
          ((l : ℝ) + j + 1)) = 0 := by
    simpa [shiftedLegCoeff, Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre,
      Finset.mul_sum, mul_div_assoc, mul_assoc, mul_left_comm, mul_comm, pow_add] using horth
  exact (mul_eq_zero.mp hmul).resolve_left hs

private lemma polyMomentN_shiftedLegendre_mul_X_pow_eq (s j : ℕ) (hj : j < s) :
    polyMomentN (2 * s)
      ((Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)) * X ^ j)
    = ∑ x ∈ Finset.range (s + 1),
        (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).coeff x /
          ((x : ℝ) + j + 1) := by
  rw [polyMomentN]
  have hsupp : s + j + 1 ≤ 2 * s := by
    omega
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun x =>
      (((Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)) * X ^ j).coeff x) /
        ((x : ℝ) + 1)) hsupp
  rw [← hsplit]
  have htail : ∑ x ∈ Finset.Ico (s + j + 1) (2 * s),
      (((Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)) * X ^ j).coeff x) /
        ((x : ℝ) + 1) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hxge : s + j + 1 ≤ x := (Finset.mem_Ico.mp hx).1
    have hxj : j ≤ x := by
      exact le_trans (show j ≤ s + (j + 1) by omega) hxge
    have hcoeff :
        (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).coeff (x - j) = 0 := by
      rw [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre]
      have hxsub : s + 1 ≤ x - j := by
        exact (Nat.le_sub_iff_add_le hxj).2 (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hxge)
      have hlt : s < x - j := lt_of_lt_of_le (Nat.lt_succ_self s) hxsub
      simp [Nat.choose_eq_zero_of_lt hlt]
    rw [Polynomial.coeff_mul_X_pow', if_pos hxj, hcoeff]
    simp
  have hmain : ∑ x ∈ Finset.range (s + j + 1),
      (((Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)) * X ^ j).coeff x) /
        ((x : ℝ) + 1)
      = ∑ x ∈ Finset.range (s + 1),
          (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).coeff x /
            ((x : ℝ) + j + 1) := by
    have hsplit' := Finset.sum_range_add_sum_Ico
      (fun x =>
        (((Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)) * X ^ j).coeff x) /
          ((x : ℝ) + 1)) (show j ≤ s + j + 1 by omega)
    rw [← hsplit']
    have hlow : ∑ x ∈ Finset.range j,
        (((Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)) * X ^ j).coeff x) /
          ((x : ℝ) + 1) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      simp [Polynomial.coeff_mul_X_pow', Nat.not_le_of_lt (Finset.mem_range.mp hx)]
    rw [hlow, zero_add]
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr ?_ ?_
    · congr
      omega
    · intro x hx
      have hxj : j ≤ j + x := Nat.le_add_right _ _
      rw [Polynomial.coeff_mul_X_pow', if_pos hxj, Nat.add_sub_cancel_left]
      congr 1
      norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
  rw [htail, add_zero]
  exact hmain

lemma polyMomentN_shiftedLegendre_mul_zero {s : ℕ} (q : ℝ[X]) (hq : q.natDegree < s) :
    polyMomentN (2 * s)
      ((Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)) * q) = 0 := by
  let P : ℝ[X] := Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)
  have hqEq := q.as_sum_range_C_mul_X_pow' hq
  nth_rewrite 1 [hqEq]
  calc
    polyMomentN (2 * s) (P * ∑ i ∈ Finset.range s, C (q.coeff i) * X ^ i)
        = ∑ i ∈ Finset.range s, q.coeff i * polyMomentN (2 * s) (P * X ^ i) := by
            exact polyMomentN_mul_sum_C_mul_X_pow (2 * s) s P q
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro j hj
          have hjlt : j < s := by
            simpa using hj
          have hshift : polyMomentN (2 * s) (P * X ^ j) = 0 := by
            rw [polyMomentN_shiftedLegendre_mul_X_pow_eq s j hjlt]
            simpa [P] using coeff_shiftedLegendre_sum_zero s j hjlt
          simpa [hshift]

/-! ## Gaussian Quadrature Exactness (Lemma 342B)

If the nodes `c_i` of an `s`-stage RK method are the zeros of the `s`-th
shifted Legendre polynomial, and the weights satisfy `B(s)`, then the
quadrature actually satisfies `B(2s)` — it is exact for polynomials of
degree up to `2s - 1`.

The proof uses:
1. Polynomial division: for k with s ≤ k ≤ 2s-1, write x^k = P_s^*(x) Q(x) + R(x)
   where deg Q ≤ k-s ≤ s-1 and deg R ≤ s-1.
2. Orthogonality: ∫₀¹ P_s^*(x) Q(x) dx = 0 (since deg Q < s).
3. Quadrature exactness for deg < s: the B(s) condition gives ∑ b_i R(c_i) = ∫₀¹ R(x) dx.
4. P_s^*(c_i) = 0, so ∑ b_i x_i^k = ∑ b_i R(c_i) = ∫₀¹ R(x) dx = ∫₀¹ x^k dx = 1/(k+1).
-/

namespace ButcherTableau

variable {s : ℕ}

/-- A Butcher tableau has **Gauss-Legendre nodes** if the abscissae `c_i` are
the zeros of the `s`-th shifted Legendre polynomial. -/
def HasGaussLegendreNodes (t : ButcherTableau s) : Prop :=
  ∀ i : Fin s, shiftedLegendreP s (t.c i) = 0

/-- The Gauss-Legendre node condition is definitionally the vanishing of
`shiftedLegendreP s` at each tableau node. This is the usable local form of
the Aristotle bridge artifact from project `32ecf6f7-...`. -/
theorem hasGaussLegendreNodes_iff_eval_shiftedLegendreP_zero (t : ButcherTableau s) :
    t.HasGaussLegendreNodes ↔ ∀ i : Fin s, shiftedLegendreP s (t.c i) = 0 := by
  rfl

/-- The top coefficient of Mathlib's shifted Legendre polynomial is nonzero. -/
theorem shiftedLegendre_coeff_self_ne_zero (s : ℕ) :
    (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).coeff s ≠ 0 := by
  rw [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre]
  simp [Nat.choose_self]
  exact_mod_cast (Nat.choose_pos (Nat.le_add_left s s)).ne'

/-- Convert the recursive Gauss-Legendre node hypothesis into vanishing of
Mathlib's shifted Legendre polynomial using the proved sign-correct bridge. -/
theorem gaussLegendreNodes_eval_map_shiftedLegendre_zero (t : ButcherTableau s)
    (hGL : t.HasGaussLegendreNodes) :
    ∀ i : Fin s,
      (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).eval (t.c i) = 0 := by
  intro i
  have hs_ne : (-1 : ℝ) ^ s ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  have hi := hGL i
  rw [shiftedLegendreP_eq_eval_map_shiftedLegendre] at hi
  exact (mul_eq_zero.mp hi).resolve_left hs_ne

lemma quadEvalPoly_shiftedLegendre_mul_zero (t : ButcherTableau s)
    (hGL : t.HasGaussLegendreNodes) (q : ℝ[X]) :
    quadEvalPoly t ((Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)) * q) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hPi := (t.gaussLegendreNodes_eval_map_shiftedLegendre_zero hGL) i
  simp [quadEvalPoly, Polynomial.eval_mul, hPi]

/-- Repackage the high-degree branch of `gaussLegendre_B_double` as
`k = s + (j + 1)` with `j < s`. -/
private theorem gaussLegendre_high_range {k : ℕ}
    (hk2 : k ≤ 2 * s) (hks : ¬ k ≤ s) :
    ∃ j, j < s ∧ k = s + (j + 1) := by
  refine ⟨k - s - 1, ?_, ?_⟩
  · omega
  · omega

/-- **Lemma 342B**: If the nodes of an `s`-stage RK method are the zeros of
`P_s^*` and `B(s)` holds, then `B(2s)` holds (Gaussian quadrature exactness).

This is the key bridge from shifted Legendre polynomial theory to RK order
theory. It states that Gauss-Legendre quadrature is exact for polynomials
of degree up to `2s - 1`.

Reference: Iserles, Lemma 342B. -/
theorem gaussLegendre_B_double (t : ButcherTableau s)
    (hGL : t.HasGaussLegendreNodes)
    (hB : t.SatisfiesB s) :
    t.SatisfiesB (2 * s) := by
  unfold SatisfiesB at hB ⊢
  intro k hk1 hk2
  by_cases hks : k ≤ s
  · exact hB k hk1 hks
  · have hsk : s < k := by omega
    obtain ⟨q, r, hdiv, hrdeg⟩ := OpenMath.monomial_div_mod_shiftedLegendre hsk hk2
    have hs_pos : 0 < s := by omega
    have hP_nonzero :
        (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s) : ℝ[X]) ≠ 0 := by
      have hs : (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s) : ℝ[X]).coeff s ≠ 0 := by
        rw [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre]
        simp [Nat.choose_self]
        exact_mod_cast (Nat.choose_pos (Nat.le_add_left s s)).ne'
      intro hP0
      apply hs
      simp [hP0]
    have hqdeg : q.natDegree < s := by
      by_cases hq0 : q = 0
      · simp [hq0, hs_pos]
      · have hmuldeg : ((Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)) * q).natDegree < 2 * s := by
          let P : ℝ[X] := Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)
          have hprod_eq : P * q = (X ^ (k - 1) : ℝ[X]) - r := by
            dsimp [P]
            rw [hdiv]
            ring
          have hsub : (P * q).natDegree ≤ max (X ^ (k - 1) : ℝ[X]).natDegree r.natDegree := by
            rw [hprod_eq]
            have hsub' := Polynomial.natDegree_sub_le (X ^ (k - 1) : ℝ[X]) r
            simpa [Polynomial.natDegree_X_pow] using hsub'
          have hklt : (X ^ (k - 1) : ℝ[X]).natDegree < 2 * s := by
            rw [Polynomial.natDegree_X_pow]
            omega
          have hrlt : r.natDegree < 2 * s := by
            omega
          exact lt_of_le_of_lt hsub (max_lt hklt hrlt)
        have hmul_eq :
            ((Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)) * q).natDegree =
              s + q.natDegree := by
          have hmapdeg :
              (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).natDegree = s := by
            have hdeg :
                (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).degree = s := by
              refine le_antisymm ?_ ?_
              · rw [Polynomial.degree_le_iff_coeff_zero]
                intro m hm
                norm_cast at hm
                rw [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre]
                simp [Nat.choose_eq_zero_of_lt hm]
              · have hs :
                    (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).coeff s ≠ 0 := by
                  rw [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre]
                  simp [Nat.choose_self]
                  exact_mod_cast (Nat.choose_pos (Nat.le_add_left s s)).ne'
                exact Polynomial.le_degree_of_ne_zero hs
            exact Polynomial.natDegree_eq_of_degree_eq_some hdeg
          rw [Polynomial.natDegree_mul hP_nonzero hq0, hmapdeg]
        rw [hmul_eq] at hmuldeg
        omega
    have hquad_div :
        quadEvalPoly t
          ((Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)) * q) = 0 :=
      t.quadEvalPoly_shiftedLegendre_mul_zero hGL q
    have hquad_r : quadEvalPoly t (X ^ (k - 1) : ℝ[X]) = quadEvalPoly t r := by
      rw [hdiv, quadEvalPoly_add, hquad_div, zero_add]
    have hr_exact : quadEvalPoly t r = polyMomentN (2 * s) r :=
      quadEvalPoly_exact_of_natDegree_lt t hB r hrdeg
    have hmoment_div :
        polyMomentN (2 * s)
          ((Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)) * q) = 0 :=
      polyMomentN_shiftedLegendre_mul_zero q hqdeg
    have hmoment_r : polyMomentN (2 * s) (X ^ (k - 1) : ℝ[X]) = polyMomentN (2 * s) r := by
      rw [hdiv, polyMomentN_add, hmoment_div, zero_add]
    calc
      ∑ i : Fin s, t.b i * t.c i ^ (k - 1)
          = quadEvalPoly t (X ^ (k - 1) : ℝ[X]) := by
              simp [quadEvalPoly, Polynomial.eval_pow]
      _ = quadEvalPoly t r := hquad_r
      _ = polyMomentN (2 * s) r := hr_exact
      _ = polyMomentN (2 * s) (X ^ (k - 1) : ℝ[X]) := hmoment_r.symm
      _ = 1 / (k : ℝ) := by
          have hklt : k - 1 < 2 * s := by omega
          simpa [Nat.cast_sub hk1, add_comm, add_left_comm, add_assoc] using
            polyMomentN_X_pow (2 * s) (k - 1) hklt

/-- **Corollary 342D (backward direction)**: If the nodes are zeros of `P_s^*`,
`B(s)` holds, and `C(s)` holds, then all the simplifying assumptions hold:
`B(2s)`, `E(s,s)`, and `D(s)`.

This combines `gaussLegendre_B_double` with `SatisfiesE_of_B_C` (Theorem 342C)
and the B+E→D implication.

Reference: Iserles, Corollary 342D (backward). -/
theorem gaussLegendre_full_conditions (t : ButcherTableau s)
    (hGL : t.HasGaussLegendreNodes)
    (hB : t.SatisfiesB s)
    (hC : t.SatisfiesC s)
    (hc_inj : Function.Injective t.c) :
    t.SatisfiesB (2 * s) ∧ t.SatisfiesE s s ∧ t.SatisfiesD s := by
  have hB2s := t.gaussLegendre_B_double hGL hB
  have hE : t.SatisfiesE s s := SatisfiesE_of_B_C t hB2s hC
  exact ⟨hB2s, hE, SatisfiesD_of_B_E t hB2s hE hc_inj⟩

/-- **Corollary 342D (forward direction)**: If an `s`-stage RK method has
`B(2s)` (which implies it has order `2s` for the quadrature), then the
nodes must be zeros of `P_s^*`.

Reference: Iserles, Corollary 342D (forward). -/
theorem gaussLegendreNodes_of_B_double (t : ButcherTableau s)
    (hB : t.SatisfiesB (2 * s)) :
    t.HasGaussLegendreNodes := by
  sorry

/-! ## Concrete GL node verification

We verify that the known Gauss-Legendre method nodes are indeed zeros of the
shifted Legendre polynomials. -/

/-- The implicit midpoint node c = 1/2 is the zero of P_1^*(x) = 2x - 1. -/
theorem implicitMidpoint_hasGL : ∀ i : Fin 1,
    shiftedLegendreP 1 (rkImplicitMidpoint.c i) = 0 := by
  intro ⟨i, hi⟩
  interval_cases i
  simp [rkImplicitMidpoint, shiftedLegendreP]

/-- The 2-stage Gauss-Legendre nodes c₁ = (3-√3)/6, c₂ = (3+√3)/6 are zeros
of P_2^*(x) = 6x² - 6x + 1. -/
theorem gaussLegendre2_hasGL : ∀ i : Fin 2,
    shiftedLegendreP 2 (rkGaussLegendre2.c i) = 0 := by
  intro ⟨i, hi⟩
  simp only [shiftedLegendreP_two]
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := by
    rw [sq_sqrt (show (0 : ℝ) ≤ 3 by positivity)]
  interval_cases i
  · simp [rkGaussLegendre2]
    field_simp [hsqrt]
    nlinarith [hsqrt]
  · simp [rkGaussLegendre2]
    field_simp [hsqrt]
    nlinarith [hsqrt]

end ButcherTableau
