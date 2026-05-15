/-
Helper lemmas for the Butcher §342 (342d) norm-square integral.

Adapted from the Aristotle proof (cycle 281, project
`d4ce527b-b714-4e51-b0a6-e3d06302d7fa`) of
`butcherShiftedLegendre_norm_sq : ∫₀¹ (P_n^*(x))² dx = 1 / (2n + 1)`.

The helpers exposed:
- `iterate_derivative_natDegree_eq` — `n`-th derivative of a degree-`n`
  polynomial is the constant `C (leadingCoeff · n!)`.
- `poly_ibp_vanishing` — IBP on `[0,1]` for two polynomials when one
  vanishes at both endpoints.
- `iterated_ibp_XnOneSubXn` — iterated IBP × `n` transferring all
  derivatives from `X^n · (1-X)^n` onto an arbitrary polynomial `p`.
- `integral_pow_mul_one_sub_pow` — the Euler/Beta integral
  `∫₀¹ x^n · (1-x)^n dx = (n!)² / (2n+1)!`, via Mathlib's complex
  Beta function `Complex.betaIntegral_eval_nat_add_one_right`.
- `choose_mul_factorial_sq_div` — arithmetic identity
  `C(2n,n) · (n!)² / (2n+1)! = 1 / (2n+1)`.
-/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.BigOperators

open Polynomial MeasureTheory intervalIntegral Finset

namespace OpenMath.Chapter3.Section342Helpers

/-! ### `n`-th derivative of a degree-`n` polynomial -/

/-- The `n`-th derivative of a polynomial of `natDegree` exactly `n` is
the constant polynomial `C (leadingCoeff · n!)`. -/
lemma iterate_derivative_natDegree_eq {p : Polynomial ℝ} {n : ℕ}
    (hn : p.natDegree = n) :
    Polynomial.derivative^[n] p = Polynomial.C (p.leadingCoeff * n.factorial) := by
  have hle : (Polynomial.derivative^[n] p).natDegree ≤ 0 := by
    have h := Polynomial.natDegree_iterate_derivative p n
    omega
  have hcoeff : (Polynomial.derivative^[n] p).coeff 0
      = p.leadingCoeff * n.factorial := by
    rw [Polynomial.coeff_iterate_derivative, zero_add,
        Nat.descFactorial_self, nsmul_eq_mul, Polynomial.leadingCoeff,
        hn, mul_comm]
  rw [Polynomial.eq_C_of_natDegree_le_zero hle, hcoeff]

/-! ### Polynomial IBP with vanishing boundary -/

/-- Integration by parts on `[0,1]` for two polynomials when `q`
vanishes at both endpoints. -/
lemma poly_ibp_vanishing (p q : Polynomial ℝ) (hq0 : q.eval 0 = 0)
    (hq1 : q.eval 1 = 0) :
    ∫ x in (0:ℝ)..1, p.eval x * (Polynomial.derivative q).eval x =
      -(∫ x in (0:ℝ)..1, (Polynomial.derivative p).eval x * q.eval x) := by
  have hu : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x => p.eval x)
      ((Polynomial.derivative p).eval x) x := fun x _ => p.hasDerivAt x
  have hv : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x => q.eval x)
      ((Polynomial.derivative q).eval x) x := fun x _ => q.hasDerivAt x
  have hu' : IntervalIntegrable
      (fun x => (Polynomial.derivative p).eval x) volume 0 1 :=
    (Polynomial.continuous _).intervalIntegrable _ _
  have hv' : IntervalIntegrable
      (fun x => (Polynomial.derivative q).eval x) volume 0 1 :=
    (Polynomial.continuous _).intervalIntegrable _ _
  have h := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  simp [hq0, hq1] at h
  linarith

/-! ### Iterated IBP for `X^n · (1-X)^n` -/

/-- Boundary vanishing at `x = 0`. -/
lemma deriv_iter_XnOneMinusXn_eval_zero (n k : ℕ) (hk : k < n) :
    (Polynomial.derivative^[k]
      ((Polynomial.X : Polynomial ℝ) ^ n * (1 - Polynomial.X) ^ n)).eval 0 = 0 := by
  rw [Polynomial.iterate_derivative_mul]
  rw [Polynomial.eval_finset_sum, Finset.sum_eq_zero]
  intros
  simp +decide [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
                Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
                Polynomial.eval_natCast, Polynomial.eval_ofNat,
                Polynomial.iterate_derivative_X_pow_eq_smul,
                Nat.descFactorial_eq_zero_iff_lt.mpr
                  (Nat.sub_lt (pos_of_gt hk) (Nat.succ_pos _))]
  exact Or.inr <| Or.inr <| Or.inl <| Nat.sub_ne_zero_of_lt <| by omega

/-- Boundary vanishing at `x = 1`. -/
lemma deriv_iter_XnOneMinusXn_eval_one (n k : ℕ) (hk : k < n) :
    (Polynomial.derivative^[k]
      ((Polynomial.X : Polynomial ℝ) ^ n * (1 - Polynomial.X) ^ n)).eval 1 = 0 := by
  have h_symm₁ : ((Polynomial.derivative^[k]
        ((Polynomial.X : Polynomial ℝ) ^ n * (1 - Polynomial.X) ^ n)).eval 1) =
      ((Polynomial.derivative^[k]
        ((1 - Polynomial.X) ^ n * (Polynomial.X : Polynomial ℝ) ^ n)).eval 1) := by
    rw [mul_comm]
  have h_symm₂ : ((Polynomial.derivative^[k]
        ((1 - Polynomial.X) ^ n * (Polynomial.X : Polynomial ℝ) ^ n)).eval 1) =
      ((Polynomial.derivative^[k]
        ((Polynomial.X : Polynomial ℝ) ^ n * (1 - Polynomial.X) ^ n)).eval 0) *
        (-1) ^ k := by
    have h_chain : ∀ (p : Polynomial ℝ), ((Polynomial.derivative^[k]
        (p.comp (1 - Polynomial.X))).eval 1) =
        ((Polynomial.derivative^[k] p).eval 0) * (-1) ^ k := by
      simp_all +decide [mul_comm]
    convert h_chain ((Polynomial.X : Polynomial ℝ) ^ n
        * (1 - Polynomial.X) ^ n) using 1
    norm_num [mul_comm]
  have := deriv_iter_XnOneMinusXn_eval_zero n k hk
  aesop

/-- Internal recursion for iterated IBP: peels off `m ≤ n` derivatives. -/
private lemma gen_ibp (n m : ℕ) (hm : m ≤ n) :
    ∀ p : Polynomial ℝ,
    ∫ x in (0:ℝ)..1, p.eval x *
      (Polynomial.derivative^[m]
        ((Polynomial.X : Polynomial ℝ) ^ n * (1 - Polynomial.X) ^ n)).eval x =
    (-1 : ℝ) ^ m * ∫ x in (0:ℝ)..1,
      (Polynomial.derivative^[m] p).eval x *
      ((Polynomial.X : Polynomial ℝ) ^ n * (1 - Polynomial.X) ^ n).eval x := by
  induction m with
  | zero => intro p; simp
  | succ m ih =>
    intro p
    rw [Function.iterate_succ_apply']
    have hm' : m < n := Nat.lt_of_succ_le hm
    rw [poly_ibp_vanishing p _ (deriv_iter_XnOneMinusXn_eval_zero n m hm')
      (deriv_iter_XnOneMinusXn_eval_one n m hm')]
    rw [ih (Nat.le_of_lt hm') (Polynomial.derivative p)]
    have hcomm : Polynomial.derivative^[m] (Polynomial.derivative p) =
        Polynomial.derivative (Polynomial.derivative^[m] p) :=
      Function.Commute.iterate_self Polynomial.derivative m p
    rw [Function.iterate_succ_apply', hcomm]
    ring

/-- **Iterated IBP × `n`** transferring all `n` derivatives from
`X^n · (1-X)^n` onto a polynomial `p`, with overall sign `(-1)^n`. -/
lemma iterated_ibp_XnOneSubXn (p : Polynomial ℝ) (n : ℕ) :
    ∫ x in (0:ℝ)..1, p.eval x *
      (Polynomial.derivative^[n]
        ((Polynomial.X : Polynomial ℝ) ^ n * (1 - Polynomial.X) ^ n)).eval x =
    (-1 : ℝ) ^ n * ∫ x in (0:ℝ)..1,
      (Polynomial.derivative^[n] p).eval x *
      ((Polynomial.X : Polynomial ℝ) ^ n * (1 - Polynomial.X) ^ n).eval x :=
  gen_ibp n n le_rfl p

/-! ### Beta integral `∫₀¹ x^n (1-x)^n dx = (n!)² / (2n+1)!` -/

/-- Auxiliary product identity:
`(n+1).ascFactorial (n+1) = (n+1)(n+2)…(2n+1) = (2n+1)! / n!`,
phrased in multiplicative form to avoid `ℕ`-division. -/
private lemma ascFactorial_succ_self (n : ℕ) :
    (n + 1).ascFactorial (n + 1) * n.factorial = (2 * n + 1).factorial := by
  rw [mul_comm, Nat.factorial_mul_ascFactorial]
  congr 1; ring

/-- The Beta integral `∫₀¹ x^n (1-x)^n dx = (n!)² / (2n+1)!` over `ℝ`. -/
lemma integral_pow_mul_one_sub_pow (n : ℕ) :
    ∫ x in (0:ℝ)..1, x ^ n * (1 - x) ^ n =
      ((n.factorial : ℝ) ^ 2 / ((2 * n + 1).factorial : ℝ)) := by
  -- Step 1: pointwise equality between the real integrand cast to ℂ
  -- and the integrand of `Complex.betaIntegral (n+1) (n+1)`.
  have hreal : ∀ x : ℝ, ((x ^ n * (1 - x) ^ n : ℝ) : ℂ) =
      (x : ℂ) ^ ((((n : ℕ) + 1 : ℕ) : ℂ) - 1) *
        ((1 : ℂ) - (x : ℂ)) ^ ((((n : ℕ) + 1 : ℕ) : ℂ) - 1) := by
    intro x
    have hexp : ((((n : ℕ) + 1 : ℕ) : ℂ) - 1) = ((n : ℕ) : ℂ) := by
      push_cast; ring
    rw [hexp]
    rw [show ((1 : ℂ) - (x : ℂ)) = ((1 - x : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.cpow_natCast, Complex.cpow_natCast]
    push_cast
    ring
  -- Step 2: Complex Beta integral = real integral cast to ℂ.
  have h_int_eq :
      Complex.betaIntegral (((n : ℕ) + 1 : ℕ) : ℂ) (((n : ℕ) + 1 : ℕ) : ℂ) =
        ((∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n : ℝ) : ℂ) := by
    unfold Complex.betaIntegral
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr ?_
    intros x _
    exact (hreal x).symm
  -- Step 3: evaluate the complex Beta integral.
  have hu : (0 : ℝ) < ((((n : ℕ) + 1 : ℕ) : ℂ)).re := by
    rw [Complex.natCast_re]
    exact_mod_cast Nat.succ_pos n
  have h_beta_raw := Complex.betaIntegral_eval_nat_add_one_right hu n
  -- h_beta_raw : Complex.betaIntegral (↑(n+1)) (↑n + 1) =
  --              ↑n.factorial / ∏ j ∈ range (n+1), (↑(n+1) + ↑j)
  -- Move (↑n + 1) to (↑(n+1)) on both sides for uniformity.
  have hnplus1 : (((n : ℕ) : ℂ) + 1) = (((n : ℕ) + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hnplus1] at h_beta_raw
  -- Step 4: compute the product `∏ (n+1+j) = (2n+1)! / n!`.
  have hprod_nat : (∏ j ∈ Finset.range (n + 1), (n + 1 + j)) * n.factorial =
      (2 * n + 1).factorial := by
    rw [← Nat.ascFactorial_eq_prod_range]
    exact ascFactorial_succ_self n
  have hfact_ne : (n.factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2n1_ne : (((2 * n + 1).factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hprod_cast :
      ∏ j ∈ Finset.range (n + 1), (((((n : ℕ) + 1 : ℕ) : ℂ)) + (j : ℂ)) =
        (((2 * n + 1).factorial : ℕ) : ℂ) / (n.factorial : ℂ) := by
    rw [eq_div_iff hfact_ne]
    have h_cast : (∏ j ∈ Finset.range (n + 1),
        (((((n : ℕ) + 1 : ℕ) : ℂ)) + (j : ℂ))) =
        ((∏ j ∈ Finset.range (n + 1), ((n + 1 + j : ℕ))) : ℂ) := by
      push_cast
      rfl
    rw [h_cast]
    exact_mod_cast hprod_nat
  rw [hprod_cast] at h_beta_raw
  -- Step 5: combine the equations and take the real part.
  rw [h_int_eq] at h_beta_raw
  -- h_beta_raw : ↑(real integral) = ↑n.factorial / (↑(2n+1)! / ↑n.factorial)
  have h_collapse : (n.factorial : ℂ) /
      ((((2 * n + 1).factorial : ℕ) : ℂ) / (n.factorial : ℂ)) =
      (((n.factorial : ℝ) ^ 2 / ((2 * n + 1).factorial : ℝ)) : ℂ) := by
    rw [div_div_eq_mul_div]
    push_cast
    field_simp
  rw [h_collapse] at h_beta_raw
  exact_mod_cast h_beta_raw

/-! ### Arithmetic identity -/

/-- `C(2n,n) · (n!)² / (2n+1)! = 1 / (2n+1)`. -/
lemma choose_mul_factorial_sq_div (n : ℕ) :
    (Nat.choose (2 * n) n : ℝ) *
        ((n.factorial : ℝ) ^ 2 / ((2 * n + 1).factorial : ℝ)) =
      1 / (2 * n + 1) := by
  -- Identity at ℕ: (2n+1)! = (2n+1) * C(2n,n) * n! * n!.
  have h_nat : (2 * n + 1).factorial = (2 * n + 1) * Nat.choose (2 * n) n
      * n.factorial * n.factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial
      (show n ≤ 2 * n from by omega)
    have hsub : 2 * n - n = n := by omega
    rw [hsub] at h
    rw [Nat.factorial_succ, ← h]
    ring
  have hfact_n_ne : (n.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2n1_ne : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hchoose_pos : (0 : ℕ) < Nat.choose (2 * n) n :=
    Nat.choose_pos (by omega)
  have hchoose_ne : (Nat.choose (2 * n) n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hchoose_pos.ne'
  -- Cast the natural identity to ℝ.
  have h_real : ((2 * n + 1).factorial : ℝ) =
      (2 * (n : ℝ) + 1) * (Nat.choose (2 * n) n : ℝ) *
        (n.factorial : ℝ) * (n.factorial : ℝ) := by
    exact_mod_cast h_nat
  rw [h_real]
  field_simp

end OpenMath.Chapter3.Section342Helpers
