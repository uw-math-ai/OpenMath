import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Real.Basic

/-!
# Butcher §342 — Shifted Legendre polynomials on `[0,1]`

This file opens Butcher §342 by defining the *shifted Legendre
polynomials* `P_n^*` on `[0,1]` in the sign convention used by
Butcher and proving the normalisation `P_n^*(1) = 1` (342b) together
with the parity identity `P_n^*(1 - x) = (-1)^n P_n^*(x)` (342c).

## Anchor entity

`lem:342A` (Butcher, *Numerical Methods for Ordinary Differential
Equations*, 3rd ed., §342, p. 236). The textbook statement (verbatim
from `extraction/formalization_data/entities/lem_342A.json`):

> There exist polynomials `P_n^* : [0, 1] → ℝ`, of degrees `n`, for
> `n = 0, 1, 2, …` with the properties that
>   `∫₀¹ P_m^*(x) P_n^*(x) dx = 0`, `m ≠ n`,                 (342a)
>   `P_n^*(1) = 1`,                                           (342b)
> Furthermore, the polynomials defined by (342a) and (342b) have
> the following additional properties:
>   `P_n^*(1 - x) = (-1)^n P_n^*(x)`,                         (342c)
>   `∫₀¹ P_n^*(x)^2 dx = 1/(2n + 1)`,                         (342d)
>   `P_n^*(x) = (1/n!) (d/dx)^n ((x^2 - x)^n)`,               (342e)
>   `n P_n^*(x) = (2x-1)(2n-1) P_{n-1}^*(x) - (n-1) P_{n-2}^*(x)`,
>                                                              (342f)
>   `P_n^*` has `n` distinct real zeros in `(0, 1)`.           (342g)

## Mathlib bridge

Mathlib supplies `Polynomial.shiftedLegendre n : ℤ[X]` in
`Mathlib.RingTheory.Polynomial.ShiftedLegendre`, with the explicit
coefficient formula
`(shiftedLegendre n).coeff k = (-1)^k * C(n,k) * C(n+k,n)`. Mathlib's
sign convention sets `shiftedLegendre n |_(x = 0) = 1` and
`shiftedLegendre n |_(x = 1) = (-1)^n`, whereas Butcher's
normalisation (342b) demands `P_n^*(1) = 1`. The two conventions are
related by the parity factor `(-1)^n` (equivalently, by the mirror
`x ↦ 1 - x` via `Polynomial.shiftedLegendre_eval_symm`). We therefore
define `butcherShiftedLegendre n = (-1)^n * (shiftedLegendre n).map (Int.castRingHom ℝ)`.

(342a), (342d)–(342g) are deferred to subsequent cycles. (342e) will
flow from Mathlib's `factorial_mul_shiftedLegendre_eq`; (342a) requires
a substantive integration-by-parts proof on Rodrigues' formula.
-/

namespace OpenMath.Chapter3.Section342

open Polynomial

/-- **Butcher's shifted Legendre polynomial** `P_n^*` on `[0,1]`
(Butcher §342, p. 236). Defined as `(-1)^n` times Mathlib's
`Polynomial.shiftedLegendre n` (cast to `ℝ`). This sign choice
realises Butcher's normalisation `P_n^*(1) = 1` (342b) — see
`butcherShiftedLegendre_eval_one`. -/
noncomputable def butcherShiftedLegendre (n : ℕ) : Polynomial ℝ :=
  Polynomial.C ((-1 : ℝ) ^ n) *
    (Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)

/-- Helper: the integer-coefficient `shiftedLegendre n` evaluates to `1`
at `x = 0`, since the constant term is `(-1)^0 * C(n,0) * C(n,n) = 1`. -/
private lemma shiftedLegendre_eval_zero_int (n : ℕ) :
    (Polynomial.shiftedLegendre n).eval (0 : ℤ) = 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_shiftedLegendre]
  simp

/-- Helper: the integer-coefficient `shiftedLegendre n` evaluates to
`(-1)^n` at `x = 1`, obtained from `shiftedLegendre_eval_symm` via the
value at `x = 0`. -/
private lemma shiftedLegendre_eval_one_int (n : ℕ) :
    (Polynomial.shiftedLegendre n).eval (1 : ℤ) = (-1) ^ n := by
  -- Mathlib's symmetry: aeval 1 p = (-1)^n * aeval (1 - 1) p = (-1)^n * aeval 0 p.
  have hsymm := Polynomial.shiftedLegendre_eval_symm n (R := ℤ) 1
  rw [show ((1 : ℤ) - 1 : ℤ) = 0 from by ring] at hsymm
  -- aeval over ℤ-poly evaluated at an integer is just `.eval`.
  rw [Polynomial.coe_aeval_eq_eval, Polynomial.coe_aeval_eq_eval,
      shiftedLegendre_eval_zero_int] at hsymm
  -- hsymm : (shiftedLegendre n).eval 1 = (-1)^n * 1
  simpa using hsymm

/-- **Butcher §342 (342b)**: `P_n^*(1) = 1` for every `n`.

Proof: unfold the definition, push the `Int.castRingHom ℝ` cast
through `.eval 1` via `eval_map` + `eval₂_at_one`, then use the helper
`shiftedLegendre_eval_one_int` to evaluate the integer polynomial at
`1` as `(-1)^n`. The outer `(-1)^n` from the Butcher sign convention
cancels the `(-1)^n` from Mathlib's evaluation. -/
theorem butcherShiftedLegendre_eval_one (n : ℕ) :
    (butcherShiftedLegendre n).eval 1 = 1 := by
  unfold butcherShiftedLegendre
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
      Polynomial.eval₂_at_one]
  -- Goal: (-1)^n * (Int.castRingHom ℝ) ((shiftedLegendre n).eval 1) = 1
  rw [shiftedLegendre_eval_one_int]
  -- Goal: (-1)^n * (Int.castRingHom ℝ) ((-1)^n) = 1
  simp only [map_pow, map_neg, map_one]
  -- Goal: (-1)^n * (-1)^n = 1
  rw [← mul_pow]
  norm_num

/-- **Butcher §342 (342c)**: `P_n^*(1 - x) = (-1)^n P_n^*(x)`.

Proof: Mathlib's `shiftedLegendre_eval_symm` instantiated at `R := ℝ`
gives `(shiftedLegendre n).map …`-evaluation at `1 - x` equals `(-1)^n`
times the evaluation at `x` (after rewriting `aeval` over the int-cast
substrate). Multiplying both sides by the Butcher sign factor `(-1)^n`
yields the claim. -/
theorem butcherShiftedLegendre_eval_one_sub (n : ℕ) (x : ℝ) :
    (butcherShiftedLegendre n).eval (1 - x) =
      (-1 : ℝ) ^ n * (butcherShiftedLegendre n).eval x := by
  -- Symmetry of the underlying Mathlib polynomial, lifted to ℝ.
  have hsymm :
      ((Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)).eval (1 - x)
        = (-1 : ℝ) ^ n *
          ((Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)).eval x := by
    -- Apply `shiftedLegendre_eval_symm` with `R := ℝ` at the point `1 - x`.
    have heq := Polynomial.shiftedLegendre_eval_symm n (R := ℝ) (1 - x)
    rw [show (1 : ℝ) - (1 - x) = x from by ring] at heq
    -- Reduce `aeval` over an `Int.castRingHom ℝ`-cast substrate to `eval`.
    have hcast : ∀ y : ℝ,
        (Polynomial.aeval y) (Polynomial.shiftedLegendre n)
          = ((Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)).eval y := by
      intro y
      rw [Polynomial.aeval_def, Polynomial.eval_map, algebraMap_int_eq]
    rw [hcast, hcast] at heq
    exact heq
  unfold butcherShiftedLegendre
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_C, hsymm]

/-! ### Non-vacuity witnesses (342b) -/

example : (butcherShiftedLegendre 0).eval 1 = 1 :=
  butcherShiftedLegendre_eval_one 0

example : (butcherShiftedLegendre 1).eval 1 = 1 :=
  butcherShiftedLegendre_eval_one 1

example : (butcherShiftedLegendre 2).eval 1 = 1 :=
  butcherShiftedLegendre_eval_one 2

/-! ### Non-vacuity witnesses (342c) -/

example (x : ℝ) :
    (butcherShiftedLegendre 1).eval (1 - x) =
      -(butcherShiftedLegendre 1).eval x := by
  have h := butcherShiftedLegendre_eval_one_sub 1 x
  simpa using h

example (x : ℝ) :
    (butcherShiftedLegendre 2).eval (1 - x) =
      (butcherShiftedLegendre 2).eval x := by
  have h := butcherShiftedLegendre_eval_one_sub 2 x
  simpa using h

end OpenMath.Chapter3.Section342
