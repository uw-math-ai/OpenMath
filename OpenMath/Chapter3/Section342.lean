import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
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

/-- **Butcher §342 (342e)** — Rodrigues' formula for the shifted Legendre
polynomials on `[0,1]`:
`n! · P_n^*(x) = (-1)^n (d/dx)^n (x^n (1-x)^n)`.

Equivalent to Butcher's stated `P_n^*(x) = (1/n!) (d/dx)^n ((x^2 - x)^n)`
via `(x^2 - x)^n = (-x)^n (1-x)^n = (-1)^n x^n (1-x)^n`. The form below
is the polynomial-ring identity over `ℝ[X]` and avoids dividing by `n!`.

Proof: lift Mathlib's `Polynomial.factorial_mul_shiftedLegendre_eq`
(stated over `ℤ[X]`) along `Int.castRingHom ℝ` and combine with the
Butcher sign convention factor `(-1)^n` from the definition of
`butcherShiftedLegendre`. -/
theorem butcherShiftedLegendre_rodrigues (n : ℕ) :
    Polynomial.C ((n.factorial : ℝ)) * butcherShiftedLegendre n
      = Polynomial.C ((-1 : ℝ) ^ n) *
        Polynomial.derivative^[n]
          ((Polynomial.X : Polynomial ℝ) ^ n *
            (1 - (Polynomial.X : Polynomial ℝ)) ^ n) := by
  -- Lift Mathlib's `factorial_mul_shiftedLegendre_eq` from `ℤ[X]` to `ℝ[X]`
  -- by applying `Polynomial.map (Int.castRingHom ℝ)` to both sides.
  have h := congrArg (Polynomial.map (Int.castRingHom ℝ))
    (Polynomial.factorial_mul_shiftedLegendre_eq n)
  rw [Polynomial.map_mul, Polynomial.map_natCast,
      ← Polynomial.iterate_derivative_map,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X] at h
  -- h : ((n.factorial : ℕ) : ℝ[X]) * (shiftedLegendre n).map ι
  --     = derivative^[n] (X^n * (1 - X)^n)   over ℝ[X]
  rw [← Polynomial.C_eq_natCast] at h
  -- h : C ((n.factorial : ℝ)) * (shiftedLegendre n).map ι
  --     = derivative^[n] (X^n * (1 - X)^n)
  -- Goal: C (n.factorial : ℝ) * (C ((-1)^n) * (shiftedLegendre n).map ι)
  --     = C ((-1)^n) * derivative^[n] (X^n * (1 - X)^n)
  unfold butcherShiftedLegendre
  rw [← mul_assoc,
      mul_comm (Polynomial.C ((n.factorial : ℝ))) (Polynomial.C ((-1 : ℝ) ^ n)),
      mul_assoc, h]

/-! ### Non-vacuity witnesses (342e)

These three witnesses confirm Butcher's small-`n` values match
`n! · P_n^*(x) = (-1)^n (d/dx)^n (x^n (1-x)^n)`. -/

-- `n = 0`: `0! · P_0^* = (-1)^0 · (X^0 · (1-X)^0) = 1`.
example :
    Polynomial.C ((Nat.factorial 0 : ℝ)) * butcherShiftedLegendre 0
      = Polynomial.C ((-1 : ℝ) ^ 0) *
        Polynomial.derivative^[0]
          ((Polynomial.X : Polynomial ℝ) ^ 0 *
            (1 - (Polynomial.X : Polynomial ℝ)) ^ 0) :=
  butcherShiftedLegendre_rodrigues 0

-- `n = 1`: `1! · P_1^* = -1 · derivative (X · (1-X)) = 2X - 1`.
example :
    Polynomial.C ((Nat.factorial 1 : ℝ)) * butcherShiftedLegendre 1
      = Polynomial.C ((-1 : ℝ) ^ 1) *
        Polynomial.derivative^[1]
          ((Polynomial.X : Polynomial ℝ) ^ 1 *
            (1 - (Polynomial.X : Polynomial ℝ)) ^ 1) :=
  butcherShiftedLegendre_rodrigues 1

-- `n = 2`: `2! · P_2^* = 1 · derivative^[2] (X^2 · (1-X)^2)`,
-- giving Butcher's `2 · P_2^*(x) = 12x^2 - 12x + 2`.
example :
    Polynomial.C ((Nat.factorial 2 : ℝ)) * butcherShiftedLegendre 2
      = Polynomial.C ((-1 : ℝ) ^ 2) *
        Polynomial.derivative^[2]
          ((Polynomial.X : Polynomial ℝ) ^ 2 *
            (1 - (Polynomial.X : Polynomial ℝ)) ^ 2) :=
  butcherShiftedLegendre_rodrigues 2

/-- **Butcher §342 (degree of `P_n^*`)**: Butcher's shifted Legendre
polynomial has `natDegree = n`. Follows directly from Mathlib's
`natDegree_shiftedLegendre` since multiplication by the nonzero
constant `C ((-1)^n)` and the injective coefficient cast
`Int.castRingHom ℝ` both preserve `natDegree`. -/
theorem butcherShiftedLegendre_natDegree (n : ℕ) :
    (butcherShiftedLegendre n).natDegree = n := by
  have h_unit : IsUnit ((-1 : ℝ) ^ n) :=
    isUnit_iff_ne_zero.mpr (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0))
  have h_inj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  unfold butcherShiftedLegendre
  rw [Polynomial.natDegree_C_mul_of_isUnit h_unit,
      Polynomial.natDegree_map_eq_of_injective h_inj,
      Polynomial.natDegree_shiftedLegendre]

/-- **Butcher §342 helper — `P_n^*(0) = (-1)^n`**: the value at the
left endpoint follows from (342c) parity applied at `x = 1` combined
with (342b) `P_n^*(1) = 1`. Useful as an input to the (342g)
distinct-roots argument and to a future (342f) recurrence check at
`x = 0`. -/
theorem butcherShiftedLegendre_eval_zero (n : ℕ) :
    (butcherShiftedLegendre n).eval 0 = (-1 : ℝ) ^ n := by
  have h := butcherShiftedLegendre_eval_one_sub n 1
  rw [show (1 - 1 : ℝ) = 0 from by ring, butcherShiftedLegendre_eval_one] at h
  simpa using h

/-- **Butcher §342 helper — `P_0^* = 1`**: the degree-`0` shifted
Legendre polynomial is the constant `1`. Follows by `Polynomial.ext`
+ `coeff_shiftedLegendre` over the unique coefficient slot `k = 0`. -/
theorem butcherShiftedLegendre_zero :
    butcherShiftedLegendre 0 = Polynomial.C 1 := by
  unfold butcherShiftedLegendre
  ext k
  rcases k with _ | k
  · simp [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre,
          Polynomial.coeff_one]
  · simp [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre,
          Polynomial.coeff_one]

/-- **Butcher §342 helper — `P_1^* = 2X - 1`**: the degree-`1` shifted
Legendre polynomial expands explicitly. Computed via `Polynomial.ext`
+ `coeff_shiftedLegendre` over slots `k ∈ {0, 1}` (higher slots vanish
by `natDegree`). -/
theorem butcherShiftedLegendre_one :
    butcherShiftedLegendre 1 =
      Polynomial.C 2 * Polynomial.X - Polynomial.C 1 := by
  unfold butcherShiftedLegendre
  ext k
  match k with
  | 0 =>
      simp [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre,
            Polynomial.coeff_sub, Polynomial.coeff_C]
  | 1 =>
      simp [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre,
            Polynomial.coeff_sub, Polynomial.coeff_one]
  | (k+2) =>
      have hk : (1 : ℕ).choose (k + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre,
            Polynomial.coeff_sub, Polynomial.coeff_one, hk]

/-- **Butcher §342 helper — `P_2^* = 6X² - 6X + 1`**: the degree-`2`
shifted Legendre polynomial expands explicitly via the coefficient
formula `(shiftedLegendre 2).coeff k = (-1)^k · C(2,k) · C(2+k, 2)`.
The relevant values are `(1, -6, 6)` at `k = 0, 1, 2`; higher slots
vanish since `2.choose k = 0` for `k ≥ 3`. The outer `(-1)^2 = 1`
sign factor from `butcherShiftedLegendre` is trivial. -/
theorem butcherShiftedLegendre_two :
    butcherShiftedLegendre 2 =
      Polynomial.C 6 * Polynomial.X ^ 2 - Polynomial.C 6 * Polynomial.X
        + Polynomial.C 1 := by
  unfold butcherShiftedLegendre
  ext k
  match k with
  | 0 =>
      simp [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre,
            Polynomial.coeff_add, Polynomial.coeff_sub,
            Polynomial.coeff_X_pow, Polynomial.coeff_X,
            Polynomial.coeff_C, Polynomial.coeff_one]
  | 1 =>
      simp [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre,
            Polynomial.coeff_add, Polynomial.coeff_sub,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_C, Polynomial.coeff_one]
  | 2 =>
      have hch : Nat.choose 4 2 = 6 := by decide
      simp [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre,
            Polynomial.coeff_add, Polynomial.coeff_sub,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch]
  | (k+3) =>
      have hk : (2 : ℕ).choose (k + 3) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre,
            Polynomial.coeff_add, Polynomial.coeff_sub,
            Polynomial.coeff_one, hk]

/-! ### Non-vacuity witnesses for §342 helpers

These confirm the helper lemmas evaluate correctly on small inputs. -/

example : (butcherShiftedLegendre 0).eval 0 = 1 := by
  rw [butcherShiftedLegendre_eval_zero 0]; norm_num

example : (butcherShiftedLegendre 1).eval 0 = -1 := by
  rw [butcherShiftedLegendre_eval_zero 1]; norm_num

example : (butcherShiftedLegendre 2).eval 0 = 1 := by
  rw [butcherShiftedLegendre_eval_zero 2]; norm_num

example : butcherShiftedLegendre 0 = Polynomial.C 1 :=
  butcherShiftedLegendre_zero

example : (butcherShiftedLegendre 1).eval 0 = -1 := by
  rw [butcherShiftedLegendre_one]
  simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]

example : (butcherShiftedLegendre 1).eval 1 = 1 := by
  rw [butcherShiftedLegendre_one]
  simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
  norm_num

/-! ### (342d) — concrete cases at `n = 0` and `n = 1`

Butcher §342 (342d) asserts the norm-square identity
`∫₀¹ (P_n^*(x))^2 dx = 1 / (2n + 1)`. The general statement requires
iterated integration by parts × `n` against the Rodrigues representation
and the Beta-function identity `∫₀¹ x^n (1 - x)^n dx = (n!)^2 / (2n+1)!`
— substantial machinery that is deferred (general case submitted to
Aristotle, cycle 274). The two concrete instances below verify the
formula at the smallest cases `n = 0` and `n = 1` via direct polynomial
evaluation, providing concrete witnesses that (342d)'s right-hand side
`1 / (2n + 1)` is the correct closed form for the small-degree shifted
Legendre polynomials. -/

/-- **Butcher §342 (342d) at `n = 0`**: `∫₀¹ (P_0^*(x))^2 dx = 1`.

The `n = 0` instance of (342d). Direct computation using
`butcherShiftedLegendre_zero` (`P_0^* = C 1`, so the integrand is `1`)
and `intervalIntegral.integral_one`. -/
theorem butcherShiftedLegendre_norm_sq_zero :
    ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 0).eval x ^ 2 = 1 := by
  have hP : ∀ x : ℝ, (butcherShiftedLegendre 0).eval x ^ 2 = 1 := by
    intro x
    rw [butcherShiftedLegendre_zero]
    simp
  simp_rw [hP]
  simp [intervalIntegral.integral_const]

/-- **Butcher §342 (342d) at `n = 1`**: `∫₀¹ (P_1^*(x))^2 dx = 1/3`.

The `n = 1` instance of (342d). Direct computation:
`P_1^*(x) = 2x - 1` (cycle 273's `butcherShiftedLegendre_one`), so
`(P_1^*(x))^2 = 4x^2 - 4x + 1`. Then
`∫₀¹ (4x^2 - 4x + 1) dx = 4/3 - 2 + 1 = 1/3`. -/
theorem butcherShiftedLegendre_norm_sq_one :
    ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 1).eval x ^ 2 = 1 / 3 := by
  have hP : ∀ x : ℝ, (butcherShiftedLegendre 1).eval x ^ 2
      = 4 * x ^ 2 - 4 * x + 1 := by
    intro x
    rw [butcherShiftedLegendre_one]
    simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X]
    ring
  simp_rw [hP]
  have hint_x2 : IntervalIntegrable (fun x : ℝ => x ^ 2) MeasureTheory.volume 0 1 :=
    (continuous_pow 2).intervalIntegrable 0 1
  have hint_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have h1 : ∫ x in (0 : ℝ)..1, x ^ 2 = 1 / 3 := by
    rw [integral_pow]; norm_num
  have h2 : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
    have hp1 := integral_pow (a := (0 : ℝ)) (b := 1) 1
    simp only [pow_one, Nat.cast_one] at hp1
    rw [hp1]; norm_num
  rw [intervalIntegral.integral_add
        ((hint_x2.const_mul 4).sub (hint_x.const_mul 4))
        intervalIntegrable_const,
      intervalIntegral.integral_sub
        (hint_x2.const_mul 4)
        (hint_x.const_mul 4),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      h1, h2, integral_one]
  ring

/-- **Butcher §342 (342d) at `n = 2`**: `∫₀¹ (P_2^*(x))^2 dx = 1/5`.

The `n = 2` instance of (342d). Direct computation:
`P_2^*(x) = 6x² - 6x + 1` (`butcherShiftedLegendre_two`), so
`(P_2^*(x))^2 = 36x⁴ - 72x³ + 48x² - 12x + 1`. Then
`∫₀¹ (36x⁴ - 72x³ + 48x² - 12x + 1) dx = 36/5 - 18 + 16 - 6 + 1 = 1/5`. -/
theorem butcherShiftedLegendre_norm_sq_two :
    ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 2).eval x ^ 2 = 1 / 5 := by
  have hP : ∀ x : ℝ, (butcherShiftedLegendre 2).eval x ^ 2
      = 36 * x ^ 4 - 72 * x ^ 3 + 48 * x ^ 2 - 12 * x + 1 := by
    intro x
    rw [butcherShiftedLegendre_two]
    simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    ring
  simp_rw [hP]
  have hi_x4 : IntervalIntegrable (fun x : ℝ => x ^ 4) MeasureTheory.volume 0 1 :=
    (continuous_pow 4).intervalIntegrable 0 1
  have hi_x3 : IntervalIntegrable (fun x : ℝ => x ^ 3) MeasureTheory.volume 0 1 :=
    (continuous_pow 3).intervalIntegrable 0 1
  have hi_x2 : IntervalIntegrable (fun x : ℝ => x ^ 2) MeasureTheory.volume 0 1 :=
    (continuous_pow 2).intervalIntegrable 0 1
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have h4 : ∫ x in (0 : ℝ)..1, x ^ 4 = 1 / 5 := by
    rw [integral_pow]; norm_num
  have h3 : ∫ x in (0 : ℝ)..1, x ^ 3 = 1 / 4 := by
    rw [integral_pow]; norm_num
  have h2 : ∫ x in (0 : ℝ)..1, x ^ 2 = 1 / 3 := by
    rw [integral_pow]; norm_num
  have h1 : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
    have hp1 := integral_pow (a := (0 : ℝ)) (b := 1) 1
    simp only [pow_one, Nat.cast_one] at hp1
    rw [hp1]; norm_num
  -- The integrand is `((((36·x⁴ − 72·x³) + 48·x²) − 12·x) + 1)` (left-associative).
  rw [intervalIntegral.integral_add
        ((((hi_x4.const_mul 36).sub (hi_x3.const_mul 72)).add
            (hi_x2.const_mul 48)).sub (hi_x.const_mul 12))
        intervalIntegrable_const,
      intervalIntegral.integral_sub
        (((hi_x4.const_mul 36).sub (hi_x3.const_mul 72)).add
            (hi_x2.const_mul 48))
        (hi_x.const_mul 12),
      intervalIntegral.integral_add
        ((hi_x4.const_mul 36).sub (hi_x3.const_mul 72))
        (hi_x2.const_mul 48),
      intervalIntegral.integral_sub
        (hi_x4.const_mul 36)
        (hi_x3.const_mul 72),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      h4, h3, h2, h1, integral_one]
  ring

/-! ### Non-vacuity witnesses for (342d) cases -/

-- (342d) at `n = 0`: matches the closed form `1 / (2 * 0 + 1) = 1`.
example : ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 0).eval x ^ 2
    = 1 / (2 * (0 : ℕ) + 1) := by
  rw [butcherShiftedLegendre_norm_sq_zero]; norm_num

-- (342d) at `n = 1`: matches the closed form `1 / (2 * 1 + 1) = 1/3`.
example : ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 1).eval x ^ 2
    = 1 / (2 * (1 : ℕ) + 1) := by
  rw [butcherShiftedLegendre_norm_sq_one]; norm_num

-- (342d) at `n = 2`: matches the closed form `1 / (2 * 2 + 1) = 1/5`.
example : ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 2).eval x ^ 2
    = 1 / (2 * (2 : ℕ) + 1) := by
  rw [butcherShiftedLegendre_norm_sq_two]; norm_num

end OpenMath.Chapter3.Section342
