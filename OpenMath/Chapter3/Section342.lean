import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Cases
import Mathlib.Data.Real.Basic
import OpenMath.Chapter3.Section342NormSqHelpers
import OpenMath.Chapter3.Section342DistinctRootsHelpers

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

/-- **Butcher §342 helper — `P_3^* = 20X³ - 30X² + 12X - 1`**: the
degree-`3` shifted Legendre polynomial expands explicitly via the
coefficient formula `(shiftedLegendre 3).coeff k = (-1)^k · C(3,k) · C(3+k, 3)`.
The relevant values are `(1, -12, 30, -20)` at `k = 0, 1, 2, 3`; higher
slots vanish since `3.choose k = 0` for `k ≥ 4`. The outer Butcher
sign factor `(-1)^3 = -1` flips every sign, yielding the closed form
`20X³ - 30X² + 12X - 1`. Sanity: evaluating at `x = 0` gives `-1`
(matches `P_3^*(0) = (-1)^3 = -1`); evaluating at `x = 1` gives
`20 - 30 + 12 - 1 = 1` (matches `P_n^*(1) = 1` from (342b)). -/
theorem butcherShiftedLegendre_three :
    butcherShiftedLegendre 3 =
      Polynomial.C 20 * Polynomial.X ^ 3 - Polynomial.C 30 * Polynomial.X ^ 2
        + Polynomial.C 12 * Polynomial.X - Polynomial.C 1 := by
  unfold butcherShiftedLegendre
  ext k
  -- Peel off the `C ((-1)^3) * ·` factor BEFORE simp can collapse
  -- `C ((-1)^3)` to the polynomial `-1` (which would block `coeff_C_mul`).
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
             Polynomial.coeff_shiftedLegendre]
  match k with
  | 0 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_X_pow, Polynomial.coeff_X,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 1 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 2 =>
      have hch : Nat.choose 5 3 = 10 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch]
      norm_num
  | 3 =>
      have hch : Nat.choose 6 3 = 20 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch]
      norm_num
  | (k+4) =>
      have hk : (3 : ℕ).choose (k + 4) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_one, hk]

/-- **Butcher §342 helper — `P_4^* = 70X^4 - 140X^3 + 90X^2 - 20X + 1`**:
the degree-`4` shifted Legendre polynomial expands explicitly via the
coefficient formula `(shiftedLegendre 4).coeff k = (-1)^k · C(4,k) · C(4+k, 4)`.
The relevant values are `(1, -20, 90, -140, 70)` at `k = 0, 1, 2, 3, 4`;
higher slots vanish since `4.choose k = 0` for `k ≥ 5`. The outer Butcher
sign factor `(-1)^4 = 1` is trivial — the even-`n` case mirrors cycle 275's
`butcherShiftedLegendre_two` recipe (no peel-off needed). Sanity:
`70 - 140 + 90 - 20 + 1 = 1` at `x = 1` (matches (342b)). -/
theorem butcherShiftedLegendre_four :
    butcherShiftedLegendre 4 =
      Polynomial.C 70 * Polynomial.X ^ 4
        - Polynomial.C 140 * Polynomial.X ^ 3
        + Polynomial.C 90 * Polynomial.X ^ 2
        - Polynomial.C 20 * Polynomial.X
        + Polynomial.C 1 := by
  unfold butcherShiftedLegendre
  ext k
  -- Peel off the `C ((-1)^4) * ·` factor BEFORE simp can collapse it
  -- to the polynomial `1` (which blocks `coeff_C_mul`).
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
             Polynomial.coeff_shiftedLegendre]
  match k with
  | 0 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_X_pow, Polynomial.coeff_X,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 1 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 2 =>
      have hch1 : Nat.choose 6 4 = 15 := by decide
      have hch2 : Nat.choose 4 2 = 6 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 3 =>
      have hch : Nat.choose 7 4 = 35 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch]
      norm_num
  | 4 =>
      have hch : Nat.choose 8 4 = 70 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch]
      norm_num
  | (k+5) =>
      have hk : (4 : ℕ).choose (k + 5) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_one, hk]

/-- **Butcher §342 helper — `P_5^* = 252X^5 - 630X^4 + 560X^3 - 210X^2 + 30X - 1`**:
the degree-`5` shifted Legendre polynomial expands explicitly via the
coefficient formula `(shiftedLegendre 5).coeff k = (-1)^k · C(5,k) · C(5+k, 5)`.
The relevant values at `k = 0,…,5` are `(1, -30, 210, -560, 630, -252)`;
higher slots vanish since `5.choose k = 0` for `k ≥ 6`. The outer Butcher
sign factor `(-1)^5 = -1` flips every sign, yielding the closed form
`252X^5 - 630X^4 + 560X^3 - 210X^2 + 30X - 1`. Sanity: evaluating at
`x = 0` gives `-1` (matches `P_5^*(0) = (-1)^5 = -1`); evaluating at
`x = 1` gives `252 - 630 + 560 - 210 + 30 - 1 = 1` (matches (342b)). -/
theorem butcherShiftedLegendre_five :
    butcherShiftedLegendre 5 =
      Polynomial.C 252 * Polynomial.X ^ 5
        - Polynomial.C 630 * Polynomial.X ^ 4
        + Polynomial.C 560 * Polynomial.X ^ 3
        - Polynomial.C 210 * Polynomial.X ^ 2
        + Polynomial.C 30 * Polynomial.X
        - Polynomial.C 1 := by
  unfold butcherShiftedLegendre
  ext k
  -- Peel off the `C ((-1)^5) * ·` factor BEFORE simp can collapse
  -- `C ((-1)^5)` to the polynomial `-1` (which would block `coeff_C_mul`).
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
             Polynomial.coeff_shiftedLegendre]
  match k with
  | 0 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_X_pow, Polynomial.coeff_X,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 1 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 2 =>
      have hch1 : Nat.choose 7 5 = 21 := by decide
      have hch2 : Nat.choose 5 2 = 10 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 3 =>
      have hch1 : Nat.choose 8 5 = 56 := by decide
      have hch2 : Nat.choose 5 3 = 10 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 4 =>
      have hch : Nat.choose 9 5 = 126 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch]
      norm_num
  | 5 =>
      have hch : Nat.choose 10 5 = 252 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch]
      norm_num
  | (k+6) =>
      have hk : (5 : ℕ).choose (k + 6) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_one, hk]

/-- **Butcher §342 helper — `P_6^* = 924X^6 - 2772X^5 + 3150X^4 - 1680X^3 + 420X^2 - 42X + 1`**:
the degree-`6` shifted Legendre polynomial expands explicitly via the
coefficient formula `(shiftedLegendre 6).coeff k = (-1)^k · C(6,k) · C(6+k, 6)`.
The relevant values at `k = 0,…,6` are `(1, -42, 420, -1680, 3150, -2772, 924)`;
higher slots vanish since `6.choose k = 0` for `k ≥ 7`. The outer Butcher
sign factor `(-1)^6 = 1` is trivial — the even-`n` case mirrors cycle 277's
`butcherShiftedLegendre_four` recipe. Sanity: `924 - 2772 + 3150 - 1680
+ 420 - 42 + 1 = 1` at `x = 1` (matches (342b)); constant term `1` matches
`P_6^*(0) = (-1)^6 = 1`. -/
theorem butcherShiftedLegendre_six :
    butcherShiftedLegendre 6 =
      Polynomial.C 924 * Polynomial.X ^ 6
        - Polynomial.C 2772 * Polynomial.X ^ 5
        + Polynomial.C 3150 * Polynomial.X ^ 4
        - Polynomial.C 1680 * Polynomial.X ^ 3
        + Polynomial.C 420 * Polynomial.X ^ 2
        - Polynomial.C 42 * Polynomial.X
        + Polynomial.C 1 := by
  unfold butcherShiftedLegendre
  ext k
  -- Peel off the `C ((-1)^6) * ·` factor BEFORE simp can collapse it
  -- to the polynomial `1` (which would block `coeff_C_mul`).
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
             Polynomial.coeff_shiftedLegendre]
  match k with
  | 0 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_X_pow, Polynomial.coeff_X,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 1 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 2 =>
      have hch1 : Nat.choose 8 6 = 28 := by decide
      have hch2 : Nat.choose 6 2 = 15 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 3 =>
      have hch1 : Nat.choose 9 6 = 84 := by decide
      have hch2 : Nat.choose 6 3 = 20 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 4 =>
      have hch1 : Nat.choose 10 6 = 210 := by decide
      have hch2 : Nat.choose 6 4 = 15 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 5 =>
      have hch1 : Nat.choose 11 6 = 462 := by decide
      have hch2 : Nat.choose 6 5 = 6 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 6 =>
      have hch : Nat.choose 12 6 = 924 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch]
      norm_num
  | (k+7) =>
      have hk : (6 : ℕ).choose (k + 7) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_one, hk]

/-- **Butcher §342 helper — `P_7^* = 3432X^7 - 12012X^6 + 16632X^5 - 11550X^4
+ 4200X^3 - 756X^2 + 56X - 1`**:
the degree-`7` shifted Legendre polynomial expands explicitly via the
coefficient formula `(shiftedLegendre 7).coeff k = (-1)^k · C(7,k) · C(7+k, 7)`.
The relevant values at `k = 0,…,7` are `(1, -56, 756, -4200, 11550, -16632,
12012, -3432)`; higher slots vanish since `7.choose k = 0` for `k ≥ 8`. The
outer Butcher sign factor `(-1)^7 = -1` flips every sign, yielding the closed
form above. Sanity: evaluating at `x = 0` gives `-1` (matches
`P_7^*(0) = (-1)^7 = -1`); evaluating at `x = 1` gives
`3432 - 12012 + 16632 - 11550 + 4200 - 756 + 56 - 1 = 1` (matches (342b)). -/
theorem butcherShiftedLegendre_seven :
    butcherShiftedLegendre 7 =
      Polynomial.C 3432 * Polynomial.X ^ 7
        - Polynomial.C 12012 * Polynomial.X ^ 6
        + Polynomial.C 16632 * Polynomial.X ^ 5
        - Polynomial.C 11550 * Polynomial.X ^ 4
        + Polynomial.C 4200 * Polynomial.X ^ 3
        - Polynomial.C 756 * Polynomial.X ^ 2
        + Polynomial.C 56 * Polynomial.X
        - Polynomial.C 1 := by
  unfold butcherShiftedLegendre
  ext k
  -- Peel off the `C ((-1)^7) * ·` factor BEFORE simp can collapse
  -- `C ((-1)^7)` to the polynomial `-1` (which would block `coeff_C_mul`).
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
             Polynomial.coeff_shiftedLegendre]
  match k with
  | 0 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_X_pow, Polynomial.coeff_X,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 1 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 2 =>
      have hch1 : Nat.choose 9 7 = 36 := by decide
      have hch2 : Nat.choose 7 2 = 21 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 3 =>
      have hch1 : Nat.choose 10 7 = 120 := by decide
      have hch2 : Nat.choose 7 3 = 35 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 4 =>
      have hch1 : Nat.choose 11 7 = 330 := by decide
      have hch2 : Nat.choose 7 4 = 35 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 5 =>
      have hch1 : Nat.choose 12 7 = 792 := by decide
      have hch2 : Nat.choose 7 5 = 21 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 6 =>
      have hch1 : Nat.choose 13 7 = 1716 := by decide
      have hch2 : Nat.choose 7 6 = 7 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 7 =>
      have hch : Nat.choose 14 7 = 3432 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch]
      norm_num
  | (k+8) =>
      have hk : (7 : ℕ).choose (k + 8) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_one, hk]

/-- **Butcher §342 helper — `P_8^* = 12870X^8 - 51480X^7 + 84084X^6 - 72072X^5
+ 34650X^4 - 9240X^3 + 1260X^2 - 72X + 1`**:
the degree-`8` shifted Legendre polynomial expands explicitly via the
coefficient formula `(shiftedLegendre 8).coeff k = (-1)^k · C(8,k) · C(8+k, 8)`.
The relevant values at `k = 0,…,8` are `(1, -72, 1260, -9240, 34650, -72072,
84084, -51480, 12870)`; higher slots vanish since `8.choose k = 0` for `k ≥ 9`.
The outer Butcher sign factor `(-1)^8 = 1` is trivial, so the closed form
matches the unsigned coefficients above. Sanity: evaluating at `x = 0` gives
`1` (matches `P_8^*(0) = (-1)^8 = 1`); evaluating at `x = 1` gives
`12870 - 51480 + 84084 - 72072 + 34650 - 9240 + 1260 - 72 + 1 = 1` (matches
(342b)). -/
theorem butcherShiftedLegendre_eight :
    butcherShiftedLegendre 8 =
      Polynomial.C 12870 * Polynomial.X ^ 8
        - Polynomial.C 51480 * Polynomial.X ^ 7
        + Polynomial.C 84084 * Polynomial.X ^ 6
        - Polynomial.C 72072 * Polynomial.X ^ 5
        + Polynomial.C 34650 * Polynomial.X ^ 4
        - Polynomial.C 9240 * Polynomial.X ^ 3
        + Polynomial.C 1260 * Polynomial.X ^ 2
        - Polynomial.C 72 * Polynomial.X
        + Polynomial.C 1 := by
  unfold butcherShiftedLegendre
  ext k
  -- Peel off the `C ((-1)^8) * ·` factor BEFORE simp can collapse it
  -- to the polynomial `1` (which would block `coeff_C_mul`).
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
             Polynomial.coeff_shiftedLegendre]
  match k with
  | 0 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_X_pow, Polynomial.coeff_X,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 1 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 2 =>
      have hch1 : Nat.choose 10 8 = 45 := by decide
      have hch2 : Nat.choose 8 2 = 28 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 3 =>
      have hch1 : Nat.choose 11 8 = 165 := by decide
      have hch2 : Nat.choose 8 3 = 56 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 4 =>
      have hch1 : Nat.choose 12 8 = 495 := by decide
      have hch2 : Nat.choose 8 4 = 70 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 5 =>
      have hch1 : Nat.choose 13 8 = 1287 := by decide
      have hch2 : Nat.choose 8 5 = 56 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 6 =>
      have hch1 : Nat.choose 14 8 = 3003 := by decide
      have hch2 : Nat.choose 8 6 = 28 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 7 =>
      have hch1 : Nat.choose 15 8 = 6435 := by decide
      have hch2 : Nat.choose 8 7 = 8 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 8 =>
      have hch : Nat.choose 16 8 = 12870 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch]
      norm_num
  | (k+9) =>
      have hk : (8 : ℕ).choose (k + 9) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_one, hk]

/-- **Butcher §342 helper — `P_9^* = 48620X^9 − 218790X^8 + 411840X^7 − 420420X^6
+ 252252X^5 − 90090X^4 + 18480X^3 − 1980X^2 + 90X − 1`**:
the degree-`9` shifted Legendre polynomial expands explicitly via the
coefficient formula `(shiftedLegendre 9).coeff k = (-1)^k · C(9,k) · C(9+k, 9)`.
The relevant values at `k = 0,…,9` are
`(1, −9, 36, −84, 126, −126, 84, −36, 9, −1)` for `C(9,k)` (signed by `(-1)^k`)
and `(1, 10, 55, 220, 715, 2002, 5005, 11440, 24310, 48620)` for `C(9+k, 9)`.
The outer Butcher sign factor `(-1)^9 = -1` flips every coefficient, giving the
explicit form above. Sanity: evaluating at `x = 0` gives `-1` (matches
`P_9^*(0) = (-1)^9 = -1`); evaluating at `x = 1` gives
`48620 − 218790 + 411840 − 420420 + 252252 − 90090 + 18480 − 1980 + 90 − 1 = 1`
(matches (342b), verified via Python integer arithmetic). -/
theorem butcherShiftedLegendre_nine :
    butcherShiftedLegendre 9 =
      Polynomial.C 48620 * Polynomial.X ^ 9
        - Polynomial.C 218790 * Polynomial.X ^ 8
        + Polynomial.C 411840 * Polynomial.X ^ 7
        - Polynomial.C 420420 * Polynomial.X ^ 6
        + Polynomial.C 252252 * Polynomial.X ^ 5
        - Polynomial.C 90090 * Polynomial.X ^ 4
        + Polynomial.C 18480 * Polynomial.X ^ 3
        - Polynomial.C 1980 * Polynomial.X ^ 2
        + Polynomial.C 90 * Polynomial.X
        - Polynomial.C 1 := by
  unfold butcherShiftedLegendre
  ext k
  -- Peel off the `C ((-1)^9) * ·` factor BEFORE simp can collapse
  -- `C ((-1)^9)` to the polynomial `-1` (which would block `coeff_C_mul`).
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
             Polynomial.coeff_shiftedLegendre]
  match k with
  | 0 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_X_pow, Polynomial.coeff_X,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 1 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 2 =>
      have hch1 : Nat.choose 11 9 = 55 := by decide
      have hch2 : Nat.choose 9 2 = 36 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 3 =>
      have hch1 : Nat.choose 12 9 = 220 := by decide
      have hch2 : Nat.choose 9 3 = 84 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 4 =>
      have hch1 : Nat.choose 13 9 = 715 := by decide
      have hch2 : Nat.choose 9 4 = 126 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 5 =>
      have hch1 : Nat.choose 14 9 = 2002 := by decide
      have hch2 : Nat.choose 9 5 = 126 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 6 =>
      have hch1 : Nat.choose 15 9 = 5005 := by decide
      have hch2 : Nat.choose 9 6 = 84 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 7 =>
      have hch1 : Nat.choose 16 9 = 11440 := by decide
      have hch2 : Nat.choose 9 7 = 36 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 8 =>
      have hch1 : Nat.choose 17 9 = 24310 := by decide
      have hch2 : Nat.choose 9 8 = 9 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 9 =>
      have hch : Nat.choose 18 9 = 48620 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch]
      norm_num
  | (k+10) =>
      have hk : (9 : ℕ).choose (k + 10) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_one, hk]

/-- **Butcher §342 helper — `P_10^* = 184756X^10 − 923780X^9 + 1969110X^8
− 2333760X^7 + 1681680X^6 − 756756X^5 + 210210X^4 − 34320X^3 + 2970X^2
− 110X + 1`**:
the degree-`10` shifted Legendre polynomial expands explicitly via the
coefficient formula `(shiftedLegendre 10).coeff k = (-1)^k · C(10,k) · C(10+k, 10)`.
The relevant values at `k = 0,…,10` are
`(1, −110, 2970, −34320, 210210, −756756, 1681680, −2333760, 1969110,
−923780, 184756)`; higher slots vanish since `10.choose k = 0` for
`k ≥ 11`. The outer Butcher sign factor `(-1)^10 = +1` is trivial, so the
closed form matches the unsigned coefficients above. Sanity: evaluating
at `x = 0` gives `1` (matches `P_10^*(0) = (-1)^10 = 1`); evaluating at
`x = 1` sums to `1` (matches (342b), verified via Python integer
arithmetic in cycle 286). -/
theorem butcherShiftedLegendre_ten :
    butcherShiftedLegendre 10 =
      Polynomial.C 184756 * Polynomial.X ^ 10
        - Polynomial.C 923780 * Polynomial.X ^ 9
        + Polynomial.C 1969110 * Polynomial.X ^ 8
        - Polynomial.C 2333760 * Polynomial.X ^ 7
        + Polynomial.C 1681680 * Polynomial.X ^ 6
        - Polynomial.C 756756 * Polynomial.X ^ 5
        + Polynomial.C 210210 * Polynomial.X ^ 4
        - Polynomial.C 34320 * Polynomial.X ^ 3
        + Polynomial.C 2970 * Polynomial.X ^ 2
        - Polynomial.C 110 * Polynomial.X
        + Polynomial.C 1 := by
  unfold butcherShiftedLegendre
  ext k
  -- Peel off the `C ((-1)^10) * ·` factor BEFORE simp can collapse it
  -- to the polynomial `1` (which would block `coeff_C_mul`).
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
             Polynomial.coeff_shiftedLegendre]
  match k with
  | 0 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_X_pow, Polynomial.coeff_X,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 1 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 2 =>
      have hch1 : Nat.choose 12 10 = 66 := by decide
      have hch2 : Nat.choose 10 2 = 45 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 3 =>
      have hch1 : Nat.choose 13 10 = 286 := by decide
      have hch2 : Nat.choose 10 3 = 120 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 4 =>
      have hch1 : Nat.choose 14 10 = 1001 := by decide
      have hch2 : Nat.choose 10 4 = 210 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 5 =>
      have hch1 : Nat.choose 15 10 = 3003 := by decide
      have hch2 : Nat.choose 10 5 = 252 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 6 =>
      have hch1 : Nat.choose 16 10 = 8008 := by decide
      have hch2 : Nat.choose 10 6 = 210 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 7 =>
      have hch1 : Nat.choose 17 10 = 19448 := by decide
      have hch2 : Nat.choose 10 7 = 120 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 8 =>
      have hch1 : Nat.choose 18 10 = 43758 := by decide
      have hch2 : Nat.choose 10 8 = 45 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 9 =>
      have hch1 : Nat.choose 19 10 = 92378 := by decide
      have hch2 : Nat.choose 10 9 = 10 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 10 =>
      have hch : Nat.choose 20 10 = 184756 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch]
      norm_num
  | (k+11) =>
      have hk : (10 : ℕ).choose (k + 11) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_one, hk]

/-- **Non-vacuity cross-check** for cycle 286's `butcherShiftedLegendre_ten`:
the explicit polynomial expansion evaluates to `1` at `x = 1`, matching
Butcher's (342b) `P_n^*(1) = 1` at `n = 10`. Cross-validates the explicit
coefficient table (cycle 286) against the abstract characterization
`butcherShiftedLegendre_eval_one`; if the explicit coefficients had a
sign or magnitude error the `norm_num` call would fail. -/
theorem butcherShiftedLegendre_ten_explicit_eval_one :
    (butcherShiftedLegendre 10).eval 1 = 1 := by
  rw [butcherShiftedLegendre_ten]
  simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_one]
  norm_num

/-- **Non-vacuity cross-check** for cycle 286's `butcherShiftedLegendre_ten`:
the explicit polynomial expansion evaluates to `1` at `x = 0`, matching
Butcher's (342c) parity `P_n^*(0) = (-1)^n` at `n = 10`. Cross-validates the
explicit coefficient table (cycle 286) against the abstract characterization
`butcherShiftedLegendre_eval_zero`. -/
theorem butcherShiftedLegendre_ten_explicit_eval_zero :
    (butcherShiftedLegendre 10).eval 0 = 1 := by
  rw [butcherShiftedLegendre_ten]
  simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_one]

/-- **Butcher §342 helper — `P_11^* = 705432X^11 − 3879876X^10 + 9237800X^9
− 12471030X^8 + 10501920X^7 − 5717712X^6 + 2018016X^5 − 450450X^4
+ 60060X^3 − 4290X^2 + 132X − 1`**:
the degree-`11` shifted Legendre polynomial expands explicitly via the
coefficient formula `(shiftedLegendre 11).coeff k = (-1)^k · C(11,k) · C(11+k, 11)`.
The relevant unsigned coefficients at `k = 0,…,11` are
`(1, −132, 4290, −60060, 450450, −2018016, 5717712, −10501920, 12471030,
−9237800, 3879876, −705432)`; higher slots vanish since `11.choose k = 0`
for `k ≥ 12`. The outer Butcher sign factor `(-1)^11 = −1` flips every
sign, producing the closed form above. Sanity: evaluating at `x = 0`
gives `−1` (matches `P_11^*(0) = (-1)^11 = −1`); evaluating at `x = 1`
sums to `1` (matches (342b), verified via Python integer arithmetic in
cycle 288). Eleventh rung of the empirical ladder — cycles 282–287
established `n = 2,…,10`. -/
theorem butcherShiftedLegendre_eleven :
    butcherShiftedLegendre 11 =
      Polynomial.C 705432 * Polynomial.X ^ 11
        - Polynomial.C 3879876 * Polynomial.X ^ 10
        + Polynomial.C 9237800 * Polynomial.X ^ 9
        - Polynomial.C 12471030 * Polynomial.X ^ 8
        + Polynomial.C 10501920 * Polynomial.X ^ 7
        - Polynomial.C 5717712 * Polynomial.X ^ 6
        + Polynomial.C 2018016 * Polynomial.X ^ 5
        - Polynomial.C 450450 * Polynomial.X ^ 4
        + Polynomial.C 60060 * Polynomial.X ^ 3
        - Polynomial.C 4290 * Polynomial.X ^ 2
        + Polynomial.C 132 * Polynomial.X
        - Polynomial.C 1 := by
  unfold butcherShiftedLegendre
  ext k
  -- Peel off the `C ((-1)^11) * ·` factor BEFORE simp can collapse
  -- `C ((-1)^11)` to the polynomial `-1` (which would block `coeff_C_mul`).
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
             Polynomial.coeff_shiftedLegendre]
  match k with
  | 0 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_X_pow, Polynomial.coeff_X,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 1 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 2 =>
      have hch1 : Nat.choose 13 11 = 78 := by decide
      have hch2 : Nat.choose 11 2 = 55 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 3 =>
      have hch1 : Nat.choose 14 11 = 364 := by decide
      have hch2 : Nat.choose 11 3 = 165 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 4 =>
      have hch1 : Nat.choose 15 11 = 1365 := by decide
      have hch2 : Nat.choose 11 4 = 330 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 5 =>
      have hch1 : Nat.choose 16 11 = 4368 := by decide
      have hch2 : Nat.choose 11 5 = 462 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 6 =>
      have hch1 : Nat.choose 17 11 = 12376 := by decide
      have hch2 : Nat.choose 11 6 = 462 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 7 =>
      have hch1 : Nat.choose 18 11 = 31824 := by decide
      have hch2 : Nat.choose 11 7 = 330 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 8 =>
      have hch1 : Nat.choose 19 11 = 75582 := by decide
      have hch2 : Nat.choose 11 8 = 165 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 9 =>
      have hch1 : Nat.choose 20 11 = 167960 := by decide
      have hch2 : Nat.choose 11 9 = 55 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 10 =>
      have hch1 : Nat.choose 21 11 = 352716 := by decide
      have hch2 : Nat.choose 11 10 = 11 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 11 =>
      have hch : Nat.choose 22 11 = 705432 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch]
      norm_num
  | (k+12) =>
      have hk : (11 : ℕ).choose (k + 12) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_one, hk]

/-- Closed-form expansion of `butcherShiftedLegendre 13`.

Follows the cycle 287 `_eleven` template (per-`k` `simp` arm + `norm_num`).
The relevant unsigned coefficients at `k = 0,…,13` are
`(1, −182, 8190, −160160, 1701700, −11027016, 46558512, −133024320,
261891630, −355655300, 327202876, −194699232, 67603900, −10400600)`;
higher slots vanish since `13.choose k = 0` for `k ≥ 14`. The outer
Butcher sign factor `(-1)^13 = −1` flips every sign, producing the
closed form above. Sanity: `P_13^*(0) = -1` (matches `(-1)^13`);
`P_13^*(1) = 1` (matches (342b), verified via Python `Fraction` in
cycle 300). Thirteenth rung of the empirical ladder — cycles 282–287
established `n = 2,…,10` and cycle 287 added `n = 11`. -/
theorem butcherShiftedLegendre_thirteen :
    butcherShiftedLegendre 13 =
      Polynomial.C 10400600 * Polynomial.X ^ 13
        - Polynomial.C 67603900 * Polynomial.X ^ 12
        + Polynomial.C 194699232 * Polynomial.X ^ 11
        - Polynomial.C 327202876 * Polynomial.X ^ 10
        + Polynomial.C 355655300 * Polynomial.X ^ 9
        - Polynomial.C 261891630 * Polynomial.X ^ 8
        + Polynomial.C 133024320 * Polynomial.X ^ 7
        - Polynomial.C 46558512 * Polynomial.X ^ 6
        + Polynomial.C 11027016 * Polynomial.X ^ 5
        - Polynomial.C 1701700 * Polynomial.X ^ 4
        + Polynomial.C 160160 * Polynomial.X ^ 3
        - Polynomial.C 8190 * Polynomial.X ^ 2
        + Polynomial.C 182 * Polynomial.X
        - Polynomial.C 1 := by
  unfold butcherShiftedLegendre
  ext k
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
             Polynomial.coeff_shiftedLegendre]
  match k with
  | 0 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_X_pow, Polynomial.coeff_X,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 1 =>
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_C, Polynomial.coeff_one]
      norm_num
  | 2 =>
      have hch1 : Nat.choose 15 13 = 105 := by decide
      have hch2 : Nat.choose 13 2 = 78 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 3 =>
      have hch1 : Nat.choose 16 13 = 560 := by decide
      have hch2 : Nat.choose 13 3 = 286 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 4 =>
      have hch1 : Nat.choose 17 13 = 2380 := by decide
      have hch2 : Nat.choose 13 4 = 715 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 5 =>
      have hch1 : Nat.choose 18 13 = 8568 := by decide
      have hch2 : Nat.choose 13 5 = 1287 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 6 =>
      have hch1 : Nat.choose 19 13 = 27132 := by decide
      have hch2 : Nat.choose 13 6 = 1716 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 7 =>
      have hch1 : Nat.choose 20 13 = 77520 := by decide
      have hch2 : Nat.choose 13 7 = 1716 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 8 =>
      have hch1 : Nat.choose 21 13 = 203490 := by decide
      have hch2 : Nat.choose 13 8 = 1287 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 9 =>
      have hch1 : Nat.choose 22 13 = 497420 := by decide
      have hch2 : Nat.choose 13 9 = 715 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 10 =>
      have hch1 : Nat.choose 23 13 = 1144066 := by decide
      have hch2 : Nat.choose 13 10 = 286 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 11 =>
      have hch1 : Nat.choose 24 13 = 2496144 := by decide
      have hch2 : Nat.choose 13 11 = 78 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 12 =>
      have hch1 : Nat.choose 25 13 = 5200300 := by decide
      have hch2 : Nat.choose 13 12 = 13 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch1, hch2]
      norm_num
  | 13 =>
      have hch : Nat.choose 26 13 = 10400600 := by decide
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_one, hch]
      norm_num
  | (k+14) =>
      have hk : (13 : ℕ).choose (k + 14) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
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

/-! ### (342a) — Orthogonality of `P_n^*` on `[0, 1]`

Butcher §342 (342a): `∫₀¹ P_m^*(x) P_n^*(x) dx = 0` for `m ≠ n`.

Proof strategy (Aristotle, cycle 274 submission, run `727396d5`, COMPLETE
2026-05-15): WLOG `m < n`. Apply Rodrigues' formula
(`butcherShiftedLegendre_rodrigues`) to express `P_n^*` as
`((-1)^n / n!) · D^n (X^n (1-X)^n)`. The boundary terms vanish at both
endpoints because each Leibniz summand of `D^k (X^n (1-X)^n)` for `k < n`
retains a factor with positive `X`-exponent (at `x = 0`) or positive
`(1-X)`-exponent (at `x = 1`). After `n` integrations by parts, all
derivatives sit on `P_m^*`, whose `natDegree = m < n`
(`butcherShiftedLegendre_natDegree`), so `D^n P_m^* = 0`. -/

/-- Helper for (342a): the `k`-th derivative of `X^n · (1-X)^n` vanishes
at `x = 0` for `k < n`. Each Leibniz summand has `X^j` with `j ≥ 1`
surviving since `j = n - (k - i) ≥ n - k ≥ 1`. -/
private lemma iterDeriv_XnOneSubXn_eval_zero {n k : ℕ} (hk : k < n) :
    (Polynomial.derivative^[k]
      ((Polynomial.X : Polynomial ℝ) ^ n *
        (1 - Polynomial.X) ^ n)).eval 0 = 0 := by
  have h_deriv_sum : ∀ k < n,
      (Polynomial.derivative^[k]
        (Polynomial.X ^ n * (1 - Polynomial.X) ^ n)).eval (0 : ℝ)
      = ∑ j ∈ Finset.range (k + 1),
          Nat.choose k j * (Nat.descFactorial n (k - j)) *
            (Polynomial.derivative^[j]
              ((1 - Polynomial.X) ^ n)).eval (0 : ℝ) *
            0 ^ (n - (k - j)) := by
    intro k hk
    have h_leibniz : Polynomial.derivative^[k]
        (Polynomial.X ^ n * (1 - Polynomial.X) ^ n)
        = ∑ j ∈ Finset.range (k + 1),
            Polynomial.C (Nat.choose k j : ℝ)
              * (Polynomial.derivative^[k - j] (Polynomial.X ^ n))
              * (Polynomial.derivative^[j] ((1 - Polynomial.X) ^ n)) := by
      have h_deriv_sum : ∀ p q : Polynomial ℝ, ∀ k,
          Polynomial.derivative^[k] (p * q)
          = ∑ j ∈ Finset.range (k + 1),
              Nat.choose k j •
                (Polynomial.derivative^[k - j] p *
                  Polynomial.derivative^[j] q) :=
        fun p q k => Polynomial.iterate_derivative_mul p q
      convert h_deriv_sum (Polynomial.X ^ n) ((1 - Polynomial.X) ^ n) k using 1
      norm_num [mul_assoc]
    have h_deriv_Xn : ∀ j ≤ k,
        (Polynomial.derivative^[j] (Polynomial.X ^ n)).eval (0 : ℝ)
        = Nat.descFactorial n j * 0 ^ (n - j) := by
      have h_deriv_def : ∀ m : ℕ,
          Polynomial.derivative^[m] (Polynomial.X ^ n)
          = Polynomial.C (Nat.descFactorial n m : ℝ) *
              Polynomial.X ^ (n - m) := by
        intro m
        induction' m with m ih
        · simp
        · simp_all +decide [Function.iterate_succ_apply',
                            Polynomial.derivative_pow]
          rw [Nat.sub_sub]
          ring
      simp_all +decide [Polynomial.derivative_pow]
    simp_all +decide [mul_assoc, mul_comm, mul_left_comm,
                      Polynomial.eval_finset_sum]
  rw [h_deriv_sum k hk, Finset.sum_eq_zero]
  intros
  simp_all +decide [Nat.sub_eq_zero_of_le, le_of_lt]
  omega

/-- Helper for (342a): the `k`-th derivative of `X^n · (1-X)^n` vanishes
at `x = 1` for `k < n`. Each Leibniz summand has `(1 - X)^j` with `j ≥ 1`
surviving. -/
private lemma iterDeriv_XnOneSubXn_eval_one {n k : ℕ} (hk : k < n) :
    (Polynomial.derivative^[k]
      ((Polynomial.X : Polynomial ℝ) ^ n *
        (1 - Polynomial.X) ^ n)).eval 1 = 0 := by
  let P : Polynomial ℝ := Polynomial.X ^ n
  let Q : Polynomial ℝ := (1 - Polynomial.X) ^ n
  have h_diff : Polynomial.derivative^[k] (P * Q)
      = ∑ j ∈ Finset.range k.succ,
          k.choose j •
            (Polynomial.derivative^[k - j] P *
              Polynomial.derivative^[j] Q) :=
    Polynomial.iterate_derivative_mul P Q
  have h_Q_deriv : ∀ j < n,
      (Polynomial.derivative^[j]
        ((1 - Polynomial.X : Polynomial ℝ) ^ n)).eval 1 = 0 := by
    intros j hj
    have h_Q_deriv_step : Polynomial.derivative^[j]
        ((1 - Polynomial.X : Polynomial ℝ) ^ n)
        = (-1) ^ j * (Nat.descFactorial n j : ℝ) •
            (1 - Polynomial.X : Polynomial ℝ) ^ (n - j) := by
      induction' j with j ih
      · simp
      · simp_all +decide [Function.iterate_succ_apply',
                          Polynomial.derivative_pow]
        rw [ih (Nat.lt_of_succ_lt hj)]
        norm_num [Polynomial.derivative_pow, Polynomial.derivative_mul,
                  Polynomial.derivative_X, Polynomial.derivative_one,
                  Polynomial.smul_eq_C_mul]
        ring
        rw [Nat.sub_sub, add_comm]
    simp_all +decide [ne_of_gt]
  replace h_diff := congr_arg (Polynomial.eval 1) h_diff
  simp_all +decide [Polynomial.eval_finset_sum]
  exact h_diff.trans
    (Finset.sum_eq_zero fun x hx => by
      specialize h_Q_deriv x (by linarith [Finset.mem_range.mp hx])
      aesop)

/-- Helper for (342a): integration by parts for polynomial evaluations
on `[0,1]`. A clean specialization of
`intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt` with
`u := f.eval`, `v := g.eval`. -/
private lemma poly_ibp (f g : Polynomial ℝ) :
    ∫ x in (0:ℝ)..1, f.eval x * (Polynomial.derivative g).eval x =
    f.eval 1 * g.eval 1 - f.eval 0 * g.eval 0 -
    ∫ x in (0:ℝ)..1, (Polynomial.derivative f).eval x * g.eval x :=
  intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x => f.eval x) (v := fun x => g.eval x)
    (u' := fun x => (Polynomial.derivative f).eval x)
    (v' := fun x => (Polynomial.derivative g).eval x)
    (Polynomial.continuous f).continuousOn
    (Polynomial.continuous g).continuousOn
    (fun x _ => f.hasDerivAt x)
    (fun x _ => g.hasDerivAt x)
    ((Polynomial.continuous _).intervalIntegrable _ _)
    ((Polynomial.continuous _).intervalIntegrable _ _)

/-- General iterated IBP: if `f` has degree `< n` and all derivatives
`D^k g` for `k < n` vanish at both endpoints `0` and `1`, then
`∫₀¹ f · D^n(g) = 0`. -/
private lemma integral_poly_mul_iterDeriv_vanish
    (f g : Polynomial ℝ) (n : ℕ)
    (hf : f.natDegree < n)
    (hg0 : ∀ k, k < n → (Polynomial.derivative^[k] g).eval (0:ℝ) = 0)
    (hg1 : ∀ k, k < n → (Polynomial.derivative^[k] g).eval (1:ℝ) = 0) :
    ∫ x in (0:ℝ)..1,
      f.eval x * (Polynomial.derivative^[n] g).eval x = 0 := by
  induction' n with n ih generalizing f g <;>
    simp_all +decide [Function.iterate_succ_apply']
  have h_parts : ∫ x in (0:ℝ)..1,
      (f.eval x) *
        (Polynomial.derivative ((Polynomial.derivative^[n] g))).eval x
      = (f.eval 1) * ((Polynomial.derivative^[n] g).eval 1)
          - (f.eval 0) * ((Polynomial.derivative^[n] g).eval 0)
          - ∫ x in (0:ℝ)..1,
              (Polynomial.derivative f).eval x *
                ((Polynomial.derivative^[n] g).eval x) := by
    rw [poly_ibp]
  by_cases h : Polynomial.natDegree (Polynomial.derivative f) < n <;>
    simp_all +decide [Function.iterate_succ_apply']
  · exact ih _ _ h (fun k hk => hg0 k hk.le) (fun k hk => hg1 k hk.le)
  · rcases k : Polynomial.natDegree f with (_ | k) <;>
      simp_all +decide [Polynomial.natDegree]
    · cases k <;> simp_all +decide [Polynomial.degree_eq_natDegree]
      rw [Polynomial.eq_C_of_degree_eq_zero ‹f.degree = 0›]
      aesop
    · exact absurd h
        (not_le_of_gt (Nat.lt_of_le_of_lt (Nat.le_refl _) hf))

/-- Specialization of `integral_poly_mul_iterDeriv_vanish` to
`g = X^n · (1-X)^n`: for `f` with `natDegree f < n`, the integral of
`f` against `D^n(X^n · (1-X)^n)` is zero. -/
private lemma integral_poly_mul_iterDeriv_XnOneSubXn_eq_zero
    (f : Polynomial ℝ) (n : ℕ) (hf : f.natDegree < n) :
    ∫ x in (0:ℝ)..1,
      f.eval x * (Polynomial.derivative^[n]
        ((Polynomial.X : Polynomial ℝ) ^ n *
          (1 - Polynomial.X) ^ n)).eval x = 0 :=
  integral_poly_mul_iterDeriv_vanish f _ n hf
    (fun _ hk => iterDeriv_XnOneSubXn_eval_zero hk)
    (fun _ hk => iterDeriv_XnOneSubXn_eval_one hk)

/-- **Butcher §342 (342a)** — orthogonality of `P_n^*` on `[0, 1]`.

For all `m ≠ n`, `∫₀¹ P_m^*(x) · P_n^*(x) dx = 0`.

Proof (Aristotle, cycle 274 submission, integrated cycle 277):
WLOG `m < n`. Substitute Rodrigues' formula
(`butcherShiftedLegendre_rodrigues`) to write `P_n^*` as
`((-1)^n / n!) · D^n (X^n (1-X)^n)`. Apply
`integral_poly_mul_iterDeriv_XnOneSubXn_eq_zero` with `f := P_m^*`
(which has `natDegree = m < n` by `butcherShiftedLegendre_natDegree`)
to kill the integral. -/
theorem butcherShiftedLegendre_orthogonal {m n : ℕ} (hmn : m ≠ n) :
    ∫ x in (0 : ℝ)..1,
      (butcherShiftedLegendre m).eval x *
      (butcherShiftedLegendre n).eval x = 0 := by
  wlog hmn' : m < n generalizing m n
  · convert this hmn.symm
      (lt_of_le_of_ne (le_of_not_gt hmn') hmn.symm) using 1
    ac_rfl
  have h_integral : ∫ x in (0 : ℝ)..1,
      (butcherShiftedLegendre m).eval x * (butcherShiftedLegendre n).eval x
      = (-1 : ℝ) ^ n / (n.factorial : ℝ) *
          ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre m).eval x *
            ((Polynomial.derivative^[n]
              ((Polynomial.X : Polynomial ℝ) ^ n *
                (1 - Polynomial.X) ^ n)).eval x) := by
    have h_subst : ∀ x : ℝ, (butcherShiftedLegendre n).eval x =
        ((-1 : ℝ) ^ n / (n.factorial : ℝ)) *
          ((Polynomial.derivative^[n]
            ((Polynomial.X : Polynomial ℝ) ^ n *
              (1 - Polynomial.X) ^ n)).eval x) := by
      intro x
      have := congr_arg (Polynomial.eval x)
        (butcherShiftedLegendre_rodrigues n)
      simp only [Polynomial.eval_mul, Polynomial.eval_C] at this
      rw [div_mul_eq_mul_div, eq_div_iff] <;> [linarith; positivity]
    simp_rw [h_subst, ← intervalIntegral.integral_const_mul]
    congr 1
    ext
    ring
  rw [h_integral,
      integral_poly_mul_iterDeriv_XnOneSubXn_eq_zero _ _
        (by rw [butcherShiftedLegendre_natDegree]; exact hmn'),
      mul_zero]

/-! ### Non-vacuity witnesses (342a)

These confirm orthogonality on the smallest non-trivial pairs. -/

example : ∫ x in (0 : ℝ)..1,
    (butcherShiftedLegendre 0).eval x * (butcherShiftedLegendre 1).eval x
      = 0 :=
  butcherShiftedLegendre_orthogonal (by decide)

example : ∫ x in (0 : ℝ)..1,
    (butcherShiftedLegendre 1).eval x * (butcherShiftedLegendre 2).eval x
      = 0 :=
  butcherShiftedLegendre_orthogonal (by decide)

example : ∫ x in (0 : ℝ)..1,
    (butcherShiftedLegendre 0).eval x * (butcherShiftedLegendre 2).eval x
      = 0 :=
  butcherShiftedLegendre_orthogonal (by decide)

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

/-- **Butcher §342 (342d) at `n = 3`**: `∫₀¹ (P_3^*(x))^2 dx = 1/7`.

The `n = 3` instance of (342d). Direct computation:
`P_3^*(x) = 20x³ - 30x² + 12x - 1` (`butcherShiftedLegendre_three`), so
`(P_3^*(x))^2 = 400x⁶ - 1200x⁵ + 1380x⁴ - 760x³ + 204x² - 24x + 1`.
Then
`∫₀¹ (400x⁶ - 1200x⁵ + 1380x⁴ - 760x³ + 204x² - 24x + 1) dx`
`= 400/7 - 200 + 276 - 190 + 68 - 12 + 1 = 1/7`. -/
theorem butcherShiftedLegendre_norm_sq_three :
    ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 3).eval x ^ 2 = 1 / 7 := by
  have hP : ∀ x : ℝ, (butcherShiftedLegendre 3).eval x ^ 2
      = 400 * x ^ 6 - 1200 * x ^ 5 + 1380 * x ^ 4 - 760 * x ^ 3
        + 204 * x ^ 2 - 24 * x + 1 := by
    intro x
    rw [butcherShiftedLegendre_three]
    simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    ring
  simp_rw [hP]
  have hi_x6 : IntervalIntegrable (fun x : ℝ => x ^ 6) MeasureTheory.volume 0 1 :=
    (continuous_pow 6).intervalIntegrable 0 1
  have hi_x5 : IntervalIntegrable (fun x : ℝ => x ^ 5) MeasureTheory.volume 0 1 :=
    (continuous_pow 5).intervalIntegrable 0 1
  have hi_x4 : IntervalIntegrable (fun x : ℝ => x ^ 4) MeasureTheory.volume 0 1 :=
    (continuous_pow 4).intervalIntegrable 0 1
  have hi_x3 : IntervalIntegrable (fun x : ℝ => x ^ 3) MeasureTheory.volume 0 1 :=
    (continuous_pow 3).intervalIntegrable 0 1
  have hi_x2 : IntervalIntegrable (fun x : ℝ => x ^ 2) MeasureTheory.volume 0 1 :=
    (continuous_pow 2).intervalIntegrable 0 1
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have h6 : ∫ x in (0 : ℝ)..1, x ^ 6 = 1 / 7 := by
    rw [integral_pow]; norm_num
  have h5 : ∫ x in (0 : ℝ)..1, x ^ 5 = 1 / 6 := by
    rw [integral_pow]; norm_num
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
  -- The integrand is left-associative:
  -- ((((((400·x⁶ − 1200·x⁵) + 1380·x⁴) − 760·x³) + 204·x²) − 24·x) + 1)
  rw [intervalIntegral.integral_add
        ((((((hi_x6.const_mul 400).sub (hi_x5.const_mul 1200)).add
              (hi_x4.const_mul 1380)).sub (hi_x3.const_mul 760)).add
              (hi_x2.const_mul 204)).sub (hi_x.const_mul 24))
        intervalIntegrable_const,
      intervalIntegral.integral_sub
        (((((hi_x6.const_mul 400).sub (hi_x5.const_mul 1200)).add
              (hi_x4.const_mul 1380)).sub (hi_x3.const_mul 760)).add
              (hi_x2.const_mul 204))
        (hi_x.const_mul 24),
      intervalIntegral.integral_add
        ((((hi_x6.const_mul 400).sub (hi_x5.const_mul 1200)).add
              (hi_x4.const_mul 1380)).sub (hi_x3.const_mul 760))
        (hi_x2.const_mul 204),
      intervalIntegral.integral_sub
        (((hi_x6.const_mul 400).sub (hi_x5.const_mul 1200)).add
              (hi_x4.const_mul 1380))
        (hi_x3.const_mul 760),
      intervalIntegral.integral_add
        ((hi_x6.const_mul 400).sub (hi_x5.const_mul 1200))
        (hi_x4.const_mul 1380),
      intervalIntegral.integral_sub
        (hi_x6.const_mul 400)
        (hi_x5.const_mul 1200),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      h6, h5, h4, h3, h2, h1, integral_one]
  ring

/-- **Butcher §342 (342d) at `n = 4`**: `∫₀¹ (P_4^*(x))^2 dx = 1/9`.

The `n = 4` instance of (342d). Direct computation:
`P_4^*(x) = 70x⁴ - 140x³ + 90x² - 20x + 1` (`butcherShiftedLegendre_four`),
so
`(P_4^*(x))^2 = 4900x⁸ - 19600x⁷ + 32200x⁶ - 28000x⁵ + 13840x⁴
                - 3880x³ + 580x² - 40x + 1`.
Then
`∫₀¹ (4900x⁸ − 19600x⁷ + 32200x⁶ − 28000x⁵ + 13840x⁴ − 3880x³
       + 580x² − 40x + 1) dx`
`= 4900/9 − 2450 + 4600 − 14000/3 + 2768 − 970 + 580/3 − 20 + 1 = 1/9`. -/
theorem butcherShiftedLegendre_norm_sq_four :
    ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 4).eval x ^ 2 = 1 / 9 := by
  have hP : ∀ x : ℝ, (butcherShiftedLegendre 4).eval x ^ 2
      = 4900 * x ^ 8 - 19600 * x ^ 7 + 32200 * x ^ 6 - 28000 * x ^ 5
        + 13840 * x ^ 4 - 3880 * x ^ 3 + 580 * x ^ 2 - 40 * x + 1 := by
    intro x
    rw [butcherShiftedLegendre_four]
    simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    ring
  simp_rw [hP]
  have hi_x8 : IntervalIntegrable (fun x : ℝ => x ^ 8) MeasureTheory.volume 0 1 :=
    (continuous_pow 8).intervalIntegrable 0 1
  have hi_x7 : IntervalIntegrable (fun x : ℝ => x ^ 7) MeasureTheory.volume 0 1 :=
    (continuous_pow 7).intervalIntegrable 0 1
  have hi_x6 : IntervalIntegrable (fun x : ℝ => x ^ 6) MeasureTheory.volume 0 1 :=
    (continuous_pow 6).intervalIntegrable 0 1
  have hi_x5 : IntervalIntegrable (fun x : ℝ => x ^ 5) MeasureTheory.volume 0 1 :=
    (continuous_pow 5).intervalIntegrable 0 1
  have hi_x4 : IntervalIntegrable (fun x : ℝ => x ^ 4) MeasureTheory.volume 0 1 :=
    (continuous_pow 4).intervalIntegrable 0 1
  have hi_x3 : IntervalIntegrable (fun x : ℝ => x ^ 3) MeasureTheory.volume 0 1 :=
    (continuous_pow 3).intervalIntegrable 0 1
  have hi_x2 : IntervalIntegrable (fun x : ℝ => x ^ 2) MeasureTheory.volume 0 1 :=
    (continuous_pow 2).intervalIntegrable 0 1
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have h8 : ∫ x in (0 : ℝ)..1, x ^ 8 = 1 / 9 := by
    rw [integral_pow]; norm_num
  have h7 : ∫ x in (0 : ℝ)..1, x ^ 7 = 1 / 8 := by
    rw [integral_pow]; norm_num
  have h6 : ∫ x in (0 : ℝ)..1, x ^ 6 = 1 / 7 := by
    rw [integral_pow]; norm_num
  have h5 : ∫ x in (0 : ℝ)..1, x ^ 5 = 1 / 6 := by
    rw [integral_pow]; norm_num
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
  -- The integrand is left-associative:
  -- ((((((((4900·x⁸ − 19600·x⁷) + 32200·x⁶) − 28000·x⁵) + 13840·x⁴)
  --     − 3880·x³) + 580·x²) − 40·x) + 1)
  rw [intervalIntegral.integral_add
        ((((((((hi_x8.const_mul 4900).sub (hi_x7.const_mul 19600)).add
              (hi_x6.const_mul 32200)).sub (hi_x5.const_mul 28000)).add
              (hi_x4.const_mul 13840)).sub (hi_x3.const_mul 3880)).add
              (hi_x2.const_mul 580)).sub (hi_x.const_mul 40))
        intervalIntegrable_const,
      intervalIntegral.integral_sub
        (((((((hi_x8.const_mul 4900).sub (hi_x7.const_mul 19600)).add
              (hi_x6.const_mul 32200)).sub (hi_x5.const_mul 28000)).add
              (hi_x4.const_mul 13840)).sub (hi_x3.const_mul 3880)).add
              (hi_x2.const_mul 580))
        (hi_x.const_mul 40),
      intervalIntegral.integral_add
        ((((((hi_x8.const_mul 4900).sub (hi_x7.const_mul 19600)).add
              (hi_x6.const_mul 32200)).sub (hi_x5.const_mul 28000)).add
              (hi_x4.const_mul 13840)).sub (hi_x3.const_mul 3880))
        (hi_x2.const_mul 580),
      intervalIntegral.integral_sub
        (((((hi_x8.const_mul 4900).sub (hi_x7.const_mul 19600)).add
              (hi_x6.const_mul 32200)).sub (hi_x5.const_mul 28000)).add
              (hi_x4.const_mul 13840))
        (hi_x3.const_mul 3880),
      intervalIntegral.integral_add
        ((((hi_x8.const_mul 4900).sub (hi_x7.const_mul 19600)).add
              (hi_x6.const_mul 32200)).sub (hi_x5.const_mul 28000))
        (hi_x4.const_mul 13840),
      intervalIntegral.integral_sub
        (((hi_x8.const_mul 4900).sub (hi_x7.const_mul 19600)).add
              (hi_x6.const_mul 32200))
        (hi_x5.const_mul 28000),
      intervalIntegral.integral_add
        ((hi_x8.const_mul 4900).sub (hi_x7.const_mul 19600))
        (hi_x6.const_mul 32200),
      intervalIntegral.integral_sub
        (hi_x8.const_mul 4900)
        (hi_x7.const_mul 19600),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      h8, h7, h6, h5, h4, h3, h2, h1, integral_one]
  ring

/-- **Butcher §342 (342d) at `n = 5`**: `∫₀¹ (P_5^*(x))^2 dx = 1/11`.

The `n = 5` instance of (342d). Direct computation:
`P_5^*(x) = 252x⁵ - 630x⁴ + 560x³ - 210x² + 30x - 1`
(`butcherShiftedLegendre_five`), so
`(P_5^*(x))^2 = 63504x¹⁰ - 317520x⁹ + 679140x⁸ - 811440x⁷ + 593320x⁶
                - 273504x⁵ + 78960x⁴ - 13720x³ + 1320x² - 60x + 1`.
Then
`∫₀¹ (63504x¹⁰ − 317520x⁹ + 679140x⁸ − 811440x⁷ + 593320x⁶ − 273504x⁵
       + 78960x⁴ − 13720x³ + 1320x² − 60x + 1) dx`
`= 63504/11 − 31752 + 75460 − 101430 + 84760 − 45584 + 15792 − 3430
   + 440 − 30 + 1 = 1/11`. -/
theorem butcherShiftedLegendre_norm_sq_five :
    ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 5).eval x ^ 2 = 1 / 11 := by
  have hP : ∀ x : ℝ, (butcherShiftedLegendre 5).eval x ^ 2
      = 63504 * x ^ 10 - 317520 * x ^ 9 + 679140 * x ^ 8 - 811440 * x ^ 7
        + 593320 * x ^ 6 - 273504 * x ^ 5 + 78960 * x ^ 4 - 13720 * x ^ 3
        + 1320 * x ^ 2 - 60 * x + 1 := by
    intro x
    rw [butcherShiftedLegendre_five]
    simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    ring
  simp_rw [hP]
  have hi_x10 : IntervalIntegrable (fun x : ℝ => x ^ 10) MeasureTheory.volume 0 1 :=
    (continuous_pow 10).intervalIntegrable 0 1
  have hi_x9 : IntervalIntegrable (fun x : ℝ => x ^ 9) MeasureTheory.volume 0 1 :=
    (continuous_pow 9).intervalIntegrable 0 1
  have hi_x8 : IntervalIntegrable (fun x : ℝ => x ^ 8) MeasureTheory.volume 0 1 :=
    (continuous_pow 8).intervalIntegrable 0 1
  have hi_x7 : IntervalIntegrable (fun x : ℝ => x ^ 7) MeasureTheory.volume 0 1 :=
    (continuous_pow 7).intervalIntegrable 0 1
  have hi_x6 : IntervalIntegrable (fun x : ℝ => x ^ 6) MeasureTheory.volume 0 1 :=
    (continuous_pow 6).intervalIntegrable 0 1
  have hi_x5 : IntervalIntegrable (fun x : ℝ => x ^ 5) MeasureTheory.volume 0 1 :=
    (continuous_pow 5).intervalIntegrable 0 1
  have hi_x4 : IntervalIntegrable (fun x : ℝ => x ^ 4) MeasureTheory.volume 0 1 :=
    (continuous_pow 4).intervalIntegrable 0 1
  have hi_x3 : IntervalIntegrable (fun x : ℝ => x ^ 3) MeasureTheory.volume 0 1 :=
    (continuous_pow 3).intervalIntegrable 0 1
  have hi_x2 : IntervalIntegrable (fun x : ℝ => x ^ 2) MeasureTheory.volume 0 1 :=
    (continuous_pow 2).intervalIntegrable 0 1
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have h10 : ∫ x in (0 : ℝ)..1, x ^ 10 = 1 / 11 := by
    rw [integral_pow]; norm_num
  have h9 : ∫ x in (0 : ℝ)..1, x ^ 9 = 1 / 10 := by
    rw [integral_pow]; norm_num
  have h8 : ∫ x in (0 : ℝ)..1, x ^ 8 = 1 / 9 := by
    rw [integral_pow]; norm_num
  have h7 : ∫ x in (0 : ℝ)..1, x ^ 7 = 1 / 8 := by
    rw [integral_pow]; norm_num
  have h6 : ∫ x in (0 : ℝ)..1, x ^ 6 = 1 / 7 := by
    rw [integral_pow]; norm_num
  have h5 : ∫ x in (0 : ℝ)..1, x ^ 5 = 1 / 6 := by
    rw [integral_pow]; norm_num
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
  -- The integrand is left-associative:
  -- ((((((((((63504·x¹⁰ − 317520·x⁹) + 679140·x⁸) − 811440·x⁷) + 593320·x⁶)
  --       − 273504·x⁵) + 78960·x⁴) − 13720·x³) + 1320·x²) − 60·x) + 1)
  rw [intervalIntegral.integral_add
        ((((((((((hi_x10.const_mul 63504).sub (hi_x9.const_mul 317520)).add
              (hi_x8.const_mul 679140)).sub (hi_x7.const_mul 811440)).add
              (hi_x6.const_mul 593320)).sub (hi_x5.const_mul 273504)).add
              (hi_x4.const_mul 78960)).sub (hi_x3.const_mul 13720)).add
              (hi_x2.const_mul 1320)).sub (hi_x.const_mul 60))
        intervalIntegrable_const,
      intervalIntegral.integral_sub
        (((((((((hi_x10.const_mul 63504).sub (hi_x9.const_mul 317520)).add
              (hi_x8.const_mul 679140)).sub (hi_x7.const_mul 811440)).add
              (hi_x6.const_mul 593320)).sub (hi_x5.const_mul 273504)).add
              (hi_x4.const_mul 78960)).sub (hi_x3.const_mul 13720)).add
              (hi_x2.const_mul 1320))
        (hi_x.const_mul 60),
      intervalIntegral.integral_add
        ((((((((hi_x10.const_mul 63504).sub (hi_x9.const_mul 317520)).add
              (hi_x8.const_mul 679140)).sub (hi_x7.const_mul 811440)).add
              (hi_x6.const_mul 593320)).sub (hi_x5.const_mul 273504)).add
              (hi_x4.const_mul 78960)).sub (hi_x3.const_mul 13720))
        (hi_x2.const_mul 1320),
      intervalIntegral.integral_sub
        (((((((hi_x10.const_mul 63504).sub (hi_x9.const_mul 317520)).add
              (hi_x8.const_mul 679140)).sub (hi_x7.const_mul 811440)).add
              (hi_x6.const_mul 593320)).sub (hi_x5.const_mul 273504)).add
              (hi_x4.const_mul 78960))
        (hi_x3.const_mul 13720),
      intervalIntegral.integral_add
        ((((((hi_x10.const_mul 63504).sub (hi_x9.const_mul 317520)).add
              (hi_x8.const_mul 679140)).sub (hi_x7.const_mul 811440)).add
              (hi_x6.const_mul 593320)).sub (hi_x5.const_mul 273504))
        (hi_x4.const_mul 78960),
      intervalIntegral.integral_sub
        (((((hi_x10.const_mul 63504).sub (hi_x9.const_mul 317520)).add
              (hi_x8.const_mul 679140)).sub (hi_x7.const_mul 811440)).add
              (hi_x6.const_mul 593320))
        (hi_x5.const_mul 273504),
      intervalIntegral.integral_add
        ((((hi_x10.const_mul 63504).sub (hi_x9.const_mul 317520)).add
              (hi_x8.const_mul 679140)).sub (hi_x7.const_mul 811440))
        (hi_x6.const_mul 593320),
      intervalIntegral.integral_sub
        (((hi_x10.const_mul 63504).sub (hi_x9.const_mul 317520)).add
              (hi_x8.const_mul 679140))
        (hi_x7.const_mul 811440),
      intervalIntegral.integral_add
        ((hi_x10.const_mul 63504).sub (hi_x9.const_mul 317520))
        (hi_x8.const_mul 679140),
      intervalIntegral.integral_sub
        (hi_x10.const_mul 63504)
        (hi_x9.const_mul 317520),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, integral_one]
  ring

/-- **Butcher §342 (342d) at `n = 6`**: `∫₀¹ (P_6^*(x))^2 dx = 1/13`.

The `n = 6` instance of (342d). Direct computation:
`P_6^*(x) = 924x⁶ - 2772x⁵ + 3150x⁴ - 1680x³ + 420x² - 42x + 1`
(`butcherShiftedLegendre_six`), so the squared coefficient
convolution gives
`(P_6^*(x))^2 = 853776x¹² − 5122656x¹¹ + 13505184x¹⁰ − 20568240x⁹
                + 20012580x⁸ − 12990096x⁷ + 5703096x⁶ − 1681344x⁵
                + 323820x⁴ − 38640x³ + 2604x² − 84x + 1`.
Integrating termwise and summing the resulting 13 fractions yields
`1/13 = 1/(2·6 + 1)`. -/
theorem butcherShiftedLegendre_norm_sq_six :
    ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 6).eval x ^ 2 = 1 / 13 := by
  have hP : ∀ x : ℝ, (butcherShiftedLegendre 6).eval x ^ 2
      = 853776 * x ^ 12 - 5122656 * x ^ 11 + 13505184 * x ^ 10
        - 20568240 * x ^ 9 + 20012580 * x ^ 8 - 12990096 * x ^ 7
        + 5703096 * x ^ 6 - 1681344 * x ^ 5 + 323820 * x ^ 4
        - 38640 * x ^ 3 + 2604 * x ^ 2 - 84 * x + 1 := by
    intro x
    rw [butcherShiftedLegendre_six]
    simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    ring
  simp_rw [hP]
  have hi_x12 : IntervalIntegrable (fun x : ℝ => x ^ 12) MeasureTheory.volume 0 1 :=
    (continuous_pow 12).intervalIntegrable 0 1
  have hi_x11 : IntervalIntegrable (fun x : ℝ => x ^ 11) MeasureTheory.volume 0 1 :=
    (continuous_pow 11).intervalIntegrable 0 1
  have hi_x10 : IntervalIntegrable (fun x : ℝ => x ^ 10) MeasureTheory.volume 0 1 :=
    (continuous_pow 10).intervalIntegrable 0 1
  have hi_x9 : IntervalIntegrable (fun x : ℝ => x ^ 9) MeasureTheory.volume 0 1 :=
    (continuous_pow 9).intervalIntegrable 0 1
  have hi_x8 : IntervalIntegrable (fun x : ℝ => x ^ 8) MeasureTheory.volume 0 1 :=
    (continuous_pow 8).intervalIntegrable 0 1
  have hi_x7 : IntervalIntegrable (fun x : ℝ => x ^ 7) MeasureTheory.volume 0 1 :=
    (continuous_pow 7).intervalIntegrable 0 1
  have hi_x6 : IntervalIntegrable (fun x : ℝ => x ^ 6) MeasureTheory.volume 0 1 :=
    (continuous_pow 6).intervalIntegrable 0 1
  have hi_x5 : IntervalIntegrable (fun x : ℝ => x ^ 5) MeasureTheory.volume 0 1 :=
    (continuous_pow 5).intervalIntegrable 0 1
  have hi_x4 : IntervalIntegrable (fun x : ℝ => x ^ 4) MeasureTheory.volume 0 1 :=
    (continuous_pow 4).intervalIntegrable 0 1
  have hi_x3 : IntervalIntegrable (fun x : ℝ => x ^ 3) MeasureTheory.volume 0 1 :=
    (continuous_pow 3).intervalIntegrable 0 1
  have hi_x2 : IntervalIntegrable (fun x : ℝ => x ^ 2) MeasureTheory.volume 0 1 :=
    (continuous_pow 2).intervalIntegrable 0 1
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have h12 : ∫ x in (0 : ℝ)..1, x ^ 12 = 1 / 13 := by
    rw [integral_pow]; norm_num
  have h11 : ∫ x in (0 : ℝ)..1, x ^ 11 = 1 / 12 := by
    rw [integral_pow]; norm_num
  have h10 : ∫ x in (0 : ℝ)..1, x ^ 10 = 1 / 11 := by
    rw [integral_pow]; norm_num
  have h9 : ∫ x in (0 : ℝ)..1, x ^ 9 = 1 / 10 := by
    rw [integral_pow]; norm_num
  have h8 : ∫ x in (0 : ℝ)..1, x ^ 8 = 1 / 9 := by
    rw [integral_pow]; norm_num
  have h7 : ∫ x in (0 : ℝ)..1, x ^ 7 = 1 / 8 := by
    rw [integral_pow]; norm_num
  have h6 : ∫ x in (0 : ℝ)..1, x ^ 6 = 1 / 7 := by
    rw [integral_pow]; norm_num
  have h5 : ∫ x in (0 : ℝ)..1, x ^ 5 = 1 / 6 := by
    rw [integral_pow]; norm_num
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
  -- The integrand is left-associative (13 terms = 12 binary ops).
  rw [intervalIntegral.integral_add
        ((((((((((((hi_x12.const_mul 853776).sub (hi_x11.const_mul 5122656)).add
              (hi_x10.const_mul 13505184)).sub (hi_x9.const_mul 20568240)).add
              (hi_x8.const_mul 20012580)).sub (hi_x7.const_mul 12990096)).add
              (hi_x6.const_mul 5703096)).sub (hi_x5.const_mul 1681344)).add
              (hi_x4.const_mul 323820)).sub (hi_x3.const_mul 38640)).add
              (hi_x2.const_mul 2604)).sub (hi_x.const_mul 84))
        intervalIntegrable_const,
      intervalIntegral.integral_sub
        (((((((((((hi_x12.const_mul 853776).sub (hi_x11.const_mul 5122656)).add
              (hi_x10.const_mul 13505184)).sub (hi_x9.const_mul 20568240)).add
              (hi_x8.const_mul 20012580)).sub (hi_x7.const_mul 12990096)).add
              (hi_x6.const_mul 5703096)).sub (hi_x5.const_mul 1681344)).add
              (hi_x4.const_mul 323820)).sub (hi_x3.const_mul 38640)).add
              (hi_x2.const_mul 2604))
        (hi_x.const_mul 84),
      intervalIntegral.integral_add
        ((((((((((hi_x12.const_mul 853776).sub (hi_x11.const_mul 5122656)).add
              (hi_x10.const_mul 13505184)).sub (hi_x9.const_mul 20568240)).add
              (hi_x8.const_mul 20012580)).sub (hi_x7.const_mul 12990096)).add
              (hi_x6.const_mul 5703096)).sub (hi_x5.const_mul 1681344)).add
              (hi_x4.const_mul 323820)).sub (hi_x3.const_mul 38640))
        (hi_x2.const_mul 2604),
      intervalIntegral.integral_sub
        (((((((((hi_x12.const_mul 853776).sub (hi_x11.const_mul 5122656)).add
              (hi_x10.const_mul 13505184)).sub (hi_x9.const_mul 20568240)).add
              (hi_x8.const_mul 20012580)).sub (hi_x7.const_mul 12990096)).add
              (hi_x6.const_mul 5703096)).sub (hi_x5.const_mul 1681344)).add
              (hi_x4.const_mul 323820))
        (hi_x3.const_mul 38640),
      intervalIntegral.integral_add
        ((((((((hi_x12.const_mul 853776).sub (hi_x11.const_mul 5122656)).add
              (hi_x10.const_mul 13505184)).sub (hi_x9.const_mul 20568240)).add
              (hi_x8.const_mul 20012580)).sub (hi_x7.const_mul 12990096)).add
              (hi_x6.const_mul 5703096)).sub (hi_x5.const_mul 1681344))
        (hi_x4.const_mul 323820),
      intervalIntegral.integral_sub
        (((((((hi_x12.const_mul 853776).sub (hi_x11.const_mul 5122656)).add
              (hi_x10.const_mul 13505184)).sub (hi_x9.const_mul 20568240)).add
              (hi_x8.const_mul 20012580)).sub (hi_x7.const_mul 12990096)).add
              (hi_x6.const_mul 5703096))
        (hi_x5.const_mul 1681344),
      intervalIntegral.integral_add
        ((((((hi_x12.const_mul 853776).sub (hi_x11.const_mul 5122656)).add
              (hi_x10.const_mul 13505184)).sub (hi_x9.const_mul 20568240)).add
              (hi_x8.const_mul 20012580)).sub (hi_x7.const_mul 12990096))
        (hi_x6.const_mul 5703096),
      intervalIntegral.integral_sub
        (((((hi_x12.const_mul 853776).sub (hi_x11.const_mul 5122656)).add
              (hi_x10.const_mul 13505184)).sub (hi_x9.const_mul 20568240)).add
              (hi_x8.const_mul 20012580))
        (hi_x7.const_mul 12990096),
      intervalIntegral.integral_add
        ((((hi_x12.const_mul 853776).sub (hi_x11.const_mul 5122656)).add
              (hi_x10.const_mul 13505184)).sub (hi_x9.const_mul 20568240))
        (hi_x8.const_mul 20012580),
      intervalIntegral.integral_sub
        (((hi_x12.const_mul 853776).sub (hi_x11.const_mul 5122656)).add
              (hi_x10.const_mul 13505184))
        (hi_x9.const_mul 20568240),
      intervalIntegral.integral_add
        ((hi_x12.const_mul 853776).sub (hi_x11.const_mul 5122656))
        (hi_x10.const_mul 13505184),
      intervalIntegral.integral_sub
        (hi_x12.const_mul 853776)
        (hi_x11.const_mul 5122656),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, integral_one]
  ring

/-- **Butcher §342 (342d) at `n = 7`**: `∫₀¹ (P_7^*(x))^2 dx = 1/15`.

The `n = 7` instance of (342d). Direct computation:
`P_7^*(x) = 3432x^7 - 12012x^6 + 16632x^5 - 11550x^4 + 4200x^3 - 756x^2
            + 56x - 1` (`butcherShiftedLegendre_seven`), so the squared
coefficient convolution gives
`(P_7^*(x))^2 = 11778624x^14 − 82450368x^13 + 258450192x^12 − 478846368x^11
                + 582929424x^10 − 490289184x^9 + 291657828x^8 − 123519792x^7
                + 36990408x^6 − 7677264x^5 + 1065036x^4 − 93072x^3
                + 4648x^2 − 112x + 1`.
Integrating termwise and summing the resulting 15 fractions yields
`1/15 = 1/(2·7 + 1)`. -/
theorem butcherShiftedLegendre_norm_sq_seven :
    ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 7).eval x ^ 2 = 1 / 15 := by
  have hP : ∀ x : ℝ, (butcherShiftedLegendre 7).eval x ^ 2
      = 11778624 * x ^ 14 - 82450368 * x ^ 13 + 258450192 * x ^ 12
        - 478846368 * x ^ 11 + 582929424 * x ^ 10 - 490289184 * x ^ 9
        + 291657828 * x ^ 8 - 123519792 * x ^ 7 + 36990408 * x ^ 6
        - 7677264 * x ^ 5 + 1065036 * x ^ 4 - 93072 * x ^ 3
        + 4648 * x ^ 2 - 112 * x + 1 := by
    intro x
    rw [butcherShiftedLegendre_seven]
    simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    ring
  simp_rw [hP]
  have hi_x14 : IntervalIntegrable (fun x : ℝ => x ^ 14) MeasureTheory.volume 0 1 :=
    (continuous_pow 14).intervalIntegrable 0 1
  have hi_x13 : IntervalIntegrable (fun x : ℝ => x ^ 13) MeasureTheory.volume 0 1 :=
    (continuous_pow 13).intervalIntegrable 0 1
  have hi_x12 : IntervalIntegrable (fun x : ℝ => x ^ 12) MeasureTheory.volume 0 1 :=
    (continuous_pow 12).intervalIntegrable 0 1
  have hi_x11 : IntervalIntegrable (fun x : ℝ => x ^ 11) MeasureTheory.volume 0 1 :=
    (continuous_pow 11).intervalIntegrable 0 1
  have hi_x10 : IntervalIntegrable (fun x : ℝ => x ^ 10) MeasureTheory.volume 0 1 :=
    (continuous_pow 10).intervalIntegrable 0 1
  have hi_x9 : IntervalIntegrable (fun x : ℝ => x ^ 9) MeasureTheory.volume 0 1 :=
    (continuous_pow 9).intervalIntegrable 0 1
  have hi_x8 : IntervalIntegrable (fun x : ℝ => x ^ 8) MeasureTheory.volume 0 1 :=
    (continuous_pow 8).intervalIntegrable 0 1
  have hi_x7 : IntervalIntegrable (fun x : ℝ => x ^ 7) MeasureTheory.volume 0 1 :=
    (continuous_pow 7).intervalIntegrable 0 1
  have hi_x6 : IntervalIntegrable (fun x : ℝ => x ^ 6) MeasureTheory.volume 0 1 :=
    (continuous_pow 6).intervalIntegrable 0 1
  have hi_x5 : IntervalIntegrable (fun x : ℝ => x ^ 5) MeasureTheory.volume 0 1 :=
    (continuous_pow 5).intervalIntegrable 0 1
  have hi_x4 : IntervalIntegrable (fun x : ℝ => x ^ 4) MeasureTheory.volume 0 1 :=
    (continuous_pow 4).intervalIntegrable 0 1
  have hi_x3 : IntervalIntegrable (fun x : ℝ => x ^ 3) MeasureTheory.volume 0 1 :=
    (continuous_pow 3).intervalIntegrable 0 1
  have hi_x2 : IntervalIntegrable (fun x : ℝ => x ^ 2) MeasureTheory.volume 0 1 :=
    (continuous_pow 2).intervalIntegrable 0 1
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have h14 : ∫ x in (0 : ℝ)..1, x ^ 14 = 1 / 15 := by
    rw [integral_pow]; norm_num
  have h13 : ∫ x in (0 : ℝ)..1, x ^ 13 = 1 / 14 := by
    rw [integral_pow]; norm_num
  have h12 : ∫ x in (0 : ℝ)..1, x ^ 12 = 1 / 13 := by
    rw [integral_pow]; norm_num
  have h11 : ∫ x in (0 : ℝ)..1, x ^ 11 = 1 / 12 := by
    rw [integral_pow]; norm_num
  have h10 : ∫ x in (0 : ℝ)..1, x ^ 10 = 1 / 11 := by
    rw [integral_pow]; norm_num
  have h9 : ∫ x in (0 : ℝ)..1, x ^ 9 = 1 / 10 := by
    rw [integral_pow]; norm_num
  have h8 : ∫ x in (0 : ℝ)..1, x ^ 8 = 1 / 9 := by
    rw [integral_pow]; norm_num
  have h7 : ∫ x in (0 : ℝ)..1, x ^ 7 = 1 / 8 := by
    rw [integral_pow]; norm_num
  have h6 : ∫ x in (0 : ℝ)..1, x ^ 6 = 1 / 7 := by
    rw [integral_pow]; norm_num
  have h5 : ∫ x in (0 : ℝ)..1, x ^ 5 = 1 / 6 := by
    rw [integral_pow]; norm_num
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
  -- The integrand is left-associative (15 terms = 14 binary ops).
  rw [intervalIntegral.integral_add
        ((((((((((((((hi_x14.const_mul 11778624).sub (hi_x13.const_mul 82450368)).add
              (hi_x12.const_mul 258450192)).sub (hi_x11.const_mul 478846368)).add
              (hi_x10.const_mul 582929424)).sub (hi_x9.const_mul 490289184)).add
              (hi_x8.const_mul 291657828)).sub (hi_x7.const_mul 123519792)).add
              (hi_x6.const_mul 36990408)).sub (hi_x5.const_mul 7677264)).add
              (hi_x4.const_mul 1065036)).sub (hi_x3.const_mul 93072)).add
              (hi_x2.const_mul 4648)).sub (hi_x.const_mul 112))
        intervalIntegrable_const,
      intervalIntegral.integral_sub
        (((((((((((((hi_x14.const_mul 11778624).sub (hi_x13.const_mul 82450368)).add
              (hi_x12.const_mul 258450192)).sub (hi_x11.const_mul 478846368)).add
              (hi_x10.const_mul 582929424)).sub (hi_x9.const_mul 490289184)).add
              (hi_x8.const_mul 291657828)).sub (hi_x7.const_mul 123519792)).add
              (hi_x6.const_mul 36990408)).sub (hi_x5.const_mul 7677264)).add
              (hi_x4.const_mul 1065036)).sub (hi_x3.const_mul 93072)).add
              (hi_x2.const_mul 4648))
        (hi_x.const_mul 112),
      intervalIntegral.integral_add
        ((((((((((((hi_x14.const_mul 11778624).sub (hi_x13.const_mul 82450368)).add
              (hi_x12.const_mul 258450192)).sub (hi_x11.const_mul 478846368)).add
              (hi_x10.const_mul 582929424)).sub (hi_x9.const_mul 490289184)).add
              (hi_x8.const_mul 291657828)).sub (hi_x7.const_mul 123519792)).add
              (hi_x6.const_mul 36990408)).sub (hi_x5.const_mul 7677264)).add
              (hi_x4.const_mul 1065036)).sub (hi_x3.const_mul 93072))
        (hi_x2.const_mul 4648),
      intervalIntegral.integral_sub
        (((((((((((hi_x14.const_mul 11778624).sub (hi_x13.const_mul 82450368)).add
              (hi_x12.const_mul 258450192)).sub (hi_x11.const_mul 478846368)).add
              (hi_x10.const_mul 582929424)).sub (hi_x9.const_mul 490289184)).add
              (hi_x8.const_mul 291657828)).sub (hi_x7.const_mul 123519792)).add
              (hi_x6.const_mul 36990408)).sub (hi_x5.const_mul 7677264)).add
              (hi_x4.const_mul 1065036))
        (hi_x3.const_mul 93072),
      intervalIntegral.integral_add
        ((((((((((hi_x14.const_mul 11778624).sub (hi_x13.const_mul 82450368)).add
              (hi_x12.const_mul 258450192)).sub (hi_x11.const_mul 478846368)).add
              (hi_x10.const_mul 582929424)).sub (hi_x9.const_mul 490289184)).add
              (hi_x8.const_mul 291657828)).sub (hi_x7.const_mul 123519792)).add
              (hi_x6.const_mul 36990408)).sub (hi_x5.const_mul 7677264))
        (hi_x4.const_mul 1065036),
      intervalIntegral.integral_sub
        (((((((((hi_x14.const_mul 11778624).sub (hi_x13.const_mul 82450368)).add
              (hi_x12.const_mul 258450192)).sub (hi_x11.const_mul 478846368)).add
              (hi_x10.const_mul 582929424)).sub (hi_x9.const_mul 490289184)).add
              (hi_x8.const_mul 291657828)).sub (hi_x7.const_mul 123519792)).add
              (hi_x6.const_mul 36990408))
        (hi_x5.const_mul 7677264),
      intervalIntegral.integral_add
        ((((((((hi_x14.const_mul 11778624).sub (hi_x13.const_mul 82450368)).add
              (hi_x12.const_mul 258450192)).sub (hi_x11.const_mul 478846368)).add
              (hi_x10.const_mul 582929424)).sub (hi_x9.const_mul 490289184)).add
              (hi_x8.const_mul 291657828)).sub (hi_x7.const_mul 123519792))
        (hi_x6.const_mul 36990408),
      intervalIntegral.integral_sub
        (((((((hi_x14.const_mul 11778624).sub (hi_x13.const_mul 82450368)).add
              (hi_x12.const_mul 258450192)).sub (hi_x11.const_mul 478846368)).add
              (hi_x10.const_mul 582929424)).sub (hi_x9.const_mul 490289184)).add
              (hi_x8.const_mul 291657828))
        (hi_x7.const_mul 123519792),
      intervalIntegral.integral_add
        ((((((hi_x14.const_mul 11778624).sub (hi_x13.const_mul 82450368)).add
              (hi_x12.const_mul 258450192)).sub (hi_x11.const_mul 478846368)).add
              (hi_x10.const_mul 582929424)).sub (hi_x9.const_mul 490289184))
        (hi_x8.const_mul 291657828),
      intervalIntegral.integral_sub
        (((((hi_x14.const_mul 11778624).sub (hi_x13.const_mul 82450368)).add
              (hi_x12.const_mul 258450192)).sub (hi_x11.const_mul 478846368)).add
              (hi_x10.const_mul 582929424))
        (hi_x9.const_mul 490289184),
      intervalIntegral.integral_add
        ((((hi_x14.const_mul 11778624).sub (hi_x13.const_mul 82450368)).add
              (hi_x12.const_mul 258450192)).sub (hi_x11.const_mul 478846368))
        (hi_x10.const_mul 582929424),
      intervalIntegral.integral_sub
        (((hi_x14.const_mul 11778624).sub (hi_x13.const_mul 82450368)).add
              (hi_x12.const_mul 258450192))
        (hi_x11.const_mul 478846368),
      intervalIntegral.integral_add
        ((hi_x14.const_mul 11778624).sub (hi_x13.const_mul 82450368))
        (hi_x12.const_mul 258450192),
      intervalIntegral.integral_sub
        (hi_x14.const_mul 11778624)
        (hi_x13.const_mul 82450368),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, integral_one]
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

-- (342d) at `n = 3`: matches the closed form `1 / (2 * 3 + 1) = 1/7`.
example : ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 3).eval x ^ 2
    = 1 / (2 * (3 : ℕ) + 1) := by
  rw [butcherShiftedLegendre_norm_sq_three]; norm_num

-- (342d) at `n = 4`: matches the closed form `1 / (2 * 4 + 1) = 1/9`.
example : ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 4).eval x ^ 2
    = 1 / (2 * (4 : ℕ) + 1) := by
  rw [butcherShiftedLegendre_norm_sq_four]; norm_num

-- (342d) at `n = 5`: matches the closed form `1 / (2 * 5 + 1) = 1/11`.
example : ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 5).eval x ^ 2
    = 1 / (2 * (5 : ℕ) + 1) := by
  rw [butcherShiftedLegendre_norm_sq_five]; norm_num

-- (342d) at `n = 6`: matches the closed form `1 / (2 * 6 + 1) = 1/13`.
example : ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 6).eval x ^ 2
    = 1 / (2 * (6 : ℕ) + 1) := by
  rw [butcherShiftedLegendre_norm_sq_six]; norm_num

-- (342d) at `n = 7`: matches the closed form `1 / (2 * 7 + 1) = 1/15`.
example : ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 7).eval x ^ 2
    = 1 / (2 * (7 : ℕ) + 1) := by
  rw [butcherShiftedLegendre_norm_sq_seven]; norm_num

/-! ### (342d) general — `∫₀¹ (P_n^*(x))^2 dx = 1 / (2n + 1)`

Aristotle (cycle 281, project `d4ce527b-b714-4e51-b0a6-e3d06302d7fa`)
returned a complete proof of the general norm-square identity. The
proof relies on three substantial helpers extracted to
`OpenMath.Chapter3.Section342NormSqHelpers`:

1. `iterate_derivative_natDegree_eq` — the `n`-th derivative of a
   degree-`n` polynomial is the constant `C (leadingCoeff · n!)`.
2. `iterated_ibp_XnOneSubXn` — iterated IBP `n` times against
   `X^n · (1-X)^n`, with all boundary terms vanishing thanks to the
   evaluation lemmas of cycle 277.
3. `integral_pow_mul_one_sub_pow` — the Beta integral
   `∫₀¹ x^n (1-x)^n dx = (n!)² / (2n+1)!`, derived from Mathlib's
   complex `Complex.betaIntegral_eval_nat_add_one_right`.

Combined with `butcherShiftedLegendre_rodrigues` (cycle 272) and
`butcherShiftedLegendre_natDegree` (cycle 272), these helpers complete
the textbook (342d) clause of `lem:342A`. -/

/-- Helper: the leading coefficient of `butcherShiftedLegendre n` is
`Nat.choose (2 * n) n`. The Mathlib coefficient formula
`(shiftedLegendre n).coeff n = (-1)^n · C(n,n) · C(2n, n)` combined
with the outer Butcher sign factor `(-1)^n` cancels to give `C(2n, n)`. -/
private lemma butcherShiftedLegendre_leadingCoeff (n : ℕ) :
    (butcherShiftedLegendre n).leadingCoeff = (Nat.choose (2 * n) n : ℝ) := by
  rw [Polynomial.leadingCoeff, butcherShiftedLegendre_natDegree]
  unfold butcherShiftedLegendre
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_map,
      Polynomial.coeff_shiftedLegendre]
  simp only [Int.coe_castRingHom, Nat.choose_self, Nat.cast_one, Int.cast_mul,
             Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, mul_one]
  rw [show (n + n : ℕ) = 2 * n from by ring]
  have hsq : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    rw [← pow_add, show n + n = 2 * n from by ring, pow_mul]
    norm_num
  nlinarith [hsq, sq_nonneg ((-1 : ℝ) ^ n)]

/-- Helper: `(d/dx)^n P_n^*(x) = C(2n, n) · n!` (a constant in `x`). -/
private lemma iterate_derivative_butcherShiftedLegendre_eval (n : ℕ) (x : ℝ) :
    (Polynomial.derivative^[n] (butcherShiftedLegendre n)).eval x =
      (Nat.choose (2 * n) n : ℝ) * (n.factorial : ℝ) := by
  rw [Section342Helpers.iterate_derivative_natDegree_eq
        (butcherShiftedLegendre_natDegree n)]
  simp [butcherShiftedLegendre_leadingCoeff]

/-- **Butcher §342 (342d)** — general norm-square identity.

For every `n`, `∫₀¹ (P_n^*(x))^2 dx = 1 / (2n + 1)`.

Proof (Aristotle, cycle 281 submission `d4ce527b`, integrated cycle 281):
substitute Rodrigues' formula `butcherShiftedLegendre_rodrigues` for one of
the two `P_n^*` factors, expressing it as `((-1)^n / n!) · D^n(X^n(1-X)^n)`.
Apply iterated integration by parts `n` times via
`Section342Helpers.iterated_ibp_XnOneSubXn`; boundary terms vanish at every
step (the helpers `iterDeriv_XnOneSubXn_eval_zero/_eval_one` from cycle 277
witness this). After all derivatives transfer to the other `P_n^*` factor,
the remaining `D^n P_n^*` is the constant `C(2n,n) · n!`
(`iterate_derivative_butcherShiftedLegendre_eval`). The leftover integral
is the Beta integral `∫₀¹ x^n (1-x)^n dx = (n!)² / (2n+1)!`
(`Section342Helpers.integral_pow_mul_one_sub_pow`); the final arithmetic
identity `C(2n,n) · (n!)² / (2n+1)! = 1/(2n+1)`
(`Section342Helpers.choose_mul_factorial_sq_div`) closes the goal. -/
theorem butcherShiftedLegendre_norm_sq (n : ℕ) :
    ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre n).eval x ^ 2 =
      1 / (2 * (n : ℝ) + 1) := by
  have hfact_pos : (0 : ℝ) < n.factorial :=
    Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hfact_ne : (n.factorial : ℝ) ≠ 0 := ne_of_gt hfact_pos
  -- Step 1: rewrite `^2` as `_ * _`.
  simp_rw [sq]
  -- Step 2: replace one factor of `P_n^*` via Rodrigues.
  have h_integrand : ∀ x : ℝ,
      (butcherShiftedLegendre n).eval x * (butcherShiftedLegendre n).eval x =
      (-1 : ℝ) ^ n / (n.factorial : ℝ) *
        ((butcherShiftedLegendre n).eval x *
          (Polynomial.derivative^[n]
            ((Polynomial.X : Polynomial ℝ) ^ n *
              (1 - Polynomial.X) ^ n)).eval x) := by
    intro x
    have hrod := congr_arg (Polynomial.eval x)
      (butcherShiftedLegendre_rodrigues n)
    simp only [Polynomial.eval_mul, Polynomial.eval_C] at hrod
    have h_subst : (butcherShiftedLegendre n).eval x =
        (-1 : ℝ) ^ n / (n.factorial : ℝ) *
          (Polynomial.derivative^[n]
            ((Polynomial.X : Polynomial ℝ) ^ n *
              (1 - Polynomial.X) ^ n)).eval x := by
      field_simp
      linarith
    rw [h_subst]; ring
  rw [intervalIntegral.integral_congr (fun x _ => h_integrand x),
      intervalIntegral.integral_const_mul]
  -- Step 3: iterated IBP transfers all `n` derivatives onto `P_n^*`.
  rw [Section342Helpers.iterated_ibp_XnOneSubXn (butcherShiftedLegendre n) n]
  -- Step 4: substitute `D^n P_n^* = C(2n,n) · n!` and simplify the
  -- `(X^n · (1-X)^n).eval x` factor to `x^n · (1-x)^n`.
  have h_xy : ∀ x : ℝ,
      ((Polynomial.X : Polynomial ℝ) ^ n * (1 - Polynomial.X) ^ n).eval x =
        x ^ n * (1 - x) ^ n := by
    intro x
    simp [Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
  simp_rw [iterate_derivative_butcherShiftedLegendre_eval, h_xy]
  -- Step 5: pull the constant `C(2n,n) · n!` out of the integral.
  have h_split : (fun x : ℝ => (Nat.choose (2 * n) n : ℝ) * (n.factorial : ℝ) *
        (x ^ n * (1 - x) ^ n)) =
      (fun x : ℝ => ((Nat.choose (2 * n) n : ℝ) * (n.factorial : ℝ)) *
        (x ^ n * (1 - x) ^ n)) := by
    ext x; ring
  rw [h_split, intervalIntegral.integral_const_mul]
  -- Step 6: evaluate the Beta integral.
  rw [Section342Helpers.integral_pow_mul_one_sub_pow]
  -- Step 7: simplify the `(-1)^n / n! · (-1)^n · …` prefactor to `C(2n,n) · (n!)² / (2n+1)!`.
  have h_2n1_ne : ((2 * n + 1).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h_neg_sq : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add, show n + n = 2 * n from by ring, pow_mul]; norm_num
  have h_collapse : (-1 : ℝ) ^ n / (n.factorial : ℝ) *
        ((-1 : ℝ) ^ n *
          ((Nat.choose (2 * n) n : ℝ) * (n.factorial : ℝ) *
            ((n.factorial : ℝ) ^ 2 / ((2 * n + 1).factorial : ℝ)))) =
      (Nat.choose (2 * n) n : ℝ) *
        ((n.factorial : ℝ) ^ 2 / ((2 * n + 1).factorial : ℝ)) := by
    field_simp
    nlinarith [h_neg_sq]
  rw [h_collapse]
  -- Step 8: close via the arithmetic identity.
  rw [Section342Helpers.choose_mul_factorial_sq_div]

/-! ### (342f) recurrence — concrete sanity-check witnesses at `n ∈ {2, 3, 4}`

Butcher §342 (342f) asserts the Bonnet-style three-term recurrence
`n · P_n^*(x) = (2x - 1)(2n - 1) · P_{n−1}^*(x) − (n − 1) · P_{n−2}^*(x)`
for `n = 2, 3, 4, …`. The general statement requires substantive
parity/degree reasoning (currently submitted to Aristotle in cycle 282).
The three witnesses below verify the formula at the smallest cases
`n ∈ {2, 3, 4}` by direct polynomial computation against cycles
273–275's explicit forms `_zero` through `_four`. They serve as
regression sanity-checks for the recurrence form (ruling out
sign/coefficient errors) and compose with the general theorem once
it ships. -/

/-- **Butcher §342 (342f) at `n = 2`**:
`2 · P_2^*(x) = 3 · (2x − 1) · P_1^*(x) − 1 · P_0^*(x)`.

The smallest non-trivial instance of (342f). Direct verification:
LHS = `2(6x² − 6x + 1) = 12x² − 12x + 2`;
RHS = `3(2x − 1)² − 1 = 12x² − 12x + 2`. Proved by `Polynomial.funext`
+ explicit-form substitution + `ring` (cycle 180's recipe for
explicit-polynomial-arithmetic identities). -/
theorem butcherShiftedLegendre_recurrence_two :
    (2 : ℝ) • butcherShiftedLegendre 2 =
      Polynomial.C 3 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 1
      - Polynomial.C 1 * butcherShiftedLegendre 0 := by
  apply Polynomial.funext
  intro x
  rw [butcherShiftedLegendre_two, butcherShiftedLegendre_one,
      butcherShiftedLegendre_zero]
  simp [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
  ring

/-- **Butcher §342 (342f) at `n = 3`**:
`3 · P_3^*(x) = 5 · (2x − 1) · P_2^*(x) − 2 · P_1^*(x)`.

Direct verification:
LHS = `3(20x³ − 30x² + 12x − 1) = 60x³ − 90x² + 36x − 3`;
RHS = `5(2x − 1)(6x² − 6x + 1) − 2(2x − 1) = 60x³ − 90x² + 36x − 3`.
Same `Polynomial.funext` + `ring` recipe. -/
theorem butcherShiftedLegendre_recurrence_three :
    (3 : ℝ) • butcherShiftedLegendre 3 =
      Polynomial.C 5 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 2
      - Polynomial.C 2 * butcherShiftedLegendre 1 := by
  apply Polynomial.funext
  intro x
  rw [butcherShiftedLegendre_three, butcherShiftedLegendre_two,
      butcherShiftedLegendre_one]
  simp [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
  ring

/-- **Butcher §342 (342f) at `n = 4`**:
`4 · P_4^*(x) = 7 · (2x − 1) · P_3^*(x) − 3 · P_2^*(x)`.

Direct verification:
LHS = `4(70x⁴ − 140x³ + 90x² − 20x + 1) = 280x⁴ − 560x³ + 360x² − 80x + 4`;
RHS = `7(2x − 1)(20x³ − 30x² + 12x − 1) − 3(6x² − 6x + 1) = 280x⁴ − 560x³ + 360x² − 80x + 4`.
Same `Polynomial.funext` + `ring` recipe. -/
theorem butcherShiftedLegendre_recurrence_four :
    (4 : ℝ) • butcherShiftedLegendre 4 =
      Polynomial.C 7 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 3
      - Polynomial.C 3 * butcherShiftedLegendre 2 := by
  apply Polynomial.funext
  intro x
  rw [butcherShiftedLegendre_four, butcherShiftedLegendre_three,
      butcherShiftedLegendre_two]
  simp [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
  ring

/-- **Butcher §342 (342f) at `n = 5`**:
`5 · P_5^*(x) = 9 · (2x − 1) · P_4^*(x) − 4 · P_3^*(x)`.

Direct verification:
LHS = `5 · (252x⁵ − 630x⁴ + 560x³ − 210x² + 30x − 1)
     = 1260x⁵ − 3150x⁴ + 2800x³ − 1050x² + 150x − 5`;
RHS = `9 · (2x − 1) · (70x⁴ − 140x³ + 90x² − 20x + 1)
     − 4 · (20x³ − 30x² + 12x − 1)
     = 1260x⁵ − 3150x⁴ + 2800x³ − 1050x² + 150x − 5`.
Same `Polynomial.funext` + `ring` recipe. -/
theorem butcherShiftedLegendre_recurrence_five :
    (5 : ℝ) • butcherShiftedLegendre 5 =
      Polynomial.C 9 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 4
      - Polynomial.C 4 * butcherShiftedLegendre 3 := by
  apply Polynomial.funext
  intro x
  rw [butcherShiftedLegendre_five, butcherShiftedLegendre_four,
      butcherShiftedLegendre_three]
  simp [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
  ring

/-- **Butcher §342 (342f) at `n = 6`**:
`6 · P_6^*(x) = 11 · (2x − 1) · P_5^*(x) − 5 · P_4^*(x)`.

Direct verification:
LHS = `6 · (924x⁶ − 2772x⁵ + 3150x⁴ − 1680x³ + 420x² − 42x + 1)
     = 5544x⁶ − 16632x⁵ + 18900x⁴ − 10080x³ + 2520x² − 252x + 6`;
RHS = `11 · (2x − 1) · (252x⁵ − 630x⁴ + 560x³ − 210x² + 30x − 1)
     − 5 · (70x⁴ − 140x³ + 90x² − 20x + 1)
     = 5544x⁶ − 16632x⁵ + 18900x⁴ − 10080x³ + 2520x² − 252x + 6`.
Same `Polynomial.funext` + `ring` recipe. -/
theorem butcherShiftedLegendre_recurrence_six :
    (6 : ℝ) • butcherShiftedLegendre 6 =
      Polynomial.C 11 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 5
      - Polynomial.C 5 * butcherShiftedLegendre 4 := by
  apply Polynomial.funext
  intro x
  rw [butcherShiftedLegendre_six, butcherShiftedLegendre_five,
      butcherShiftedLegendre_four]
  simp [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
  ring

/-- **Butcher §342 (342f) at `n = 7`**:
`7 · P_7^*(x) = 13 · (2x − 1) · P_6^*(x) − 6 · P_5^*(x)`.

Direct verification:
LHS = `7 · (3432x⁷ − 12012x⁶ + 16632x⁵ − 11550x⁴ + 4200x³ − 756x² + 56x − 1)
     = 24024x⁷ − 84084x⁶ + 116424x⁵ − 80850x⁴ + 29400x³ − 5292x² + 392x − 7`;
RHS = `13 · (2x − 1) · (924x⁶ − 2772x⁵ + 3150x⁴ − 1680x³ + 420x² − 42x + 1)
     − 6 · (252x⁵ − 630x⁴ + 560x³ − 210x² + 30x − 1)
     = 24024x⁷ − 84084x⁶ + 116424x⁵ − 80850x⁴ + 29400x³ − 5292x² + 392x − 7`.
Same `Polynomial.funext` + `ring` recipe. -/
theorem butcherShiftedLegendre_recurrence_seven :
    (7 : ℝ) • butcherShiftedLegendre 7 =
      Polynomial.C 13 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 6
      - Polynomial.C 6 * butcherShiftedLegendre 5 := by
  apply Polynomial.funext
  intro x
  rw [butcherShiftedLegendre_seven, butcherShiftedLegendre_six,
      butcherShiftedLegendre_five]
  simp [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
  ring

/-- **Butcher §342 (342f) at `n = 8`**:
`8 · P_8^*(x) = 15 · (2x − 1) · P_7^*(x) − 7 · P_6^*(x)`.

Direct verification:
LHS = `8 · (12870x⁸ − 51480x⁷ + 84084x⁶ − 72072x⁵ + 34650x⁴ − 9240x³ + 1260x²
     − 72x + 1) = 102960x⁸ − 411840x⁷ + 672672x⁶ − 576576x⁵ + 277200x⁴
     − 73920x³ + 10080x² − 576x + 8`;
RHS = `15 · (2x − 1) · (3432x⁷ − 12012x⁶ + 16632x⁵ − 11550x⁴ + 4200x³ − 756x²
     + 56x − 1) − 7 · (924x⁶ − 2772x⁵ + 3150x⁴ − 1680x³ + 420x² − 42x + 1)
     = 102960x⁸ − 411840x⁷ + 672672x⁶ − 576576x⁵ + 277200x⁴ − 73920x³
     + 10080x² − 576x + 8`.
Same `Polynomial.funext` + `ring` recipe. -/
theorem butcherShiftedLegendre_recurrence_eight :
    (8 : ℝ) • butcherShiftedLegendre 8 =
      Polynomial.C 15 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 7
      - Polynomial.C 7 * butcherShiftedLegendre 6 := by
  apply Polynomial.funext
  intro x
  rw [butcherShiftedLegendre_eight, butcherShiftedLegendre_seven,
      butcherShiftedLegendre_six]
  simp [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
  ring

/-- **Butcher §342 (342f) at `n = 9`**:
`9 · P_9^*(x) = 17 · (2x − 1) · P_8^*(x) − 8 · P_7^*(x)`.

Direct verification (coefficients in descending degree, paper-verified
via Python integer arithmetic in cycle 285):
LHS = `9 · P_9^*` has coefficients
  `[437580, −1969110, 3706560, −3783780, 2270268, −810810, 166320, −17820, 810, −9]`;
RHS = `17 · (2X − 1) · P_8^* − 8 · P_7^*` produces the same vector,
  confirming `(2n − 1, n − 1) = (17, 8)` at `n = 9`.
Same `Polynomial.funext` + `ring` recipe as cycles 282–284. -/
theorem butcherShiftedLegendre_recurrence_nine :
    (9 : ℝ) • butcherShiftedLegendre 9 =
      Polynomial.C 17 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 8
      - Polynomial.C 8 * butcherShiftedLegendre 7 := by
  apply Polynomial.funext
  intro x
  rw [butcherShiftedLegendre_nine, butcherShiftedLegendre_eight,
      butcherShiftedLegendre_seven]
  simp [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
  ring

/-- **Butcher §342 (342f) at `n = 10`**:
`10 · P_10^*(x) = 19 · (2x − 1) · P_9^*(x) − 9 · P_8^*(x)`.

Direct verification (coefficients in descending degree, paper-verified
via Python integer arithmetic in cycle 286):
LHS = `10 · P_10^*` has coefficients
  `[1847560, −9237800, 19691100, −23337600, 16816800, −7567560, 2102100,
   −343200, 29700, −1100, 10]`;
RHS = `19 · (2X − 1) · P_9^* − 9 · P_8^*` produces the same vector,
  confirming `(2n − 1, n − 1) = (19, 9)` at `n = 10`.
Same `Polynomial.funext` + `ring` recipe as cycles 282–285. -/
theorem butcherShiftedLegendre_recurrence_ten :
    (10 : ℝ) • butcherShiftedLegendre 10 =
      Polynomial.C 19 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 9
      - Polynomial.C 9 * butcherShiftedLegendre 8 := by
  apply Polynomial.funext
  intro x
  rw [butcherShiftedLegendre_ten, butcherShiftedLegendre_nine,
      butcherShiftedLegendre_eight]
  simp [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
  ring

/-- **Butcher §342 (342f) at `n = 11`**:
`11 · P_11^*(x) = 21 · (2x − 1) · P_10^*(x) − 10 · P_9^*(x)`.

Direct verification (coefficients in ascending degree, paper-verified
via Python integer arithmetic in cycle 288):
LHS = `11 · P_11^*` has coefficients
  `[−11, 1452, −47190, 660660, −4954950, 22198176, −62894832, 115521120,
   −137181330, 101615800, −42678636, 7759752]`;
RHS = `21 · (2X − 1) · P_10^* − 10 · P_9^*` produces the same vector,
  confirming `(2n − 1, n − 1) = (21, 10)` at `n = 11`.
Same `Polynomial.funext` + `ring` recipe as cycles 282–286.
Eleventh rung of the empirical recurrence ladder. -/
theorem butcherShiftedLegendre_recurrence_eleven :
    (11 : ℝ) • butcherShiftedLegendre 11 =
      Polynomial.C 21 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 10
      - Polynomial.C 10 * butcherShiftedLegendre 9 := by
  apply Polynomial.funext
  intro x
  rw [butcherShiftedLegendre_eleven, butcherShiftedLegendre_ten,
      butcherShiftedLegendre_nine]
  simp [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
  ring

/-! ### (342f) general recurrence — Phase A.1: residual has `natDegree < n`

Per `.prover-state/issues/lem_342A_342f_manual_closure_plan.md` (opened
cycle 289 after Aristotle project `efe4940e` cancelled at the third
consecutive 20% stall), the manual closure of the general (342f)
three-term recurrence proceeds in three phases:

* **Phase A.1** (cycle 289+): residual `Q := n·P_n^* − (2n−1)·(2X−1)·P_{n−1}^*
  + (n−1)·P_{n−2}^*` satisfies `Q.natDegree < n` via the binomial
  leading-coefficient identity `n·C(2n,n) = 2(2n−1)·C(2n−2,n−1)`.
* **Phase A.2** (cycle 291): `⟨Q, P_k^*⟩ = 0` for `k ≤ n − 2` via
  (342a)/(342d) orthogonality on each summand.
* **Phase A.3** (cycle 292): conclude `Q = 0` from A.1 + A.2 via the
  polynomial-basis spanning argument on `Polynomial.degreeLT ℝ n`.

This block ships Phase A.1.
-/

/-- **Phase A.1 binomial helper** (cycle 289): the leading-coefficient
identity behind (342f). For every `n ≥ 2`,
`n · C(2n, n) = 2 · (2n − 1) · C(2n − 2, n − 1)`.

Paper proof: both sides equal `(2n)! / (n! · (n − 1)!)`. Lean route:
- `Nat.choose_mul_right` gives `C(2n, n) = 2 · C(2n − 1, n − 1)`.
- `Nat.choose_eq_choose_pred_add` (Pascal) gives
  `C(2n − 1, n − 1) = C(2n − 2, n − 2) + C(2n − 2, n − 1)`.
- `Nat.choose_succ_right_eq` at `(2n − 2, n − 2)` gives
  `C(2n − 2, n − 1) · (n − 1) = C(2n − 2, n − 2) · n`.
Composing, `n · C(2n, n) = 2n · (C(2n−2,n−2) + C(2n−2,n−1))
  = 2(n − 1) · C(2n − 2, n − 1) + 2n · C(2n − 2, n − 1)
  = (4n − 2) · C(2n − 2, n − 1) = 2(2n − 1) · C(2n − 2, n − 1)`. -/
private lemma n_mul_choose_two_n_n_eq (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * (Nat.choose (2 * n) n : ℝ)
      = 2 * ((2 * n - 1 : ℕ) : ℝ) * (Nat.choose (2 * n - 2) (n - 1) : ℝ) := by
  set C1 := (Nat.choose (2 * n - 2) (n - 1) : ℝ) with hC1_def
  set C2 := (Nat.choose (2 * n - 2) (n - 2) : ℝ) with hC2_def
  -- step1 over ℕ, then cast.
  have step1_nat : Nat.choose (2 * n) n = 2 * Nat.choose (2 * n - 1) (n - 1) :=
    Nat.choose_mul_right (m := 2) (n := n) (by omega)
  have step1 : ((Nat.choose (2 * n) n : ℕ) : ℝ)
      = 2 * ((Nat.choose (2 * n - 1) (n - 1) : ℕ) : ℝ) := by
    exact_mod_cast step1_nat
  -- step3 (Pascal) over ℕ, then cast.
  have step3_nat : Nat.choose (2 * n - 1) (n - 1)
      = Nat.choose (2 * n - 2) (n - 2) + Nat.choose (2 * n - 2) (n - 1) := by
    have h := Nat.choose_eq_choose_pred_add
      (n := 2 * n - 1) (k := n - 1) (by omega) (by omega)
    rw [show ((2 * n - 1) - 1 : ℕ) = 2 * n - 2 from by omega,
        show ((n - 1) - 1 : ℕ) = n - 2 from by omega] at h
    exact h
  have step3 : ((Nat.choose (2 * n - 1) (n - 1) : ℕ) : ℝ) = C2 + C1 := by
    have := congrArg (Nat.cast (R := ℝ)) step3_nat
    push_cast at this
    -- this : C(2n-1,n-1) = C(2n-2,n-2) + C(2n-2,n-1)  (all cast to ℝ)
    -- The RHS matches C2 + C1 by definition.
    exact this
  -- step2 (Bonnet-style choose identity): C(2n-2,n-1) · (n-1) = C(2n-2,n-2) · n
  have step2_nat : Nat.choose (2 * n - 2) (n - 1) * (n - 1)
      = Nat.choose (2 * n - 2) (n - 2) * n := by
    have h := Nat.choose_succ_right_eq (2 * n - 2) (n - 2)
    rw [show ((n - 2) + 1 : ℕ) = n - 1 from by omega,
        show ((2 * n - 2) - (n - 2) : ℕ) = n from by omega] at h
    exact h
  have step2 : C1 * ((n - 1 : ℕ) : ℝ) = C2 * (n : ℝ) := by
    have := congrArg (Nat.cast (R := ℝ)) step2_nat
    push_cast at this
    exact this
  -- Convert nat-subtractions inside `((... : ℕ) : ℝ)` to real subtractions.
  have h_2n_minus_1_real : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    push_cast
    ring
  have h_n_minus_1_real : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  -- Rewrite step2 in terms of real subtraction.
  rw [h_n_minus_1_real] at step2
  -- Rewrite the goal: substitute the chain step1 ↦ step3 and convert (2n - 1).
  rw [step1, step3, h_2n_minus_1_real]
  -- Goal: (n : ℝ) * (2 * (C2 + C1)) = 2 * (2 * (n : ℝ) - 1) * C1.
  -- Use step2 : C1 * ((n : ℝ) - 1) = C2 * (n : ℝ).
  linear_combination (-2 : ℝ) * step2

/-- **Phase A.1 (b)** (cycle 290): the (342f) residual polynomial
`Q := n·P_n^* − (2n−1)·(2X−1)·P_{n−1}^* + (n−1)·P_{n−2}^*` has
`natDegree < n`.

Paper proof (Butcher §342 p. 236):
- `A := (n : ℝ) • P_n^*` has `natDegree = n` and leading coefficient
  `n · C(2n, n)`.
- `B := (2n−1) · (2X − 1) · P_{n−1}^*` has `natDegree = 1 + (n−1) = n`
  and leading coefficient `(2n−1) · 2 · C(2(n−1), n−1)`.
- By the cycle 289 binomial identity `n · C(2n, n) = 2(2n−1) · C(2n−2,
  n−1)`, `A.leadingCoeff = B.leadingCoeff`, so `Polynomial.degree_sub_lt`
  gives `(A − B).degree < n`.
- `Cterm := (n−1) · P_{n−2}^*` has `natDegree ≤ n − 2 < n`.
- Combining via `Polynomial.natDegree_add_le` + `Nat.max_lt`. -/
theorem recurrence_residual_natDegree_lt (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℝ) • butcherShiftedLegendre n
      - Polynomial.C ((2 * n - 1 : ℕ) : ℝ)
        * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre (n - 1)
      + Polynomial.C ((n - 1 : ℕ) : ℝ)
        * butcherShiftedLegendre (n - 2)).natDegree < n := by
  -- Basic numeric facts from `hn : 2 ≤ n`.
  have hn_pos : 0 < n := by omega
  have hn_ne_nat : n ≠ 0 := by omega
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn_ne_nat
  have hβ_nat_pos : 0 < 2 * n - 1 := by omega
  have hβ_real : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring
  have hβ_ne : ((2 * n - 1 : ℕ) : ℝ) ≠ 0 := by
    rw [hβ_real]
    have h : (1 : ℝ) ≤ 2 * (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ 2 * (n : ℝ) := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      linarith
    linarith
  -- Convert smul to C-mul, leaving the goal in a uniform C-mul form.
  rw [Polynomial.smul_eq_C_mul]
  -- Aliases for readability.
  set L : Polynomial ℝ :=
    Polynomial.C 2 * Polynomial.X - Polynomial.C 1 with hL_def
  set A : Polynomial ℝ :=
    Polynomial.C (n : ℝ) * butcherShiftedLegendre n with hA_def
  set B : Polynomial ℝ :=
    Polynomial.C ((2 * n - 1 : ℕ) : ℝ) * L * butcherShiftedLegendre (n - 1)
    with hB_def
  set Cterm : Polynomial ℝ :=
    Polynomial.C ((n - 1 : ℕ) : ℝ) * butcherShiftedLegendre (n - 2)
    with hCterm_def
  -- Goal: (A - B + Cterm).natDegree < n.
  -- Non-vanishing of the three shifted-Legendre factors.
  have hPn_ne : butcherShiftedLegendre n ≠ 0 := by
    intro h
    have hd := butcherShiftedLegendre_natDegree n
    rw [h] at hd; simp at hd; omega
  have hPnm1_ne : butcherShiftedLegendre (n - 1) ≠ 0 := by
    intro h
    have hd := butcherShiftedLegendre_natDegree (n - 1)
    rw [h] at hd; simp at hd; omega
  -- Step 1: L = C 2 * X - C 1 has natDegree 1 and leadingCoeff 2.
  have hL_nd : L.natDegree = 1 := by
    rw [hL_def]; compute_degree!
  have hL_lc : L.leadingCoeff = 2 := by
    rw [Polynomial.leadingCoeff, hL_nd, hL_def, Polynomial.coeff_sub,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_one, Polynomial.coeff_C]
    norm_num
  have hL_ne : L ≠ 0 := by
    intro h; rw [h, Polynomial.leadingCoeff_zero] at hL_lc; norm_num at hL_lc
  -- Step 2: B = (C β * L) * P_{n-1}. Compute natDegree and leadingCoeff.
  have hβL_nd : (Polynomial.C ((2 * n - 1 : ℕ) : ℝ) * L).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul hβ_ne, hL_nd]
  have hβL_ne : Polynomial.C ((2 * n - 1 : ℕ) : ℝ) * L ≠ 0 := by
    intro h
    have hd : (Polynomial.C ((2 * n - 1 : ℕ) : ℝ) * L).natDegree = 1 := hβL_nd
    rw [h] at hd; simp at hd
  have hB_nd : B.natDegree = n := by
    rw [hB_def, Polynomial.natDegree_mul hβL_ne hPnm1_ne, hβL_nd,
        butcherShiftedLegendre_natDegree (n - 1)]
    omega
  have hβL_lc :
      (Polynomial.C ((2 * n - 1 : ℕ) : ℝ) * L).leadingCoeff
        = ((2 * n - 1 : ℕ) : ℝ) * 2 := by
    rw [Polynomial.leadingCoeff_C_mul_of_isUnit
          (isUnit_iff_ne_zero.mpr hβ_ne), hL_lc]
  have hB_lc :
      B.leadingCoeff
        = ((2 * n - 1 : ℕ) : ℝ) * 2 * (Nat.choose (2 * (n - 1)) (n - 1) : ℝ) := by
    rw [hB_def, Polynomial.leadingCoeff_mul, hβL_lc,
        butcherShiftedLegendre_leadingCoeff (n - 1)]
  -- Step 3: A.natDegree = n, A.leadingCoeff = n * C(2n, n).
  have hA_nd : A.natDegree = n := by
    rw [hA_def, Polynomial.natDegree_C_mul hn_ne]
    exact butcherShiftedLegendre_natDegree n
  have hA_lc : A.leadingCoeff = (n : ℝ) * (Nat.choose (2 * n) n : ℝ) := by
    rw [hA_def, Polynomial.leadingCoeff_C_mul_of_isUnit
          (isUnit_iff_ne_zero.mpr hn_ne),
        butcherShiftedLegendre_leadingCoeff n]
  -- Step 4: Bridge `n - 1` in C(2(n-1), n-1) ↔ C(2n - 2, n - 1) for the helper.
  have h2nm2_eq : 2 * (n - 1) = 2 * n - 2 := by omega
  have hB_lc' :
      B.leadingCoeff
        = ((2 * n - 1 : ℕ) : ℝ) * 2 * (Nat.choose (2 * n - 2) (n - 1) : ℝ) := by
    rw [hB_lc, h2nm2_eq]
  -- Step 5: A.leadingCoeff = B.leadingCoeff via cycle 289 helper.
  have hAB_lc : A.leadingCoeff = B.leadingCoeff := by
    rw [hA_lc, hB_lc']
    have := n_mul_choose_two_n_n_eq n hn
    linarith [this]
  -- Step 6: A.degree = B.degree (both = n, computed via natDegree).
  have hA_ne : A ≠ 0 := by
    intro h
    have hd : A.natDegree = n := hA_nd
    rw [h] at hd; simp at hd; omega
  have hB_ne : B ≠ 0 := by
    intro h
    have hd : B.natDegree = n := hB_nd
    rw [h] at hd; simp at hd; omega
  have hA_deg : A.degree = (n : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hA_ne, hA_nd]
  have hB_deg : B.degree = (n : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hB_ne, hB_nd]
  -- Step 7: (A - B).degree < n via Polynomial.degree_sub_lt.
  have hAB_deg : (A - B).degree < (n : WithBot ℕ) := by
    have h := Polynomial.degree_sub_lt (hA_deg.trans hB_deg.symm) hA_ne hAB_lc
    rw [hA_deg] at h
    exact h
  have hAB_nd : (A - B).natDegree < n := by
    by_cases h : A - B = 0
    · simp [h]; omega
    · exact (Polynomial.natDegree_lt_iff_degree_lt h).mpr hAB_deg
  -- Step 8: Cterm.natDegree ≤ n - 2 < n.
  have hCterm_nd_le : Cterm.natDegree ≤ n - 2 := by
    rw [hCterm_def]
    calc (Polynomial.C ((n - 1 : ℕ) : ℝ) * butcherShiftedLegendre (n - 2)).natDegree
        ≤ (butcherShiftedLegendre (n - 2)).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
      _ = n - 2 := butcherShiftedLegendre_natDegree (n - 2)
  have hCterm_nd : Cterm.natDegree < n := lt_of_le_of_lt hCterm_nd_le (by omega)
  -- Step 9: Combine via Polynomial.natDegree_add_le.
  calc (A - B + Cterm).natDegree
      ≤ max (A - B).natDegree Cterm.natDegree :=
        Polynomial.natDegree_add_le _ _
    _ < n := by
        rw [Nat.max_lt]
        exact ⟨hAB_nd, hCterm_nd⟩

/-! ### Phase A.2 starter lemmas — orthogonality of easy summands

Cycle 291 ships the two easy components (F.1 and F.2) of Phase A.2 for
the (342f) manual closure plan. Each reduces to (342a) orthogonality
(`butcherShiftedLegendre_orthogonal`, cycle 277) via a constant
pull-out through `intervalIntegral.integral_const_mul`. The hard
cross-term `⟨(2n - 1) · (2X - 1) · P_{n-1}^*, P_k^*⟩ = 0` (F.3) is
deferred to a later cycle since it requires the basis expansion of
`P_1^* · P_{n-1}^*`. -/

/-- **Phase A.2 (F.1) — orthogonality of `(n : ℝ) • P_n^*` against
`P_k^*` for `k < n`.** Direct from cycle 277's
`butcherShiftedLegendre_orthogonal` via scalar pull-out. The first
summand of the cycle 290 recurrence residual is orthogonal to `P_k^*`
for every `k < n`. -/
theorem recurrence_residual_orthogonal_first_term (n : ℕ)
    {k : ℕ} (hk : k < n) :
    ∫ x in (0 : ℝ)..1, ((n : ℝ) • butcherShiftedLegendre n).eval x *
                       (butcherShiftedLegendre k).eval x = 0 := by
  simp only [Polynomial.eval_smul, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul,
      butcherShiftedLegendre_orthogonal hk.ne', mul_zero]

/-- **Phase A.2 (F.2) — orthogonality of `C((n - 1 : ℕ) : ℝ) · P_{n-2}^*`
against `P_k^*` for `k ≤ n - 3`.** Direct from cycle 277's
`butcherShiftedLegendre_orthogonal` since `k ≤ n - 3 < n - 2`, so
`n - 2 ≠ k`. Constant pull-out via `Polynomial.eval_mul`,
`Polynomial.eval_C`, and `intervalIntegral.integral_const_mul`. The
third summand of the cycle 290 recurrence residual is orthogonal to
`P_k^*` for every `k ≤ n - 3`. -/
theorem recurrence_residual_orthogonal_third_term (n : ℕ) (hn : 3 ≤ n)
    {k : ℕ} (hk : k ≤ n - 3) :
    ∫ x in (0 : ℝ)..1, (Polynomial.C ((n - 1 : ℕ) : ℝ) *
                       butcherShiftedLegendre (n - 2)).eval x *
                       (butcherShiftedLegendre k).eval x = 0 := by
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  have h_ne : n - 2 ≠ k := by omega
  rw [butcherShiftedLegendre_orthogonal h_ne, mul_zero]

/-- **Partial Phase A.2** — combined orthogonality of the first and
third summands of the cycle 290 recurrence residual against `P_k^*`
for `k ≤ n - 3`. The second summand (cross-term involving
`(2X - 1) · P_{n-1}^*`) is deferred to a separate cycle since it
requires basis expansion via `2X - 1 = butcherShiftedLegendre 1`. -/
theorem recurrence_residual_orthogonal_easy (n : ℕ) (hn : 3 ≤ n)
    {k : ℕ} (hk : k ≤ n - 3) :
    ∫ x in (0 : ℝ)..1, (((n : ℝ) • butcherShiftedLegendre n +
                         Polynomial.C ((n - 1 : ℕ) : ℝ) *
                         butcherShiftedLegendre (n - 2)).eval x) *
                       (butcherShiftedLegendre k).eval x = 0 := by
  have hk_lt : k < n := by omega
  have hf_int : IntervalIntegrable
      (fun x : ℝ => ((n : ℝ) • butcherShiftedLegendre n).eval x *
                    (butcherShiftedLegendre k).eval x)
      MeasureTheory.volume 0 1 :=
    (((((n : ℝ) • butcherShiftedLegendre n)).continuous.mul
      (butcherShiftedLegendre k).continuous).intervalIntegrable _ _)
  have hg_int : IntervalIntegrable
      (fun x : ℝ => (Polynomial.C ((n - 1 : ℕ) : ℝ) *
                     butcherShiftedLegendre (n - 2)).eval x *
                    (butcherShiftedLegendre k).eval x)
      MeasureTheory.volume 0 1 :=
    (((Polynomial.C ((n - 1 : ℕ) : ℝ) *
        butcherShiftedLegendre (n - 2)).continuous.mul
      (butcherShiftedLegendre k).continuous).intervalIntegrable _ _)
  simp only [Polynomial.eval_add, add_mul]
  rw [intervalIntegral.integral_add hf_int hg_int,
      recurrence_residual_orthogonal_first_term n hk_lt,
      recurrence_residual_orthogonal_third_term n hn hk, add_zero]

/-! ### Phase A.2 P1 — basis-span orthogonality helper

Cycle 292 ships the reusable orthogonality lemma against **any**
polynomial of natDegree strictly less than `m`. This is the key
ingredient for the cycle 292 F.3 cross-term and for the cycle 293+
Phase A.3 basis-spanning conclusion. The proof is by induction on a
degree bound `d ≥ q.natDegree`, reducing each step to (342a)
(`butcherShiftedLegendre_orthogonal`, cycle 277). At each inductive
step we subtract a scalar multiple of `P_d^*` (where `d = q.natDegree`)
to drop the residual's degree by one; the IH then closes the residual. -/

/-- **Phase A.2 (P1) — basis-span helper for `P_m^*` orthogonality.**

For every polynomial `q` with `q.natDegree < m`, the inner product
`∫₀¹ P_m^*(x) · q(x) dx = 0`. Equivalently, `P_m^*` is orthogonal to
every element of `Polynomial.degreeLT ℝ m`.

The proof is by induction on a bound `d` with `q.natDegree ≤ d < m`:
* Base case `d = 0`: `q` is constant, integrand pulls the scalar out,
  remaining `∫ P_m^* = ∫ P_m^* · P_0^* = 0` via (342a).
* Inductive step `d → d + 1`: cases on `q.natDegree ≤ d` (apply IH) or
  `q.natDegree = d + 1` (subtract `c · P_{d+1}^*` to drop the leading
  term, apply IH to the residual, and use (342a) on the subtracted
  term since `d + 1 < m`).

The leading-coefficient bookkeeping uses cycle 281's
`butcherShiftedLegendre_leadingCoeff` and standard polynomial
degree API (`Polynomial.degree_sub_lt`,
`Polynomial.natDegree_C_mul`, `Polynomial.leadingCoeff_mul`). -/
theorem butcherShiftedLegendre_orthogonal_to_lower_degree
    (m : ℕ) (q : Polynomial ℝ) (hq : q.natDegree < m) :
    ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre m).eval x * q.eval x = 0 := by
  -- Reduce to an induction-friendly form indexed by a bound `d`.
  suffices h : ∀ d : ℕ, d < m → ∀ q : Polynomial ℝ, q.natDegree ≤ d →
      ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre m).eval x * q.eval x = 0 from
    h q.natDegree hq q le_rfl
  intro d
  induction d with
  | zero =>
      intro hm q hq
      have hq_nd : q.natDegree = 0 := Nat.le_zero.mp hq
      have hq_eq : q = Polynomial.C (q.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hq_nd
      rw [hq_eq]
      simp only [Polynomial.eval_C]
      simp_rw [mul_comm _ (q.coeff 0)]
      rw [intervalIntegral.integral_const_mul]
      have h_orth : ∫ x in (0 : ℝ)..1,
          (butcherShiftedLegendre m).eval x * (butcherShiftedLegendre 0).eval x = 0 :=
        butcherShiftedLegendre_orthogonal hm.ne'
      rw [butcherShiftedLegendre_zero] at h_orth
      simp only [Polynomial.eval_C, mul_one] at h_orth
      rw [h_orth, mul_zero]
  | succ d ih =>
      intro hm q hq
      by_cases hq_lt : q.natDegree ≤ d
      · exact ih (Nat.lt_of_succ_lt hm) q hq_lt
      · push_neg at hq_lt
        have heq : q.natDegree = d + 1 := Nat.le_antisymm hq hq_lt
        have hq_ne : q ≠ 0 := by
          intro h
          rw [h] at heq
          simp at heq
        have hq_lc : q.leadingCoeff = q.coeff (d + 1) := by
          rw [Polynomial.leadingCoeff, heq]
        have hq_coeff_ne : q.coeff (d + 1) ≠ 0 := by
          rw [← hq_lc]
          exact Polynomial.leadingCoeff_ne_zero.mpr hq_ne
        have hPdp1_lc : (butcherShiftedLegendre (d + 1)).leadingCoeff =
                         (Nat.choose (2 * (d + 1)) (d + 1) : ℝ) :=
          butcherShiftedLegendre_leadingCoeff (d + 1)
        have hPdp1_lc_pos : (0 : ℝ) < (Nat.choose (2 * (d + 1)) (d + 1) : ℝ) := by
          exact_mod_cast Nat.choose_pos (by omega)
        have hPdp1_lc_ne : (butcherShiftedLegendre (d + 1)).leadingCoeff ≠ 0 := by
          rw [hPdp1_lc]
          exact ne_of_gt hPdp1_lc_pos
        set c : ℝ := q.coeff (d + 1) / (butcherShiftedLegendre (d + 1)).leadingCoeff with hc_def
        have hc_ne : c ≠ 0 := div_ne_zero hq_coeff_ne hPdp1_lc_ne
        have h_Cc_Pdp1_lc :
            (Polynomial.C c * butcherShiftedLegendre (d + 1)).leadingCoeff =
              q.coeff (d + 1) := by
          rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc_def]
          field_simp
        have h_Cc_Pdp1_nd :
            (Polynomial.C c * butcherShiftedLegendre (d + 1)).natDegree = d + 1 := by
          rw [Polynomial.natDegree_C_mul hc_ne, butcherShiftedLegendre_natDegree]
        have h_Cc_Pdp1_ne : Polynomial.C c * butcherShiftedLegendre (d + 1) ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mp (by rw [h_Cc_Pdp1_lc]; exact hq_coeff_ne)
        have h_deg_eq :
            q.degree = (Polynomial.C c * butcherShiftedLegendre (d + 1)).degree := by
          rw [Polynomial.degree_eq_natDegree hq_ne,
              Polynomial.degree_eq_natDegree h_Cc_Pdp1_ne,
              heq, h_Cc_Pdp1_nd]
        have h_lc_eq : q.leadingCoeff =
            (Polynomial.C c * butcherShiftedLegendre (d + 1)).leadingCoeff := by
          rw [hq_lc, h_Cc_Pdp1_lc]
        have h_sub_deg :
            (q - Polynomial.C c * butcherShiftedLegendre (d + 1)).degree < q.degree :=
          Polynomial.degree_sub_lt h_deg_eq hq_ne h_lc_eq
        have h_sub_nd :
            (q - Polynomial.C c * butcherShiftedLegendre (d + 1)).natDegree ≤ d := by
          by_cases h_zero : q - Polynomial.C c * butcherShiftedLegendre (d + 1) = 0
          · rw [h_zero]; simp
          · rw [Polynomial.degree_eq_natDegree h_zero,
                Polynomial.degree_eq_natDegree hq_ne, heq] at h_sub_deg
            exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast h_sub_deg)
        -- Split q = (q - C c * P_{d+1}^*) + C c * P_{d+1}^* and use linearity.
        have h_split : q = (q - Polynomial.C c * butcherShiftedLegendre (d + 1)) +
                        Polynomial.C c * butcherShiftedLegendre (d + 1) := by ring
        have hf_int : IntervalIntegrable (fun x : ℝ =>
            (butcherShiftedLegendre m).eval x *
            (q - Polynomial.C c * butcherShiftedLegendre (d + 1)).eval x)
            MeasureTheory.volume 0 1 :=
          ((butcherShiftedLegendre m).continuous.mul
            (q - Polynomial.C c * butcherShiftedLegendre (d + 1)).continuous).intervalIntegrable
              _ _
        have hg_int : IntervalIntegrable (fun x : ℝ =>
            (butcherShiftedLegendre m).eval x *
            (Polynomial.C c * butcherShiftedLegendre (d + 1)).eval x)
            MeasureTheory.volume 0 1 :=
          ((butcherShiftedLegendre m).continuous.mul
            (Polynomial.C c * butcherShiftedLegendre (d + 1)).continuous).intervalIntegrable
              _ _
        rw [h_split]
        simp only [Polynomial.eval_add, mul_add]
        rw [intervalIntegral.integral_add hf_int hg_int]
        -- First term: by IH on the lower-degree residual.
        have h_first : ∫ x in (0 : ℝ)..1,
            (butcherShiftedLegendre m).eval x *
            (q - Polynomial.C c * butcherShiftedLegendre (d + 1)).eval x = 0 :=
          ih (Nat.lt_of_succ_lt hm) _ h_sub_nd
        -- Second term: constant pull-out plus (342a) orthogonality.
        have h_second : ∫ x in (0 : ℝ)..1,
            (butcherShiftedLegendre m).eval x *
            (Polynomial.C c * butcherShiftedLegendre (d + 1)).eval x = 0 := by
          have h_eq : ∀ x : ℝ,
              (butcherShiftedLegendre m).eval x *
              (Polynomial.C c * butcherShiftedLegendre (d + 1)).eval x =
              c * ((butcherShiftedLegendre m).eval x *
                   (butcherShiftedLegendre (d + 1)).eval x) := by
            intro x
            simp only [Polynomial.eval_mul, Polynomial.eval_C]
            ring
          simp_rw [h_eq]
          rw [intervalIntegral.integral_const_mul,
              butcherShiftedLegendre_orthogonal (by omega : m ≠ d + 1), mul_zero]
        rw [h_first, h_second, add_zero]

/-! ### Phase A.2 P2 — F.3 cross-term orthogonality

The cross-term of cycle 290's recurrence residual, `(2n - 1) · (2X - 1) ·
P_{n-1}^*`, is orthogonal to `P_k^*` for `k ≤ n - 3`. The proof factors
the constant `(2n - 1)`, commutes the integrand so that `P_{n-1}^*` is
on the left and `(2X - 1) · P_k^*` is on the right, then applies the P1
basis-span helper with `m := n - 1` and
`q := (C 2 · X - C 1) · P_k^*`. The natDegree side condition
`q.natDegree ≤ 1 + k ≤ n - 2 < n - 1` is discharged via
`butcherShiftedLegendre_one` (cycle 273: `P_1^* = C 2 · X - C 1`) and
`butcherShiftedLegendre_natDegree` (cycle 273). -/
theorem recurrence_residual_orthogonal_cross_term (n : ℕ) (hn : 3 ≤ n)
    {k : ℕ} (hk : k ≤ n - 3) :
    ∫ x in (0 : ℝ)..1,
      (Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
       (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
       butcherShiftedLegendre (n - 1)).eval x *
      (butcherShiftedLegendre k).eval x = 0 := by
  -- Rewrite the integrand as `(2n - 1) * (P_{n-1}^*.eval x * q.eval x)`
  -- where `q := (C 2 · X - C 1) * P_k^*`.
  have h_eq : ∀ x : ℝ,
      (Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
       (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
       butcherShiftedLegendre (n - 1)).eval x *
      (butcherShiftedLegendre k).eval x =
      ((2 * n - 1 : ℕ) : ℝ) *
        ((butcherShiftedLegendre (n - 1)).eval x *
          ((Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
            butcherShiftedLegendre k).eval x) := by
    intro x
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
    ring
  simp_rw [h_eq]
  rw [intervalIntegral.integral_const_mul]
  -- natDegree bound for the test polynomial.
  have h_2X_1_nd :
      (Polynomial.C 2 * Polynomial.X - Polynomial.C 1 : Polynomial ℝ).natDegree = 1 := by
    rw [← butcherShiftedLegendre_one]
    exact butcherShiftedLegendre_natDegree 1
  have h_q_nd :
      ((Polynomial.C 2 * Polynomial.X - Polynomial.C 1) * butcherShiftedLegendre k).natDegree
        < n - 1 := by
    calc ((Polynomial.C 2 * Polynomial.X - Polynomial.C 1) * butcherShiftedLegendre k).natDegree
        ≤ (Polynomial.C 2 * Polynomial.X - Polynomial.C 1 : Polynomial ℝ).natDegree +
            (butcherShiftedLegendre k).natDegree := Polynomial.natDegree_mul_le
      _ = 1 + k := by rw [h_2X_1_nd, butcherShiftedLegendre_natDegree]
      _ < n - 1 := by omega
  rw [butcherShiftedLegendre_orthogonal_to_lower_degree (n - 1) _ h_q_nd, mul_zero]

/-! ### Phase A.2 P3 — full residual orthogonality

Combine F.1, F.2 (cycle 291), and F.3 (above) to express the full
cycle 290 recurrence residual `Q := n • P_n^* - (2n - 1)(2X - 1)
P_{n-1}^* + (n - 1) P_{n-2}^*` as orthogonal to `P_k^*` for every
`k ≤ n - 3`. Closure: split via `intervalIntegral.integral_sub` and
`intervalIntegral.integral_add`, then dispatch each summand via the
corresponding cycle 291 / cycle 292 component. -/
theorem recurrence_residual_orthogonal (n : ℕ) (hn : 3 ≤ n)
    {k : ℕ} (hk : k ≤ n - 3) :
    ∫ x in (0 : ℝ)..1,
      (((n : ℝ) • butcherShiftedLegendre n
        - Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
          (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
          butcherShiftedLegendre (n - 1)
        + Polynomial.C ((n - 1 : ℕ) : ℝ) *
          butcherShiftedLegendre (n - 2)).eval x) *
      (butcherShiftedLegendre k).eval x = 0 := by
  have hk_lt : k < n := by omega
  have h_int_1 : IntervalIntegrable (fun x : ℝ =>
      ((n : ℝ) • butcherShiftedLegendre n).eval x * (butcherShiftedLegendre k).eval x)
      MeasureTheory.volume 0 1 :=
    (((((n : ℝ) • butcherShiftedLegendre n)).continuous.mul
      (butcherShiftedLegendre k).continuous).intervalIntegrable _ _)
  have h_int_2 : IntervalIntegrable (fun x : ℝ =>
      (Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
        (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
        butcherShiftedLegendre (n - 1)).eval x * (butcherShiftedLegendre k).eval x)
      MeasureTheory.volume 0 1 :=
    (((Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
        (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
        butcherShiftedLegendre (n - 1)).continuous.mul
      (butcherShiftedLegendre k).continuous).intervalIntegrable _ _)
  have h_int_3 : IntervalIntegrable (fun x : ℝ =>
      (Polynomial.C ((n - 1 : ℕ) : ℝ) * butcherShiftedLegendre (n - 2)).eval x *
      (butcherShiftedLegendre k).eval x)
      MeasureTheory.volume 0 1 :=
    (((Polynomial.C ((n - 1 : ℕ) : ℝ) * butcherShiftedLegendre (n - 2)).continuous.mul
      (butcherShiftedLegendre k).continuous).intervalIntegrable _ _)
  simp only [Polynomial.eval_add, Polynomial.eval_sub, sub_mul, add_mul]
  rw [intervalIntegral.integral_add (h_int_1.sub h_int_2) h_int_3,
      intervalIntegral.integral_sub h_int_1 h_int_2,
      recurrence_residual_orthogonal_first_term n hk_lt,
      recurrence_residual_orthogonal_cross_term n hn hk,
      recurrence_residual_orthogonal_third_term n hn hk,
      sub_zero, add_zero]

/-! ### Phase A.3 — derive `Q = 0` and extract the (342f) recurrence

Cycle 293 ships the infrastructure to derive `Q = 0` from the cycle 290
degree bound (`Q.natDegree < n`) and cycle 292 orthogonality
(`⟨Q, P_k^*⟩ = 0` for `k ≤ n - 3`).

The textbook route (Butcher §342, p. 236):
1. Compute `Q.eval 1 = 0` directly from (342b) (`P_n^*(1) = 1`).
2. Compute `Q(1 - x) = (-1)^n · Q(x)` from (342c)'s parity for each
   summand (cycle 272's `butcherShiftedLegendre_eval_one_sub`).
3. Combined with `Q.natDegree < n`, parity drops the bound to
   `Q.natDegree ≤ n - 2`. -/

/-- **Phase A.3 P1**: the cycle 290 recurrence residual evaluates to
zero at `x = 1`.

The residual is
`Q := (n : ℝ) • P_n^* − C(2n - 1) · (2X - 1) · P_{n-1}^* + C(n - 1) ·
P_{n-2}^*`. Direct from (342b): each `P_k^*(1) = 1` so the three terms
contribute `n`, `−(2n - 1) · (2·1 - 1) · 1 = −(2n - 1)`, and `+(n - 1)`,
summing to `n - (2n - 1) + (n - 1) = 0`. -/
theorem recurrence_residual_eval_at_one (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℝ) • butcherShiftedLegendre n
      - Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
        (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
        butcherShiftedLegendre (n - 1)
      + Polynomial.C ((n - 1 : ℕ) : ℝ) *
        butcherShiftedLegendre (n - 2)).eval 1 = 0 := by
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
             Polynomial.eval_smul, Polynomial.eval_C, Polynomial.eval_X,
             butcherShiftedLegendre_eval_one,
             smul_eq_mul]
  have h1 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring
  have h2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring
  rw [h1, h2]; ring

/-- **Phase A.3 P2**: the cycle 290 recurrence residual `Q` satisfies the
parity `Q(1 - x) = (-1)^n · Q(x)`.

Direct combination of cycle 272's `butcherShiftedLegendre_eval_one_sub`
on each of the three summands:
* `(n • P_n)(1 - x) = n · (-1)^n · P_n(x)`.
* The cross-term factor `(2 · (1 - x) - 1) = -(2x - 1)`, combining with
  `P_{n-1}(1-x) = (-1)^{n-1} P_{n-1}(x)` gives `(-1)^n · (2x - 1) ·
  P_{n-1}(x)`.
* `(n - 1) · P_{n-2}(1 - x) = (n - 1) · (-1)^{n-2} · P_{n-2}(x) =
  (n - 1) · (-1)^n · P_{n-2}(x)` for `n ≥ 2`.

Then `ring` factors out `(-1)^n`. -/
theorem recurrence_residual_parity (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    ((n : ℝ) • butcherShiftedLegendre n
      - Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
        (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
        butcherShiftedLegendre (n - 1)
      + Polynomial.C ((n - 1 : ℕ) : ℝ) *
        butcherShiftedLegendre (n - 2)).eval (1 - x)
    = ((-1 : ℝ) ^ n) *
      ((n : ℝ) • butcherShiftedLegendre n
        - Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
          (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
          butcherShiftedLegendre (n - 1)
        + Polynomial.C ((n - 1 : ℕ) : ℝ) *
          butcherShiftedLegendre (n - 2)).eval x := by
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
             Polynomial.eval_smul, Polynomial.eval_C, Polynomial.eval_X,
             smul_eq_mul]
  -- Parity facts for each P_k^*
  have hPn := butcherShiftedLegendre_eval_one_sub n x
  have hPnm1 := butcherShiftedLegendre_eval_one_sub (n - 1) x
  have hPnm2 := butcherShiftedLegendre_eval_one_sub (n - 2) x
  -- `(-1)^(n - 1) = -((-1)^n)` for n ≥ 1.
  have h_pow_nm1 : ((-1 : ℝ) ^ (n - 1)) = -((-1 : ℝ) ^ n) := by
    have hsplit : n = (n - 1) + 1 := by omega
    conv_rhs => rw [hsplit, pow_add, pow_one]
    ring
  -- `(-1)^(n - 2) = (-1)^n` for n ≥ 2.
  have h_pow_nm2 : ((-1 : ℝ) ^ (n - 2)) = (-1 : ℝ) ^ n := by
    have hsplit : n = (n - 2) + 2 := by omega
    conv_rhs => rw [hsplit, pow_add]
    norm_num
  rw [hPn, hPnm1, hPnm2, h_pow_nm1, h_pow_nm2]
  ring

/-- **Phase A.3 P3**: the cycle 290 recurrence residual `Q` has
`natDegree ≤ n - 2`.

Combines cycle 290's `recurrence_residual_natDegree_lt` (`Q.natDegree
< n`) with the parity from P2. The argument: if `Q ≠ 0`, lift parity to
the polynomial-level identity `Q.comp (C 1 - X) = C ((-1)^n) * Q`. Take
leading coefficients: `(Q.comp (C 1 - X)).leadingCoeff = Q.leadingCoeff
· (-1)^Q.natDegree` (via `Polynomial.leadingCoeff_comp`) while
`(C ((-1)^n) · Q).leadingCoeff = (-1)^n · Q.leadingCoeff`. Equating and
cancelling `Q.leadingCoeff ≠ 0` gives `(-1)^Q.natDegree = (-1)^n`.

Now suppose `Q.natDegree = n - 1`. Substituting gives `(-1)^(n-1) =
(-1)^n`, but the algebraic identity `(-1)^(n-1) · (-1) = (-1)^n` forces
`(-1)^(n-1) = 0`, contradiction. Hence `Q.natDegree ≤ n - 2`. -/
theorem recurrence_residual_natDegree_le (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℝ) • butcherShiftedLegendre n
      - Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
        (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
        butcherShiftedLegendre (n - 1)
      + Polynomial.C ((n - 1 : ℕ) : ℝ) *
        butcherShiftedLegendre (n - 2)).natDegree ≤ n - 2 := by
  set Q : Polynomial ℝ :=
    (n : ℝ) • butcherShiftedLegendre n
      - Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
        (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
        butcherShiftedLegendre (n - 1)
      + Polynomial.C ((n - 1 : ℕ) : ℝ) *
        butcherShiftedLegendre (n - 2) with hQ_def
  -- Cycle 290 degree bound.
  have hQ_lt : Q.natDegree < n := recurrence_residual_natDegree_lt n hn
  -- P2 parity, applied pointwise.
  have hQ_parity_eval : ∀ x : ℝ, Q.eval (1 - x) = (-1 : ℝ)^n * Q.eval x := by
    intro x
    exact recurrence_residual_parity n hn x
  -- If Q = 0, the bound is trivial.
  by_cases hQ_zero : Q = 0
  · rw [hQ_zero, Polynomial.natDegree_zero]; omega
  -- Q ≠ 0 case.
  have hLC_ne : Q.leadingCoeff ≠ 0 := by
    intro h; exact hQ_zero (Polynomial.leadingCoeff_eq_zero.mp h)
  -- Lift parity to polynomial level.
  have hQ_comp :
      Q.comp (Polynomial.C 1 - Polynomial.X) = Polynomial.C ((-1 : ℝ)^n) * Q := by
    apply Polynomial.funext
    intro x
    simp [Polynomial.eval_comp, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_mul]
    exact hQ_parity_eval x
  -- leadingCoeff of (C 1 - X) is -1.
  have hSub_lc :
      ((Polynomial.C 1 - Polynomial.X) : Polynomial ℝ).leadingCoeff = -1 := by
    have heq : ((Polynomial.C 1 - Polynomial.X) : Polynomial ℝ)
                 = -(Polynomial.X - Polynomial.C 1) := by ring
    rw [heq, Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_X_sub_C]
  -- natDegree of (C 1 - X) is 1.
  have hSub_nd : ((Polynomial.C 1 - Polynomial.X) : Polynomial ℝ).natDegree = 1 := by
    have heq : ((Polynomial.C 1 - Polynomial.X) : Polynomial ℝ)
                 = -(Polynomial.X - Polynomial.C 1) := by ring
    rw [heq, Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
  -- LHS leadingCoeff = Q.leadingCoeff * (-1)^Q.natDegree.
  have hLHS_lc :
      (Q.comp (Polynomial.C 1 - Polynomial.X)).leadingCoeff
        = Q.leadingCoeff * (-1 : ℝ)^Q.natDegree := by
    rw [Polynomial.leadingCoeff_comp (by rw [hSub_nd]; omega), hSub_lc]
  -- RHS leadingCoeff = (-1)^n * Q.leadingCoeff.
  have h_unit : IsUnit ((-1 : ℝ)^n) :=
    isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0))
  have hRHS_lc :
      (Polynomial.C ((-1 : ℝ)^n) * Q).leadingCoeff = (-1 : ℝ)^n * Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff_C_mul_of_isUnit h_unit]
  -- Equate.
  have hLC_eq : Q.leadingCoeff * (-1 : ℝ)^Q.natDegree
                = (-1 : ℝ)^n * Q.leadingCoeff := by
    have := congrArg Polynomial.leadingCoeff hQ_comp
    rw [hLHS_lc, hRHS_lc] at this
    exact this
  -- Cancel Q.leadingCoeff: (-1)^Q.natDegree = (-1)^n.
  have h_pow_eq : (-1 : ℝ)^Q.natDegree = (-1 : ℝ)^n := by
    have hLC_eq' : Q.leadingCoeff * (-1 : ℝ)^Q.natDegree
                   = Q.leadingCoeff * (-1 : ℝ)^n := by
      rw [hLC_eq]; ring
    exact mul_left_cancel₀ hLC_ne hLC_eq'
  -- Combine with Q.natDegree < n to derive Q.natDegree ≤ n - 2.
  by_contra h_not
  push_neg at h_not  -- h_not : n - 2 < Q.natDegree
  -- Q.natDegree < n and n - 2 < Q.natDegree, so Q.natDegree = n - 1.
  have h_d_eq : Q.natDegree = n - 1 := by omega
  rw [h_d_eq] at h_pow_eq
  -- (-1)^(n-1) = (-1)^n; use (-1)^n = (-1)^(n-1) * (-1) for n ≥ 1.
  have h_split : n = (n - 1) + 1 := by omega
  have h_pow_n : (-1 : ℝ)^n = (-1 : ℝ)^(n - 1) * (-1 : ℝ) := by
    conv_lhs => rw [h_split, pow_add, pow_one]
  rw [h_pow_n] at h_pow_eq
  -- h_pow_eq : (-1)^(n - 1) = (-1)^(n - 1) * (-1).
  have h_zero : (-1 : ℝ)^(n - 1) = 0 := by linarith
  exact (pow_ne_zero (n - 1) (by norm_num : (-1 : ℝ) ≠ 0)) h_zero

/-- **Phase A.3 P4** — basis-span converse helper.

If `q : ℝ[X]` has `natDegree ≤ m` and is orthogonal to `P_k^*` for every
`k < m`, then `q` is a scalar multiple of `P_m^*`. This is the
Gram-Schmidt-style converse of cycle 292's
`butcherShiftedLegendre_orthogonal_to_lower_degree`.

The proof is by induction on `m`:
* `m = 0`: `q.natDegree = 0`, so `q = C (q.coeff 0) = C (q.coeff 0) ·
  P_0^*` (using `P_0^* = C 1`).
* `m + 1`: subtract `c_top · P_{m+1}^*` to drop `natDegree` to `≤ m`,
  apply the IH on the residual `q'` to obtain `q' = C c' · P_m^*`,
  then use orthogonality of `q` to `P_m^*` plus `‖P_m^*‖² > 0` to
  force `c' = 0`. Hence `q = C c_top · P_{m+1}^*`. -/
theorem polynomial_eq_smul_butcherShiftedLegendre_of_natDegree_le_of_orthogonal
    (m : ℕ) (q : Polynomial ℝ) (hq_deg : q.natDegree ≤ m)
    (h_orth : ∀ k, k < m →
      ∫ x in (0 : ℝ)..1, q.eval x * (butcherShiftedLegendre k).eval x = 0) :
    ∃ c : ℝ, q = Polynomial.C c * butcherShiftedLegendre m := by
  suffices h : ∀ m' : ℕ, ∀ q : Polynomial ℝ, q.natDegree ≤ m' →
      (∀ k, k < m' →
        ∫ x in (0 : ℝ)..1, q.eval x * (butcherShiftedLegendre k).eval x = 0) →
      ∃ c : ℝ, q = Polynomial.C c * butcherShiftedLegendre m' from
    h m q hq_deg h_orth
  intro m'
  induction m' with
  | zero =>
      intro q hq_deg _
      have hq_nd : q.natDegree = 0 := Nat.le_zero.mp hq_deg
      have hq_eq : q = Polynomial.C (q.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hq_nd
      refine ⟨q.coeff 0, ?_⟩
      rw [hq_eq, butcherShiftedLegendre_zero]
      simp
  | succ m' ih =>
      intro q hq_deg h_orth
      -- Leading-coefficient setup for P_{m' + 1}^*.
      have hPmp1_lc : (butcherShiftedLegendre (m' + 1)).leadingCoeff =
                       (Nat.choose (2 * (m' + 1)) (m' + 1) : ℝ) :=
        butcherShiftedLegendre_leadingCoeff (m' + 1)
      have hPmp1_lc_pos : (0 : ℝ) < (Nat.choose (2 * (m' + 1)) (m' + 1) : ℝ) := by
        exact_mod_cast Nat.choose_pos (by omega)
      have hPmp1_lc_ne : (butcherShiftedLegendre (m' + 1)).leadingCoeff ≠ 0 := by
        rw [hPmp1_lc]; exact ne_of_gt hPmp1_lc_pos
      -- Define c_top and the residual q'.
      set c_top : ℝ := q.coeff (m' + 1) / (butcherShiftedLegendre (m' + 1)).leadingCoeff
        with hc_top_def
      set q' : Polynomial ℝ := q - Polynomial.C c_top * butcherShiftedLegendre (m' + 1)
        with hq'_def
      -- Step 1: q'.natDegree ≤ m'.
      have hq'_nd : q'.natDegree ≤ m' := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rw [hq'_def, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
        by_cases hN_eq : N = m' + 1
        · rw [hN_eq, hc_top_def]
          have hPmp1_at_mp1 : (butcherShiftedLegendre (m' + 1)).coeff (m' + 1) =
                              (butcherShiftedLegendre (m' + 1)).leadingCoeff := by
            rw [Polynomial.leadingCoeff, butcherShiftedLegendre_natDegree]
          rw [hPmp1_at_mp1, div_mul_cancel₀ _ hPmp1_lc_ne, sub_self]
        · have hq_coeff : q.coeff N = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < N)
          have hP_coeff : (butcherShiftedLegendre (m' + 1)).coeff N = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt
              (by rw [butcherShiftedLegendre_natDegree]; omega)
          rw [hq_coeff, hP_coeff, mul_zero, sub_zero]
      -- Step 2: q' orthogonal to P_k^* for k < m'.
      have hq'_orth : ∀ k, k < m' →
          ∫ x in (0 : ℝ)..1, q'.eval x * (butcherShiftedLegendre k).eval x = 0 := by
        intro k hk
        have h_int_q : IntervalIntegrable
            (fun x : ℝ => q.eval x * (butcherShiftedLegendre k).eval x)
            MeasureTheory.volume 0 1 :=
          (q.continuous.mul (butcherShiftedLegendre k).continuous).intervalIntegrable _ _
        have h_int_cP : IntervalIntegrable
            (fun x : ℝ =>
              (Polynomial.C c_top * butcherShiftedLegendre (m' + 1)).eval x *
              (butcherShiftedLegendre k).eval x)
            MeasureTheory.volume 0 1 :=
          ((Polynomial.C c_top * butcherShiftedLegendre (m' + 1)).continuous.mul
            (butcherShiftedLegendre k).continuous).intervalIntegrable _ _
        rw [hq'_def]
        simp only [Polynomial.eval_sub, sub_mul]
        rw [intervalIntegral.integral_sub h_int_q h_int_cP,
            h_orth k (by omega : k < m' + 1)]
        have h_eval_eq : ∀ x : ℝ,
            (Polynomial.C c_top * butcherShiftedLegendre (m' + 1)).eval x *
              (butcherShiftedLegendre k).eval x =
            c_top * ((butcherShiftedLegendre (m' + 1)).eval x *
                     (butcherShiftedLegendre k).eval x) := by
          intro x; simp [Polynomial.eval_mul, Polynomial.eval_C]; ring
        simp_rw [h_eval_eq]
        rw [intervalIntegral.integral_const_mul,
            butcherShiftedLegendre_orthogonal (by omega : m' + 1 ≠ k)]
        ring
      -- Step 3: apply IH to q'.
      obtain ⟨c', hc'_eq⟩ := ih q' hq'_nd hq'_orth
      -- Step 4: force c' = 0 via orthogonality of q at k = m'.
      have hc'_zero : c' = 0 := by
        have hm_orth : ∫ x in (0 : ℝ)..1,
            q.eval x * (butcherShiftedLegendre m').eval x = 0 :=
          h_orth m' (Nat.lt_succ_self m')
        have hq_combine : q = Polynomial.C c' * butcherShiftedLegendre m' +
                              Polynomial.C c_top * butcherShiftedLegendre (m' + 1) := by
          have h1 : q = q' + Polynomial.C c_top * butcherShiftedLegendre (m' + 1) := by
            rw [hq'_def]; ring
          rw [h1, hc'_eq]
        rw [hq_combine] at hm_orth
        have h_int_1 : IntervalIntegrable
            (fun x : ℝ =>
              (Polynomial.C c' * butcherShiftedLegendre m').eval x *
              (butcherShiftedLegendre m').eval x)
            MeasureTheory.volume 0 1 :=
          ((Polynomial.C c' * butcherShiftedLegendre m').continuous.mul
            (butcherShiftedLegendre m').continuous).intervalIntegrable _ _
        have h_int_2 : IntervalIntegrable
            (fun x : ℝ =>
              (Polynomial.C c_top * butcherShiftedLegendre (m' + 1)).eval x *
              (butcherShiftedLegendre m').eval x)
            MeasureTheory.volume 0 1 :=
          ((Polynomial.C c_top * butcherShiftedLegendre (m' + 1)).continuous.mul
            (butcherShiftedLegendre m').continuous).intervalIntegrable _ _
        simp only [Polynomial.eval_add, add_mul] at hm_orth
        rw [intervalIntegral.integral_add h_int_1 h_int_2] at hm_orth
        -- Vanish the c_top term.
        have h_eval_eq2 : ∀ x : ℝ,
            (Polynomial.C c_top * butcherShiftedLegendre (m' + 1)).eval x *
              (butcherShiftedLegendre m').eval x =
            c_top * ((butcherShiftedLegendre (m' + 1)).eval x *
                     (butcherShiftedLegendre m').eval x) := by
          intro x; simp [Polynomial.eval_mul, Polynomial.eval_C]; ring
        have h_term2 : ∫ x in (0 : ℝ)..1,
            (Polynomial.C c_top * butcherShiftedLegendre (m' + 1)).eval x *
              (butcherShiftedLegendre m').eval x = 0 := by
          simp_rw [h_eval_eq2]
          rw [intervalIntegral.integral_const_mul,
              butcherShiftedLegendre_orthogonal (by omega : m' + 1 ≠ m')]
          ring
        rw [h_term2, add_zero] at hm_orth
        -- hm_orth : ∫ (C c' * P_m') * P_m' = 0
        have h_eval_eq1 : ∀ x : ℝ,
            (Polynomial.C c' * butcherShiftedLegendre m').eval x *
              (butcherShiftedLegendre m').eval x =
            c' * ((butcherShiftedLegendre m').eval x *
                  (butcherShiftedLegendre m').eval x) := by
          intro x; simp [Polynomial.eval_mul, Polynomial.eval_C]; ring
        simp_rw [h_eval_eq1] at hm_orth
        rw [intervalIntegral.integral_const_mul] at hm_orth
        -- Convert ∫ P_m'^2 to ∫ P_m' * P_m'.
        have h_normsq : ∫ x in (0 : ℝ)..1,
            (butcherShiftedLegendre m').eval x * (butcherShiftedLegendre m').eval x
            = 1 / (2 * (m' : ℝ) + 1) := by
          have := butcherShiftedLegendre_norm_sq m'
          simp_rw [pow_two] at this
          exact this
        rw [h_normsq] at hm_orth
        have h_ne : (1 : ℝ) / (2 * (m' : ℝ) + 1) ≠ 0 := by
          apply div_ne_zero one_ne_zero
          positivity
        exact (mul_eq_zero.mp hm_orth).resolve_right h_ne
      -- Step 5: conclude q = C c_top * P_{m' + 1}^*.
      refine ⟨c_top, ?_⟩
      have hq'_zero : q' = 0 := by
        rw [hc'_eq, hc'_zero]; simp
      have h_sub_zero : q - Polynomial.C c_top * butcherShiftedLegendre (m' + 1) = 0 := by
        rw [← hq'_def]; exact hq'_zero
      exact sub_eq_zero.mp h_sub_zero

/-- **Phase A.3 P5** — the cycle 290 recurrence residual vanishes for `n ≥ 3`.

Combines:
* Cycle 290's `recurrence_residual_natDegree_lt` + Phase A.3 P3's
  parity-tightened bound `Q.natDegree ≤ n - 2`.
* Cycle 292's `recurrence_residual_orthogonal` (orthogonality of `Q`
  to `P_k^*` for `k ≤ n - 3`).
* Phase A.3 P4's basis-span converse, applied at `m := n - 2`, to
  obtain `Q = C c · P_{n-2}^*` for some scalar `c`.
* Phase A.3 P1's `recurrence_residual_eval_at_one` (`Q.eval 1 = 0`)
  combined with (342b) (`P_{n-2}^*(1) = 1`) to force `c = 0`.

Hence `Q = 0`. -/
theorem recurrence_residual_eq_zero (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) • butcherShiftedLegendre n
      - Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
        (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
        butcherShiftedLegendre (n - 1)
      + Polynomial.C ((n - 1 : ℕ) : ℝ) *
        butcherShiftedLegendre (n - 2) = 0 := by
  have hn2 : 2 ≤ n := by omega
  set Q : Polynomial ℝ :=
    (n : ℝ) • butcherShiftedLegendre n
      - Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
        (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
        butcherShiftedLegendre (n - 1)
      + Polynomial.C ((n - 1 : ℕ) : ℝ) *
        butcherShiftedLegendre (n - 2) with hQ_def
  have h_deg : Q.natDegree ≤ n - 2 := recurrence_residual_natDegree_le n hn2
  have h_orth : ∀ k, k < n - 2 →
      ∫ x in (0 : ℝ)..1, Q.eval x * (butcherShiftedLegendre k).eval x = 0 := by
    intro k hk
    exact recurrence_residual_orthogonal n hn (by omega : k ≤ n - 3)
  obtain ⟨c, hQ_eq⟩ :=
    polynomial_eq_smul_butcherShiftedLegendre_of_natDegree_le_of_orthogonal
      (n - 2) Q h_deg h_orth
  -- Q.eval 1 = 0 (P1) combined with hQ_eq forces c = 0.
  have h_Q_at_1 : Q.eval 1 = 0 := recurrence_residual_eval_at_one n hn2
  rw [hQ_eq] at h_Q_at_1
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
             butcherShiftedLegendre_eval_one, mul_one] at h_Q_at_1
  -- h_Q_at_1 : c = 0
  rw [hQ_eq, h_Q_at_1, Polynomial.C_0, zero_mul]

/-- **Butcher §342 (342f) — general three-term recurrence**.

For every `n ≥ 2`,
`n · P_n^*(x) = (2n - 1) · (2x - 1) · P_{n-1}^*(x) − (n - 1) · P_{n-2}^*(x)`.

Closes (342f) at all `n ≥ 2` by combining:
* The base case `n = 2`: cycle 282's
  `butcherShiftedLegendre_recurrence_two` (verified via direct
  computation).
* The general case `n ≥ 3`: Phase A.3 P5's
  `recurrence_residual_eq_zero` (this cycle), which packages the
  cycle 289–292 + Phase A.3 P1–P4 closure path. -/
theorem butcherShiftedLegendre_recurrence (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) • butcherShiftedLegendre n =
      Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
        (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
        butcherShiftedLegendre (n - 1)
      - Polynomial.C ((n - 1 : ℕ) : ℝ) *
        butcherShiftedLegendre (n - 2) := by
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · -- n = 2 base case
    interval_cases n
    have h := butcherShiftedLegendre_recurrence_two
    show (2 : ℝ) • butcherShiftedLegendre 2 =
         Polynomial.C ((2 * 2 - 1 : ℕ) : ℝ) *
           (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
           butcherShiftedLegendre (2 - 1)
         - Polynomial.C ((2 - 1 : ℕ) : ℝ) * butcherShiftedLegendre (2 - 2)
    convert h using 2 <;> norm_num
  · -- n ≥ 3 general case
    have h_zero := recurrence_residual_eq_zero n hn3
    linear_combination h_zero

/-! ## §342 (342g) — initial witnesses for `P_n^*` zeros in `(0, 1)`

The full clause (342g) — `P_n^*` has `n` distinct real zeros in
`(0, 1)` for every `n` — is the subject of the cycle-294 Aristotle
submission (project `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`) and a
multi-cycle manual fallback. This section ships three small empirical
deliverables that anchor the general statement:

* `butcherShiftedLegendre_one_root` (P2.1): `x = 1/2` is the unique
  root of `P_1^* = 2X - 1` and lies in `(0, 1)`.
* `butcherShiftedLegendre_two_roots` (P2.2): `(3 ± √3)/6` are two
  distinct roots of `P_2^* = 6X² - 6X + 1`, both in `(0, 1)`.
* `butcherShiftedLegendre_card_roots_le` (P3): the upper-bound half
  of (342g), `(P_n^*).roots.card ≤ n`, via `Polynomial.card_roots'`
  and `butcherShiftedLegendre_natDegree`.
-/

/-- **Butcher §342 (342g), witness for `n = 1`** — `P_1^*` has a root
at `x = 1/2 ∈ (0, 1)`.

Direct evaluation: `P_1^* = 2X - 1`, so `P_1^*(1/2) = 2 · (1/2) - 1 = 0`,
and `0 < 1/2 < 1` is immediate. -/
theorem butcherShiftedLegendre_one_root :
    (butcherShiftedLegendre 1).eval (1 / 2 : ℝ) = 0 ∧
      (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · rw [butcherShiftedLegendre_one]
    simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X]
  · simp [Set.mem_Ioo]
    norm_num

/-- **Butcher §342 (342g), witness for `n = 2`** — `P_2^*` has two
distinct roots `(3 ± √3)/6` in `(0, 1)`.

Proof: `P_2^* = 6X² - 6X + 1`. By the quadratic formula, the roots
are `x = (6 ± √12)/12 = (3 ± √3)/6`. Since `0 < √3 < 2` (from
`(√3)² = 3` and `3 < 4`), both roots lie strictly between `0` and `1`.
Distinctness follows from `√3 > 0`. -/
theorem butcherShiftedLegendre_two_roots :
    ∃ x₁ x₂ : ℝ,
      x₁ ≠ x₂ ∧
      x₁ ∈ Set.Ioo (0 : ℝ) 1 ∧ x₂ ∈ Set.Ioo (0 : ℝ) 1 ∧
      (butcherShiftedLegendre 2).eval x₁ = 0 ∧
      (butcherShiftedLegendre 2).eval x₂ = 0 := by
  have hsqrt3_nonneg : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsqrt3_pos : (0 : ℝ) < Real.sqrt 3 :=
    Real.sqrt_pos.mpr (by norm_num)
  have hsqrt3_sq : Real.sqrt 3 ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  -- √3 < 2 since (√3)² = 3 < 4 = 2².
  have hsqrt3_lt_two : Real.sqrt 3 < 2 := by
    nlinarith [hsqrt3_sq, hsqrt3_nonneg]
  refine ⟨(3 - Real.sqrt 3) / 6, (3 + Real.sqrt 3) / 6, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have : Real.sqrt 3 = 0 := by linarith
    linarith
  · simp only [Set.mem_Ioo]
    refine ⟨?_, ?_⟩
    · -- (3 - √3)/6 > 0 since √3 < 3
      have : Real.sqrt 3 < 3 := by linarith
      linarith
    · -- (3 - √3)/6 < 1 since 6 > 3 - √3 i.e. √3 > -3 (trivial)
      linarith
  · simp only [Set.mem_Ioo]
    refine ⟨?_, ?_⟩
    · -- (3 + √3)/6 > 0
      linarith
    · -- (3 + √3)/6 < 1 since 3 + √3 < 6 i.e. √3 < 3
      have : Real.sqrt 3 < 3 := by linarith
      linarith
  · rw [butcherShiftedLegendre_two]
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
               Polynomial.eval_mul, Polynomial.eval_pow,
               Polynomial.eval_C, Polynomial.eval_X]
    nlinarith [hsqrt3_sq]
  · rw [butcherShiftedLegendre_two]
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
               Polynomial.eval_mul, Polynomial.eval_pow,
               Polynomial.eval_C, Polynomial.eval_X]
    nlinarith [hsqrt3_sq]

/-- **Butcher §342 (342g), upper bound** — `P_n^*` has at most `n`
distinct real roots.

This is the easy half of (342g): combining Mathlib's
`Polynomial.card_roots'` (`p.roots.card ≤ p.natDegree`) with cycle
273's `butcherShiftedLegendre_natDegree` gives the multiset bound;
`Multiset.toFinset_card_le` then yields the `Finset` version. -/
theorem butcherShiftedLegendre_card_roots_le (n : ℕ) :
    (butcherShiftedLegendre n).roots.toFinset.card ≤ n := by
  calc (butcherShiftedLegendre n).roots.toFinset.card
      ≤ Multiset.card (butcherShiftedLegendre n).roots :=
        Multiset.toFinset_card_le _
    _ ≤ (butcherShiftedLegendre n).natDegree :=
        Polynomial.card_roots' _
    _ = n := butcherShiftedLegendre_natDegree n

/-- **Butcher §342 (342g), witness for `n = 3`** — `P_3^*` has three
distinct roots in `(0, 1)`.

Strategy (non-closed-form to avoid the cubic-formula nested radicals):
* `P_3^*(1/2) = 0` by the parity identity (342c): since `3` is odd,
  `P_3^*(1 - 1/2) = - P_3^*(1/2)`, so `P_3^*(1/2) = - P_3^*(1/2)`, hence
  `P_3^*(1/2) = 0`. This is the middle root.
* The other two roots come from IVT on `[0, 1/5]` and `[4/5, 1]` using
  the closed form `P_3^*(x) = 20x³ - 30x² + 12x - 1` from
  `butcherShiftedLegendre_three`:
  - `P_3^*(0) = -1`, `P_3^*(1/5) = 9/25 > 0` ⇒ root in `(0, 1/5)`.
  - `P_3^*(4/5) = -9/25 < 0`, `P_3^*(1) = 1` ⇒ root in `(4/5, 1)`.
* Distinctness follows from the disjoint open intervals
  `(0, 1/5)`, `{1/2}`, `(4/5, 1)`. -/
theorem butcherShiftedLegendre_three_roots :
    ∃ x₁ x₂ x₃ : ℝ,
      x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ ∧
      x₁ ∈ Set.Ioo (0 : ℝ) 1 ∧
      x₂ ∈ Set.Ioo (0 : ℝ) 1 ∧
      x₃ ∈ Set.Ioo (0 : ℝ) 1 ∧
      (butcherShiftedLegendre 3).eval x₁ = 0 ∧
      (butcherShiftedLegendre 3).eval x₂ = 0 ∧
      (butcherShiftedLegendre 3).eval x₃ = 0 := by
  have hP3 := butcherShiftedLegendre_three
  have hcont : Continuous (fun x : ℝ => (butcherShiftedLegendre 3).eval x) :=
    (butcherShiftedLegendre 3).continuous
  -- Key evaluations of `P_3^*` at five points.
  have hf_0 : (butcherShiftedLegendre 3).eval (0 : ℝ) = -1 := by
    rw [hP3]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  have hf_1 : (butcherShiftedLegendre 3).eval (1 : ℝ) = 1 := by
    rw [hP3]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_one_fifth : (butcherShiftedLegendre 3).eval (1 / 5 : ℝ) = 9 / 25 := by
    rw [hP3]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_four_fifths : (butcherShiftedLegendre 3).eval (4 / 5 : ℝ) = -(9 / 25) := by
    rw [hP3]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_half : (butcherShiftedLegendre 3).eval (1 / 2 : ℝ) = 0 := by
    have h := butcherShiftedLegendre_eval_one_sub 3 (1 / 2 : ℝ)
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num] at h
    have hsign : ((-1 : ℝ)) ^ 3 = -1 := by norm_num
    rw [hsign] at h
    linarith
  -- IVT on `[0, 1/5]`: sign flip from `-1` to `9/25` over `Ioo 0 (1/5)`.
  have hivt_left :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 3).eval x) '' Set.Ioo (0 : ℝ) (1 / 5) := by
    apply intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1 / 5) hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 3).eval (0 : ℝ))
        ((butcherShiftedLegendre 3).eval (1 / 5 : ℝ))
    rw [hf_0, hf_one_fifth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨x₁, hx₁_mem, hx₁_eval⟩ := hivt_left
  -- IVT on `[4/5, 1]`: sign flip from `-9/25` to `1` over `Ioo (4/5) 1`.
  have hivt_right :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 3).eval x) '' Set.Ioo (4 / 5 : ℝ) 1 := by
    apply intermediate_value_Ioo (by norm_num : (4 / 5 : ℝ) ≤ 1) hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 3).eval (4 / 5 : ℝ))
        ((butcherShiftedLegendre 3).eval (1 : ℝ))
    rw [hf_four_fifths, hf_1]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨x₃, hx₃_mem, hx₃_eval⟩ := hivt_right
  refine ⟨x₁, 1 / 2, x₃, ?_, ?_, ?_, ?_, ?_, ?_, hx₁_eval, hf_half, hx₃_eval⟩
  · -- `x₁ ≠ 1/2`: `x₁ < 1/5 < 1/2`.
    obtain ⟨_, hx₁_lt⟩ := hx₁_mem
    intro h
    linarith
  · -- `x₁ ≠ x₃`: `x₁ < 1/5 < 4/5 < x₃`.
    obtain ⟨_, hx₁_lt⟩ := hx₁_mem
    obtain ⟨hx₃_gt, _⟩ := hx₃_mem
    intro h
    linarith
  · -- `1/2 ≠ x₃`: `1/2 < 4/5 < x₃`.
    obtain ⟨hx₃_gt, _⟩ := hx₃_mem
    intro h
    linarith
  · -- `x₁ ∈ (0, 1)`: lift from `Ioo 0 (1/5)`.
    obtain ⟨hgt, hlt⟩ := hx₁_mem
    exact ⟨hgt, by linarith⟩
  · -- `1/2 ∈ (0, 1)`.
    refine ⟨?_, ?_⟩ <;> norm_num
  · -- `x₃ ∈ (0, 1)`: lift from `Ioo (4/5) 1`.
    obtain ⟨hgt, hlt⟩ := hx₃_mem
    exact ⟨by linarith, hlt⟩

/-- **Butcher §342 (342c) corollary** — for odd `n`, the midpoint
`x = 1/2` is automatically a root of `P_n^*`.

Proof: parity (342c) applied at `x = 1/2` gives
`P_n^*(1/2) = P_n^*(1 - 1/2) = (-1)^n · P_n^*(1/2)`. When `n` is odd,
`(-1)^n = -1`, so `P_n^*(1/2) = -P_n^*(1/2)`, forcing `P_n^*(1/2) = 0`.

This generalises the midpoint-root argument that opens the `n = 1`
and `n = 3` empirical anchors above, making the corresponding clause
for every future odd-`n` anchor a one-liner. -/
theorem butcherShiftedLegendre_eval_half_eq_zero_of_odd
    (n : ℕ) (hn : Odd n) :
    (butcherShiftedLegendre n).eval (1 / 2 : ℝ) = 0 := by
  have h := butcherShiftedLegendre_eval_one_sub n (1 / 2 : ℝ)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num] at h
  rw [hn.neg_one_pow] at h
  linarith

/-- **Butcher §342 (342g), witness for `n = 5`** — `P_5^*` has five
distinct roots in `(0, 1)`.

Strategy (mirrors cycle 295's `n = 3` recipe, scaled to five roots):
* Middle root `r₃ = 1/2` via cycle 295's
  `butcherShiftedLegendre_eval_half_eq_zero_of_odd` applied to
  `Odd 5 = ⟨2, rfl⟩` — `P_5^*(1/2) = 0` is parity-forced.
* Two roots on the left half via IVT using the closed form
  `P_5^*(x) = 252X^5 - 630X^4 + 560X^3 - 210X^2 + 30X - 1`:
  - `P_5^*(0) = -1 < 0 < 2497/6250 = P_5^*(1/10)` ⇒ root in `(0, 1/10)`.
  - `P_5^*(1/4) = -23/256 < 0 < 2497/6250 = P_5^*(1/10)` ⇒ root in
    `(1/10, 1/4)` via `intermediate_value_Ioo'` (descending endpoints).
* Two roots on the right half by the parity-symmetric evaluations:
  - `P_5^*(9/10) = -2497/6250 < 0 < 23/256 = P_5^*(3/4)` ⇒ root in
    `(3/4, 9/10)` via `intermediate_value_Ioo'`.
  - `P_5^*(9/10) = -2497/6250 < 0 < 1 = P_5^*(1)` ⇒ root in `(9/10, 1)`.
* Distinctness follows from the disjoint open intervals
  `(0, 1/10)`, `(1/10, 1/4)`, `{1/2}`, `(3/4, 9/10)`, `(9/10, 1)`. -/
theorem butcherShiftedLegendre_five_roots :
    ∃ r₁ r₂ r₃ r₄ r₅ : ℝ,
      r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₁ ≠ r₄ ∧ r₁ ≠ r₅ ∧
      r₂ ≠ r₃ ∧ r₂ ≠ r₄ ∧ r₂ ≠ r₅ ∧
      r₃ ≠ r₄ ∧ r₃ ≠ r₅ ∧
      r₄ ≠ r₅ ∧
      r₁ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₂ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₃ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₄ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₅ ∈ Set.Ioo (0 : ℝ) 1 ∧
      (butcherShiftedLegendre 5).eval r₁ = 0 ∧
      (butcherShiftedLegendre 5).eval r₂ = 0 ∧
      (butcherShiftedLegendre 5).eval r₃ = 0 ∧
      (butcherShiftedLegendre 5).eval r₄ = 0 ∧
      (butcherShiftedLegendre 5).eval r₅ = 0 := by
  have hP5 := butcherShiftedLegendre_five
  have hcont : Continuous (fun x : ℝ => (butcherShiftedLegendre 5).eval x) :=
    (butcherShiftedLegendre 5).continuous
  -- Seven key evaluations of `P_5^*`.
  have hf_0 : (butcherShiftedLegendre 5).eval (0 : ℝ) = -1 := by
    rw [hP5]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  have hf_1 : (butcherShiftedLegendre 5).eval (1 : ℝ) = 1 := by
    rw [hP5]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_one_tenth : (butcherShiftedLegendre 5).eval (1 / 10 : ℝ) = 2497 / 6250 := by
    rw [hP5]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_one_fourth : (butcherShiftedLegendre 5).eval (1 / 4 : ℝ) = -(23 / 256) := by
    rw [hP5]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_three_fourths : (butcherShiftedLegendre 5).eval (3 / 4 : ℝ) = 23 / 256 := by
    rw [hP5]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_nine_tenths :
      (butcherShiftedLegendre 5).eval (9 / 10 : ℝ) = -(2497 / 6250) := by
    rw [hP5]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_half : (butcherShiftedLegendre 5).eval (1 / 2 : ℝ) = 0 :=
    butcherShiftedLegendre_eval_half_eq_zero_of_odd 5 ⟨2, rfl⟩
  -- IVT₁: ascending on `[0, 1/10]` — `P_5^*(0) = -1`, `P_5^*(1/10) = 2497/6250`.
  have hivt_1 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 5).eval x) ''
        Set.Ioo (0 : ℝ) (1 / 10) := by
    apply intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1 / 10) hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 5).eval (0 : ℝ))
        ((butcherShiftedLegendre 5).eval (1 / 10 : ℝ))
    rw [hf_0, hf_one_tenth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₁, hr₁_mem, hr₁_eval⟩ := hivt_1
  -- IVT₂: descending on `[1/10, 1/4]` — `P_5^*(1/10) = 2497/6250`,
  -- `P_5^*(1/4) = -23/256`.  Use `intermediate_value_Ioo'`.
  have hivt_2 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 5).eval x) ''
        Set.Ioo (1 / 10 : ℝ) (1 / 4) := by
    apply intermediate_value_Ioo' (by norm_num : (1 / 10 : ℝ) ≤ 1 / 4) hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 5).eval (1 / 4 : ℝ))
        ((butcherShiftedLegendre 5).eval (1 / 10 : ℝ))
    rw [hf_one_fourth, hf_one_tenth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₂, hr₂_mem, hr₂_eval⟩ := hivt_2
  -- IVT₄: descending on `[3/4, 9/10]` — `P_5^*(3/4) = 23/256`,
  -- `P_5^*(9/10) = -2497/6250`.  Use `intermediate_value_Ioo'`.
  have hivt_4 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 5).eval x) ''
        Set.Ioo (3 / 4 : ℝ) (9 / 10) := by
    apply intermediate_value_Ioo' (by norm_num : (3 / 4 : ℝ) ≤ 9 / 10) hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 5).eval (9 / 10 : ℝ))
        ((butcherShiftedLegendre 5).eval (3 / 4 : ℝ))
    rw [hf_nine_tenths, hf_three_fourths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₄, hr₄_mem, hr₄_eval⟩ := hivt_4
  -- IVT₅: ascending on `[9/10, 1]` — `P_5^*(9/10) = -2497/6250`, `P_5^*(1) = 1`.
  have hivt_5 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 5).eval x) ''
        Set.Ioo (9 / 10 : ℝ) 1 := by
    apply intermediate_value_Ioo (by norm_num : (9 / 10 : ℝ) ≤ 1) hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 5).eval (9 / 10 : ℝ))
        ((butcherShiftedLegendre 5).eval (1 : ℝ))
    rw [hf_nine_tenths, hf_1]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₅, hr₅_mem, hr₅_eval⟩ := hivt_5
  refine ⟨r₁, r₂, 1 / 2, r₄, r₅,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_,
          hr₁_eval, hr₂_eval, hf_half, hr₄_eval, hr₅_eval⟩
  · -- r₁ ≠ r₂: r₁ < 1/10 < r₂.
    obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₂_gt, _⟩ := hr₂_mem
    intro h; linarith
  · -- r₁ ≠ 1/2: r₁ < 1/10 < 1/2.
    obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    intro h; linarith
  · -- r₁ ≠ r₄: r₁ < 1/10 < 3/4 < r₄.
    obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₄_gt, _⟩ := hr₄_mem
    intro h; linarith
  · -- r₁ ≠ r₅: r₁ < 1/10 < 9/10 < r₅.
    obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₅_gt, _⟩ := hr₅_mem
    intro h; linarith
  · -- r₂ ≠ 1/2: r₂ < 1/4 < 1/2.
    obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    intro h; linarith
  · -- r₂ ≠ r₄: r₂ < 1/4 < 3/4 < r₄.
    obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₄_gt, _⟩ := hr₄_mem
    intro h; linarith
  · -- r₂ ≠ r₅: r₂ < 1/4 < 9/10 < r₅.
    obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₅_gt, _⟩ := hr₅_mem
    intro h; linarith
  · -- 1/2 ≠ r₄: 1/2 < 3/4 < r₄.
    obtain ⟨hr₄_gt, _⟩ := hr₄_mem
    intro h; linarith
  · -- 1/2 ≠ r₅: 1/2 < 9/10 < r₅.
    obtain ⟨hr₅_gt, _⟩ := hr₅_mem
    intro h; linarith
  · -- r₄ ≠ r₅: r₄ < 9/10 < r₅.
    obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₅_gt, _⟩ := hr₅_mem
    intro h; linarith
  · -- r₁ ∈ (0, 1): lift from `Ioo 0 (1/10)`.
    obtain ⟨hgt, hlt⟩ := hr₁_mem
    exact ⟨hgt, by linarith⟩
  · -- r₂ ∈ (0, 1): lift from `Ioo (1/10) (1/4)`.
    obtain ⟨hgt, hlt⟩ := hr₂_mem
    exact ⟨by linarith, by linarith⟩
  · -- 1/2 ∈ (0, 1).
    refine ⟨?_, ?_⟩ <;> norm_num
  · -- r₄ ∈ (0, 1): lift from `Ioo (3/4) (9/10)`.
    obtain ⟨hgt, hlt⟩ := hr₄_mem
    exact ⟨by linarith, by linarith⟩
  · -- r₅ ∈ (0, 1): lift from `Ioo (9/10) 1`.
    obtain ⟨hgt, hlt⟩ := hr₅_mem
    exact ⟨by linarith, hlt⟩

/-- **Butcher §342 (342g), witness for `n = 7`** — `P_7^*` has seven
distinct roots in `(0, 1)`.

Strategy (mirrors the cycle 296 `n = 5` recipe, scaled to seven roots
using cycle 280's closed form
`P_7^* = 3432X^7 - 12012X^6 + 16632X^5 - 11550X^4 + 4200X^3 - 756X^2
        + 56X - 1`):
* Middle root `r₄ = 1/2` via cycle 295's
  `butcherShiftedLegendre_eval_half_eq_zero_of_odd 7 ⟨3, rfl⟩`
  (parity-forced, one-line application of the helper).
* Three roots on the left half via IVT on disjoint sign-change
  intervals:
  - `P_7^*(0) = -1 < 0 < 74891/312500 = P_7^*(1/10)` ⇒ root `r₁ ∈ (0, 1/10)`.
  - `P_7^*(1/5) = -25203/78125 < 0 < 74891/312500 = P_7^*(1/10)` ⇒
    root `r₂ ∈ (1/10, 1/5)` via `intermediate_value_Ioo'`.
  - `P_7^*(1/5) = -25203/78125 < 0 < 22931/78125 = P_7^*(2/5)` ⇒
    root `r₃ ∈ (1/5, 2/5)`.
* Three roots on the right half (parity-symmetric to the left triple):
  - `P_7^*(3/5) = -22931/78125 < 0 < 25203/78125 = P_7^*(4/5)` ⇒
    root `r₅ ∈ (3/5, 4/5)`.
  - `P_7^*(9/10) = -74891/312500 < 0 < 25203/78125 = P_7^*(4/5)` ⇒
    root `r₆ ∈ (4/5, 9/10)` via `intermediate_value_Ioo'`.
  - `P_7^*(9/10) = -74891/312500 < 0 < 1 = P_7^*(1)` ⇒
    root `r₇ ∈ (9/10, 1)`.
* Distinctness (21 pairs) follows from the disjoint open intervals
  `(0, 1/10) < (1/10, 1/5) < (1/5, 2/5) < {1/2} < (3/5, 4/5) <
   (4/5, 9/10) < (9/10, 1)`. -/
theorem butcherShiftedLegendre_seven_roots :
    ∃ r₁ r₂ r₃ r₄ r₅ r₆ r₇ : ℝ,
      r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₁ ≠ r₄ ∧ r₁ ≠ r₅ ∧ r₁ ≠ r₆ ∧ r₁ ≠ r₇ ∧
      r₂ ≠ r₃ ∧ r₂ ≠ r₄ ∧ r₂ ≠ r₅ ∧ r₂ ≠ r₆ ∧ r₂ ≠ r₇ ∧
      r₃ ≠ r₄ ∧ r₃ ≠ r₅ ∧ r₃ ≠ r₆ ∧ r₃ ≠ r₇ ∧
      r₄ ≠ r₅ ∧ r₄ ≠ r₆ ∧ r₄ ≠ r₇ ∧
      r₅ ≠ r₆ ∧ r₅ ≠ r₇ ∧
      r₆ ≠ r₇ ∧
      r₁ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₂ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₃ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₄ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₅ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₆ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₇ ∈ Set.Ioo (0 : ℝ) 1 ∧
      (butcherShiftedLegendre 7).eval r₁ = 0 ∧
      (butcherShiftedLegendre 7).eval r₂ = 0 ∧
      (butcherShiftedLegendre 7).eval r₃ = 0 ∧
      (butcherShiftedLegendre 7).eval r₄ = 0 ∧
      (butcherShiftedLegendre 7).eval r₅ = 0 ∧
      (butcherShiftedLegendre 7).eval r₆ = 0 ∧
      (butcherShiftedLegendre 7).eval r₇ = 0 := by
  have hP7 := butcherShiftedLegendre_seven
  have hcont : Continuous (fun x : ℝ => (butcherShiftedLegendre 7).eval x) :=
    (butcherShiftedLegendre 7).continuous
  -- Nine key evaluations of `P_7^*`.
  have hf_0 : (butcherShiftedLegendre 7).eval (0 : ℝ) = -1 := by
    rw [hP7]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  have hf_1 : (butcherShiftedLegendre 7).eval (1 : ℝ) = 1 := by
    rw [hP7]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_one_tenth :
      (butcherShiftedLegendre 7).eval (1 / 10 : ℝ) = 74891 / 312500 := by
    rw [hP7]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_one_fifth :
      (butcherShiftedLegendre 7).eval (1 / 5 : ℝ) = -(25203 / 78125) := by
    rw [hP7]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_two_fifths :
      (butcherShiftedLegendre 7).eval (2 / 5 : ℝ) = 22931 / 78125 := by
    rw [hP7]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_three_fifths :
      (butcherShiftedLegendre 7).eval (3 / 5 : ℝ) = -(22931 / 78125) := by
    rw [hP7]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_four_fifths :
      (butcherShiftedLegendre 7).eval (4 / 5 : ℝ) = 25203 / 78125 := by
    rw [hP7]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_nine_tenths :
      (butcherShiftedLegendre 7).eval (9 / 10 : ℝ) = -(74891 / 312500) := by
    rw [hP7]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_half : (butcherShiftedLegendre 7).eval (1 / 2 : ℝ) = 0 :=
    butcherShiftedLegendre_eval_half_eq_zero_of_odd 7 ⟨3, rfl⟩
  -- IVT₁: ascending on `[0, 1/10]` — `P_7^*(0) = -1`, `P_7^*(1/10) = 74891/312500`.
  have hivt_1 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 7).eval x) ''
        Set.Ioo (0 : ℝ) (1 / 10) := by
    apply intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1 / 10) hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 7).eval (0 : ℝ))
        ((butcherShiftedLegendre 7).eval (1 / 10 : ℝ))
    rw [hf_0, hf_one_tenth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₁, hr₁_mem, hr₁_eval⟩ := hivt_1
  -- IVT₂: descending on `[1/10, 1/5]` — `P_7^*(1/10) = 74891/312500`,
  -- `P_7^*(1/5) = -25203/78125`. Use `intermediate_value_Ioo'`.
  have hivt_2 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 7).eval x) ''
        Set.Ioo (1 / 10 : ℝ) (1 / 5) := by
    apply intermediate_value_Ioo' (by norm_num : (1 / 10 : ℝ) ≤ 1 / 5) hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 7).eval (1 / 5 : ℝ))
        ((butcherShiftedLegendre 7).eval (1 / 10 : ℝ))
    rw [hf_one_fifth, hf_one_tenth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₂, hr₂_mem, hr₂_eval⟩ := hivt_2
  -- IVT₃: ascending on `[1/5, 2/5]` — `P_7^*(1/5) = -25203/78125`,
  -- `P_7^*(2/5) = 22931/78125`.
  have hivt_3 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 7).eval x) ''
        Set.Ioo (1 / 5 : ℝ) (2 / 5) := by
    apply intermediate_value_Ioo (by norm_num : (1 / 5 : ℝ) ≤ 2 / 5) hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 7).eval (1 / 5 : ℝ))
        ((butcherShiftedLegendre 7).eval (2 / 5 : ℝ))
    rw [hf_one_fifth, hf_two_fifths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₃, hr₃_mem, hr₃_eval⟩ := hivt_3
  -- IVT₅: ascending on `[3/5, 4/5]` — `P_7^*(3/5) = -22931/78125`,
  -- `P_7^*(4/5) = 25203/78125`.
  have hivt_5 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 7).eval x) ''
        Set.Ioo (3 / 5 : ℝ) (4 / 5) := by
    apply intermediate_value_Ioo (by norm_num : (3 / 5 : ℝ) ≤ 4 / 5) hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 7).eval (3 / 5 : ℝ))
        ((butcherShiftedLegendre 7).eval (4 / 5 : ℝ))
    rw [hf_three_fifths, hf_four_fifths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₅, hr₅_mem, hr₅_eval⟩ := hivt_5
  -- IVT₆: descending on `[4/5, 9/10]` — `P_7^*(4/5) = 25203/78125`,
  -- `P_7^*(9/10) = -74891/312500`. Use `intermediate_value_Ioo'`.
  have hivt_6 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 7).eval x) ''
        Set.Ioo (4 / 5 : ℝ) (9 / 10) := by
    apply intermediate_value_Ioo' (by norm_num : (4 / 5 : ℝ) ≤ 9 / 10) hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 7).eval (9 / 10 : ℝ))
        ((butcherShiftedLegendre 7).eval (4 / 5 : ℝ))
    rw [hf_nine_tenths, hf_four_fifths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₆, hr₆_mem, hr₆_eval⟩ := hivt_6
  -- IVT₇: ascending on `[9/10, 1]` — `P_7^*(9/10) = -74891/312500`, `P_7^*(1) = 1`.
  have hivt_7 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 7).eval x) ''
        Set.Ioo (9 / 10 : ℝ) 1 := by
    apply intermediate_value_Ioo (by norm_num : (9 / 10 : ℝ) ≤ 1) hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 7).eval (9 / 10 : ℝ))
        ((butcherShiftedLegendre 7).eval (1 : ℝ))
    rw [hf_nine_tenths, hf_1]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₇, hr₇_mem, hr₇_eval⟩ := hivt_7
  refine ⟨r₁, r₂, r₃, 1 / 2, r₅, r₆, r₇,
          ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_,
          ?_, ?_, ?_,
          ?_, ?_,
          ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          hr₁_eval, hr₂_eval, hr₃_eval, hf_half, hr₅_eval, hr₆_eval, hr₇_eval⟩
  · -- r₁ ≠ r₂: r₁ < 1/10 < r₂.
    obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₂_gt, _⟩ := hr₂_mem
    intro h; linarith
  · -- r₁ ≠ r₃: r₁ < 1/10 < 1/5 < r₃.
    obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₃_gt, _⟩ := hr₃_mem
    intro h; linarith
  · -- r₁ ≠ 1/2: r₁ < 1/10 < 1/2.
    obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    intro h; linarith
  · -- r₁ ≠ r₅: r₁ < 1/10 < 3/5 < r₅.
    obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₅_gt, _⟩ := hr₅_mem
    intro h; linarith
  · -- r₁ ≠ r₆: r₁ < 1/10 < 4/5 < r₆.
    obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₆_gt, _⟩ := hr₆_mem
    intro h; linarith
  · -- r₁ ≠ r₇: r₁ < 1/10 < 9/10 < r₇.
    obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · -- r₂ ≠ r₃: r₂ < 1/5 < r₃.
    obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₃_gt, _⟩ := hr₃_mem
    intro h; linarith
  · -- r₂ ≠ 1/2: r₂ < 1/5 < 1/2.
    obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    intro h; linarith
  · -- r₂ ≠ r₅: r₂ < 1/5 < 3/5 < r₅.
    obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₅_gt, _⟩ := hr₅_mem
    intro h; linarith
  · -- r₂ ≠ r₆: r₂ < 1/5 < 4/5 < r₆.
    obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₆_gt, _⟩ := hr₆_mem
    intro h; linarith
  · -- r₂ ≠ r₇: r₂ < 1/5 < 9/10 < r₇.
    obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · -- r₃ ≠ 1/2: r₃ < 2/5 < 1/2.
    obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    intro h; linarith
  · -- r₃ ≠ r₅: r₃ < 2/5 < 3/5 < r₅.
    obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₅_gt, _⟩ := hr₅_mem
    intro h; linarith
  · -- r₃ ≠ r₆: r₃ < 2/5 < 4/5 < r₆.
    obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₆_gt, _⟩ := hr₆_mem
    intro h; linarith
  · -- r₃ ≠ r₇: r₃ < 2/5 < 9/10 < r₇.
    obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · -- 1/2 ≠ r₅: 1/2 < 3/5 < r₅.
    obtain ⟨hr₅_gt, _⟩ := hr₅_mem
    intro h; linarith
  · -- 1/2 ≠ r₆: 1/2 < 4/5 < r₆.
    obtain ⟨hr₆_gt, _⟩ := hr₆_mem
    intro h; linarith
  · -- 1/2 ≠ r₇: 1/2 < 9/10 < r₇.
    obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · -- r₅ ≠ r₆: r₅ < 4/5 < r₆.
    obtain ⟨_, hr₅_lt⟩ := hr₅_mem
    obtain ⟨hr₆_gt, _⟩ := hr₆_mem
    intro h; linarith
  · -- r₅ ≠ r₇: r₅ < 4/5 < 9/10 < r₇.
    obtain ⟨_, hr₅_lt⟩ := hr₅_mem
    obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · -- r₆ ≠ r₇: r₆ < 9/10 < r₇.
    obtain ⟨_, hr₆_lt⟩ := hr₆_mem
    obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · -- r₁ ∈ (0, 1): lift from `Ioo 0 (1/10)`.
    obtain ⟨hgt, hlt⟩ := hr₁_mem
    exact ⟨hgt, by linarith⟩
  · -- r₂ ∈ (0, 1): lift from `Ioo (1/10) (1/5)`.
    obtain ⟨hgt, hlt⟩ := hr₂_mem
    exact ⟨by linarith, by linarith⟩
  · -- r₃ ∈ (0, 1): lift from `Ioo (1/5) (2/5)`.
    obtain ⟨hgt, hlt⟩ := hr₃_mem
    exact ⟨by linarith, by linarith⟩
  · -- 1/2 ∈ (0, 1).
    refine ⟨?_, ?_⟩ <;> norm_num
  · -- r₅ ∈ (0, 1): lift from `Ioo (3/5) (4/5)`.
    obtain ⟨hgt, hlt⟩ := hr₅_mem
    exact ⟨by linarith, by linarith⟩
  · -- r₆ ∈ (0, 1): lift from `Ioo (4/5) (9/10)`.
    obtain ⟨hgt, hlt⟩ := hr₆_mem
    exact ⟨by linarith, by linarith⟩
  · -- r₇ ∈ (0, 1): lift from `Ioo (9/10) 1`.
    obtain ⟨hgt, hlt⟩ := hr₇_mem
    exact ⟨by linarith, hlt⟩

/-- (342g) at `n = 9` — empirical anchor: `P_9^*` has nine distinct real zeros in
the open interval `(0, 1)`. Strictly weaker than the general (342g) statement
(`∀ n`, currently held by Aristotle project
`5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`), but axiom-clean and unconditional.

Mechanical extension of cycle 297's `butcherShiftedLegendre_seven_roots` recipe
to nine roots, using cycle 285's closed form `butcherShiftedLegendre_nine` and
cycle 295's parity helper `butcherShiftedLegendre_eval_half_eq_zero_of_odd`
witnessed by `9 = 2*4 + 1` (i.e. `⟨4, rfl⟩`).

Bracket plan (each endpoint sign hand-verified via Python `Fraction` before
writing):
* `r₁ ∈ (0, 1/20)`         ascending  — `P(0) = -1`, `P(1/20) = 9459468441/25600000000`
* `r₂ ∈ (1/20, 1/8)`       descending — `P(1/8) = -(10413009/33554432)`
* `r₃ ∈ (1/8, 1/4)`        ascending  — `P(1/4) = 17557/65536`
* `r₄ ∈ (1/4, 2/5)`        descending — `P(2/5) = -(96077/390625)`
* `r₅ = 1/2`               parity     — odd-degree forces `P(1/2) = 0`
* `r₆ ∈ (3/5, 3/4)`        descending — parity-mirror of (1/4, 2/5)
* `r₇ ∈ (3/4, 7/8)`        ascending  — parity-mirror of (1/8, 1/4)
* `r₈ ∈ (7/8, 19/20)`      descending — parity-mirror of (1/20, 1/8)
* `r₉ ∈ (19/20, 1)`        ascending  — parity-mirror of (0, 1/20)

Distinctness (36 pairs) follows from the strict ordering of the brackets:
`(0, 1/20) < (1/20, 1/8) < (1/8, 1/4) < (1/4, 2/5) < {1/2} < (3/5, 3/4) <
 (3/4, 7/8) < (7/8, 19/20) < (19/20, 1)`. -/
theorem butcherShiftedLegendre_nine_roots :
    ∃ r₁ r₂ r₃ r₄ r₅ r₆ r₇ r₈ r₉ : ℝ,
      r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₁ ≠ r₄ ∧ r₁ ≠ r₅ ∧ r₁ ≠ r₆ ∧ r₁ ≠ r₇ ∧
        r₁ ≠ r₈ ∧ r₁ ≠ r₉ ∧
      r₂ ≠ r₃ ∧ r₂ ≠ r₄ ∧ r₂ ≠ r₅ ∧ r₂ ≠ r₆ ∧ r₂ ≠ r₇ ∧ r₂ ≠ r₈ ∧ r₂ ≠ r₉ ∧
      r₃ ≠ r₄ ∧ r₃ ≠ r₅ ∧ r₃ ≠ r₆ ∧ r₃ ≠ r₇ ∧ r₃ ≠ r₈ ∧ r₃ ≠ r₉ ∧
      r₄ ≠ r₅ ∧ r₄ ≠ r₆ ∧ r₄ ≠ r₇ ∧ r₄ ≠ r₈ ∧ r₄ ≠ r₉ ∧
      r₅ ≠ r₆ ∧ r₅ ≠ r₇ ∧ r₅ ≠ r₈ ∧ r₅ ≠ r₉ ∧
      r₆ ≠ r₇ ∧ r₆ ≠ r₈ ∧ r₆ ≠ r₉ ∧
      r₇ ≠ r₈ ∧ r₇ ≠ r₉ ∧
      r₈ ≠ r₉ ∧
      r₁ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₂ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₃ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₄ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₅ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₆ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₇ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₈ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₉ ∈ Set.Ioo (0 : ℝ) 1 ∧
      (butcherShiftedLegendre 9).eval r₁ = 0 ∧
      (butcherShiftedLegendre 9).eval r₂ = 0 ∧
      (butcherShiftedLegendre 9).eval r₃ = 0 ∧
      (butcherShiftedLegendre 9).eval r₄ = 0 ∧
      (butcherShiftedLegendre 9).eval r₅ = 0 ∧
      (butcherShiftedLegendre 9).eval r₆ = 0 ∧
      (butcherShiftedLegendre 9).eval r₇ = 0 ∧
      (butcherShiftedLegendre 9).eval r₈ = 0 ∧
      (butcherShiftedLegendre 9).eval r₉ = 0 := by
  have hP9 := butcherShiftedLegendre_nine
  have hcont : Continuous (fun x : ℝ => (butcherShiftedLegendre 9).eval x) :=
    (butcherShiftedLegendre 9).continuous
  -- Ten key evaluations of `P_9^*`.
  have hf_0 : (butcherShiftedLegendre 9).eval (0 : ℝ) = -1 := by
    rw [hP9]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  have hf_1 : (butcherShiftedLegendre 9).eval (1 : ℝ) = 1 := by
    rw [hP9]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_one_twentieth :
      (butcherShiftedLegendre 9).eval (1 / 20 : ℝ) =
        9459468441 / 25600000000 := by
    rw [hP9]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_one_eighth :
      (butcherShiftedLegendre 9).eval (1 / 8 : ℝ) =
        -(10413009 / 33554432) := by
    rw [hP9]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_one_fourth :
      (butcherShiftedLegendre 9).eval (1 / 4 : ℝ) = 17557 / 65536 := by
    rw [hP9]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_two_fifths :
      (butcherShiftedLegendre 9).eval (2 / 5 : ℝ) = -(96077 / 390625) := by
    rw [hP9]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_three_fifths :
      (butcherShiftedLegendre 9).eval (3 / 5 : ℝ) = 96077 / 390625 := by
    rw [hP9]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_three_fourths :
      (butcherShiftedLegendre 9).eval (3 / 4 : ℝ) = -(17557 / 65536) := by
    rw [hP9]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_seven_eighths :
      (butcherShiftedLegendre 9).eval (7 / 8 : ℝ) = 10413009 / 33554432 := by
    rw [hP9]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_nineteen_twentieths :
      (butcherShiftedLegendre 9).eval (19 / 20 : ℝ) =
        -(9459468441 / 25600000000) := by
    rw [hP9]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_half : (butcherShiftedLegendre 9).eval (1 / 2 : ℝ) = 0 :=
    butcherShiftedLegendre_eval_half_eq_zero_of_odd 9 ⟨4, rfl⟩
  -- IVT₁: ascending on `[0, 1/20]`.
  have hivt_1 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 9).eval x) ''
        Set.Ioo (0 : ℝ) (1 / 20) := by
    apply intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1 / 20) hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 9).eval (0 : ℝ))
        ((butcherShiftedLegendre 9).eval (1 / 20 : ℝ))
    rw [hf_0, hf_one_twentieth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₁, hr₁_mem, hr₁_eval⟩ := hivt_1
  -- IVT₂: descending on `[1/20, 1/8]`.
  have hivt_2 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 9).eval x) ''
        Set.Ioo (1 / 20 : ℝ) (1 / 8) := by
    apply intermediate_value_Ioo' (by norm_num : (1 / 20 : ℝ) ≤ 1 / 8)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 9).eval (1 / 8 : ℝ))
        ((butcherShiftedLegendre 9).eval (1 / 20 : ℝ))
    rw [hf_one_eighth, hf_one_twentieth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₂, hr₂_mem, hr₂_eval⟩ := hivt_2
  -- IVT₃: ascending on `[1/8, 1/4]`.
  have hivt_3 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 9).eval x) ''
        Set.Ioo (1 / 8 : ℝ) (1 / 4) := by
    apply intermediate_value_Ioo (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 9).eval (1 / 8 : ℝ))
        ((butcherShiftedLegendre 9).eval (1 / 4 : ℝ))
    rw [hf_one_eighth, hf_one_fourth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₃, hr₃_mem, hr₃_eval⟩ := hivt_3
  -- IVT₄: descending on `[1/4, 2/5]`.
  have hivt_4 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 9).eval x) ''
        Set.Ioo (1 / 4 : ℝ) (2 / 5) := by
    apply intermediate_value_Ioo' (by norm_num : (1 / 4 : ℝ) ≤ 2 / 5)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 9).eval (2 / 5 : ℝ))
        ((butcherShiftedLegendre 9).eval (1 / 4 : ℝ))
    rw [hf_two_fifths, hf_one_fourth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₄, hr₄_mem, hr₄_eval⟩ := hivt_4
  -- IVT₆: descending on `[3/5, 3/4]`.
  have hivt_6 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 9).eval x) ''
        Set.Ioo (3 / 5 : ℝ) (3 / 4) := by
    apply intermediate_value_Ioo' (by norm_num : (3 / 5 : ℝ) ≤ 3 / 4)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 9).eval (3 / 4 : ℝ))
        ((butcherShiftedLegendre 9).eval (3 / 5 : ℝ))
    rw [hf_three_fourths, hf_three_fifths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₆, hr₆_mem, hr₆_eval⟩ := hivt_6
  -- IVT₇: ascending on `[3/4, 7/8]`.
  have hivt_7 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 9).eval x) ''
        Set.Ioo (3 / 4 : ℝ) (7 / 8) := by
    apply intermediate_value_Ioo (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 9).eval (3 / 4 : ℝ))
        ((butcherShiftedLegendre 9).eval (7 / 8 : ℝ))
    rw [hf_three_fourths, hf_seven_eighths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₇, hr₇_mem, hr₇_eval⟩ := hivt_7
  -- IVT₈: descending on `[7/8, 19/20]`.
  have hivt_8 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 9).eval x) ''
        Set.Ioo (7 / 8 : ℝ) (19 / 20) := by
    apply intermediate_value_Ioo' (by norm_num : (7 / 8 : ℝ) ≤ 19 / 20)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 9).eval (19 / 20 : ℝ))
        ((butcherShiftedLegendre 9).eval (7 / 8 : ℝ))
    rw [hf_nineteen_twentieths, hf_seven_eighths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₈, hr₈_mem, hr₈_eval⟩ := hivt_8
  -- IVT₉: ascending on `[19/20, 1]`.
  have hivt_9 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 9).eval x) ''
        Set.Ioo (19 / 20 : ℝ) 1 := by
    apply intermediate_value_Ioo (by norm_num : (19 / 20 : ℝ) ≤ 1)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 9).eval (19 / 20 : ℝ))
        ((butcherShiftedLegendre 9).eval (1 : ℝ))
    rw [hf_nineteen_twentieths, hf_1]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₉, hr₉_mem, hr₉_eval⟩ := hivt_9
  refine ⟨r₁, r₂, r₃, r₄, 1 / 2, r₆, r₇, r₈, r₉,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_,
          ?_, ?_, ?_,
          ?_, ?_,
          ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          hr₁_eval, hr₂_eval, hr₃_eval, hr₄_eval, hf_half,
          hr₆_eval, hr₇_eval, hr₈_eval, hr₉_eval⟩
  -- 36 distinctness goals (8 + 7 + 6 + 5 + 4 + 3 + 2 + 1).
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₂_gt, _⟩ := hr₂_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₃_gt, _⟩ := hr₃_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₄_gt, _⟩ := hr₄_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₆_gt, _⟩ := hr₆_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₃_gt, _⟩ := hr₃_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₄_gt, _⟩ := hr₄_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₆_gt, _⟩ := hr₆_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₄_gt, _⟩ := hr₄_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₆_gt, _⟩ := hr₆_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₆_gt, _⟩ := hr₆_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨hr₆_gt, _⟩ := hr₆_mem
    intro h; linarith
  · obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₆_lt⟩ := hr₆_mem
    obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · obtain ⟨_, hr₆_lt⟩ := hr₆_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₆_lt⟩ := hr₆_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₇_lt⟩ := hr₇_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₇_lt⟩ := hr₇_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₈_lt⟩ := hr₈_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  -- 9 membership-in-(0,1) goals.
  · obtain ⟨hgt, hlt⟩ := hr₁_mem
    exact ⟨hgt, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₂_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₃_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₄_mem
    exact ⟨by linarith, by linarith⟩
  · refine ⟨?_, ?_⟩ <;> norm_num
  · obtain ⟨hgt, hlt⟩ := hr₆_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₇_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₈_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₉_mem
    exact ⟨by linarith, hlt⟩

/-- (342g) at `n = 11` — empirical anchor: `P_11^*` has eleven distinct real
zeros in the open interval `(0, 1)`. Strictly weaker than the general (342g)
statement (`∀ n`, currently held by Aristotle project
`5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`), but axiom-clean and unconditional.

Mechanical extension of cycle 298's `butcherShiftedLegendre_nine_roots` recipe
to eleven roots, using cycle 287's closed form `butcherShiftedLegendre_eleven`
and cycle 295's parity helper `butcherShiftedLegendre_eval_half_eq_zero_of_odd`
witnessed by `11 = 2*5 + 1` (i.e. `⟨5, rfl⟩`).

Bracket plan (each endpoint sign hand-verified via Python `Fraction` before
writing):
* `r₁  ∈ (0, 1/50)`       ascending  — `P(0) = -1`, `P(1/50) ≈ +0.339`.
* `r₂  ∈ (1/50, 1/10)`    descending — `P(1/10) = -(900666979/3125000000)`.
* `r₃  ∈ (1/10, 1/5)`     ascending  — `P(1/5) = 11581677/48828125`.
* `r₄  ∈ (1/5, 3/10)`     descending — `P(3/10) = -(1534706671/6250000000)`.
* `r₅  ∈ (3/10, 9/20)`    ascending  — `P(9/20) = 5516425106321/25600000000000`.
* `r₆  = 1/2`             parity     — odd-degree forces `P(1/2) = 0`.
* `r₇  ∈ (11/20, 7/10)`   ascending  — parity-mirror of (3/10, 9/20).
* `r₈  ∈ (7/10, 4/5)`     descending — parity-mirror of (1/5, 3/10).
* `r₉  ∈ (4/5, 9/10)`     ascending  — parity-mirror of (1/10, 1/5).
* `r₁₀ ∈ (9/10, 49/50)`   descending — parity-mirror of (1/50, 1/10).
* `r₁₁ ∈ (49/50, 1)`      ascending  — parity-mirror of (0, 1/50).

Distinctness (55 pairs) follows from the strict ordering of the brackets:
`(0, 1/50) < (1/50, 1/10) < (1/10, 1/5) < (1/5, 3/10) < (3/10, 9/20) <
 {1/2} < (11/20, 7/10) < (7/10, 4/5) < (4/5, 9/10) < (9/10, 49/50) <
 (49/50, 1)`. -/
theorem butcherShiftedLegendre_eleven_roots :
    ∃ r₁ r₂ r₃ r₄ r₅ r₆ r₇ r₈ r₉ r₁₀ r₁₁ : ℝ,
      r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₁ ≠ r₄ ∧ r₁ ≠ r₅ ∧ r₁ ≠ r₆ ∧ r₁ ≠ r₇ ∧
        r₁ ≠ r₈ ∧ r₁ ≠ r₉ ∧ r₁ ≠ r₁₀ ∧ r₁ ≠ r₁₁ ∧
      r₂ ≠ r₃ ∧ r₂ ≠ r₄ ∧ r₂ ≠ r₅ ∧ r₂ ≠ r₆ ∧ r₂ ≠ r₇ ∧
        r₂ ≠ r₈ ∧ r₂ ≠ r₉ ∧ r₂ ≠ r₁₀ ∧ r₂ ≠ r₁₁ ∧
      r₃ ≠ r₄ ∧ r₃ ≠ r₅ ∧ r₃ ≠ r₆ ∧ r₃ ≠ r₇ ∧
        r₃ ≠ r₈ ∧ r₃ ≠ r₉ ∧ r₃ ≠ r₁₀ ∧ r₃ ≠ r₁₁ ∧
      r₄ ≠ r₅ ∧ r₄ ≠ r₆ ∧ r₄ ≠ r₇ ∧
        r₄ ≠ r₈ ∧ r₄ ≠ r₉ ∧ r₄ ≠ r₁₀ ∧ r₄ ≠ r₁₁ ∧
      r₅ ≠ r₆ ∧ r₅ ≠ r₇ ∧
        r₅ ≠ r₈ ∧ r₅ ≠ r₉ ∧ r₅ ≠ r₁₀ ∧ r₅ ≠ r₁₁ ∧
      r₆ ≠ r₇ ∧ r₆ ≠ r₈ ∧ r₆ ≠ r₉ ∧ r₆ ≠ r₁₀ ∧ r₆ ≠ r₁₁ ∧
      r₇ ≠ r₈ ∧ r₇ ≠ r₉ ∧ r₇ ≠ r₁₀ ∧ r₇ ≠ r₁₁ ∧
      r₈ ≠ r₉ ∧ r₈ ≠ r₁₀ ∧ r₈ ≠ r₁₁ ∧
      r₉ ≠ r₁₀ ∧ r₉ ≠ r₁₁ ∧
      r₁₀ ≠ r₁₁ ∧
      r₁ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₂ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₃ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₄ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₅ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₆ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₇ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₈ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₉ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₁₀ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₁₁ ∈ Set.Ioo (0 : ℝ) 1 ∧
      (butcherShiftedLegendre 11).eval r₁ = 0 ∧
      (butcherShiftedLegendre 11).eval r₂ = 0 ∧
      (butcherShiftedLegendre 11).eval r₃ = 0 ∧
      (butcherShiftedLegendre 11).eval r₄ = 0 ∧
      (butcherShiftedLegendre 11).eval r₅ = 0 ∧
      (butcherShiftedLegendre 11).eval r₆ = 0 ∧
      (butcherShiftedLegendre 11).eval r₇ = 0 ∧
      (butcherShiftedLegendre 11).eval r₈ = 0 ∧
      (butcherShiftedLegendre 11).eval r₉ = 0 ∧
      (butcherShiftedLegendre 11).eval r₁₀ = 0 ∧
      (butcherShiftedLegendre 11).eval r₁₁ = 0 := by
  have hP11 := butcherShiftedLegendre_eleven
  have hcont : Continuous (fun x : ℝ => (butcherShiftedLegendre 11).eval x) :=
    (butcherShiftedLegendre 11).continuous
  -- Twelve key evaluations of `P_11^*` (plus the parity-forced `P(1/2) = 0`).
  have hf_0 : (butcherShiftedLegendre 11).eval (0 : ℝ) = -1 := by
    rw [hP11]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  have hf_1 : (butcherShiftedLegendre 11).eval (1 : ℝ) = 1 := by
    rw [hP11]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_one_fiftieth :
      (butcherShiftedLegendre 11).eval (1 / 50 : ℝ) =
        25826480523788463 / 76293945312500000 := by
    rw [hP11]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_one_tenth :
      (butcherShiftedLegendre 11).eval (1 / 10 : ℝ) =
        -(900666979 / 3125000000) := by
    rw [hP11]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_one_fifth :
      (butcherShiftedLegendre 11).eval (1 / 5 : ℝ) = 11581677 / 48828125 := by
    rw [hP11]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_three_tenths :
      (butcherShiftedLegendre 11).eval (3 / 10 : ℝ) =
        -(1534706671 / 6250000000) := by
    rw [hP11]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_nine_twentieths :
      (butcherShiftedLegendre 11).eval (9 / 20 : ℝ) =
        5516425106321 / 25600000000000 := by
    rw [hP11]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_eleven_twentieths :
      (butcherShiftedLegendre 11).eval (11 / 20 : ℝ) =
        -(5516425106321 / 25600000000000) := by
    rw [hP11]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_seven_tenths :
      (butcherShiftedLegendre 11).eval (7 / 10 : ℝ) = 1534706671 / 6250000000 := by
    rw [hP11]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_four_fifths :
      (butcherShiftedLegendre 11).eval (4 / 5 : ℝ) = -(11581677 / 48828125) := by
    rw [hP11]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_nine_tenths :
      (butcherShiftedLegendre 11).eval (9 / 10 : ℝ) = 900666979 / 3125000000 := by
    rw [hP11]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_forty_nine_fiftieths :
      (butcherShiftedLegendre 11).eval (49 / 50 : ℝ) =
        -(25826480523788463 / 76293945312500000) := by
    rw [hP11]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_half : (butcherShiftedLegendre 11).eval (1 / 2 : ℝ) = 0 :=
    butcherShiftedLegendre_eval_half_eq_zero_of_odd 11 ⟨5, rfl⟩
  -- IVT₁: ascending on `[0, 1/50]`.
  have hivt_1 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 11).eval x) ''
        Set.Ioo (0 : ℝ) (1 / 50) := by
    apply intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1 / 50) hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 11).eval (0 : ℝ))
        ((butcherShiftedLegendre 11).eval (1 / 50 : ℝ))
    rw [hf_0, hf_one_fiftieth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₁, hr₁_mem, hr₁_eval⟩ := hivt_1
  -- IVT₂: descending on `[1/50, 1/10]`.
  have hivt_2 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 11).eval x) ''
        Set.Ioo (1 / 50 : ℝ) (1 / 10) := by
    apply intermediate_value_Ioo' (by norm_num : (1 / 50 : ℝ) ≤ 1 / 10)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 11).eval (1 / 10 : ℝ))
        ((butcherShiftedLegendre 11).eval (1 / 50 : ℝ))
    rw [hf_one_tenth, hf_one_fiftieth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₂, hr₂_mem, hr₂_eval⟩ := hivt_2
  -- IVT₃: ascending on `[1/10, 1/5]`.
  have hivt_3 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 11).eval x) ''
        Set.Ioo (1 / 10 : ℝ) (1 / 5) := by
    apply intermediate_value_Ioo (by norm_num : (1 / 10 : ℝ) ≤ 1 / 5)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 11).eval (1 / 10 : ℝ))
        ((butcherShiftedLegendre 11).eval (1 / 5 : ℝ))
    rw [hf_one_tenth, hf_one_fifth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₃, hr₃_mem, hr₃_eval⟩ := hivt_3
  -- IVT₄: descending on `[1/5, 3/10]`.
  have hivt_4 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 11).eval x) ''
        Set.Ioo (1 / 5 : ℝ) (3 / 10) := by
    apply intermediate_value_Ioo' (by norm_num : (1 / 5 : ℝ) ≤ 3 / 10)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 11).eval (3 / 10 : ℝ))
        ((butcherShiftedLegendre 11).eval (1 / 5 : ℝ))
    rw [hf_three_tenths, hf_one_fifth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₄, hr₄_mem, hr₄_eval⟩ := hivt_4
  -- IVT₅: ascending on `[3/10, 9/20]`.
  have hivt_5 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 11).eval x) ''
        Set.Ioo (3 / 10 : ℝ) (9 / 20) := by
    apply intermediate_value_Ioo (by norm_num : (3 / 10 : ℝ) ≤ 9 / 20)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 11).eval (3 / 10 : ℝ))
        ((butcherShiftedLegendre 11).eval (9 / 20 : ℝ))
    rw [hf_three_tenths, hf_nine_twentieths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₅, hr₅_mem, hr₅_eval⟩ := hivt_5
  -- IVT₇: ascending on `[11/20, 7/10]`.
  have hivt_7 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 11).eval x) ''
        Set.Ioo (11 / 20 : ℝ) (7 / 10) := by
    apply intermediate_value_Ioo (by norm_num : (11 / 20 : ℝ) ≤ 7 / 10)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 11).eval (11 / 20 : ℝ))
        ((butcherShiftedLegendre 11).eval (7 / 10 : ℝ))
    rw [hf_eleven_twentieths, hf_seven_tenths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₇, hr₇_mem, hr₇_eval⟩ := hivt_7
  -- IVT₈: descending on `[7/10, 4/5]`.
  have hivt_8 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 11).eval x) ''
        Set.Ioo (7 / 10 : ℝ) (4 / 5) := by
    apply intermediate_value_Ioo' (by norm_num : (7 / 10 : ℝ) ≤ 4 / 5)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 11).eval (4 / 5 : ℝ))
        ((butcherShiftedLegendre 11).eval (7 / 10 : ℝ))
    rw [hf_four_fifths, hf_seven_tenths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₈, hr₈_mem, hr₈_eval⟩ := hivt_8
  -- IVT₉: ascending on `[4/5, 9/10]`.
  have hivt_9 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 11).eval x) ''
        Set.Ioo (4 / 5 : ℝ) (9 / 10) := by
    apply intermediate_value_Ioo (by norm_num : (4 / 5 : ℝ) ≤ 9 / 10)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 11).eval (4 / 5 : ℝ))
        ((butcherShiftedLegendre 11).eval (9 / 10 : ℝ))
    rw [hf_four_fifths, hf_nine_tenths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₉, hr₉_mem, hr₉_eval⟩ := hivt_9
  -- IVT₁₀: descending on `[9/10, 49/50]`.
  have hivt_10 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 11).eval x) ''
        Set.Ioo (9 / 10 : ℝ) (49 / 50) := by
    apply intermediate_value_Ioo' (by norm_num : (9 / 10 : ℝ) ≤ 49 / 50)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 11).eval (49 / 50 : ℝ))
        ((butcherShiftedLegendre 11).eval (9 / 10 : ℝ))
    rw [hf_forty_nine_fiftieths, hf_nine_tenths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₁₀, hr₁₀_mem, hr₁₀_eval⟩ := hivt_10
  -- IVT₁₁: ascending on `[49/50, 1]`.
  have hivt_11 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 11).eval x) ''
        Set.Ioo (49 / 50 : ℝ) 1 := by
    apply intermediate_value_Ioo (by norm_num : (49 / 50 : ℝ) ≤ 1)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 11).eval (49 / 50 : ℝ))
        ((butcherShiftedLegendre 11).eval (1 : ℝ))
    rw [hf_forty_nine_fiftieths, hf_1]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₁₁, hr₁₁_mem, hr₁₁_eval⟩ := hivt_11
  -- Clear the polynomial-evaluation hypotheses now that the IVT closures are
  -- bound: `linarith` calls below would otherwise scan all 12 large-rational
  -- evaluations and time out on `isDefEq`. Keep `hf_half` (consumed by
  -- `refine`) and all `hrᵢ_eval` / `hrᵢ_mem` (needed downstream).
  clear hP11 hcont hf_0 hf_1 hf_one_fiftieth hf_one_tenth hf_one_fifth
        hf_three_tenths hf_nine_twentieths hf_eleven_twentieths hf_seven_tenths
        hf_four_fifths hf_nine_tenths hf_forty_nine_fiftieths
  refine ⟨r₁, r₂, r₃, r₄, r₅, 1 / 2, r₇, r₈, r₉, r₁₀, r₁₁,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_,
          ?_, ?_, ?_,
          ?_, ?_,
          ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          hr₁_eval, hr₂_eval, hr₃_eval, hr₄_eval, hr₅_eval, hf_half,
          hr₇_eval, hr₈_eval, hr₉_eval, hr₁₀_eval, hr₁₁_eval⟩
  -- 55 distinctness goals (10 + 9 + 8 + 7 + 6 + 5 + 4 + 3 + 2 + 1).
  -- r₁ vs r₂..r₁₁ (10 goals).
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₂_gt, _⟩ := hr₂_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₃_gt, _⟩ := hr₃_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₄_gt, _⟩ := hr₄_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₅_gt, _⟩ := hr₅_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  -- r₂ vs r₃..r₁₁ (9 goals).
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₃_gt, _⟩ := hr₃_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₄_gt, _⟩ := hr₄_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₅_gt, _⟩ := hr₅_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  -- r₃ vs r₄..r₁₁ (8 goals).
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₄_gt, _⟩ := hr₄_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₅_gt, _⟩ := hr₅_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  -- r₄ vs r₅..r₁₁ (7 goals).
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₅_gt, _⟩ := hr₅_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  -- r₅ vs r₆..r₁₁ (6 goals).
  · obtain ⟨_, hr₅_lt⟩ := hr₅_mem
    intro h; linarith
  · obtain ⟨_, hr₅_lt⟩ := hr₅_mem
    obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · obtain ⟨_, hr₅_lt⟩ := hr₅_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₅_lt⟩ := hr₅_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₅_lt⟩ := hr₅_mem
    obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨_, hr₅_lt⟩ := hr₅_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  -- r₆ = 1/2 vs r₇..r₁₁ (5 goals).
  · obtain ⟨hr₇_gt, _⟩ := hr₇_mem
    intro h; linarith
  · obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  -- r₇ vs r₈..r₁₁ (4 goals).
  · obtain ⟨_, hr₇_lt⟩ := hr₇_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₇_lt⟩ := hr₇_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₇_lt⟩ := hr₇_mem
    obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨_, hr₇_lt⟩ := hr₇_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  -- r₈ vs r₉..r₁₁ (3 goals).
  · obtain ⟨_, hr₈_lt⟩ := hr₈_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₈_lt⟩ := hr₈_mem
    obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨_, hr₈_lt⟩ := hr₈_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  -- r₉ vs r₁₀, r₁₁ (2 goals).
  · obtain ⟨_, hr₉_lt⟩ := hr₉_mem
    obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨_, hr₉_lt⟩ := hr₉_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  -- r₁₀ vs r₁₁ (1 goal).
  · obtain ⟨_, hr₁₀_lt⟩ := hr₁₀_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  -- 11 Ioo (0, 1) membership goals.
  · obtain ⟨hgt, hlt⟩ := hr₁_mem
    exact ⟨hgt, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₂_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₃_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₄_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₅_mem
    exact ⟨by linarith, by linarith⟩
  · refine ⟨?_, ?_⟩ <;> norm_num
  · obtain ⟨hgt, hlt⟩ := hr₇_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₈_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₉_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₁₀_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₁₁_mem
    exact ⟨by linarith, hlt⟩

/-! ### Empirical anchor (342g) at `n = 13`

Mechanical extension of cycle 299's `butcherShiftedLegendre_eleven_roots`
recipe to thirteen roots, using cycle 300's closed form
`butcherShiftedLegendre_thirteen` and cycle 295's parity helper
`butcherShiftedLegendre_eval_half_eq_zero_of_odd` witnessed by
`13 = 2*6 + 1` (i.e. `⟨6, rfl⟩`). -/

/-- (342g) at `n = 13` — empirical anchor: `P_13^*` has thirteen distinct
real zeros in the open interval `(0, 1)`. Strictly weaker than the general
(342g) statement (`∀ n`, currently held by Aristotle project
`5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`, 30% as of cycle 300), but
axiom-clean and unconditional.

Bracket plan (each endpoint sign hand-verified via Python `Fraction` in
cycle 300):
* `r₁  ∈ (0, 1/100)`       ascending  — `P(0) = -1`, `P(1/100) > 0`.
* `r₂  ∈ (1/100, 1/20)`    descending — `P(1/20) < 0`.
* `r₃  ∈ (1/20, 1/10)`     ascending  — `P(1/10) > 0`.
* `r₄  ∈ (1/10, 1/5)`      descending — `P(1/5) < 0`.
* `r₅  ∈ (1/5, 3/10)`      ascending  — `P(3/10) > 0`.
* `r₆  ∈ (3/10, 2/5)`      descending — `P(2/5) < 0`.
* `r₇  = 1/2`              parity     — odd-degree forces `P(1/2) = 0`.
* `r₈  ∈ (3/5, 7/10)`      descending — parity-mirror of (3/10, 2/5).
* `r₉  ∈ (7/10, 4/5)`      ascending  — parity-mirror of (1/5, 3/10).
* `r₁₀ ∈ (4/5, 9/10)`      descending — parity-mirror of (1/10, 1/5).
* `r₁₁ ∈ (9/10, 19/20)`    ascending  — parity-mirror of (1/20, 1/10).
* `r₁₂ ∈ (19/20, 99/100)`  descending — parity-mirror of (1/100, 1/20).
* `r₁₃ ∈ (99/100, 1)`      ascending  — parity-mirror of (0, 1/100).

Distinctness (78 pairs) follows from the strict ordering of the brackets.
The mandatory pre-`refine` `clear` (cycle 299 discovery) drops the
large-rational `hf_*` evaluation hypotheses; without it, `linarith` times
out during `isDefEq` preprocessing on the 24-digit outer-bracket
denominators (`5 × 10²³`). -/
theorem butcherShiftedLegendre_thirteen_roots :
    ∃ r₁ r₂ r₃ r₄ r₅ r₆ r₇ r₈ r₉ r₁₀ r₁₁ r₁₂ r₁₃ : ℝ,
      r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₁ ≠ r₄ ∧ r₁ ≠ r₅ ∧ r₁ ≠ r₆ ∧ r₁ ≠ r₇ ∧
        r₁ ≠ r₈ ∧ r₁ ≠ r₉ ∧ r₁ ≠ r₁₀ ∧ r₁ ≠ r₁₁ ∧ r₁ ≠ r₁₂ ∧ r₁ ≠ r₁₃ ∧
      r₂ ≠ r₃ ∧ r₂ ≠ r₄ ∧ r₂ ≠ r₅ ∧ r₂ ≠ r₆ ∧ r₂ ≠ r₇ ∧
        r₂ ≠ r₈ ∧ r₂ ≠ r₉ ∧ r₂ ≠ r₁₀ ∧ r₂ ≠ r₁₁ ∧ r₂ ≠ r₁₂ ∧ r₂ ≠ r₁₃ ∧
      r₃ ≠ r₄ ∧ r₃ ≠ r₅ ∧ r₃ ≠ r₆ ∧ r₃ ≠ r₇ ∧
        r₃ ≠ r₈ ∧ r₃ ≠ r₉ ∧ r₃ ≠ r₁₀ ∧ r₃ ≠ r₁₁ ∧ r₃ ≠ r₁₂ ∧ r₃ ≠ r₁₃ ∧
      r₄ ≠ r₅ ∧ r₄ ≠ r₆ ∧ r₄ ≠ r₇ ∧
        r₄ ≠ r₈ ∧ r₄ ≠ r₉ ∧ r₄ ≠ r₁₀ ∧ r₄ ≠ r₁₁ ∧ r₄ ≠ r₁₂ ∧ r₄ ≠ r₁₃ ∧
      r₅ ≠ r₆ ∧ r₅ ≠ r₇ ∧
        r₅ ≠ r₈ ∧ r₅ ≠ r₉ ∧ r₅ ≠ r₁₀ ∧ r₅ ≠ r₁₁ ∧ r₅ ≠ r₁₂ ∧ r₅ ≠ r₁₃ ∧
      r₆ ≠ r₇ ∧
        r₆ ≠ r₈ ∧ r₆ ≠ r₉ ∧ r₆ ≠ r₁₀ ∧ r₆ ≠ r₁₁ ∧ r₆ ≠ r₁₂ ∧ r₆ ≠ r₁₃ ∧
      r₇ ≠ r₈ ∧ r₇ ≠ r₉ ∧ r₇ ≠ r₁₀ ∧ r₇ ≠ r₁₁ ∧ r₇ ≠ r₁₂ ∧ r₇ ≠ r₁₃ ∧
      r₈ ≠ r₉ ∧ r₈ ≠ r₁₀ ∧ r₈ ≠ r₁₁ ∧ r₈ ≠ r₁₂ ∧ r₈ ≠ r₁₃ ∧
      r₉ ≠ r₁₀ ∧ r₉ ≠ r₁₁ ∧ r₉ ≠ r₁₂ ∧ r₉ ≠ r₁₃ ∧
      r₁₀ ≠ r₁₁ ∧ r₁₀ ≠ r₁₂ ∧ r₁₀ ≠ r₁₃ ∧
      r₁₁ ≠ r₁₂ ∧ r₁₁ ≠ r₁₃ ∧
      r₁₂ ≠ r₁₃ ∧
      r₁ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₂ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₃ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₄ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₅ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₆ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₇ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₈ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₉ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₁₀ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₁₁ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₁₂ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₁₃ ∈ Set.Ioo (0 : ℝ) 1 ∧
      (butcherShiftedLegendre 13).eval r₁ = 0 ∧
      (butcherShiftedLegendre 13).eval r₂ = 0 ∧
      (butcherShiftedLegendre 13).eval r₃ = 0 ∧
      (butcherShiftedLegendre 13).eval r₄ = 0 ∧
      (butcherShiftedLegendre 13).eval r₅ = 0 ∧
      (butcherShiftedLegendre 13).eval r₆ = 0 ∧
      (butcherShiftedLegendre 13).eval r₇ = 0 ∧
      (butcherShiftedLegendre 13).eval r₈ = 0 ∧
      (butcherShiftedLegendre 13).eval r₉ = 0 ∧
      (butcherShiftedLegendre 13).eval r₁₀ = 0 ∧
      (butcherShiftedLegendre 13).eval r₁₁ = 0 ∧
      (butcherShiftedLegendre 13).eval r₁₂ = 0 ∧
      (butcherShiftedLegendre 13).eval r₁₃ = 0 := by
  have hP13 := butcherShiftedLegendre_thirteen
  have hcont : Continuous (fun x : ℝ => (butcherShiftedLegendre 13).eval x) :=
    (butcherShiftedLegendre 13).continuous
  -- 14 key evaluations of `P_13^*` (plus the parity-forced `P(1/2) = 0`).
  have hf_0 : (butcherShiftedLegendre 13).eval (0 : ℝ) = -1 := by
    rw [hP13]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  have hf_1 : (butcherShiftedLegendre 13).eval (1 : ℝ) = 1 := by
    rw [hP13]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_one_hundredth :
      (butcherShiftedLegendre 13).eval (1 / 100 : ℝ) =
        72600223747219836831653 / 500000000000000000000000 := by
    rw [hP13]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_one_twentieth :
      (butcherShiftedLegendre 13).eval (1 / 20 : ℝ) =
        -(72827093664963 / 409600000000000) := by
    rw [hP13]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_one_tenth :
      (butcherShiftedLegendre 13).eval (1 / 10 : ℝ) =
        124739261 / 12500000000 := by
    rw [hP13]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_one_fifth :
      (butcherShiftedLegendre 13).eval (1 / 5 : ℝ) =
        -(7906779 / 48828125) := by
    rw [hP13]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_three_tenths :
      (butcherShiftedLegendre 13).eval (3 / 10 : ℝ) =
        3753374453 / 25000000000 := by
    rw [hP13]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_two_fifths :
      (butcherShiftedLegendre 13).eval (2 / 5 : ℝ) =
        -(4379881 / 48828125) := by
    rw [hP13]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_three_fifths :
      (butcherShiftedLegendre 13).eval (3 / 5 : ℝ) =
        4379881 / 48828125 := by
    rw [hP13]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_seven_tenths :
      (butcherShiftedLegendre 13).eval (7 / 10 : ℝ) =
        -(3753374453 / 25000000000) := by
    rw [hP13]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_four_fifths :
      (butcherShiftedLegendre 13).eval (4 / 5 : ℝ) =
        7906779 / 48828125 := by
    rw [hP13]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_nine_tenths :
      (butcherShiftedLegendre 13).eval (9 / 10 : ℝ) =
        -(124739261 / 12500000000) := by
    rw [hP13]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_nineteen_twentieths :
      (butcherShiftedLegendre 13).eval (19 / 20 : ℝ) =
        72827093664963 / 409600000000000 := by
    rw [hP13]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_ninety_nine_hundredths :
      (butcherShiftedLegendre 13).eval (99 / 100 : ℝ) =
        -(72600223747219836831653 / 500000000000000000000000) := by
    rw [hP13]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  have hf_half : (butcherShiftedLegendre 13).eval (1 / 2 : ℝ) = 0 :=
    butcherShiftedLegendre_eval_half_eq_zero_of_odd 13 ⟨6, rfl⟩
  -- IVT₁: ascending on `[0, 1/100]`.
  have hivt_1 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 13).eval x) ''
        Set.Ioo (0 : ℝ) (1 / 100) := by
    apply intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1 / 100) hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 13).eval (0 : ℝ))
        ((butcherShiftedLegendre 13).eval (1 / 100 : ℝ))
    rw [hf_0, hf_one_hundredth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₁, hr₁_mem, hr₁_eval⟩ := hivt_1
  -- IVT₂: descending on `[1/100, 1/20]`.
  have hivt_2 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 13).eval x) ''
        Set.Ioo (1 / 100 : ℝ) (1 / 20) := by
    apply intermediate_value_Ioo' (by norm_num : (1 / 100 : ℝ) ≤ 1 / 20)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 13).eval (1 / 20 : ℝ))
        ((butcherShiftedLegendre 13).eval (1 / 100 : ℝ))
    rw [hf_one_twentieth, hf_one_hundredth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₂, hr₂_mem, hr₂_eval⟩ := hivt_2
  -- IVT₃: ascending on `[1/20, 1/10]`.
  have hivt_3 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 13).eval x) ''
        Set.Ioo (1 / 20 : ℝ) (1 / 10) := by
    apply intermediate_value_Ioo (by norm_num : (1 / 20 : ℝ) ≤ 1 / 10)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 13).eval (1 / 20 : ℝ))
        ((butcherShiftedLegendre 13).eval (1 / 10 : ℝ))
    rw [hf_one_twentieth, hf_one_tenth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₃, hr₃_mem, hr₃_eval⟩ := hivt_3
  -- IVT₄: descending on `[1/10, 1/5]`.
  have hivt_4 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 13).eval x) ''
        Set.Ioo (1 / 10 : ℝ) (1 / 5) := by
    apply intermediate_value_Ioo' (by norm_num : (1 / 10 : ℝ) ≤ 1 / 5)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 13).eval (1 / 5 : ℝ))
        ((butcherShiftedLegendre 13).eval (1 / 10 : ℝ))
    rw [hf_one_fifth, hf_one_tenth]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₄, hr₄_mem, hr₄_eval⟩ := hivt_4
  -- IVT₅: ascending on `[1/5, 3/10]`.
  have hivt_5 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 13).eval x) ''
        Set.Ioo (1 / 5 : ℝ) (3 / 10) := by
    apply intermediate_value_Ioo (by norm_num : (1 / 5 : ℝ) ≤ 3 / 10)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 13).eval (1 / 5 : ℝ))
        ((butcherShiftedLegendre 13).eval (3 / 10 : ℝ))
    rw [hf_one_fifth, hf_three_tenths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₅, hr₅_mem, hr₅_eval⟩ := hivt_5
  -- IVT₆: descending on `[3/10, 2/5]`.
  have hivt_6 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 13).eval x) ''
        Set.Ioo (3 / 10 : ℝ) (2 / 5) := by
    apply intermediate_value_Ioo' (by norm_num : (3 / 10 : ℝ) ≤ 2 / 5)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 13).eval (2 / 5 : ℝ))
        ((butcherShiftedLegendre 13).eval (3 / 10 : ℝ))
    rw [hf_two_fifths, hf_three_tenths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₆, hr₆_mem, hr₆_eval⟩ := hivt_6
  -- IVT₈: descending on `[3/5, 7/10]`.
  have hivt_8 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 13).eval x) ''
        Set.Ioo (3 / 5 : ℝ) (7 / 10) := by
    apply intermediate_value_Ioo' (by norm_num : (3 / 5 : ℝ) ≤ 7 / 10)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 13).eval (7 / 10 : ℝ))
        ((butcherShiftedLegendre 13).eval (3 / 5 : ℝ))
    rw [hf_seven_tenths, hf_three_fifths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₈, hr₈_mem, hr₈_eval⟩ := hivt_8
  -- IVT₉: ascending on `[7/10, 4/5]`.
  have hivt_9 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 13).eval x) ''
        Set.Ioo (7 / 10 : ℝ) (4 / 5) := by
    apply intermediate_value_Ioo (by norm_num : (7 / 10 : ℝ) ≤ 4 / 5)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 13).eval (7 / 10 : ℝ))
        ((butcherShiftedLegendre 13).eval (4 / 5 : ℝ))
    rw [hf_seven_tenths, hf_four_fifths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₉, hr₉_mem, hr₉_eval⟩ := hivt_9
  -- IVT₁₀: descending on `[4/5, 9/10]`.
  have hivt_10 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 13).eval x) ''
        Set.Ioo (4 / 5 : ℝ) (9 / 10) := by
    apply intermediate_value_Ioo' (by norm_num : (4 / 5 : ℝ) ≤ 9 / 10)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 13).eval (9 / 10 : ℝ))
        ((butcherShiftedLegendre 13).eval (4 / 5 : ℝ))
    rw [hf_nine_tenths, hf_four_fifths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₁₀, hr₁₀_mem, hr₁₀_eval⟩ := hivt_10
  -- IVT₁₁: ascending on `[9/10, 19/20]`.
  have hivt_11 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 13).eval x) ''
        Set.Ioo (9 / 10 : ℝ) (19 / 20) := by
    apply intermediate_value_Ioo (by norm_num : (9 / 10 : ℝ) ≤ 19 / 20)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 13).eval (9 / 10 : ℝ))
        ((butcherShiftedLegendre 13).eval (19 / 20 : ℝ))
    rw [hf_nine_tenths, hf_nineteen_twentieths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₁₁, hr₁₁_mem, hr₁₁_eval⟩ := hivt_11
  -- IVT₁₂: descending on `[19/20, 99/100]`.
  have hivt_12 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 13).eval x) ''
        Set.Ioo (19 / 20 : ℝ) (99 / 100) := by
    apply intermediate_value_Ioo' (by norm_num : (19 / 20 : ℝ) ≤ 99 / 100)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 13).eval (99 / 100 : ℝ))
        ((butcherShiftedLegendre 13).eval (19 / 20 : ℝ))
    rw [hf_ninety_nine_hundredths, hf_nineteen_twentieths]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₁₂, hr₁₂_mem, hr₁₂_eval⟩ := hivt_12
  -- IVT₁₃: ascending on `[99/100, 1]`.
  have hivt_13 :
      (0 : ℝ) ∈ (fun x : ℝ => (butcherShiftedLegendre 13).eval x) ''
        Set.Ioo (99 / 100 : ℝ) 1 := by
    apply intermediate_value_Ioo (by norm_num : (99 / 100 : ℝ) ≤ 1)
      hcont.continuousOn
    show (0 : ℝ) ∈
      Set.Ioo ((butcherShiftedLegendre 13).eval (99 / 100 : ℝ))
        ((butcherShiftedLegendre 13).eval (1 : ℝ))
    rw [hf_ninety_nine_hundredths, hf_1]
    refine ⟨?_, ?_⟩ <;> norm_num
  obtain ⟨r₁₃, hr₁₃_mem, hr₁₃_eval⟩ := hivt_13
  -- Clear the polynomial-evaluation hypotheses before the distinctness block:
  -- without this `linarith` would scan all 14 large-rational `hf_*`
  -- evaluations and time out on `isDefEq` (cycle 299 discovery; the 24-digit
  -- outer-bracket denominators make the timeout effectively guaranteed).
  clear hP13 hcont hf_0 hf_1 hf_one_hundredth hf_one_twentieth hf_one_tenth
        hf_one_fifth hf_three_tenths hf_two_fifths hf_three_fifths
        hf_seven_tenths hf_four_fifths hf_nine_tenths hf_nineteen_twentieths
        hf_ninety_nine_hundredths
  refine ⟨r₁, r₂, r₃, r₄, r₅, r₆, 1 / 2, r₈, r₉, r₁₀, r₁₁, r₁₂, r₁₃,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_,
          ?_, ?_, ?_,
          ?_, ?_,
          ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          hr₁_eval, hr₂_eval, hr₃_eval, hr₄_eval, hr₅_eval, hr₆_eval, hf_half,
          hr₈_eval, hr₉_eval, hr₁₀_eval, hr₁₁_eval, hr₁₂_eval, hr₁₃_eval⟩
  -- 78 distinctness goals (12 + 11 + 10 + 9 + 8 + 7 + 6 + 5 + 4 + 3 + 2 + 1).
  -- r₁ vs r₂..r₁₃ (12 goals).
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₂_gt, _⟩ := hr₂_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₃_gt, _⟩ := hr₃_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₄_gt, _⟩ := hr₄_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₅_gt, _⟩ := hr₅_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₆_gt, _⟩ := hr₆_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₁₂_gt, _⟩ := hr₁₂_mem
    intro h; linarith
  · obtain ⟨_, hr₁_lt⟩ := hr₁_mem
    obtain ⟨hr₁₃_gt, _⟩ := hr₁₃_mem
    intro h; linarith
  -- r₂ vs r₃..r₁₃ (11 goals).
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₃_gt, _⟩ := hr₃_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₄_gt, _⟩ := hr₄_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₅_gt, _⟩ := hr₅_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₆_gt, _⟩ := hr₆_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₁₂_gt, _⟩ := hr₁₂_mem
    intro h; linarith
  · obtain ⟨_, hr₂_lt⟩ := hr₂_mem
    obtain ⟨hr₁₃_gt, _⟩ := hr₁₃_mem
    intro h; linarith
  -- r₃ vs r₄..r₁₃ (10 goals).
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₄_gt, _⟩ := hr₄_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₅_gt, _⟩ := hr₅_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₆_gt, _⟩ := hr₆_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₁₂_gt, _⟩ := hr₁₂_mem
    intro h; linarith
  · obtain ⟨_, hr₃_lt⟩ := hr₃_mem
    obtain ⟨hr₁₃_gt, _⟩ := hr₁₃_mem
    intro h; linarith
  -- r₄ vs r₅..r₁₃ (9 goals).
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₅_gt, _⟩ := hr₅_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₆_gt, _⟩ := hr₆_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₁₂_gt, _⟩ := hr₁₂_mem
    intro h; linarith
  · obtain ⟨_, hr₄_lt⟩ := hr₄_mem
    obtain ⟨hr₁₃_gt, _⟩ := hr₁₃_mem
    intro h; linarith
  -- r₅ vs r₆..r₁₃ (8 goals).
  · obtain ⟨_, hr₅_lt⟩ := hr₅_mem
    obtain ⟨hr₆_gt, _⟩ := hr₆_mem
    intro h; linarith
  · obtain ⟨_, hr₅_lt⟩ := hr₅_mem
    intro h; linarith
  · obtain ⟨_, hr₅_lt⟩ := hr₅_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₅_lt⟩ := hr₅_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₅_lt⟩ := hr₅_mem
    obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨_, hr₅_lt⟩ := hr₅_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  · obtain ⟨_, hr₅_lt⟩ := hr₅_mem
    obtain ⟨hr₁₂_gt, _⟩ := hr₁₂_mem
    intro h; linarith
  · obtain ⟨_, hr₅_lt⟩ := hr₅_mem
    obtain ⟨hr₁₃_gt, _⟩ := hr₁₃_mem
    intro h; linarith
  -- r₆ vs r₇..r₁₃ (7 goals).
  · obtain ⟨_, hr₆_lt⟩ := hr₆_mem
    intro h; linarith
  · obtain ⟨_, hr₆_lt⟩ := hr₆_mem
    obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨_, hr₆_lt⟩ := hr₆_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₆_lt⟩ := hr₆_mem
    obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨_, hr₆_lt⟩ := hr₆_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  · obtain ⟨_, hr₆_lt⟩ := hr₆_mem
    obtain ⟨hr₁₂_gt, _⟩ := hr₁₂_mem
    intro h; linarith
  · obtain ⟨_, hr₆_lt⟩ := hr₆_mem
    obtain ⟨hr₁₃_gt, _⟩ := hr₁₃_mem
    intro h; linarith
  -- r₇ = 1/2 vs r₈..r₁₃ (6 goals).
  · obtain ⟨hr₈_gt, _⟩ := hr₈_mem
    intro h; linarith
  · obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  · obtain ⟨hr₁₂_gt, _⟩ := hr₁₂_mem
    intro h; linarith
  · obtain ⟨hr₁₃_gt, _⟩ := hr₁₃_mem
    intro h; linarith
  -- r₈ vs r₉..r₁₃ (5 goals).
  · obtain ⟨_, hr₈_lt⟩ := hr₈_mem
    obtain ⟨hr₉_gt, _⟩ := hr₉_mem
    intro h; linarith
  · obtain ⟨_, hr₈_lt⟩ := hr₈_mem
    obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨_, hr₈_lt⟩ := hr₈_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  · obtain ⟨_, hr₈_lt⟩ := hr₈_mem
    obtain ⟨hr₁₂_gt, _⟩ := hr₁₂_mem
    intro h; linarith
  · obtain ⟨_, hr₈_lt⟩ := hr₈_mem
    obtain ⟨hr₁₃_gt, _⟩ := hr₁₃_mem
    intro h; linarith
  -- r₉ vs r₁₀..r₁₃ (4 goals).
  · obtain ⟨_, hr₉_lt⟩ := hr₉_mem
    obtain ⟨hr₁₀_gt, _⟩ := hr₁₀_mem
    intro h; linarith
  · obtain ⟨_, hr₉_lt⟩ := hr₉_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  · obtain ⟨_, hr₉_lt⟩ := hr₉_mem
    obtain ⟨hr₁₂_gt, _⟩ := hr₁₂_mem
    intro h; linarith
  · obtain ⟨_, hr₉_lt⟩ := hr₉_mem
    obtain ⟨hr₁₃_gt, _⟩ := hr₁₃_mem
    intro h; linarith
  -- r₁₀ vs r₁₁..r₁₃ (3 goals).
  · obtain ⟨_, hr₁₀_lt⟩ := hr₁₀_mem
    obtain ⟨hr₁₁_gt, _⟩ := hr₁₁_mem
    intro h; linarith
  · obtain ⟨_, hr₁₀_lt⟩ := hr₁₀_mem
    obtain ⟨hr₁₂_gt, _⟩ := hr₁₂_mem
    intro h; linarith
  · obtain ⟨_, hr₁₀_lt⟩ := hr₁₀_mem
    obtain ⟨hr₁₃_gt, _⟩ := hr₁₃_mem
    intro h; linarith
  -- r₁₁ vs r₁₂, r₁₃ (2 goals).
  · obtain ⟨_, hr₁₁_lt⟩ := hr₁₁_mem
    obtain ⟨hr₁₂_gt, _⟩ := hr₁₂_mem
    intro h; linarith
  · obtain ⟨_, hr₁₁_lt⟩ := hr₁₁_mem
    obtain ⟨hr₁₃_gt, _⟩ := hr₁₃_mem
    intro h; linarith
  -- r₁₂ vs r₁₃ (1 goal).
  · obtain ⟨_, hr₁₂_lt⟩ := hr₁₂_mem
    obtain ⟨hr₁₃_gt, _⟩ := hr₁₃_mem
    intro h; linarith
  -- 13 Ioo (0, 1) membership goals.
  · obtain ⟨hgt, hlt⟩ := hr₁_mem
    exact ⟨hgt, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₂_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₃_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₄_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₅_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₆_mem
    exact ⟨by linarith, by linarith⟩
  · refine ⟨?_, ?_⟩ <;> norm_num
  · obtain ⟨hgt, hlt⟩ := hr₈_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₉_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₁₀_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₁₁_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₁₂_mem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hgt, hlt⟩ := hr₁₃_mem
    exact ⟨by linarith, hlt⟩

/-! ### (342g) — `P_n^*` has `n` distinct real zeros in `(0, 1)`

The remainder of this section closes the seventh and last clause of
`lem:342A` (clause (342g)) at full generality: the shifted Legendre
polynomial `P_n^*` has exactly `n` distinct real zeros in the open
interval `(0, 1)`, for every `n : ℕ`.

The textbook strategy (Butcher, p. 236) is a sign-change contradiction
on the orthogonality clause (342a) — equivalently, on its strengthened
form `butcherShiftedLegendre_orthogonal_to_lower_degree` (cycle 292).
If `P_n^*` had fewer than `n` odd-multiplicity zeros in `(0, 1)`,
collecting them into a polynomial `Q = ∏ (X − C xᵢ)` of `natDegree < n`
would force `P_n^* · Q = Q² · R` for some `R` with only even-multiplicity
zeros in `(0,1)`, hence `R` has constant sign on `[0, 1]` (by IVT on
the residual factor) and `P_n^* · Q` has constant non-zero sign. But
then `∫₀¹ P_n^* · Q ≠ 0`, contradicting `_orthogonal_to_lower_degree`.

The generic sign-change / polynomial machinery lives in
`OpenMath.Chapter3.Section342DistinctRootsHelpers` (mirrors the cycle
281 `Section342NormSqHelpers.lean` extraction pattern). Here we
specialise it to `butcherShiftedLegendre n`.

This closure was produced by Aristotle (cycle 301, project
`5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`); the proof reproduced below
has been adapted (namespace + import refactoring; replaced the
`Irreducible.coprime_iff_not_dvd` path with the more direct
`Polynomial.isCoprime_X_sub_C_of_isUnit_sub` to remove a spurious
`IsBezout` synth requirement) and verified to compile without any
heartbeat bump above the project default of 200000. -/

open OpenMath.Chapter3.Section342DistinctRootsHelpers

/-- `P_n^*` is not the zero polynomial (immediate from
`butcherShiftedLegendre_eval_one n : P_n^*(1) = 1 ≠ 0`). -/
theorem butcherShiftedLegendre_ne_zero (n : ℕ) :
    butcherShiftedLegendre n ≠ 0 := by
  intro h
  have h1 := butcherShiftedLegendre_eval_one n
  rw [h] at h1
  simp at h1

/-- The Finset of distinct real roots of `P_n^*` that lie in the open
interval `(0, 1)`. -/
noncomputable def butcherShiftedLegendre_rootsInIoo (n : ℕ) : Finset ℝ :=
  (butcherShiftedLegendre n).roots.toFinset.filter
    (fun x => x ∈ Set.Ioo (0 : ℝ) 1)

/-- Every element of `butcherShiftedLegendre_rootsInIoo n` lies in
`(0, 1)`. -/
lemma butcherShiftedLegendre_rootsInIoo_subset (n : ℕ) :
    ∀ x ∈ butcherShiftedLegendre_rootsInIoo n, x ∈ Set.Ioo (0 : ℝ) 1 := by
  intro x hx
  simp only [butcherShiftedLegendre_rootsInIoo, Finset.mem_filter] at hx
  exact hx.2

/-- Every element of `butcherShiftedLegendre_rootsInIoo n` is a root of
`P_n^*`. -/
lemma butcherShiftedLegendre_rootsInIoo_are_roots (n : ℕ) :
    ∀ x ∈ butcherShiftedLegendre_rootsInIoo n,
      (butcherShiftedLegendre n).eval x = 0 := by
  intro x hx
  simp only [butcherShiftedLegendre_rootsInIoo, Finset.mem_filter,
             Multiset.mem_toFinset] at hx
  exact (mem_roots (butcherShiftedLegendre_ne_zero n)).mp hx.1

/-- **Butcher §342 (342g), upper bound** — the number of roots of
`P_n^*` in `(0, 1)` is at most `n`. Refines
`butcherShiftedLegendre_card_roots_le` (cycle 294) to the open-interval
filter. -/
lemma butcherShiftedLegendre_rootsInIoo_card_le (n : ℕ) :
    (butcherShiftedLegendre_rootsInIoo n).card ≤ n := by
  calc (butcherShiftedLegendre_rootsInIoo n).card
      ≤ (butcherShiftedLegendre n).roots.toFinset.card :=
        Finset.card_filter_le _ _
    _ ≤ (butcherShiftedLegendre n).roots.card :=
        Multiset.toFinset_card_le _
    _ ≤ (butcherShiftedLegendre n).natDegree :=
        Polynomial.card_roots' _
    _ = n := butcherShiftedLegendre_natDegree n

/-- **Butcher §342 (342g), lower bound** — the number of roots of
`P_n^*` in `(0, 1)` is at least `n`.

This is the **key** half of (342g), proved by sign-change contradiction
on `butcherShiftedLegendre_orthogonal_to_lower_degree` (cycle 292).
Aristotle integrated cycle 301. -/
theorem butcherShiftedLegendre_rootsInIoo_card_ge (n : ℕ) :
    n ≤ (butcherShiftedLegendre_rootsInIoo n).card := by
  apply le_of_not_gt
  intro h
  set S := ((butcherShiftedLegendre n).roots.toFinset.filter
              (fun x => x ∈ Set.Ioo (0 : ℝ) 1)).filter
              (fun x => Odd ((butcherShiftedLegendre n).rootMultiplicity x))
            with hS_def
  have hS_card : S.card < n := by
    refine lt_of_le_of_lt (Finset.card_le_card ?_) h
    exact Finset.filter_subset _ _
  set Q : Polynomial ℝ := S.prod (fun r => Polynomial.X - Polynomial.C r)
    with hQ_def
  have hQ_div : Q ∣ butcherShiftedLegendre n := by
    apply prod_linear_factors_dvd_of_roots
    aesop
  have hQ_natDegree : Q.natDegree < n := by
    rw [Polynomial.natDegree_prod _ _ fun x _ => Polynomial.X_sub_C_ne_zero x]
    aesop
  obtain ⟨R, hR⟩ : ∃ R : Polynomial ℝ, butcherShiftedLegendre n = Q * R :=
    hQ_div
  have hR_natDegree : R.natDegree = n - S.card := by
    have hR_natDegree : R.natDegree + Q.natDegree = n := by
      rw [add_comm, ← Polynomial.natDegree_mul'] <;> norm_num [hR]
      · rw [← hR, butcherShiftedLegendre_natDegree]
      · exact ⟨Finset.prod_ne_zero_iff.mpr
                fun x _ => Polynomial.X_sub_C_ne_zero x,
              by rintro rfl
                 exact absurd hR <| by
                   exact ne_of_apply_ne (Polynomial.eval 1) <| by
                     norm_num [butcherShiftedLegendre_eval_one]⟩
    rw [show Q.natDegree = S.card from ?_] at hR_natDegree
    · omega
    rw [Polynomial.natDegree_prod _ _ fun x _ => Polynomial.X_sub_C_ne_zero x,
        Finset.sum_congr rfl fun x _ => Polynomial.natDegree_X_sub_C _]
    norm_num
  have hR_eval_zero : R.eval 0 ≠ 0 := by
    intro hR_zero
    have h_contra : (butcherShiftedLegendre n).eval 0 = 0 := by
      simp [hR, hR_zero]
    exact absurd h_contra
      (by rw [butcherShiftedLegendre_eval_zero]; positivity)
  have hR_eval_one : R.eval 1 ≠ 0 := by
    intro hR_eval_one_zero
    have h_contra : (butcherShiftedLegendre n).eval 1 = 0 := by
      rw [hR, Polynomial.eval_mul, hR_eval_one_zero, MulZeroClass.mul_zero]
    exact absurd h_contra (by rw [butcherShiftedLegendre_eval_one]; norm_num)
  have hR_even_mult_roots :
      ∀ r ∈ Set.Ioo (0 : ℝ) 1, Even (R.rootMultiplicity r) := by
    intro r hr
    have h_root_multiplicity :
        rootMultiplicity r (butcherShiftedLegendre n) =
          rootMultiplicity r Q + rootMultiplicity r R := by
      rw [hR, rootMultiplicity_mul]
      exact hR ▸ butcherShiftedLegendre_ne_zero n
    by_cases hrS : r ∈ S <;> simp +decide at h_root_multiplicity ⊢
    · have h_root_multiplicity_Q : rootMultiplicity r Q = 1 := by
        rw [hQ_def, rootMultiplicity_eq_multiplicity]
        rw [if_neg <| Finset.prod_ne_zero_iff.mpr
              fun x _ => Polynomial.X_sub_C_ne_zero x,
            multiplicity_eq_of_dvd_of_not_dvd]
        · exact dvd_trans (by norm_num) (Finset.dvd_prod_of_mem _ hrS)
        · rw [Finset.prod_eq_prod_diff_singleton_mul hrS]
          rw [pow_add, pow_one,
              mul_dvd_mul_iff_right (Polynomial.X_sub_C_ne_zero r)]
          rw [Polynomial.dvd_iff_isRoot]
          simp +decide [Polynomial.eval_prod, Finset.prod_eq_zero_iff,
                        sub_eq_zero]
      grind
    · by_cases hr_root : r ∈ (butcherShiftedLegendre n).roots.toFinset <;>
        simp +decide at hrS ⊢
      · simp +zetaDelta at *
        rw [h_root_multiplicity] at hrS
        rw [rootMultiplicity_eq_zero] at hrS <;> norm_num at hrS ⊢
        · exact hrS hr_root.1 hr_root.2 hr.1 hr.2
        · rw [Polynomial.eval_prod]
          simp +decide [Finset.prod_eq_zero_iff, sub_eq_zero]
          grind +locals
      · simp +zetaDelta at *
        rw [rootMultiplicity_eq_zero] <;>
          norm_num [hr_root (butcherShiftedLegendre_ne_zero n)]
        intro h
        specialize hr_root (butcherShiftedLegendre_ne_zero n)
        simp_all +singlePass
  have hR_ne_zero : R ≠ 0 := by
    rintro rfl
    simp_all +decide
  have hR_constant_sign :
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ R.eval x) ∨
      (∀ x ∈ Set.Icc (0 : ℝ) 1, R.eval x ≤ 0) := by
    exact poly_constant_sign_of_even_mult_roots R hR_ne_zero
      hR_eval_zero hR_eval_one hR_even_mult_roots
  have h_integrand_constant_sign :
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (butcherShiftedLegendre n).eval x * Q.eval x) ∨
      (∀ x ∈ Set.Icc (0 : ℝ) 1, (butcherShiftedLegendre n).eval x * Q.eval x ≤ 0) := by
    rcases hR_constant_sign with hR_constant_sign | hR_constant_sign <;>
      [left; right] <;> intro x hx <;> simp +decide [hR]
    · nlinarith only [sq_nonneg (eval x Q), hR_constant_sign x hx]
    · nlinarith only [mul_self_nonneg (eval x Q), hR_constant_sign x hx]
  have h_integrand_nonzero :
      ∃ x ∈ Set.Ioo (0 : ℝ) 1, (butcherShiftedLegendre n).eval x * Q.eval x ≠ 0 := by
    have h_integrand_zeros :
        Set.Finite {x ∈ Set.Ioo (0 : ℝ) 1 |
                    (butcherShiftedLegendre n).eval x * Q.eval x = 0} := by
      refine Set.Finite.subset
        (Q.roots.toFinset.finite_toSet.union
          ((butcherShiftedLegendre n |> Polynomial.roots |>
              Multiset.toFinset |> Finset.finite_toSet))) ?_
      norm_num [Set.subset_def]
      exact fun x _ _ hx₃ => Or.symm <|
        Or.imp
          (fun hx₄ => ⟨butcherShiftedLegendre_ne_zero n, hx₄⟩)
          (fun hx₄ => ⟨Finset.prod_ne_zero_iff.mpr
                        fun y _ => Polynomial.X_sub_C_ne_zero y, hx₄⟩)
          hx₃
    contrapose! h_integrand_zeros
    exact Set.Infinite.mono
      (fun x hx => ⟨hx, h_integrand_zeros x hx⟩)
      (Set.Ioo_infinite (by norm_num))
  have h_integral_zero :
      ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre n).eval x * Q.eval x = 0 := by
    convert butcherShiftedLegendre_orthogonal_to_lower_degree n Q hQ_natDegree using 1
  rcases h_integrand_constant_sign with h | h
  · rw [intervalIntegral.integral_of_le zero_le_one,
        MeasureTheory.integral_eq_zero_iff_of_nonneg_ae] at h_integral_zero
    · rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff'] at h_integral_zero <;>
        norm_num at *
      rw [MeasureTheory.ae_iff] at h_integral_zero
      contrapose! h_integral_zero
      obtain ⟨x, hx₁, hx₂, hx₃⟩ := h_integrand_nonzero
      obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ y, abs (y - x) < ε →
            (butcherShiftedLegendre n).eval y ≠ 0 ∧ Q.eval y ≠ 0 := by
        have hcontP :
            Continuous fun y => (butcherShiftedLegendre n).eval y :=
          Polynomial.continuous _
        have hcontQ : Continuous fun y => Q.eval y := Polynomial.continuous _
        obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ :=
          Metric.continuous_iff.mp hcontP x (|eval x (butcherShiftedLegendre n)|)
            (abs_pos.mpr hx₂)
        obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ :=
          Metric.continuous_iff.mp hcontQ x (|eval x Q|) (abs_pos.mpr hx₃)
        refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun y hy₁ => ?_⟩
        refine ⟨?_, ?_⟩
        · cases abs_cases (eval x (butcherShiftedLegendre n)) <;>
            linarith [abs_lt.mp (hδ₁ y (lt_of_lt_of_le hy₁ (min_le_left _ _)))]
        · cases abs_cases (eval x Q) <;>
            linarith [abs_lt.mp (hδ₂ y (lt_of_lt_of_le hy₁ (min_le_right _ _)))]
      have hxgt : (0 : ℝ) < x := hx₁.1
      have hxlt : x < (1 : ℝ) := hx₁.2
      have hmax_lt : max (0 : ℝ) (x - ε) < x := by
        rcases le_or_gt (x - ε) 0 with hle | hlt
        · rw [max_eq_left hle]; exact hxgt
        · rw [max_eq_right hlt.le]; linarith
      have hlt_min : x < min (1 : ℝ) (x + ε) := by
        rcases le_or_gt 1 (x + ε) with hle | hlt
        · rw [min_eq_left hle]; exact hxlt
        · rw [min_eq_right hlt.le]; linarith
      have h_interval_pos_measure :
          0 < MeasureTheory.MeasureSpace.volume
                (Set.Ioo (max 0 (x - ε)) (min 1 (x + ε))) := by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_pos.mpr (by linarith)
      refine ne_of_gt (lt_of_lt_of_le h_interval_pos_measure
        (MeasureTheory.measure_mono fun y hy => ?_))
      obtain ⟨hyL, hyR⟩ := hy
      have hyε : |y - x| < ε := by
        refine abs_lt.mpr ⟨?_, ?_⟩
        · rcases le_or_gt (x - ε) 0 with hle | hlt
          · rw [max_eq_left hle] at hyL; linarith
          · rw [max_eq_right hlt.le] at hyL; linarith
        · rcases le_or_gt 1 (x + ε) with hle | hlt
          · rw [min_eq_left hle] at hyR; linarith
          · rw [min_eq_right hlt.le] at hyR; linarith
      have hyPQ := hε y hyε
      refine ⟨?_, ?_, ?_⟩
      · rcases le_or_gt (x - ε) 0 with hle | hlt
        · rw [max_eq_left hle] at hyL; exact hyL
        · rw [max_eq_right hlt.le] at hyL; linarith
      · rcases le_or_gt 1 (x + ε) with hle | hlt
        · rw [min_eq_left hle] at hyR; exact hyR.le
        · rw [min_eq_right hlt.le] at hyR; linarith
      · exact hyPQ
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx using
        h x <| Set.Ioc_subset_Icc_self hx
    · refine Continuous.integrableOn_Ioc ?_
      exact ((butcherShiftedLegendre n).continuous.mul Q.continuous)
  · have h_integral_neg :
        ∫ x in (0 : ℝ)..1, -((butcherShiftedLegendre n).eval x * Q.eval x) > 0 := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      refine lt_of_le_of_lt ?_ ((MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
        ?_ ?_).2 ?_)
      · norm_num
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx using
          neg_nonneg_of_nonpos (h x <| Set.Ioc_subset_Icc_self hx)
      · refine Continuous.integrableOn_Ioc ?_
        exact ((butcherShiftedLegendre n).continuous.mul Q.continuous).neg
      · obtain ⟨x, hx₁, hx₂⟩ := h_integrand_nonzero
        obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ y, abs (y - x) < ε →
            (butcherShiftedLegendre n).eval y * Q.eval y ≠ 0 := by
          have hcontPQ :
              Continuous fun y => (butcherShiftedLegendre n).eval y * Q.eval y :=
            (butcherShiftedLegendre n).continuous.mul Q.continuous
          obtain ⟨δ, hδ_pos, hδ⟩ :=
            Metric.continuous_iff.mp hcontPQ x
              (|eval x (butcherShiftedLegendre n) * eval x Q|) (abs_pos.mpr hx₂)
          refine ⟨δ, hδ_pos, fun y hy₁ => ?_⟩
          cases abs_cases (eval x (butcherShiftedLegendre n) * eval x Q) <;>
            linarith [abs_lt.mp (hδ y hy₁)]
        have hxgt : (0 : ℝ) < x := hx₁.1
        have hxlt : x < (1 : ℝ) := hx₁.2
        have hmax_lt : max (0 : ℝ) (x - ε) < x := by
          rcases le_or_gt (x - ε) 0 with hle | hlt
          · rw [max_eq_left hle]; exact hxgt
          · rw [max_eq_right hlt.le]; linarith
        have hlt_min : x < min (1 : ℝ) (x + ε) := by
          rcases le_or_gt 1 (x + ε) with hle | hlt
          · rw [min_eq_left hle]; exact hxlt
          · rw [min_eq_right hlt.le]; linarith
        have h_interval_pos_measure :
            0 < MeasureTheory.MeasureSpace.volume
                  (Set.Ioo (max 0 (x - ε)) (min 1 (x + ε))) := by
          rw [Real.volume_Ioo]
          exact ENNReal.ofReal_pos.mpr (by linarith)
        refine h_interval_pos_measure.trans_le (MeasureTheory.measure_mono ?_)
        intro y hy
        obtain ⟨hyL, hyR⟩ := hy
        have hyε : |y - x| < ε := by
          refine abs_lt.mpr ⟨?_, ?_⟩
          · rcases le_or_gt (x - ε) 0 with hle | hlt
            · rw [max_eq_left hle] at hyL; linarith
            · rw [max_eq_right hlt.le] at hyL; linarith
          · rcases le_or_gt 1 (x + ε) with hle | hlt
            · rw [min_eq_left hle] at hyR; linarith
            · rw [min_eq_right hlt.le] at hyR; linarith
        refine ⟨?_, ?_, ?_⟩
        · simpa using neg_ne_zero.mpr (hε y hyε)
        · rcases le_or_gt (x - ε) 0 with hle | hlt
          · rw [max_eq_left hle] at hyL; exact hyL
          · rw [max_eq_right hlt.le] at hyL; linarith
        · rcases le_or_gt 1 (x + ε) with hle | hlt
          · rw [min_eq_left hle] at hyR; exact hyR.le
          · rw [min_eq_right hlt.le] at hyR; linarith
    rw [intervalIntegral.integral_neg] at h_integral_neg
    linarith

/-- **Butcher §342 (342g)** — `P_n^*` has `n` distinct real zeros in
the open interval `(0, 1)`, for every `n : ℕ`.

This is the final clause of `lem:342A`. Combined with clauses
(342a)–(342f) closed in cycles 271–293, this completes Butcher's
characterisation of the shifted Legendre polynomial family.

The proof uses
`butcherShiftedLegendre_rootsInIoo_card_le` (upper bound, this file,
refining cycle 294) and
`butcherShiftedLegendre_rootsInIoo_card_ge` (lower bound, the
sign-change contradiction integrated from Aristotle cycle 301).

Cross-check: the cycle 295–300 empirical anchors
`butcherShiftedLegendre_{one,three,five,seven,nine,eleven,thirteen}_roots`
are consistent with this general theorem specialised at the
corresponding `n` (they additionally supply explicit closed-form
sub-interval witnesses that the existential statement here does not). -/
theorem butcherShiftedLegendre_n_distinct_real_zeros (n : ℕ) :
    ∃ (xs : Finset ℝ), xs.card = n ∧
      (∀ x ∈ xs, x ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ x ∈ xs, (butcherShiftedLegendre n).eval x = 0) :=
  ⟨butcherShiftedLegendre_rootsInIoo n,
    le_antisymm
      (butcherShiftedLegendre_rootsInIoo_card_le n)
      (butcherShiftedLegendre_rootsInIoo_card_ge n),
    butcherShiftedLegendre_rootsInIoo_subset n,
    butcherShiftedLegendre_rootsInIoo_are_roots n⟩

/-! ### Phase A.1 of `lem:342B` — canonical zero enumeration

Given that `P_n^*` has exactly `n` distinct real zeros in `(0, 1)`
(`butcherShiftedLegendre_n_distinct_real_zeros`, cycle 301), we now
package those zeros as an indexed family `Fin n → ℝ` in strictly
increasing order. This is the canonical realisation of Butcher's
informal naming `c₁, c₂, …, cₛ` in §342 and is the API consumed by
the Gaussian quadrature constructions (`lem:342B` and downstream).

The enumeration is built via `Finset.orderEmbOfFin` on the concrete
finset `butcherShiftedLegendre_rootsInIoo n`, which gives strict
monotonicity (and therefore injectivity) for free.

This block ships four new symbols plus an `n = 1` non-vacuity anchor.
-/

/-- The cardinality of the root-set finset equals `n`. Combines the
upper bound (`butcherShiftedLegendre_rootsInIoo_card_le`) and the
lower bound (`butcherShiftedLegendre_rootsInIoo_card_ge`). -/
lemma butcherShiftedLegendre_rootsInIoo_card_eq (n : ℕ) :
    (butcherShiftedLegendre_rootsInIoo n).card = n :=
  le_antisymm
    (butcherShiftedLegendre_rootsInIoo_card_le n)
    (butcherShiftedLegendre_rootsInIoo_card_ge n)

/-- **Phase A.1 of `lem:342B` — canonical zeros of `P_n^*`.**

`butcherShiftedLegendre_zeros n` is the strictly increasing
enumeration `Fin n → ℝ` of the `n` distinct real zeros of `P_n^*` in
the open interval `(0, 1)`. This realises Butcher's informal
labelling `c₁, c₂, …, cₛ` (§342, p. 237) as an indexed family.

Definition: apply `Finset.orderEmbOfFin` to the concrete finset
`butcherShiftedLegendre_rootsInIoo n`, whose cardinality is `n` by
`butcherShiftedLegendre_rootsInIoo_card_eq` (combining the (342g)
upper and lower bounds from cycles 294 / 301).

Note: this is a Lean-engineering name, not a textbook entity —
Butcher names the `cᵢ` informally rather than as an indexed family,
so the canonical enumeration here is a convenience for downstream
constructions. -/
noncomputable def butcherShiftedLegendre_zeros (n : ℕ) : Fin n → ℝ :=
  (butcherShiftedLegendre_rootsInIoo n).orderEmbOfFin
    (butcherShiftedLegendre_rootsInIoo_card_eq n)

/-- Each canonical zero `butcherShiftedLegendre_zeros n i` lies in
the open interval `(0, 1)`. Immediate from
`Finset.orderEmbOfFin_mem` combined with
`butcherShiftedLegendre_rootsInIoo_subset`. -/
lemma butcherShiftedLegendre_zeros_mem_Ioo (n : ℕ) (i : Fin n) :
    butcherShiftedLegendre_zeros n i ∈ Set.Ioo (0 : ℝ) 1 :=
  butcherShiftedLegendre_rootsInIoo_subset n _
    (Finset.orderEmbOfFin_mem _ _ i)

/-- Each canonical zero `butcherShiftedLegendre_zeros n i` is in fact
a root of `P_n^*`. Immediate from `Finset.orderEmbOfFin_mem`
combined with `butcherShiftedLegendre_rootsInIoo_are_roots`. -/
lemma butcherShiftedLegendre_zeros_isRoot (n : ℕ) (i : Fin n) :
    (butcherShiftedLegendre n).eval
        (butcherShiftedLegendre_zeros n i) = 0 :=
  butcherShiftedLegendre_rootsInIoo_are_roots n _
    (Finset.orderEmbOfFin_mem _ _ i)

/-- The canonical zero enumeration is injective: distinct indices in
`Fin n` map to distinct zeros. Follows from the strict monotonicity
of `Finset.orderEmbOfFin`. -/
lemma butcherShiftedLegendre_zeros_injective (n : ℕ) :
    Function.Injective (butcherShiftedLegendre_zeros n) :=
  ((butcherShiftedLegendre_rootsInIoo n).orderEmbOfFin
    (butcherShiftedLegendre_rootsInIoo_card_eq n)).injective

/-- **Non-vacuity anchor at `n = 1`.** The unique canonical zero of
`P_1^* = 2X - 1` is `1/2`. Cross-checks the Phase A.1 enumeration
against the concrete witness from `butcherShiftedLegendre_one_root`
(cycle 294). -/
example : butcherShiftedLegendre_zeros 1 ⟨0, by omega⟩ = (1 / 2 : ℝ) := by
  have h_mem :
      butcherShiftedLegendre_zeros 1 ⟨0, by omega⟩
        ∈ butcherShiftedLegendre_rootsInIoo 1 :=
    Finset.orderEmbOfFin_mem _ _ _
  have h12_mem : (1 / 2 : ℝ) ∈ butcherShiftedLegendre_rootsInIoo 1 := by
    simp only [butcherShiftedLegendre_rootsInIoo, Finset.mem_filter,
               Multiset.mem_toFinset,
               mem_roots (butcherShiftedLegendre_ne_zero 1)]
    exact ⟨(butcherShiftedLegendre_one_root).1,
           (butcherShiftedLegendre_one_root).2⟩
  have hcard : (butcherShiftedLegendre_rootsInIoo 1).card = 1 :=
    butcherShiftedLegendre_rootsInIoo_card_eq 1
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  rw [ha, Finset.mem_singleton] at h_mem h12_mem
  rw [h_mem, ← h12_mem]

/-! ### Phase A.2 of `lem:342B` — Lagrange quadrature weights (cycle 303)

Butcher §342 p. 237 (`lem:342B`): "Let `c₁, c₂, …, c_s` denote the zeros
of `P_s^*`. Then there exist positive numbers `b₁, b₂, …, b_s` such that
`∫₀¹ φ(x) dx = ∑ᵢ bᵢ φ(cᵢ)` for any polynomial of degree less than `2s`."

The textbook proof opens with: *"Choose `bᵢ` so that (342h) holds for any
`φ` of degree less than `s`. Because the `cᵢ` are distinct the choice of
the `bᵢ` is unique."* That is Phase A.2 — defining the weights and
proving exactness on the `< n` half. The `2n`-degree extension via
`φ = P_s^* · Q + R` is Phase B and consumes (342a) orthogonality.

The weight `bⱼ` is the canonical Lagrange-quadrature formula
`bⱼ = ∫₀¹ Lⱼ(x) dx`, where `Lⱼ` is the Lagrange basis polynomial at the
node `c_j = butcherShiftedLegendre_zeros n j`. This is **not** definition
smuggling of the exactness conclusion: the formula is the canonical
choice, and the exactness theorem `butcherShiftedLegendre_quadrature_exact_lt_n`
below is a genuine consequence of the polynomial-interpolation identity
`Lagrange.eq_interpolate` (`f = interpolate s v (fun i ↦ eval (vᵢ) f)`
for `f.degree < s.card`). -/

/-- **Lagrange quadrature weights** at the canonical zeros of
`butcherShiftedLegendre n` (Butcher's `bⱼ` from §342 p. 237).
Defined as the integral of the Lagrange basis polynomial `Lⱼ` over
`[0, 1]`, where `Lⱼ` interpolates the value `1` at the node `c_j` and
`0` at the other `n - 1` nodes. The full lemma `lem:342B` also asserts
positivity (`0 < bⱼ`) and `2n`-degree exactness; both are Phase B and
deferred to a future cycle. -/
noncomputable def butcherShiftedLegendre_quadratureWeights
    (n : ℕ) (j : Fin n) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    (Lagrange.basis Finset.univ (butcherShiftedLegendre_zeros n) j).eval x

/-- **Quadrature exactness on polynomials of degree `< n`.** Phase A.2
of `lem:342B`: for every polynomial `φ ∈ ℝ[X]` with `natDegree < n`,
`∫₀¹ φ(x) dx = ∑ⱼ bⱼ · φ(cⱼ)`, where the `bⱼ` are the Lagrange weights
defined above and the `cⱼ` are the canonical zeros of the shifted
Legendre polynomial of degree `n`.

The proof is the textbook recipe: decompose `φ` via
`Lagrange.eq_interpolate` as `φ = ∑ⱼ C(φ(cⱼ)) · Lⱼ`, integrate term by
term, and recognise each integrand as a constant times the basis
polynomial `Lⱼ`. Distinctness of the nodes for the Lagrange identity
comes from `butcherShiftedLegendre_zeros_injective` (cycle 302). -/
theorem butcherShiftedLegendre_quadrature_exact_lt_n
    (n : ℕ) (φ : Polynomial ℝ) (hdeg : φ.natDegree < n) :
    (∫ x in (0 : ℝ)..1, φ.eval x)
      = ∑ j : Fin n,
          butcherShiftedLegendre_quadratureWeights n j *
          φ.eval (butcherShiftedLegendre_zeros n j) := by
  set v : Fin n → ℝ := butcherShiftedLegendre_zeros n with hv_def
  have hv : Function.Injective v :=
    butcherShiftedLegendre_zeros_injective n
  -- Step 1: decompose φ via the Lagrange interpolation identity.
  have hdecomp : φ = ∑ j : Fin n,
      Polynomial.C (Polynomial.eval (v j) φ) * Lagrange.basis Finset.univ v j := by
    have hdeg' : φ.degree < ((Finset.univ : Finset (Fin n)).card : WithBot ℕ) := by
      rw [Finset.card_univ, Fintype.card_fin]
      rcases eq_or_ne φ 0 with hφ | hφ
      · subst hφ; rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
      · rw [Polynomial.degree_eq_natDegree hφ]; exact_mod_cast hdeg
    have h_interp :=
      Lagrange.eq_interpolate (s := (Finset.univ : Finset (Fin n))) (v := v)
        hv.injOn hdeg'
    conv_lhs => rw [h_interp]
    rw [Lagrange.interpolate_apply]
  -- Step 2: integrate both sides; swap integral and sum.
  conv_lhs => rw [hdecomp]
  simp_rw [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul, butcherShiftedLegendre_quadratureWeights]
    ring
  · intro j _
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_const.mul (Polynomial.continuous _)

/-- **Non-vacuity anchor at `n = 1`.** The unique Lagrange weight at the
single node `c_1 = 1/2` is `1`, matching the elementary observation
`∫₀¹ 1 dx = 1 · φ(1/2)` for any constant `φ`. The Lagrange basis on a
singleton is identically `1` (`Lagrange.basis_singleton`), so the
defining integral collapses to `∫₀¹ 1 dx = 1`. -/
example : butcherShiftedLegendre_quadratureWeights 1 ⟨0, by omega⟩ = 1 := by
  unfold butcherShiftedLegendre_quadratureWeights
  simp [Lagrange.basis_singleton, Polynomial.eval_one]

/-! ### Phase B.1 of `lem:342B` — `2n`-degree exactness (cycle 304)

Butcher §342 p. 237 (342h): *"To prove that (342h) holds for degree up
to `2s − 1`, write `φ(x) = P_s^*(x) Q(x) + R(x)`, where the quotient `Q`
and the remainder `R` have degrees not exceeding `s − 1`. We now have
`∫₀¹ φ(x) dx = ∫₀¹ P_s^*(x) Q(x) dx + ∫₀¹ R(x) dx = 0 + ∑ᵢ bᵢ R(cᵢ) =
∑ᵢ bᵢ φ(cᵢ)`."*

The proof is the textbook recipe verbatim:
1. Polynomial division `φ = P_n^* · Q + R` via Mathlib's
   `EuclideanDomain.div_add_mod` for the Euclidean ring `ℝ[X]`.
2. Degree of the remainder `R.natDegree < n` from
   `Polynomial.degree_mod_lt` and `butcherShiftedLegendre_natDegree`.
3. Degree of the quotient `Q.natDegree < n` from
   `(P_n^* · Q).natDegree = n + Q.natDegree` (via
   `Polynomial.natDegree_mul` over the integral domain `ℝ`) combined
   with `φ.natDegree < 2n` and the fact that
   `(P_n^* · Q).natDegree > R.natDegree`, so the leading term of `φ`
   matches that of `P_n^* · Q`.
4. The high-degree summand vanishes via cycle 292's
   `butcherShiftedLegendre_orthogonal_to_lower_degree`.
5. The low-degree summand `∫₀¹ R = ∑ⱼ bⱼ R(cⱼ)` via Phase A.2's
   `butcherShiftedLegendre_quadrature_exact_lt_n`.
6. `R(cⱼ) = φ(cⱼ)` because `P_n^*(cⱼ) = 0` via Phase A.2a's
   `butcherShiftedLegendre_zeros_isRoot`.

`lem:342B` remains `partial` after this cycle because positivity
(`0 < bⱼ`) and uniqueness clauses are deferred to subsequent cycles. -/

/-- **Gaussian quadrature exactness on polynomials of degree `< 2n`.**
Phase B.1 of `lem:342B` (Butcher §342 p. 237 (342h)): for every
polynomial `φ ∈ ℝ[X]` with `natDegree < 2n`,
`∫₀¹ φ(x) dx = ∑ⱼ bⱼ · φ(cⱼ)`, where the `bⱼ` are the Lagrange weights
at the shifted Legendre zeros `cⱼ`. This is the headline result for the
existence half of `lem:342B`; positivity of the `bⱼ` and uniqueness of
the rule are Phase B.2 and Phase B.3 respectively. -/
theorem butcherShiftedLegendre_quadrature_exact_lt_two_n
    (n : ℕ) (hn : 0 < n) (φ : Polynomial ℝ) (hdeg : φ.natDegree < 2 * n) :
    (∫ x in (0 : ℝ)..1, φ.eval x)
      = ∑ j : Fin n,
          butcherShiftedLegendre_quadratureWeights n j *
          φ.eval (butcherShiftedLegendre_zeros n j) := by
  have hPn_nz : butcherShiftedLegendre n ≠ 0 := butcherShiftedLegendre_ne_zero n
  have hPn_natDeg : (butcherShiftedLegendre n).natDegree = n :=
    butcherShiftedLegendre_natDegree n
  set Q := φ / butcherShiftedLegendre n with hQ_def
  set R := φ % butcherShiftedLegendre n with hR_def
  have hdiv : butcherShiftedLegendre n * Q + R = φ :=
    EuclideanDomain.div_add_mod φ (butcherShiftedLegendre n)
  -- Degree bound: R.natDegree < n via `Polynomial.degree_mod_lt`.
  have hR_lt : R.natDegree < n := by
    rcases eq_or_ne R 0 with hR0 | hR0
    · rw [hR0, Polynomial.natDegree_zero]; exact hn
    · have h := Polynomial.degree_mod_lt φ hPn_nz
      rw [← hR_def] at h
      rw [Polynomial.degree_eq_natDegree hR0,
          Polynomial.degree_eq_natDegree hPn_nz, hPn_natDeg] at h
      exact_mod_cast h
  -- Degree bound: Q.natDegree < n from `φ = P_n^* · Q + R` and `φ.natDegree < 2n`.
  have hQ_lt : Q.natDegree < n := by
    rcases eq_or_ne Q 0 with hQ0 | hQ0
    · rw [hQ0, Polynomial.natDegree_zero]; exact hn
    · have hPQ_nd : (butcherShiftedLegendre n * Q).natDegree = n + Q.natDegree := by
        rw [Polynomial.natDegree_mul hPn_nz hQ0, hPn_natDeg]
      have hPQ_gt_R : R.natDegree < (butcherShiftedLegendre n * Q).natDegree := by
        rw [hPQ_nd]; omega
      have hφ_natDeg : φ.natDegree = (butcherShiftedLegendre n * Q).natDegree := by
        rw [← hdiv, add_comm (butcherShiftedLegendre n * Q) R]
        exact Polynomial.natDegree_add_eq_right_of_natDegree_lt hPQ_gt_R
      rw [hφ_natDeg, hPQ_nd] at hdeg
      omega
  -- Pointwise decomposition `φ(x) = P_n^*(x) · Q(x) + R(x)`.
  have h_eval : ∀ x : ℝ, φ.eval x =
      (butcherShiftedLegendre n).eval x * Q.eval x + R.eval x := by
    intro x
    have := congrArg (Polynomial.eval x) hdiv.symm
    simp only [Polynomial.eval_add, Polynomial.eval_mul] at this
    exact this
  calc (∫ x in (0 : ℝ)..1, φ.eval x)
      = ∫ x in (0 : ℝ)..1,
          (butcherShiftedLegendre n).eval x * Q.eval x + R.eval x := by
        apply intervalIntegral.integral_congr
        intro x _; exact h_eval x
    _ = (∫ x in (0 : ℝ)..1, (butcherShiftedLegendre n).eval x * Q.eval x)
          + (∫ x in (0 : ℝ)..1, R.eval x) :=
        intervalIntegral.integral_add
          (((butcherShiftedLegendre n).continuous.mul Q.continuous).intervalIntegrable 0 1)
          (R.continuous.intervalIntegrable 0 1)
    -- Step 4: orthogonality kills `∫ P_n^* · Q` (cycle 292, `Q.natDegree < n`).
    _ = 0 + ∫ x in (0 : ℝ)..1, R.eval x := by
        rw [butcherShiftedLegendre_orthogonal_to_lower_degree n Q hQ_lt]
    _ = ∫ x in (0 : ℝ)..1, R.eval x := zero_add _
    -- Step 5: Phase A.2 on `R` (cycle 303, `R.natDegree < n`).
    _ = ∑ j : Fin n,
          butcherShiftedLegendre_quadratureWeights n j *
            R.eval (butcherShiftedLegendre_zeros n j) :=
        butcherShiftedLegendre_quadrature_exact_lt_n n R hR_lt
    -- Step 6: `R(c_j) = φ(c_j)` because `P_n^*(c_j) = 0` (cycle 302).
    _ = ∑ j : Fin n,
          butcherShiftedLegendre_quadratureWeights n j *
            φ.eval (butcherShiftedLegendre_zeros n j) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        have hzero :
            (butcherShiftedLegendre n).eval (butcherShiftedLegendre_zeros n j) = 0 :=
          butcherShiftedLegendre_zeros_isRoot n j
        rw [h_eval (butcherShiftedLegendre_zeros n j), hzero, zero_mul, zero_add]

/-- **Consistency witness: `∑ⱼ bⱼ = 1`.** Apply Phase A.2's quadrature
exactness to the constant polynomial `φ = 1` (whose `natDegree = 0 < n`)
and use `∫₀¹ 1 dx = 1` to recover the textbook identity that the
Gaussian quadrature weights sum to the length of the interval. This
serves as a sanity check independent of Phase B.1: even before
`2n`-degree exactness is in scope, the `< n` exactness already forces
`∑ⱼ bⱼ = ∫₀¹ 1 dx = 1`. -/
theorem butcherShiftedLegendre_quadratureWeights_sum_eq_one
    (n : ℕ) (hn : 0 < n) :
    ∑ j : Fin n, butcherShiftedLegendre_quadratureWeights n j = 1 := by
  have h := butcherShiftedLegendre_quadrature_exact_lt_n n (1 : Polynomial ℝ)
    (by rw [Polynomial.natDegree_one]; exact hn)
  simp only [Polynomial.eval_one, intervalIntegral.integral_const, smul_eq_mul,
    mul_one, sub_zero] at h
  linarith [h]

/-! ### Phase B.2 of `lem:342B` — positivity of quadrature weights (cycle 305)

Butcher §342 p. 237 (`lem:342B`, second clause): *"To prove the `bᵢ` are
positive, let `φ(x)` denote the square of the polynomial formed by dividing
`P_s^*(x)` by `x − cᵢ`. Substitute into (342h), and the result follows."*

Verbatim execution of the textbook recipe:

1. Define `φⱼ := (P_n^* /ₘ (X - C cⱼ))²` — a non-negative-valued polynomial
   of natDegree `2(n - 1) < 2n`.
2. Vanishing at the other zeros: `φⱼ(cₖ) = 0` for `k ≠ j`, via the identity
   `(X - C cⱼ) · (P_n^* /ₘ (X - C cⱼ)) = P_n^*` (since `cⱼ` is a root) and
   `cⱼ ≠ cₖ` (cycle 302's `butcherShiftedLegendre_zeros_injective`).
3. Positivity at the own zero: `φⱼ(cⱼ) > 0`. Routes through showing each
   `cⱼ` is a *simple* root of `P_n^*` (rootMultiplicity = 1, from cycle
   301's distinct-roots fact plus `natDegree = n`) and then invoking
   `Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero`.
4. `∫₀¹ φⱼ > 0`: continuous (polynomial), non-negative everywhere (square),
   positive at `cⱼ ∈ (0, 1)` ⇒ `intervalIntegral.integral_pos`.
5. Headline closure: Phase B.1's `2n`-degree exactness on `φⱼ` reduces the
   integral to `bⱼ · φⱼ(cⱼ)` (other terms vanish by Step 2). Combined with
   the LHS positivity and `φⱼ(cⱼ) > 0`, we get `bⱼ > 0`. -/

/-- **Auxiliary: the Lagrange factor `P_n^* /ₘ (X - C cⱼ)`.** Polynomial
division of `P_n^*` by the monic linear factor at the canonical zero `cⱼ`.
This is the polynomial `q` such that `(X - C cⱼ) · q = P_n^*` (since `cⱼ`
is a root of `P_n^*`). Butcher §342 p. 237 names this *"the polynomial
formed by dividing `P_s^*(x)` by `x − cᵢ`"* and squares it to build the
positive test polynomial. -/
private noncomputable def butcherShiftedLegendre_lagrangeFactor
    (n : ℕ) (j : Fin n) : Polynomial ℝ :=
  butcherShiftedLegendre n /ₘ
    (Polynomial.X - Polynomial.C (butcherShiftedLegendre_zeros n j))

/-- **Auxiliary: Butcher's test polynomial `φⱼ`.** The square of the
Lagrange factor `P_n^* /ₘ (X - C cⱼ)`. By construction, `φⱼ(cⱼ) > 0`
(non-zero by simple-root, squared) and `φⱼ(cₖ) = 0` for `k ≠ j` (other
zeros of `P_n^*`). Used in Butcher's positivity argument for the
quadrature weights. -/
private noncomputable def butcherShiftedLegendre_lagrangeFactorSq
    (n : ℕ) (j : Fin n) : Polynomial ℝ :=
  (butcherShiftedLegendre_lagrangeFactor n j) ^ 2

/-- The factorisation identity `(X - C cⱼ) · lagrangeFactor n j = P_n^*`,
which holds because `cⱼ` is a root of `P_n^*` (cycle 302's
`butcherShiftedLegendre_zeros_isRoot`). Routes through Mathlib's
`Polynomial.mul_divByMonic_eq_iff_isRoot`. -/
private lemma butcherShiftedLegendre_lagrangeFactor_mul_factor_eq
    (n : ℕ) (j : Fin n) :
    (Polynomial.X - Polynomial.C (butcherShiftedLegendre_zeros n j))
        * butcherShiftedLegendre_lagrangeFactor n j
      = butcherShiftedLegendre n := by
  unfold butcherShiftedLegendre_lagrangeFactor
  exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr
    (butcherShiftedLegendre_zeros_isRoot n j)

/-- The natDegree of the Lagrange factor `P_n^* /ₘ (X - C cⱼ)` is `n - 1`.
Combines `Polynomial.natDegree_divByMonic` (for `(X - C cⱼ)` monic),
`butcherShiftedLegendre_natDegree` (cycle 273), and `natDegree_X_sub_C`. -/
private lemma butcherShiftedLegendre_lagrangeFactor_natDegree
    (n : ℕ) (j : Fin n) :
    (butcherShiftedLegendre_lagrangeFactor n j).natDegree = n - 1 := by
  unfold butcherShiftedLegendre_lagrangeFactor
  rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C _),
      butcherShiftedLegendre_natDegree, Polynomial.natDegree_X_sub_C]

/-- **Step 2: degree bound `(φⱼ).natDegree < 2n`.** The square of a
polynomial of natDegree `n - 1` has natDegree `2(n - 1) = 2n - 2 < 2n`
(given `0 < n`). Combines the Lagrange-factor natDegree lemma with
`Polynomial.natDegree_pow` (valid over the integral domain `ℝ`). -/
private lemma butcherShiftedLegendre_lagrangeFactorSq_natDegree_lt
    (n : ℕ) (hn : 0 < n) (j : Fin n) :
    (butcherShiftedLegendre_lagrangeFactorSq n j).natDegree < 2 * n := by
  unfold butcherShiftedLegendre_lagrangeFactorSq
  rw [Polynomial.natDegree_pow,
      butcherShiftedLegendre_lagrangeFactor_natDegree n j]
  omega

/-- **Step 3 (pre-square version).** For `k ≠ j`, the Lagrange factor
`P_n^* /ₘ (X - C cⱼ)` vanishes at `cₖ`. Proof: evaluate the identity
`(X - C cⱼ) · lagrangeFactor n j = P_n^*` at `x = cₖ`; the RHS is `0`
(by `butcherShiftedLegendre_zeros_isRoot`), and the factor `cₖ - cⱼ` is
non-zero (by `butcherShiftedLegendre_zeros_injective`). -/
private lemma butcherShiftedLegendre_lagrangeFactor_eval_zeros_ne
    (n : ℕ) (j k : Fin n) (hjk : k ≠ j) :
    (butcherShiftedLegendre_lagrangeFactor n j).eval
      (butcherShiftedLegendre_zeros n k) = 0 := by
  have h_id := butcherShiftedLegendre_lagrangeFactor_mul_factor_eq n j
  have h_root : (butcherShiftedLegendre n).eval
      (butcherShiftedLegendre_zeros n k) = 0 :=
    butcherShiftedLegendre_zeros_isRoot n k
  have h_eval := congrArg
    (Polynomial.eval (butcherShiftedLegendre_zeros n k)) h_id
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at h_eval
  rw [h_root] at h_eval
  have h_ne : butcherShiftedLegendre_zeros n k
      - butcherShiftedLegendre_zeros n j ≠ 0 := by
    intro h
    apply hjk
    exact butcherShiftedLegendre_zeros_injective n
      (sub_eq_zero.mp h)
  exact (mul_eq_zero.mp h_eval).resolve_left h_ne

/-- **Step 3 (squared corollary).** `φⱼ(cₖ) = 0` for `k ≠ j`. Immediate
from the unsquared version and `0^2 = 0`. -/
private lemma butcherShiftedLegendre_lagrangeFactorSq_eval_zeros_ne
    (n : ℕ) (j k : Fin n) (hjk : k ≠ j) :
    (butcherShiftedLegendre_lagrangeFactorSq n j).eval
      (butcherShiftedLegendre_zeros n k) = 0 := by
  unfold butcherShiftedLegendre_lagrangeFactorSq
  rw [Polynomial.eval_pow,
      butcherShiftedLegendre_lagrangeFactor_eval_zeros_ne n j k hjk]
  ring

/-- The cardinality of the roots multiset of `P_n^*` equals `n`.
Combines the upper bound (`Polynomial.card_roots'` ≤ `natDegree = n`) and
the lower bound: the toFinset filtered to `(0,1)` already has cardinality
`n` (cycle 301), and `filter ≤ toFinset ≤ roots`. -/
private lemma butcherShiftedLegendre_roots_card_eq (n : ℕ) :
    (butcherShiftedLegendre n).roots.card = n := by
  apply le_antisymm
  · calc (butcherShiftedLegendre n).roots.card
        ≤ (butcherShiftedLegendre n).natDegree := Polynomial.card_roots' _
      _ = n := butcherShiftedLegendre_natDegree n
  · calc n = (butcherShiftedLegendre_rootsInIoo n).card :=
            (butcherShiftedLegendre_rootsInIoo_card_eq n).symm
      _ ≤ (butcherShiftedLegendre n).roots.toFinset.card :=
          Finset.card_filter_le _ _
      _ ≤ (butcherShiftedLegendre n).roots.card :=
          Multiset.toFinset_card_le _

/-- The roots multiset of `P_n^*` has no duplicates: each root has
multiplicity exactly `1`. Proof: the toFinset (which dedup's the
multiset) has cardinality `n` (since the filter to `(0,1)` already has
that cardinality, and the unfiltered toFinset is a superset). The
multiset itself also has cardinality `n` (the natDegree upper bound is
saturated). Equal cardinalities of toFinset and multiset force `Nodup`
via `Multiset.toFinset_card_eq_card_iff_nodup`. -/
private lemma butcherShiftedLegendre_roots_nodup (n : ℕ) :
    (butcherShiftedLegendre n).roots.Nodup := by
  rw [← Multiset.toFinset_card_eq_card_iff_nodup]
  apply le_antisymm
  · exact Multiset.toFinset_card_le _
  · calc (butcherShiftedLegendre n).roots.card
        = n := butcherShiftedLegendre_roots_card_eq n
      _ = (butcherShiftedLegendre_rootsInIoo n).card :=
          (butcherShiftedLegendre_rootsInIoo_card_eq n).symm
      _ ≤ (butcherShiftedLegendre n).roots.toFinset.card :=
          Finset.card_filter_le _ _

/-- **Simple-root multiplicity.** Each canonical zero `cⱼ` of `P_n^*` has
`rootMultiplicity` equal to `1`. Lower bound: `cⱼ` is a root and `P_n^*`
is non-zero. Upper bound: the roots multiset is `Nodup`, so each
element's count (= rootMultiplicity, via `Polynomial.count_roots`) is at
most `1`. -/
private lemma butcherShiftedLegendre_rootMultiplicity_eq_one
    (n : ℕ) (j : Fin n) :
    (butcherShiftedLegendre n).rootMultiplicity
        (butcherShiftedLegendre_zeros n j) = 1 := by
  have hp_ne : butcherShiftedLegendre n ≠ 0 := butcherShiftedLegendre_ne_zero n
  classical
  have h_lb : 1 ≤ (butcherShiftedLegendre n).rootMultiplicity
      (butcherShiftedLegendre_zeros n j) := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [Polynomial.rootMultiplicity_eq_zero_iff] at h0
    exact hp_ne (h0 (butcherShiftedLegendre_zeros_isRoot n j))
  have h_ub : (butcherShiftedLegendre n).rootMultiplicity
      (butcherShiftedLegendre_zeros n j) ≤ 1 := by
    rw [← Polynomial.count_roots]
    exact Multiset.nodup_iff_count_le_one.mp
      (butcherShiftedLegendre_roots_nodup n) _
  omega

/-- **Step 4: `φⱼ(cⱼ) > 0`.** Combines the simple-root multiplicity fact
with `Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero` (which
states that the dehomogenisation of `P_n^*` at the root, divided by the
power `(X - C cⱼ)^m`, evaluates to a non-zero value at `cⱼ`). For
multiplicity `m = 1`, that division is exactly the Lagrange factor.
Squaring a non-zero real gives a positive real (`sq_pos_of_ne_zero`). -/
private lemma butcherShiftedLegendre_lagrangeFactorSq_eval_self_pos
    (n : ℕ) (j : Fin n) :
    0 < (butcherShiftedLegendre_lagrangeFactorSq n j).eval
      (butcherShiftedLegendre_zeros n j) := by
  unfold butcherShiftedLegendre_lagrangeFactorSq
  rw [Polynomial.eval_pow]
  apply sq_pos_of_ne_zero
  -- Reduce to `eval_divByMonic_pow_rootMultiplicity_ne_zero`.
  have h_mult := butcherShiftedLegendre_rootMultiplicity_eq_one n j
  have h_ne := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero
    (butcherShiftedLegendre_zeros n j) (butcherShiftedLegendre_ne_zero n)
  rw [h_mult, pow_one] at h_ne
  exact h_ne

/-- **Step 5: `∫₀¹ φⱼ > 0`.** Apply `intervalIntegral.integral_pos`:
- `0 < 1` (the integration bounds).
- `φⱼ` is continuous on `[0, 1]` (polynomial).
- `φⱼ x ≥ 0` for all `x` (square of a real).
- `φⱼ cⱼ > 0` with `cⱼ ∈ (0, 1) ⊂ [0, 1]` (Step 4 + cycle 302's
  `butcherShiftedLegendre_zeros_mem_Ioo`). -/
private lemma butcherShiftedLegendre_lagrangeFactorSq_integral_pos
    (n : ℕ) (j : Fin n) :
    0 < ∫ x in (0 : ℝ)..1,
      (butcherShiftedLegendre_lagrangeFactorSq n j).eval x := by
  apply intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
  · exact (Polynomial.continuous _).continuousOn
  · intro x _
    unfold butcherShiftedLegendre_lagrangeFactorSq
    rw [Polynomial.eval_pow]
    exact sq_nonneg _
  · refine ⟨butcherShiftedLegendre_zeros n j, ?_, ?_⟩
    · exact Set.Ioo_subset_Icc_self
        (butcherShiftedLegendre_zeros_mem_Ioo n j)
    · exact butcherShiftedLegendre_lagrangeFactorSq_eval_self_pos n j

/-- **Phase B.2 headline: positivity of the Gaussian quadrature weights.**
Butcher §342 p. 237 (`lem:342B`): each weight `bⱼ` in the Gaussian
quadrature formula at the canonical zeros of `P_n^*` is strictly positive.

The textbook recipe (verbatim): apply Phase B.1's `2n`-degree exactness
to the test polynomial `φⱼ := (P_n^* /ₘ (X - C cⱼ))²`. The RHS sum
collapses to the single term `bⱼ · φⱼ(cⱼ)` (other terms vanish by Step 3).
The LHS `∫₀¹ φⱼ > 0` (Step 5, square integrand). Combined with
`φⱼ(cⱼ) > 0` (Step 4), conclude `bⱼ > 0`. -/
theorem butcherShiftedLegendre_quadratureWeights_pos
    (n : ℕ) (hn : 0 < n) (j : Fin n) :
    0 < butcherShiftedLegendre_quadratureWeights n j := by
  set φ := butcherShiftedLegendre_lagrangeFactorSq n j with hφ_def
  have hdeg : φ.natDegree < 2 * n :=
    butcherShiftedLegendre_lagrangeFactorSq_natDegree_lt n hn j
  have h_exact := butcherShiftedLegendre_quadrature_exact_lt_two_n n hn φ hdeg
  have h_int_pos : 0 < ∫ x in (0 : ℝ)..1, φ.eval x :=
    butcherShiftedLegendre_lagrangeFactorSq_integral_pos n j
  -- RHS sum collapses to the single `k = j` term.
  have h_sum : ∑ k : Fin n,
      butcherShiftedLegendre_quadratureWeights n k *
        φ.eval (butcherShiftedLegendre_zeros n k)
      = butcherShiftedLegendre_quadratureWeights n j *
        φ.eval (butcherShiftedLegendre_zeros n j) := by
    apply Finset.sum_eq_single j
    · intro k _ hkj
      rw [butcherShiftedLegendre_lagrangeFactorSq_eval_zeros_ne n j k hkj,
          mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [h_sum] at h_exact
  -- So `bⱼ · φⱼ(cⱼ) > 0`. With `φⱼ(cⱼ) > 0`, conclude `bⱼ > 0`.
  have h_prod_pos : 0 < butcherShiftedLegendre_quadratureWeights n j *
      φ.eval (butcherShiftedLegendre_zeros n j) := h_exact ▸ h_int_pos
  have h_φj_pos : 0 < φ.eval (butcherShiftedLegendre_zeros n j) :=
    butcherShiftedLegendre_lagrangeFactorSq_eval_self_pos n j
  exact (mul_pos_iff_of_pos_right h_φj_pos).mp h_prod_pos

/-! ### Phase B.3 of `lem:342B` — uniqueness of quadrature weights (cycle 305 stretch)

Butcher §342 p. 237 (`lem:342B`, final clause): *"The `bᵢ` are unique."*
That is, if `(b_j)_{j < n}` is any other family of coefficients satisfying
the `< n`-degree exactness identity at the canonical zeros `(c_j)_{j < n}`,
then `b = butcherShiftedLegendre_quadratureWeights n`.

Proof: instantiate the hypothesis at each Lagrange basis polynomial
`L_j := Lagrange.basis Finset.univ v j` (where `v = butcherShiftedLegendre_zeros n`).
The Kronecker-delta property `L_j(c_k) = δ_{jk}` (`Lagrange.eval_basis_self` /
`Lagrange.eval_basis_of_ne`) collapses the RHS sum to `b j`. The LHS is
the definition of `butcherShiftedLegendre_quadratureWeights n j`. Hence
`b j = quadratureWeights n j` for all `j`. -/

/-- **Uniqueness of the Gaussian quadrature weights.** Phase B.3 of
`lem:342B` (Butcher §342 p. 237 "The `bᵢ` are unique"): any other family
`(b_j)_{j < n}` satisfying the `< n`-degree exactness identity at the
canonical zeros must agree with `butcherShiftedLegendre_quadratureWeights`
pointwise. The hypothesis only requires exactness on the `< n` half (the
weaker half of the conditions in (342h)); the `2n`-degree exactness is
not needed for uniqueness. -/
theorem butcherShiftedLegendre_quadratureWeights_unique
    (n : ℕ) (hn : 0 < n) (b : Fin n → ℝ)
    (hb : ∀ φ : Polynomial ℝ, φ.natDegree < n →
        (∫ x in (0 : ℝ)..1, φ.eval x)
          = ∑ j : Fin n, b j *
              φ.eval (butcherShiftedLegendre_zeros n j)) :
    b = butcherShiftedLegendre_quadratureWeights n := by
  funext j
  set v : Fin n → ℝ := butcherShiftedLegendre_zeros n with hv_def
  have hv : Function.Injective v := butcherShiftedLegendre_zeros_injective n
  have hv_injOn : Set.InjOn v (Finset.univ : Finset (Fin n)) :=
    hv.injOn
  set φ := Lagrange.basis (Finset.univ : Finset (Fin n)) v j with hφ_def
  have hj_mem : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have h_natDeg : φ.natDegree < n := by
    rw [hφ_def, Lagrange.natDegree_basis hv_injOn hj_mem,
        Finset.card_univ, Fintype.card_fin]
    omega
  have h := hb φ h_natDeg
  -- RHS sum collapses to `b j` via the Kronecker-delta property of the basis.
  have h_rhs : (∑ k : Fin n, b k * φ.eval (v k)) = b j := by
    rw [Finset.sum_eq_single j]
    · rw [hφ_def, Lagrange.eval_basis_self hv_injOn hj_mem, mul_one]
    · intro k _ hkj
      rw [hφ_def, Lagrange.eval_basis_of_ne hkj.symm (Finset.mem_univ k),
          mul_zero]
    · intro habs; exact absurd (Finset.mem_univ j) habs
  -- LHS is precisely the definition of `quadratureWeights n j`.
  have h_lhs : (∫ x in (0 : ℝ)..1, φ.eval x) =
      butcherShiftedLegendre_quadratureWeights n j := by
    rw [butcherShiftedLegendre_quadratureWeights, hφ_def, hv_def]
  rw [h_lhs, h_rhs] at h
  exact h.symm

/-! ### Bridge from `lem:342B` to Butcher §321 `B(2n)` (cycle 307)

The cycle 304/305 Phase B results say that the canonical Lagrange weights
`b_j := butcherShiftedLegendre_quadratureWeights n j` at the shifted
Legendre zeros `c_j := butcherShiftedLegendre_zeros n j` integrate
*every* polynomial of degree `< 2n` exactly. Specialising the exactness
identity to the monomials `φ = X^{k-1}` for `1 ≤ k ≤ 2n` recovers the
algebraic content of Butcher §321's `B(2n)` quadrature condition:
`∑ⱼ b_j · c_j^{k-1} = 1/k` for `k = 1, …, 2n`. -/

/-- **Bridge from `lem:342B` 2n-degree exactness to the §321 `B(2n)`
order condition.** The canonical Lagrange weights at the shifted Legendre
zeros reproduce the integrals `∫₀¹ x^{k-1} dx = 1/k` exactly for every
power `1 ≤ k ≤ 2n`:

  `∑ⱼ b_j · c_j^(k-1) = 1/k`

where `c_j = butcherShiftedLegendre_zeros n j` and
`b_j = butcherShiftedLegendre_quadratureWeights n j`. This is the
algebraic content of Butcher §321 `B(2n)` for the canonical Gauss-
Legendre quadrature; lifting it to a `RKTableau` (which would let us
state it as `(gaussLegendreRK n).SatisfiesB (2 * n)`) requires
constructing the full Gauss-Legendre tableau (collocation `A`-matrix),
which is multi-cycle work deferred to cycle 308+. -/
theorem butcherShiftedLegendre_quadratureWeights_satisfiesB
    (n : ℕ) (hn : 0 < n) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 2 * n →
      (∑ j : Fin n, butcherShiftedLegendre_quadratureWeights n j *
            butcherShiftedLegendre_zeros n j ^ (k - 1))
        = 1 / (k : ℝ) := by
  intro k hk1 hk2n
  set φ : Polynomial ℝ := (Polynomial.X : Polynomial ℝ) ^ (k - 1) with hφ_def
  -- Degree bound for cycle 304's exactness lemma.
  have hdeg : φ.natDegree < 2 * n := by
    rw [hφ_def, Polynomial.natDegree_X_pow]
    omega
  -- Apply cycle 304's `2n`-degree exactness identity.
  have hex := butcherShiftedLegendre_quadrature_exact_lt_two_n n hn φ hdeg
  -- Compute the integral side via `intervalIntegral.integral_pow`.
  have hint : (∫ x in (0 : ℝ)..1, φ.eval x) = 1 / (k : ℝ) := by
    have heval : (fun x : ℝ => φ.eval x) = (fun x : ℝ => x ^ (k - 1)) := by
      funext x
      simp [hφ_def, Polynomial.eval_pow, Polynomial.eval_X]
    rw [heval, integral_pow]
    have hkk : (k - 1 : ℕ) + 1 = k := Nat.sub_add_cancel hk1
    have hzero_pow : (0 : ℝ) ^ ((k - 1 : ℕ) + 1) = 0 := by
      rw [hkk]
      exact zero_pow (by omega)
    rw [one_pow, hzero_pow, sub_zero]
    rw [show ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) by
          have := congrArg (Nat.cast : ℕ → ℝ) hkk
          push_cast at this
          linarith]
  -- Rewrite the sum side to expose `c_j ^ (k - 1)`.
  have hsum :
      (∑ j : Fin n, butcherShiftedLegendre_quadratureWeights n j *
            φ.eval (butcherShiftedLegendre_zeros n j))
        = ∑ j : Fin n, butcherShiftedLegendre_quadratureWeights n j *
            butcherShiftedLegendre_zeros n j ^ (k - 1) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [hφ_def, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hint, hsum] at hex
  exact hex.symm

/-- **Non-vacuity anchor for `B(2)` at `n = 1`.** Confirms that the
canonical Gauss-Legendre quadrature on a single node (`c₁ = 1/2`,
`b₁ = 1`) satisfies the §321 `B(2)` identity at `k = 2`:
`1 · (1/2)^1 = 1/2 = 1/2`. -/
example :
    (∑ j : Fin 1, butcherShiftedLegendre_quadratureWeights 1 j *
          butcherShiftedLegendre_zeros 1 j ^ ((2 : ℕ) - 1)) = 1 / (2 : ℝ) :=
  butcherShiftedLegendre_quadratureWeights_satisfiesB 1 (by norm_num) 2
    (by norm_num) (by norm_num)

/-- **Non-vacuity anchor for `B(2)` at `n = 1, k = 1`.** Boundary case
where `k - 1 = 0` and `c_j ^ 0 = 1`, so the identity collapses to
`∑ⱼ bⱼ = 1` for the `n = 1` Gauss method (i.e. `1 = 1/1`). -/
example :
    (∑ j : Fin 1, butcherShiftedLegendre_quadratureWeights 1 j *
          butcherShiftedLegendre_zeros 1 j ^ ((1 : ℕ) - 1)) = 1 / (1 : ℝ) := by
  have h := butcherShiftedLegendre_quadratureWeights_satisfiesB 1
    (by norm_num) 1 (by norm_num) (by norm_num)
  simpa using h

end OpenMath.Chapter3.Section342
