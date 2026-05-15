/-
# Aristotle submission: Butcher §342 (342d) norm-square integral of shifted Legendre polynomials on [0,1]

## Target

Prove `∫_0^1 P_n^*(x)^2 dx = 1 / (2n + 1)`, where `P_n^*` is Butcher's
shifted Legendre polynomial on `[0, 1]` (signed so that `P_n^*(1) = 1`).

## Strategy hint

Apply the Rodrigues formula `butcherShiftedLegendre_rodrigues`:

  n! · P_n^* = (-1)^n · D^n (X^n (1-X)^n)

so

  P_n^*(x) = ((-1)^n / n!) · D^n (x^n (1-x)^n).

Substitute one factor of `P_n^*` in the integrand and apply integration
by parts `n` times. Each step transfers one derivative from the
Rodrigues factor onto the remaining `P_n^*` factor; the boundary
contributions vanish because at step `k < n` the surviving factor
`D^k (x^n (1-x)^n)` still carries a factor of `x · (1-x)` (by Leibniz)
and so vanishes at both `x = 0` and `x = 1`.

After `n` IBPs, all derivatives sit on the second `P_n^*` factor.
Its `n`-th derivative is constant — equal to the leading coefficient
of `P_n^*` times `n!`. Since `P_n^* = (-1)^n · (Mathlib's shiftedLegendre n).map ι`
and `Polynomial.coeff_shiftedLegendre` gives the leading coefficient,
this constant is `((-1)^n)^2 · C(2n, n) · n! = C(2n, n) · n! = (2n)!/n!`.

The integral therefore collapses to

  ((-1)^n / n!) · (-1)^n · ((2n)!/n!) · ∫₀¹ x^n (1-x)^n dx
    = ((2n)!/(n!)^2) · B(n+1, n+1)
    = ((2n)!/(n!)^2) · ((n!)^2 / (2n+1)!)
    = (2n)! / (2n+1)!
    = 1/(2n+1).

The Beta-function identity `∫₀¹ x^n (1-x)^n dx = (n!)^2 / (2n+1)!` can
be derived from Mathlib's `Real.GammaIntegral` machinery, or proved
inline by induction on `n` using the substitution `u = 1 - x` and
IBP × n.

The setup leverages cycle 271/272/273's shipped lemmas, provided as
named hypotheses below so Aristotle can cite them directly:
* `butcherShiftedLegendre_eval_one`        : (342b) `P_n^*(1) = 1`
* `butcherShiftedLegendre_eval_one_sub`    : (342c) parity at `1 - x`
* `butcherShiftedLegendre_rodrigues`       : (342e) Rodrigues' formula
* `butcherShiftedLegendre_natDegree`       : `natDegree P_n^* = n`
* `butcherShiftedLegendre_eval_zero`       : `P_n^*(0) = (-1)^n`
* `butcherShiftedLegendre_zero`            : `P_0^* = C 1`
* `butcherShiftedLegendre_one`             : `P_1^* = C 2 * X - C 1`

These are provided as axioms so Aristotle can cite them directly
without needing to re-prove the prerequisites. The (342d) target is
the only sorry to fill.
-/

import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Data.Real.Basic

namespace OpenMath.Chapter3.Section342Aristotle

open Polynomial

/-- **Butcher's shifted Legendre polynomial** `P_n^*` on `[0,1]`. -/
noncomputable def butcherShiftedLegendre (n : ℕ) : Polynomial ℝ :=
  Polynomial.C ((-1 : ℝ) ^ n) *
    (Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)

/-- (342b) — provided as a hypothesis for Aristotle. -/
axiom butcherShiftedLegendre_eval_one (n : ℕ) :
    (butcherShiftedLegendre n).eval 1 = 1

/-- (342c) — provided as a hypothesis for Aristotle. -/
axiom butcherShiftedLegendre_eval_one_sub (n : ℕ) (x : ℝ) :
    (butcherShiftedLegendre n).eval (1 - x) =
      (-1 : ℝ) ^ n * (butcherShiftedLegendre n).eval x

/-- (342e) — Rodrigues' formula, provided as a hypothesis for Aristotle.

`n! · P_n^*(x) = (-1)^n (d/dx)^n (x^n (1-x)^n)` as an identity in `ℝ[X]`. -/
axiom butcherShiftedLegendre_rodrigues (n : ℕ) :
    Polynomial.C ((n.factorial : ℝ)) * butcherShiftedLegendre n
      = Polynomial.C ((-1 : ℝ) ^ n) *
        Polynomial.derivative^[n]
          ((Polynomial.X : Polynomial ℝ) ^ n *
            (1 - (Polynomial.X : Polynomial ℝ)) ^ n)

/-- (degree) — provided as a hypothesis for Aristotle. -/
axiom butcherShiftedLegendre_natDegree (n : ℕ) :
    (butcherShiftedLegendre n).natDegree = n

/-- `P_n^*(0) = (-1)^n` — provided as a hypothesis for Aristotle. -/
axiom butcherShiftedLegendre_eval_zero (n : ℕ) :
    (butcherShiftedLegendre n).eval 0 = (-1 : ℝ) ^ n

/-- `P_0^* = C 1` — provided as a hypothesis for Aristotle. -/
axiom butcherShiftedLegendre_zero :
    butcherShiftedLegendre 0 = Polynomial.C 1

/-- `P_1^* = C 2 * X - C 1` — provided as a hypothesis for Aristotle. -/
axiom butcherShiftedLegendre_one :
    butcherShiftedLegendre 1 =
      Polynomial.C 2 * Polynomial.X - Polynomial.C 1

/-- **Butcher §342 (342d)** — norm-square integral on `[0, 1]`.

For all `n`, `∫_0^1 (P_n^*(x))^2 dx = 1 / (2n + 1)`. -/
theorem butcherShiftedLegendre_norm_sq (n : ℕ) :
    ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre n).eval x ^ 2 =
      1 / (2 * n + 1) := by
  sorry

end OpenMath.Chapter3.Section342Aristotle
