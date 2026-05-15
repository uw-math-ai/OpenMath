/-
# Aristotle submission: Butcher §342 (342a) orthogonality of shifted Legendre polynomials on [0,1]

## Target

Prove `∫_0^1 P_m^*(x) P_n^*(x) dx = 0` for `m ≠ n`, where `P_n^*` is
Butcher's shifted Legendre polynomial (signed so that `P_n^*(1) = 1`).

## Strategy hint

Use Rodrigues' formula `butcherShiftedLegendre_rodrigues`
(`n! · P_n^* = (-1)^n · D^n (X^n (1-X)^n)`) plus integration by parts
`n` times. The boundary terms at `x = 0` and `x = 1` vanish for every
`k < n` because `D^k (X^n (1-X)^n)` has a factor of `X^{n-k} (1-X)^{n-k}`
remaining in every Leibniz product-rule summand, and both `X^{n-k}` and
`(1-X)^{n-k}` vanish at `0` and `1` respectively when `n - k ≥ 1`.

Repeating `n` integrations by parts moves all derivatives onto
`P_m^*`, which is a polynomial of degree `m < n`, so `D^n P_m^* = 0`,
killing the integral.

The setup may also leverage cycle 271/272's shipped lemmas:
* `butcherShiftedLegendre_eval_one`        : (342b) `P_n^*(1) = 1`
* `butcherShiftedLegendre_eval_one_sub`    : (342c) parity at `1 - x`
* `butcherShiftedLegendre_rodrigues`       : (342e) Rodrigues' formula
* `butcherShiftedLegendre_natDegree`       : `natDegree P_n^* = n`

These are provided as named hypotheses below so Aristotle can cite
them directly without needing to re-prove or re-derive.
-/

import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegrationByParts
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

/-- **Butcher §342 (342a)** — orthogonality on `[0, 1]`.

For all `m ≠ n`, `∫_0^1 P_m^*(x) · P_n^*(x) dx = 0`. -/
theorem butcherShiftedLegendre_orthogonal {m n : ℕ} (hmn : m ≠ n) :
    ∫ x in (0 : ℝ)..1,
      (butcherShiftedLegendre m).eval x *
      (butcherShiftedLegendre n).eval x = 0 := by
  sorry

end OpenMath.Chapter3.Section342Aristotle
