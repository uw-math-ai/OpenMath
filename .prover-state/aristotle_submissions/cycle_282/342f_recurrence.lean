/-
# Aristotle submission: Butcher §342 (342f) three-term recurrence

## Target

Prove the Bonnet-style three-term recurrence for Butcher's shifted
Legendre polynomials `P_n^*` on `[0, 1]`:

  n · P_n^*(x) = (2x − 1)(2n − 1) · P_{n−1}^*(x) − (n − 1) · P_{n−2}^*(x),
                                                     n = 2, 3, 4, …

This is Butcher §342, equation (342f), p. 236.

## Strategy hint (textbook proof outline)

Butcher §342, p. 236 sketch:

  Step 1. Let Q := n · P_n^* − (2x − 1)(2n − 1) · P_{n−1}^* − (n − 1) · P_{n−2}^*.
          Compare highest-degree coefficients to show Q has degree < n.
          Leading coefficient identity: lc(P_n^*) = C(2n, n);
          lc((2x − 1)(2n − 1) · P_{n−1}^*) = 2(2n − 1) · C(2n − 2, n − 1).
          The identity n · C(2n, n) = 2(2n − 1) · C(2n − 2, n − 1) closes
          step 1 (provable via `Nat.choose` factorial expansion).

  Step 2. By parity (342c), `P_n^*(1 − x) = (-1)^n · P_n^*(x)`, so Q has
          the same parity as n. Combined with degree < n, this gives
          degree(Q) < n − 1.

  Step 3. Q is orthogonal to P_k^* for all k < n − 2 (by (342a), since
          Q has degree at most n − 2 and (342a) gives orthogonality to
          all P_k^* with k > degree(Q)). Combined with degree < n − 1,
          Q is determined by its coefficient on P_{n−2}^*.

  Step 4. Substitute x = 1 to fix the P_{n−2}^* coefficient:
            LHS = n · P_n^*(1) = n · 1 = n.
            RHS = 1 · (2n − 1) · P_{n−1}^*(1) − (n − 1) · P_{n−2}^*(1)
                = (2n − 1) − (n − 1) = n.   ✓

  So Q = 0, which is the claim.

## Cited prerequisites (provided as axioms)

All cycles 271–281 results are bundled as named hypotheses below, so
Aristotle may cite them directly without re-proving:

* `butcherShiftedLegendre`              definition.
* `butcherShiftedLegendre_eval_one`     (342b) `P_n^*(1) = 1`
* `butcherShiftedLegendre_eval_one_sub` (342c) parity at `1 − x`
* `butcherShiftedLegendre_eval_zero`    `P_n^*(0) = (−1)^n`
* `butcherShiftedLegendre_natDegree`    `natDegree P_n^* = n`
* `butcherShiftedLegendre_rodrigues`    (342e) Rodrigues' formula
* `butcherShiftedLegendre_orthogonal`   (342a) orthogonality on `[0, 1]`
* `butcherShiftedLegendre_norm_sq`      (342d) `∫₀¹ P_n^*(x)² dx = 1/(2n+1)`
* `butcherShiftedLegendre_zero/one/two/three/four` — explicit small-n forms.

Small-`n` sanity check (verified on paper):

  n = 2: 2·P_2^* = 3(2x − 1)·P_1^* − P_0^*.
    LHS:  2(6x² − 6x + 1) = 12x² − 12x + 2.
    RHS:  3(2x − 1)² − 1 = 12x² − 12x + 2.  ✓

  n = 3: 3·P_3^* = 5(2x − 1)·P_2^* − 2·P_1^*.
    LHS:  3(20x³ − 30x² + 12x − 1) = 60x³ − 90x² + 36x − 3.
    RHS:  5(2x − 1)(6x² − 6x + 1) − 2(2x − 1) = 60x³ − 90x² + 36x − 3.  ✓

  n = 4: 4·P_4^* = 7(2x − 1)·P_3^* − 3·P_2^*.
    LHS:  4(70x⁴ − 140x³ + 90x² − 20x + 1)
        = 280x⁴ − 560x³ + 360x² − 80x + 4.
    RHS:  7(2x − 1)(20x³ − 30x² + 12x − 1) − 3(6x² − 6x + 1)
        = 280x⁴ − 560x³ + 360x² − 80x + 4.  ✓

The (342f) target is the only sorry to fill.
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

/-- `P_n^*(0) = (−1)^n` — provided as a hypothesis for Aristotle. -/
axiom butcherShiftedLegendre_eval_zero (n : ℕ) :
    (butcherShiftedLegendre n).eval 0 = (-1 : ℝ) ^ n

/-- (natDegree) — provided as a hypothesis for Aristotle. -/
axiom butcherShiftedLegendre_natDegree (n : ℕ) :
    (butcherShiftedLegendre n).natDegree = n

/-- (342e) — Rodrigues' formula, provided as a hypothesis for Aristotle. -/
axiom butcherShiftedLegendre_rodrigues (n : ℕ) :
    Polynomial.C ((n.factorial : ℝ)) * butcherShiftedLegendre n
      = Polynomial.C ((-1 : ℝ) ^ n) *
        Polynomial.derivative^[n]
          ((Polynomial.X : Polynomial ℝ) ^ n *
            (1 - (Polynomial.X : Polynomial ℝ)) ^ n)

/-- (342a) — orthogonality on `[0, 1]`, provided as a hypothesis for Aristotle. -/
axiom butcherShiftedLegendre_orthogonal {m n : ℕ} (hmn : m ≠ n) :
    ∫ x in (0 : ℝ)..1,
      (butcherShiftedLegendre m).eval x *
      (butcherShiftedLegendre n).eval x = 0

/-- (342d) — norm-square integral, provided as a hypothesis for Aristotle. -/
axiom butcherShiftedLegendre_norm_sq (n : ℕ) :
    ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre n).eval x ^ 2 =
      1 / (2 * (n : ℝ) + 1)

/-- `P_0^* = C 1` — provided as a hypothesis for Aristotle. -/
axiom butcherShiftedLegendre_zero :
    butcherShiftedLegendre 0 = Polynomial.C 1

/-- `P_1^* = C 2 * X − C 1` — provided as a hypothesis for Aristotle. -/
axiom butcherShiftedLegendre_one :
    butcherShiftedLegendre 1 =
      Polynomial.C 2 * Polynomial.X - Polynomial.C 1

/-- `P_2^* = 6X² − 6X + 1` — provided as a hypothesis for Aristotle. -/
axiom butcherShiftedLegendre_two :
    butcherShiftedLegendre 2 =
      Polynomial.C 6 * Polynomial.X ^ 2 - Polynomial.C 6 * Polynomial.X
        + Polynomial.C 1

/-- `P_3^* = 20X³ − 30X² + 12X − 1` — provided as a hypothesis for Aristotle. -/
axiom butcherShiftedLegendre_three :
    butcherShiftedLegendre 3 =
      Polynomial.C 20 * Polynomial.X ^ 3 - Polynomial.C 30 * Polynomial.X ^ 2
        + Polynomial.C 12 * Polynomial.X - Polynomial.C 1

/-- `P_4^* = 70X⁴ − 140X³ + 90X² − 20X + 1` — provided as a hypothesis for Aristotle. -/
axiom butcherShiftedLegendre_four :
    butcherShiftedLegendre 4 =
      Polynomial.C 70 * Polynomial.X ^ 4
        - Polynomial.C 140 * Polynomial.X ^ 3
        + Polynomial.C 90 * Polynomial.X ^ 2
        - Polynomial.C 20 * Polynomial.X
        + Polynomial.C 1

/-- **Butcher §342 (342f)** — three-term recurrence for the shifted
Legendre polynomials on `[0, 1]`.

For all `n ≥ 2`,
  n · P_n^*(x) = (2x − 1)(2n − 1) · P_{n−1}^*(x) − (n − 1) · P_{n−2}^*(x). -/
theorem butcherShiftedLegendre_recurrence (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) • butcherShiftedLegendre n =
      Polynomial.C (2 * (n : ℝ) - 1)
        * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre (n - 1)
      - Polynomial.C ((n : ℝ) - 1) * butcherShiftedLegendre (n - 2) := by
  sorry

end OpenMath.Chapter3.Section342Aristotle
