/-
# Aristotle submission v2 (cycle 285): Butcher §342 (342f) three-term recurrence

## Target

Prove the Bonnet-style three-term recurrence for Butcher's shifted
Legendre polynomials `P_n^*` on `[0, 1]`:

  n · P_n^*(x) = (2x − 1)(2n − 1) · P_{n−1}^*(x) − (n − 1) · P_{n−2}^*(x),
                                                     n = 2, 3, 4, …

This is Butcher §342, equation (342f), p. 236.

## Strengthening over cycle 282 submission

The cycle 282 submission stalled in Aristotle (12% for three consecutive
polls). This v2 adds:

* `integral_poly_mul_iterDeriv_vanish`  — cycle 277's iterated-IBP lemma,
  the core orthogonality machinery, axiomatized so Aristotle can cite it
  directly.
* `butcherShiftedLegendre_leadingCoeff` — cycle 281's leading-coefficient
  identity `lc(P_n^*) = C(2n, n)`, axiomatized for Step 1 of the
  textbook proof (degree-comparison).
* Explicit small-`n` forms now extended to `n = 0, 1, ..., 8` (cycle 282
  only supplied through `n = 4`).
* The textbook proof sketch from `lem_342A.json` quoted verbatim.

## Textbook proof sketch (verbatim from `extraction/formalization_data/entities/lem_342A.json`)

> The highest degree coefficients in P_n^* and P_{n-1}^* can be compared
> so that n P_n^*(x) - (2x - 1)(2n - 1) P_{n-1}^*(x) is a polynomial, Q
> say, of degree less than n. Because Q has the same parity as n, it is
> of degree less than n - 1. A simple calculation shows that Q is
> orthogonal to P_k^* for k < n - 2. Hence, (342f) follows except for
> the value of the P_{n-2}^* coefficient, which is resolved by
> substituting x = 1.

Translated to the explicit Q := n·P_n^* − (2x−1)(2n−1)·P_{n−1}^* + (n−1)·P_{n−2}^*:

  Step 1 (degree < n).  Leading-coefficient identity:
    lc(P_n^*) = C(2n, n);
    lc((2X−1)(2n−1) P_{n−1}^*) = 2(2n − 1) · C(2n − 2, n − 1).
    Pascal-style identity: n · C(2n, n) = 2(2n − 1) · C(2n − 2, n − 1).
    So the X^n coefficient in Q is `0`, hence natDegree(Q) < n.

  Step 2 (degree < n − 1).  Parity: by (342c), P_n^*(1 − x) = (−1)^n P_n^*(x).
    Q(1 − x) = n·(−1)^n P_n^*(x) − (1 − 2x)(2n − 1)·(−1)^{n−1} P_{n−1}^*(x)
              + (n − 1)·(−1)^{n−2} P_{n−2}^*(x)
            = (−1)^n · Q(x).
    Combined with Step 1, the X^{n−1} coefficient in Q must vanish
    (parity forces consecutive coefficients to alternate signs around
    midpoint x = 1/2; an "even-around-1/2" polynomial of degree < n
    of parity n has no X^{n−1} term).

  Step 3 (orthogonality).  For k ≤ n − 3, k < n − 2, by (342a) each of
    ∫₀¹ P_k^* · P_n^* dx, ∫₀¹ P_k^* · X · P_{n−1}^* dx, ∫₀¹ P_k^* · P_{n−2}^* dx
    can be shown to vanish (the second by writing X·P_{n−1}^* in the basis
    P_0^*, …, P_n^* and noting only the k-th coefficient can match; but the
    full basis expansion is not needed: by `integral_poly_mul_iterDeriv_vanish`,
    ∫₀¹ p(x) D^n((X(1−X))^n) dx = 0 whenever `natDegree p < n`).
    Combined with Steps 1+2: Q has natDegree < n−1 ≤ n−2, hence
    ∫₀¹ Q · P_k^* dx = 0 for all k.  In particular for k = n−2.

  Step 4 (resolving the P_{n−2}^* coefficient).  Substitute x = 1:
    LHS = n · P_n^*(1) = n · 1 = n.
    RHS = 1 · (2n − 1) · P_{n−1}^*(1) − (n − 1) · P_{n−2}^*(1)
        = (2n − 1) − (n − 1) = n.  ✓
    So the difference (LHS − RHS) at x = 1 is 0.
    Since by Steps 1+2+3 the difference is a polynomial of natDegree < n − 1
    orthogonal to P_0^*, …, P_{n−3}^*, and these last form an (n − 2)-
    dimensional basis of the (n − 2)-dimensional space of polynomials of
    degree ≤ n − 3, the difference is a multiple of P_{n−2}^*; let
    Q = c · P_{n−2}^*. At x = 1, c · P_{n−2}^*(1) = c · 1 = c = 0 by
    direct calculation. So Q = 0.

## Cited prerequisites (provided as axioms)

All cycles 271–281 results are bundled below as named hypotheses, so
Aristotle may cite them directly without re-proving.
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

/-- (342b) — `P_n^*(1) = 1`. -/
axiom butcherShiftedLegendre_eval_one (n : ℕ) :
    (butcherShiftedLegendre n).eval 1 = 1

/-- (342c) — parity at `1 − x`. -/
axiom butcherShiftedLegendre_eval_one_sub (n : ℕ) (x : ℝ) :
    (butcherShiftedLegendre n).eval (1 - x) =
      (-1 : ℝ) ^ n * (butcherShiftedLegendre n).eval x

/-- `P_n^*(0) = (−1)^n`. -/
axiom butcherShiftedLegendre_eval_zero (n : ℕ) :
    (butcherShiftedLegendre n).eval 0 = (-1 : ℝ) ^ n

/-- natDegree. -/
axiom butcherShiftedLegendre_natDegree (n : ℕ) :
    (butcherShiftedLegendre n).natDegree = n

/-- (342e) — Rodrigues' formula. -/
axiom butcherShiftedLegendre_rodrigues (n : ℕ) :
    Polynomial.C ((n.factorial : ℝ)) * butcherShiftedLegendre n
      = Polynomial.C ((-1 : ℝ) ^ n) *
        Polynomial.derivative^[n]
          ((Polynomial.X : Polynomial ℝ) ^ n *
            (1 - (Polynomial.X : Polynomial ℝ)) ^ n)

/-- (342a) — orthogonality on `[0, 1]`. -/
axiom butcherShiftedLegendre_orthogonal {m n : ℕ} (hmn : m ≠ n) :
    ∫ x in (0 : ℝ)..1,
      (butcherShiftedLegendre m).eval x *
      (butcherShiftedLegendre n).eval x = 0

/-- (342d) — norm-square integral. -/
axiom butcherShiftedLegendre_norm_sq (n : ℕ) :
    ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre n).eval x ^ 2 =
      1 / (2 * (n : ℝ) + 1)

/-- **Cycle 281**: `lc(P_n^*) = C(2n, n)`. -/
axiom butcherShiftedLegendre_leadingCoeff (n : ℕ) :
    (butcherShiftedLegendre n).leadingCoeff = (Nat.choose (2 * n) n : ℝ)

/-- **Cycle 277**: general iterated-IBP lemma. If `natDegree f < n`
and all `D^k g` vanish at both endpoints for `k < n`, then
`∫₀¹ f · D^n(g) = 0`. -/
axiom integral_poly_mul_iterDeriv_vanish
    (f g : Polynomial ℝ) (n : ℕ)
    (hf : f.natDegree < n)
    (hg0 : ∀ k, k < n → (Polynomial.derivative^[k] g).eval (0:ℝ) = 0)
    (hg1 : ∀ k, k < n → (Polynomial.derivative^[k] g).eval (1:ℝ) = 0) :
    ∫ x in (0:ℝ)..1,
      f.eval x * (Polynomial.derivative^[n] g).eval x = 0

/-- Specialization to `g = X^n · (1-X)^n`: for `f` with `natDegree f < n`,
`∫₀¹ f · D^n(X^n · (1-X)^n) = 0`. Combined with Rodrigues this implies
`∫₀¹ f · P_n^* = 0` whenever `natDegree f < n`. -/
axiom integral_poly_mul_iterDeriv_XnOneSubXn_eq_zero
    (f : Polynomial ℝ) (n : ℕ) (hf : f.natDegree < n) :
    ∫ x in (0:ℝ)..1,
      f.eval x * (Polynomial.derivative^[n]
        ((Polynomial.X : Polynomial ℝ) ^ n *
          (1 - Polynomial.X) ^ n)).eval x = 0

/-! ### Explicit small-`n` forms — provided as axioms. -/

axiom butcherShiftedLegendre_zero :
    butcherShiftedLegendre 0 = Polynomial.C 1

axiom butcherShiftedLegendre_one :
    butcherShiftedLegendre 1 =
      Polynomial.C 2 * Polynomial.X - Polynomial.C 1

axiom butcherShiftedLegendre_two :
    butcherShiftedLegendre 2 =
      Polynomial.C 6 * Polynomial.X ^ 2 - Polynomial.C 6 * Polynomial.X
        + Polynomial.C 1

axiom butcherShiftedLegendre_three :
    butcherShiftedLegendre 3 =
      Polynomial.C 20 * Polynomial.X ^ 3 - Polynomial.C 30 * Polynomial.X ^ 2
        + Polynomial.C 12 * Polynomial.X - Polynomial.C 1

axiom butcherShiftedLegendre_four :
    butcherShiftedLegendre 4 =
      Polynomial.C 70 * Polynomial.X ^ 4
        - Polynomial.C 140 * Polynomial.X ^ 3
        + Polynomial.C 90 * Polynomial.X ^ 2
        - Polynomial.C 20 * Polynomial.X
        + Polynomial.C 1

axiom butcherShiftedLegendre_five :
    butcherShiftedLegendre 5 =
      Polynomial.C 252 * Polynomial.X ^ 5
        - Polynomial.C 630 * Polynomial.X ^ 4
        + Polynomial.C 560 * Polynomial.X ^ 3
        - Polynomial.C 210 * Polynomial.X ^ 2
        + Polynomial.C 30 * Polynomial.X
        - Polynomial.C 1

axiom butcherShiftedLegendre_six :
    butcherShiftedLegendre 6 =
      Polynomial.C 924 * Polynomial.X ^ 6
        - Polynomial.C 2772 * Polynomial.X ^ 5
        + Polynomial.C 3150 * Polynomial.X ^ 4
        - Polynomial.C 1680 * Polynomial.X ^ 3
        + Polynomial.C 420 * Polynomial.X ^ 2
        - Polynomial.C 42 * Polynomial.X
        + Polynomial.C 1

axiom butcherShiftedLegendre_seven :
    butcherShiftedLegendre 7 =
      Polynomial.C 3432 * Polynomial.X ^ 7
        - Polynomial.C 12012 * Polynomial.X ^ 6
        + Polynomial.C 16632 * Polynomial.X ^ 5
        - Polynomial.C 11550 * Polynomial.X ^ 4
        + Polynomial.C 4200 * Polynomial.X ^ 3
        - Polynomial.C 756 * Polynomial.X ^ 2
        + Polynomial.C 56 * Polynomial.X
        - Polynomial.C 1

axiom butcherShiftedLegendre_eight :
    butcherShiftedLegendre 8 =
      Polynomial.C 12870 * Polynomial.X ^ 8
        - Polynomial.C 51480 * Polynomial.X ^ 7
        + Polynomial.C 84084 * Polynomial.X ^ 6
        - Polynomial.C 72072 * Polynomial.X ^ 5
        + Polynomial.C 34650 * Polynomial.X ^ 4
        - Polynomial.C 9240 * Polynomial.X ^ 3
        + Polynomial.C 1260 * Polynomial.X ^ 2
        - Polynomial.C 72 * Polynomial.X
        + Polynomial.C 1

/-! ### Witnessed small-`n` instances of (342f) (cycles 282–284 + cycle 285 n=9). -/

axiom butcherShiftedLegendre_recurrence_two :
    (2 : ℝ) • butcherShiftedLegendre 2 =
      Polynomial.C 3 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 1
      - Polynomial.C 1 * butcherShiftedLegendre 0

axiom butcherShiftedLegendre_recurrence_three :
    (3 : ℝ) • butcherShiftedLegendre 3 =
      Polynomial.C 5 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 2
      - Polynomial.C 2 * butcherShiftedLegendre 1

axiom butcherShiftedLegendre_recurrence_four :
    (4 : ℝ) • butcherShiftedLegendre 4 =
      Polynomial.C 7 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 3
      - Polynomial.C 3 * butcherShiftedLegendre 2

axiom butcherShiftedLegendre_recurrence_five :
    (5 : ℝ) • butcherShiftedLegendre 5 =
      Polynomial.C 9 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 4
      - Polynomial.C 4 * butcherShiftedLegendre 3

axiom butcherShiftedLegendre_recurrence_six :
    (6 : ℝ) • butcherShiftedLegendre 6 =
      Polynomial.C 11 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 5
      - Polynomial.C 5 * butcherShiftedLegendre 4

axiom butcherShiftedLegendre_recurrence_seven :
    (7 : ℝ) • butcherShiftedLegendre 7 =
      Polynomial.C 13 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 6
      - Polynomial.C 6 * butcherShiftedLegendre 5

axiom butcherShiftedLegendre_recurrence_eight :
    (8 : ℝ) • butcherShiftedLegendre 8 =
      Polynomial.C 15 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 7
      - Polynomial.C 7 * butcherShiftedLegendre 6

/-- **Butcher §342 (342f)** — three-term recurrence for the shifted
Legendre polynomials on `[0, 1]`.

For all `n ≥ 2`,
  n · P_n^*(x) = (2x − 1)(2n − 1) · P_{n−1}^*(x) − (n − 1) · P_{n−2}^*(x).

See the long comment at the top of this file for the textbook proof
sketch and a Lean-oriented re-translation of each step. -/
theorem butcherShiftedLegendre_recurrence (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) • butcherShiftedLegendre n =
      Polynomial.C (2 * (n : ℝ) - 1)
        * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre (n - 1)
      - Polynomial.C ((n : ℝ) - 1) * butcherShiftedLegendre (n - 2) := by
  sorry

end OpenMath.Chapter3.Section342Aristotle
