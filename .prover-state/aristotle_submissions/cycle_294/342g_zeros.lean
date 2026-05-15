/-
# Aristotle submission: Butcher §342 (342g) — `P_n^*` has `n` distinct real zeros in `(0, 1)`

## Target

Prove that the Butcher shifted Legendre polynomial `P_n^*` on `[0, 1]`
has `n` distinct real zeros in the open interval `(0, 1)`. That is,
there is a finite set `xs ⊆ (0, 1)` of cardinality `n`, all of whose
elements are roots of `P_n^*`.

## Strategy hint

Proof by contradiction. Suppose `P_n^*` has fewer than `n` sign-change
points in `(0, 1)`. Let `x_1, …, x_k` be the distinct sign-change
points (`k < n`), and form
`Q := ∏ᵢ (X − Polynomial.C xᵢ)` with `natDegree = k < n`. Then
`P_n^*(x) · Q(x)` has constant non-zero sign on `(0, 1)` except at
the finite root set (sign changes paired off), so
`∫₀¹ P_n^* · Q ≠ 0`. But
`butcherShiftedLegendre_orthogonal_to_lower_degree n Q hq` (cycle 292)
with `hq : Q.natDegree < n` gives `∫₀¹ P_n^* · Q = 0`. Contradiction.

Combined with `(P_n^*).natDegree = n` and
`(P_n^*).roots.card ≤ natDegree`, equality is forced and the zeros
are all in `(0, 1)`.

The named axioms below are all *closed* lemmas at HEAD in
`OpenMath/Chapter3/Section342.lean`. They are reproduced here as
axiom statements so Aristotle has the full toolkit:
* `butcherShiftedLegendre_eval_one`         : (342b) `P_n^*(1) = 1`
* `butcherShiftedLegendre_eval_one_sub`     : (342c) parity
* `butcherShiftedLegendre_eval_zero`        : `P_n^*(0) = (-1)^n`
* `butcherShiftedLegendre_natDegree`        : `natDegree P_n^* = n`
* `butcherShiftedLegendre_rodrigues`        : (342e) Rodrigues
* `butcherShiftedLegendre_orthogonal`       : (342a) general orthogonality
* `butcherShiftedLegendre_norm_sq`          : (342d) `∫ (P_n^*)² = 1/(2n+1)`
* `butcherShiftedLegendre_orthogonal_to_lower_degree` : the **key**
  lemma for the contradiction argument
* `butcherShiftedLegendre_recurrence`       : (342f) three-term recurrence
* Explicit forms `_zero`, `_one`, `_two` for base cases.

Integrals here are `intervalIntegral` form `∫ x in (0:ℝ)..1, ...`,
NOT measure-theoretic unbounded form. Use
`MeasureTheory.intervalIntegral` API.
-/

import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

namespace OpenMath.Chapter3.Section342Aristotle342g

open Polynomial

/-- **Butcher's shifted Legendre polynomial** `P_n^*` on `[0, 1]`. -/
noncomputable def butcherShiftedLegendre (n : ℕ) : Polynomial ℝ :=
  Polynomial.C ((-1 : ℝ) ^ n) *
    (Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)

/-- (342b) — provided as axiom. -/
axiom butcherShiftedLegendre_eval_one (n : ℕ) :
    (butcherShiftedLegendre n).eval 1 = 1

/-- (342c) — provided as axiom. -/
axiom butcherShiftedLegendre_eval_one_sub (n : ℕ) (x : ℝ) :
    (butcherShiftedLegendre n).eval (1 - x) =
      (-1 : ℝ) ^ n * (butcherShiftedLegendre n).eval x

/-- `P_n^*(0) = (-1)^n` — provided as axiom. -/
axiom butcherShiftedLegendre_eval_zero (n : ℕ) :
    (butcherShiftedLegendre n).eval 0 = (-1 : ℝ) ^ n

/-- (degree) — provided as axiom. -/
axiom butcherShiftedLegendre_natDegree (n : ℕ) :
    (butcherShiftedLegendre n).natDegree = n

/-- Explicit forms for small `n` — provided as axioms. -/
axiom butcherShiftedLegendre_zero :
    butcherShiftedLegendre 0 = Polynomial.C 1

axiom butcherShiftedLegendre_one :
    butcherShiftedLegendre 1 =
      Polynomial.C 2 * Polynomial.X - Polynomial.C 1

axiom butcherShiftedLegendre_two :
    butcherShiftedLegendre 2 =
      Polynomial.C 6 * Polynomial.X ^ 2 - Polynomial.C 6 * Polynomial.X
        + Polynomial.C 1

/-- (342e) — Rodrigues' formula. -/
axiom butcherShiftedLegendre_rodrigues (n : ℕ) :
    Polynomial.C ((n.factorial : ℝ)) * butcherShiftedLegendre n
      = Polynomial.C ((-1 : ℝ) ^ n) *
        Polynomial.derivative^[n]
          ((Polynomial.X : Polynomial ℝ) ^ n *
            (1 - (Polynomial.X : Polynomial ℝ)) ^ n)

/-- (342a) — general orthogonality. -/
axiom butcherShiftedLegendre_orthogonal {m n : ℕ} (hmn : m ≠ n) :
    ∫ x in (0 : ℝ)..1,
      (butcherShiftedLegendre m).eval x *
      (butcherShiftedLegendre n).eval x = 0

/-- (342d) — `∫ (P_n^*)² = 1/(2n+1)`. -/
axiom butcherShiftedLegendre_norm_sq (n : ℕ) :
    ∫ x in (0 : ℝ)..1,
      ((butcherShiftedLegendre n).eval x) ^ 2 = 1 / (2 * n + 1)

/-- (342f) — three-term recurrence (`n ≥ 2`). -/
axiom butcherShiftedLegendre_recurrence (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) • butcherShiftedLegendre n =
      Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
        (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
        butcherShiftedLegendre (n - 1)
      - Polynomial.C ((n - 1 : ℕ) : ℝ) *
        butcherShiftedLegendre (n - 2)

/-- **The KEY axiom**: orthogonality of `P_n^*` to every polynomial of
strictly smaller degree (cycle 292). For any `q : Polynomial ℝ` with
`natDegree q < n`, we have `∫₀¹ P_n^*(x) · q(x) dx = 0`.

This is the *load-bearing* lemma for the (342g) sign-change argument:
the product `Q := ∏ᵢ (X − C xᵢ)` of sign-change linear factors has
degree `< n`, so its integral against `P_n^*` is zero. -/
axiom butcherShiftedLegendre_orthogonal_to_lower_degree
    (m : ℕ) (q : Polynomial ℝ) (hq : q.natDegree < m) :
    ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre m).eval x * q.eval x = 0

/-- **Butcher §342 (342g)** — `P_n^*` has `n` distinct real zeros in `(0, 1)`.

For every `n`, there is a finite set `xs ⊆ (0, 1)` of cardinality `n`
all of whose elements are roots of `P_n^*`. -/
theorem butcherShiftedLegendre_n_distinct_real_zeros (n : ℕ) :
    ∃ (xs : Finset ℝ), xs.card = n ∧
      (∀ x ∈ xs, x ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ x ∈ xs, (butcherShiftedLegendre n).eval x = 0) := by
  sorry

end OpenMath.Chapter3.Section342Aristotle342g
