import OpenMath.Chapter3.Section342

/-!
# Butcher §344 — Radau and Lobatto quadrature polynomials (Phase A)

This file opens Butcher §344 by defining the three polynomial families
whose roots in `[0, 1]` are the Radau I, Radau II, and Lobatto
quadrature abscissae:

* `butcherRadauI s   = P_s^* + P_{s-1}^*`,
* `butcherRadauII s  = P_s^* - P_{s-1}^*`,
* `butcherLobatto s  = P_s^* - P_{s-2}^*`,

where `P_n^* = butcherShiftedLegendre n` is Butcher's shifted Legendre
polynomial from §342.

## Anchor entity

`thm:344A` (Butcher, *Numerical Methods for Ordinary Differential
Equations*, 3rd ed., §344, p. 244). The textbook statement (verbatim
from `extraction/formalization_data/entities/thm_344A.json`):

> Let `c_1 < c_2 < … < c_s` be chosen as abscissae of the Radau I, the
> Radau II or the Lobatto quadrature formula, respectively. Then:
>   I.   For the Radau I formula, `c_1 = 0`. This formula is exact for
>        polynomials of degree up to `2s − 2`.
>   II.  For the Radau II formula, `c_s = 1`. This formula is exact for
>        polynomials of degree up to `2s − 2`.
>   III. For the Lobatto formula, `c_1 = 0`, `c_s = 1`. This formula is
>        exact for polynomials of degree up to `2s − 3`.
> Furthermore, for each of the three quadrature formulae,
> `c_i ∈ [0, 1]` for `i = 1, 2, …, s`, and `b_i > 0` for `i = 1, 2, …, s`.

The proof in Butcher (p. 244) opens with the observation that

* `x = 1` is a zero of `P_s^*(x) − P_{s-1}^*(x)` and of
  `P_s^*(x) − P_{s-2}^*(x)` (from (342b): `P_n^*(1) = 1`);
* `x = 0` is a zero of `P_s^*(x) + P_{s-1}^*(x)` and of
  `P_s^*(x) − P_{s-2}^*(x)` (from (342c) parity at `x = 1`,
  equivalently from `P_n^*(0) = (-1)^n`).

This file ships **Phase A** of `thm:344A`: the polynomial definitions,
their endpoint vanishing at `0` and/or `1`, the small-`s` explicit
forms, and the natural-degree bounds. The polynomial-exactness clauses
(`2s − 2`, `2s − 3`), the homotopy-based weight-positivity and
abscissae-confinement arguments, and the construction of the
associated `RKTableau` families (Radau IA/IIA, Lobatto IIIA/IIIB/IIIC)
are deferred to later cycles (cycles 318+).
-/

namespace OpenMath.Chapter3.Section344

open OpenMath.Chapter3.Section342
open Polynomial

/-! ## Deliverable A — Polynomial family definitions

The three Radau/Lobatto quadrature polynomials are defined as the
literal sums/differences of consecutive Butcher shifted Legendre
polynomials, matching Butcher §344 p. 244. We use `ℕ` truncated
subtraction in `s - 1` and `s - 2`; endpoint and degree theorems below
carry `0 < s` (Radau) or `2 ≤ s` (Lobatto) hypotheses to rule out
degenerate cases. -/

/-- **Butcher §344 — Radau I polynomial** `P_s^* + P_{s-1}^*`.
The roots in `[0, 1]` are the Radau I quadrature abscissae. The
polynomial has `natDegree = s` and `0` as a root for `s ≥ 1`.

At `s = 1`: `butcherRadauI 1 = P_1^* + P_0^* = (2X - 1) + 1 = 2X`.
The single root is `0`, matching Radau I with one stage at `c_1 = 0`. -/
noncomputable def butcherRadauI (s : ℕ) : Polynomial ℝ :=
  butcherShiftedLegendre s + butcherShiftedLegendre (s - 1)

/-- **Butcher §344 — Radau II polynomial** `P_s^* - P_{s-1}^*`.
The roots in `[0, 1]` are the Radau II quadrature abscissae. The
polynomial has `natDegree = s` and `1` as a root for `s ≥ 1`.

At `s = 1`: `butcherRadauII 1 = P_1^* - P_0^* = (2X - 1) - 1 = 2X - 2`.
The single root is `1`, matching Radau II with one stage at `c_1 = 1`. -/
noncomputable def butcherRadauII (s : ℕ) : Polynomial ℝ :=
  butcherShiftedLegendre s - butcherShiftedLegendre (s - 1)

/-- **Butcher §344 — Lobatto polynomial** `P_s^* - P_{s-2}^*`.
The roots in `[0, 1]` are the Lobatto quadrature abscissae. The
polynomial has `natDegree = s` (for `s ≥ 2`) and both `0` and `1` as
roots.

At `s = 2`: `butcherLobatto 2 = P_2^* - P_0^* = (6X^2 - 6X + 1) - 1
= 6X^2 - 6X = 6X(X - 1)`. The two roots are `0` and `1`, matching
Lobatto with two stages at `c_1 = 0`, `c_2 = 1`. -/
noncomputable def butcherLobatto (s : ℕ) : Polynomial ℝ :=
  butcherShiftedLegendre s - butcherShiftedLegendre (s - 2)

/-! ## Deliverable B — Endpoint vanishing

The four endpoint theorems below follow Butcher's argument on p. 244:

* `(P_s^* + P_{s-1}^*)(0) = 0` (Radau I) from `P_n^*(0) = (-1)^n` and
  the parity collapse `(-1)^s + (-1)^(s-1) = 0` for `s ≥ 1`.
* `(P_s^* - P_{s-1}^*)(1) = 0` (Radau II) from `P_n^*(1) = 1`
  (342b) — the two values cancel exactly.
* `(P_s^* - P_{s-2}^*)(0) = 0` (Lobatto) from `P_n^*(0) = (-1)^n` and
  the parity collapse `(-1)^s - (-1)^(s-2) = 0` for `s ≥ 2`.
* `(P_s^* - P_{s-2}^*)(1) = 0` (Lobatto) from `P_n^*(1) = 1` (342b). -/

/-- **Butcher §344 (endpoint at 0, Radau I)** —
`(P_s^* + P_{s-1}^*)(0) = 0` for `s ≥ 1`.

Proof: evaluate via `butcherShiftedLegendre_eval_zero`, obtaining
`(-1)^s + (-1)^(s-1)`. Write `s = k + 1`; then `s - 1 = k` and the sum
becomes `(-1)^(k+1) + (-1)^k = -((-1)^k) + (-1)^k = 0`. -/
theorem butcherRadauI_eval_zero (s : ℕ) (hs : 0 < s) :
    (butcherRadauI s).eval 0 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hs)
  unfold butcherRadauI
  rw [Polynomial.eval_add, butcherShiftedLegendre_eval_zero,
      butcherShiftedLegendre_eval_zero]
  -- Goal: (-1)^(k+1) + (-1)^((k+1)-1) = 0
  rw [show (k + 1 - 1 : ℕ) = k from rfl, pow_succ]
  ring

/-- **Butcher §344 (endpoint at 1, Radau II)** —
`(P_s^* - P_{s-1}^*)(1) = 0`.

Proof: evaluate via `butcherShiftedLegendre_eval_one` (which gives `1`
for every `n`); the difference is `1 - 1 = 0`. The textbook's
`s ≥ 1` hypothesis is required only for `c_s = 1` to refer to the
`s`-th abscissa of the Radau II quadrature formula; the pure
polynomial fact `(P_s^* - P_{s-1}^*)(1) = 0` holds for all `s` (with
`s = 0` giving the trivial `P_0^* - P_0^* = 0`). -/
theorem butcherRadauII_eval_one (s : ℕ) :
    (butcherRadauII s).eval 1 = 0 := by
  unfold butcherRadauII
  rw [Polynomial.eval_sub, butcherShiftedLegendre_eval_one,
      butcherShiftedLegendre_eval_one]
  ring

/-- **Butcher §344 (endpoint at 0, Lobatto)** —
`(P_s^* - P_{s-2}^*)(0) = 0` for `s ≥ 2`.

Proof: evaluate via `butcherShiftedLegendre_eval_zero`, obtaining
`(-1)^s - (-1)^(s-2)`. Write `s = k + 2`; then `s - 2 = k` and the
difference becomes `(-1)^(k+2) - (-1)^k = ((-1)^2) · (-1)^k - (-1)^k
= (-1)^k - (-1)^k = 0`. -/
theorem butcherLobatto_eval_zero (s : ℕ) (hs : 2 ≤ s) :
    (butcherLobatto s).eval 0 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  -- now s = 2 + k
  unfold butcherLobatto
  rw [Polynomial.eval_sub, butcherShiftedLegendre_eval_zero,
      butcherShiftedLegendre_eval_zero]
  -- Goal: (-1)^(2+k) - (-1)^((2+k)-2) = 0
  rw [show (2 + k - 2 : ℕ) = k from by omega, pow_add]
  ring

/-- **Butcher §344 (endpoint at 1, Lobatto)** —
`(P_s^* - P_{s-2}^*)(1) = 0`.

Proof: evaluate via `butcherShiftedLegendre_eval_one` (which gives `1`
for every `n`); the difference is `1 - 1 = 0`. The textbook's
`s ≥ 2` hypothesis is required only for `c_s = 1` to refer to the
`s`-th abscissa of the Lobatto quadrature formula; the pure
polynomial fact `(P_s^* - P_{s-2}^*)(1) = 0` holds for all `s`. -/
theorem butcherLobatto_eval_one (s : ℕ) :
    (butcherLobatto s).eval 1 = 0 := by
  unfold butcherLobatto
  rw [Polynomial.eval_sub, butcherShiftedLegendre_eval_one,
      butcherShiftedLegendre_eval_one]
  ring

/-! ## Deliverable C — Small-`s` explicit forms

Concrete witnesses at `s ∈ {1, 2}` (Radau) and `s ∈ {2, 3}` (Lobatto)
expand the three polynomial families using the cycle 273+ shifted
Legendre closed forms. Each closes by `unfold` + `rw` + `ring`. -/

/-- **Butcher §344 small-`s` — Radau I at `s = 1`**:
`butcherRadauI 1 = P_1^* + P_0^* = (2X - 1) + 1 = 2X`. -/
theorem butcherRadauI_one :
    butcherRadauI 1 = Polynomial.C 2 * Polynomial.X := by
  unfold butcherRadauI
  rw [show (1 - 1 : ℕ) = 0 from rfl, butcherShiftedLegendre_one,
      butcherShiftedLegendre_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
             Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- **Butcher §344 small-`s` — Radau I at `s = 2`**:
`butcherRadauI 2 = P_2^* + P_1^* = (6X^2 - 6X + 1) + (2X - 1)
= 6X^2 - 4X`. -/
theorem butcherRadauI_two :
    butcherRadauI 2 =
      Polynomial.C 6 * Polynomial.X ^ 2 - Polynomial.C 4 * Polynomial.X := by
  unfold butcherRadauI
  rw [show (2 - 1 : ℕ) = 1 from rfl, butcherShiftedLegendre_two,
      butcherShiftedLegendre_one]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
             Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- **Butcher §344 small-`s` — Radau II at `s = 1`**:
`butcherRadauII 1 = P_1^* - P_0^* = (2X - 1) - 1 = 2X - 2`. -/
theorem butcherRadauII_one :
    butcherRadauII 1 = Polynomial.C 2 * Polynomial.X - Polynomial.C 2 := by
  unfold butcherRadauII
  rw [show (1 - 1 : ℕ) = 0 from rfl, butcherShiftedLegendre_one,
      butcherShiftedLegendre_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_sub, Polynomial.eval_mul,
             Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- **Butcher §344 small-`s` — Radau II at `s = 2`**:
`butcherRadauII 2 = P_2^* - P_1^* = (6X^2 - 6X + 1) - (2X - 1)
= 6X^2 - 8X + 2`. -/
theorem butcherRadauII_two :
    butcherRadauII 2 =
      Polynomial.C 6 * Polynomial.X ^ 2 - Polynomial.C 8 * Polynomial.X
        + Polynomial.C 2 := by
  unfold butcherRadauII
  rw [show (2 - 1 : ℕ) = 1 from rfl, butcherShiftedLegendre_two,
      butcherShiftedLegendre_one]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
             Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- **Butcher §344 small-`s` — Lobatto at `s = 2`**:
`butcherLobatto 2 = P_2^* - P_0^* = (6X^2 - 6X + 1) - 1
= 6X^2 - 6X = 6X(X - 1)`. -/
theorem butcherLobatto_two :
    butcherLobatto 2 =
      Polynomial.C 6 * Polynomial.X ^ 2 - Polynomial.C 6 * Polynomial.X := by
  unfold butcherLobatto
  rw [show (2 - 2 : ℕ) = 0 from rfl, butcherShiftedLegendre_two,
      butcherShiftedLegendre_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
             Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- **Butcher §344 small-`s` — Lobatto at `s = 3`**:
`butcherLobatto 3 = P_3^* - P_1^* = (20X^3 - 30X^2 + 12X - 1)
- (2X - 1) = 20X^3 - 30X^2 + 10X`. -/
theorem butcherLobatto_three :
    butcherLobatto 3 =
      Polynomial.C 20 * Polynomial.X ^ 3 - Polynomial.C 30 * Polynomial.X ^ 2
        + Polynomial.C 10 * Polynomial.X := by
  unfold butcherLobatto
  rw [show (3 - 2 : ℕ) = 1 from rfl, butcherShiftedLegendre_three,
      butcherShiftedLegendre_one]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
             Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-! ### Non-vacuity witnesses

These confirm the endpoint theorems fire on the small-`s` explicit
forms. Each closes by `rw` + `simp`. -/

example : (butcherRadauI 1).eval 0 = 0 := by
  rw [butcherRadauI_one]; simp

example : (butcherRadauII 1).eval 1 = 0 := by
  rw [butcherRadauII_one]; simp

example : (butcherLobatto 2).eval 0 = 0 := by
  rw [butcherLobatto_two]; simp

example : (butcherLobatto 2).eval 1 = 0 := by
  rw [butcherLobatto_two]; simp

/-! ## Deliverable D — Degree bounds

Each Radau/Lobatto polynomial inherits its `natDegree` from the
leading shifted Legendre summand `P_s^*` (cycle 273
`butcherShiftedLegendre_natDegree`). The lower-index summand has
strictly smaller degree, so
`Polynomial.natDegree_add_eq_left_of_natDegree_lt` (or its `sub`
variant) closes each goal. -/

/-- **Butcher §344 — Radau I degree**: `natDegree (P_s^* + P_{s-1}^*) = s`
for `s ≥ 1`. The leading summand `P_s^*` has degree `s`; the trailing
`P_{s-1}^*` has degree `s - 1 < s`. -/
theorem butcherRadauI_natDegree (s : ℕ) (hs : 0 < s) :
    (butcherRadauI s).natDegree = s := by
  unfold butcherRadauI
  have h_lt : (butcherShiftedLegendre (s - 1)).natDegree
      < (butcherShiftedLegendre s).natDegree := by
    rw [butcherShiftedLegendre_natDegree, butcherShiftedLegendre_natDegree]
    omega
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt h_lt,
      butcherShiftedLegendre_natDegree]

/-- **Butcher §344 — Radau II degree**: `natDegree (P_s^* - P_{s-1}^*) = s`
for `s ≥ 1`. The leading summand `P_s^*` has degree `s`; the trailing
`P_{s-1}^*` has degree `s - 1 < s`. -/
theorem butcherRadauII_natDegree (s : ℕ) (hs : 0 < s) :
    (butcherRadauII s).natDegree = s := by
  unfold butcherRadauII
  have h_lt : (butcherShiftedLegendre (s - 1)).natDegree
      < (butcherShiftedLegendre s).natDegree := by
    rw [butcherShiftedLegendre_natDegree, butcherShiftedLegendre_natDegree]
    omega
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt h_lt,
      butcherShiftedLegendre_natDegree]

/-- **Butcher §344 — Lobatto degree**: `natDegree (P_s^* - P_{s-2}^*) = s`
for `s ≥ 2`. The leading summand `P_s^*` has degree `s`; the trailing
`P_{s-2}^*` has degree `s - 2 < s`. -/
theorem butcherLobatto_natDegree (s : ℕ) (hs : 2 ≤ s) :
    (butcherLobatto s).natDegree = s := by
  unfold butcherLobatto
  have h_lt : (butcherShiftedLegendre (s - 2)).natDegree
      < (butcherShiftedLegendre s).natDegree := by
    rw [butcherShiftedLegendre_natDegree, butcherShiftedLegendre_natDegree]
    omega
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt h_lt,
      butcherShiftedLegendre_natDegree]

end OpenMath.Chapter3.Section344
