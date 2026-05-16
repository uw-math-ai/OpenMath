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

/-! ## Deliverable E — Orthogonality to lower-degree polynomials (Phase B.1)

Each Radau/Lobatto polynomial inherits orthogonality from cycle 292's
`butcherShiftedLegendre_orthogonal_to_lower_degree`: a Radau/Lobatto
polynomial is a sum or difference of two shifted Legendre polynomials,
so orthogonality to a test polynomial `q` of degree `< s - 1` (Radau)
or `< s - 2` (Lobatto) follows from linearity of the integral and
orthogonality of each summand.

These statements are the input to the Phase B.2 polynomial-exactness
theorem (Butcher p. 244): the textbook proof divides `φ = Q · F + R`
where `F` is the Radau/Lobatto polynomial, and the `Q · F` summand
vanishes against the quadrature precisely because `Q.natDegree < s - 1`
(Radau) or `Q.natDegree < s - 2` (Lobatto). -/

private lemma intervalIntegrable_polyMul (p q : Polynomial ℝ) :
    IntervalIntegrable (fun x : ℝ => p.eval x * q.eval x)
      MeasureTheory.volume 0 1 :=
  (p.continuous.mul q.continuous).intervalIntegrable _ _

/-- **Butcher §344 — Radau I orthogonality** —
For `s ≥ 1` and `q` a polynomial with `q.natDegree < s - 1`,
`∫₀¹ (P_s^* + P_{s-1}^*)(x) · q(x) dx = 0`.

This is the orthogonality property that powers Butcher's polynomial-
exactness argument (p. 244) for Radau I quadrature: any polynomial
`φ` of degree `≤ 2s − 2` divides as `Q · (P_s^* + P_{s-1}^*) + R`
with `Q.natDegree < s − 1`, and the `Q · (P_s^* + P_{s-1}^*)` summand
integrates to zero.

Proof: unfold `butcherRadauI`, distribute via `eval_add` + `add_mul`,
split via `intervalIntegral.integral_add`, and apply cycle 292's
`butcherShiftedLegendre_orthogonal_to_lower_degree` at `m := s` (using
`s - 1 ≤ s`) and `m := s - 1` (using the hypothesis directly). -/
theorem butcherRadauI_orthogonal_to_lower_degree (s : ℕ) (hs : 1 ≤ s)
    (q : Polynomial ℝ) (hq : q.natDegree < s - 1) :
    ∫ x in (0 : ℝ)..1, (butcherRadauI s).eval x * q.eval x = 0 := by
  unfold butcherRadauI
  have h_int1 := intervalIntegrable_polyMul (butcherShiftedLegendre s) q
  have h_int2 := intervalIntegrable_polyMul (butcherShiftedLegendre (s - 1)) q
  have h_eq : ∀ x : ℝ,
      (butcherShiftedLegendre s + butcherShiftedLegendre (s - 1)).eval x * q.eval x =
      (butcherShiftedLegendre s).eval x * q.eval x +
      (butcherShiftedLegendre (s - 1)).eval x * q.eval x := by
    intro x
    simp only [Polynomial.eval_add]
    ring
  simp_rw [h_eq]
  rw [intervalIntegral.integral_add h_int1 h_int2]
  have h1 : q.natDegree < s := by omega
  rw [butcherShiftedLegendre_orthogonal_to_lower_degree s q h1,
      butcherShiftedLegendre_orthogonal_to_lower_degree (s - 1) q hq]
  ring

/-- **Butcher §344 — Radau II orthogonality** —
For `s ≥ 1` and `q` a polynomial with `q.natDegree < s - 1`,
`∫₀¹ (P_s^* - P_{s-1}^*)(x) · q(x) dx = 0`.

This is the orthogonality property powering Butcher's polynomial-
exactness argument (p. 244) for Radau II quadrature, the dual of
Radau I.

Proof: same recipe as `butcherRadauI_orthogonal_to_lower_degree`,
with `add` replaced by `sub` (using `intervalIntegral.integral_sub`). -/
theorem butcherRadauII_orthogonal_to_lower_degree (s : ℕ) (hs : 1 ≤ s)
    (q : Polynomial ℝ) (hq : q.natDegree < s - 1) :
    ∫ x in (0 : ℝ)..1, (butcherRadauII s).eval x * q.eval x = 0 := by
  unfold butcherRadauII
  have h_int1 := intervalIntegrable_polyMul (butcherShiftedLegendre s) q
  have h_int2 := intervalIntegrable_polyMul (butcherShiftedLegendre (s - 1)) q
  have h_eq : ∀ x : ℝ,
      (butcherShiftedLegendre s - butcherShiftedLegendre (s - 1)).eval x * q.eval x =
      (butcherShiftedLegendre s).eval x * q.eval x -
      (butcherShiftedLegendre (s - 1)).eval x * q.eval x := by
    intro x
    simp only [Polynomial.eval_sub]
    ring
  simp_rw [h_eq]
  rw [intervalIntegral.integral_sub h_int1 h_int2]
  have h1 : q.natDegree < s := by omega
  rw [butcherShiftedLegendre_orthogonal_to_lower_degree s q h1,
      butcherShiftedLegendre_orthogonal_to_lower_degree (s - 1) q hq]
  ring

/-- **Butcher §344 — Lobatto orthogonality** —
For `s ≥ 2` and `q` a polynomial with `q.natDegree < s - 2`,
`∫₀¹ (P_s^* - P_{s-2}^*)(x) · q(x) dx = 0`.

This is the orthogonality property powering Butcher's polynomial-
exactness argument (p. 244) for Lobatto quadrature: any polynomial
`φ` of degree `≤ 2s − 3` divides as `Q · (P_s^* - P_{s-2}^*) + R`
with `Q.natDegree < s − 2`, and the `Q · (P_s^* - P_{s-2}^*)` summand
integrates to zero.

Proof: same recipe as `butcherRadauII_orthogonal_to_lower_degree`,
with the lower-index shift bumped from `s - 1` to `s - 2`, applying
cycle 292's orthogonality at `m := s` and `m := s - 2`. -/
theorem butcherLobatto_orthogonal_to_lower_degree (s : ℕ) (hs : 2 ≤ s)
    (q : Polynomial ℝ) (hq : q.natDegree < s - 2) :
    ∫ x in (0 : ℝ)..1, (butcherLobatto s).eval x * q.eval x = 0 := by
  unfold butcherLobatto
  have h_int1 := intervalIntegrable_polyMul (butcherShiftedLegendre s) q
  have h_int2 := intervalIntegrable_polyMul (butcherShiftedLegendre (s - 2)) q
  have h_eq : ∀ x : ℝ,
      (butcherShiftedLegendre s - butcherShiftedLegendre (s - 2)).eval x * q.eval x =
      (butcherShiftedLegendre s).eval x * q.eval x -
      (butcherShiftedLegendre (s - 2)).eval x * q.eval x := by
    intro x
    simp only [Polynomial.eval_sub]
    ring
  simp_rw [h_eq]
  rw [intervalIntegral.integral_sub h_int1 h_int2]
  have h1 : q.natDegree < s := by omega
  rw [butcherShiftedLegendre_orthogonal_to_lower_degree s q h1,
      butcherShiftedLegendre_orthogonal_to_lower_degree (s - 2) q hq]
  ring

/-! ### Non-vacuity witnesses for the orthogonality lemmas

Each lemma is fired against a constant test polynomial `q = C 1`,
which has `natDegree = 0`. The hypothesis `0 < s - 1` (Radau) or
`0 < s - 2` (Lobatto) is satisfied at `s = 2` (Radau) and `s = 3`
(Lobatto). -/

example :
    ∫ x in (0 : ℝ)..1, (butcherRadauI 2).eval x * (Polynomial.C (1 : ℝ)).eval x = 0 :=
  butcherRadauI_orthogonal_to_lower_degree 2 (by norm_num) (Polynomial.C 1)
    (by simp)

example :
    ∫ x in (0 : ℝ)..1, (butcherRadauII 2).eval x * (Polynomial.C (1 : ℝ)).eval x = 0 :=
  butcherRadauII_orthogonal_to_lower_degree 2 (by norm_num) (Polynomial.C 1)
    (by simp)

example :
    ∫ x in (0 : ℝ)..1, (butcherLobatto 3).eval x * (Polynomial.C (1 : ℝ)).eval x = 0 :=
  butcherLobatto_orthogonal_to_lower_degree 3 (by norm_num) (Polynomial.C 1)
    (by simp)

/-! ## Deliverable C.1 — Small-`s` explicit roots

Each small-`s` Radau/Lobatto polynomial from Deliverable C factors
cleanly with rational roots in `[0, 1]`. These named root theorems
are the abscissae-side anchor for downstream RKTableau construction
(planned for cycle 320+) and the small-`s` `R.natDegree < s`
Lagrange-interpolation collapse needed for the eventual
polynomial-exactness theorem (Phase B.2).

| Polynomial         | Roots          |
|--------------------|----------------|
| `butcherRadauI 1`  | `0`            |
| `butcherRadauI 2`  | `0, 2/3`       |
| `butcherRadauII 1` | `1`            |
| `butcherRadauII 2` | `1/3, 1`       |
| `butcherLobatto 2` | `0, 1`         |
| `butcherLobatto 3` | `0, 1/2, 1`    |
-/

/-- **Butcher §344 small-`s` roots — Radau I at `s = 1`**:
the single root of `butcherRadauI 1 = 2X` is the left endpoint
`x = 0`. This is the named-theorem version of the cycle 318
`example` immediately above, packaged for downstream abscissae-table
use. -/
theorem butcherRadauI_one_root :
    (butcherRadauI 1).eval (0 : ℝ) = 0 := by
  rw [butcherRadauI_one]
  simp

/-- **Butcher §344 small-`s` roots — Radau I at `s = 2`**:
the two roots of `butcherRadauI 2 = 6X² − 4X = 2X(3X − 2)` are
`x = 0` (left endpoint) and `x = 2/3` (interior). The endpoint
matches Radau I's `c_1 = 0` constraint. -/
theorem butcherRadauI_two_roots :
    (butcherRadauI 2).eval (0 : ℝ) = 0 ∧
    (butcherRadauI 2).eval (2/3 : ℝ) = 0 ∧
    (0 : ℝ) ≠ 2/3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [butcherRadauI_two]
    simp
  · rw [butcherRadauI_two]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
               Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  · norm_num

/-- **Butcher §344 small-`s` roots — Radau II at `s = 1`**:
the single root of `butcherRadauII 1 = 2X − 2` is the right endpoint
`x = 1`. This matches Radau II's `c_s = 1` constraint with one
stage. -/
theorem butcherRadauII_one_root :
    (butcherRadauII 1).eval (1 : ℝ) = 0 := by
  rw [butcherRadauII_one]
  simp

/-- **Butcher §344 small-`s` roots — Radau II at `s = 2`**:
the two roots of `butcherRadauII 2 = 6X² − 8X + 2 = 2(3X − 1)(X − 1)`
are `x = 1/3` (interior) and `x = 1` (right endpoint). The endpoint
matches Radau II's `c_s = 1` constraint. -/
theorem butcherRadauII_two_roots :
    (butcherRadauII 2).eval (1/3 : ℝ) = 0 ∧
    (butcherRadauII 2).eval (1 : ℝ) = 0 ∧
    (1/3 : ℝ) ≠ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [butcherRadauII_two]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
               Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  · rw [butcherRadauII_two]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
               Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  · norm_num

/-- **Butcher §344 small-`s` roots — Lobatto at `s = 2`**:
the two roots of `butcherLobatto 2 = 6X² − 6X = 6X(X − 1)` are both
endpoints `x = 0` and `x = 1`. Matches Lobatto's
`c_1 = 0`, `c_s = 1` constraints with two stages (no interior
abscissae). -/
theorem butcherLobatto_two_roots :
    (butcherLobatto 2).eval (0 : ℝ) = 0 ∧
    (butcherLobatto 2).eval (1 : ℝ) = 0 ∧
    (0 : ℝ) ≠ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [butcherLobatto_two]
    simp
  · rw [butcherLobatto_two]
    simp
  · norm_num

/-- **Butcher §344 small-`s` roots — Lobatto at `s = 3`**:
the three roots of `butcherLobatto 3 = 20X³ − 30X² + 10X
= 10X(2X − 1)(X − 1)` are `x = 0` (left endpoint), `x = 1/2`
(interior), and `x = 1` (right endpoint). The endpoints match
Lobatto's `c_1 = 0`, `c_s = 1` constraints; the midpoint `1/2`
is the unique interior abscissa. -/
theorem butcherLobatto_three_roots :
    (butcherLobatto 3).eval (0 : ℝ) = 0 ∧
    (butcherLobatto 3).eval (1/2 : ℝ) = 0 ∧
    (butcherLobatto 3).eval (1 : ℝ) = 0 ∧
    (0 : ℝ) ≠ 1/2 ∧ (0 : ℝ) ≠ 1 ∧ (1/2 : ℝ) ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [butcherLobatto_three]
    simp
  · rw [butcherLobatto_three]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
               Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  · rw [butcherLobatto_three]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
               Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  · norm_num
  · norm_num
  · norm_num

/-! ## Deliverable C.2 — Small-`s` abscissae functions

Package cycle 319's explicit-root theorems into named abscissae
arrays `Fin s → ℝ`, mirroring cycle 302's
`butcherShiftedLegendre_zeros`. Each entry of the array is the
root of the corresponding §344 polynomial at the corresponding
position in Butcher's strictly increasing enumeration
`c_1 < c_2 < … < c_s`.

For each abscissae function we ship three properties:

* `_isRoot`: every entry is a root of the §344 polynomial,
* `_strictMono` (multi-stage only): the abscissae are strictly
  increasing,
* `_mem_Icc`: every entry lies in `[0, 1]`.

These are the abscissae-side prerequisites for downstream
small-`s` Lagrange-interpolation quadrature weights (cycle 321)
and small-`s` `RKTableau` constructions (Radau IA, IIA, Lobatto IIIB).

| Function                        | Body                              |
|---------------------------------|-----------------------------------|
| `butcherRadauI_zeros_one`       | `(0)`                             |
| `butcherRadauI_zeros_two`       | `(0, 2/3)`                        |
| `butcherRadauII_zeros_one`      | `(1)`                             |
| `butcherRadauII_zeros_two`      | `(1/3, 1)`                        |
| `butcherLobatto_zeros_two`      | `(0, 1)`                          |
| `butcherLobatto_zeros_three`    | `(0, 1/2, 1)`                     |
-/

/-- **Butcher §344 abscissae — Radau I, `s = 1`**: the single Radau I
abscissa at one stage is `c_1 = 0`, the root of `butcherRadauI 1`
from `butcherRadauI_one_root`. -/
noncomputable def butcherRadauI_zeros_one : Fin 1 → ℝ
  | ⟨0, _⟩ => 0

/-- **Butcher §344 abscissae — Radau I, `s = 2`**: the two Radau I
abscissae at two stages are `c_1 = 0` and `c_2 = 2/3`, the roots of
`butcherRadauI 2` from `butcherRadauI_two_roots`. -/
noncomputable def butcherRadauI_zeros_two : Fin 2 → ℝ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2 / 3

/-- **Butcher §344 abscissae — Radau II, `s = 1`**: the single Radau II
abscissa at one stage is `c_1 = 1`, the root of `butcherRadauII 1`
from `butcherRadauII_one_root`. -/
noncomputable def butcherRadauII_zeros_one : Fin 1 → ℝ
  | ⟨0, _⟩ => 1

/-- **Butcher §344 abscissae — Radau II, `s = 2`**: the two Radau II
abscissae at two stages are `c_1 = 1/3` and `c_2 = 1`, the roots of
`butcherRadauII 2` from `butcherRadauII_two_roots`. -/
noncomputable def butcherRadauII_zeros_two : Fin 2 → ℝ
  | ⟨0, _⟩ => 1 / 3
  | ⟨1, _⟩ => 1

/-- **Butcher §344 abscissae — Lobatto, `s = 2`**: the two Lobatto
abscissae at two stages are `c_1 = 0` and `c_2 = 1`, the roots of
`butcherLobatto 2` from `butcherLobatto_two_roots`. -/
noncomputable def butcherLobatto_zeros_two : Fin 2 → ℝ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1

/-- **Butcher §344 abscissae — Lobatto, `s = 3`**: the three Lobatto
abscissae at three stages are `c_1 = 0`, `c_2 = 1/2`, `c_3 = 1`,
the roots of `butcherLobatto 3` from `butcherLobatto_three_roots`. -/
noncomputable def butcherLobatto_zeros_three : Fin 3 → ℝ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1 / 2
  | ⟨2, _⟩ => 1

/-! ### `_isRoot` theorems — each abscissa is a root of the §344 polynomial. -/

/-- Every entry of `butcherRadauI_zeros_one` is a root of `butcherRadauI 1`. -/
theorem butcherRadauI_zeros_one_isRoot (i : Fin 1) :
    (butcherRadauI 1).eval (butcherRadauI_zeros_one i) = 0 := by
  fin_cases i
  exact butcherRadauI_one_root

/-- Every entry of `butcherRadauI_zeros_two` is a root of `butcherRadauI 2`. -/
theorem butcherRadauI_zeros_two_isRoot (i : Fin 2) :
    (butcherRadauI 2).eval (butcherRadauI_zeros_two i) = 0 := by
  fin_cases i
  · exact butcherRadauI_two_roots.1
  · exact butcherRadauI_two_roots.2.1

/-- Every entry of `butcherRadauII_zeros_one` is a root of `butcherRadauII 1`. -/
theorem butcherRadauII_zeros_one_isRoot (i : Fin 1) :
    (butcherRadauII 1).eval (butcherRadauII_zeros_one i) = 0 := by
  fin_cases i
  exact butcherRadauII_one_root

/-- Every entry of `butcherRadauII_zeros_two` is a root of `butcherRadauII 2`. -/
theorem butcherRadauII_zeros_two_isRoot (i : Fin 2) :
    (butcherRadauII 2).eval (butcherRadauII_zeros_two i) = 0 := by
  fin_cases i
  · exact butcherRadauII_two_roots.1
  · exact butcherRadauII_two_roots.2.1

/-- Every entry of `butcherLobatto_zeros_two` is a root of `butcherLobatto 2`. -/
theorem butcherLobatto_zeros_two_isRoot (i : Fin 2) :
    (butcherLobatto 2).eval (butcherLobatto_zeros_two i) = 0 := by
  fin_cases i
  · exact butcherLobatto_two_roots.1
  · exact butcherLobatto_two_roots.2.1

/-- Every entry of `butcherLobatto_zeros_three` is a root of `butcherLobatto 3`. -/
theorem butcherLobatto_zeros_three_isRoot (i : Fin 3) :
    (butcherLobatto 3).eval (butcherLobatto_zeros_three i) = 0 := by
  fin_cases i
  · exact butcherLobatto_three_roots.1
  · exact butcherLobatto_three_roots.2.1
  · exact butcherLobatto_three_roots.2.2.1

/-! ### `_strictMono` theorems — abscissae are strictly increasing. -/

/-- The two-stage Radau I abscissae `(0, 2/3)` are strictly increasing. -/
theorem butcherRadauI_zeros_two_strictMono :
    StrictMono butcherRadauI_zeros_two := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [butcherRadauI_zeros_two]

/-- The two-stage Radau II abscissae `(1/3, 1)` are strictly increasing. -/
theorem butcherRadauII_zeros_two_strictMono :
    StrictMono butcherRadauII_zeros_two := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [butcherRadauII_zeros_two]
  norm_num

/-- The two-stage Lobatto abscissae `(0, 1)` are strictly increasing. -/
theorem butcherLobatto_zeros_two_strictMono :
    StrictMono butcherLobatto_zeros_two := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [butcherLobatto_zeros_two]

/-- The three-stage Lobatto abscissae `(0, 1/2, 1)` are strictly increasing. -/
theorem butcherLobatto_zeros_three_strictMono :
    StrictMono butcherLobatto_zeros_three := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [butcherLobatto_zeros_three]
  norm_num

/-! ### `_mem_Icc` theorems — every abscissa lies in `[0, 1]`. -/

/-- Every entry of `butcherRadauI_zeros_one` lies in `[0, 1]`. -/
theorem butcherRadauI_zeros_one_mem_Icc (i : Fin 1) :
    butcherRadauI_zeros_one i ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases i
  simp [butcherRadauI_zeros_one, Set.mem_Icc]

/-- Every entry of `butcherRadauI_zeros_two` lies in `[0, 1]`. -/
theorem butcherRadauI_zeros_two_mem_Icc (i : Fin 2) :
    butcherRadauI_zeros_two i ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases i <;> simp [butcherRadauI_zeros_two, Set.mem_Icc]
  norm_num

/-- Every entry of `butcherRadauII_zeros_one` lies in `[0, 1]`. -/
theorem butcherRadauII_zeros_one_mem_Icc (i : Fin 1) :
    butcherRadauII_zeros_one i ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases i
  simp [butcherRadauII_zeros_one, Set.mem_Icc]

/-- Every entry of `butcherRadauII_zeros_two` lies in `[0, 1]`. -/
theorem butcherRadauII_zeros_two_mem_Icc (i : Fin 2) :
    butcherRadauII_zeros_two i ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases i <;> simp [butcherRadauII_zeros_two, Set.mem_Icc]
  norm_num

/-- Every entry of `butcherLobatto_zeros_two` lies in `[0, 1]`. -/
theorem butcherLobatto_zeros_two_mem_Icc (i : Fin 2) :
    butcherLobatto_zeros_two i ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases i <;> simp [butcherLobatto_zeros_two, Set.mem_Icc]

/-- Every entry of `butcherLobatto_zeros_three` lies in `[0, 1]`. -/
theorem butcherLobatto_zeros_three_mem_Icc (i : Fin 3) :
    butcherLobatto_zeros_three i ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases i <;> simp [butcherLobatto_zeros_three, Set.mem_Icc]
  norm_num

end OpenMath.Chapter3.Section344
