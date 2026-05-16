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

/-! ### Phase D.1 — Lagrange quadrature weights

For each cycle-320 abscissae function `butcher<Family>_zeros_<s>`, the
quadrature weights `b_j := ∫₀¹ L_j(x) dx` are the integrals of the
Lagrange basis polynomials interpolating `δ_jk` at the abscissae.
Mirrors cycle 303's `butcherShiftedLegendre_quadratureWeights`
construction at the §342 zeros. The six closed-form `_apply` theorems
verify the textbook values:

* Radau I  `s=1` → `(1)`              ; `s=2` → `(1/4, 3/4)`
* Radau II `s=1` → `(1)`              ; `s=2` → `(3/4, 1/4)`
* Lobatto  `s=2` → `(1/2, 1/2)` (trapezoidal rule)
* Lobatto  `s=3` → `(1/6, 2/3, 1/6)` (Simpson's rule)
-/

/-- **Butcher §344 — Radau I `s = 1` quadrature weight.**
`b_j := ∫₀¹ L_j(x) dx` at the single Radau I abscissa `c_1 = 0`. The
Lagrange basis on a singleton is identically `1` (Mathlib's
`Lagrange.basis_singleton`), so the unique entry is `∫₀¹ 1 dx = 1`. -/
noncomputable def butcherRadauI_quadratureWeights_one (j : Fin 1) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    (Lagrange.basis Finset.univ butcherRadauI_zeros_one j).eval x

/-- **Butcher §344 — Radau I `s = 2` quadrature weights.**
`b_j := ∫₀¹ L_j(x) dx` at the Radau I abscissae `(0, 2/3)`. Closed-form
weights `(b_0, b_1) = (1/4, 3/4)` (Butcher Table 344(I) p. 245). -/
noncomputable def butcherRadauI_quadratureWeights_two (j : Fin 2) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    (Lagrange.basis Finset.univ butcherRadauI_zeros_two j).eval x

/-- **Butcher §344 — Radau II `s = 1` quadrature weight.**
`b_j := ∫₀¹ L_j(x) dx` at the single Radau II abscissa `c_1 = 1`. The
Lagrange basis on a singleton is identically `1`, so the unique entry
is `∫₀¹ 1 dx = 1`. -/
noncomputable def butcherRadauII_quadratureWeights_one (j : Fin 1) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    (Lagrange.basis Finset.univ butcherRadauII_zeros_one j).eval x

/-- **Butcher §344 — Radau II `s = 2` quadrature weights.**
`b_j := ∫₀¹ L_j(x) dx` at the Radau II abscissae `(1/3, 1)`. Closed-form
weights `(b_0, b_1) = (3/4, 1/4)` (Butcher Table 344(II) p. 245). -/
noncomputable def butcherRadauII_quadratureWeights_two (j : Fin 2) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    (Lagrange.basis Finset.univ butcherRadauII_zeros_two j).eval x

/-- **Butcher §344 — Lobatto `s = 2` quadrature weights.**
`b_j := ∫₀¹ L_j(x) dx` at the Lobatto abscissae `(0, 1)`. Closed-form
weights `(b_0, b_1) = (1/2, 1/2)` — the trapezoidal rule. -/
noncomputable def butcherLobatto_quadratureWeights_two (j : Fin 2) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    (Lagrange.basis Finset.univ butcherLobatto_zeros_two j).eval x

/-- **Butcher §344 — Lobatto `s = 3` quadrature weights.**
`b_j := ∫₀¹ L_j(x) dx` at the Lobatto abscissae `(0, 1/2, 1)`.
Closed-form weights `(b_0, b_1, b_2) = (1/6, 2/3, 1/6)` — Simpson's
rule. -/
noncomputable def butcherLobatto_quadratureWeights_three (j : Fin 3) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    (Lagrange.basis Finset.univ butcherLobatto_zeros_three j).eval x

/-! #### `_apply` theorems for `s = 1` (singleton Lagrange basis) -/

/-- **Radau I `s = 1` weight at `j = 0`.** Value `1`. The basis on the
singleton `Finset.univ : Finset (Fin 1)` is `1` (`Lagrange.basis_singleton`),
so the integral collapses to `∫₀¹ 1 dx = 1`. -/
theorem butcherRadauI_quadratureWeights_one_apply :
    butcherRadauI_quadratureWeights_one ⟨0, by omega⟩ = 1 := by
  unfold butcherRadauI_quadratureWeights_one
  simp [Lagrange.basis_singleton, Polynomial.eval_one]

/-- **Radau II `s = 1` weight at `j = 0`.** Value `1`. The basis on the
singleton `Finset.univ : Finset (Fin 1)` is `1`, so the integral
collapses to `∫₀¹ 1 dx = 1`. -/
theorem butcherRadauII_quadratureWeights_one_apply :
    butcherRadauII_quadratureWeights_one ⟨0, by omega⟩ = 1 := by
  unfold butcherRadauII_quadratureWeights_one
  simp [Lagrange.basis_singleton, Polynomial.eval_one]

/-! #### `_apply` theorems for `s = 2` (two-node Lagrange basis)

For two-stage methods, the Lagrange basis polynomials are
`L_0(x) = (x − c_1)/(c_0 − c_1)` and `L_1(x) = (x − c_0)/(c_1 − c_0)`.
After computing the concrete pointwise expression, the integrals collapse
to `∫₀¹ 1 dx + (slope) · ∫₀¹ x dx` via `integral_id` and `integral_one`. -/

/-- **Lobatto `s = 2` weight at `j = 0`.** Value `1/2` (trapezoidal
rule). With nodes `(0, 1)`, the basis polynomial `L_0(x) = 1 − x`, so
`b_0 = ∫₀¹ (1 − x) dx = 1 − 1/2 = 1/2`. -/
theorem butcherLobatto_quadratureWeights_two_apply_zero :
    butcherLobatto_quadratureWeights_two ⟨0, by omega⟩ = 1 / 2 := by
  unfold butcherLobatto_quadratureWeights_two
  have h_erase : ((Finset.univ : Finset (Fin 2)).erase ⟨0, by omega⟩)
      = ({⟨1, by omega⟩} : Finset (Fin 2)) := by decide
  have h_eval : ∀ x : ℝ,
      (Lagrange.basis (Finset.univ : Finset (Fin 2)) butcherLobatto_zeros_two
          ⟨0, by omega⟩).eval x = 1 - x := by
    intro x
    rw [Lagrange.basis, h_erase, Finset.prod_singleton, Lagrange.basisDivisor]
    simp [butcherLobatto_zeros_two, Polynomial.eval_sub,
          Polynomial.eval_X]
  simp_rw [h_eval]
  have h_int : ∫ x in (0 : ℝ)..1, ((1 : ℝ) - x) = 1 / 2 := by
    have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
      continuous_id.intervalIntegrable 0 1
    have hx : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
      have hp1 := integral_pow (a := (0 : ℝ)) (b := 1) 1
      simp only [pow_one, Nat.cast_one] at hp1
      rw [hp1]; norm_num
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi_x,
        integral_one, hx]
    norm_num
  exact h_int

/-- **Lobatto `s = 2` weight at `j = 1`.** Value `1/2` (trapezoidal
rule). With nodes `(0, 1)`, the basis polynomial `L_1(x) = x`, so
`b_1 = ∫₀¹ x dx = 1/2`. -/
theorem butcherLobatto_quadratureWeights_two_apply_one :
    butcherLobatto_quadratureWeights_two ⟨1, by omega⟩ = 1 / 2 := by
  unfold butcherLobatto_quadratureWeights_two
  have h_erase : ((Finset.univ : Finset (Fin 2)).erase ⟨1, by omega⟩)
      = ({⟨0, by omega⟩} : Finset (Fin 2)) := by decide
  have h_eval : ∀ x : ℝ,
      (Lagrange.basis (Finset.univ : Finset (Fin 2)) butcherLobatto_zeros_two
          ⟨1, by omega⟩).eval x = x := by
    intro x
    rw [Lagrange.basis, h_erase, Finset.prod_singleton, Lagrange.basisDivisor]
    simp [butcherLobatto_zeros_two, Polynomial.eval_X]
  simp_rw [h_eval]
  have hp1 := integral_pow (a := (0 : ℝ)) (b := 1) 1
  simp only [pow_one, Nat.cast_one] at hp1
  rw [hp1]; norm_num

/-- **Radau I `s = 2` weight at `j = 0`.** Value `1/4`. With nodes
`(0, 2/3)`, the basis polynomial `L_0(x) = 1 − (3/2)x`, so
`b_0 = ∫₀¹ (1 − (3/2)x) dx = 1 − 3/4 = 1/4`
(Butcher Table 344(I) p. 245). -/
theorem butcherRadauI_quadratureWeights_two_apply_zero :
    butcherRadauI_quadratureWeights_two ⟨0, by omega⟩ = 1 / 4 := by
  unfold butcherRadauI_quadratureWeights_two
  have h_erase : ((Finset.univ : Finset (Fin 2)).erase ⟨0, by omega⟩)
      = ({⟨1, by omega⟩} : Finset (Fin 2)) := by decide
  have h_eval : ∀ x : ℝ,
      (Lagrange.basis (Finset.univ : Finset (Fin 2)) butcherRadauI_zeros_two
          ⟨0, by omega⟩).eval x = 1 - (3/2) * x := by
    intro x
    rw [Lagrange.basis, h_erase, Finset.prod_singleton, Lagrange.basisDivisor]
    simp [butcherRadauI_zeros_two, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X]
    ring
  simp_rw [h_eval]
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have hx : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
    have hp1 := integral_pow (a := (0 : ℝ)) (b := 1) 1
    simp only [pow_one, Nat.cast_one] at hp1
    rw [hp1]; norm_num
  rw [intervalIntegral.integral_sub intervalIntegrable_const
        (hi_x.const_mul (3/2)),
      integral_one, intervalIntegral.integral_const_mul, hx]
  norm_num

/-- **Radau I `s = 2` weight at `j = 1`.** Value `3/4`. With nodes
`(0, 2/3)`, the basis polynomial `L_1(x) = (3/2)x`, so
`b_1 = ∫₀¹ (3/2)x dx = 3/4` (Butcher Table 344(I) p. 245). -/
theorem butcherRadauI_quadratureWeights_two_apply_one :
    butcherRadauI_quadratureWeights_two ⟨1, by omega⟩ = 3 / 4 := by
  unfold butcherRadauI_quadratureWeights_two
  have h_erase : ((Finset.univ : Finset (Fin 2)).erase ⟨1, by omega⟩)
      = ({⟨0, by omega⟩} : Finset (Fin 2)) := by decide
  have h_eval : ∀ x : ℝ,
      (Lagrange.basis (Finset.univ : Finset (Fin 2)) butcherRadauI_zeros_two
          ⟨1, by omega⟩).eval x = (3/2) * x := by
    intro x
    rw [Lagrange.basis, h_erase, Finset.prod_singleton, Lagrange.basisDivisor]
    simp [butcherRadauI_zeros_two, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X]
  simp_rw [h_eval]
  have hx : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
    have hp1 := integral_pow (a := (0 : ℝ)) (b := 1) 1
    simp only [pow_one, Nat.cast_one] at hp1
    rw [hp1]; norm_num
  rw [intervalIntegral.integral_const_mul, hx]
  norm_num

/-- **Radau II `s = 2` weight at `j = 0`.** Value `3/4`. With nodes
`(1/3, 1)`, the basis polynomial `L_0(x) = (3/2) − (3/2)x`, so
`b_0 = ∫₀¹ ((3/2) − (3/2)x) dx = 3/2 − 3/4 = 3/4`
(Butcher Table 344(II) p. 245). -/
theorem butcherRadauII_quadratureWeights_two_apply_zero :
    butcherRadauII_quadratureWeights_two ⟨0, by omega⟩ = 3 / 4 := by
  unfold butcherRadauII_quadratureWeights_two
  have h_erase : ((Finset.univ : Finset (Fin 2)).erase ⟨0, by omega⟩)
      = ({⟨1, by omega⟩} : Finset (Fin 2)) := by decide
  have h_eval : ∀ x : ℝ,
      (Lagrange.basis (Finset.univ : Finset (Fin 2)) butcherRadauII_zeros_two
          ⟨0, by omega⟩).eval x = (3/2) - (3/2) * x := by
    intro x
    rw [Lagrange.basis, h_erase, Finset.prod_singleton, Lagrange.basisDivisor]
    simp [butcherRadauII_zeros_two, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X]
    ring
  simp_rw [h_eval]
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have hx : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
    have hp1 := integral_pow (a := (0 : ℝ)) (b := 1) 1
    simp only [pow_one, Nat.cast_one] at hp1
    rw [hp1]; norm_num
  rw [intervalIntegral.integral_sub intervalIntegrable_const
        (hi_x.const_mul (3/2)),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      hx]
  norm_num

/-- **Radau II `s = 2` weight at `j = 1`.** Value `1/4`. With nodes
`(1/3, 1)`, the basis polynomial `L_1(x) = (3/2)x − 1/2`, so
`b_1 = ∫₀¹ ((3/2)x − 1/2) dx = 3/4 − 1/2 = 1/4`
(Butcher Table 344(II) p. 245). -/
theorem butcherRadauII_quadratureWeights_two_apply_one :
    butcherRadauII_quadratureWeights_two ⟨1, by omega⟩ = 1 / 4 := by
  unfold butcherRadauII_quadratureWeights_two
  have h_erase : ((Finset.univ : Finset (Fin 2)).erase ⟨1, by omega⟩)
      = ({⟨0, by omega⟩} : Finset (Fin 2)) := by decide
  have h_eval : ∀ x : ℝ,
      (Lagrange.basis (Finset.univ : Finset (Fin 2)) butcherRadauII_zeros_two
          ⟨1, by omega⟩).eval x = (3/2) * x - (1/2) := by
    intro x
    rw [Lagrange.basis, h_erase, Finset.prod_singleton, Lagrange.basisDivisor]
    simp [butcherRadauII_zeros_two, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X]
    ring
  simp_rw [h_eval]
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have hx : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
    have hp1 := integral_pow (a := (0 : ℝ)) (b := 1) 1
    simp only [pow_one, Nat.cast_one] at hp1
    rw [hp1]; norm_num
  rw [intervalIntegral.integral_sub (hi_x.const_mul (3/2))
        intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      hx]
  norm_num

/-! #### `_apply` theorems for `s = 3` (three-node Lagrange basis)

For three-stage Lobatto, the basis polynomials are quadratic. The
expansion via `Finset.prod_pair` reduces the two-factor product to the
explicit polynomial form, after which integration follows the cycle 274
`_norm_sq_*` template (`integral_pow` for `x²`, `x`, and `integral_one`
for the constant term). -/

/-- **Lobatto `s = 3` weight at `j = 0`.** Value `1/6` (Simpson's rule
endpoint weight). With nodes `(0, 1/2, 1)`, the basis polynomial
`L_0(x) = 2x² − 3x + 1`, so
`b_0 = ∫₀¹ (2x² − 3x + 1) dx = 2/3 − 3/2 + 1 = 1/6`. -/
theorem butcherLobatto_quadratureWeights_three_apply_zero :
    butcherLobatto_quadratureWeights_three ⟨0, by omega⟩ = 1 / 6 := by
  unfold butcherLobatto_quadratureWeights_three
  have h_erase : ((Finset.univ : Finset (Fin 3)).erase ⟨0, by omega⟩)
      = ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin 3)) := by decide
  have h_ne : (⟨1, by omega⟩ : Fin 3) ≠ ⟨2, by omega⟩ := by decide
  have h_eval : ∀ x : ℝ,
      (Lagrange.basis (Finset.univ : Finset (Fin 3)) butcherLobatto_zeros_three
          ⟨0, by omega⟩).eval x = 2 * x ^ 2 - 3 * x + 1 := by
    intro x
    rw [Lagrange.basis, h_erase, Finset.prod_pair h_ne, Polynomial.eval_mul,
        Lagrange.basisDivisor, Lagrange.basisDivisor]
    simp [butcherLobatto_zeros_three, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X]
    ring
  simp_rw [h_eval]
  have hi_x2 : IntervalIntegrable (fun x : ℝ => x ^ 2) MeasureTheory.volume 0 1 :=
    (continuous_pow 2).intervalIntegrable 0 1
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have h2 : ∫ x in (0 : ℝ)..1, x ^ 2 = 1 / 3 := by
    rw [integral_pow]; norm_num
  have h1 : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
    have hp1 := integral_pow (a := (0 : ℝ)) (b := 1) 1
    simp only [pow_one, Nat.cast_one] at hp1
    rw [hp1]; norm_num
  rw [intervalIntegral.integral_add
        ((hi_x2.const_mul 2).sub (hi_x.const_mul 3))
        intervalIntegrable_const,
      intervalIntegral.integral_sub (hi_x2.const_mul 2) (hi_x.const_mul 3),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      h2, h1, integral_one]
  norm_num

/-- **Lobatto `s = 3` weight at `j = 1`.** Value `2/3` (Simpson's rule
midpoint weight). With nodes `(0, 1/2, 1)`, the basis polynomial
`L_1(x) = −4x² + 4x`, so
`b_1 = ∫₀¹ (−4x² + 4x) dx = −4/3 + 2 = 2/3`. -/
theorem butcherLobatto_quadratureWeights_three_apply_one :
    butcherLobatto_quadratureWeights_three ⟨1, by omega⟩ = 2 / 3 := by
  unfold butcherLobatto_quadratureWeights_three
  have h_erase : ((Finset.univ : Finset (Fin 3)).erase ⟨1, by omega⟩)
      = ({⟨0, by omega⟩, ⟨2, by omega⟩} : Finset (Fin 3)) := by decide
  have h_ne : (⟨0, by omega⟩ : Fin 3) ≠ ⟨2, by omega⟩ := by decide
  have h_eval : ∀ x : ℝ,
      (Lagrange.basis (Finset.univ : Finset (Fin 3)) butcherLobatto_zeros_three
          ⟨1, by omega⟩).eval x = -4 * x ^ 2 + 4 * x := by
    intro x
    rw [Lagrange.basis, h_erase, Finset.prod_pair h_ne, Polynomial.eval_mul,
        Lagrange.basisDivisor, Lagrange.basisDivisor]
    simp [butcherLobatto_zeros_three, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X]
    ring
  simp_rw [h_eval]
  have hi_x2 : IntervalIntegrable (fun x : ℝ => x ^ 2) MeasureTheory.volume 0 1 :=
    (continuous_pow 2).intervalIntegrable 0 1
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have h2 : ∫ x in (0 : ℝ)..1, x ^ 2 = 1 / 3 := by
    rw [integral_pow]; norm_num
  have h1 : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
    have hp1 := integral_pow (a := (0 : ℝ)) (b := 1) 1
    simp only [pow_one, Nat.cast_one] at hp1
    rw [hp1]; norm_num
  rw [intervalIntegral.integral_add (hi_x2.const_mul (-4)) (hi_x.const_mul 4),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      h2, h1]
  norm_num

/-- **Lobatto `s = 3` weight at `j = 2`.** Value `1/6` (Simpson's rule
endpoint weight). With nodes `(0, 1/2, 1)`, the basis polynomial
`L_2(x) = 2x² − x`, so
`b_2 = ∫₀¹ (2x² − x) dx = 2/3 − 1/2 = 1/6`. -/
theorem butcherLobatto_quadratureWeights_three_apply_two :
    butcherLobatto_quadratureWeights_three ⟨2, by omega⟩ = 1 / 6 := by
  unfold butcherLobatto_quadratureWeights_three
  have h_erase : ((Finset.univ : Finset (Fin 3)).erase ⟨2, by omega⟩)
      = ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin 3)) := by decide
  have h_ne : (⟨0, by omega⟩ : Fin 3) ≠ ⟨1, by omega⟩ := by decide
  have h_eval : ∀ x : ℝ,
      (Lagrange.basis (Finset.univ : Finset (Fin 3)) butcherLobatto_zeros_three
          ⟨2, by omega⟩).eval x = 2 * x ^ 2 - x := by
    intro x
    rw [Lagrange.basis, h_erase, Finset.prod_pair h_ne, Polynomial.eval_mul,
        Lagrange.basisDivisor, Lagrange.basisDivisor]
    simp [butcherLobatto_zeros_three, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X]
    ring
  simp_rw [h_eval]
  have hi_x2 : IntervalIntegrable (fun x : ℝ => x ^ 2) MeasureTheory.volume 0 1 :=
    (continuous_pow 2).intervalIntegrable 0 1
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have h2 : ∫ x in (0 : ℝ)..1, x ^ 2 = 1 / 3 := by
    rw [integral_pow]; norm_num
  have h1 : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
    have hp1 := integral_pow (a := (0 : ℝ)) (b := 1) 1
    simp only [pow_one, Nat.cast_one] at hp1
    rw [hp1]; norm_num
  rw [intervalIntegral.integral_sub (hi_x2.const_mul 2) hi_x,
      intervalIntegral.integral_const_mul, h2, h1]
  norm_num

/-! #### Non-vacuity anchors — weight-sum equals `1`

For any interpolatory quadrature exact on constants, the weights sum
to `1` (the integral of the constant function `1` over `[0, 1]`). The
three multi-stage examples below confirm this concretely for the
small-`s` Radau I, Lobatto s=2, and Lobatto s=3 weight arrays. -/

/-- **Radau I `s = 2` weight-sum**: `1/4 + 3/4 = 1`. -/
example : butcherRadauI_quadratureWeights_two ⟨0, by omega⟩
        + butcherRadauI_quadratureWeights_two ⟨1, by omega⟩ = 1 := by
  rw [butcherRadauI_quadratureWeights_two_apply_zero,
      butcherRadauI_quadratureWeights_two_apply_one]
  norm_num

/-- **Lobatto `s = 2` weight-sum**: `1/2 + 1/2 = 1` (trapezoidal rule). -/
example : butcherLobatto_quadratureWeights_two ⟨0, by omega⟩
        + butcherLobatto_quadratureWeights_two ⟨1, by omega⟩ = 1 := by
  rw [butcherLobatto_quadratureWeights_two_apply_zero,
      butcherLobatto_quadratureWeights_two_apply_one]
  norm_num

/-- **Lobatto `s = 3` weight-sum**: `1/6 + 2/3 + 1/6 = 1` (Simpson's
rule). -/
example : butcherLobatto_quadratureWeights_three ⟨0, by omega⟩
        + butcherLobatto_quadratureWeights_three ⟨1, by omega⟩
        + butcherLobatto_quadratureWeights_three ⟨2, by omega⟩ = 1 := by
  rw [butcherLobatto_quadratureWeights_three_apply_zero,
      butcherLobatto_quadratureWeights_three_apply_one,
      butcherLobatto_quadratureWeights_three_apply_two]
  norm_num

/-! ## Deliverable D.2 — Small-`s` RKTableau (Radau IIA, `s = 1`)

Cycle 322: lift cycle 320's `butcherRadauII_zeros_one`, cycle 321's
`butcherRadauII_quadratureWeights_one`, and this cycle's
`butcherRadauII_collocationA_one` into a concrete `RKTableau 1`
matching backward Euler. Mirrors cycle 308's
`butcherGaussLegendreRK_one` template
(`Section342.lean:6840–6912`). -/

/-- **Butcher §344 — Radau II collocation A-matrix at `s = 1`**.
The single entry `A_{0,0} = ∫₀^{c_1} L_0(x) dx`, where the unique
Lagrange basis `L_0` at the singleton `{0}` is identically `1`
(`Lagrange.basis_singleton`), so the integral collapses to
`∫₀^1 1 dx = 1`. This recovers the standard **backward Euler**
A-matrix entry. -/
noncomputable def butcherRadauII_collocationA_one : Fin 1 → Fin 1 → ℝ
  | _, _ => ∫ x in (0 : ℝ)..butcherRadauII_zeros_one 0,
      (Lagrange.basis Finset.univ butcherRadauII_zeros_one 0).eval x

/-- The unique entry of `butcherRadauII_collocationA_one` is `1`.
At `s = 1` with `c_1 = 1`, the Lagrange basis on the singleton
`{0}` is identically `1`, and `∫₀^1 1 dx = 1`. Recovers the
backward Euler `A`-matrix entry. -/
theorem butcherRadauII_collocationA_one_apply :
    butcherRadauII_collocationA_one ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by
  unfold butcherRadauII_collocationA_one
  show ∫ x in (0 : ℝ)..butcherRadauII_zeros_one 0,
      (Lagrange.basis Finset.univ butcherRadauII_zeros_one 0).eval x = 1
  simp [butcherRadauII_zeros_one, Lagrange.basis_singleton, Polynomial.eval_one]

/-- **The 1-stage Radau IIA `RKTableau`** assembled from the
canonical Lagrange weights, zeros, and collocation A-matrix of
the Radau II quadrature. At `s = 1` this is backward Euler with
`c = 1`, `b = 1`, `A = 1`. -/
noncomputable def butcherRadauIIA_one :
    OpenMath.Chapter3.Section312.RKTableau 1 where
  A := butcherRadauII_collocationA_one
  b := butcherRadauII_quadratureWeights_one
  c := butcherRadauII_zeros_one

/-- **Direct backward-Euler tableau** for cross-validation:
`c = 1`, `b = 1`, `A = 1` declared inline rather than via
collocation. -/
noncomputable def butcherBackwardEulerRK :
    OpenMath.Chapter3.Section312.RKTableau 1 where
  A := fun _ _ => 1
  b := fun _ => 1
  c := fun _ => 1

/-- **Coincidence**: the cycle-322 collocation-assembled Radau IIA
tableau at `s = 1` equals the direct backward-Euler tableau. The
bridge routes through three small-`s` `_apply` evaluations: A-field
(`butcherRadauII_collocationA_one_apply` = 1), b-field
(`butcherRadauII_quadratureWeights_one_apply` = 1), c-field
(`butcherRadauII_zeros_one` evaluated at `⟨0, _⟩` reduces to `1`). -/
theorem butcherRadauIIA_one_eq_backwardEuler :
    butcherRadauIIA_one = butcherBackwardEulerRK := by
  refine OpenMath.Chapter3.Section312.RKTableau.mk.injEq .. |>.mpr ⟨?_, ?_, ?_⟩
  · funext i j; fin_cases i; fin_cases j
    show butcherRadauII_collocationA_one ⟨0, by omega⟩ ⟨0, by omega⟩ = 1
    exact butcherRadauII_collocationA_one_apply
  · funext i; fin_cases i
    show butcherRadauII_quadratureWeights_one ⟨0, by omega⟩ = 1
    exact butcherRadauII_quadratureWeights_one_apply
  · funext i; fin_cases i
    rfl

/-- **Non-vacuity**: the collocation-assembled Radau IIA tableau at
`s = 1` satisfies the order-1 quadrature condition `B(1)`. Routes
through the coincidence theorem to the direct backward-Euler form,
where `∑ᵢ b_i · c_i^0 = 1 · 1 = 1 = 1/1` follows by `simp`. -/
example : butcherRadauIIA_one.SatisfiesB 1 := by
  rw [butcherRadauIIA_one_eq_backwardEuler]
  intro k h1 hk
  interval_cases k
  · simp [butcherBackwardEulerRK]

/-! ## Deliverable D.3 — Small-`s` RKTableau (Lobatto IIIA, `s = 2`)

Cycle 323: lift cycle 320's `butcherLobatto_zeros_two`, cycle 321's
`butcherLobatto_quadratureWeights_two`, and this cycle's
`butcherLobatto_collocationA_two` into a concrete `RKTableau 2`
matching the trapezoidal rule. Direct extension of cycle 322's
Radau IIA `s = 1` ship to two stages — exercises the
collocation-A-matrix machinery at four entries for the first time.
The textbook tableau (Butcher §344, Table 344(III)) is

  `c = (0, 1)`, `b = (1/2, 1/2)`, `A = !![0, 0; 1/2, 1/2]`,

i.e. the trapezoidal rule. -/

/-- **Butcher §344 — Lobatto IIIA collocation A-matrix at `s = 2`**.
Entry `(i, j) = ∫₀^{c_i} L_j(x) dx`, where the Lagrange basis
polynomials `L_j` are taken over the two-leaf abscissae
`c = (c_0, c_1) = (0, 1)` (`butcherLobatto_zeros_two`). At `s = 2`
the four entries are `(0, 0, 1/2, 1/2)` — i.e. the trapezoidal-rule
A-matrix `!![0, 0; 1/2, 1/2]`. -/
noncomputable def butcherLobatto_collocationA_two
    (i j : Fin 2) : ℝ :=
  ∫ x in (0 : ℝ)..butcherLobatto_zeros_two i,
    (Lagrange.basis Finset.univ butcherLobatto_zeros_two j).eval x

/-- The `(0, 0)` entry of `butcherLobatto_collocationA_two` is `0`.
The upper limit is `c_0 = 0`, so the integral is vacuous
(`intervalIntegral.integral_same`). -/
theorem butcherLobatto_collocationA_two_apply_zero_zero :
    butcherLobatto_collocationA_two ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 := by
  unfold butcherLobatto_collocationA_two
  show ∫ x in (0 : ℝ)..butcherLobatto_zeros_two ⟨0, by omega⟩,
      (Lagrange.basis Finset.univ butcherLobatto_zeros_two
          ⟨0, by omega⟩).eval x = 0
  simp [butcherLobatto_zeros_two, intervalIntegral.integral_same]

/-- The `(0, 1)` entry of `butcherLobatto_collocationA_two` is `0`.
The upper limit is `c_0 = 0`, so the integral is vacuous
(`intervalIntegral.integral_same`). -/
theorem butcherLobatto_collocationA_two_apply_zero_one :
    butcherLobatto_collocationA_two ⟨0, by omega⟩ ⟨1, by omega⟩ = 0 := by
  unfold butcherLobatto_collocationA_two
  show ∫ x in (0 : ℝ)..butcherLobatto_zeros_two ⟨0, by omega⟩,
      (Lagrange.basis Finset.univ butcherLobatto_zeros_two
          ⟨1, by omega⟩).eval x = 0
  simp [butcherLobatto_zeros_two, intervalIntegral.integral_same]

/-- The `(1, 0)` entry of `butcherLobatto_collocationA_two` is `1/2`.
The upper limit is `c_1 = 1` and the integrand is the basis polynomial
`L_0(x) = 1 - x`, so `∫₀¹ (1 - x) dx = 1/2`. Same integral as
`butcherLobatto_quadratureWeights_two_apply_zero` (cycle 321). -/
theorem butcherLobatto_collocationA_two_apply_one_zero :
    butcherLobatto_collocationA_two ⟨1, by omega⟩ ⟨0, by omega⟩ = 1 / 2 := by
  unfold butcherLobatto_collocationA_two
  show ∫ x in (0 : ℝ)..butcherLobatto_zeros_two ⟨1, by omega⟩,
      (Lagrange.basis Finset.univ butcherLobatto_zeros_two
          ⟨0, by omega⟩).eval x = 1 / 2
  have h_erase : ((Finset.univ : Finset (Fin 2)).erase ⟨0, by omega⟩)
      = ({⟨1, by omega⟩} : Finset (Fin 2)) := by decide
  have h_eval : ∀ x : ℝ,
      (Lagrange.basis (Finset.univ : Finset (Fin 2)) butcherLobatto_zeros_two
          ⟨0, by omega⟩).eval x = 1 - x := by
    intro x
    rw [Lagrange.basis, h_erase, Finset.prod_singleton, Lagrange.basisDivisor]
    simp [butcherLobatto_zeros_two, Polynomial.eval_sub,
          Polynomial.eval_X]
  simp_rw [h_eval]
  show ∫ x in (0 : ℝ)..butcherLobatto_zeros_two ⟨1, by omega⟩, ((1 : ℝ) - x)
      = 1 / 2
  have h_c1 : butcherLobatto_zeros_two ⟨1, by omega⟩ = 1 := rfl
  rw [h_c1]
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have hx : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
    have hp1 := integral_pow (a := (0 : ℝ)) (b := 1) 1
    simp only [pow_one, Nat.cast_one] at hp1
    rw [hp1]; norm_num
  rw [intervalIntegral.integral_sub intervalIntegrable_const hi_x,
      integral_one, hx]
  norm_num

/-- The `(1, 1)` entry of `butcherLobatto_collocationA_two` is `1/2`.
The upper limit is `c_1 = 1` and the integrand is the basis polynomial
`L_1(x) = x`, so `∫₀¹ x dx = 1/2`. Same integral as
`butcherLobatto_quadratureWeights_two_apply_one` (cycle 321). -/
theorem butcherLobatto_collocationA_two_apply_one_one :
    butcherLobatto_collocationA_two ⟨1, by omega⟩ ⟨1, by omega⟩ = 1 / 2 := by
  unfold butcherLobatto_collocationA_two
  show ∫ x in (0 : ℝ)..butcherLobatto_zeros_two ⟨1, by omega⟩,
      (Lagrange.basis Finset.univ butcherLobatto_zeros_two
          ⟨1, by omega⟩).eval x = 1 / 2
  have h_erase : ((Finset.univ : Finset (Fin 2)).erase ⟨1, by omega⟩)
      = ({⟨0, by omega⟩} : Finset (Fin 2)) := by decide
  have h_eval : ∀ x : ℝ,
      (Lagrange.basis (Finset.univ : Finset (Fin 2)) butcherLobatto_zeros_two
          ⟨1, by omega⟩).eval x = x := by
    intro x
    rw [Lagrange.basis, h_erase, Finset.prod_singleton, Lagrange.basisDivisor]
    simp [butcherLobatto_zeros_two, Polynomial.eval_X]
  simp_rw [h_eval]
  show ∫ x in (0 : ℝ)..butcherLobatto_zeros_two ⟨1, by omega⟩, x = 1 / 2
  have h_c1 : butcherLobatto_zeros_two ⟨1, by omega⟩ = 1 := rfl
  rw [h_c1]
  have hp1 := integral_pow (a := (0 : ℝ)) (b := 1) 1
  simp only [pow_one, Nat.cast_one] at hp1
  rw [hp1]; norm_num

/-- **The 2-stage Lobatto IIIA `RKTableau`** assembled from the
canonical Lagrange weights, zeros, and collocation A-matrix of the
Lobatto quadrature. At `s = 2` this is the trapezoidal rule with
`c = (0, 1)`, `b = (1/2, 1/2)`, `A = !![0, 0; 1/2, 1/2]`. -/
noncomputable def butcherLobattoIIIA_two :
    OpenMath.Chapter3.Section312.RKTableau 2 where
  A := butcherLobatto_collocationA_two
  b := butcherLobatto_quadratureWeights_two
  c := butcherLobatto_zeros_two

/-- **Direct trapezoidal-rule tableau** for cross-validation:
`c = (0, 1)`, `b = (1/2, 1/2)`, `A = !![0, 0; 1/2, 1/2]`
declared inline rather than via collocation. -/
noncomputable def butcherTrapezoidalRK :
    OpenMath.Chapter3.Section312.RKTableau 2 where
  A := !![0, 0; 1/2, 1/2]
  b := ![1/2, 1/2]
  c := ![0, 1]

/-- **Coincidence**: the cycle-323 collocation-assembled Lobatto IIIA
tableau at `s = 2` equals the direct trapezoidal-rule tableau. The
bridge routes through four `_apply` evaluations of the collocation
A-matrix (`butcherLobatto_collocationA_two_apply_*`), the cycle 321
weight `_apply` lemmas, and the pattern-matched abscissae reductions. -/
theorem butcherLobattoIIIA_two_eq_trapezoidal :
    butcherLobattoIIIA_two = butcherTrapezoidalRK := by
  refine OpenMath.Chapter3.Section312.RKTableau.mk.injEq .. |>.mpr ⟨?_, ?_, ?_⟩
  · funext i j; fin_cases i <;> fin_cases j
    · show butcherLobatto_collocationA_two ⟨0, by omega⟩ ⟨0, by omega⟩ = _
      rw [butcherLobatto_collocationA_two_apply_zero_zero]; rfl
    · show butcherLobatto_collocationA_two ⟨0, by omega⟩ ⟨1, by omega⟩ = _
      rw [butcherLobatto_collocationA_two_apply_zero_one]; rfl
    · show butcherLobatto_collocationA_two ⟨1, by omega⟩ ⟨0, by omega⟩ = _
      rw [butcherLobatto_collocationA_two_apply_one_zero]; rfl
    · show butcherLobatto_collocationA_two ⟨1, by omega⟩ ⟨1, by omega⟩ = _
      rw [butcherLobatto_collocationA_two_apply_one_one]; rfl
  · funext i; fin_cases i
    · show butcherLobatto_quadratureWeights_two ⟨0, by omega⟩ = _
      rw [butcherLobatto_quadratureWeights_two_apply_zero]; rfl
    · show butcherLobatto_quadratureWeights_two ⟨1, by omega⟩ = _
      rw [butcherLobatto_quadratureWeights_two_apply_one]; rfl
  · funext i; fin_cases i <;> rfl

/-- **Non-vacuity**: the collocation-assembled Lobatto IIIA tableau at
`s = 2` satisfies the order-2 quadrature condition `B(2)`. Routes
through the coincidence theorem to the direct trapezoidal-rule form,
where `∑ⱼ bⱼ · cⱼ^0 = 1/2 + 1/2 = 1 = 1/1` and
`∑ⱼ bⱼ · cⱼ^1 = (1/2)·0 + (1/2)·1 = 1/2 = 1/2`. -/
example : butcherLobattoIIIA_two.SatisfiesB 2 := by
  rw [butcherLobattoIIIA_two_eq_trapezoidal]
  intro k h1 hk
  interval_cases k
  · simp [butcherTrapezoidalRK, Fin.sum_univ_two]; norm_num
  · simp [butcherTrapezoidalRK, Fin.sum_univ_two]

/-! ## Deliverable D.4 — Small-`s` RKTableau (Radau IIA, `s = 2`)

Cycle 324: lift cycle 320's `butcherRadauII_zeros_two`, cycle 321's
`butcherRadauII_quadratureWeights_two`, and this cycle's
`butcherRadauII_collocationA_two` into a concrete `RKTableau 2`
matching Butcher §344 Table 344(II) (p. 245). Direct extension of
cycle 322's Radau IIA `s = 1` and structural mirror of cycle 323's
Lobatto IIIA `s = 2` ship, but with non-trivial integration over
`[0, 1/3]` for the `(0, j)` A-matrix entries. The textbook tableau
(Butcher §344, Table 344(II)) is

  `c = (1/3, 1)`, `b = (3/4, 1/4)`,
  `A = !![5/12, -1/12; 3/4, 1/4]`. -/

/-- **Butcher §344 — Radau II collocation A-matrix at `s = 2`**.
Entry `(i, j) = ∫₀^{c_i} L_j(x) dx`, where the Lagrange basis
polynomials `L_j` are taken over the two-leaf abscissae
`c = (c_0, c_1) = (1/3, 1)` (`butcherRadauII_zeros_two`). At `s = 2`
the four entries are `(5/12, -1/12, 3/4, 1/4)` — i.e. the Radau IIA
A-matrix `!![5/12, -1/12; 3/4, 1/4]` (Butcher Table 344(II) p. 245). -/
noncomputable def butcherRadauII_collocationA_two
    (i j : Fin 2) : ℝ :=
  ∫ x in (0 : ℝ)..butcherRadauII_zeros_two i,
    (Lagrange.basis Finset.univ butcherRadauII_zeros_two j).eval x

/-- The `(0, 0)` entry of `butcherRadauII_collocationA_two` is `5/12`.
The upper limit is `c_0 = 1/3` and the integrand is the basis polynomial
`L_0(x) = (3/2) − (3/2)x`, so `∫₀^{1/3} ((3/2) − (3/2)x) dx
= (3/2)(1/3) − (3/4)(1/9) = 1/2 − 1/12 = 5/12`. -/
theorem butcherRadauII_collocationA_two_apply_zero_zero :
    butcherRadauII_collocationA_two ⟨0, by omega⟩ ⟨0, by omega⟩ = 5 / 12 := by
  unfold butcherRadauII_collocationA_two
  show ∫ x in (0 : ℝ)..butcherRadauII_zeros_two ⟨0, by omega⟩,
      (Lagrange.basis Finset.univ butcherRadauII_zeros_two
          ⟨0, by omega⟩).eval x = 5 / 12
  have h_erase : ((Finset.univ : Finset (Fin 2)).erase ⟨0, by omega⟩)
      = ({⟨1, by omega⟩} : Finset (Fin 2)) := by decide
  have h_eval : ∀ x : ℝ,
      (Lagrange.basis (Finset.univ : Finset (Fin 2)) butcherRadauII_zeros_two
          ⟨0, by omega⟩).eval x = (3/2) - (3/2) * x := by
    intro x
    rw [Lagrange.basis, h_erase, Finset.prod_singleton, Lagrange.basisDivisor]
    simp [butcherRadauII_zeros_two, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X]
    ring
  simp_rw [h_eval]
  show ∫ x in (0 : ℝ)..butcherRadauII_zeros_two ⟨0, by omega⟩,
      ((3 : ℝ)/2 - (3/2) * x) = 5 / 12
  have h_c0 : butcherRadauII_zeros_two ⟨0, by omega⟩ = 1 / 3 := rfl
  rw [h_c0]
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 (1/3) :=
    continuous_id.intervalIntegrable 0 (1/3)
  have hx : ∫ x in (0 : ℝ)..(1/3 : ℝ), x = 1/18 := by
    have hp1 := integral_pow (a := (0 : ℝ)) (b := (1/3 : ℝ)) 1
    simp only [pow_one, Nat.cast_one] at hp1
    rw [hp1]; norm_num
  rw [intervalIntegral.integral_sub intervalIntegrable_const
        (hi_x.const_mul (3/2)),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      hx]
  norm_num

/-- The `(0, 1)` entry of `butcherRadauII_collocationA_two` is `-1/12`.
The upper limit is `c_0 = 1/3` and the integrand is the basis polynomial
`L_1(x) = (3/2)x − 1/2`, so `∫₀^{1/3} ((3/2)x − 1/2) dx
= (3/4)(1/9) − (1/2)(1/3) = 1/12 − 1/6 = −1/12`. -/
theorem butcherRadauII_collocationA_two_apply_zero_one :
    butcherRadauII_collocationA_two ⟨0, by omega⟩ ⟨1, by omega⟩ = -(1 / 12) := by
  unfold butcherRadauII_collocationA_two
  show ∫ x in (0 : ℝ)..butcherRadauII_zeros_two ⟨0, by omega⟩,
      (Lagrange.basis Finset.univ butcherRadauII_zeros_two
          ⟨1, by omega⟩).eval x = -(1 / 12)
  have h_erase : ((Finset.univ : Finset (Fin 2)).erase ⟨1, by omega⟩)
      = ({⟨0, by omega⟩} : Finset (Fin 2)) := by decide
  have h_eval : ∀ x : ℝ,
      (Lagrange.basis (Finset.univ : Finset (Fin 2)) butcherRadauII_zeros_two
          ⟨1, by omega⟩).eval x = (3/2) * x - (1/2) := by
    intro x
    rw [Lagrange.basis, h_erase, Finset.prod_singleton, Lagrange.basisDivisor]
    simp [butcherRadauII_zeros_two, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X]
    ring
  simp_rw [h_eval]
  show ∫ x in (0 : ℝ)..butcherRadauII_zeros_two ⟨0, by omega⟩,
      ((3 : ℝ)/2 * x - (1/2)) = -(1 / 12)
  have h_c0 : butcherRadauII_zeros_two ⟨0, by omega⟩ = 1 / 3 := rfl
  rw [h_c0]
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 (1/3) :=
    continuous_id.intervalIntegrable 0 (1/3)
  have hx : ∫ x in (0 : ℝ)..(1/3 : ℝ), x = 1/18 := by
    have hp1 := integral_pow (a := (0 : ℝ)) (b := (1/3 : ℝ)) 1
    simp only [pow_one, Nat.cast_one] at hp1
    rw [hp1]; norm_num
  rw [intervalIntegral.integral_sub (hi_x.const_mul (3/2))
        intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      hx]
  norm_num

/-- The `(1, 0)` entry of `butcherRadauII_collocationA_two` is `3/4`.
The upper limit is `c_1 = 1` and the integrand is the basis polynomial
`L_0(x) = (3/2) − (3/2)x`, so `∫₀¹ ((3/2) − (3/2)x) dx
= 3/2 − 3/4 = 3/4`. Same integral as
`butcherRadauII_quadratureWeights_two_apply_zero` (cycle 321). -/
theorem butcherRadauII_collocationA_two_apply_one_zero :
    butcherRadauII_collocationA_two ⟨1, by omega⟩ ⟨0, by omega⟩ = 3 / 4 := by
  unfold butcherRadauII_collocationA_two
  show ∫ x in (0 : ℝ)..butcherRadauII_zeros_two ⟨1, by omega⟩,
      (Lagrange.basis Finset.univ butcherRadauII_zeros_two
          ⟨0, by omega⟩).eval x = 3 / 4
  have h_erase : ((Finset.univ : Finset (Fin 2)).erase ⟨0, by omega⟩)
      = ({⟨1, by omega⟩} : Finset (Fin 2)) := by decide
  have h_eval : ∀ x : ℝ,
      (Lagrange.basis (Finset.univ : Finset (Fin 2)) butcherRadauII_zeros_two
          ⟨0, by omega⟩).eval x = (3/2) - (3/2) * x := by
    intro x
    rw [Lagrange.basis, h_erase, Finset.prod_singleton, Lagrange.basisDivisor]
    simp [butcherRadauII_zeros_two, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X]
    ring
  simp_rw [h_eval]
  show ∫ x in (0 : ℝ)..butcherRadauII_zeros_two ⟨1, by omega⟩,
      ((3 : ℝ)/2 - (3/2) * x) = 3 / 4
  have h_c1 : butcherRadauII_zeros_two ⟨1, by omega⟩ = 1 := rfl
  rw [h_c1]
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have hx : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
    have hp1 := integral_pow (a := (0 : ℝ)) (b := 1) 1
    simp only [pow_one, Nat.cast_one] at hp1
    rw [hp1]; norm_num
  rw [intervalIntegral.integral_sub intervalIntegrable_const
        (hi_x.const_mul (3/2)),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      hx]
  norm_num

/-- The `(1, 1)` entry of `butcherRadauII_collocationA_two` is `1/4`.
The upper limit is `c_1 = 1` and the integrand is the basis polynomial
`L_1(x) = (3/2)x − 1/2`, so `∫₀¹ ((3/2)x − 1/2) dx
= 3/4 − 1/2 = 1/4`. Same integral as
`butcherRadauII_quadratureWeights_two_apply_one` (cycle 321). -/
theorem butcherRadauII_collocationA_two_apply_one_one :
    butcherRadauII_collocationA_two ⟨1, by omega⟩ ⟨1, by omega⟩ = 1 / 4 := by
  unfold butcherRadauII_collocationA_two
  show ∫ x in (0 : ℝ)..butcherRadauII_zeros_two ⟨1, by omega⟩,
      (Lagrange.basis Finset.univ butcherRadauII_zeros_two
          ⟨1, by omega⟩).eval x = 1 / 4
  have h_erase : ((Finset.univ : Finset (Fin 2)).erase ⟨1, by omega⟩)
      = ({⟨0, by omega⟩} : Finset (Fin 2)) := by decide
  have h_eval : ∀ x : ℝ,
      (Lagrange.basis (Finset.univ : Finset (Fin 2)) butcherRadauII_zeros_two
          ⟨1, by omega⟩).eval x = (3/2) * x - (1/2) := by
    intro x
    rw [Lagrange.basis, h_erase, Finset.prod_singleton, Lagrange.basisDivisor]
    simp [butcherRadauII_zeros_two, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X]
    ring
  simp_rw [h_eval]
  show ∫ x in (0 : ℝ)..butcherRadauII_zeros_two ⟨1, by omega⟩,
      ((3 : ℝ)/2 * x - (1/2)) = 1 / 4
  have h_c1 : butcherRadauII_zeros_two ⟨1, by omega⟩ = 1 := rfl
  rw [h_c1]
  have hi_x : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have hx : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
    have hp1 := integral_pow (a := (0 : ℝ)) (b := 1) 1
    simp only [pow_one, Nat.cast_one] at hp1
    rw [hp1]; norm_num
  rw [intervalIntegral.integral_sub (hi_x.const_mul (3/2))
        intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      hx]
  norm_num

/-- **The 2-stage Radau IIA `RKTableau`** assembled from the
canonical Lagrange weights, zeros, and collocation A-matrix of the
Radau II quadrature. At `s = 2` this is Butcher §344 Table 344(II)
with `c = (1/3, 1)`, `b = (3/4, 1/4)`,
`A = !![5/12, -1/12; 3/4, 1/4]`. -/
noncomputable def butcherRadauIIA_two :
    OpenMath.Chapter3.Section312.RKTableau 2 where
  A := butcherRadauII_collocationA_two
  b := butcherRadauII_quadratureWeights_two
  c := butcherRadauII_zeros_two

/-- **Direct Radau IIA `s = 2` tableau** for cross-validation:
`c = (1/3, 1)`, `b = (3/4, 1/4)`, `A = !![5/12, -1/12; 3/4, 1/4]`
declared inline rather than via collocation. -/
noncomputable def butcherRadauIIADirect_two :
    OpenMath.Chapter3.Section312.RKTableau 2 where
  A := !![5/12, -(1/12); 3/4, 1/4]
  b := ![3/4, 1/4]
  c := ![1/3, 1]

/-- **Coincidence**: the cycle-324 collocation-assembled Radau IIA
tableau at `s = 2` equals the direct Radau IIA tableau. The bridge
routes through four `_apply` evaluations of the collocation A-matrix
(`butcherRadauII_collocationA_two_apply_*`), the cycle 321 weight
`_apply` lemmas, and the pattern-matched abscissae reductions. -/
theorem butcherRadauIIA_two_eq_direct :
    butcherRadauIIA_two = butcherRadauIIADirect_two := by
  refine OpenMath.Chapter3.Section312.RKTableau.mk.injEq .. |>.mpr ⟨?_, ?_, ?_⟩
  · funext i j; fin_cases i <;> fin_cases j
    · show butcherRadauII_collocationA_two ⟨0, by omega⟩ ⟨0, by omega⟩ = _
      rw [butcherRadauII_collocationA_two_apply_zero_zero]; rfl
    · show butcherRadauII_collocationA_two ⟨0, by omega⟩ ⟨1, by omega⟩ = _
      rw [butcherRadauII_collocationA_two_apply_zero_one]; rfl
    · show butcherRadauII_collocationA_two ⟨1, by omega⟩ ⟨0, by omega⟩ = _
      rw [butcherRadauII_collocationA_two_apply_one_zero]; rfl
    · show butcherRadauII_collocationA_two ⟨1, by omega⟩ ⟨1, by omega⟩ = _
      rw [butcherRadauII_collocationA_two_apply_one_one]; rfl
  · funext i; fin_cases i
    · show butcherRadauII_quadratureWeights_two ⟨0, by omega⟩ = _
      rw [butcherRadauII_quadratureWeights_two_apply_zero]; rfl
    · show butcherRadauII_quadratureWeights_two ⟨1, by omega⟩ = _
      rw [butcherRadauII_quadratureWeights_two_apply_one]; rfl
  · funext i; fin_cases i <;> rfl

/-- **Non-vacuity**: the collocation-assembled Radau IIA tableau at
`s = 2` satisfies the order-3 quadrature condition `B(3)` (Radau IIA
at `s = 2` is exact for polynomials of degree `2s − 1 = 3`). Routes
through the coincidence theorem to the direct Radau IIA form, where
`∑ⱼ bⱼ · cⱼ^0 = 3/4 + 1/4 = 1 = 1/1`,
`∑ⱼ bⱼ · cⱼ^1 = (3/4)·(1/3) + (1/4)·1 = 1/4 + 1/4 = 1/2`, and
`∑ⱼ bⱼ · cⱼ^2 = (3/4)·(1/9) + (1/4)·1 = 1/12 + 3/12 = 1/3`. -/
example : butcherRadauIIA_two.SatisfiesB 3 := by
  rw [butcherRadauIIA_two_eq_direct]
  intro k h1 hk
  interval_cases k
  · simp [butcherRadauIIADirect_two, Fin.sum_univ_two]; norm_num
  · simp [butcherRadauIIADirect_two, Fin.sum_univ_two]; norm_num
  · simp [butcherRadauIIADirect_two, Fin.sum_univ_two]; norm_num

/-! ## Deliverable D.5 — Small-`s` RKTableau (Radau IA, `s = 1`)

Cycle 325: lift cycle 320's `butcherRadauI_zeros_one`, cycle 321's
`butcherRadauI_quadratureWeights_one`, and this cycle's
`butcherRadauI_collocationA_one` into a concrete `RKTableau 1`
matching forward Euler. Mirrors cycle 322's Radau IIA `s = 1` ship
with three swaps: `RadauII` → `RadauI`, integral becomes vacuous via
`intervalIntegral.integral_same` since `c_1 = 0`, and direct form
`A = !![1]` becomes `A = !![0]`. -/

/-- **Butcher §344 — Radau I collocation A-matrix at `s = 1`**.
The single entry `A_{0,0} = ∫₀^{c_1} L_0(x) dx`, where `c_1 = 0`
(`butcherRadauI_zeros_one`). The integration interval `[0, 0]` is
degenerate so the integral evaluates to `0`
(`intervalIntegral.integral_same`). This recovers the standard
**forward Euler** A-matrix entry. -/
noncomputable def butcherRadauI_collocationA_one : Fin 1 → Fin 1 → ℝ
  | _, _ => ∫ x in (0 : ℝ)..butcherRadauI_zeros_one 0,
      (Lagrange.basis Finset.univ butcherRadauI_zeros_one 0).eval x

/-- The unique entry of `butcherRadauI_collocationA_one` is `0`.
At `s = 1` with `c_1 = 0`, the integration interval `[0, 0]` is
degenerate, so `∫₀^0 L_0(x) dx = 0`
(`intervalIntegral.integral_same`). Recovers the forward Euler
`A`-matrix entry. -/
theorem butcherRadauI_collocationA_one_apply :
    butcherRadauI_collocationA_one ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 := by
  unfold butcherRadauI_collocationA_one
  show ∫ x in (0 : ℝ)..butcherRadauI_zeros_one 0,
      (Lagrange.basis Finset.univ butcherRadauI_zeros_one 0).eval x = 0
  simp [butcherRadauI_zeros_one, intervalIntegral.integral_same]

/-- **The 1-stage Radau IA `RKTableau`** assembled from the
canonical Lagrange weights, zeros, and collocation A-matrix of
the Radau I quadrature. At `s = 1` this is forward Euler with
`c = 0`, `b = 1`, `A = 0`. -/
noncomputable def butcherRadauIA_one :
    OpenMath.Chapter3.Section312.RKTableau 1 where
  A := butcherRadauI_collocationA_one
  b := butcherRadauI_quadratureWeights_one
  c := butcherRadauI_zeros_one

/-- **Direct forward-Euler tableau** for cross-validation:
`c = 0`, `b = 1`, `A = 0` declared inline rather than via
collocation. -/
noncomputable def butcherForwardEulerRK :
    OpenMath.Chapter3.Section312.RKTableau 1 where
  A := fun _ _ => 0
  b := fun _ => 1
  c := fun _ => 0

/-- **Coincidence**: the cycle-325 collocation-assembled Radau IA
tableau at `s = 1` equals the direct forward-Euler tableau. The
bridge routes through three small-`s` `_apply` evaluations: A-field
(`butcherRadauI_collocationA_one_apply` = 0), b-field
(`butcherRadauI_quadratureWeights_one_apply` = 1), c-field
(`butcherRadauI_zeros_one` evaluated at `⟨0, _⟩` reduces to `0`). -/
theorem butcherRadauIA_one_eq_forwardEuler :
    butcherRadauIA_one = butcherForwardEulerRK := by
  refine OpenMath.Chapter3.Section312.RKTableau.mk.injEq .. |>.mpr ⟨?_, ?_, ?_⟩
  · funext i j; fin_cases i; fin_cases j
    show butcherRadauI_collocationA_one ⟨0, by omega⟩ ⟨0, by omega⟩ = 0
    exact butcherRadauI_collocationA_one_apply
  · funext i; fin_cases i
    show butcherRadauI_quadratureWeights_one ⟨0, by omega⟩ = 1
    exact butcherRadauI_quadratureWeights_one_apply
  · funext i; fin_cases i
    rfl

/-- **Non-vacuity**: the collocation-assembled Radau IA tableau at
`s = 1` satisfies the order-1 quadrature condition `B(1)`. Routes
through the coincidence theorem to the direct forward-Euler form,
where `∑ᵢ b_i · c_i^0 = 1 · 1 = 1 = 1/1` follows by `simp`. Forward
Euler has classical order `2s − 1 = 1`, so `B(1)` is maximal here. -/
example : butcherRadauIA_one.SatisfiesB 1 := by
  rw [butcherRadauIA_one_eq_forwardEuler]
  intro k h1 hk
  interval_cases k
  · simp [butcherForwardEulerRK]

/-! ## Deliverable D.6 — Small-`s` RKTableau (Radau IA, `s = 2`)

Cycle 326. Per Butcher Table 344(I) (`extraction/raw_text/ch03.txt:5214`)
the Radau IA family's `A`-matrix is *"the reflections of Radau II"*,
**not** the plain Lagrange collocation matrix
`A_{ij} = ∫₀^{c_i} L_j(x) dx`. The cycle 326 §D faithfulness audit
confirmed this divergence at `s = 2`: plain collocation at the
Radau I abscissae `(0, 2/3)` yields rows `(0, 0)` and `(1/3, 1/3)`,
while Butcher's printed Radau IA `s = 2` table (p. 225,
`ch03.txt:5274`) gives rows `(1/4, -1/4)` and `(1/4, 5/12)`. See
`.prover-state/issues/radau_ia_collocation_divergence.md` for the
full audit.

Cycle 326 therefore ships only the **direct form** of the Radau IA
`s = 2` tableau, with the textbook values declared inline. The
collocation/reflection bridge from `butcherRadauIIA_two` (cycle 324)
to `butcherRadauIADirect_two` (this cycle) is deferred to a future
cycle that formalises Butcher's "reflections of Radau II"
construction in full. -/

/-- **Butcher §344 — Radau IA `s = 2` tableau** declared inline from
Butcher's printed Table 344(I), p. 225: `c = (0, 2/3)`,
`b = (1/4, 3/4)`, `A = !![1/4, -1/4; 1/4, 5/12]`. This is the
classical Radau IA two-stage method with attainable order
`p = 2s − 1 = 3`.

The A-matrix follows the *"reflections of Radau II"* recipe from
Butcher Table 344(I) rather than plain Lagrange collocation; see
the section header docstring and
`.prover-state/issues/radau_ia_collocation_divergence.md` for the
audit. -/
noncomputable def butcherRadauIADirect_two :
    OpenMath.Chapter3.Section312.RKTableau 2 where
  A := !![1/4, -(1/4); 1/4, 5/12]
  b := ![1/4, 3/4]
  c := ![0, 2/3]

/-- **Non-vacuity**: the direct Radau IA `s = 2` tableau satisfies
the order-3 quadrature condition `B(3)` (Radau IA at `s = 2` is
exact for polynomials of degree `2s − 1 = 3`).
`∑ⱼ bⱼ · cⱼ^0 = 1/4 + 3/4 = 1 = 1/1`,
`∑ⱼ bⱼ · cⱼ^1 = (1/4)·0 + (3/4)·(2/3) = 1/2`,
`∑ⱼ bⱼ · cⱼ^2 = 0 + (3/4)·(4/9) = 1/3`. -/
example : butcherRadauIADirect_two.SatisfiesB 3 := by
  intro k h1 hk
  interval_cases k
  · simp [butcherRadauIADirect_two, Fin.sum_univ_two]; norm_num
  · simp [butcherRadauIADirect_two, Fin.sum_univ_two]; norm_num
  · simp [butcherRadauIADirect_two, Fin.sum_univ_two]; norm_num

/-! ## Deliverable D.7 — Small-`s` RKTableau (Lobatto IIIB, `s = 3`)

Cycle 327. Per Butcher Table 344(I) p. 224
(`extraction/raw_text/ch03.txt:5263`), the Lobatto IIIB family does
**not** exist at `s = 2`, so `s = 3` is the smallest available stage
count. The `A`-matrix follows Butcher's D(s) recipe rather than plain
Lagrange collocation; the `b` and `c` agree with Lobatto IIIA `s = 3`
(both come from Lobatto quadrature at `(0, 1/2, 1)` with weights
`(1/6, 2/3, 1/6)`). The classical order is `p = 2s − 2 = 4`.

As with cycle 326's Radau IA direct-form ship, the
collocation/reflection bridge to an abstract construction of
`butcherLobattoIIIBDirect_three` is deferred. -/

/-- **Butcher §344 — Lobatto IIIB `s = 3` tableau** declared inline
from Butcher's printed Table 344(III), p. 245
(`extraction/raw_text/ch03.txt:5426-5434`): `c = (0, 1/2, 1)`,
`b = (1/6, 2/3, 1/6)`,
`A = !![1/6, -(1/6), 0; 1/6, 1/3, 0; 1/6, 5/6, 0]`. The classical
attainable order is `p = 2s − 2 = 4`.

The `A`-matrix follows Butcher's D(s) recipe (NOT plain Lagrange
collocation, which would diverge in the same manner as the cycle 326
Radau IA audit); `b` and `c` coincide with Lobatto IIIA `s = 3` since
both families share the Lobatto quadrature choice. -/
noncomputable def butcherLobattoIIIBDirect_three :
    OpenMath.Chapter3.Section312.RKTableau 3 where
  A := !![1/6, -(1/6), 0; 1/6, 1/3, 0; 1/6, 5/6, 0]
  b := ![1/6, 2/3, 1/6]
  c := ![0, 1/2, 1]

/-- **Non-vacuity**: the direct Lobatto IIIB `s = 3` tableau satisfies
the order-4 quadrature condition `B(4)` (Lobatto IIIB at `s = 3` is
exact for polynomials of degree `2s − 2 = 4`).
`∑ⱼ bⱼ · cⱼ^0 = 1/6 + 2/3 + 1/6 = 1 = 1/1`,
`∑ⱼ bⱼ · cⱼ^1 = 0 + (2/3)·(1/2) + (1/6)·1 = 1/2`,
`∑ⱼ bⱼ · cⱼ^2 = 0 + (2/3)·(1/4) + (1/6)·1 = 1/3`,
`∑ⱼ bⱼ · cⱼ^3 = 0 + (2/3)·(1/8) + (1/6)·1 = 1/4`. -/
example : butcherLobattoIIIBDirect_three.SatisfiesB 4 := by
  intro k h1 hk
  interval_cases k
  · simp [butcherLobattoIIIBDirect_three, Fin.sum_univ_three]; norm_num
  · simp [butcherLobattoIIIBDirect_three, Fin.sum_univ_three]; norm_num
  · simp [butcherLobattoIIIBDirect_three, Fin.sum_univ_three]; norm_num
  · simp [butcherLobattoIIIBDirect_three, Fin.sum_univ_three]; norm_num

/-! ## Deliverable D.8 — Small-`s` RKTableau (Radau II, `s = 2`, D(s) variant)

Cycle 328. Per Butcher Table 344(I) p. 244 (`ch03.txt:5219`), the
Radau II family uses `Choice of A = D(s)` — the matrix satisfying the
D(s) simplifying assumption — while Radau IIA uses
`Choice of A = "reflections of Radau I"` (which, for the printed
small-`s` tables, agrees with the plain Lagrange collocation matrix
at the Radau II abscissae). The two families share `b` and `c` (both
use the Radau II quadrature) but the `A`-matrices differ.

The cycle 328 §D faithfulness audit (Butcher Table 344(II) p. 245,
`ch03.txt:5284-5289`) confirms this divergence at `s = 2`: the
printed Radau II `s = 2` table reads `c = (1/3, 1)`, `b = (3/4, 1/4)`,
`A = !![1/3, 0; 1, 0]`, whereas the cycle-324
`butcherRadauIIA_two` direct form ships
`A = !![5/12, -1/12; 3/4, 1/4]`. The D(s) A-matrix has its last
column equal to zero (since `c_s = 1` forces
`(b_j/k)(1 - c_j^k) = 0` for `j = s`, and the D(s) construction
fixes the entries individually); this matches the printed Radau II
`s = 3` table at `ch03.txt:5344-5350` where the last column of `A`
is also `(0, 0, 0)`.

As with cycles 326/327's direct-form ships, the abstract
construction of the D(s) A-matrix from the simplifying-assumption
equations is deferred; this cycle ships the printed values inline. -/

/-- **Butcher §344 — Radau II `s = 2` tableau (D(s) variant)**
declared inline from Butcher's printed Table 344(II), p. 245
(`extraction/raw_text/ch03.txt:5284-5289`): `c = (1/3, 1)`,
`b = (3/4, 1/4)`, `A = !![1/3, 0; 1, 0]`. This is the classical
Radau II two-stage method (Butcher's `Choice of A = D(s)` row of
Table 344(I)), with attainable order `p = 2s − 1 = 3`.

The A-matrix follows Butcher's *D(s) simplifying-assumption* recipe
rather than the *"reflections of Radau I"* recipe used by Radau IIA;
the two coincide on `b` and `c` (both arise from the Radau II
quadrature) but disagree on `A`. See `butcherRadauIIA_two` (cycle
324) for the IIA variant, and the section header docstring for the
audit. -/
noncomputable def butcherRadauIIDirect_two :
    OpenMath.Chapter3.Section312.RKTableau 2 where
  A := !![1/3, 0; 1, 0]
  b := ![3/4, 1/4]
  c := ![1/3, 1]

/-- **Non-vacuity (B(3))**: the direct Radau II `s = 2` tableau
satisfies the order-3 quadrature condition `B(3)` (Radau II at
`s = 2` is exact for polynomials of degree `2s − 1 = 3`). The
`b` and `c` agree with `butcherRadauIIA_two`, so the same arithmetic
applies:
`∑ⱼ bⱼ · cⱼ^0 = 3/4 + 1/4 = 1 = 1/1`,
`∑ⱼ bⱼ · cⱼ^1 = (3/4)·(1/3) + (1/4)·1 = 1/4 + 1/4 = 1/2`,
`∑ⱼ bⱼ · cⱼ^2 = (3/4)·(1/9) + (1/4)·1 = 1/12 + 3/12 = 1/3`. -/
example : butcherRadauIIDirect_two.SatisfiesB 3 := by
  intro k h1 hk
  interval_cases k
  · simp [butcherRadauIIDirect_two, Fin.sum_univ_two]; norm_num
  · simp [butcherRadauIIDirect_two, Fin.sum_univ_two]; norm_num
  · simp [butcherRadauIIDirect_two, Fin.sum_univ_two]; norm_num

/-- **Non-vacuity (D(2))** — the certificate that distinguishes
this tableau from `butcherRadauIIA_two`: the D(s)-variant Radau II
tableau satisfies the order-2 simplifying assumption
`D(2)`, namely `∑ᵢ bᵢ · cᵢ^(k-1) · Aᵢⱼ = (bⱼ/k)·(1 - cⱼ^k)` for
`k ∈ {1, 2}` and `j ∈ {0, 1}`.

Arithmetic checks:
- `(k=1, j=0)`: `(3/4)(1/3) + (1/4)(1) = 1/2 = (3/4)(1 - 1/3)`.
- `(k=1, j=1)`: `(3/4)(0) + (1/4)(0) = 0 = (1/4)(1 - 1)`.
- `(k=2, j=0)`: `(3/4)(1/3)(1/3) + (1/4)(1)(1) = 1/3 = (3/8)(1 - 1/9)`.
- `(k=2, j=1)`: `(3/4)(1/3)(0) + (1/4)(1)(0) = 0 = (1/8)(0)`. -/
example : butcherRadauIIDirect_two.SatisfiesD 2 := by
  intro j k h1 hk
  fin_cases j <;> interval_cases k <;>
    simp [butcherRadauIIDirect_two, Fin.sum_univ_two] <;> norm_num

end OpenMath.Chapter3.Section344
