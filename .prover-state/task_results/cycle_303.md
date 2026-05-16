# Cycle 303 Results

## Worked on

Phase A.2 of `lem:342B` (Gaussian quadrature exactness degree, Butcher
§342 p. 237). Two new declarations in `OpenMath/Chapter3/Section342.lean`:

* **D1** — `butcherShiftedLegendre_quadratureWeights (n : ℕ) (j : Fin n) : ℝ`
  defines Butcher's `bⱼ` as the integral over `[0,1]` of the Lagrange
  basis polynomial `Lⱼ` at the canonical zero `cⱼ = butcherShiftedLegendre_zeros n j`.
* **D2** — `butcherShiftedLegendre_quadrature_exact_lt_n (n : ℕ) (φ : Polynomial ℝ) (hdeg : φ.natDegree < n) : ∫₀¹ φ.eval x dx = ∑ⱼ bⱼ · φ(cⱼ)` —
  exactness of the quadrature on polynomials of degree strictly less than `n`.
* **D3** (non-vacuity anchor) — `butcherShiftedLegendre_quadratureWeights 1 ⟨0,_⟩ = 1`
  via `Lagrange.basis_singleton`.

Added import `Mathlib.LinearAlgebra.Lagrange`. File now 6288 LOC; cycle
303 added 88 LOC.

## Approach

Strategy doc's "Lagrange API path" worked first try. The Mathlib hooks
that fired:

| Concept | Mathlib name | Note |
|---|---|---|
| Lagrange basis on `Finset ι`, `v : ι → F` | `Lagrange.basis Finset.univ v j` | works with `Field ℝ` and `Fin n` index |
| Interpolation identity for `deg < card` | `Lagrange.eq_interpolate hv.injOn hdeg'` | `hv.injOn : Set.InjOn v ↑Finset.univ` lifted from cycle 302's `butcherShiftedLegendre_zeros_injective` |
| Interpolant as basis sum | `Lagrange.interpolate_apply : interpolate s v r = ∑ i ∈ s, C (r i) * basis s v i` | this is the bridge that turns the abstract `interpolate` into a concrete sum |
| Push `eval x` through finite sum | `Polynomial.eval_finset_sum` via `simp_rw` | |
| Swap integral / finite sum | `intervalIntegral.integral_finset_sum` (needs per-summand `IntervalIntegrable`) | |
| Pull constant factor out of integral | `intervalIntegral.integral_const_mul` | |
| Integrability of `C (eval (v j) φ) * basis _ _ j` | `(continuous_const.mul (Polynomial.continuous _)).intervalIntegrable` | |

The degree cast was the only mildly fiddly bit: `Lagrange.eq_interpolate`
wants `φ.degree < (s.card : WithBot ℕ)`, and `φ.degree = ⊥` when `φ = 0`,
so the `rcases eq_or_ne φ 0` split: the `φ = 0` case discharges via
`WithBot.bot_lt_coe _` (no need for `n > 0`), the nonzero case via
`Polynomial.degree_eq_natDegree hφ` + `exact_mod_cast hdeg`.

## Result

**SUCCESS** — D1, D2, D3 axiom-clean (`[propext, Classical.choice, Quot.sound]`
only), full `Section342.lean` compiles in ~1m on the NVMe toolchain, 0
sorries. Health-check audit at cycle start passed (HEAD = `d511f55`,
file compiled, sorry-free, cycle 302's `butcherShiftedLegendre_zeros`
axiom-clean).

## Faithfulness check

* **D1: `butcherShiftedLegendre_quadratureWeights`**
  Entity ID: `lem:342B` (Butcher §342 p. 237).
  > "there exist positive numbers b₁, b₂, ..., bₛ such that
  > ∫₀¹ φ(x) dx = ∑ᵢ bᵢ φ(cᵢ)"
  Lean statement captures: **the canonical definition** of `bⱼ` as
  `∫₀¹ Lⱼ(x) dx`. This is **not** definition smuggling — Butcher's
  proof text opens with "Choose `bᵢ` so that (342h) holds for any `φ`
  of degree less than `s`. Because the `cᵢ` are distinct the choice
  of the `bᵢ` is unique." The closed-form characterisation of that
  unique choice is `bⱼ = ∫₀¹ Lⱼ` (since for `φ = Lⱼ` the RHS of (342h)
  reduces to `bⱼ`). The positivity claim is a separate consequence
  proved in Phase B by substituting `φ := (Pₛ*/(X − cⱼ))²` into the
  `2s − 1`-degree extension — `D1` itself does not assert positivity.

* **D2: `butcherShiftedLegendre_quadrature_exact_lt_n`**
  Entity ID: `lem:342B` (continued).
  > "∫₀¹ φ(x) dx = ∑ᵢ bᵢ φ(cᵢ), for any polynomial of degree less than 2s"
  Lean statement captures: **weaker** — exactness only on `natDegree < n`
  (Butcher's "less than `s`" preliminary step), not the full `2s`-degree
  exactness. **Justification for divergence**: this is Phase A.2 of a
  multi-cycle decomposition. Phase B (`2n`-degree exactness, positivity,
  uniqueness) requires the (342a) orthogonality of `Pₛ*` against all
  lower-degree polynomials, composed with the polynomial-division
  argument `φ = Pₛ* · Q + R` with `deg Q, deg R < n`. The `lean_status.json`
  row reflects `partial`, not `formalized`, and the `notes` field
  enumerates the three Phase B remainders explicitly.

* **D3 (anchor): `b₁ = 1` at `n = 1`**
  Non-vacuity anchor only, not a textbook-named entity. The Lagrange
  basis on a singleton is the constant polynomial `1` (`Lagrange.basis_singleton`),
  so `b₁ = ∫₀¹ 1 dx = 1`. Cross-checks that D1 and D2 collapse to
  `∫₀¹ φ(x) dx = φ(1/2)` for constant `φ` at `n = 1` (the midpoint
  rule).

* **Tautology / Identity / Hypothesis-strength checks**: D2's hypothesis
  `hdeg : φ.natDegree < n` is exactly the textbook hypothesis (Butcher's
  "degree less than `s`"), so no strengthening. D2's conclusion does
  not appear as a hypothesis. The proof is **not** a single `exact h` —
  it goes through `Lagrange.eq_interpolate`, `Lagrange.interpolate_apply`,
  `simp_rw [Polynomial.eval_finset_sum, ...]`, `intervalIntegral.integral_finset_sum`,
  and `intervalIntegral.integral_const_mul`, so D2 is doing real
  mathematical work (encoding the textbook recipe).

## Dead ends

None this cycle. The strategy's Phase A.2 plan executed cleanly:

* The "Mathlib hooks to verify EARLY" audit (per strategy) returned
  `Lagrange.basis` (yes, on `Field ℝ` + `Fin n` index), `Lagrange.interpolate`,
  `Lagrange.eq_interpolate`, `Lagrange.interpolate_apply` — all four
  primary names exist in Mathlib (`Mathlib.LinearAlgebra.Lagrange`)
  with the signatures the strategy anticipated.
* The first probe proof template (in `/tmp/test_lagrange2.lean`)
  compiled before integration, so the in-file insert succeeded on
  first attempt with no in-place debugging.
* Backup B (direct construction via `∏ k ≠ j, (X − cₖ)/(cⱼ − cₖ)`) was
  unneeded.

The only minor false start: my initial degree-cast tactic
`exact WithBot.bot_lt_coe _` works directly without needing
`hn_pos : 0 < n` — the `n = 0` case is vacuous (`hdeg : φ.natDegree < 0`
is `False`), but the `degree_zero` branch of the case split closes by
`⊥ < ↑n` for any `n` (including `n = 0` where `↑0 = (0 : WithBot ℕ) > ⊥`).

## Discovery

* **Mathlib's Lagrange API is stable and ergonomic for our use case.**
  `Lagrange.interpolate_apply` (interpolant = `∑ i ∈ s, C (r i) * basis s v i`)
  is the right hook for bridging `Lagrange.interpolate` (abstract `→ₗ[F]`)
  into a concrete sum-of-basis-polynomials decomposition that's amenable
  to integral-pushing. No name churn observed.
* **`Field ℝ` instance is sufficient** — `Lagrange` requires `Field F`,
  and ℝ trivially qualifies. No need for a custom adapter.
* **`Function.Injective.injOn` does the lift cleanly** — given cycle
  302's `Function.Injective (butcherShiftedLegendre_zeros n)`, `.injOn`
  produces the `Set.InjOn v ↑(Finset.univ : Finset (Fin n))` that
  `Lagrange.eq_interpolate` and friends consume.
* **The `φ = 0` edge case is the only non-trivial cast bookkeeping** —
  `Polynomial.degree 0 = ⊥`, so `Polynomial.degree_eq_natDegree` doesn't
  apply unconditionally. The `rcases eq_or_ne φ 0` pattern handles it
  in two lines.
* **Aristotle was not used this cycle** — Lagrange/integration was
  immediate, no batch needed. Consistent with strategy's "Aristotle
  queue empty" state assessment.

## Suggested next approach

**Phase B of `lem:342B`** — three deliverables in priority order:

1. **`2n`-degree exactness extension** (the headline of `lem:342B`).
   Textbook recipe: write `φ ∈ ℝ[X]` with `φ.natDegree < 2n` as
   `φ = Pₛ* · Q + R` with `Q.natDegree < n`, `R.natDegree < n`. Then:
   * `∫₀¹ Pₛ*(x) Q(x) dx = 0` by cycle 292's `butcherShiftedLegendre_orthogonal_to_lower_degree`
     (note this lemma takes `m` and `q` with `q.natDegree < m`; substitute
     `m := n`, `q := Q`, returns `∫ Pₛ* · Q = 0`).
   * `∫₀¹ R(x) dx = ∑ⱼ bⱼ R(cⱼ)` by cycle 303's
     `butcherShiftedLegendre_quadrature_exact_lt_n` (Phase A.2).
   * `∑ⱼ bⱼ R(cⱼ) = ∑ⱼ bⱼ φ(cⱼ)` because `Pₛ*(cⱼ) = 0` so
     `φ(cⱼ) = Pₛ*(cⱼ) · Q(cⱼ) + R(cⱼ) = R(cⱼ)`. The `Pₛ*(cⱼ) = 0`
     step uses cycle 302's `butcherShiftedLegendre_zeros_isRoot`.

   Mathlib hook for the polynomial division: `Polynomial.modByMonic` +
   `Polynomial.divByMonic` (`φ = Pₛ* * (φ /ₘ Pₛ*) + (φ %ₘ Pₛ*)` for
   monic divisor). `Pₛ*` is not monic — its leading coefficient is some
   non-trivial expression. Either (a) normalise to a monic associate
   before dividing, or (b) use the general `Polynomial.div_add_mod`
   for `EuclideanDomain (Polynomial ℝ)`, or (c) hand-roll the
   division for the degree-bound argument we actually need.

   Estimated 200–300 LOC. One-cycle target, possibly two.

2. **Positivity of weights** (`0 < bⱼ`). Butcher's recipe:
   substitute `φ := (Pₛ*/(X − cⱼ))²` into the `2n − 1`-degree exactness
   (so we need Phase B.1 first). LHS is the integral of a non-negative
   polynomial that's strictly positive somewhere → `> 0`. RHS collapses
   to `bⱼ · φ(cⱼ)` because `φ(cₖ) = 0` for `k ≠ j` (the factor
   `(X − cₖ)` in `Pₛ*/(X − cⱼ)` vanishes at `cₖ`), and `φ(cⱼ) > 0`
   (it's a non-zero square). So `bⱼ = LHS / φ(cⱼ) > 0`.

   Hook: `Polynomial.div_X_sub_C` (or `divByMonic` with the monic
   `X - C cⱼ`). 100–150 LOC.

3. **Uniqueness of weights**. Two quadrature rules `b, b'` exact on
   degree `< n` polynomials agree on the Lagrange basis polynomials
   `Lⱼ` (since `Lⱼ(cₖ) = δⱼₖ`), so `bⱼ = b'ⱼ` for each `j`. ~50 LOC.

A reasonable cycle 304 scope is Phase B.1 only; cycle 305 picks up
B.2 + B.3.

**Optional cycle 304 sub-deliverable**: prove `butcherShiftedLegendre_quadratureWeights`
sums to `1` (i.e. `∑ⱼ bⱼ = 1`, the consistency condition for RK
quadrature) by applying D2 to `φ = 1`. ~15 LOC. Small additional
non-vacuity witness independent of Phase B.

**LOC budget reality**: §342 file is now 6288 LOC. Approaching the
upper end of comfortable single-file size; consider extracting Phase B
deliverables to a sibling file `OpenMath/Chapter3/Section342Quadrature.lean`
mirroring cycle 281's `Section342NormSqHelpers.lean` extraction pattern
if Phase B grows past ~300 LOC.
