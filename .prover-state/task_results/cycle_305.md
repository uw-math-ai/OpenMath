# Cycle 305 Results

## Worked on
- `lem:342B` Phase B.2 (positivity of quadrature weights) **+ Phase B.3
  stretch (uniqueness)**. Both shipped — `lem:342B` is now fully
  formalized in Lean.

## Approach
Executed Butcher's textbook recipe (§342 p. 237) verbatim. The
positivity argument routes through the test polynomial
`φⱼ := (P_n^* /ₘ (X - C cⱼ))²` (the square of the Lagrange factor at
the root `cⱼ`):

**Phase B.2** — `butcherShiftedLegendre_quadratureWeights_pos`:
1. `butcherShiftedLegendre_lagrangeFactor n j := P_n^* /ₘ (X - C cⱼ)`
   (private def).
2. `butcherShiftedLegendre_lagrangeFactorSq n j := (lagrangeFactor n j)^2`
   (Butcher's φⱼ).
3. **Factor identity**: `(X - C cⱼ) · lagrangeFactor n j = P_n^*` via
   `Polynomial.mul_divByMonic_eq_iff_isRoot` (forward) applied to cycle
   302's `butcherShiftedLegendre_zeros_isRoot`.
4. **Degree bound**: `(φⱼ).natDegree = 2(n - 1) < 2n` via
   `Polynomial.natDegree_divByMonic` (giving `n - 1`) + `Polynomial.natDegree_pow`
   (doubling) + `omega` (valid over ℝ as an integral domain).
5. **Vanishing at other zeros**: `φⱼ(cₖ) = 0` for `k ≠ j`. Evaluate the
   factor identity at `cₖ`; LHS is `(cₖ - cⱼ) · lagrangeFactor(cₖ)`; RHS
   is `P_n^*(cₖ) = 0`; `cₖ - cⱼ ≠ 0` by cycle 302's
   `butcherShiftedLegendre_zeros_injective`. So `lagrangeFactor(cₖ) = 0`,
   hence `φⱼ(cₖ) = 0`.
6. **Simple-root multiplicity**:
   `butcherShiftedLegendre_rootMultiplicity_eq_one (n : ℕ) (j : Fin n) :
   rootMultiplicity cⱼ P_n^* = 1`. The lower bound uses
   `Polynomial.rootMultiplicity_eq_zero_iff` + `cⱼ` is a root.
   The upper bound uses `Polynomial.count_roots` + the `Multiset.Nodup`
   property of `P_n^*.roots`, which itself comes from squeezing
   cardinalities: `n ≤ filter.card ≤ toFinset.card ≤ roots.card ≤ n`
   (combining cycle 301's filter cardinality with `Polynomial.card_roots'`),
   then `Multiset.toFinset_card_eq_card_iff_nodup`.
7. **Positivity at own zero**: `φⱼ(cⱼ) > 0` via `sq_pos_of_ne_zero`
   applied to `Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero`
   (since `rootMultiplicity = 1` collapses `(X - C cⱼ)^1` to `(X - C cⱼ)`).
8. **Integral positivity**: `0 < ∫₀¹ φⱼ` via `intervalIntegral.integral_pos`
   — polynomial is continuous, square is non-negative, and the integrand
   is strictly positive at `cⱼ ∈ (0, 1) ⊂ [0, 1]` (cycle 302's
   `_zeros_mem_Ioo` + `Set.Ioo_subset_Icc_self`).
9. **Headline closure**: apply Phase B.1's
   `butcherShiftedLegendre_quadrature_exact_lt_two_n` to φⱼ (degree-bound
   from Step 4). The RHS sum collapses via `Finset.sum_eq_single j`
   (other terms vanish by Step 5). So `bⱼ · φⱼ(cⱼ) = ∫₀¹ φⱼ > 0`.
   With `φⱼ(cⱼ) > 0`, `mul_pos_iff_of_pos_right` extracts `0 < bⱼ`.

**Phase B.3** — `butcherShiftedLegendre_quadratureWeights_unique`:
For any `(b : Fin n → ℝ)` satisfying the `< n`-degree exactness identity
at the canonical zeros, instantiate the hypothesis at each Lagrange
basis polynomial `Lⱼ := Lagrange.basis Finset.univ v j`:
- natDegree `Lⱼ.natDegree = n - 1 < n` via `Lagrange.natDegree_basis`.
- Kronecker delta `Lⱼ(cₖ) = δⱼₖ` via `Lagrange.eval_basis_self` /
  `Lagrange.eval_basis_of_ne` collapses RHS sum to `b j`.
- LHS = `∫₀¹ Lⱼ = quadratureWeights n j` by definition.
- Hence `b j = quadratureWeights n j` for all `j`; `funext` closes.

## Result
**SUCCESS — both theorems shipped, axiom-clean.**

- `butcherShiftedLegendre_quadratureWeights_pos (n : ℕ) (hn : 0 < n)
  (j : Fin n) : 0 < butcherShiftedLegendre_quadratureWeights n j` ✓
- `butcherShiftedLegendre_quadratureWeights_unique (n : ℕ) (hn : 0 < n)
  (b : Fin n → ℝ) (hb : ...) : b = butcherShiftedLegendre_quadratureWeights n` ✓
- File compiles: `lake env lean OpenMath/Chapter3/Section342.lean` exits 0.
- 0 sorries.
- `#print axioms` on both: `[propext, Classical.choice, Quot.sound]` only.
- File now 6724 LOC (+~310 LOC this cycle).

`lem:342B` is therefore **fully formalized** (existence via Phase B.1,
positivity via Phase B.2, uniqueness via Phase B.3). Status flipped
from `partial` to `formalized` in `lean_status.json`; plan.md row flipped
from `[~]` to `[x]`.

## Faithfulness check

### For `butcherShiftedLegendre_quadratureWeights_pos`:
- Entity ID: `lem:342B` (from `formalization_data/entities/lem_342B.json`).
- Textbook statement quote: *"Let `c_1, c_2, …, c_s` denote the zeros of
  `P_s^*`. Then there exist positive numbers `b_1, b_2, …, b_s` such
  that `∫_0^1 φ(x) dx = ∑_{i=1}^s b_i φ(c_i)`, for any polynomial of
  degree less than 2s. The b_i are unique."*
- Lean statement captures: **same content** for the positivity clause
  (`0 < bⱼ` for each `j : Fin n`, where the `bⱼ` are the Lagrange
  weights at the canonical zeros — the unique choice forced by the
  `< n`-degree exactness, as proved separately in Phase B.3).
- Hypothesis strength: `0 < n` matches Butcher's implicit `s ≥ 1` (with
  no `cᵢ`, the statement is vacuous).
- No definition smuggling: the weights are defined as Lagrange-basis
  integrals (cycle 303's `butcherShiftedLegendre_quadratureWeights`),
  which is the canonical primary definition. Positivity is a genuine
  consequence proved here, not smuggled into the definition.
- No tautology: conclusion `0 < bⱼ` is not a hypothesis.
- No identity proof: the proof routes through 9 auxiliary lemmas plus
  Phase B.1's exactness — substantial mathematical work.

### For `butcherShiftedLegendre_quadratureWeights_unique`:
- Entity ID: `lem:342B` (same entity, uniqueness clause).
- Textbook statement quote: *"The b_i are unique."*
- Lean statement captures: **same content** — any family `b : Fin n → ℝ`
  satisfying the `< n`-exactness identity (the weakest sufficient
  condition; the `2n`-extension is not required for uniqueness) at the
  canonical zeros must agree with `butcherShiftedLegendre_quadratureWeights`.
- Hypothesis strength: only `< n`-degree exactness is required (matches
  Butcher's textbook proof — uniqueness follows from the `< n` half
  alone, by Lagrange interpolation argument).
- No definition smuggling, no tautology, no identity proof.

### For private aux `butcherShiftedLegendre_lagrangeFactor` etc.:
- These are Lean-engineering names (private), not textbook concepts.
  They package the polynomial division `P_n^* /ₘ (X - C cⱼ)` for use
  in the positivity proof.
- `butcherShiftedLegendre_rootMultiplicity_eq_one` is a genuine theorem
  (each canonical zero is a simple root) — not a definition.
- `butcherShiftedLegendre_roots_nodup` and `_roots_card_eq` are
  consequences of cycle 301's distinct-roots fact + cycle 273's
  `natDegree = n`. Proved, not assumed.

## Dead ends
None — the strategy's prescribed Mathlib hooks all existed and worked
on first try:
- `Polynomial.natDegree_divByMonic`, `Polynomial.mul_divByMonic_eq_iff_isRoot`,
  `Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero` (in
  `Mathlib.Algebra.Polynomial.Div`).
- `Polynomial.natDegree_pow` (in `Mathlib.Algebra.Polynomial.Degree.Domain`).
- `Multiset.toFinset_card_eq_card_iff_nodup`,
  `Multiset.nodup_iff_count_le_one` (in `Mathlib.Data.Finset.Card` /
  `Mathlib.Data.Multiset.Nodup`).
- `Polynomial.count_roots` (in `Mathlib.Algebra.Polynomial.Roots`).
- `intervalIntegral.integral_pos` (in
  `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`).
- `sq_pos_of_ne_zero`, `mul_pos_iff_of_pos_right` (in `Mathlib.Algebra.Order.Ring`).
- `Lagrange.natDegree_basis`, `Lagrange.eval_basis_self`,
  `Lagrange.eval_basis_of_ne` (in `Mathlib.LinearAlgebra.Lagrange`).

Two minor typos required a fixup pass:
- `(h0 ...) hp_ne` should have been `hp_ne (h0 ...)` (function
  application direction in the `rootMultiplicity_eq_zero_iff` use).
- `Lagrange.eval_basis_of_ne` expects a membership of the *evaluation*
  index `k`, not the basis index `j` (so `Finset.mem_univ k`, not
  `hj_mem`).

Both caught immediately by Lean's diagnostics.

## Discovery
- `Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero` is the
  cleanest tool for "factor out a simple root and evaluate the
  cofactor". The path through `rootMultiplicity = 1` is much shorter
  than a derivative-of-product argument.
- The squeeze `n ≤ filter ≤ toFinset ≤ multiset ≤ natDegree = n`
  collapses to all-equal in one `le_antisymm` block. Combined with
  `Multiset.toFinset_card_eq_card_iff_nodup`, this is the canonical
  recipe for "n distinct roots of a degree-n polynomial ⇒ all simple".
- Phase B.3 needs only the `< n`-exactness half, not the `2n`-exactness.
  The textbook statement implicitly bundles uniqueness with the
  full result, but the proof only consumes the weaker half.

## Suggested next approach
**`lem:342B` is fully closed.** The planner should consider the next
entity in §342 / §343 order:
- `cor:342D` (Gaussian quadrature Runge-Kutta order condition) — the
  immediate downstream consumer of `lem:342B` per the dependency graph.
- `lem:342A` companion-cleanup if any open clauses remain (cycle 301
  reported it closed; verify).
- Alternatively, move to §344 (the existence theorem `thm:344A`
  consuming Gaussian quadrature) or §351 stability entities.

For cycle 306, my recommendation is **`cor:342D`** — it directly
exercises the lem:342B API we've now fully built, and is the natural
arc completion for the Gaussian-quadrature RK methods chapter.
