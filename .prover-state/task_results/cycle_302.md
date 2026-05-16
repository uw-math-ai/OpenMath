# Cycle 302 Results

## Worked on

Phase A.1 of `lem:342B` (Gaussian quadrature exactness, Butcher §342
p. 237). Infrastructure for the multi-cycle decomposition outlined in
cycle 302 strategy §F: canonical indexed-family enumeration of the
zeros of `P_n^*` consumed by Phases A.2–A.5.

Cycle 301 health verified per strategy §E steps 1–2:
* HEAD = `4d07773` (cycle 301), 6108 lines, 0 sorrys.
* Tautology-pattern grep: zero real matches in `Section342.lean` /
  `Section342DistinctRootsHelpers.lean`. The two `obtain ⟨..⟩ :=
  h_integrand_nonzero` hits flagged by the supervisor's scanner are
  destructurings, not vacuous closers — confirming the cycle 301
  score = -1 was a phantom (per
  `tautology_scanner_false_positives.md`).

## Approach

Appended five new declarations to `OpenMath/Chapter3/Section342.lean`
between cycle 301's `butcherShiftedLegendre_n_distinct_real_zeros`
and the trailing `end` of the namespace, plus one `example`
non-vacuity anchor at `n = 1`. The new block adds 92 LOC (file
6108 → 6200), within the planner's 50–80 LOC budget tolerance.

Key design choice: rather than the strategy's suggested
`Classical.choose` indirection, I built `butcherShiftedLegendre_zeros`
directly on the concrete finset `butcherShiftedLegendre_rootsInIoo n`
(already defined and shipped in cycle 301 as the witness for
`butcherShiftedLegendre_n_distinct_real_zeros`'s existential). This
avoids a layer of opacity (the underlying finset is now nameable, not
just `Classical.choose _`), making downstream rewrites and the `n = 1`
anchor proof simpler.

New symbols (all in namespace `OpenMath.Chapter3.Section342`):

1. **`butcherShiftedLegendre_rootsInIoo_card_eq (n : ℕ) :
   (butcherShiftedLegendre_rootsInIoo n).card = n`** — pre-existing
   card upper / lower bounds composed via `le_antisymm`. Helper for
   the `orderEmbOfFin` constructor.

2. **`butcherShiftedLegendre_zeros (n : ℕ) : Fin n → ℝ`** —
   `noncomputable def`. The strictly increasing enumeration via
   `Finset.orderEmbOfFin`.

3. **`butcherShiftedLegendre_zeros_mem_Ioo (n : ℕ) (i : Fin n) :
   butcherShiftedLegendre_zeros n i ∈ Set.Ioo (0 : ℝ) 1`** — direct
   composition of `Finset.orderEmbOfFin_mem` and
   `butcherShiftedLegendre_rootsInIoo_subset`.

4. **`butcherShiftedLegendre_zeros_isRoot (n : ℕ) (i : Fin n) :
   (butcherShiftedLegendre n).eval (butcherShiftedLegendre_zeros n i)
   = 0`** — direct composition of `Finset.orderEmbOfFin_mem` and
   `butcherShiftedLegendre_rootsInIoo_are_roots`.

5. **`butcherShiftedLegendre_zeros_injective (n : ℕ) :
   Function.Injective (butcherShiftedLegendre_zeros n)`** — via
   `OrderEmbedding.injective` (inherited from the underlying
   `Function.Embedding`).

Plus an anonymous `example` proving
`butcherShiftedLegendre_zeros 1 ⟨0, _⟩ = 1/2`. The proof uses
`Finset.card_eq_one` to destructure the root finset as a singleton
`{a}`, then membership of both `1/2` and the enumeration's value
forces `a = 1/2`.

## Result

**SUCCESS.**

* `lake build OpenMath.Chapter3.Section342` completes with no errors.
* `#print axioms` on all five new symbols (incl. the helper card_eq
  lemma) returns `[propext, Classical.choice, Quot.sound]` only —
  axiom-clean.
* Sorry count in `Section342.lean` remains 0.
* All five new symbols compile in a single warm rebuild pass.

## Faithfulness check

* **`butcherShiftedLegendre_rootsInIoo_card_eq`**:
  - Entity ID: not a textbook entity — internal Lean engineering helper.
  - Mathematical content: the upper bound (342g upper, cycle 294) and
    lower bound (342g lower, cycle 301) anti-symmetric composition.
  - Captures: same content as the conjunction of its two factors.

* **`butcherShiftedLegendre_zeros`** (`def`):
  - Entity ID: Lean-engineering name, not a textbook concept.
    Butcher §342 p. 237 introduces the zeros informally as
    `c₁, c₂, …, cₛ` but does not give them as an indexed family.
  - Lean realisation: canonical strictly-increasing enumeration via
    `Finset.orderEmbOfFin` on the concrete root finset.
  - Captures: faithful realisation. Documented in the docstring that
    this is engineering, not faithfulness deviation.

* **`butcherShiftedLegendre_zeros_mem_Ioo`** (`lemma`):
  - Mathematical content: clause of (342g) restated for the indexed
    family.
  - Textbook statement (from `lem_342A.json`): "the n zeros of
    P_n^* are real, distinct, and contained in the open interval
    (0,1)" — `_mem_Ioo` captures the open-interval clause via the
    enumeration.
  - Captures: same content.

* **`butcherShiftedLegendre_zeros_isRoot`** (`lemma`):
  - Mathematical content: a tautological consequence of the
    enumeration's construction from the root finset.
  - Captures: real work (composes membership + the `_are_roots`
    spec), not a vacuous re-export.

* **`butcherShiftedLegendre_zeros_injective`** (`lemma`):
  - Mathematical content: the (342g) clause "distinct" restated as
    `Function.Injective` for the indexed family.
  - Captures: same content (distinctness ↔ injectivity for indexed
    families).

**Tautology check**: no theorem's conclusion appears verbatim as a
hypothesis. The four spec lemmas have no hypotheses (just `(n : ℕ)`
and `(i : Fin n)`), and their conclusions are non-trivial properties
of the new `def`.

**Identity check**: no proof is bare `exact h` or `:= h`. The two
membership specs compose two named lemmas; the injectivity spec
extracts a field from a constructed `OrderEmbedding`. The `n = 1`
anchor uses `Finset.card_eq_one` + `Finset.mem_singleton`
destructuring — genuine work, not vacuous.

**Hypothesis-strength check**: all four spec lemmas are unconditional
in `n : ℕ` and `i : Fin n`. The textbook (342g) likewise quantifies
over all `n ≥ 0`. The `n = 0` edge case is handled vacuously by
`Fin 0` being the empty type.

**Definition smuggling check**: `butcherShiftedLegendre_zeros` does
NOT define the zeros as "the algebraic conditions characterising
them" then claim the characterisation theorem is proved. The
definition is a canonical-choice construction from cycle 301's
existential (via the concrete finset); the textbook-content claims
about the zeros (membership in `(0,1)`, being roots, injectivity)
are SEPARATE lemmas whose proofs trace back to (342g).

## Dead ends

None this cycle — the construction was direct and mechanical, as the
strategy anticipated. Two minor design notes:

1. **`Classical.choose` vs concrete finset**: the planner's suggested
   `Classical.choose` route would have worked but adds an extra
   indirection. Using `butcherShiftedLegendre_rootsInIoo` directly
   gives the same definitional behaviour with a more readable
   signature (the underlying finset is nameable rather than hidden
   behind `Classical.choose _`).

2. **`n = 1` anchor strategy**: `rfl` on `orderEmbOfFin` does NOT
   reduce — `orderEmbOfFin` is opaque enough that direct unfolding
   fails. Used the singleton-uniqueness route per the planner's
   fallback: `Finset.card_eq_one` gives `{a}`, both the enumeration's
   value and `1/2` are in this singleton via `Finset.mem_singleton`,
   so they're equal.

## Discovery

* **`Finset.orderEmbOfFin` is the right Mathlib hook**, not the
  fallback `Finset.equivFin`. The order-embedding API gives strict
  monotonicity (hence injectivity) for free as `.injective` on the
  underlying `Function.Embedding`.

* **The membership spec is named `Finset.orderEmbOfFin_mem`** — no
  Mathlib churn relative to what the planner anticipated.

* **`butcherShiftedLegendre_rootsInIoo` was already concrete enough**
  to bypass `Classical.choose`. Future phase work (especially the
  Lagrange weights in Phase A.2) can similarly define quadrature
  weights as `Finset` sums over `butcherShiftedLegendre_rootsInIoo`
  rather than over `Fin n` indices — choose whichever indexing makes
  the proof goal cleanest for the specific lemma.

## Suggested next approach

**Cycle 303 — Phase A.2 of `lem:342B`** (per strategy §F).

Define `butcherShiftedLegendre_quadratureWeights (n : ℕ) : Fin n → ℝ`
via Lagrange interpolation:
```
bⱼ := ∫₀¹ Lⱼ(x) dx
where Lⱼ(x) = ∏_{k ≠ j} (x - cₖ) / (cⱼ - cₖ).
```

Prove exactness on polynomials of degree `< n`: for any `φ` with
`deg φ < n`, the Lagrange interpolant of `φ` at the `n` nodes equals
`φ` (basic interpolation lemma), so `∫₀¹ φ = ∑ bⱼ φ(cⱼ)`.

Mathlib hooks to verify at cycle start:
* `Lagrange.basis` or `Polynomial.lagrange_basis` for the `Lⱼ`.
* `Polynomial.interpolate_eq_of_degree_lt` (or similar) for
  exactness on `deg φ < n`.
* `intervalIntegral` for `∫₀¹ Lⱼ`.

Phase A.2 estimated scope: ~100–150 LOC, single cycle, Aristotle NOT
needed (mechanical interpolation reasoning).

The `n = 2` non-vacuity stretch from cycle 302 strategy §B can be
shipped alongside Phase A.2 if time permits: the explicit
Gauss–Legendre 2-point nodes `(3 ± √3)/6` are nameable via cycle 294's
`butcherShiftedLegendre_two_roots`. Strict-monotone ordering
`(3 − √3)/6 < (3 + √3)/6` is `nlinarith [Real.sqrt_pos.mpr …]`.
