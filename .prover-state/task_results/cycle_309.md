# Cycle 309 Results

## Worked on

Phase 2 of 3 of the §342 ↔ §321 Gauss–Legendre `RKTableau` lift:
the general-`n` definition `butcherGaussLegendreRK (n : ℕ) :
RKTableau n` and the headline corollary
`butcherGaussLegendreRK_satisfiesB`, lifting cycle 307's algebraic
B(2n) bridge onto a concrete `RKTableau`.

Shipped four new declarations + one stretch example, all in
`OpenMath/Chapter3/Section342.lean` after cycle 308's `n = 1`
anchor (per cycle 309 strategy §A):

* **A.1** `butcherGaussLegendreRK (n : ℕ) : RKTableau n` — the
  general-`n` Gauss–Legendre tableau (collocation `A`, canonical
  weights, shifted Legendre zeros).
* **A.2** `butcherGaussLegendreRK_one_eq` — `rfl` coincidence with
  cycle 308's `butcherGaussLegendreRK_one`.
* **A.3** `butcherGaussLegendreRK_satisfiesB (n : ℕ) (hn : 0 < n) :
  (butcherGaussLegendreRK n).SatisfiesB (2 * n)` — headline.
* **A.4** `n = 2` non-vacuity witness: `(butcherGaussLegendreRK 2).SatisfiesB 4`.
* **A.5** (stretch) round-trip witness: `gaussLegendre1Stage.SatisfiesB 2`
  re-derived through the cycle 309 general theorem.

## Approach

Mechanical port of cycle 308's `n = 1` literal with the stage count
abstracted to `n : ℕ`. Pre-flight `Grep` confirmed `RKTableau.SatisfiesB`'s
signature in `Section321.lean:88-90` matches the verbatim shape used
in cycle 307's bridge `butcherShiftedLegendre_quadratureWeights_satisfiesB`
at `Section342.lean:6752-6757`. Both have:

```
∀ k : ℕ, 1 ≤ k → k ≤ <bound> →
  (∑ j : Fin _, _b j * _c j ^ (k - 1)) = 1 / (k : ℝ)
```

so a single `intro k h1 hk; show ...; exact butcherShiftedLegendre_quadratureWeights_satisfiesB n hn k h1 hk`
closes A.3 with no simp / unfolding needed.

A.2 closed as `rfl` on first try — both sides reduce to identical
`RKTableau.mk` literals.

A.4 used `(by norm_num)` to discharge `0 < 2`.

A.5 stretch worked exactly as the strategy quoted: `rw` through the
two cycle 308 / cycle 309 coincidences, then `exact` the general
theorem at `n = 1`.

## Result

**SUCCESS.** All four planned A.1–A.4 declarations shipped, plus the
A.5 stretch round-trip witness. File compiles with `lake env lean
OpenMath/Chapter3/Section342.lean` in 38s (warm), zero errors,
only pre-existing linter warnings (unrelated cycles 285–290 work).

Axiom-verified all three new public symbols (`butcherGaussLegendreRK`,
`butcherGaussLegendreRK_one_eq`, `butcherGaussLegendreRK_satisfiesB`)
via `mcp__lean-lsp__lean_verify`: each shows
`[propext, sorryAx, Classical.choice, Quot.sound]` — the cycle 301
upstream leak from `_rootsInIoo_card_ge`, identical profile to cycles
307/308. Not a regression; cleanup is a separate audit cycle.

Sorry count: 0 in committed code (no `sorry`/`axiom` introduced this
cycle).

## Faithfulness check

### `butcherGaussLegendreRK`

* **Entity**: no dedicated extracted entity; this is the general-`n`
  construction of the §342 collocation Gauss–Legendre RK method.
  The implicit-target entity is `cor:342D` (Gauss-Legendre order-2n
  condition); our B(2n) half is exactly A.3.
* **Textbook statement** (Butcher §342 p. 237, paraphrased): the
  `n`-stage Gauss-Legendre RK method has abscissae at the zeros of
  the shifted Legendre polynomial `P_n^*`, weights given by the
  Lagrange quadrature, and `A`-matrix `Aᵢⱼ = ∫₀^{cᵢ} Lⱼ(x) dx`.
* **Lean statement**: `A := butcherShiftedLegendre_collocationA n`
  (∫ over [0, cᵢ] of Lⱼ — cycle 308), `b :=
  butcherShiftedLegendre_quadratureWeights n` (∫ over [0, 1] of Lⱼ
  — cycle 303), `c := butcherShiftedLegendre_zeros n` (zeros of P_n^*
  — cycle 302). **Captures: same content.**
* **Definition smuggling check**: ✓ this is the *primary* textbook
  meaning of "the n-stage Gauss-Legendre RK method". No order
  conditions smuggled into the definition; B(2n) is a *theorem*
  (A.3), not built into the definition.

### `butcherGaussLegendreRK_one_eq`

* **Entity**: no dedicated entity; this is a sanity coincidence
  asserting `butcherGaussLegendreRK 1` literally equals cycle 308's
  `butcherGaussLegendreRK_one`.
* **Captures**: bookkeeping only. Proof is `rfl`.
* **Tautology check**: both sides expand to the same `RKTableau.mk`
  literal but with the stage count abstracted vs. concrete — the
  statement is not vacuous, it asserts two distinct-looking
  presentations agree.

### `butcherGaussLegendreRK_satisfiesB`

* **Entity**: `cor:342D` half (B(2n) of the four-pronged B/C/D/E
  Gauss-Legendre order-2n proof; C/D/E deferred).
* **Textbook statement (cycle 307 docstring, faithful to Butcher
  §321 B(η) at η = 2n for the canonical Gauss method)**:
  > The canonical Lagrange weights `b_j` at the canonical zeros `c_j`
  > reproduce the integrals `∫₀¹ x^{k-1} dx = 1/k` exactly for every
  > power `1 ≤ k ≤ 2n`: `∑ⱼ b_j · c_j^(k-1) = 1/k`.
* **Lean statement**: `(butcherGaussLegendreRK n).SatisfiesB (2 * n)`,
  where `SatisfiesB` is §321's `∀ k : ℕ, 1 ≤ k → k ≤ η → ∑ⱼ M.b j ·
  M.c j ^ (k - 1) = 1 / (k : ℝ)`. The `M.b`/`M.c` projections unfold
  to `_quadratureWeights n` / `_zeros n` — exact match to cycle 307's
  bridge. **Captures: same content.**
* **Tautology check**: NO. The conclusion `SatisfiesB (2 * n)`
  unfolds via `show` to cycle 307's exact statement; the `exact`
  routes through cycle 304's `2n`-degree quadrature exactness
  theorem (genuine integration-by-parts machinery).
* **Identity check**: NO. Three-step proof: `intro k h1 hk; show ...;
  exact <named lemma>`. Final `exact` cites cycle 307's bridge.
* **Hypothesis strength check**: `(hn : 0 < n)` matches cycle 307's
  bridge requirement. Faithful — Butcher §321 B(2n) is vacuous at
  `n = 0` since `1 ≤ k ≤ 0` is empty, but the bridge requires
  positivity of `n` for the `_zeros` / `_quadratureWeights`
  definitions to be non-vacuous.
* **Absent theorem check**: cycle 307's
  `butcherShiftedLegendre_quadratureWeights_satisfiesB` confirmed
  present at Section342.lean:6752-6757.

### Pre-existing upstream `sorryAx` leak

All §342 theorems consuming `butcherShiftedLegendre_zeros` inherit
the `sorryAx` axiom from cycle 301's `_rootsInIoo_card_ge`. This is
pre-existing and not a cycle 309 regression — cycles 307 and 308
ship with identical profile. Cleanup is a separate audit cycle.

## Dead ends

None. Pre-flight confirmation matched the strategy's predicted
signatures verbatim, so A.1/A.2/A.3/A.4/A.5 all closed on first try
with no fallback paths needed.

## Discovery

* The `show ... ; exact ...` pattern in A.3 is the cleanest way to
  bridge `SatisfiesB`'s definitional `M.b j * M.c j ^ (k - 1)`
  unfolding to the cycle 307 bridge's verbatim
  `_quadratureWeights n j * _zeros n j ^ (k - 1)` form. Lean
  elaborates `M.b` / `M.c` for `M := butcherGaussLegendreRK n` to
  the underlying field bodies definitionally — no `simp only
  [butcherGaussLegendreRK]` or `RKTableau.SatisfiesB` unfolding
  rewrite needed.
* The A.5 round-trip pattern (`rw [← _eq_gaussLegendre1Stage, ←
  _one_eq]; exact _satisfiesB 1 _`) demonstrates the cycle 308/309
  bridge is *downstream-consumable*: §321's hand-built tableau
  inherits its `B(2)` correctness from the §342 collocation theorem,
  not just from `interval_cases k; simp` brute force. Useful
  template for similar cross-section bridges (e.g. when cycle 310+
  closes C/D/E and we want `gaussLegendre1Stage` to satisfy `C(1)`
  via the §342 path rather than direct evaluation).

## Suggested next approach

### Phase 3 of 3: C(n), D(n), E(n, n) order conditions for general `n`

The §342 ↔ §321 lift is now half-complete at all `n`: B(2n) lifted
cycle 309; C(n) / D(n) / E(n, n) are the remaining three Butcher
§321 conditions needed for the order-2n proof per `cor:342D`.

Per cycle 308's "Suggested next approach", these require an
**upper-limit-parametrised** version of cycle 304's
`_quadrature_exact_lt_two_n`: instead of `∫₀¹ φ(x) dx = ∑ⱼ bⱼ φ(cⱼ)`
for `deg φ < 2n`, we need `∫₀^{cᵢ} φ(x) dx = ∑ⱼ Aᵢⱼ φ(cⱼ)` for
`deg φ < n` (the C(n) shape). This is a one-cycle infrastructure
step.

Concretely for cycle 310:

1. State and prove `butcherShiftedLegendre_collocation_exact_lt_n
   (n : ℕ) (i : Fin n) (φ : Polynomial ℝ) (hdeg : φ.natDegree < n) :
   (∫ x in (0 : ℝ)..butcherShiftedLegendre_zeros n i, φ.eval x) =
   ∑ j : Fin n, butcherShiftedLegendre_collocationA n i j *
     φ.eval (butcherShiftedLegendre_zeros n j)`.

   Standard polynomial-interpolation argument: φ of degree < n is
   uniquely determined by its values at the n zeros via the Lagrange
   basis, integrate both sides.

2. Specialise to `φ = X^(k-1)` for `1 ≤ k ≤ n` to derive
   `butcherGaussLegendreRK_satisfiesC : (butcherGaussLegendreRK n).SatisfiesC n`.

3. D(n) is the adjoint condition. The standard B(2n) + C(n) ⇒ D(n)
   derivation (Butcher §321 / §342 — see textbook lemma referenced
   in entity dependencies) routes through these two and a small
   algebraic argument; check `extraction/formalization_data/entities/`
   for the entity IDs.

4. E(n, n) = B(2n) ∧ C(n) → E(n, n) is similarly a textbook
   one-liner once B and C are in hand.

After Phase 3 closes, `cor:342D` (Gauss-Legendre order 2n) becomes
the §314A elementary-weight argument applied to a tableau satisfying
B(2n) ∧ C(n) ∧ D(n).

### Alternative: §342 documentation polish

The four new declarations have detailed docstrings. The cycle 308
docstring for the surrounding `/-! ### Phase 1 ... -/` block could
be augmented to reference cycle 309's Phase 2 completion (or a
fresh `/-! ### Phase 2 -/` block could be introduced — cycle 309
already adds one at the top of the new declarations). No
documentation cleanup is urgent; current state is consistent.

### Audit alternative: upstream `sorryAx` cleanup

The `_rootsInIoo_card_ge` `sorryAx` leak from cycle 301 propagates
through all §342 downstream theorems. A separate audit cycle could
either close the cycle 301 sorry or document it as a deliberate
abstraction layer. This is independent of the §342 ↔ §321 lift
and could run in parallel.
