# Cycle 498 Results

## Worked on
Quotient-facing §381/§383 packaging in `OpenMath/ButcherGroup.lean`, plus
the optional §387 trivial-element identity.

## Approach
- `Quotient.lift` over `isRKEquivalentSetoid s`, using the cycle-497
  invariance lemmas (`satisfiesTreeCondition_iff`, `hasTreeOrder_iff`,
  `weights_sum_eq`, `c_sum_eq`) as the well-definedness witnesses.
- For propositional lifts, converted `Iff` to `Eq` via `propext`.
- For the §387 identity, `funext` on `Fin 0` discharges every field
  equality vacuously through `Fin.elim0`. Uniqueness uses
  `ButcherTableau.mk.injEq` to reduce to three componentwise equalities,
  each closed the same way.

## Result
SUCCESS. All scaffold items landed sorry-free in one shot — no Aristotle
batch was needed, since there were no residual sorry's to outsource. New
declarations in `OpenMath/ButcherGroup.lean`:

- `ButcherTableau.QuotEquiv (s : ℕ) : Type`
- `ButcherTableau.QuotEquiv.satisfiesTreeCondition`
- `ButcherTableau.QuotEquiv.hasTreeOrder`
- `ButcherTableau.QuotEquiv.satisfiesTreeCondition_mk` (`@[simp]`, `rfl`)
- `ButcherTableau.QuotEquiv.hasTreeOrder_mk` (`@[simp]`, `rfl`)
- `ButcherTableau.QuotEquiv.weightsSum` (`ℝ`-valued)
- `ButcherTableau.QuotEquiv.cSum` (`ℝ`-valued)
- `ButcherTableau.QuotEquiv.weightsSum_mk` (`@[simp]`, `rfl`)
- `ButcherTableau.QuotEquiv.cSum_mk` (`@[simp]`, `rfl`)
- `ButcherTableau.trivialTableau : ButcherTableau 0`
- `ButcherTableau.trivialTableau_unique`

Build: `lake env lean OpenMath/ButcherGroup.lean` and
`lake build OpenMath.ButcherGroup` both succeed sorry-free.

## Dead ends
None this cycle. The strategy's structural advice (`b` and `c` are
`Fin s → ℝ`, so the value-valued lifts return `ℝ`) was correct against
`OpenMath/RungeKutta.lean:38,40`; no type-mismatch trouble. The five
ready Aristotle bundles were correctly identified by the planner as
targeting already-closed cycle-497 surface — they were skipped, not
incorporated, per the strategy.

## Discovery
- `Fin 0` vacuity is enough to discharge identity-uniqueness:
  `ButcherTableau.mk.injEq` plus `funext i; exact Fin.elim0 i` closes
  all three field-equality goals. This pattern will reappear when the
  §387 inverse and integer-power constructions add structure-preserving
  lemmas — uniqueness of the zero-stage tableau means the identity
  element is forced and any composition with `trivialTableau` should
  reduce to a `Fin 0` reindexing.
- The `Quotient.lift` template is small and uniform: one
  well-definedness witness per lift, `propext` for `Prop`-valued lifts
  and a direct equality for value-valued lifts. This will likely work
  unchanged when §382 composition needs a binary lift via
  `Quotient.lift₂`, **provided** the underlying composition law is
  correctly defined (see next).

## Suggested next approach
The §382 composition seam still needs an issue file before any
implementation cycle reopens it. Cycle 495's task result remains
authoritative: the four-parameter
`ButcherTableau s → ButcherTableau t → ButcherTableau (s + t)`
associativity has a real structural mismatch — left nesting yields
`[γ₁δ₁, γ₁δ₂, γ₂]` while right nesting yields
`[γ₁, γ₂δ₁, γ₂δ₂]`, so the law as written is simply not associative.

Concrete next-cycle proposal:

1. **First** open `.prover-state/issues/butcher_section382_composition.md`
   documenting (a) the cycle-495 dead end, (b) why naïve
   stage-concatenation cannot be associative, and (c) at least two
   candidate fixes — composition modulo a relabeling equivalence on the
   sum, or composition through the `G₁` tree-elementary-weight
   homomorphism (Butcher's preferred algebraic route).
2. **Then** schedule a separate cycle that picks one of those fixes and
   sorry-first-scaffolds the chosen composition law.

The `QuotEquiv` alias landed this cycle is shaped to receive that
composition once it exists: a `QuotEquiv s × QuotEquiv t → QuotEquiv ?`
binary lift, with the well-definedness obligation reusing cycle-497's
invariance lemmas (extended cross-stage-count if needed).

The §387 inverse / integer-power side still needs §382 composition
first, since "inverse" is meaningful only relative to a composition
law. Identity-element side is now in place.
