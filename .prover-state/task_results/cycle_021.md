# Cycle 021 Results

## Worked on
`def:381C` — *0-reducible Runge–Kutta method* and *0-reduced method*
(Butcher §380, page 303). Extended `OpenMath/Chapter3/Section381.lean`
with three new declarations (`IsZeroReducibleVia`, `IsZeroReducible`,
`zeroReduced`), one helper (`zeroReducedEmb`), three API unfolding
lemmas (`zeroReduced_{A,b,c}_apply`), and two non-vacuous witness
`example`s on `paddedEuler`.

## Approach
Followed cycle 020's three-namespace layout for §380:
`Section381 → Section312.RKTableau → Section381`. Encoded the 2-block
partition as a Boolean predicate `inP1 : Fin s → Bool`, with
`P₀ = {i | inP1 i = false}` and `P₁ = {i | inP1 i = true}` (cleaner
than `Set` because the witness is `![true, false]` and `decide`
discharges Boolean side conditions).

The 0-reduced method's new index set is
`Fin (Finset.univ.filter (inP1 · = true)).card`, with re-indexing via
`Finset.orderEmbOfFin _ rfl : Fin (#P₁) ↪o Fin s`. Hoisted the
embedding into a named helper `zeroReducedEmb` so the three API
lemmas close by `rfl`. No `Classical.choose` needed (contrast with
`pReduced`'s `A` and `c` fields), so 0-reduction has no
representative-choice ambiguity at all.

Witnesses on `paddedEuler` (which has `b = ![1, 0]`, `A = 0`) use
partition `![true, false]` (so `P₀ = {1}`, `P₁ = {0}`):
`fin_cases i <;> simp_all [paddedEuler]` discharges the
`b 1 = 0` clause; the `A`-clause is trivially `simp [paddedEuler]`.

## Result
SUCCESS.

* `lake env lean OpenMath/Chapter3/Section381.lean` — clean.
* `lake build` — clean (2825 jobs).
* `#print axioms` on all seven new declarations:
  `[propext, Classical.choice, Quot.sound]` only.
* Sorry scanner / tautology scanner: 0 hits across `OpenMath/`.
* `extraction/formalization_data/lean_status.json` row for `def:381C`
  updated to `formalized` with symbol
  `OpenMath.Chapter3.Section312.RKTableau.IsZeroReducible`.
* `plan.md` progress counter bumped `21 / 175 → 22 / 175` and
  `[ ] def:381C` flipped to `[x]`.
* No Aristotle submissions (per strategy: all proofs are `rfl` or
  `fin_cases <;> simp`, which is below the threshold for batched
  Aristotle use; mirrors cycle 020's reasoning).

## Faithfulness check

For each new `def`/`theorem` introduced this cycle:

### `IsZeroReducibleVia` (predicate form of def:381C)
- Entity ID: `def:381C`. Textbook statement (quoted from
  `def_381C.json`):
  > A Runge–Kutta method (A, b, c) is '0-reducible' if the stage
  > index set can be partitioned into two subsets
  > `{1, 2, …, s} = P₀ ∪ P₁` such that `bᵢ = 0` for all `i ∈ P₀` and
  > such that `aᵢⱼ = 0` if `i ∈ P₁` and `j ∈ P₀`.
- Lean statement captures: **same content** (predicate form). The
  Boolean predicate `inP1 : Fin s → Bool` is an equivalent encoding
  of a partition of `Fin s` into two subsets `P₀ ∪ P₁`. The two
  conjuncts match Butcher's two zero conditions verbatim. The
  encoding choice is documented in the file docstring under
  "Faithfulness notes".

### `IsZeroReducible` (existential closure)
- Same entity, existential closure with side condition.
- Lean statement captures: **same content + minimal non-triviality
  strengthening**. Adds `(∃ i, inP1 i = false)` (i.e. `P₀ ≠ ∅`) as a
  side condition to rule out the trivial all-`P₁` partition under
  which every tableau is vacuously 0-reducible. This parallels the
  `ŝ < s` strengthening on `IsPReducible` (cycle 020) and is
  explicitly documented near the definition. Strictly weaker than
  also requiring `P₁ ≠ ∅` (which would exclude the legitimate
  "delete all stages" reduction).

### `zeroReducedEmb` (helper)
- Not a textbook entity. Pure infrastructure: order embedding from
  `Fin (#P₁)` into `Fin s` whose image is exactly `P₁`. Used only to
  re-index the surviving stages.

### `zeroReduced` (the 0-reduced method itself)
- Entity ID: `def:381C` (second sentence). Textbook statement
  (quoted): *"The method formed by deleting all stages indexed by
  members of `P₀` is known as the '0-reduced method'."*
- Lean statement captures: **same content**. The new stage count
  `(Finset.univ.filter (inP1 · = true)).card` equals `|P₁|`, exactly
  Butcher's "delete all stages indexed by `P₀`". The order embedding
  makes each new stage correspond unambiguously to a specific old
  stage in `P₁`. New `A`, `b`, `c` are pointwise restrictions
  through the embedding — no `Classical.choose` ambiguity (contrast
  `pReduced`).

### `zeroReduced_{A,b,c}_apply` (three API lemmas)
- All three are `rfl` unfoldings of the structure projection,
  rewritten through `zeroReducedEmb`. Tautology check: each
  conclusion is an equation between `(M.zeroReduced inP1).{A,b,c}`
  and `M.{A,b,c}` composed with `zeroReducedEmb`, distinct from any
  hypothesis. Identity check: the proofs are unfolding lemmas, not
  vacuous re-exports of a hypothesis. Pass.

### Witness `example`s
- `paddedEuler` is non-trivial (2-stage method with non-zero `b`).
  The witnesses confirm a 0-reducible tableau exists in our
  codebase, satisfying the CLAUDE.md non-vacuity requirement for new
  predicates.

### Hypothesis-strength check
- `IsZeroReducibleVia` uses no hypotheses beyond Butcher's two zero
  conditions.
- `IsZeroReducible` adds the *minimal* non-triviality side
  condition `(∃ i, inP1 i = false)`; documented.
- API lemmas use no hypotheses beyond what `rfl` requires.

### Definition-smuggling check
- The 0-reduced method is *constructed*; it is not a separate
  predicate. There is no characterisation theorem masquerading as a
  definition.

## Dead ends
None. The strategy's recommended approach (named `zeroReducedEmb`
helper) was used directly; the alternative `let emb := ...` inside
the lemma statements was not attempted because the named helper
keeps `rfl` unambiguous.

## Discovery
* `Finset.orderEmbOfFin` lives in `Mathlib.Data.Finset.Sort` (not
  `Mathlib.Order.Fin.Finset` as the strategy speculated). It's
  already in scope through transitive imports of
  `Mathlib.Algebra.BigOperators.Fin` (which Section312 imports).
* The `rfl` proofs for `zeroReduced_{A,b,c}_apply` work directly
  with the named-helper spelling because each structure projection
  unfolds to a literal `M.X (zeroReducedEmb inP1 …)` term — no
  `let` bindings to navigate.
* Cycle 020's `pReduced` paid a cost (representative `Classical.choose`
  with attendant well-definedness lemma `pReduced_A_apply`) for
  encoding partitions with surjective `block`. Cycle 021's
  `zeroReduced` avoids that cost entirely by using `orderEmbOfFin`
  to materialise a canonical *injection* from new indices to old.
  This suggests `pReduced` could be refactored along similar lines
  in a future cycle (using a sorted representative per block) — but
  this is a refactor, not a defect, since `pReduced_A_apply`
  delivers the intended interface.
* The bridge lemma `IsPReducible_of_IsZeroReducible` (suggested as a
  stretch goal) is **not straightforward**: from a 0-reducibility
  partition `inP1` one can build the `PPartition s 2` whose blocks
  are `P₀` and `P₁`, but `IsPReducibleVia` for that partition asks
  for the row sums `Σ_{j ∈ P_J} a_{ij}` to be **constant on each
  block of `i`**, and `def:381C` only provides this for the
  `(P₁, P₀)` cross-block sum (which is identically zero by
  hypothesis). For the other three cross-block sums, no such
  constancy is implied by the 0-reducibility hypotheses alone.
  Concretely: `Σ_{j ∈ P₀} a_{ij}` for `i, i' ∈ P₀` need not agree.
  Conclusion: 0-reducibility does **not** imply P-reducibility under
  Butcher's definitions; the bridge would require additional
  hypotheses (e.g. `c`-block-constancy or row-sum-constancy of `A`
  on `P₀`-rows). Not committed.

## Suggested next approach
Cycle 022: **`def:381E` "irreducible"**. Now that both `def:381C`
(0-reducible) and `def:381D` (P-reducible) are formalised, `def:381E`
is the natural composite:

> A method is *irreducible* if it is neither 0-reducible nor
> P-reducible.

Lean signature (proposed):

```lean
def IsIrreducible {s : ℕ} (M : RKTableau s) : Prop :=
  ¬ M.IsZeroReducible ∧ ¬ M.IsPReducible
```

This unblocks `def:370A` (the algebraic-stability discussion's
implicit irreducibility hypothesis). For a non-vacuous witness, the
1-stage explicit Euler is irreducible (no non-trivial partition of a
1-element index set exists), but the witness will need a small lemma
ruling out `IsZeroReducible` for `s = 1` (the only `inP1 : Fin 1 → Bool`
with non-empty `P₀` is the all-false predicate, and Butcher's
explicit Euler has `b 0 = 1 ≠ 0`).

Alternatively, cycle 023 candidate: `def:381F` *P-equivalent*
(combines `def:381B` and `def:381D`).

Defer indefinitely (blocked on `thm:306A` Taylor's theorem):
`def:381A` "equivalent", `lem:310B`.
