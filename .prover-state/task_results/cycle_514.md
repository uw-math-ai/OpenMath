# Cycle 514 Results

## Worked on
§383 G₁ order-p cross-stage equivalence: introduced
`ButcherTableau.IsG1Equiv p q₁ q₂` (agreement of `QuotEquiv.bSeriesHom`
on every rooted tree of order ≤ p) and its basic algebraic and bridge
laws, in `OpenMath/ButcherGroup.lean`.

## Approach
Sorry-first scaffold of the full Tier 1 + Tier 2 block placed at the
end of `OpenMath/ButcherGroup.lean` (after the `IsRKEquivalentExt`
namespace, still inside `namespace ButcherTableau`), then closed each
lemma directly. All proofs are 1–3 lines and went through on the
first compile, so no Aristotle round-trip was needed.

Tier 1 (definition + algebraic laws):
- `IsG1Equiv` definition (heterogeneous `s u : ℕ` stage counts)
- `IsG1Equiv.refl`
- `IsG1Equiv.symm`
- `IsG1Equiv.trans`
- `IsG1Equiv.mono` (monotonicity in the order parameter)
- `IsG1Equiv.zero` (vacuous at order 0 — closed via `BTree.order_pos`
  and `omega`)

Tier 2 (bridges to the existing layers):
- `IsRKEquivalentExt.toG1Equiv` — cross-stage equivalence implies G₁
  equivalence at every order, via
  `congr_fun (IsRKEquivalentExt.bSeriesHom_eq h) τ`.
- `IsG1Equiv.satisfiesTreeCondition_apply` — single-tree bridge to
  `QuotEquiv.satisfiesTreeCondition` via
  `QuotEquiv.satisfiesTreeCondition_iff_bSeries`.
- `IsG1Equiv.hasTreeOrder_iff` — bridge to
  `QuotEquiv.hasTreeOrder p` via the cycle-513
  `IsRKEquivalentExt.hasTreeOrder_iff_forall` private helper, which is
  callable from within the same file (no visibility widening).

## Result
SUCCESS. Eight new declarations landed sorry-free.
`lake env lean OpenMath/ButcherGroup.lean` succeeds (PATH starts with
`/tmp/lake-bin:/tmp/lean4-toolchain/bin`). File grew from 1403 to
1481 lines, well under the 3000-line cap.

Tier 3 (`weightsSum_eq` corollary) was not opened — Tier 1 + Tier 2
are the load-bearing foundation; per the strategy, Tier 3 is optional
and should be deferred if the next-cycle quotient construction is the
natural follow-up.

## Aristotle
No jobs submitted this cycle. All eight Tier 1+2 lemmas were 1–3 line
proofs that landed on the first compile, so an Aristotle round-trip
would have been pure latency with no upside. Cycles 509, 511, 512,
513 all hit immediate HTTP 429 on submission, confirming Aristotle
remains unreliable; reserving the quota for a non-trivial future
cycle is the right call.

## Dead ends
None. The strategy's note that the cycle-513
`hasTreeOrder_iff_forall` helper is `private` was a non-issue — Lean
4's `private` is per-file, and the new code lives in the same file,
so the helper is callable directly without any visibility change.

## Discovery
- The eight Tier 1 + Tier 2 lemmas were essentially mechanical
  wrappers over cycle 511 (`bSeriesHom_eq`), cycle 499
  (`satisfiesTreeCondition_iff_bSeries`), and cycle 513
  (`hasTreeOrder_iff_forall`). The §383 layer was waiting for a
  thin wrapper, not for new mathematical content.
- `BTree.order_pos` (RootedTree.lean:600) is the right citation for
  the order-≥-1 fact; no separate `BTree.one_le_order` lemma is
  needed — `omega` after `have := BTree.order_pos τ` closes it.

## Suggested next approach
The natural cycle-515 headline is the `G₁(p)` quotient itself:
- Define `IsG1Equiv p` as a `Setoid (Σ s, QuotEquiv s)` (use
  `IsG1Equiv.refl`/`symm`/`trans` from this cycle as the witness)
  — note that the heterogeneous stage-count requires a Sigma carrier,
  paralleling the `IsRKEquivalentExt` Sigma packaging.
- Define `G₁` as the quotient of `Σ s, QuotEquiv s` by that setoid.
- Lift `bSeriesHom` (restricted to trees of order ≤ p) and the
  `satisfiesTreeCondition`/`hasTreeOrder` predicates to `G₁(p)` via
  `Quotient.lift`, using the cycle-514 bridges as the well-definedness
  witnesses.

§384 tree-coefficient convolution and §382 full `c`-field
associativity remain deliberately deferred per existing issue files
(`butcher_section384_convolution.md`,
`butcher_section382_composition.md`).
