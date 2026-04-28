# Cycle 520 Results

## Worked on

§384 right-block recursive natAdd reduction in
`OpenMath/ButcherGroup.lean`. The strategy specified Option A: introduce
the recursive helper `ButcherProduct.rightAuxAt` and prove

```
(ButcherProduct t₁ t₂).elementaryWeight τ (Fin.natAdd s i)
  = ButcherProduct.rightAuxAt t₁ t₂ τ i
```

by `BTree.rec` with the same nested motive_1/motive_2 split used for the
cycle 519 upper-left block reduction.

## Approach

1. Read cycle 519 deliverables in `OpenMath/ButcherGroup.lean`,
   specifically `ButcherProduct.elementaryWeight_castAdd`,
   `ButcherTableau.bSeries`, and the powerset identity
   `ButcherProduct.elementaryWeight_natAdd_node_eq_powerset_sum_bSeries`.
2. Defined `ButcherProduct.rightAuxAt` as a `noncomputable def` with the
   leaf clause `1` and the node clause matching the `ψ` recursion
   recorded in `.prover-state/issues/butcher_g1_mul_section384_blocker.md`.
   Used the same `termination_by sizeOf` / `decreasing_by` pattern as
   `ButcherTableau.elementaryWeight`.
3. Exposed two computation lemmas: `rightAuxAt_leaf` (`@[simp]`,
   discharged by `simp [rightAuxAt]`) and `rightAuxAt_node` (discharged
   by `rw [rightAuxAt]`).
4. Proved `ButcherProduct.elementaryWeight_natAdd` by `BTree.rec` with
   motive_1 stating the headline identity on a single tree and motive_2
   stating the corresponding foldr identity on `List BTree`. The
   leaf/nil cases close with `simp`. The node case applies the
   children's foldr-IH after rewriting the LHS via the
   `ButcherTableau.elementaryWeight` reduction at a node and the RHS via
   `rightAuxAt_node`. The cons case splits the inner `Fin (s + t)` sum
   with `Fin.sum_univ_add`, identifies the lower-left block via
   `ButcherProduct.elementaryWeight_castAdd` plus the
   `ButcherTableau.bSeries` definition (`hL`), and identifies the
   lower-right block via the child IH `ih_head k` plus
   `simp [ButcherProduct]` (`hR`).

## Result

SUCCESS — all four sub-deliverables landed and the file is sorry-free.

- `ButcherProduct.rightAuxAt` (noncomputable def, `BTree → Fin t → ℝ`).
- `ButcherProduct.rightAuxAt_leaf` (@[simp]).
- `ButcherProduct.rightAuxAt_node`.
- `ButcherProduct.elementaryWeight_natAdd`.

`OpenMath/ButcherGroup.lean` compiles in ~7s on the cluster and
`lake build` completes in 8073 jobs with only pre-existing warnings.
`grep -c sorry OpenMath/ButcherGroup.lean` is `0`.

## Aristotle batch

Three scaffolds prepared in
`.prover-state/aristotle_scaffolds/cycle_520/`:
- `option_a_rightAuxAt_def.lean`
- `option_a_natAdd_full.lean`
- `option_b_natAdd_node_direct.lean`

A single `submit_file` for `option_a_rightAuxAt_def.lean` returned
HTTP 429 ("too many requests in progress") immediately, consistent with
the cycle 511–519 streak documented in the strategy. Per the strategy's
"do not retry HTTP 429 within the cycle" rule, I did not retry and did
not sleep — I worked through Option A manually instead.

## Dead ends

None during the manual proof. The cycle 519 nested motive pattern
transferred over directly: the only delicate step was the `hsum` split
in the cons case, where the lower-left and lower-right block summations
had to be peeled off independently before the upper-left
`elementaryWeight_castAdd` corollary could collapse the cut side to
`t₁.bSeries head`.

## Discovery

The Option A helper is exactly the structural witness the §384 closed
form will recurse on. Concretely, with `rightAuxAt` available, the next
layer can prove a closed-form identity of the shape

```
∑ i : Fin t, t₂.b i * rightAuxAt t₁ t₂ τ i
  = ∑ (trunk, cuts) of τ, (∏ cut, t₁.bSeries cut) · t₂.bSeries trunk
```

without ever re-deriving the per-stage block decomposition. That is the
piece that
`.prover-state/issues/butcher_g1_mul_section384_blocker.md` flags as
the actual blocker for `IsG1Equiv.product_congr`.

The `decreasing_by` proof for `rightAuxAt` worked verbatim with the
foldr-bound child variable `c`, mirroring `ButcherTableau.elementaryWeight`'s
`t`. `List.sizeOf_lt_of_mem (by assumption) ` plus the
`sizeOf children < sizeOf (BTree.node children)` step is the canonical
shape; no alternative `WellFoundedRecursion` boilerplate was needed.

## Suggested next approach

Two possible cycles ahead:

1. **Closed-form `rightAuxAt`** — define a `BTree → ℝ`-valued
   `(trunk, cuts)` aggregator on rooted-tree splittings (likely indexed
   by `Finset (Fin children.length)` per node, generalising the cycle
   519 powerset identity) and prove the headline identity above. Once
   the closed form lands, `(ButcherProduct t₁ t₂).bSeries τ
   = t₁.bSeries τ + ∑ (trunk, cuts), …` is a one-line rewrite combining
   `bSeries`, `elementaryWeight_castAdd`, and `elementaryWeight_natAdd`.
   This is the genuine §384 convolution.
2. **Sub-decomposition of `rightAuxAt`** — if the full `(trunk, cuts)`
   aggregator is too large for one cycle, an intermediate target is the
   list-level analogue of cycle 519's powerset identity but applied to
   the *kept* side of `rightAuxAt`. Concretely, prove that
   `rightAuxAt t₁ t₂ (BTree.node children) i` expands as
   `∑ S : Finset (Fin children.length), (∏ Sᶜ, t₁.bSeries (children.get p))
   * (∏ S, ∑ j, t₂.A i j * rightAuxAt t₁ t₂ (children.get p) j)` —
   reuse `foldr_mul_add_eq_powerset_sum` on the node clause directly.
   This is the same shape as
   `elementaryWeight_natAdd_node_eq_powerset_sum_bSeries` but with the
   `t₂.elementaryWeight` factors replaced by the structural recursion
   `rightAuxAt`.

Either option is unblocked by today's deliverables.
