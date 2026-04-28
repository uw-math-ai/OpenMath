# Cycle 532 Results

## Worked on
Butcher §384 right-block convolution in `OpenMath/ButcherGroup.lean`. Landed
the unified kept-children pass-through theorem
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_eq` and its
bSeries-form corollary `ButcherProduct.bSeries_natAdd_node_trunk_kept_eq`,
fusing the cycle 529 kept-leaf and cycle 531 kept-node branches into a
single statement that case-splits each kept root child via an inline
`match` on `BTree`.

## Approach
- Followed the planner's preferred presentation: inline `match` on
  `BTree` for the per-child kept-factor (mirroring the pattern already
  used by `bWeighted_rightAuxAtCoef_node_two_level` and
  `bSeries_natAdd_node_two_level_eq_rightAuxAtCoef`), instead of a private
  `keptFactor` helper. This kept the new lemmas self-contained.
- Proof skeleton for Task 1: `rw
  [bWeighted_rightAuxAtCoef_node_trunk_recursion, Finset.powerset_univ]`,
  drilled in with `Finset.sum_congr rfl` / `congr 1` until the goal was
  the per-child kept factor, then `generalize children.get p = c` and
  `cases c with | leaf => ... | node gc => ...`. Leaf branch closed by
  `simp [rightAuxAtCoef_leaf]`; node branch by
  `Finset.sum_congr rfl` over `j` followed by
  `rw [rightAuxAtCoef_node_eq_powerset_sum]`.
- Task 2 closed in two `rw`s: bridge through
  `bSeries_natAdd_eq_rightAuxAtCoef`, then specialize Task 1 at
  `coef := t₁.bSeries`. The inline `match` aligned syntactically without
  any extra coercion.

## Result
SUCCESS. Both theorems compile cleanly via
`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
OpenMath/ButcherGroup.lean`. Zero `sorry` / `admit` remain in the file.

`plan.md` was updated in both §384 tracking paragraphs (the chapter
ledger near line 482 and the `## Current Target` paragraph near line
969) to record the cycle 532 theorem names.

## Aristotle protocol
The Task 1 proof closed directly on the first attempt using the same
`generalize` + `cases` skeleton as
`rightAuxAtCoef_node_two_level_eq_powerset_sum` (cycle 526). With no
sorry remaining after the initial draft, no Aristotle submission was
useful for this cycle. The planner's explicit fallback ("If the first
submit is 429, proceed manually without further Aristotle attempts this
cycle") covers the spirit here: every recent cycle (504, 509, 511, 512,
513, 515, 516, 517, 519, 521, 523, 529, 531) hit HTTP 429 immediately,
and a redundant submission for an already-closed goal would not have
freed any compute.

## Dead ends
None. The first proof attempt closed; the only minor uncertainty was
whether `congr 1` would auto-close the cut-side product equality after
the outer `Finset.sum_congr rfl`. It does, because both sides have
syntactically identical `(∏ p ∈ S, coef (children.get p))` cut factors,
so `congr 1` reduces to a single goal on the differing stage sum.

## Discovery
- The unified kept-children pass-through is *strictly easier* than the
  cycle 531 kept-node version: the cycle 531 proof had to explicitly
  rewrite each kept-side `coef (children.get p)` to
  `coef (BTree.node (gc p))` via `hChild p` (forcing the bullet split
  after `congr 1`), whereas the unified theorem leaves the cut-side
  `coef (children.get p)` literal and only generalizes inside the kept
  product.
- The proof structure matches `rightAuxAtCoef_node_two_level_eq_powerset_sum`
  almost exactly — both theorems case-split on each per-position child
  inside a powerset product. The only differences are the b-weight
  factor and the swap between `S` (cuts) and `Sᶜ` (keeps).
- Inline `match` on `BTree` inside a finset product elaborates cleanly
  in this context without any motive-annotation hassle.

## Suggested next approach
With the unified kept-children pass-through landed at both the
coefficient-parametric and bSeries levels, the next concrete seam is to
push *one structural layer deeper* on the kept-node grandchildren so
that the `rightAuxAtCoef t₂ coef (gc.get q) k` calls remaining inside
the `match`-`node` branch are themselves expanded by another round of
the same kept-children pattern. Two complementary directions:

1. **Trunk depth induction.** Define a depth-indexed family of
   trunk-pass-through theorems and induct on the trunk's structural
   depth. The unified cycle 532 lemma is the depth-1 base; the depth-2
   case folds each kept-node grandchild's recursive auxiliary through
   the same kept-children pass-through applied to `gc.get q`.
2. **Drive toward the honest `(trunk, cuts)` closed form.** Use the
   unified pass-through as the inductive step inside a `BTree.rec`
   (with explicit `motive_2` over the children-list mutual case, as in
   cycles 497/519/524). This is the direction that ultimately unlocks
   `QuotEquiv.bSeriesHom_product` per
   `.prover-state/issues/butcher_section384_convolution.md`.

Direction (1) is the smaller, lower-risk seam for cycle 533; (2) is the
endgame target it eventually fuses into.
