# Cycle 587 Results

## Worked on

§386 unital associativity in `OpenMath/ButcherGroup/Section386Aug.lean`:
the replicate-subtree lift and the arbitrary-children scaffold.

## Approach

1. Checked the previous Aristotle result
   `7609a42a-7684-4222-8dde-e40f61e6042b`; it matches the planner triage and
   is not transplantable because it fabricated a standalone
   `OpenMath/ButcherGroup.lean` with fake `BTree`, `RawTableau`, and
   `QuotEquiv` declarations.
2. Added the cycle 587 sorry-first scaffold:
   - `mul_assoc_at_node` for arbitrary `children : List BTree` (one active
     §386 `sorry`);
   - `mul_assoc_at_node_replicate` as the replicate-subtree API;
   - `mul_assoc_at_node_two_subtrees` as the `n = 2` corollary;
   - `mul_assoc_at_node_replicate_zero` and
     `mul_assoc_at_node_replicate_one` sanity corollaries.
3. Built five Aristotle payloads under
   `.prover-state/aristotle_scaffolds/cycle_587/` plus a compiled
   counterexample file for the naive closed form.
4. Submitted the requested Aristotle batch:
   - `closed_form_replicate_subtree.lean` accepted as project
     `4449050d-0ce6-4a92-8a2f-9bae4930ecfb`;
   - the other four submissions (`inner_cut_forest_replicate_sum`,
     `mul_assoc_replicate_subtree`, `two_subtrees`, `mul_assoc_node`) returned
     HTTP 429.
5. Slept 30 minutes and checked the accepted Aristotle project once.  It was
   still `QUEUED`, so there was no result to incorporate this cycle.
6. Used Lean to isolate the obstruction to the planner's proposed closed
   form.  The scratch file
   `.prover-state/aristotle_scaffolds/cycle_587/closed_form_counterexample.lean`
   proves that for `τ = BTree.node [BTree.leaf]` the actual convolution has a
   partial-trunk contribution while the naive powerset RHS is zero.

## Result

PARTIAL SUCCESS.  The target file compiles, the planned public APIs now exist,
and the `n = 2` two-subtree corollary is available.  There is exactly one live
`sorry` in tracked `OpenMath` code, at the active §386 scaffold
`mul_assoc_at_node`; the replicate-subtree and two-subtree theorems reduce to
that scaffold.

The naive closed form `bSeriesConvAug_node_replicate` from the strategy was
not added to the main file because it is false for arbitrary `τ`.

## Dead ends

- The binomial proof used for `BTree.leaf` cannot be reused unchanged for
  arbitrary `τ`.  The leaf case works because each child has only two relevant
  cuts: keep the leaf or prune it.  A general subtree also has partial-trunk
  cuts, and those terms survive at the parent node.
- Aristotle did not produce usable proof output this cycle: one project stayed
  queued after the required wait and the remaining submissions hit HTTP 429.

## Discovery

The first failing subtree is already `τ = BTree.node [BTree.leaf]`.
With `α leaf = 1`, all other `α` coefficients zero, and
`β (BTree.node [BTree.node []]) = 1`, all other `β` coefficients zero, Lean
checks:

- actual `bSeriesConvAug α β (BTree.node [τ]) = 1`;
- naive powerset RHS using only `α τ` and kept copies of `τ` is `0`.

The missing term is the partial child cut
`α.toFun BTree.leaf * β.toFun (BTree.node [BTree.node []])`.

## Suggested next approach

Do not try to prove the naive replicate-subtree closed form.  The next proof
should target the active scaffold `mul_assoc_at_node` through a true
composition-of-cuts lemma:

1. State a list-level associativity identity for `BTree.innerCutForest
   children` that keeps each child cut opaque.
2. Reindex by child cut choices, not just by a powerset of fully pruned child
   positions.
3. Use the existing closed forms (`leaf`, `node []`, replicate-leaf) only as
   tests of the general identity.

If a smaller intermediate milestone is wanted, prove the binomial closed form
for children satisfying a two-branch inner-cut predicate; this recovers
`τ = BTree.node []` without pretending it covers arbitrary subtrees.
