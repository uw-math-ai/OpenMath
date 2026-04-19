# Cycle 130 Results

## Worked on
Theorem 342C equations (342j) and (342k) in `OpenMath/Collocation.lean`:
- **342j**: `G(p) => B(p)` — tree-based order p implies the B quadrature condition
- **342k**: `G(2n) => E(n,n)` — tree-based order 2n implies the E cross-condition
- **342l**: `B(2n) /\ C(n) /\ D(n) => G(2n)` — skeleton only (sorry)

## Approach
1. Added `import OpenMath.OrderConditions` to Collocation.lean
2. Defined `bushyTree k` — root with k-1 leaf children (order k, density k)
3. Proved helper lemmas: `foldr_order_replicate_leaf`, `bushyTree_order`, `foldr_density_replicate_leaf`, `bushyTree_density`, `foldr_ew_replicate_leaf`, `bushyTree_ew`
4. Proved `satisfiesTreeCondition_bushyTree`: tree condition for bushy tree iff B(k)
5. Proved `SatisfiesB_of_hasTreeOrder` (342j): apply `hasTreeOrder` to `bushyTree k`
6. Defined `branchedTree k l` — root with k-1 leaves + one bushy-l child (order k+l, density l*(k+l))
7. Added generalized foldr helpers (`foldr_order_replicate_leaf_init`, `foldr_density_replicate_leaf_init`, `foldr_ew_replicate_leaf_init`)
8. Proved `branchedTree_order`, `branchedTree_density`, `branchedTree_ew`
9. Proved `satisfiesTreeCondition_branchedTree`: tree condition iff E(k,l)
10. Proved `SatisfiesE_of_hasTreeOrder` (342k): apply `hasTreeOrder` to `branchedTree k l`
11. Stated `hasTreeOrder_of_B_C_D` (342l) with sorry

## Result
**SUCCESS** — 342j and 342k fully proved, 342l skeleton stated.

The only remaining sorry is `hasTreeOrder_of_B_C_D` (342l), which requires structural induction on all trees with a nontrivial argument that B+C+D cover all tree conditions.

## Dead ends
- None — the approach from the strategy worked cleanly.

## Discovery
- The `List.foldr` on `replicate` lemmas need generalized versions with arbitrary initial values (not just 0 or 1) when used with `List.foldr_append` for the branched tree proofs.
- Row-sum consistency direction: `IsRowSumConsistent` gives `c i = sum A i j`, so `(hrc i).symm` gives `sum A i j = c i`.
- `Nat.cast_mul` / `push_cast` is needed to reconcile `↑(l * (k+l))` with `↑l * ↑(k+l)` in the density cast.

## Suggested next approach
- **342l** (`B(2n) /\ C(n) /\ D(n) => G(2n)`) is the main remaining target. This requires:
  1. A structural induction on `BTree`
  2. Showing that C(n) handles the "one-child subtree" contributions
  3. Showing that D(n) handles the chain-like structures
  4. B(2n) covers the bushy trees
  This is substantially harder than 342j/k and may need a dedicated sub-lemma architecture.
- Alternatively, consider formalizing other results from Chapter 3 that don't depend on 342l.

## Aristotle
- Submitted 2 jobs (bushy props + branched props), but proved everything manually before results came back.
- Job IDs: 4091c4c3, 6b27b01b (both IN_PROGRESS at cycle end).
