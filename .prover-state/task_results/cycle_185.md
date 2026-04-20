# Cycle 185 Results

## Worked on
- Aristotle triage for bundles `b7678a80-23f8-4369-9fdb-eeafe6be1ec1` and `653f6857-f09f-419f-8022-e6fb727b096a`
- Theorem 301A rooted-tree infrastructure in `OpenMath/RootedTree.lean`
- Narrow downstream bag-based consumer lemmas in `OpenMath/OrderConditions.lean`

## Approach
- Inspected both Aristotle result directories first and checked whether they contained a tiny reusable helper worth transplanting.
- Audited the current rooted-tree API boundary: `childrenBag` already existed, `order_node_perm` and `density_node_perm` were already in place, and `symmetry` was still list-scan based with no permutation/bag-facing theorem.
- Proved a fold-over-`dedup` characterization of `symmetryScan`, then used it to prove permutation invariance for node symmetry.
- Lifted node invariants to a bag-first API by quotient-lifting from `List` to `Multiset` for `order`, `density`, `symmetry`, `beta`, and `alpha`.
- Added `childrenBag` equality corollaries so downstream code can use unordered child multiplicities directly.
- In `OrderConditions.lean`, proved that `elementaryWeight` and `satisfiesTreeCondition` for nodes depend only on `childrenBag`.

## Result
- SUCCESS
- Aristotle bundles were checked and skipped. Both were stale Legendre/Collocation replacement projects with broad file transplants and stub-style scaffolding, not small in-repo-compatible helpers for current mainline rooted-tree work.
- Added rooted-tree bag API:
  - `symmetry_node_perm`
  - `orderBag`, `densityBag`, `symmetryBag`, `betaBag`, `alphaBag`
  - `order_eq_of_childrenBag_eq`
  - `density_eq_of_childrenBag_eq`
  - `symmetry_eq_of_childrenBag_eq`
  - `beta_eq_of_childrenBag_eq`
  - `alpha_eq_of_childrenBag_eq`
- `symmetry` was shown permutation-invariant for node child lists, and then exposed through `childrenBag`.
- Downstream code now consumes the unordered interface through:
  - `elementaryWeight_node_perm`
  - `elementaryWeight_eq_of_childrenBag_eq`
  - `satisfiesTreeCondition_eq_of_childrenBag_eq`

## Dead ends
- Lean could not derive a usable `LawfulBEq`/`DecidableEq` stack automatically for this nested recursive inductive. I first tried to lean on derived equality infrastructure, but that blocked the `contains`/`dedup` proof path for `symmetryScan`.
- Resolved that by writing an explicit recursive `BEq` plus `LawfulBEq`, and using a noncomputable classical `DecidableEq` instance only for proof-side `dedup`/quotient arguments.

## Discovery
- The existing `symmetryScan` already computes an order-independent quantity; the real missing step was proving that it matches a fold over `remaining.dedup` with child multiplicity factors.
- Quotient-lifting node invariants from `List` to `Multiset` gives a clean bag-first API without replacing the recursive `List` representation.
- `lake env lean OpenMath/RootedTree.lean` alone was not enough to refresh downstream imports for a separate scratch `#check`; rebuilding `OpenMath.RootedTree` refreshed the import artifact cleanly.

## Suggested next approach
- Use the new `childrenBag`-facing lemmas to eliminate remaining order-sensitive statements in the rooted-tree/order-condition pipeline.
- If further rooted-tree invariants are added, define them bag-first by quotient lift immediately instead of adding more list-only public lemmas.
- A later cleanup cycle could remove a few pre-existing `simp` warnings in `OrderConditions.lean`, but that was not necessary for this representational blocker.

## Verification
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/RootedTree.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build OpenMath.RootedTree`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build`
