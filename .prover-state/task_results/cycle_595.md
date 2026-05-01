# Cycle 595 Results

## Worked on
Butcher Section 386 augmented convolution combinator infrastructure in
`OpenMath/ButcherGroup/Section386Aug.lean`.

Landed the disjoint-pair `Finset` combinator API:
- `threeChoice` at line 754.
- `threeChoice_zero` at line 758.
- `mem_threeChoice_iff` at line 761.
- `threeChoice_one` at line 765.

## Approach
Followed the sorry-first workflow for the three primary lemmas, then closed
the concrete `n = 0` and `n = 1` cases with `decide`.  The membership lemma
was closed by simplifying `threeChoice` with
`Finset.disjoint_iff_inter_eq_empty`; Lean Finder confirmed that this is the
available Mathlib theorem for the disjointness/intersection bridge.

## Result
SUCCESS.  The requested three primary facts are sorry-free and do not state
the parametric closed form or any new associativity headline.

Verification:
- `lake build OpenMath.ButcherGroup.Section386Aug` completed successfully.
- `lake env lean OpenMath/ButcherGroup/Section386Aug.lean` completed
  successfully after rebuilding the temporary Mathlib/OpenMath cache.
- `lake build` completed successfully.

## Dead ends
Initial `lake env lean` failed with:
`error: compiled configuration is invalid; run with '-R' to reconfigure`.

The first cache restore attempt then failed because `/tmp/lean4-toolchain`
contained only `bin`, so the cache executable could not link against
Lean's bundled `libc++`, `libc++abi`, `gmp`, and `uv`.  Copying the missing
toolchain `lib` directory into `/tmp/lean4-toolchain` and rerunning
`lake -R exe cache get` restored the cache.

## Discovery
The temporary Lake cache may survive with sources but without build artifacts.
If this recurs, run cache restore with `lake -R exe cache get` and ensure
`/tmp/lean4-toolchain/lib` exists before blaming Lean source changes.

## Suggested next approach
Add the optional `trunkChildren` positional combinator and prove
`trunkChildren_length`.  After that, start the disjoint-pair binomial
identity needed for the eventual parametric closed form for
`BTree.node (List.replicate n (BTree.node [BTree.leaf]))`.
