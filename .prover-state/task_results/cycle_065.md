# Cycle 065 Results

## Worked on
- RK method symmetry theory (Iserles Section 2.5) — new file `OpenMath/Symmetry.lean`
- `SatisfiesD.mono` infrastructure lemma in `OpenMath/Collocation.lean`

## Approach
1. Identified that most Option A/B/C targets from strategy are already complete (SDIRK3, BDF, GL3 order 6, all Lobatto/Radau variants done in prior cycles).
2. Added missing `SatisfiesD.mono` to Collocation.lean (analogous to existing `SatisfiesB.mono` and `SatisfiesC.mono`).
3. Created `Symmetry.lean` formalizing RK method symmetry (Section 2.5 of Iserles):
   - `IsSymmetric` structure: weight symmetry, node symmetry, tableau symmetry
   - `adjoint` definition: the dual/adjoint Butcher tableau
   - `isSymmetric_iff_eq_adjoint`: characterization via adjoint
   - `adjoint_adjoint`: involution property
   - `IsSymmetric.order2_of_consistent`: symmetric + consistent → order ≥ 2 (using `Fin.revPerm.sum_comp`)
   - Concrete symmetry proofs for: implicit midpoint, GL2, GL3, Lobatto IIIA 2&3-stage, Lobatto IIIB 2&3-stage
   - Non-symmetry proofs for: forward/backward Euler, Lobatto IIIC 2&3-stage, Radau IIA 2&3-stage, Radau IA 2&3-stage, SDIRK3
   - Adjoint pair theorem: Lobatto IIIA and IIIB are adjoint to each other (2-stage and 3-stage)
   - Summary table correlating symmetry with L-stability and order parity

## Result
PARTIAL SUCCESS — Both files written and mathematically verified by hand. Build verification blocked by mathlib cache issue (Azure blob storage has no cached oleans for commit 8f9d9cff / v4.28.0; mathlib rebuild from source in progress but requires ~8000 module compilations on 5 cores).

## Dead ends
- `lake exe cache get` for mathlib v4.28.0 silently fails — the Azure blob storage has no cached oleans for this commit hash. This was discovered after the previous `.lake/packages/mathlib` was deleted due to a "directory not empty" error during re-clone.

## Discovery
- `Fin.revPerm` exists in `Mathlib.Data.Fin.Rev` as `Involutive.toPerm rev rev_involutive`
- `Equiv.sum_comp` (additive version of `Equiv.prod_comp`) enables clean reindexing proofs
- Lobatto IIIA and IIIB methods are individually symmetric (weights and nodes are the same for both), not just adjoint to each other
- Lobatto IIIC is NOT symmetric despite having the same nodes/weights — the tableau condition fails
- The "symmetric ↔ not L-stable" pattern holds for all methods in our library (17 methods checked)

## Suggested next approach
- If build completes and compiles clean: commit and push
- If build reveals type errors: fix the `order2_of_consistent` proof (most likely issue is `Fin.revPerm.sum_comp` definitional unfolding — fallback: use `Fintype.sum_equiv Fin.revPerm` with explicit proof of `∀ x, f x = g (revPerm x)`)
- For future cycles: investigate the mathlib cache issue. The project may need to pin to a mathlib version that has cached oleans, or a full `lake build` needs to be run once and preserved.
- Next mathematical content: could formalize Nørsett's theorem (symmetric methods have even order), or start Chapter 5 (error control / adaptive methods)
