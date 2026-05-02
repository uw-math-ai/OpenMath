# Cycle 663 Results

## Worked on
Butcher §521 Step C.2 in `OpenMath/LMMAsGLM/StabilityCharpoly.lean`:
collapsing the rank-one adjugate contraction selector sums to two named
scalar polynomials.

## Approach
Added the two noncomputable scalar entries
`LMM.toGLM_stabilityCharpolyRowY` and
`LMM.toGLM_stabilityCharpolyRowF`, guarded by the `s = 0` branch. Added
the local helper `fin_q_succ_eq_s_iff` for the unique selected
`q : Fin s` under `0 < s`, then used `Finset.sum_eq_single` to prove
the past-`y` and past-`h*f` selector-collapse lemmas.

Submitted one Aristotle job for the four new sorry-first goals, but the
queue was not needed; the proofs were closed manually. The Lean LSP goal
query timed out on the large import, so the final proof work used small
edits plus `lake env lean` diagnostics.

## Result
SUCCESS. Landed:

- `LMM.toGLM_stabilityCharpolyRowY`
- `LMM.toGLM_stabilityCharpolyRowF`
- `LMM.sum_castAdd_selector_collapse`
- `LMM.sum_natAdd_selector_collapse`
- `LMM.toGLM_stabilityMatrix_charpoly_rankOne_contraction_explicit`

Verification:

- `lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean`
- `lake env lean OpenMath/LMMAsGLM.lean`
- LSP `lean_verify` on
  `LMM.toGLM_stabilityMatrix_charpoly_rankOne_contraction_explicit`
  reported only standard imported axioms and no scan warnings.

## Dead ends
The first helper proof initially used `ext; omega`, but `omega` did not
simplify the final `Fin` value enough. Changing the proof to `apply
Fin.ext`, then `change (q : ℕ) = s - 1`, exposed the Nat equality and
closed immediately.

## Discovery
The selected terms in both scalar-entry definitions unfold definitionally
after `rw [if_pos hlast]` and `rw [dif_neg ...]`; no extra `Fin.cast`
congruence proof was needed.

## Suggested next approach
Proceed to Step C.3: evaluate `toGLM_stabilityCharpolyRowY` and
`toGLM_stabilityCharpolyRowF` against the block-upper-triangular
charmatrix of `toGLM_V_active_lift m`. The reusable route is still a
focused adjugate lemma for `Matrix.fromBlocks A B 0 D`; avoid expanding
the full stability charpoly until those two entries are computed.
