# Issue: Butcher §512 — LMM-side `toGLM_isStable` stability lift

## Blocker

The LMM → GLM embedding `LMM.toGLM` carries a `(2*s) × (2*s)` block-structured
`V` matrix. Showing `m.toGLM.IsStable` from `m.IsZeroStable` is the substantive
content of cycle 618's deliverable #3. Cycle 618 closed the §512 definition and
the RK-side sanity check (`ButcherTableau.toGLM_isConvergent`) but did **not**
land the LMM-side stability lift. This issue records exactly what is needed.

## Context

`OpenMath/LMMAsGLM.lean` contains `LMM.toGLM` (lines 56–80) with the block
structure described in the file's docstring:

* y-slots `0 … s-1`: rows `0 … s-2` are y-shift (`V[k, k+1] = 1`),
  row `s-1` is the LMM update row
  (`V[s-1, l] = -m.α (Fin.castSucc l)` for `l < s`,
  `V[s-1, s+l] = m.β (Fin.castSucc l)` for `l < s`).
* h·f-slots `s … 2s-1`: rows `s … 2s-2` are h·f-shift
  (`V[s+k, s+k+1] = 1`, others zero), row `2s-1` is identically zero.

`GeneralLinearMethod.IsStable` (in `OpenMath/GeneralLinearMethod.lean:149`) is
the elementary `Function.iterate`-based predicate: there exists `M ≥ 0` such
that for every `n` and every input `q` with `|q k| ≤ 1`, every coordinate of
`((mulVec V)^[n] q)` is bounded by `M`.

`m.HasStableRecurrence` and the spectral bound
`uniformly_bounded_tupleSucc_iterates`
(`OpenMath/DahlquistEquivalence.lean:380`) operate over `ℂ` on the `Fin s`
y-recurrence companion operator, not on the `Fin (2 * s) → ℝ` GLM iterate.

## What was tried

Cycle 618 stopped at the §512 definition + RK sanity check (the strategy's
explicit "minimum acceptable" closure). The four-phase decomposition
suggested in the strategy was **not** scaffolded with sorry's because:

1. `LMMAsGLM.lean` is a tracked file already used by downstream theorems
   (RK / GLM stability arguments will eventually consume `toGLM_isStable`).
   Inserting a sorry-bearing scaffold in this file violates the project rule
   against live `sorry`s in tracked files outside the active proof target.
2. The four phases each require nontrivial structural work:
   * Phase 1 (bound on first `s` iterates) needs an explicit row-bound
     lemma `|V_iter q k| ≤ C^n · M_max` that the existing GLM file does not
     supply.
   * Phase 2 (h·f slots zero after `n ≥ s` iterates) needs a structural
     induction on V's block decomposition. The cleanest formulation is
     a separate predicate `HfSlotsZeroFrom` indexed by `n` and a bottom-up
     induction. This is roughly 40–80 lines.
   * Phase 3 (y-slot bound from zero-stability) requires bridging
     `Fin (2*s) → ℝ` (the GLM iterate domain) to `Fin s → ℂ` (the
     companion operator domain) and converting the y-coordinate of
     `V^n q` into the LMM characteristic recurrence. The reindexing alone
     is several lemmas.
   * Phase 4 needs Phase 1 for `n < s` and Phase 2/3 for `n ≥ s`, plus
     the ℝ → ℂ norm coercion in the IsStable witness.

The combined budget is roughly 200–300 lines of proof, well beyond a single
cycle when the structural V-row lemmas have to be developed from scratch.

## Possible solutions

1. **Multi-cycle plan** (recommended). Split the work as:
   * Cycle A: structural V-row lemmas
     (`toGLM_V_castAdd_shift`, `toGLM_V_castAdd_last`,
     `toGLM_V_natAdd_shift`, `toGLM_V_natAdd_last_zero`) as `@[simp]`
     normal forms in `LMMAsGLM.lean`. This mirrors the existing
     `toGLM_U_castAdd` / `toGLM_U_natAdd` pattern (lines 87–99).
   * Cycle B: Phase 2 — `toGLM_V_iter_eq_zero_on_hf_slots`. Bottom-up
     induction on `n` and `k`. No spectral input.
   * Cycle C: Phase 1 — combinatorial row-bound for the first `s`
     iterates.
   * Cycle D: Phase 3 — the y-slot reindexing and the call into
     `stableRecurrence_of_zeroStable` /
     `uniformly_bounded_tupleSucc_iterates`.
   * Cycle E: Phase 4 — combine, then close `toGLM_isStable` and
     `toGLM_isConvergent` (the latter being a one-liner).

2. **Single-cycle attempt with a clear scratch file**. Develop the four
   phases in `.prover-state/scratch/section512_lmm_stability_lift.lean`,
   then move them into `LMMAsGLM.lean` once each is closed. This avoids
   the live-sorry rule but requires a follow-up cycle for the move.

## What changed in cycle 618

* Added `GeneralLinearMethod.IsConvergent` (§512 definition) in
  `OpenMath/GeneralLinearMethod.lean`.
* Added `ButcherTableau.toGLM_isConvergent` in `OpenMath/RKAsGLM.lean`.
* `OpenMath/LMMAsGLM.lean` is unchanged; the LMM-side `toGLM_isStable` /
  `toGLM_isConvergent` lift remains open.
