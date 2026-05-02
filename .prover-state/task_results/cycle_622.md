# Cycle 622 Results

## Worked on

Butcher §512 LMM stability lift Phase D step 1 in
`OpenMath/LMMAsGLM.lean`: y-half / past-h·f-half projections, plus the
one-step companion bridge for the LMM-as-GLM `V`-block.

## Approach

Followed the planner sequence.

1. Added `toGLM_y_half` and `toGLM_hf_half` projections — pure shape
   `def`s extracting the past-`y` and past-`h·f` halves of a
   `Fin (2*s)`-indexed input vector.
2. Stated the one-step bridge in two pieces (the planner explicitly
   permitted splitting the `if`-form because the `else` branch's
   `(k : ℕ) + 1 < s` proof obligation does not propagate into the
   term):
   * `toGLM_V_step_y_of_hf_zero_shift`: non-last past-`y` row.
     Closed with `toGLM_V_castAdd_shift_apply` then
     `Finset.sum_eq_single` at the column
     `Fin.cast (Nat.two_mul s).symm (Fin.castAdd s ⟨(k:ℕ)+1, _⟩)`.
     The output collapses to `toGLM_y_half q ⟨(k:ℕ)+1, _⟩` by `rfl`.
     The `hhf` hypothesis is unused in this branch by design.
   * `toGLM_V_step_y_of_hf_zero_last`: last past-`y` row.
     Reindexed `Fin (2*s)` to `Fin (s+s)` via the cycle 621 / cycle 619
     `rfl + Fin.sum_congr' + Fin.sum_univ_add` pattern, then
     `simp_rw` with `toGLM_V_castAdd_last_castAdd_apply` and
     `toGLM_V_castAdd_last_natAdd_apply`. The past-`h·f` half is zero
     termwise via `hhf`; the past-`y` half matches the target by
     `rfl`.

## Result

SUCCESS. Both deliverables landed sorry-free:

* `toGLM_y_half`, `toGLM_hf_half` (definitions)
* `toGLM_V_step_y_of_hf_zero_shift`
* `toGLM_V_step_y_of_hf_zero_last`

Sorry count: 0 (verified by `grep sorry OpenMath/LMMAsGLM.lean`).

Verified with:

* `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAsGLM.lean`
  exited 0.

## Dead ends

First attempt at a single `if`-form theorem failed because the proof
obligation `(k : ℕ) + 1 < s` in the `else` branch is unconditional in
the theorem statement and cannot be discharged by `omega` from
`k.isLt` alone. The planner anticipated this and the split form went
through cleanly.

The first reindex draft used a non-`rfl` `have` lifting `l` to
`Fin.cast (Nat.two_mul s).symm l`, which `rw` could not match. The
fix was the cycle 621 pattern: an `rfl` step that wraps each `l` in
`Fin.cast (Nat.two_mul s).symm (Fin.cast (Nat.two_mul s) l)`, then
`Fin.sum_congr'` over the wrapped form.

## Discovery

The two-theorem split is more ergonomic than the single `if`-form
when the `else` branch produces a `Fin s` value whose bound depends
on the negated `if`-condition. For Phase D step 2 (multi-step
y-iterate bridge) the split form will compose better: each iterate
case-splits on whether the iterate index has reached `s − 1`.

The `hhf` hypothesis is genuinely needed only in the last-row
branch. The shift branch keeps the past-`h·f` half untouched (the
shift row picks out a single past-`y` column), so dropping `hhf`
from the shift theorem mirrors the mathematical content.

## Suggested next approach

Phase D step 2: multi-step y-iterate bridge. Iterate
`toGLM_V_step_y_of_hf_zero_shift` / `…_last` over `n ≥ s` against
the structural Phase B invariant
`toGLM_V_iter_natAdd_eq_zero_of_le` (which guarantees the
past-`h·f` half stays zero past iteration `s`). The intended
shape is a recursion on `n - s` that propagates `hhf` via Phase B.
Once that lands, Phase D step 3 lifts the bound from ℝ to ℂ via
`Vℂ` coercion and feeds the LMM zero-stability hypothesis through
the spectral bound on the LMM companion matrix to close
`toGLM_isStable`. Phase E combines those to close
`toGLM_isConvergent`.
