# Cycle 623 Results

## Worked on

Butcher §512 LMM stability lift Phase D step 2 in
`OpenMath/LMMAsGLM.lean`: multi-step y-iterate companion bridge on top
of the already-iterated `V^n q` input.

## Approach

Followed the planner's Phase D step 2 scaffold after reading
`.prover-state/strategy.md`.

1. Added `toGLM_V_iter_step_y_shift`, the non-last past-`y` row bridge
   applied to `(fun v => fun k' => ∑ l, m.toGLM.V k' l * v l)^[n] q`.
   It closed by the one-line delegation
   `exact toGLM_V_step_y_of_hf_zero_shift m _ k hk1`; no extra
   reindexing was needed.
2. Added `toGLM_V_iter_step_y_last`, the last-row companion update at
   the same iterated input. The proof first introduced
   `hhf : ∀ k, toGLM_hf_half (V^n q) k = 0` and closed each slot with
   `exact toGLM_V_iter_natAdd_eq_zero_of_le m q n hn k`, then delegated
   to `toGLM_V_step_y_of_hf_zero_last m _ hhf k hk1`.

## Result

SUCCESS. Both Phase D step 2 deliverables landed sorry-free:

* `toGLM_V_iter_step_y_shift`
* `toGLM_V_iter_step_y_last`

`toGLM_hf_half (V^n q) k = 0` reduced definitionally against
`toGLM_V_iter_natAdd_eq_zero_of_le`; no `show`, `change`, or `unfold`
step was required.

Verified with:

* `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAsGLM.lean`
  exited 0.
* `grep -c sorry OpenMath/LMMAsGLM.lean` printed `0`.

## Dead ends

None. The sorry-first scaffold compiled immediately, and both proofs
closed using the planned step-1 bridge lemmas.

## Discovery

The anonymous iterate form still composes cleanly with the cycle 622
projection definitions. Lean accepts the Phase B corollary directly as a
proof of the `toGLM_hf_half` slot, confirming that the `Fin.natAdd`
projection shape is definitionally aligned.

## Suggested next approach

Phase D step 3 should package the y-half iterate as the LMM companion
state on `Fin s → ℂ`, probably by proving a forward-step rewrite for
`toGLM_y_half ((Vop)^[n+1] q) k` from the two split lemmas and then
matching it to `tupleSucc` / the companion update. After coercing the
real y-half slots to complex coefficients, use
`uniformly_bounded_tupleSucc_iterates` to obtain the spectral bound
needed for `LMM.toGLM_isStable`. Phase E can then combine the existing
consistency theorem with stability for `toGLM_isConvergent`.
