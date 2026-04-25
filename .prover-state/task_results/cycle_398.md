# Cycle 398 Results

## Worked on
Task A from the cycle 398 strategy: the translated leading-coefficient
identity `LMM.truncationOp_polyShiftDegSucc_eq_leading_of_HasOrder` in
`OpenMath/LMMTruncationOp.lean`.

## Approach
Followed the cycle 397 template that closed
`truncationOp_polyShift_eq_zero_of_HasOrder` (lines 288–303 of the live
file). The recipe:

1. Apply `truncationOp_translation h t` to convert the operator at
   evaluation point `t` on `fun u => f (u - t)` into the operator at
   evaluation point `0` on `fun u => f ((u + t) - t) = f u`.
2. Apply `truncationOp_polyDegSucc_eq_leading_of_HasOrder` to the
   unshifted polynomial form.
3. Close with `simpa [add_sub_cancel_right]`.

The proof is 8 lines and structurally identical to the vanishing
analogue, with the final reference swapped from the vanishing theorem to
the leading-coefficient theorem.

## Result
SUCCESS.

- `OpenMath/LMMTruncationOp.lean` compiles clean (305 → 327 lines).
- `OpenMath/MultistepMethods.lean` compiles clean.
- `lake build` succeeds.
- `lean_verify` on `LMM.truncationOp_polyShiftDegSucc_eq_leading_of_HasOrder`
  reports only standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
  and no `sorry`.
- `plan.md` updated under §1.2 truncation-operator bullets with the new
  theorem tagged cycle 398.

## Aristotle
- Triaged the two pre-existing bundles
  (`bc18023b-b07b-4657-b5b0-3fd4bc607bb3`,
   `34e5b2e1-92c9-4b35-a55d-cad496496973`) per the strategy: both target a
  closed lemma (`bdf7_cayley_image_root`, closed in cycle 379), both
  rewrite the file to `import Mathlib`, and one introduces a fresh
  `sorry`. Rejected; not transplanted.
- Submitted a single fire-and-forget diagnostic batch:
  `.prover-state/aristotle_scaffolds/cycle_398/task_a_diag.lean` —
  project id `d418653c-871c-4f88-9f6c-33477d37ad7f`. Asks Aristotle for
  an *independent* proof of Task A that does not just compose
  `truncationOp_translation` with `truncationOp_polyDegSucc_eq_leading_of_HasOrder`.
  The live theorem is already closed; this job is purely a cross-check
  and is not awaited within this cycle.
- Not submitting Task B per strategy ("Skip Task B if it would just
  restate Task A"): the wrapper would be `a ⟨p+1, …⟩` instead of
  `a (Fin.last (p+1))`, which is a notational shuffle.

## Dead ends
None this cycle. The recipe template lifted directly.

## Discovery
Task A required no new helper. The combination of
`truncationOp_translation` and `truncationOp_polyDegSucc_eq_leading_of_HasOrder`
is enough — and the leading-coefficient version transfers across the
shift just as cleanly as the vanishing version did in cycle 397.

This confirms the cycle 397 split was structured correctly: every
"polynomial in `(u - t)` at evaluation point `t`" theorem reduces to the
matching polynomial-at-origin theorem via the translation identity, with
no further Taylor or smoothness machinery needed.

## Suggested next approach
The polynomial side of the truncation operator is now packaged for both
vanishing (`truncationOp_polyShift_eq_zero_of_HasOrder`) and leading
coefficient (`truncationOp_polyShiftDegSucc_eq_leading_of_HasOrder`).
The textbook local truncation error formula `τ(t, h)` is the next
natural target, but per the strategy this cycle was polynomial-only.

The next cycle should bridge to smooth solutions:

1. Introduce a single `taylorWithinEval` (or `iteratedDeriv`) hypothesis
   for a `ContDiff ℝ (p+1) y` test function.
2. Use the Taylor-with-remainder identity to write `y` as a polynomial
   of degree `≤ p` in `(u - t)` plus a remainder term of order
   `(u - t)^(p+1)`.
3. Apply `truncationOp_polyShift_eq_zero_of_HasOrder` to the polynomial
   piece and `truncationOp_polyShiftDegSucc_eq_leading_of_HasOrder`
   directly to the leading `(u - t)^(p+1) · (...)` term.
4. Bound the residual remainder.

The polynomial-only seam is now stable enough to interface with this
Taylor bridge without needing further preparatory polynomial lemmas.

If next cycle wants to stay polynomial-only one more pass, the only
remaining low-hanging item is a notation wrapper that takes the leading
coefficient via a degree index rather than `Fin.last`. The strategy
already tagged this as low-value, so I would skip it.

## Files touched
- `OpenMath/LMMTruncationOp.lean` (added Task A theorem, +22 lines)
- `plan.md` (added cycle 398 sub-bullet under §1.2 truncation operator)
- `.prover-state/aristotle_scaffolds/cycle_398/task_a_diag.lean` (new
  scratch scaffold for the fire-and-forget Aristotle diagnostic)
