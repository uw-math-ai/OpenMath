# Cycle 395 Results

## Worked on
Monomial converse infrastructure for the linear multistep method order
conditions in `OpenMath/MultistepMethods.lean`.

Added:
- `LMM.hasOrder_of_orderCondVal_vanishing`
- `LMM.hasOrder_iff_orderCondVal_vanishing`
- `LMM.hasOrder_of_truncationOp_vanishing_on_monomials`

Also updated `plan.md` Chapter 1 §1.2 to record the cycle-395 converse,
iff, and truncation-operator sufficient condition.

## Approach
Followed the cycle-395 strategy and first read the live `LMM.HasOrder`
definition. The live structure is not just the positive-degree monomial
conditions: it has

```lean
conditions_hold : ∀ q, q ≤ p → m.orderCondVal q = 0
next_nonzero : m.orderCondVal (p + 1) ≠ 0
```

Therefore the converse theorem needs explicit hypotheses for the zeroth
condition and the next nonzero condition in addition to the positive
monomial vanishing assumptions.

Used the required sorry-first workflow: added the two target declarations
with `sorry`, verified `OpenMath/MultistepMethods.lean` compiled, then
closed the proofs by direct structure construction. Since that landed
quickly, also added the optional truncation-operator-only sufficient
condition, with the zeroth and next conditions expressed via
`truncationOp` at `h = 1`.

## Result
SUCCESS.

`OpenMath/MultistepMethods.lean` now has the monomial converse and iff
packaging for `HasOrder`, plus the direct truncation-operator sufficient
condition on monomials. No new `sorry`s and no heartbeat changes.

Verified with:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/MultistepMethods.lean
```

The command exits `0`. The output contains only pre-existing linter
warnings elsewhere in the file.

## Dead ends
- The optional truncation-operator theorem initially rewrote the zeroth
  monomial identity directly and failed because the displayed term used
  `0 : ℝ` while the instantiated identity displayed `↑0`. Replaced that
  step with an explicitly typed local `hkey`, after which the rewrite
  was stable.

## Discovery
- The live `HasOrder` definition packages both `q = 0` and the failure
  of the `(p+1)`-st condition. Future order-condition converses should
  either use the all-`q ≤ p` form directly or include explicit zeroth
  and next-condition hypotheses.
- `truncationOp_monomial_zero` at `h = 1` is enough to convert
  truncation-operator vanishing/nonvanishing facts back into
  `orderCondVal` facts without division.

## Aristotle activity
No Aristotle batch was submitted this cycle. This was the planner-approved
no-op case: the work was a converse of a closed monomial identity plus
mechanical `HasOrder` structure unfolding, with no isolated algebraic
sub-goal worth a job.

## Suggested next approach
The next small extension would be an all-`q ≤ p` truncation-operator iff
that mirrors the live `HasOrder.conditions_hold` field directly. The
larger Taylor-with-remainder truncation-error route should remain a
separate planned cycle.
