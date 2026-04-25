# Cycle 416 Results

## Worked on
Landed the AB3 scalar scaffold in a new tracked file
`OpenMath/LMMAB3Convergence.lean`, mirroring the AB2 scalar chain template
from `OpenMath/LMMAB2Convergence.lean`.

## Approach
Followed the cycle 416 strategy's deliberately narrowed scope:

1. Read `OpenMath/LMMAB2Convergence.lean` lines 31–71 (the AB2 iteration,
   boundary `@[simp]` lemmas, single-step reduction, and LTE rewrite).
2. Verified the AB3 method definition in `OpenMath/AdamsMethods.lean`:
   `α = ![0, 0, -1, 1]`, `β = ![5/12, -16/12, 23/12, 0]`.
3. Created `OpenMath/LMMAB3Convergence.lean` with the mechanical edits
   from the strategy:
   - `ab2Iter → ab3Iter` with three starting samples `y₀ y₁ y₂` and
     match arms `0 / 1 / 2 / n + 3`
   - recurrence
     `y_{n+3} = y_{n+2} + h·(23/12·f_{n+2} − 16/12·f_{n+1} + 5/12·f_n)`
   - `Fin.sum_univ_three → Fin.sum_univ_four`
   - `adamsBashforth2 → adamsBashforth3`
   - `2 * h → 3 * h` in the LTE statement, with the additional
     `5/12 · y'(t)` term
4. Verified the file compiles cleanly with
   `lake env lean OpenMath/LMMAB3Convergence.lean` — no errors, no warnings.

## Result
SUCCESS. Six declarations landed, all fully proved with no `sorry`s:
- `LMM.ab3Iter`
- `LMM.ab3Iter_zero` (`@[simp]`)
- `LMM.ab3Iter_one` (`@[simp]`)
- `LMM.ab3Iter_two` (`@[simp]`)
- `LMM.ab3Iter_succ_succ_succ`
- `LMM.ab3_localTruncationError_eq`

Total: ~70 lines. The LTE rewrite closed cleanly with the strategy's
suggested one-liner
`simp [adamsBashforth3, Fin.sum_univ_four, iteratedDeriv_one,
   iteratedDeriv_zero]; ring`.

`plan.md` updated with a new bullet under §1.2 documenting the AB3 scalar
scaffold and noting the convergence theorem itself is not yet landed.

## Dead ends
None. The strategy's mechanical-template approach worked on first try
without diagnostic iteration. No Aristotle batch was needed (and was
explicitly disrecommended for this minimum scope).

## Discovery
The mechanical-template approach the strategy advocates is robust: the
LTE rewrite for both AB2 (cycle 408) and AB3 (this cycle) uses literally
the same proof body modulo the method name and the `Fin.sum_univ_*`
expansion. This suggests AB4/AB5/etc. LTE rewrites can be ground out
identically, with the bottleneck being the subsequent Lipschitz +
residual-bound layers, not the LTE rewrite.

## Suggested next approach
Cycle 417 should add `ab3_one_step_lipschitz` and
`ab3_one_step_error_bound`, mirroring `ab2_one_step_lipschitz` /
`ab2_one_step_error_bound` (`OpenMath/LMMAB2Convergence.lean`, lines
~76–187). The effective Lipschitz constant is `(23 + 16 + 5)/12 · L =
44/12 · L = 11L/3`, and the max-norm should be taken over **three**
errors `max(eₙ, eₙ₊₁, eₙ₊₂)` rather than two, because AB3 has three
function evaluations per step. The recurrence shape becomes
`max(eₙ₊₁, eₙ₊₂, eₙ₊₃) ≤ (1 + h · 11L/3) · max(eₙ, eₙ₊₁, eₙ₊₂) + |τ_n|`.

Cycle 418 should land the local residual bound and global error bound,
which are heavier and where cycle 415 stalled. Aristotle is likely
appropriate for the residual-bound piece (Taylor expansions to order 4
giving an `O(h⁴)` pointwise bound).
