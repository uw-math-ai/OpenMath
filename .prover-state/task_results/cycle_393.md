# Cycle 393 Results

## Worked on
`bdf7_errorConstant` in `OpenMath/MultistepMethods.lean`, plus the optional Adams error-constant sign lemmas in `OpenMath/AdamsMethods.lean`.

## Approach
Rejected Aristotle project `408efb68-d0ad-4458-9138-d86325e985e3` after reading its summary: it created a stub `OpenMath/MultistepMethods.lean` and proved an already-closed `adamsMoulton6_errorConstant` against that stub, so nothing was safe to transplant into the live 2400+ line module.

Did not submit new Aristotle jobs this cycle because there were no live `sorry`s and the new BDF7 theorem was a direct finite-sum arithmetic proof following the existing BDF error-constant recipe.

Verified the BDF7 value against the live coefficients before committing. The planner's closed-form calculation included an extra factor of `k`: the live calculation gives
`LMM.orderCondVal bdf7 8 / 8! = -35/726`, not `-245/726`.

## Result
SUCCESS.

- Added `theorem bdf7_errorConstant : bdf7.errorConstant 7 = -(35 / 726)`.
- Added `adamsBashforth_errorConstant_pos` for AB2–AB6.
- Added `adamsMoulton_errorConstant_neg` for AM2–AM6.
- Updated `plan.md` to include BDF7's error constant and the Adams sign lemmas.

## Dead ends
The initially requested target value `-245/726` failed against the live `bdf7` coefficients. Recomputing from `LMM.orderCondVal` showed the correct live value is `-35/726`, matching the sibling BDF constants via `-1 / ((k+1) * H_k)`.

The requested placement immediately after `bdf6_errorConstant` was not literally possible because `bdf7` is defined immediately after that block. The theorem was placed immediately after the live `bdf7` definition.

## Discovery
For BDF methods in this normalization, the implemented constants follow `C_{k+1} = -1 / ((k+1) * H_k)`. This agrees with existing BDF2–BDF6 values and gives BDF7 `-35/726`.

## Suggested next approach
Continue to avoid the stale stub-based Aristotle bundle. There is no remaining BDF error-constant table gap after BDF7; future work should return to the planner's next non-stale target rather than reopening completed 358A, spectral-bound, or Adams zero-stability issues.
