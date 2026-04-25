# Cycle 390 Results

## Worked on
Per the cycle-390 strategy: introduce `LMM.errorConstant` and prove explicit
leading error constants for the first four Adams methods plus a forward Euler
smoke test.

## Approach
1. Added `LMM.errorConstant (m : LMM s) (p : ℕ) : ℝ := m.orderCondVal (p+1) /
   (p+1)!` to `OpenMath/MultistepMethods.lean`, immediately under
   `HasOrder.isConsistent`, inside the existing `namespace LMM` block.
2. Added `forwardEuler_errorConstant : forwardEuler.errorConstant 1 = 1/2`
   in `OpenMath/MultistepMethods.lean` next to the other forward-Euler order
   theorems.
3. Added four Adams error-constant theorems in `OpenMath/AdamsMethods.lean`
   under a new `## Error constants` section, between the order theorems and
   the zero-stability theorems:
   - `adamsBashforth2_errorConstant : adamsBashforth2.errorConstant 2 = 5/12`
   - `adamsMoulton2_errorConstant   : adamsMoulton2.errorConstant 3 = -(1/24)`
   - `adamsBashforth3_errorConstant : adamsBashforth3.errorConstant 3 = 3/8`
   - `adamsMoulton3_errorConstant   : adamsMoulton3.errorConstant 4 = -(19/720)`

Each closed via the strategy's standard pattern:
```
unfold LMM.errorConstant LMM.orderCondVal <method>
simp [Fin.sum_univ_three / Fin.sum_univ_four / Fin.sum_univ_two, Nat.factorial]
norm_num
```
For the forward-Euler smoke test the trailing `norm_num` was unnecessary
(`simp` closed the goal); leaving it produced a "no goals" error, which I
removed.

## Result
SUCCESS.

- `LMM.errorConstant` defined.
- All five new theorems compile clean (no `sorry`).
- `lake env lean OpenMath/MultistepMethods.lean` compiles clean (only
  pre-existing linter warnings, no errors).
- `lake env lean OpenMath/AdamsMethods.lean` compiles clean.
- `lake build OpenMath.MultistepMethods` succeeds (8027 jobs).
- `plan.md` §1.2 updated with a single new bullet citing the new
  `LMM.errorConstant` API and the four numeric constants plus the forward
  Euler smoke test.

## Aristotle bundles
- The cycle-390 strategy noted one COMPLETE bundle from cycle 389
  (`3d933e59-5698-4072-9274-1f604cdf13be`) and explicitly marked it
  "triaged-and-closed" because cycle 389 already rejected it as a stub of
  `OpenMath/MultistepMethods.lean`. Did **not** re-attempt incorporation,
  per the strategy's instruction.
- Did **not** submit a new Aristotle batch this cycle: the four Adams
  error-constant theorems and the forward Euler smoke test all closed
  manually on the first attempt with the strategy's prescribed
  `unfold ; simp ; norm_num` pattern, leaving zero `sorry`s for Aristotle
  to dispatch. Submitting a no-sorry bundle would just burn a queue slot.
  This is a deliberate choice consistent with the cycle's definition of
  done — no live `sorry`s remained anywhere by Step 2's end.

## Dead ends
- Initial attempt at `forwardEuler_errorConstant` included a trailing
  `norm_num`. With `simp [Fin.sum_univ_two, Nat.factorial]` the goal closes
  fully, so the extra tactic produced a "No goals to be solved" error.
  Resolved by dropping `norm_num` for that one lemma; the four Adams
  versions need it because the rational arithmetic on the AB/AM β
  coefficients does not reduce purely under `simp`.

## Discovery
- `Fin.sum_univ_*` plus `Nat.factorial` plus `norm_num` is the cleanest way
  to evaluate `orderCondVal (p+1)` symbolically for these tableaux. This is
  the same pattern used for the existing AB/AM `HasOrder` proofs, just one
  index higher.
- The Iserles error-constant table (AB2 = 5/12, AM2 = −1/24, AB3 = 3/8,
  AM3 = −19/720) matches the formula `C_{p+1} = orderCondVal(p+1) / (p+1)!`
  exactly with the existing `LMM.orderCondVal` sign convention. No sign
  fixup or factorial-off-by-one workaround was needed, so the issue file
  `cycle_390_adams_error_constant_mismatch.md` is not required.
- Verified by hand before stating each theorem:
  - AB2: V_3 = 7 − 9/2 = 5/2; C_3 = 5/12.
  - AM2: V_4 = 15 − 16 = −1; C_4 = −1/24.
  - AB3: V_4 = 65 − 56 = 9; C_4 = 9/24 = 3/8.
  - AM3: V_5 = 211 − 5140/24 = −19/6; C_5 = (−19/6)/120 = −19/720.
  - FE:  V_2 = 1; C_2 = 1/2.

## Suggested next approach
- The next planner cycle could extend `errorConstant` lemmas to
  AB4/AM4/AB5/AM5/AB6/AM6 mechanically (same proof skeleton, just larger
  `Fin.sum_univ_*`); these are pure computational lemmas and would not
  bring in the §1.3 quantitative-convergence textbook gap that has blocked
  recent cycles.
- An alternative is a single helper
  `errorConstant_eq_div (m : LMM s) (p : ℕ) :
     m.errorConstant p = m.orderCondVal (p+1) / (p+1)!`
  to make user-facing rewriting easier; right now `errorConstant` is
  definitionally that quotient, but a named lemma would let downstream
  proofs `rw` instead of `unfold`. Low priority.
- The §1.3/§2.2 quantitative `O(h^p)` global-error theorem and the §3.5.10
  Theorem 359D restatement remain blocked on textbook references, per
  cycles 388/389. The new `errorConstant` API is a small structural step
  that supports either of those theorems if the references appear later.
