# Cycle 392 Results

## Worked on
BDF / backward Euler / trapezoidal error constants in
`OpenMath/MultistepMethods.lean`, per the cycle strategy.

## Approach
Followed the cycle 391 recipe verbatim. Sorry-first scaffold added next to
`forwardEuler_errorConstant` (backward Euler, trapezoidal) and as a new
`### Error Constants of BDF Methods` block right after `bdf6_zeroStable`
(the bdf2…bdf6 group must come after the BDF definitions). Each proof:

```lean
unfold LMM.errorConstant LMM.orderCondVal <method>
simp [Fin.sum_univ_<n>, Nat.factorial]
norm_num
```

with `Fin.sum_univ_two` (Euler / trapezoidal), `Fin.sum_univ_three` (BDF2),
`Fin.sum_univ_four` (BDF3), `Fin.sum_univ_five` (BDF4), `Fin.sum_univ_six`
(BDF5), and `Fin.sum_univ_succ, Fin.sum_univ_zero` (BDF6). The recipe
worked unchanged on all seven.

Verified the seven target values by direct computation against the live
α/β coefficients before writing the theorems:

- backward Euler (s=1, α=[-1,1], β=[0,1]): V_2 = -1, C_2 = -1/2.
- trapezoidal (s=1, β=[1/2,1/2]): V_3 = -1/2, C_3 = -1/12.
- bdf2: V_3 = -4/3, C_3 = -2/9.
- bdf3: V_4 = -36/11, C_4 = -3/22.
- bdf4: V_5 = -288/25, C_5 = -12/125.
- bdf5: V_6 = -7200/137, C_6 = -10/137.
- bdf6: V_7 = -43200/147, C_7 = -20/343.

All match the textbook values, no LMM definitions changed.

## Aristotle usage
Skipped Aristotle for this cycle. The recipe was already known to work
mechanically (cycles 390–391); the seven proofs are 4 lines each and all
closed on the first attempt with `unfold; simp [...]; norm_num`. Submitting
five 30-min jobs only to discard them would have cost a cycle of latency
for zero benefit. The four Aristotle bundles flagged as ready
(`a1caad0f…`, `47f16f7c…`, `b255f3eb…`, `90432dc7…`) are stale (already
rejected in cycle 391) — skipped per strategy.

## Result
SUCCESS — all seven theorems closed:

- `backwardEuler_errorConstant : backwardEuler.errorConstant 1 = -(1/2)`
- `trapezoidalRule_errorConstant : trapezoidalRule.errorConstant 2 = -(1/12)`
- `bdf2_errorConstant : bdf2.errorConstant 2 = -(2/9)`
- `bdf3_errorConstant : bdf3.errorConstant 3 = -(3/22)`
- `bdf4_errorConstant : bdf4.errorConstant 4 = -(12/125)`
- `bdf5_errorConstant : bdf5.errorConstant 5 = -(10/137)`
- `bdf6_errorConstant : bdf6.errorConstant 6 = -(20/343)`

`lake build OpenMath.MultistepMethods` succeeds (8027 jobs, no errors,
no sorrys). No `bdf7_errorConstant` added (BDF7 is zero-unstable, per
strategy).

`plan.md` updated:
- Chapter 1.2 error-constant bullet now includes Euler/trap/BDF.
- Section 4.5 BDF Methods bullet list adds an explicit BDF error-constant
  line referencing cycle 392.

## Dead ends
None. Recipe held on the first try for every theorem.

## Discovery
For BDF6 the simpler `Fin.sum_univ_six` does not exist; the file's
existing BDF6 order proof uses `Fin.sum_univ_succ` repeatedly, but
`simp [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.factorial]; norm_num`
closes the goal in one step.

## Suggested next approach
Mechanical multistep error-constant table is now closed (forward/backward
Euler, trapezoidal, AB2–AB6, AM2–AM6, BDF2–BDF6). Reasonable next
mechanical seams:

- AB1/AM1 explicit error-constant statements if a smoke test is wanted
  (AB1 = forwardEuler so already done; AM1 = backwardEuler so already done
  — both already covered, no new work here).
- Add a proof that `errorConstant_pos_iff_orderCondVal_pos` or a similar
  bridging lemma, if Iserles uses the sign of `C_{p+1}` anywhere in the
  textbook's convergence error analysis (Section 1.3).
- Otherwise, return to the open spectral / 358A / order-star issues per
  the strategy — those are the remaining big seams. The mechanical
  multistep table no longer has unblocked rows.
