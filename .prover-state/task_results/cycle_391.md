# Cycle 391 Results

## Worked on
Extended `LMM.errorConstant` coverage in `OpenMath/AdamsMethods.lean` from the
cycle-390 AB2/AM2/AB3/AM3 table to the remaining mechanical Adams methods:
AB4, AM4, AB5, AM5, AB6, and AM6.

## Approach
Followed the sorry-first / Aristotle-first workflow:

1. Added the six theorem statements in the existing `## Error constants`
   section with `sorry` bodies and verified the file compiled in that
   intermediate state.
2. Submitted the five planner-selected Aristotle jobs against the live
   `OpenMath/AdamsMethods.lean`:
   - `47f16f7c-43a1-4e8d-80f9-7a2160504be6`:
     `adamsBashforth4_errorConstant`
   - `a1caad0f-d7b3-4921-841d-ec35e83a8288`:
     `adamsBashforth5_errorConstant`
   - `90432dc7-9998-4a8c-b322-de7164928944`:
     `adamsBashforth6_errorConstant`
   - `b255f3eb-cb37-4b46-aa82-2c923a63c2b2`:
     `adamsMoulton5_errorConstant`
   - `408efb68-d0ad-4458-9138-d86325e985e3`:
     `adamsMoulton6_errorConstant`
3. Slept for 30 minutes, then performed one refresh pass.
4. Replaced all six sorries with direct finite-sum computations:
   `unfold LMM.errorConstant LMM.orderCondVal <method>`, then
   `simp [Fin.sum_univ_five/Fin.sum_univ_succ, Nat.factorial]`, then
   `norm_num`.

## Result
SUCCESS.

New theorems:

- `adamsBashforth4_errorConstant : adamsBashforth4.errorConstant 4 = 251/720`
- `adamsMoulton4_errorConstant : adamsMoulton4.errorConstant 5 = -(3/160)`
- `adamsBashforth5_errorConstant : adamsBashforth5.errorConstant 5 = 95/288`
- `adamsMoulton5_errorConstant : adamsMoulton5.errorConstant 6 = -(863/60480)`
- `adamsBashforth6_errorConstant : adamsBashforth6.errorConstant 6 = 19087/60480`
- `adamsMoulton6_errorConstant : adamsMoulton6.errorConstant 7 = -(275/24192)`

Verification:

- `lake env lean OpenMath/AdamsMethods.lean` succeeds.
- `lake build OpenMath.AdamsMethods` succeeds.
- Lean LSP goal check at `adamsMoulton6_errorConstant` reports no goals.
- `plan.md` section 1.2 error-constants bullet now lists AB4/AM4/AB5/AM5/AB6/AM6.

Aristotle refresh results:

- `47f16f7c...` COMPLETE.
- `a1caad0f...` COMPLETE.
- `90432dc7...` COMPLETE_WITH_ERRORS.
- `b255f3eb...` COMPLETE_WITH_ERRORS.
- `408efb68...` still IN_PROGRESS at 9% after the single required refresh.

The four terminal bundles were extracted under
`.prover-state/aristotle_results/cycle_391/`. They were not merged directly:
each bundle created or modified a stub `OpenMath/MultistepMethods.lean`, which
the strategy explicitly rejects. The usable content was only the expected proof
shape, matching the local direct computations.

## Dead ends
No proof dead end. The only rejected path was wholesale Aristotle bundle
transplant: even the COMPLETE bundles carried stub dependency files and
therefore were not safe to merge.

## Discovery
The standard cycle-390 proof skeleton scales to the rest of AB/AM through AM6.
For the 5- and 6-step methods, `Fin.sum_univ_succ` is sufficient; no named
`Fin.sum_univ_six` lemma or heartbeat increase is needed.

Hand checks against the live coefficient lists matched the table:

- AB4: `V_5 = 251/6`, so `C_5 = 251/720`.
- AM4: `V_6 = -27/2`, so `C_6 = -3/160`.
- AB5: `V_6 = 475/2`, so `C_6 = 95/288`.
- AM5: `V_7 = -863/12`, so `C_7 = -863/60480`.
- AB6: `V_7 = 19087/12`, so `C_7 = 19087/60480`.
- AM6: `V_8 = -1375/3`, so `C_8 = -275/24192`.

## Suggested next approach
The AB2-AB6 and AM2-AM6 error-constant table is now closed. Do not revisit the
blocked section 1.3 / section 2.2 quantitative starting-error theorem or Theorem 359D without a
new primary-source citation. A future small cycle could audit for another
purely mechanical Adams identity, but the main Adams error-constant extension
scheduled for this cycle is complete.
