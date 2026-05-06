# Cycle 1158 Results

## Worked on
`adamsMoulton6_toGLM_hasOrderGe2` and projection `_hasOrderGe1` in
`OpenMath/LMMAsGLM/Section530.lean`. Continues the §530 LMM-as-GLM
ladder following AB6GE2 (cycle 1154) and AB6GE3 (cycle 1156).

## Approach
Mirrored the AB6GE2 recipe verbatim with `adamsBashforth6 → adamsMoulton6`
substitution and unshifted natural Nordsieck Taylor template (no
`s² − 2 β_s s` shift since GE2 obligations don't need it):

- New `namespace AM6GE2` block inserted after `adamsBashforth6_toGLM_hasOrderGe3`.
- Per-row helpers `q''_obligation_<k>` for `k ∈ {5, 6, 7, 8, 9, 10, 11}`
  to keep each row's heartbeats bounded under the 200000 ceiling.
- Master dispatcher `q''_obligation` with inline `simp; norm_num` for
  `k ∈ {1..4}`, bare `simp` for `k = 0`, and `exact q''_obligation_<k>`
  for `k ∈ {5..11}`.
- Public theorem assembled via `refine ⟨…⟩` with the closure-row dispatch
  `intro i; fin_cases i; all_goals simp [...]`.

## Result
SUCCESS — `lake env lean OpenMath/LMMAsGLM/Section530.lean` builds clean
in 1m30s, no errors or warnings. File grows from 1926 → 2070 lines, well
under the 3000-line cap.

## Dead ends
First pass had `simp [...]; norm_num` for `q''_obligation_six` (k=6, first
past-h·f row). Lean rejected with "No goals to be solved" at column 20
(the `norm_num` token), confirming the strategy's predicted boundary
nuance: for k=6 the `simp` alone closes the goal because the row carries
no fractional remainder. Removing the trailing `; norm_num` for that one
helper made the file compile. All other helpers (k = 5, 7, 8, 9, 10, 11)
need both `simp` and `norm_num` because AM6's implicit β coefficients
leave fractional residues that `simp` cannot resolve.

## Discovery
The implicit/explicit boundary at row k=6 is identical for AM6 and AB6:
both close with `simp` alone, despite the very different β-coefficient
structures (AB6 has β_s = 0, AM6 has β_s = 19087/60480). This suggests
the `simp`-vs-`simp; norm_num` boundary at k=6 is a structural property
of the toGLM `Fin 12` U-row layout (likely the first past-h·f row's V
entries reduce to plain integer multiples of q''N values) rather than a
coefficient-dependent quirk. The next AM6GE3 cycle should expect the
same boundary.

## Suggested next approach
Cycle 1160: `adamsMoulton6_toGLM_hasOrderGe3` with shift constant
`C := s² − 2·β_s·s = 36 − 2·(19087/60480)·6 = 162353/5040`. Mirror
AB6GE3 (cycle 1156) with `Fin 12` size and pre-extracted per-row
q''-helpers (k = 5..11) and q'''-helpers (k = 4..11). The fractional
shift constant has uglier numerator/denominator than AM5GE3's `3125/144`
so `norm_num` may need extra heartbeats per row; if any row times out,
try `field_simp; ring` after `simp`.

After AM6GE3 lands, the §530 s = 6 frontier is BDF6GE2 → BDF6GE3 → s = 7
(AB7/AM7) per the cycle 1138 obstruction (HasOrderGe4 is structurally
blocked at GE4 for every consistent LMM under the current Pascal
template).
