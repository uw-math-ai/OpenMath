# Cycle 1170 Results

## Worked on
- Step 0 prerequisite: `adamsMoulton7_consistent` in
  `OpenMath/AdamsMethods.lean` next to `adamsMoulton6_consistent`.
- §530 LMM-as-GLM order-≥ 2 witness `adamsMoulton7_toGLM_hasOrderGe2`
  (and the projection `adamsMoulton7_toGLM_hasOrderGe1`) in
  `OpenMath/LMMAsGLM/Section530Step7.lean`.

## Approach
Mechanically mirrored the cycle 1164 AM6GE2 template
(`OpenMath/LMMAsGLM/Section530.lean:1368-1497`) with the
straightforward s : 6 → 7 substitutions specified by the strategy.

- Added `adamsMoulton7_consistent` with the standard
  `simp [LMM.rho/sigma, adamsMoulton7, Fin.sum_univ_succ]; norm_num`
  shape used for AM5/AM6.
- In `Section530Step7.lean` introduced `namespace AM7GE2` with the
  unshifted natural Nordsieck vectors `qN`, `q'N`, `q''N`
  (`q''` is `j² / 2j`, **no** `C` shift — the `β_s ≠ 0` implicit
  method does not need a shift at `HasOrderGe2`).
- `q'_obligation`: single `fin_cases k; all_goals simp [...];
  all_goals norm_num` over `Fin 14`.
- `q''_obligation` dispatcher inlines k = 0..5 (k = 0 is `simp`
  alone, k = 1..5 are `simp; norm_num`) and dispatches k = 6..13
  to eight per-row helpers `q''_obligation_six` …
  `q''_obligation_thirteen`.
- Boundary `q''_obligation_seven` (first past-`h·f` row, k = s = 7)
  closes with `simp` alone — adding `norm_num` would trigger
  "no goals to be solved", matching the AM6GE2 / AB7GE2 evidence.
- All other helpers use `simp [LMM.toGLM, adamsMoulton7,
  Fin.addCases, Fin.sum_univ_succ, qN, q'N, q''N]; norm_num`.
- Headline closure mirrors AM6GE2 verbatim: first goal
  `exact adamsMoulton7.toGLM_V_nordsieckQ_eq
  adamsMoulton7_consistent`; second goal `intro i; fin_cases i;
  all_goals simp [...]` (simp alone, β_s ≠ 0 implicit case).

## Result
SUCCESS.
- `lake env lean OpenMath/AdamsMethods.lean` clean.
- `lake build OpenMath.AdamsMethods` clean (cache refreshed).
- `lake env lean OpenMath/LMMAsGLM/Section530Step7.lean` clean
  (~2m05s wall, in line with AB7GE2 / AB7GE3 history).
- `lake build OpenMath` clean.
- File grew from 322 → 502 lines, well under the 3000-line cap.
- Both headline theorems sorry-free; AM7GE2 internals private.

## Dead ends
None. The mirror was first-try clean — every per-row tactic
prediction in the strategy held: k = 7 boundary closes with `simp`
alone, k = 6 (last past-y) and k = 8..13 (other past-h·f rows)
need `simp; norm_num`, and the closure row's second goal closes
with `simp` alone (β_s = 36799/120960 ≠ 0 implicit method, no
norm_num needed). No tactic adjustments were required.

## Discovery
- The "k = s boundary closes with `simp` alone, k > s rows need
  `simp; norm_num`" pattern continues to hold across the s = 7
  AB → AM rotation. AM7GE2 confirms what AB7GE2 / AM6GE2 / BDF6GE2
  established: this is a structural property of the dispatch row
  rather than a method-specific quirk.
- The AM6GE2 / AM7GE2 closure row's second goal also continues to
  close with `simp` alone for implicit `β_s ≠ 0` Adams–Moulton
  methods (in contrast to AB / BDF which need `simp; norm_num`).

## Suggested next approach
Per the strategy's "After this cycle" planning context, the
rotation continues with:

1. `adamsMoulton7_toGLM_hasOrderGe3` — order-3 mirror of AM6GE3
   with the AM7-specific shift `C := s² − 2 β_s s`. For AM7,
   `s = 7` and `β_s = 36799/120960`, so
   `C = 49 − 2·7·(36799/120960) = 49 − 36799/8640
       = (49·8640 − 36799)/8640 = (423360 − 36799)/8640
       = 386561/8640`.
   Per cycle 1168's AB7GE3 discovery, the k = 7
   `q'''_obligation_seven` boundary likely needs `simp; norm_num`
   (not simp alone) because the non-zero shift propagates into
   `q'''N` non-trivially.
2. `bdf7_toGLM_hasOrderGe2` and `bdf7_toGLM_hasOrderGe3` — closes
   the s = 7 quartet.
3. Once s = 7 closes, schedule §531 GLM local truncation error
   work in `OpenMath/GeneralLinearMethod.lean` — that is genuine
   new theorem work rather than rotation.
