# OpenMath Loop Evaluation — 2026-05-05 (after cycle 111)

## Red flags (auto)
_None — all metrics within thresholds._

## Headline numbers
| Metric                  | Value             | Detail                                                                                                                       |
| ----------------------- | ----------------- | ---------------------------------------------------------------------------------------------------------------------------- |
| Entities formalized     | 66/175 (37.7%)    | new-entity EMA 0.00/cycle                                                                                                    |
| Sorry-close velocity    | +0.00/cycle (net) | 6 gross closes in window                                                                                                     |
| Open sorries (current)  | 3                 | 0 suspected vacuous                                                                                                          |
| Open issue files        | 26                |                                                                                                                              |
| Last progress score     | 2                 | tail non-positive run = 0                                                                                                    |
| Loop state              | terminated        | terminated (process gone — likely SLURM time limit or kill); heartbeat 1634.3 min; lock=held (5935.8 min old); stuck level 0 |
| Aristotle ROI (last 20) | 8/8 (100%)        |                                                                                                                              |

## M1  Velocity (forward progress per cycle)
| Cycle | Newly formalized entities |
| ----- | ------------------------- |
| 102   | 0                         |
| 103   | 0                         |
| 104   | 0                         |
| 105   | 0                         |
| 106   | 0                         |
| 107   | 0                         |
| 108   | 0                         |
| 109   | 0                         |
| 110   | 0                         |
| 111   | 0                         |

- New-entity EMA: **0.00**/cycle
- Sorry-close net: **+0.00**/cycle (6 gross closes over window)

Flag fires only on combined stagnation (no new entities, no net sorry decrease, and zero gross closures). Flag: **False**  —  66/175 formalized; new-entity EMA-10=0.00/cycle, sorry-close net=+0.00/cycle (gross 6 over window)

## M2  Sorry trajectory
| Cycle | Pre | Post | Semantic (post) |
| ----- | --- | ---- | --------------- |
| 102   | 1   | 0    | 0               |
| 103   | 0   | 3    | 0               |
| 104   | 3   | 1    | 0               |
| 105   | 1   | 1    | 0               |
| 106   | 1   | 1    | 0               |
| 107   | 1   | 0    | 0               |
| 108   | 0   | 3    | 0               |
| 109   | 3   | 2    | 0               |
| 110   | 2   | 2    | 0               |
| 111   | 2   | 1    | 0               |

Current: **3** sorry, **0** suspected vacuous.
Rising-post run: 0.  Flag: **False**

## M3  Self-reported progress score
| Score | Count |
| ----- | ----- |
| -2    | 14    |
| -1    | 5     |
| 0     | 10    |
| 1     | 19    |
| 2     | 56    |
| 3     | 1     |

Recent scores: [2, -2, 2, 1, 2, 2, -2, 2, 1, 2]
Longest non-positive run (any time): 5; tail run: 0.  Flag: **False**

## M4  Sorry ↔ Issue map
| File:line                              | Issue file(s)                                                                                                                                             | Snippet |
| -------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------- | ------- |
| OpenMath/Chapter5/Section515.lean:1504 | aux_515D_output_tendsto_hypotheses.md, aux_515D_stage_eventually_bounded_deferred.md, lem_515B_eta_contraction_deferred.md, thm_515D_s_zero_degenerate.md | sorry   |
| OpenMath/Chapter5/Section515.lean:1523 | aux_515D_output_tendsto_hypotheses.md, aux_515D_stage_eventually_bounded_deferred.md, lem_515B_eta_contraction_deferred.md, thm_515D_s_zero_degenerate.md | sorry   |
| OpenMath/Chapter5/Section515.lean:1622 | aux_515D_output_tendsto_hypotheses.md, aux_515D_stage_eventually_bounded_deferred.md, lem_515B_eta_contraction_deferred.md, thm_515D_s_zero_degenerate.md | sorry   |

Flag: **False**  —  3 live sorry; 0 unmatched; 0 orphan issues (>30d, no live sorry)

## M5  Faithfulness audit
_No tautology hits._

Flag: **False**  —  0 tautology hit(s); 0 cycle(s) with faithfulness_flags in last 10

## M6  Aristotle ROI (last 20 cycles)
| Cycle | # Submitted | Landed? |
| ----- | ----------- | ------- |
| 92    | 1           | ✓       |
| 94    | 1           | ✓       |
| 100   | 1           | ✓       |
| 103   | 1           | ✓       |
| 105   | 1           | ✓       |
| 112   | 3           | ✓       |

Flag: **False**  —  last 20 cycles: 8/8 submissions landed (100%)

_(Heuristic: a submission counts as 'landed' if the same or next 3 task_results files mention 'Aristotle' near SUCCESS / closed / ported / harvested.)_

## M7  Blocker leverage (open issues, ranked by # blocked dependents)
| Issue                                  | Entity IDs                                                                                                                                 | # blocked | # closure |
| -------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------ | --------- | --------- |
| consultant_advice_cycle_015.md         | def:310A, def:350A, def:381B, def:381D, lem:319A, lem:322A, lem:383C, thm:142D, thm:213B, thm:243A, thm:301A, thm:302C                     | 75        | 102       |
| symmetry_group_equivalence.md          | def:310A, def:388D, lem:310B, lem:312B, lem:313A, thm:301A, thm:302A, thm:311D, thm:317A, thm:372A                                         | 41        | 58        |
| consultant_advice_cycle_009.md         | def:110A, def:112A, lem:319A, thm:110C, thm:111A, thm:111B, thm:112B, thm:123A, thm:123B, thm:140A, thm:141A, thm:142C, thm:142E, thm:142F | 34        | 63        |
| reduced_method_deferred.md             | def:370A, def:381A, def:381C, def:381E, def:381F, thm:381G, thm:381H                                                                       | 19        | 24        |
| equivalent_self_general_deferred.md    | def:381A, lem:383A, lem:389A, thm:381H, thm:382A, thm:384A, thm:388B                                                                       | 16        | 20        |
| is_convergent_strengthened.md          | def:402A, thm:110C                                                                                                                         | 13        | 24        |
| picard_lindelof_bound_strengthening.md | lem:319A, thm:110C, thm:111A, thm:112B                                                                                                     | 13        | 24        |
| convolution_vertex_vs_multiset.md      | lem:383A, lem:383B, lem:383D, thm:386A                                                                                                     | 9         | 11        |
| AN_stability_deferred.md               | cor:356D, def:356A, def:356B, def:357B, thm:356C, thm:357C, thm:357D                                                                       | 8         | 12        |
| glm_convergence_witness_deferred.md    | def:402A, def:512A, def:542A, lem:515B, thm:513A, thm:514A, thm:515D                                                                       | 6         | 15        |

## M8  Liveness
- **state**: — `terminated`
- pid: `86025` (dead)
- phase: `worker`
- cycle: `112`
- heartbeat age: **1634.3 min**
- lock file: present (age **5935.8 min**)
- stuck: no indicators

Flag: **False**  —  terminated (process gone — likely SLURM time limit or kill); heartbeat 1634.3 min; lock=held (5935.8 min old); stuck level 0

## Manual spot-check queue
| Entity   | Slot         | Kind       | Lean file                         | Symbol                                                                |
| -------- | ------------ | ---------- | --------------------------------- | --------------------------------------------------------------------- |
| def:512A | recent       | definition | OpenMath/Chapter5/Section512.lean | OpenMath.Chapter5.Section510.GeneralLinearMethod.IsConvergent         |
| lem:515B | recent       | lemma      | OpenMath/Chapter5/Section515.lean | OpenMath.Chapter5.Section510.GeneralLinearMethod.localStepError_bound |
| def:142B | highest-tier | definition | OpenMath/Chapter1/Section142.lean | OpenMath.Chapter1.Section142.Convergent                               |
| thm:123B | random-proof | theorem    | OpenMath/Chapter1/Section123.lean | OpenMath.Chapter1.Section123.area_const                               |
| def:110A | rotation     | definition | OpenMath/Chapter1/Section110.lean | OpenMath.Chapter1.Section110.LipschitzInSecond                        |

Run `python scripts/spotcheck.py` to audit these via LLM (or do the manual checklist yourself).

---
_Generated by `scripts/evaluate_loop.py`. Run with `--no-write` for stdout-only._
