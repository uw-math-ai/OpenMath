# Cycle 109 Results

## Worked on

`OpenMath.Chapter5.Section510.GeneralLinearMethod.stable_consistent_isConvergent`
(`thm:515D`) — course-correct cycle 108's sorry-count regression
(0 → 3 sorries) by closing the inline `s = 0` degenerate-branch sorry.

## Approach

Followed the strategy's Priority 1 (REQUIRED): apply Option D from
`thm_515D_s_zero_degenerate.md` — strengthen the theorem signature
with an `(hs : 0 < s)` precondition and drop the `by_cases hs` /
`s = 0` branch entirely. The `u ≠ 0` clause now closes inline via
`congrFun hUu ⟨0, hs⟩` + `simp [Matrix.mulVec, dotProduct]`.

Concrete edits:

1. `OpenMath/Chapter5/Section515.lean:1573` — added
   `(hs : 0 < s)` parameter; dropped `by_cases hs` branch.
2. Docstring updated with explicit "Faithfulness divergence" note
   linking to the issue file.
3. `extraction/formalization_data/lean_status.json:823` — `thm:515D`
   row updated to "scaffold + 2 sorries (cycle 109; `0 < s`
   precondition added)" with cycle bumped 108 → 109.
4. `.prover-state/issues/thm_515D_s_zero_degenerate.md` — prepended
   `## Resolution (cycle 109) — RESOLVED via Option D` section;
   kept the prior analysis as a record.

Aristotle plan: polled the cycle-108 batch
(`40554853-18b3-424c-81e4-2a2fae9e57c4`) once. Status: `IN_PROGRESS`,
6% complete. Per the strategy's branching rule, ignored — did not
poll again, did not submit a fresh batch.

Priority 2 (refactor `aux_515D_stage_tendsto` to take `h_output`
explicit) was deliberately skipped this cycle. Per the strategy's
own scenario table, the refactor-with-deferred-boundedness path
nets the same 3 → 2 sorry count as Priority 1 alone but adds
structural churn; the inline-boundedness path is ~150–200 LOC and
risks a no-progress cycle if it falls over. The cycle-109 floor
(3 → 2) is the safe, blessed deliverable; Priority 2 is now
trajectory cycle 110's target with the cycle-108 Aristotle batch
likely returning by then.

## Result

**SUCCESS** — sorry count 3 → 2 (out of 2 in `OpenMath/`).

Verification:
* `lake env lean OpenMath/Chapter5/Section515.lean` produces only
  the two expected warnings:
  - `OpenMath/Chapter5/Section515.lean:1481:16: warning: declaration uses 'sorry'`
    (`aux_515D_output_tendsto`)
  - `OpenMath/Chapter5/Section515.lean:1522:16: warning: declaration uses 'sorry'`
    (`aux_515D_stage_tendsto`)
* No external callers of the Chapter 5 `GLM.stable_consistent_isConvergent`
  outside `Section515.lean` itself (Chapter 4 references all point
  at the LMM analog `LinearMultistepMethod.stable_consistent_isConvergent`).

## Faithfulness check

For `GeneralLinearMethod.stable_consistent_isConvergent` (modified):

- Entity ID and textbook statement (quoted from
  `entities/thm_515D.json`):
  > A stable and consistent general linear method is convergent.
- Lean statement captures: **stronger** (extra hypothesis
  `(hs : 0 < s)`).
- Justification for divergence: Butcher §515 implicitly assumes the
  GLM has at least one internal stage. The abscissae
  `c = A·𝟙 + U·v` analyzed in lem:515A are vacuous (empty function)
  when `s = 0`, and the entire §515 narrative concerns RK-style
  methods with at least one stage. For `(s, r) = (0, 0)` the
  IsConvergent statement is **literally False** (vacuously) because
  `Fin 0 → ℝ` has only the zero inhabitant, so `u ≠ 0` is
  impossible — the textbook's flat statement is therefore also
  incorrect at that corner case, and our `(hs : 0 < s)` divergence
  is just making this explicit. Documented in the docstring at
  `Section515.lean:1562-1570` and in the resolution section of
  `.prover-state/issues/thm_515D_s_zero_degenerate.md`.
- Tautology check: hypotheses `(hs, M, M.IsStable, M.IsConsistent)`
  ≠ conclusion `M.IsConvergent`. ✓
- Identity check: proof uses `intro / obtain / refine / congrFun /
  simp` plus dispatch to two named sub-lemmas. Not a vacuous
  re-export. ✓
- Hypothesis strength check: `(hs : 0 < s)` is a strengthening,
  documented. `IsStable` + `IsConsistent` unchanged from
  the entity statement. ✓
- Absent theorem check: docstring promises `aux_515D_output_tendsto`
  and `aux_515D_stage_tendsto`; both exist (sorry'd, lines 1481 and
  1522). ✓

No new `def` / `structure` introduced this cycle.

## Dead ends

None — Priority 1 was straightforward once the strategy locked in
Option D. The only judgment call was deferring Priority 2; that is
documented in the Approach section above.

## Discovery

* The signature change `(hs : 0 < s)` had **zero downstream impact**
  outside `Section515.lean`. The Chapter 4 references to
  `stable_consistent_isConvergent` all point at the LMM analog
  `LinearMultistepMethod.stable_consistent_isConvergent` (in
  `Section404.lean:5455` and `Section405.lean:600`). This makes
  future cycles' refactors of the GLM theorem cheap.
* The cycle-108 Aristotle batch is still 6% in progress after ~50
  minutes. If it completes by cycle 110/111 with usable output for
  `aux_515D_output_tendsto`, that would unblock the Grönwall-flavour
  output-convergence proof faster than a manual decomposition.
  However, do NOT count on Aristotle for this — historically poor
  on discrete-Grönwall + squeeze (cycles 094/096).

## Suggested next approach

For cycle 110 (assuming this cycle's commit lands at 3 → 2):

1. **Refactor `aux_515D_stage_tendsto` signature** to take an
   `h_output : Tendsto (fun n => Y n n) atTop (nhds (fun i => u i * yex x))`
   explicit hypothesis, per cycle 109 Priority 2 Step 2a. This is a
   *zero-cost* refactor (call site already exists in
   `stable_consistent_isConvergent` and adapts to a `let h_output := …`
   binding).
2. **Close `aux_515D_stage_tendsto`** modulo the eventual-stage-
   boundedness piece, exposing the latter as a sorry'd helper
   `aux_515D_stage_eventually_bounded`. Net sorry count stays at 2
   (refactored). The proof shape is laid out in cycle 109 strategy
   Step 2b: T1 = h_n · ∑ A·f → 0 (squeeze via Lipschitz +
   `tendsto_one_div_atTop_nhds_zero`); T2 = U·(Y n n) → U·(u·yex x) =
   yex x (matrix-mulVec continuity + `hUu`). The combine step uses
   `tendsto_pi_nhds.mpr` with `Filter.Tendsto.congr'` for the n = 0
   edge.
3. **Cycle 111** — close `aux_515D_stage_eventually_bounded` via
   the M-matrix infrastructure (`OpenMath/Chapter5/MMatrix.lean`'s
   `Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg` from
   cycles 105–107). Net 2 → 1.
4. **Cycle 112+** — open `aux_515D_output_tendsto` decomposition
   (per cycle 109 strategy Priority 3 sketch), mirroring the LMM
   chain at `Section404.lean:1300+`.

Aristotle handling: poll the cycle-108 batch once more in cycle
110. If completed with proofs and they fit either signature, salvage;
otherwise cancel to free the queue.
