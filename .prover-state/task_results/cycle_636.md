# Cycle 636 Results

## Worked on

§521 LMM-side stability-defect bridge in `OpenMath/LMMAsGLM.lean`,
mirroring cycle 635's RK-side bridge.

## Approach

Per strategy: land the four deliverables in a new
`§521 — Stability defect for LMM as GLM` section placed after
`LMM.toGLM_isConvergent`, in order 1 → 2 → 3 → 4.

1. **Deliverable 1** — `LMM.nordsieckQ` (the past-`y` indicator
   preconsistency vector) plus simp lemmas `nordsieckQ_castAdd`
   and `nordsieckQ_natAdd`.
2. **Deliverable 2** — `qℂ` lifts `toGLM_qℂ_nordsieckQ_castAdd` and
   `toGLM_qℂ_nordsieckQ_natAdd`.
3. **Deliverable 3** — `toGLM_V_nordsieckQ_eq` extracting the V·q=q
   row computation from cycle 614's `toGLM_isConsistent` first
   subgoal. Proof body lifted by copying the existing tactic chain
   and substituting `nordsieckQ s` for the inline `Fin.addCases`
   lambda. Required adding the `IsConsistent` hypothesis (the
   strategy's signature omitted it, but the last past-`y` row uses
   `hm.sum_α_eq_zero`).
4. **Deliverable 4** — `LMM.toGLM_stabilityDefect_zero` as a
   one-liner via `GeneralLinearMethod.stabilityDefect_zero` and
   `toGLM_V_nordsieckQ_eq`.

## Result

SUCCESS — all four deliverables landed sorry-free. `lake env lean`
on `OpenMath/LMMAsGLM.lean`, `OpenMath/RKAsGLM.lean`, and
`OpenMath/GeneralLinearMethod.lean` all pass. Total file size of
`LMMAsGLM.lean` after cycle: 1820 lines (was 1603), well under the
3000-line cap.

## Dead ends

* First attempt at the `qℂ` lift for `nordsieckQ_natAdd` used
  `simp [GeneralLinearMethod.qℂ]` which left a residual goal of
  shape `nordsieckQ s (Fin.cast _ (k.addNat s)) = 0`. The simp
  lemma is stated with `Fin.natAdd s k`, but Lean normalised the
  application to `addNat` form. Fixed by replacing `simp` with
  explicit `unfold qℂ; rw [nordsieckQ_natAdd]; norm_num`.
* The strategy asked for a single-line refactor of
  `toGLM_isConsistent`'s first subgoal:
  `exact m.toGLM_V_nordsieckQ_eq hm k`. Attempted, but creates a
  forward reference: `toGLM_isConsistent` is at line ~720 and
  `toGLM_V_nordsieckQ_eq` lives in the new §521 section after
  `toGLM_isConvergent` (line ~1330). Lean rejected with
  "environment does not contain `LMM.toGLM_V_nordsieckQ_eq`".
  Reverted to the original 176-line inline proof. The four
  deliverables themselves are unaffected.

## Discovery

* `Fin.natAdd s k` and `k.addNat s` produce the same value but
  Lean's elaborator may pick either form. When stating simp lemmas
  for the `Fin (s + s)` injections, prefer manual unfolding +
  `rw` over `simp` to avoid normalisation surprises.
* Reorganising `nordsieckQ` and `toGLM_V_nordsieckQ_eq` to live
  before `toGLM_isConsistent` would unlock the strategy's intended
  refactor; the helpers themselves do not depend on
  `toGLM_isConsistent`. A future cycle can move the new section
  ahead of `toGLM_isConsistent` and then collapse subgoal 1 to a
  one-liner — net change would be roughly −175 lines.

## Suggested next approach

Two non-blocking cleanup options before the iff bridge:
1. Move the new `§521 — Stability defect for LMM as GLM` section to
   appear before `toGLM_isConsistent` in `LMMAsGLM.lean`, then
   refactor `toGLM_isConsistent`'s first subgoal to
   `exact m.toGLM_V_nordsieckQ_eq hm k`. Net −~175 lines.
2. Land an `LMM.toGLM_stabilityDefect_apply` mirror of cycle 635's
   RK lemma — the LMM-side row formula for the defect entries —
   so a downstream `LMM.HasStabilityOrder` characterisation can
   reuse it.

Either is a small and concrete next-cycle task. The blocked
`LMM.toGLM_isAStable_iff` (general-`s` charpoly factorisation)
still needs a structured plan and is not the right next seam.

§38 remains paused per `plan.md` "Paused note" and
`.prover-state/issues/section386aug_strong_induction_obstruction.md`.
