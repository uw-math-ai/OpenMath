# Cycle 610 Results

## Worked on

Butcher §502 — Runge–Kutta methods as general linear methods. New
tracked module `OpenMath/RKAsGLM.lean` consuming the cycle 609 GLM
public API.

## Approach

Sorry-first scaffold of the file with the strategy's exact signatures,
verified compilation, then closed each sorry.

- `toGLM` definition with `r = 1`, `U = 1`, `V = 1` (matches Butcher's
  §502 description verbatim — confirmed).
- Four `simp` projection lemmas (`toGLM_A`/`_U`/`_B`/`_V`) close by
  `rfl`.
- `toGLM_stageMap_eq`: `simp [GeneralLinearMethod.stageMap_apply,
  toGLM]; ring`. The `r = 1` sum over `Fin 1` collapses
  automatically through `simp` — no explicit `Fin.sum_univ_one` needed
  (multi_attempt warned that `Fin.sum_univ_one` is unused).
- `toGLM_step_eq`: same recipe via `step_apply`.
- `toGLM_isExplicit`: `intro i j hij; exact ht i j
  (Fin.le_iff_val_le_val.mpr hij)`. The two-line bridge between the
  GLM `j.val ≥ i.val` form and the RK `i ≤ j` form went through
  exactly as the strategy predicted; the fallback in
  `glm_isExplicit_alignment.md` did not need to fire.
- `toGLM_stageEquations_unique_solution`: direct one-liner
  `exact t.toGLM.stageEquations_unique_solution hf hh (fun _ => y₀)
  hsmall`.

## Result

SUCCESS — `OpenMath/RKAsGLM.lean` compiles cleanly with zero `sorry`,
zero diagnostic warnings. `lake build OpenMath.RKAsGLM` succeeds (file
is the only fresh compilation unit).

## Dead ends

None this cycle. The proofs landed exactly along the strategy's
recipes. `lean_multi_attempt` confirmed both `simp [...]; ring` and the
`rw + simp + ring` variant for the stage/step lemmas; chose the
shorter `simp; ring` form.

## Discovery

The `Fin 1` collapse in the stage/step lemmas is fully automated by
`simp` once `toGLM` is unfolded — no explicit
`Fin.sum_univ_one`/`Finset.sum_const` step required. This keeps the
proofs to a single line each, matching the strategy's "if a target
collapses by a single `simp` after the right unfolding, keep the proof
that short" guidance.

## Suggested next approach

Promote backlog item #1 — Butcher §503 (LMM-as-GLM, `s = 1`
Nordsieck-vector embedding) — to the next cycle's strategy. This
reuses the same `GeneralLinearMethod` module via the existing `LMM`
interface and is structurally analogous to §502, so the same
sorry-first scaffold and `simp [...]; ring` recipe should apply once
the embedding is written.

§510 (GLM consistency definitions) is the natural follow-up after
§503 to complete the Chapter 5 opening salvo.
