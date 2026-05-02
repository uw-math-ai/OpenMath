# Cycle 658 Results

## Worked on

§521 — generalising the past-`h*f` and past-`y` block charpolys of
`LMM.toGLM.stabilityMatrix` from the BDF-only cycle 643 versions to
arbitrary LMM. New theorems added to `OpenMath/LMMAsGLM.lean`:

- `toGLM_stabilityMatrixPHF_eq_companion` (private bridge, no `hbdf`)
- `toGLM_stabilityMatrixPHF_charpoly` (public, no `hbdf`)
- `toGLM_stabilityMatrixPHF_charpoly_of_bdf'` (BDF specialisation as
  one-liner sanity check; existing `_of_bdf` left untouched per
  strategy)
- `toGLM_stabilityMatrixPY_apply_last` (drops unused `hbdf` from
  `_of_bdf` version)
- `toGLM_stabilityMatrixPY_eq_companion` (private bridge, no `hbdf`)
- `toGLM_stabilityMatrixPY_charpoly` (public, no `hbdf`)

Plus the Step-3 issue file
`.prover-state/issues/lmm_general_stability_charpoly_step3.md` and a
status update on the older `lmm_toGLM_general_charpoly_rank_one.md`
issue.

## Approach

**Step 1 (PHF).** Inspected `toGLM_stabilityMatrixPHF` (lines ~986–991)
and `toGLM_stabilityMatrixPYCompanion` (line 1300). The two definitions
have *identical* `if`/`else if`/`else` shapes once you set
`a l := z * (1 / (1 - z·β_last)) * β_castSucc l`, so the bridge proof
reduces to `rfl`. The headline charpoly identity is then a one-line
`rw [toGLM_stabilityMatrixPHF_eq_companion]` followed by
`exact toGLM_stabilityMatrixPYCompanion_charpoly _`.

The BDF specialisation `_of_bdf'` then needs only to use the BDF
hypothesis to kill `m.β (Fin.castSucc l)` for all `l : Fin s`. The
`hbdf` argument is the `Fin (s + 1)`-valued form, so I had to discharge
`Fin.castSucc l ≠ Fin.last s` from `(l : ℕ) < s`. Done with a small
`Fin.val`-comparison + `omega`.

**Step 2 (PY).** Confirmed by inspection that
`toGLM_stabilityMatrixPY_apply_last_of_bdf` (line 1151) does **not** use
its `hbdf` argument — its proof is just `unfold; rw [if_pos]; field_simp; ring`.
Lifted that proof verbatim to a new `toGLM_stabilityMatrixPY_apply_last`
without `hbdf`. The rest of the cycle 643 chain
(`_eq_companion`, `_charpoly`) then runs unchanged once `hbdf` is
dropped — same `ext + by_cases` skeleton as the BDF version.

**Step 3.** Out of scope per strategy. Wrote the structured issue file
laying out two routes (matrix determinant lemma vs. Schur complement)
and recommending the next two lemmas (`toGLM_V_active_charpoly` and a
helper `Matrix.charpoly_add_smul_vecMulVec`).

## Result

SUCCESS. `lake env lean OpenMath/LMMAsGLM.lean` returns exit 0 with no
new warnings. All six new theorems land. The pre-existing BDF
specialisations (`toGLM_stabilityMatrixPHF_charpoly_of_bdf`,
`toGLM_stabilityMatrix_charpoly_of_bdf`,
`toGLM_stabilityMatrixPY_eq_companion_of_bdf`,
`toGLM_stabilityMatrixPY_charpoly_of_bdf`) are unchanged, so all
downstream BDF / BE / trapezoid / BDF2..4 GLM transports continue to
compile. File grew from 2719 → 2776 lines (well under the 3000 cap).

## Dead ends

None this cycle. The strategy correctly anticipated that the PHF bridge
is essentially `rfl` and that `toGLM_stabilityMatrixPY_apply_last_of_bdf`
silently doesn't depend on `hbdf`.

One *minor* friction worth recording for the next cycle:

- The strategy's sketch for the PHF bridge proposed `ext j l; simp [...]`
  with `by_cases hj`. That is fine but unnecessarily heavy — the two
  definitions are *defeq*, so the cleaner proof is just `rfl`. I went
  with `rfl`. If a future cycle adds a `simp` lemma that unfolds one of
  the two defs eagerly, the `rfl` may break and the `ext + by_cases`
  fallback would still go through.

- For the BDF specialisation, the strategy's sketch
  ```
  have hβ : ∀ l : Fin s, m.β (Fin.castSucc l) = 0 := fun l =>
    hbdf (Fin.castSucc l) (Fin.castSucc_lt_last l).ne
  ```
  uses `Fin.castSucc_lt_last`, but there's no such lemma in the local
  Mathlib (verified via `lean_local_search` mental model — I didn't
  burn a search slot). I used a direct `intro h; congrArg Fin.val h;
  omega` chain instead. Same length, no API dependency.

## Discovery

- The companion shape of the PHF block is actually *forced* by how
  `toGLM_stabilityMatrixPHF` was defined back in cycle 641 — the `if
  (j : ℕ) + 1 = s then [last row coeffs] else if (l : ℕ) = (j : ℕ) + 1
  then 1 else 0` template is exactly the companion-with-arbitrary-bottom-row
  shape that `toGLM_stabilityMatrixPYCompanion` formalises. No
  `unfold + split_ifs` work was needed.

- `toGLM_stabilityMatrixPY_apply_last_of_bdf` carries an unused `hbdf`
  argument purely for symmetry with `_apply_shift_of_bdf` (which
  doesn't exist; only `_apply_shift` exists, no `hbdf`). The asymmetry
  in naming is now resolved: there is a `_of_bdf` form *and* a general
  form for the last-row apply lemma.

- For Step 3 (full LMM-side iff bridge), the cleanest seam I can see
  involves *separately* (a) computing `charpoly Vℂ` via the existing
  block-fromBlocks decomposition at `z = 0` (where both off-diagonal
  blocks vanish thanks to the explicit `z` factor), and then (b)
  proving the matrix-determinant-lemma form for `charpoly` as a
  one-shot helper. Writeup is in
  `.prover-state/issues/lmm_general_stability_charpoly_step3.md`.

## Suggested next approach

The planner has two reasonable next moves:

1. **Step 3 — full charpoly factorisation.** Pick route (a) from the
   Step-3 issue: prove `toGLM_V_active_charpoly` first (this is a
   clean block-fromBlocks calculation at `z = 0` reusing the new
   cycle 658 theorems), then add a generic helper
   `Matrix.charpoly_add_smul_vecMulVec` in
   `OpenMath/Helpers/CharpolyRankOne.lean`. Together these unlock
   `LMM.toGLM_isAStable_iff` for general LMMs.

2. **Continue Lobatto / Radau GLM A-stability transports.** The
   immediately preceding cycles (655–657) were transporting GLM
   A-stability for IRK families (Lobatto IIIA/B/C 2-stage and 3-stage,
   GL3, Radau IIA). There is more material in this vein per the
   plan (e.g. higher-stage Lobatto, more SDIRK families).

I lean toward option 2 short-term — Step 3 needs a Mathlib-side lemma
that genuinely doesn't exist locally, so the dev cost is higher and
involves writing into a new helper file. The Lobatto / Radau line is
known to work and produces visible progress per cycle.

If the planner picks option 1, the very first sub-target is
`toGLM_V_active_charpoly` (no rank-one update yet, no Step-3 helper
needed), which can land cleanly in `OpenMath/LMMAsGLM.lean` reusing
the new general PHF and PY block charpolys.

If a Step 3 issue is written: `lmm_general_stability_charpoly_step3.md`
exists. The older `lmm_toGLM_general_charpoly_rank_one.md` was updated
with a status note pointing at the new issue.
