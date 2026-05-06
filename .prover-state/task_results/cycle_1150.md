# Cycle 1150 Results

## Worked on
File-size split of `OpenMath/LMMAsGLM.lean` (3203 lines, over the 3000-line
file-size cap) into the parent file plus a new
`OpenMath/LMMAsGLM/Section530.lean` carrying the §530 order-≥ 2 and
order-≥ 3 LMM-as-GLM witnesses.

## Approach
Followed the planner's mechanical recipe verbatim:

1. Confirmed boundaries via
   `grep -n "^/-! ### §530\|^namespace Matrix\|^end LMM" OpenMath/LMMAsGLM.lean`.
   Lines 1670 (start of `AB5GE2`) through 3018 (last `all_goals norm_num`
   of the `adamsMoulton4` order-≥ 3 wrapper) are the §530 order-≥ 2 /
   order-≥ 3 block. Line 3019 is blank; line 3020 starts `namespace Matrix`.
2. Created `OpenMath/LMMAsGLM/Section530.lean` with a 22-line file
   header (imports `OpenMath.LMMAsGLM`; opens `Finset Real`) followed by
   the verbatim copy of lines 1670–3018. Total new file size: **1372 lines**.
3. Replaced lines 1670–3018 of the parent file with a single
   re-export comment pointing at `OpenMath/LMMAsGLM/Section530.lean`.
   Parent file shrinks to **1856 lines**.
4. No external consumer of LMM-side `_toGLM_hasOrderGe2` /
   `_toGLM_hasOrderGe3` witnesses exists outside `OpenMath/LMMAsGLM.lean`
   itself (verified via `grep -rln "_toGLM_hasOrderGe2\|_toGLM_hasOrderGe3"
   OpenMath/`; the only matches in `OpenMath/RKAsGLM.lean` are RK names,
   not LMM names). No import updates needed elsewhere.
5. Verified the split with `lake env lean` per file and a final
   `lake build` over the whole project.

## Result
SUCCESS — the split landed cleanly.

- `OpenMath/LMMAsGLM.lean`: 3203 → **1856 lines**.
- `OpenMath/LMMAsGLM/Section530.lean` created at **1372 lines**.
- `lake env lean OpenMath/LMMAsGLM.lean` succeeds in ~95 s.
- `lake env lean OpenMath/LMMAsGLM/Section530.lean` succeeds in ~61 s
  (after rebuilding the parent olean).
- `lake env lean OpenMath/LMMAsGLM/Stability.lean`,
  `OpenMath/LMMAsGLM/StabilityCharpoly.lean`,
  `OpenMath/LMMAsGLM/StabilityCharpolyEval.lean` all still typecheck
  against the trimmed parent.
- `lake build` reports **Build completed successfully (8087 jobs)** —
  no transitive breakage.
- `grep -n "sorry" OpenMath/LMMAsGLM.lean OpenMath/LMMAsGLM/Section530.lean`
  is empty.

## Dead ends
First attempt at compiling `Section530.lean` reported every theorem
"already declared" because the `lake env lean` typecheck of the trimmed
parent does **not** rewrite `.lake/build/lib/lean/OpenMath/LMMAsGLM.olean`
— it only typechecks against the existing olean. The cached olean was
the pre-split full version, so importing `OpenMath.LMMAsGLM` from the
new sibling file pulled in the still-cached §530 declarations and they
collided with the same declarations being introduced in `Section530.lean`.

The fix: invoke `lake build OpenMath.LMMAsGLM` to refresh the olean
before checking the new sibling. After that, `Section530.lean` typechecks
without errors. This is a pattern worth remembering: **after deleting
declarations from a parent file, run `lake build <ParentModule>` to
refresh its olean before importing it from a new child**.

## Discovery
- The §530 block is genuinely self-contained: no internal cross-references
  between order-ge2/ge3 witnesses and the rest of the file other than
  reading the public top-level `LMM.toGLM_hasOrderGe1` / `.toHasOrderGe1`
  forwarders and the §510/§511 LMM helpers, all of which remain in the
  parent. The mechanical move worked verbatim with zero edits to any
  declaration body.
- Lake's `lean_lib name = "OpenMath"` config auto-discovers
  `OpenMath/LMMAsGLM/Section530.lean`; no `lakefile.toml` edit needed.
- Stability.lean / StabilityCharpoly.lean / StabilityCharpolyEval.lean
  do not depend on §530 ge2/ge3 witnesses, only on `namespace LMM` plus
  `namespace Matrix` helpers (both unchanged) — confirms the planner's
  dependency analysis.

## Suggested next approach
With the file size cap now comfortably resolved (parent 1856 lines,
child 1372 lines), the §530 LMM-as-GLM rotation can resume:

- Stretch target deferred from this cycle: `bdf5_toGLM_hasOrderGe3`
  in `OpenMath/LMMAsGLM/Section530.lean`. Recipe per planner: mirror
  `BDF4GE3` (now at lines ~1183–1257 of `Section530.lean`), with
  `bdf4` → `bdf5`, `Fin (2 * 4)` → `Fin (2 * 5)`, `Fin 8` → `Fin 10`,
  and the shift constant `C := s² − 2 β_s · s` recomputed from
  `bdf5.β` in `OpenMath/BDF.lean`.
- After `bdf5_toGLM_hasOrderGe3`, the §530 ge3 frontier still has
  `adamsBashforth5_toGLM_hasOrderGe3` (already landed cycle 1142) and
  `adamsMoulton5_toGLM_hasOrderGe3` (landed cycle 1146). The natural
  next-but-one ge3 target after BDF5 is `adamsMoulton6_toGLM_hasOrderGe2`
  (no ge1 yet for AM6 — check if `adamsMoulton6` is even defined in
  `OpenMath/AdamsMethods.lean` before planning that).
- Cycle 1138's order-4 obstruction
  (`.prover-state/issues/cycle_1138_am3_hasOrderGe4_obstruction.md`)
  remains a hard structural blocker for the entire `r = 2 * s` Nordsieck
  template. The next §530 architectural question — if/when the
  rotation runs out of ge2/ge3 targets — is whether to extend the
  Nordsieck input width to `r = 3 * s` (carrying past `h² · y''` values)
  to bypass the obstruction. That deserves its own planner cycle.

## File-size status after this cycle
- `OpenMath/LMMAsGLM.lean`: 1856 lines (under cap).
- `OpenMath/LMMAsGLM/Section530.lean`: 1372 lines (well under cap).
- `OpenMath/LMMAsGLM/StabilityCharpolyEval.lean`: ~2200 lines (unchanged,
  approaching cap but still under).
- `OpenMath/LMMAsGLM/StabilityCharpoly.lean`: ~1900 lines (unchanged).
- `OpenMath/LMMAsGLM/Stability.lean`: ~1600 lines (unchanged).
