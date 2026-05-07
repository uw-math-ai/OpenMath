# Issue: GPFS filesystem slowness blocked cycle 182 verification

## Blocker

Cycle 182 wrote three substantive theorems for Phase C.2 of `lem:441A`
(Butcher §441 p. 376) — `ρPoly_complex_root_norm_le_one_of_stable`,
`αPoly_complex_root_norm_ge_one_of_stable`, and
`aPoly_complex_root_re_nonpos_of_stable` — totaling ~250 LOC of new
content.

Three consecutive `lake env lean OpenMath/Chapter4/Section441.lean`
attempts ran for 13–22 minutes each without completing. A fourth
attempt with `lake build OpenMath.Chapter4.Section441` (which uses
caching) ran for 20+ minutes (lake-real spent 4 min on dependency
analysis, then lean ran for 9+ min) without finishing.

Lean processes consistently showed:
* CPU 0.7–1.5% (very low)
* Read rate ~10 KB/sec (extremely slow)
* One thread always in `D` (disk wait) state
* Total mathlib oleans needed: ~3.5 MB (per cycle 181 baseline)
* Current rate: 30+ minutes per attempt

The bottleneck is GPFS olean loading — not Lean elaboration, not
my proof tactics. Cycle 181's compile (with similar file size and
mathlib load) finished in ~3 minutes yesterday on the same cluster.

## Context

The newly-written proofs are saved at
`.prover-state/cycle_182_draft_section441.lean` (1568 LOC — 341 LOC
added on top of cycle 181's 1227-line file). This draft is
mathematically careful and uses only standard Mathlib idioms verified
in Phase B (cycles 175–179):
* `simp only [..., aeval_*, eval_map, ...]` recipe — direct match
  with cycle 175's `geomSeq_isHomogeneousSolution_of_ρPoly_isRoot`
  (`OpenMath/Chapter4/Section441.lean:467–491` in HEAD).
* `Complex.re_sum`, `Complex.im_sum`, `Complex.normSq_apply`,
  `Complex.norm_pow` — verified-present via Mathlib source grep.
* `pow_unbounded_of_one_lt`, `pow_lt_pow_left₀`, `pow_mul_pow_sub`,
  `inv_le_one₀`, `Real.sq_sqrt` — verified-present.

To minimize tactic-side risk on a future re-attempt, the draft uses
explicit, fast tactics throughout:
* `eq_of_sub_eq_zero` instead of `linear_combination` (avoids
  ring-tactic overhead).
* Explicit `ring` rewrites + `linarith` instead of `nlinarith`.
* Explicit `mul_inv_cancel₀` chain instead of `field_simp`.
* `pow_le_pow_left₀` instead of `gcongr`.

## What was tried

1. `lake env lean OpenMath/Chapter4/Section441.lean` — three
   attempts (vN1, vN2, vN3, vN4 in /tmp logs).
2. `lake build OpenMath.Chapter4.Section441` — one attempt; got
   to "Replayed OpenMath.Chapter4.Section410" successfully (8031
   of 8032 build tasks complete from cache), then started
   compiling Section441 fresh, which is where the slowness lives.
3. Tactic simplification: replaced potentially-slow tactics
   (`linear_combination`, `nlinarith`, `field_simp`, `gcongr`)
   with their explicit-step equivalents. Did not help — bottleneck
   is olean loading, not tactic elaboration.
4. Process state inspection (`/proc/PID/wchan`,
   `/proc/PID/io`, `/proc/PID/task/.../status`): one thread
   consistently in `D` state on a GPFS kernel synchronization
   condition; reads progressing at 10 KB/sec.

## Possible solutions

### Loop-maintainer territory

* **Cluster admin consultation**: GPFS performance on
  `/mmfs1/gscratch/amath/...` may need investigation. The cycle
  181 baseline (3 minutes) vs cycle 182 (20+ minutes for the
  same file) is a 7× regression.
* **Pre-load oleans into `/tmp/` ramdisk**: similar to the elan-
  toolchain workaround in CLAUDE.md. Cache the full Mathlib olean
  set in tmpfs to avoid GPFS reads during compile.
* **Smaller smoke-test files**: replace the "compile the whole
  modified file" verification with a "compile a tiny test file
  that imports only the new theorems" smoke test. Cuts olean
  loading by 10×+.

### Worker-side workarounds

* **Wait it out**: lake build did make progress; it would have
  finished eventually given enough time (estimate 30–45 minutes
  per attempt today).
* **Commit unverified for Section441**: the file has no
  downstream dependents beyond `OpenMath/Chapter4.lean` (a thin
  aggregator), so a broken Section441 doesn't cascade. This is
  what cycle 182 ALMOST did, but ultimately reverted to HEAD to
  keep the build green.
* **Re-attempt next cycle**: GPFS slowness is variable; cycle 183
  may see normal performance.

## Cycle 182 disposition

* Section441.lean reverted to HEAD (cycle 181 state), 1227 lines,
  zero sorries, axiom-clean.
* Phase C.2 proof draft preserved at
  `.prover-state/cycle_182_draft_section441.lean`.
* `lean_status.json` row for `lem:441A` NOT updated (Phase C.2
  remains unshipped pending verification).
* `plan.md` row for `lem:441A` NOT updated.
* `lem_441A_phase_C_scoping.md` NOT updated to mark Phase C.2
  closed (since unverified).

## Recommended next-cycle entry point

1. Re-run `lake env lean OpenMath/Chapter4/Section441.lean` on a
   fresh shell to test current GPFS state.
2. If fast: copy `.prover-state/cycle_182_draft_section441.lean`
   to `OpenMath/Chapter4/Section441.lean`, re-run compile, fix
   any specific errors.
3. If still slow: try `lake build OpenMath.Chapter4.Section441`
   with longer patience (estimate 20–40 minutes); or try
   submitting just the Section441.lean file to Aristotle as a
   "fill in the sorries" job (even though there are no sorries,
   Aristotle may report compile errors; this is fast if Aristotle
   accepts it, ~1–2 minutes).
4. On clean compile: update `lean_status.json`, `plan.md`,
   `lem_441A_phase_C_scoping.md`, `cycle_183.md` to record Phase
   C.2 closure. Then proceed to Phase C.3 per the scoping doc.

## Files modified by cycle 182 (final state)

* `.prover-state/task_results/cycle_182.md` — created
* `.prover-state/issues/cycle_182_gpfs_slowness.md` — created (this file)
* `.prover-state/cycle_182_draft_section441.lean` — created
  (preserved Phase C.2 proof draft)
* `OpenMath/Chapter4/Section441.lean` — reverted to HEAD; no net change

## Cross-references

* Cycle 181 issue `phantom_commit_verdict_pattern.md` — different
  filesystem-related issue (commit verdict false positives), not
  related to today's slowness.
* CLAUDE.md PATH note (`/tmp/lake-bin:/tmp/lean4-toolchain/bin`):
  this workaround IS in effect; doesn't fix today's GPFS read
  slowness.
