# Cycle 372 Results

## Worked on
- Theorem 359C (Iserles §3.5.9): classical collocation families are
  algebraically stable.
- New file `OpenMath/CollocationFamilies.lean` (124 lines, zero sorry's).

## Approach
- Applied Theorem 358A (closed cycle 371) to the Gauss–Legendre case via a
  one-line bridge `gaussLegendreNodes_hasAlgStabilityBoundaryNodes`:
  `algStabilityBoundaryPoly s 0 = shiftedLegendreStarPoly s` reduces θ=0 to
  the existing GL-node hypothesis through `shiftedLegendreStarPoly_eval`.
- Stated the abstract theorems:
  - `thm_359C_gaussLegendre`: collocation + GL nodes ⇒ algebraically stable
  - `thm_359C_radauI`: collocation + zeros of `P_s^* − P_{s-1}^*` ⇒
    algebraically stable (θ = 1)
- Added concrete corollaries reusing existing GL2/GL3 tableaux:
  - `rkGaussLegendre2_isCollocation`, `rkGaussLegendre2_hasGaussLegendreNodes`,
    `rkGaussLegendre2_algStable_via_358A`
  - GL3 analogs (proofs use existing `B(s)`, `C(s)`, `D(s)` lemmas plus
    `nlinarith` + `Real.sq_sqrt` for the injectivity of node values).

## Result
- SUCCESS.
- `OpenMath/CollocationFamilies.lean` compiles cleanly (`lake env lean
  OpenMath/CollocationFamilies.lean` after a /tmp-wipe rebuild of the lake
  cache and project oleans — see Discovery).
- `lake build` succeeds for the OpenMath target after the cache restore.
- 358A and 359C are now both closed; project remains at zero sorry's.

## Dead ends
- None for the math itself — Theorem 358A did all the work; 359C is a
  one-line θ = 0 specialization plus collocation/GL-node verifications for
  the concrete tableaux.

## Discovery
- The cluster's `/tmp` was wiped between cycles 371 and 372, dropping the
  NVMe `lean4-toolchain` and `OpenMath-lake` directories. The
  `restore_nvme.sh` script re-copies the toolchain but `lake exe cache get`
  re-builds the Cache binary, which fails because the bundled `clang`
  requires `GLIBC_2.29` while the host has `2.28`.
  Workaround: `LEAN_CC=$(which gcc) LIBRARY_PATH=/tmp/lean4-toolchain/lib:/tmp/lean4-toolchain/lib/lean lake exe cache get`
  (system gcc 8.5 builds the Cache binary; only Cache binary needs C
  compilation, the .olean build itself uses lean directly).
  This is the same blocker recorded in
  `.prover-state/issues/lake_cache_glibc_mismatch.md` — the gcc/LIBRARY_PATH
  path resolves it.
- `~/.cache/mathlib` had been replaced with a 1.1G prebuilt cache at
  `/gscratch/amath/vilin/.cache-mathlib/` (8014 .ltar files); symlinking
  resurrects the cache without any network round-trips
  (`Already decompressed 8010 file(s) ... No files to download`).

## Suggested next approach
- Pick the next downstream theorem in Iserles §3.5 after 359C. Radau IIA
  (θ = −1) is NOT directly accessible via 358A — keep the existing concrete
  Radau IIA proofs and look beyond 359C in the textbook.
- Encode the gcc/LIBRARY_PATH workaround into `restore_nvme.sh` so the next
  /tmp wipe self-recovers without manual intervention.
- Now that 358A and 359C are closed, consider committing
  `OpenMath/CollocationFamilies.lean` and updating `plan.md` accordingly
  (done in this cycle).
