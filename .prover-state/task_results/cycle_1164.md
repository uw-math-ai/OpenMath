# Cycle 1164 Results

## Worked on
`bdf6_toGLM_hasOrderGe3` in `OpenMath/LMMAsGLM/Section530.lean`. This
closes the last missing rung of the §530 LMM-as-GLM order-≥ 3 rotation
for 5-/6-step methods (AB5/AM5/BDF5, AB6/AM6 already landed; BDF6
HasOrderGe2 landed cycle 1162; BDF6 HasOrderGe3 landed this cycle).

## Approach
Mechanical mirror of `BDF5GE3` (cycle 1152) with `Fin 10 → Fin 12`,
`bdf5 → bdf6`, `Nat.two_mul 5 → Nat.two_mul 6`, and shift constant
`2825/137 → 1524/49` (since BDF6 has `β_s = 60/147 = 20/49`, giving
`C = 36 − 2·(20/49)·6 = 1524/49`). Per-row helper extraction at Fin 12
following the BDF6GE2 (cycle 1162) and AM6GE3 (cycle 1160) layouts:

- `qN`, `q'N`, `q''N`, `q'''N` Nordsieck vectors with the shift on
  past-`y` slots of `q''N` and `q'''N`.
- `q'_obligation` (Fin 12) inline.
- `q''_obligation` with seven per-row helpers (k = 5..11) plus inline
  k = 0..4 dispatcher.
- `q'''_obligation` with eight per-row helpers (k = 4..11) plus inline
  k = 0..3 dispatcher.
- Headline `bdf6_toGLM_hasOrderGe3` mirrors `bdf5_toGLM_hasOrderGe3`
  using `bdf6_consistent` and `bdf6.toGLM_V_nordsieckQ_eq`.

## Result
SUCCESS. `lake env lean OpenMath/LMMAsGLM/Section530.lean` runs clean
in 3m08s. File grew by ~280 lines (now 2747 lines, well under the
3000-line soft cap).

## Dead ends
First build attempt failed with "no goals to be solved" at the BDF6GE3
`q''_obligation_six` helper (k = 6 row). The `simp [...]; norm_num`
combo over-tactic'd that branch — `simp` already closed the goal due
to the algebraic shape of the closure row (the past-`h·f` `β_s` slot
contribution combines with the constant shift to leave nothing for
`norm_num`). Fix per the strategy's documented quirk: drop the
trailing `norm_num`, leaving `simp [...]` alone for k = 6. This
matches the same nuance seen in BDF6GE2 (cycle 1162) and AM6GE2
(cycle 1158); the strategy correctly anticipated it.

Note: only `q''_obligation_six` had the quirk for BDF6GE3. None of
the q''' helpers needed the strip; they all closed cleanly with
`simp [...]; norm_num`.

## Discovery
- The k = 6 simp-only quirk is consistent across the BDF6/AM6 Fin-12
  family for `q''` only. q''' helpers always need `; norm_num`.
- The 49-denominator rationals from the `1524/49` shift posed no
  norm_num performance issue — wall time matched BDF5GE3
  (137-denominator) within 1m.
- The dispatcher `q''_obligation` itself does NOT need the simp-only
  treatment for k = 6 in BDF6GE3 (uses `exact q''_obligation_six`,
  delegating). Only the helper body needs the strip.

## Suggested next approach
With AB5/AM5/BDF5/AB6/AM6/BDF6 all at HasOrderGe3, the §530 LMM-as-GLM
order-≥ 3 rotation for 5-/6-step methods is complete. Per the
strategy's "What NOT to try" guard:
- HasOrderGe4 is structurally blocked (cycle 1138 issue file).
- BDF7 is zero-unstable; out of scope for §530.

Likely next-cycle targets per `plan.md`:
- Pivot back to `OpenMath/GeneralLinearMethod.lean` /
  `OpenMath/RKAsGLM.lean` (the original "current target files").
- Or extend §521/§522 charpoly work, §541/§542/§543/§525 blocks, or
  §38 group structure (whichever is currently unblocked per plan.md
  guard list).

The planner should consult `plan.md` `## Current Target` and recent
non-§530 task results to choose the next rotation.
