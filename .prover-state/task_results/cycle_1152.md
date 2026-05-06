# Cycle 1152 Results

## Worked on

`bdf5_toGLM_hasOrderGe3` in `OpenMath/LMMAsGLM/Section530.lean`. This
was the BDF5 ge3 entry needed to close the §530 LMM-as-GLM ge3 ladder
for every consistent LMM in the repo with `s ≤ 5`.

## Approach

Followed the planner strategy verbatim:

1. Located the end of the BDF5GE2 / `bdf5_toGLM_hasOrderGe1` block at
   line 805 of `OpenMath/LMMAsGLM/Section530.lean`.
2. Appended a new `BDF5GE3` namespace by mirroring the `AM5GE3`
   namespace (cycle 1146) verbatim with the substitutions:
   - `AM5GE3` → `BDF5GE3`
   - `adamsMoulton5` → `bdf5`
   - `3125 / 144` → `2825/137` (the BDF5 shift constant
     `C := s² − 2 β_s s = 25 − 2·(60/137)·5 = 2825/137`)
3. Mirrored the AM5GE3 wrapper at the end (`bdf5_toGLM_hasOrderGe3`),
   using `all_goals simp + all_goals norm_num` for the `Fin 10` `U q = 𝟙`
   obligation as instructed.
4. Used the four-helper `q'''_obligation_{four,seven,eight,nine}`
   extraction pattern verbatim to give each heavy `Fin 10` case its
   own heartbeat budget.
5. Verified with `lake env lean OpenMath/LMMAsGLM/Section530.lean`.

## Result

SUCCESS. `lake env lean OpenMath/LMMAsGLM/Section530.lean` typechecked
in `2m59s` wall time (under the 3-minute strategy estimate, and well
under the 10-minute hard ceiling). No errors, no warnings, no sorry
introduced.

Diff is `+153 / -0` lines, all confined to
`OpenMath/LMMAsGLM/Section530.lean`. No other tracked files changed.

File size after the edit: 1525 lines (was 1372 lines), still well
under the 3000-line cap.

## Dead ends

None. The recipe transferred verbatim. The strategy correctly warned
that the `all_goals simp + all_goals norm_num` form (rather than the
single `simp; norm_num` used for `Fin 8` BDF4) is the right shape on
`Fin 10`, and the four-helper `q'''_obligation` extraction was needed
to keep each heavy row inside the 200000 heartbeat budget.

## Discovery

The mechanical-substitution recipe for the §530 ge3 ladder is now
fully shape-stable on `s = 5` LMMs:

  - The shift `C := s² − 2 β_s s` parametrizes both `q''N` and
    `q'''N` and only appears in `(q''_obligation, q'''_obligation*)`
    obligations — `q'_obligation` and `qN/q'N` are independent of `C`.
  - For `s = 5` (`Fin 10`), the rows that exhaust the heartbeat budget
    inline are `k ∈ {4, 7, 8, 9}`; the four extracted helpers are
    independent of the LMM weights as a syntactic shape, only the
    referenced `bdf5` / `adamsMoulton5` / `adamsBashforth5` constant
    differs.
  - The `all_goals simp + all_goals norm_num` `Fin 10` U-row pattern
    is needed to discharge all ten case-goals; the BDF4-style
    `simp; norm_num` form does not transfer because `Fin 8` only has
    eight cases and the inline `simp; norm_num` exhausts the budget
    sooner on the larger row count.

`C = 2825/137 ≈ 20.62` for BDF5; vs the BDF ladder so far:
`C(BDF1) = −1`, `C(BDF2) = 4/3`, `C(BDF3) = 63/11`, `C(BDF4) = 304/25`,
`C(BDF5) = 2825/137`. The denominator is `137`, slightly heavier than
AM5's `144`, but `norm_num` had no trouble.

## Suggested next approach

The §530 LMM-as-GLM ge3 ladder is now closed for every consistent
LMM in the repo with `s ≤ 5`:

| method        | ge2 | ge3 |
| ------------- | --- | --- |
| AB4 / BDF4    | ✓   | ✓   |
| AM4           | ✓   | ✓   |
| AB5 / AM5     | ✓   | ✓   |
| BDF5          | ✓   | ✓   |  ← cycle 1152

Order-4 is **structurally blocked** for any consistent LMM with
`B = ∑β ≠ 0` (cycle 1138 obstruction in
`.prover-state/issues/cycle_1138_am3_hasOrderGe4_obstruction.md`),
which includes every method in the table above.

Per the strategy's "After this cycle" section, the planner should:

1. **Promote** the cycle 1138 algebraic obstruction into
   `disproven.md` so future planner cycles do not propose order-4
   LMM-as-GLM witnesses. The disproven entry should restate that the
   `r = 2 s` Nordsieck template caps at order 3 for any consistent
   LMM with `B ≠ 0`.
2. **Pivot away from §530 LMM witnesses**. Candidate next frontiers
   from the strategy backlog:
   - §215 Euler asymptotic error formula
   - §522 Butcher–Chipman outline
   - §523 GLM algebraic stability
   - §530 RK-side ge3 / ge4 ladder (RK has `r = 1`, not `r = 2 s`,
     so the cycle 1138 obstruction does not apply — order 4 may be
     achievable)
3. **Do NOT** propose `bdf5_toGLM_hasOrderGe4` (structurally blocked).
4. **Do NOT** propose 6-step LMM ge3 entries (e.g. `adamsMoulton6`)
   without first scoping the `Fin 12` heartbeat-budget exploration —
   the four-helper recipe extracted at `s = 5` was already at the
   edge of the inline budget on heavy rows.

The §530 RK-side ladder is the most natural next §530 target: the
cycle 1138 obstruction is `B ≠ 0`-specific, and Runge–Kutta methods
have a different Nordsieck embedding (`r = 1`).
