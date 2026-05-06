# Cycle 1186 Results

## Worked on
`adamsBashforth9_toGLM_hasOrderGe3` — §530 LMM-as-GLM order ≥ 3 witness
for the 9-step Adams–Bashforth method, in
`OpenMath/LMMAsGLM/Section530Step9.lean`.

## Approach
Followed the AB8GE3 (cycle 1180) recipe verbatim with `s = 8 → 9` and
the shifted Nordsieck constant `C = s² − 2 β_s · s = 81` (since
`β_s = 0` for AB methods). Appended a new `AB9GE3` namespace after the
existing closed `AB9GE2` block, plus the headline theorem
`adamsBashforth9_toGLM_hasOrderGe3`.

Per the strategy and prior Fin 18 lessons (cycles 1178/1182/1184),
extracted **all eighteen rows** of both `q''_obligation` and
`q'''_obligation` as private helpers. Each helper closes with
`simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
qN, q'N, q''N, q'''N]` plus `norm_num` (with the boundary nuances
documented below).

## Result
SUCCESS — file compiles sorry-free in **2m12s** wall-clock
(`lake env lean OpenMath/LMMAsGLM/Section530Step9.lean`). All four
deliverables land:

1. Witness vectors `qN`, `q'N`, `q''N` (shifted by `C = 81`),
   `q'''N` (shifted by `C = 81` — past-`y` `j³ − 486 j`,
   past-`h·f` `3 j² − 486`).
2. 18 per-row `q''_obligation_*` helpers (k = 0..17).
3. 18 per-row `q'''_obligation_*` helpers (k = 0..17).
4. Top-level dispatchers `q'_obligation` (inline `fin_cases` —
   the order-1 obligation is light enough to fit), `q''_obligation`,
   `q'''_obligation`, and the headline
   `adamsBashforth9_toGLM_hasOrderGe3`.

## Shift constant
`C = 81 = 9²` (forced by the order-3 Nordsieck identity at the last
past-`h·f` row k = 17). Continues the rotation
AB7 → 49, AB8 → 64, AB9 → 81.

## Per-row tactic table actually used
- `q''_obligation_zero` (k = 0): `simp [...]; norm_num` ✓
  (Note: the strategy hinted this might close with `simp` alone,
  but here `norm_num` was needed and did *not* trigger
  "no goals to be solved". The non-zero `C = 81` shift in `q''N`
  past-`y` produces a numeric residue at k = 0 that `simp` alone
  does not close.)
- `q''_obligation_nine` (k = s = 9 boundary): `simp` alone ✓
  (matches AB8GE3 nuance — adding `norm_num` here would error)
- All other q'' rows (k = 1..8, 10..17): `simp + norm_num` ✓
- All 18 q''' rows: `simp + norm_num` ✓
- `q'_obligation`: inline `fin_cases k; all_goals simp [...]; all_goals norm_num`
  (matches AB9GE2 — at Fin 18 the GE1 obligation still fits inline)

## Dead ends
None. The recipe transferred mechanically from AB8GE3 with the
expected literal substitutions (`8 → 9`, `Fin 16 → Fin 18`,
`64 → 81`, `192 → 243`, `384 → 486`, `adamsBashforth8 →
adamsBashforth9`).

## Discovery
For the AB9GE3 q''-obligation, `q''_obligation_zero` (k = 0) does
**need** the trailing `norm_num` — unlike the AB9GE2 unshifted
case (cycle 1184, `q''N` past-`y` is `j²` with no shift) where
the same row closes with `simp` alone. The shift `C = 81 ≠ 0` in
the AB9GE3 `q''N` past-`y` template (`j² − 81`) injects a numeric
constant that `simp` does not normalise away. This matches AB8GE3
(cycle 1180), where the analogous k = 0 row also needed `norm_num`.

The boundary k = s = 9 row remains `simp`-only on the q''-side:
the V matrix at row s on the `Fin (2 * 9)` GLM expansion produces
a structural identity rather than a numeric residue when `β_s = 0`.

## Suggested next approach
Per the planner note: next cycle should land **AM9 GE2** (Adams–
Moulton 9-step, unshifted natural Nordsieck template at Fin 18).
Mirror AM8GE2 from cycle 1182 with `s = 8 → 9`. Subsequently:

- AM9 GE3 — shifted Nordsieck with `C = s² − 2 β_s · s` for AM9's
  `β_s` (AM is implicit so `β_s ≠ 0`; compute `C` from the
  AM9 leading coefficient).
- BDF8 GE2 / GE3 — fills the BDF8 gap before BDF9 begins.

Each step is mechanical and follows the AB9GE3 template above with
`s` and `C` updated to the appropriate values.

## Build profile
`lake env lean OpenMath/LMMAsGLM/Section530Step9.lean`: 2m12s
wall-clock, well inside the 8-minute halting budget. The full file
is now ~770 lines (was 256 pre-cycle), still far below the 3000-line
soft cap.
