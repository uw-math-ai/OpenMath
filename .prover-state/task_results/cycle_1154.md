# Cycle 1154 Results

## Worked on

§530 LMM-as-GLM `HasOrderGe2` for Adams–Bashforth 6-step
(`adamsBashforth6_toGLM_hasOrderGe2`) — the s = 6 entry on the
LMM-as-GLM ladder. Headline target landed sorry-free in
`OpenMath/LMMAsGLM/Section530.lean` (lines 952–1106), inserted right
below the existing `bdf5_toGLM_hasOrderGe3` so the s ≤ 6 block
clusters.

## Approach

Mirrored the AB5GE2 recipe verbatim (cycle 1140) with `Fin 10 →
Fin 12` and `adamsBashforth5 → adamsBashforth6`. New private
namespace `AB6GE2` carries:

- `qN`, `q'N`, `q''N : Fin (2 * 6) → ℝ` — the natural Nordsieck
  Taylor template (no `C₂` shift, since GE2 obligations don't feel
  the `s² − 2 β_s s` constant — that enters at GE3).
- `q'_obligation` — single `fin_cases k <;> simp ...; all_goals
  norm_num`, fits in budget at `Fin 12`.
- `q''_obligation` — required per-row helper extraction (see
  below).

Public theorem `adamsBashforth6_toGLM_hasOrderGe2` assembles via
`refine ⟨…⟩` plus the closure-row check on `qN`.

## Result

**SUCCESS** — `lake env lean OpenMath/LMMAsGLM/Section530.lean`
reports a clean build (≈ 2 m 34 s). No sorrys introduced.

## Heartbeat split

Inline `q''_obligation` at `Fin 12` blew the 200000 heartbeat cap
(`(deterministic) timeout at whnf` at the theorem header). The
`q'_obligation` body was fine — the q'' nested A-and-Uq' combinator
inside the B-sum is what tipped it over. The fix replicates the
AB5GE3 cycle 1142 recipe: extract heavy rows as private
`q''_obligation_five .. q''_obligation_eleven` theorems (one per
row for k = 5..11; rows k = 0..4 still close inline). Each helper
just runs `simp [...]; norm_num` (or just `simp [...]` for k = 6,
where the natural ratios already collapse).

Two minor surprises forced one-line tweaks:

1. `q''_obligation_six` (first past-h·f row, j = 0) closes with
   `simp` alone — adding `; norm_num` produced "no goals to be
   solved" and had to be dropped.
2. The `k = 0` case inside the master `q''_obligation` body is
   the same — `simp` alone suffices.

In both cases the `; norm_num` was deleted. All other rows still
need the trailing `norm_num` (β coefficients are dyadic rationals
with denominators 1440, so `simp` reduces but does not normalize).

## Dead ends

None — the AB5GE2 recipe transferred cleanly. The only cost was
heartbeat-driven row extraction for q''.

## Discovery

- AB family at `Fin 12` needs per-row q'' extraction at level 2,
  not just at level 3. This is one rung lower than AB5GE3 (which
  was the first cycle in the AB ladder where row extraction was
  required); for AB6, row extraction starts at GE2 because the
  larger `Fin 12` widens the per-row simp work past the cap.
- The `simp`-only rows (k = 0 and k = 6 for q'') are the trivial
  past-y / past-h·f boundary indices: `qN ⟨0, _⟩ = 1, q'N ⟨0, _⟩ =
  0` (and analogous for k = 6, j = 0 of the past-h·f block) leaves
  a structural identity that simp's defeq machinery closes outright.
- File grew from 1525 → 1664 lines (+139 LOC), still well under
  the 3000-line module cap.

## Suggested next approach

Per the strategy's stretch ladder, the natural cycle 1156 / 1158 /
1160 sequence is:

1. **AB6GE3** — same recipe with `q'''N` Taylor template plus
   `C₂ = s² − 2 β_s s = 36 − 0 = 36` shift on past-y q'' / q'''
   rows (since β_s = 0 for AB6, the AB3 / AB5 form `q'''_{past-y j}
   = j³ − C₂ j` and `q'''_{past-h·f j} = 3 (j² − C₂)` is the
   correct template). Expect the AB5GE3 row-extraction pattern to
   need analogous helpers at all of k = 5..11 plus possibly some
   late past-y rows; budget per build ≈ 2.5 m on this file.
2. **AM6GE2** — implicit, `β_s = 19087 / 60480 ≠ 0`. AM5GE2 cycle
   1144 used the `simp`-only closure row (no trailing `norm_num`);
   AM6GE2 may pattern likewise. Per-row q'' extraction will likely
   be required at `Fin 12`.
3. **AM6GE3** — implicit, `β_s = 19087 / 60480`, so
   `C₂ = 36 − 2 · (19087 / 60480) · 6 ≠ 0` — the AM2 / AM5 shifted
   template applies. Same row-extraction expectation.
4. **BDF6GE2 → BDF6GE3** — BDF6 has `α = ![−12/147, 75/147, …]`
   and `β_s = 60/147`. Mirrors BDF5 cycles 1148/1150/1152.

Do **not** attempt `HasOrderGe4` for any s = 6 LMM — the cycle 1138
obstruction (entry #1 of `disproven.md`) applies identically.

## Mechanical notes for the next worker

- The split point `k = 5` for q'' helpers (rather than `k = 6`)
  came up because `k = s − 1 = 5` is the "last past-y" row in the
  Fin 12 enumeration — the asymmetric cell where past-y meets the
  past-h·f boundary, which has historically been heavy across
  AB5GE3 (cycle 1142) and BDF5GE3 (cycle 1152). For q''' the
  expected heavy rows are the same: `k = 5, 6, 7, …, 11`.
- Keep the cycle-1142 `⟨n, by decide⟩ : Fin 12` index pattern
  inside helpers; `decide` discharges the `Fin` membership cleanly
  at compile time.
