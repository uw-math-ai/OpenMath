# Cycle 1166 Results

## Worked on
`adamsBashforth7_toGLM_hasOrderGe2` and the `HasOrderGe1` corollary in
`OpenMath/LMMAsGLM/Section530.lean`. Mirror of the AB6GE2 recipe
(cycle 1154) sized up from `s = 6` (Fin 12) to `s = 7` (Fin 14).

(Note: invoked under the cycle 1167 strategy that explicitly
supersedes the previous cycle 1166 plan; landing the AB7GE2 milestone
is the on-strategy work.)

## Approach
Appended a fresh `namespace AB7GE2` block at the end of
`Section530.lean` mirroring the AB6GE2 template byte-for-byte with
substitutions:

- `adamsBashforth6` → `adamsBashforth7`
- `Fin (2 * 6)`, `Fin 12` → `Fin (2 * 7)`, `Fin 14`
- `Fin 6` → `Fin 7` inside the `Fin.addCases` motives
- `Nat.two_mul 6` → `Nat.two_mul 7`

Per-row `q''_obligation_*` helpers extracted for `k ∈ {6, 7, 8, 9, 10,
11, 12, 13}` (last past-`y` row + seven past-`h·f` rows). `k = 0..5`
close inline inside `q''_obligation`'s `fin_cases` block — `k = 0`
closes with `simp` alone, `k = 1..5` with `simp; norm_num`.

The boundary nuance (AB6GE2 row `k = 6` closes with `simp` alone) sized
up to AB7 row `k = 7` (first past-`h·f` row, `β_s = 0`). Lean closed
that row with `simp` alone, exactly matching the predicted shape.

Headline followed by the trivial `HasOrderGe1` corollary via
`HasOrderGe2.toHasOrderGe1`.

## Result
SUCCESS. Both new theorems compile sorry-free.

- `lake env lean OpenMath/LMMAsGLM/Section530.lean` — exit 0,
  real time `3m9.8s` (user `13m38.8s`).
- `lake build OpenMath.LMMAsGLM` — exit 0 in `4.2s` (cached `.olean`s
  recompiled; only pre-existing simp-argument linter warnings in
  `OpenMath/BDF.lean`).

## File metrics
- `OpenMath/LMMAsGLM/Section530.lean` grew from **2737** lines to
  **2889** lines (+152). Still under the 3000 soft cap.
- New private theorems: 11 (3 nordsieck defs `qN`/`q'N`/`q''N`, plus
  `q'_obligation`, eight per-row `q''_obligation_*` helpers, and
  `q''_obligation`).
- New public theorems: 2 (`adamsBashforth7_toGLM_hasOrderGe2` and
  `adamsBashforth7_toGLM_hasOrderGe1`).

## Per-row tactic notes (for follow-ups)
- All eight per-row helpers and the inline `k = 0..5` cases closed with
  the **full** `simp [LMM.toGLM, adamsBashforth7, Fin.addCases,
  Fin.sum_univ_succ, qN, q'N, q''N]` simp set — no need to fall back to
  `simp only`.
- The `k = 0` and `k = 7` rows close with bare `simp` (no `norm_num`);
  every other row needs the `; norm_num` tail.

## Dead ends
None — first compile pass succeeded with no errors. The AB6GE2 → AB7GE2
size-up was strictly mechanical, exactly matching the cycle 1167
strategy's predicted shape.

## Discovery
- Heartbeat budget at `Fin 14` is comfortable for the AB7 coefficients
  with the per-row split. The file extension cost matches the
  predicted ~150 lines.
- The boundary nuance ("first past-`h·f` row closes with bare `simp`")
  generalises correctly from `s = 6` to `s = 7`. This is consistent
  with the structural reading: at `β_s = 0` the corresponding `B`-row
  contribution drops out cleanly.

## Suggested next approach
Per the cycle 1167 strategy's "After this cycle" section:

1. **Cycle 1167 (next)**: `adamsMoulton7_toGLM_hasOrderGe2` —
   implicit `s = 7`, `β_s = 36799/120960 ≠ 0`. Mirror AM6GE2 with
   `Fin 12 → Fin 14`. No shift needed for HasOrderGe2.
2. **Cycle 1168**: `adamsBashforth7_toGLM_hasOrderGe3` — extend AB7
   with the `C = s² − 2·β_s·s = 49` shift (since `β_s = 0` for AB),
   mirroring AB6GE3. Anticipate ~140 line cost; file would land at
   ~3030 lines, crossing the 3000 soft cap. **Either** split
   `Section530.lean` first (`Section530/Explicit.lean` for AB
   families, `Section530/Implicit.lean` for AM/BDF) **or** ship AB7GE3
   and split in the cycle that crosses 3000.
3. After that: backlog (§531 GLM local truncation, §215 Euler
   asymptotic error formula, §535 underlying one-step method).
