# Cycle 1134 Results

## Worked on

§530 LMM-as-GLM `HasOrderGe3` — the s=4 family in
`OpenMath/LMMAsGLM.lean`:

1. **Primary target**: `adamsBashforth4_toGLM_hasOrderGe3`
   (shift `C := 16`, β_s = 0, explicit).
2. **Stretch target**: `bdf4_toGLM_hasOrderGe3`
   (shift `C := 304/25`, β_s = 12/25, implicit).

Both landed in this cycle.

## Approach

Followed the strategy literal recipe from cycles 800/802/1132 — open a
private `*GE3` namespace, define four `Fin (2*4) → ℝ` Nordsieck vectors
qN/q'N/q''N/q'''N with the shift `j² − C` and `j³ − 3·C·j`, factor the
q''' obligation as a `private theorem` taking `k : Fin 8`, then
discharge the eight cases via `fin_cases k` + per-case
`simp [LMM.toGLM, <method>, Fin.addCases, Fin.sum_univ_succ,
qN, q'N, q''N, q'''N]; norm_num` blocks.

The four parent-theorem subobligations (preconsistency `V·q = q`, `U·q
= 1`, q' Nordsieck, q'' Nordsieck) discharge inline via `intro k;
fin_cases k; all_goals simp [...]; all_goals norm_num`, exactly like
AB3GE3/BDF3GE3/AM3GE3.

## Result

**SUCCESS** — both AB4 and BDF4 `HasOrderGe3` witnesses compile with
zero errors and zero new heartbeat warnings. Total ≈180 lines added to
`OpenMath/LMMAsGLM.lean`; file now at 2626 lines, under the 3000-line
soft cap.

Each landed as its own commit:
- `Cycle 1134: §530 adamsBashforth4 toGLM HasOrderGe3 with C=16`
- `Cycle 1134: §530 bdf4 toGLM HasOrderGe3 with C=304/25`

## Dead ends

The k = 7 case of the q''' obligation (the very last `Fin 8` case) hit
the 200000 heartbeat ceiling on a single inline
`simp [...]; norm_num` block in **both** AB4 and BDF4. The strategy
fallback hierarchy was:

1. `simp [...]; norm_num` (full simp set) — **timeout**.
2. `simp only [...]; norm_num` (simp_only with explicit lemma set) —
   also **timeout**, this time at the `whnf` reducibility stage rather
   than `isDefEq`.
3. Factor the case into its own `private theorem
   q'''_obligation_seven` with `k = (⟨7, by decide⟩ : Fin 8)` inlined
   so the helper gets a fresh heartbeat budget — **success** for both
   AB4 and BDF4.

The k = 0..6 cases all close inline with `simp + norm_num`. The
asymmetry at k = 7 makes sense: in `Fin 8` with the natural
`Fin.sum_univ_succ` unfolding, the inner triple sums `B 7 j * (A j i *
... + U j l * q'N l + ...)` produce terms whose `Fin 8` value-of-`Fin
8` reductions reach the deepest part of the `Fin.cast` chain — `7` is
the last case, so every `succ` rewrite hits before the value reduces.

## Discovery

- The "factor the failing case into a fresh private theorem" recipe
  works at `Fin 8` exactly as the strategy predicted. The fresh
  heartbeat budget is sufficient on its own; no additional tactic
  tuning needed in the helper.
- `(⟨7, by decide⟩ : Fin 8)` is a clean way to spell the literal
  index in the helper's statement; `fin_cases k` produces a goal
  shape that matches this literal under the `simp + norm_num`
  rewrite path used inside the helper, so the parent-theorem
  `· exact q'''_obligation_seven` discharge is direct.
- BDF4's `25`-denominator rationals (from β_s = 12/25 ⇒ C = 304/25)
  pose no extra burden on `norm_num`. Wall-time per case felt
  comparable to AB4 in practice.
- The four parent-theorem subobligations ran identical recipes for
  both methods — no per-method tuning required.

## Suggested next approach

The natural §530 follow-up is `adamsMoulton4_toGLM_hasOrderGe3`. The
cycle 1134 strategy explicitly defers it: shift `C = 1189/90` plus
β_4 = 251/720 produces 720-denominator rationals that are expected to
push every `Fin 8` case toward the heartbeat ceiling. The s=4 fresh-
budget-helper recipe just landed for AB4/BDF4 should still apply, but
**every** case may need to be factored into its own helper, not just
k = 7.

A reasonable cycle 1135 plan:

1. Open `namespace AM4GE3` after BDF4GE3 (line ~2540).
2. Define qN/q'N/q''N/q'''N with shift `C := 1189/90`.
3. Try the inline q''' obligation first. If most cases time out
   (likely), proceed to step 4.
4. Factor each `Fin 8` case `q'''_obligation_at_k` k = 0..7 into its
   own private theorem (eight helpers, each with a fresh heartbeat
   budget). Then `fin_cases k; · exact q'''_obligation_at_zero; ...;
   · exact q'''_obligation_at_seven`.

If even the per-case helpers exhaust the budget at AM4 (because of
720-denominator rationals slowing `norm_num`), the next step is to
isolate the slow factor — try `simp only [LMM.toGLM, adamsMoulton4,
Fin.addCases, Fin.sum_univ_succ, qN, q'N, q''N, q'''N]; ring_nf;
norm_num` or split each case further into a "compute the LHS / RHS
literal" step + `norm_num` rationale. Alternatively, lift the closure-
row arithmetic into a helper computation that pre-rationalizes the
720-denominator coefficients.

After AM4 lands, the §530 LMM-as-GLM `HasOrderGe3` slate is complete
for the s ∈ {2, 3, 4} families. The s = 5 family (`adamsBashforth5`,
`adamsMoulton5`, `bdf5`) remains paused — cycle 786 confirmed even
the simpler `HasOrderGe2` witness for AB5 (`Fin 10`) times out at the
q' obligation.

## Build verification

```bash
lake env lean OpenMath/LMMAsGLM.lean
```

Zero errors. Zero `sorry`s in the new code. No new heartbeat warnings.
File at 2626 lines.
