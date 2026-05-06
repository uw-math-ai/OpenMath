# Cycle 1142 Results

## Worked on
`adamsBashforth5_toGLM_hasOrderGe3` in `OpenMath/LMMAsGLM.lean` — the
§530 LMM-as-GLM order-≥ 3 witness for AB5 (`s = 5`, `Fin 10`, explicit
with `β_s = 0`, classical order 5). Shift constant `C := 25 = 5² −
2·0·5`, matching the AB ladder AB2→1, AB3→9, AB4→16, AB5→25.

## Approach

Mirrored the cycle-1134 `AB4GE3` recipe with `s = 5`, `Fin 10`, and
`C = 25`. Added a new `namespace AB5GE3` block immediately after the
cycle-1140 `adamsBashforth5_toGLM_hasOrderGe2` block.

Step 1 (Nordsieck vectors) was a direct transcription. The interesting
work was Step 2 (q''' obligation on `Fin 10`) and Step 3 (top-level
HasOrderGe3 obligations).

## Result

**SUCCESS** — `adamsBashforth5_toGLM_hasOrderGe3` compiles sorry-free.
Wall time ~2m04s on `lake env lean OpenMath/LMMAsGLM.lean`.

## What worked

The cycle-1140 recipe of "extract each derivative obligation as its own
private theorem with `all_goals simp; all_goals norm_num`" generalises
to HasOrderGe3 on `Fin 10`. Concretely, the AB5GE3 namespace contains:

- `qN`, `q'N`, `q''N`, `q'''N` — Nordsieck Taylor templates with shift
  `C = 25` on past-`y` derivative slots ≥ 2.
- `q'_obligation` — single private theorem,
  `all_goals simp; all_goals norm_num`.
- `q''_obligation` — single private theorem,
  `all_goals simp; all_goals norm_num`.
- `q'''_obligation_four`, `_seven`, `_eight`, `_nine` — four
  per-case helpers, each with its own fresh 200000 heartbeat budget.
- `q'''_obligation` — `fin_cases k` dispatcher, six inline
  `· simp; norm_num` blocks plus four `· exact q'''_obligation_<k>`.

The top-level theorem then becomes a flat `refine` with the three
extracted obligations passed positionally; only the V·q row (Nordsieck
lemma) and the U·q row (`Fin 5` `intro i; fin_cases i; all_goals simp`)
remain inline.

## Dead ends

1. **First attempt**: AB4GE3-style template, with only the
   `k = 4` and `k = 9` cases preemptively extracted from the q'''
   obligation (per the strategy hint), and the top-level q'/q'' rows
   inline as `intro k; fin_cases k; all_goals simp; all_goals norm_num`.

   Failed with four heartbeat blowups:
   - `q'''_obligation` k=7 inline simp timeout.
   - `q'''_obligation` whnf timeout (umbrella, downstream of k=7).
   - Top-level q''-row `all_goals simp; all_goals norm_num` timeout.

   This confirms the strategy's prediction that on `Fin 10` the
   AB4GE3 single-case-extraction pattern is not sufficient.

2. **Second attempt**: switching the top-level q'-row and q''-row to
   per-case `· simp [...]; norm_num` blocks (the cycle-1134 budget-safe
   shape on `Fin ≥ 8`).

   This produced **two** new failure modes:
   - "No goals to be solved" errors from `norm_num` on cases where
     `simp` already closed the goal (top-level q'-row, multiple
     branches; this didn't happen for AB4GE3 because the `Fin 8` AB4
     q'-row never closes by simp alone).
   - Heartbeat timeouts on the q''-row per-case form, because each
     `simp [...]` invocation on `Fin 10` with the full `B (A + U·q')`
     chain plus `q''N` (with the `−25` shift) is itself >200000
     heartbeats.

   The `· simp; norm_num` form per case is **not** safe on `Fin 10`
   for the q''-row when q''N carries a shift — even with a fresh
   budget per case, simp on the full chain blows the limit. Cycle 1134
   noted this for the q'''-row k=7 on AB4 (the heaviest expansion);
   here the same blow-up shows up in the q''-row at *every* shifted
   `Fin 10` case.

3. **Third attempt (the working shape)**: extract `q'_obligation` and
   `q''_obligation` as their own private theorems inside `namespace
   AB5GE3`, mirroring the cycle-1140 AB5GE2 pattern that already
   verified `Fin 10` q'/q'' worked. Inside each helper, `fin_cases k;
   all_goals simp; all_goals norm_num` succeeds because:
   - The simp-closes-goal cases are absorbed by `all_goals norm_num`
     (which is a no-op when no goals remain), avoiding the "no goals
     to be solved" error from per-case form.
   - Each helper gets its own 200000 budget, so the cumulative cost
     of all 10 simps + all 10 norm_nums fits.

## Discovery

1. **`Fin 10` q''-row extraction discipline**. Even with a fresh
   per-case budget, `· simp [...]; norm_num` on a single `Fin 10`
   q''-row can exceed 200000 heartbeats when q''N has a non-zero
   shift constant. The robust pattern is to extract the **entire
   q''-row as a private theorem** with `fin_cases k; all_goals simp;
   all_goals norm_num`, which gives the *fin_cases-dispatcher* its
   own budget while keeping `all_goals` able to skip cases simp
   already closed. This is what cycle 1140 did for AB5GE2 and what
   needs to be lifted to AB5GE3.

2. **`· simp; norm_num` vs `all_goals simp; all_goals norm_num`**.
   The cycle-1134 per-case form (`· simp; norm_num`) silently assumes
   simp leaves a residual goal for norm_num. On `Fin 10` shifted
   templates this assumption breaks — `simp` sometimes closes the
   case and norm_num errors with "no goals to be solved". Using
   `all_goals simp; all_goals norm_num` inside an extracted helper
   tolerates both shapes.

3. **AB ladder shift constants are stable through HasOrderGe3**.
   `C := s² − 2 β_s s` continues to give a clean `q'''_obligation`
   close on AB5 (`C = 25`). No ad-hoc adjustment needed when stepping
   from `s = 4` to `s = 5`.

## Suggested next approach

Cycle 1143: target `adamsMoulton5_toGLM_hasOrderGe2` (AM5 is implicit,
`s = 5`, `Fin 10`, `β_s ≠ 0`). The Nordsieck template is the cycle
1140 unshifted AB5GE2 shape (HasOrderGe2 doesn't need the shift). If
AM5 is in `OpenMath/AdamsMethods.lean` with a corresponding
`adamsMoulton5_consistent`, this is a direct AB5GE2 transcription.

Cycle 1144 onward: AM5 HasOrderGe3 (with shift `C = 25 − 2·β_s·5`),
then BDF5 HasOrderGe3 if BDF5 is defined. The cycle 1142 recipe —
extract every derivative obligation as a private theorem, factor the
heaviest q'''-row cases as separate helpers — is the load-bearing
template for `Fin 10` order-3 LMM-as-GLM witnesses.

**Do not** attempt HasOrderGe4 for any LMM. The cycle-1138 obstruction
(`B = ∑β = 0` vs consistency `B ≠ 0`) is structural for the cycle-1132
r=2s template.

## Reference points

- AB5GE3 final shape: `OpenMath/LMMAsGLM.lean:1727–1857`
  (immediately after `adamsBashforth5_toGLM_hasOrderGe2`).
- AB5GE2 (cycle 1140) — the proven `Fin 10` q'/q''-row template that
  this cycle lifts to HasOrderGe3.
- AB4GE3 (cycle 1134) — the q'''-row per-case extraction recipe.
