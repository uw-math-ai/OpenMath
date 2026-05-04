# Cycle 800 Results

## Worked on
§530 LMM-as-GLM order-≥ 3 witness for `adamsBashforth3` (the cycle 800
must-land target). Determined the shift constant `C₂ = 9` for the
shifted Nordsieck template, factored the q''' obligation into a
private helper to fit the default `maxHeartbeats 200000` budget, and
landed `adamsBashforth3_toGLM_hasOrderGe3` sorry-free.

## Approach
1. **First pass — unshifted template (`C₂ = 0`)**. Tried the natural
   Taylor template `q'' = j², 2j` and `q''' = j³, 3j²` (no shift). The
   q''' obligation at `k = 5` (last past-`f` row, where `B[5,0] = 1`)
   reduced to `54 = 27`, off by `(U q'')_0 = 9`.

2. **Determined `C₂` by computing `(U q'')_0`**. With unshifted q'':
   - past-`y` contribution: `−α₂ · 2² = 1 · 4 = 4`
   - past-`f` contribution: `β₀ · 0 + β₁ · 2 + β₂ · 4 = −32/12 + 92/12 = 5`
   - total: `(U q'')_0 = 9`

   This matches the cycle 780 formula `C := s² − 2 β_s s = 9 − 0 = 9`
   for `s = 3, β_s = 0`. The shift `C₂ := 9` forces `(U q'')_0 = 0`.
   Because `β_s = 0` the q'' obligation has no shift constraint at the
   closure row (the `β_s · c_0` term vanishes), so `C₂` is free at level 2;
   `C₂ = 9` is forced by level 3.

3. **Witness at `C₂ = 9`**:
   - `q_{past-y j} = 1, q_{past-f j} = 0`
   - `q'_{past-y j} = j, q'_{past-f j} = 1`
   - `q''_{past-y j} = j² − 9, q''_{past-f j} = 2 j`
   - `q'''_{past-y j} = j³ − 27 j, q'''_{past-f j} = 3 (j² − 9)`

4. **Tactic restructuring for heartbeat budget**. With the witness in
   hand, `all_goals simp [LMM.toGLM, ...]; all_goals norm_num` on the
   q''' obligation timed out at default 200K budget (q'' / q' / q
   obligations all close fine). Splitting per `fin_cases k` branch did
   *not* help inside the parent theorem — case `k = 3` still timed out
   in `simp` at `isDefEq`. The fix that worked: factor the q'''
   obligation into a private helper theorem `AB3GE3.q'''_obligation`
   so each `fin_cases k` branch gets a fresh heartbeat budget. The
   four Nordsieck vectors are also extracted as `private noncomputable
   def`s (`qN, q'N, q''N, q'''N`) — this avoids the elaboration cost of
   inlined `fun k => Fin.addCases ...` closures appearing in the parent
   theorem's `refine ⟨..., ?_⟩`.

5. **No projection corollaries added**. `adamsBashforth3_toGLM_hasOrderGe1`
   already exists (line 1658) and `adamsBashforth3_toGLM_hasOrderGe2`
   already exists (line 1779) as direct witnesses, so the new GE3 only
   adds the missing slot. The strategy noted the primed `_hasOrderGe1'`
   projection is "optional and may be skipped if the primary lands clean."

## Result
SUCCESS. `adamsBashforth3_toGLM_hasOrderGe3` lands sorry-free.
`OpenMath/LMMAsGLM.lean` builds clean (`lake env lean` exits 0,
~85 seconds wall, 2298 lines total — under the 3000-line cap).

## Dead ends

### Per-case `· simp ...; norm_num` inside parent theorem still times out
Splitting the q''' obligation into six `·` blocks inside the main theorem
did *not* close in 200K heartbeats. Specifically `case k = 3` (past-`f`
j = 0 row) timed out in `simp` at `isDefEq`. The mathematical residual
after `simp` is trivially `3 * (1 - 9) = 3 + -(3 * 9)` — the budget is
spent inside `simp`'s `isDefEq` checks against `Fin.addCases` /
`Fin.cast` / the inlined Nordsieck closures, not on the arithmetic.

### `simp only` with curated lemma list — not attempted
The cycle-800 strategy suggested `simp only [...]` over bare `simp` to
shrink the rewrite set. Not attempted because the helper-extraction
approach worked first try and the curated lemma list would be brittle
to edit. If a future cycle needs to land BDF3 GE3 (cycle 780 stretch
that hit the same `Fin 6` wall), the helper-extraction recipe used here
is the recommended template — simpler than building a `simp only` list.

## Discovery

**Helper-extraction recipe for `Fin 6+` GLM obligations.** When the
q''' (or higher) Taylor obligation in a `HasOrderGeN` witness exhausts
the 200K heartbeat budget under bare `all_goals simp; all_goals norm_num`,
the per-`·`-block split inside the parent theorem is *not* sufficient.
The reliable recipe is:

1. Extract the Nordsieck vectors as `private noncomputable def`s in a
   helper namespace (e.g. `AB3GE3.qN`, `AB3GE3.q'N`, ...).
2. Extract the heaviest obligation as a `private theorem` whose
   statement explicitly lists the GLM `B/A/U/V` sums and the named
   Nordsieck vectors.
3. Discharge it with `fin_cases k` followed by per-`·`-block
   `simp [LMM.toGLM, <method>, Fin.addCases, Fin.sum_univ_succ,
   <Nordsieck names>]; norm_num`. Each branch gets a fresh budget.

This recipe should also unlock the cycle-780 BDF3 GE3 stretch
(`bdf3_toGLM_hasOrderGe3`), which failed at the same `Fin 6` wall under
identical tactic structure. The shift constant for BDF3 was already
computed in cycle 780 (`C = 63/11`); the missing ingredient was the
helper-extraction structure.

**Why the parent theorem's per-case split fails but the helper succeeds.**
Hypothesis: the `refine ⟨..., ?_⟩` elaboration over four inlined
`fun k => Fin.addCases ...` Nordsieck closures leaves residual
metavariables / context that simp's isDefEq has to traverse on every
goal. Extracting the closures as named `private noncomputable def`s
breaks the chain and lets `unfold` operate on opaque names. This is
specifically a `Fin 6+` problem — `Fin 4` (AM2 GE3) has enough budget
slack to absorb the elaboration cost.

## Suggested next approach

1. **Cycle 802** — Apply the helper-extraction recipe to land
   `bdf3_toGLM_hasOrderGe3`. The cycle 780 witness algebraically
   verified `C = 63/11`; structure the proof exactly like
   `adamsBashforth3_toGLM_hasOrderGe3` (private namespace `BDF3GE3`,
   private Nordsieck defs, private q''' obligation, main theorem).

2. **Cycle 804+** — Extend to `adamsMoulton3_toGLM_hasOrderGe3` (s = 3,
   implicit, β_s = 9/24 = 3/8, order 4). The shift constant is
   `C = s² − 2 β_s s = 9 − 9/4 = 27/4`. Same helper-extraction recipe.

3. **Cycle 806+** — Once three more `Fin 6` GE3 witnesses (BDF3, AM3,
   AB3 already done) land via this recipe, consider extracting a
   shared lemma `LMM.toGLM_hasOrderGe3_of_consistent_of_shift` that
   abstracts the shifted Nordsieck template and reduces per-method work
   to verifying the shift constant `C := s² − 2 β_s s` and one numerical
   identity. This generalizes the cycle 780 pattern to a bridge.

4. **Avoid** retrying the cycle 786 AB5/AM4/BDF5 `HasOrderGe2` cases on
   `Fin 10` — those exhausted budget on the q'' obligation, not q'''.
   The helper-extraction recipe might help, but `Fin 10` doubles every
   sum size; expect the budget to still be tight even with extraction.
