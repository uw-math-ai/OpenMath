# Cycle 786 Results

## Worked on
§530 LMM-as-GLM order-≥1 / order-≥2 witnesses for the next concrete
methods (AB4, AB5, AM3, BDF3) in `OpenMath/LMMAsGLM.lean`. Followed the
cycle 786 strategy must-land list.

## Approach
Inserted five new theorems using the established Nordsieck Taylor
templates already in the file:

1. `adamsBashforth4_toGLM_hasOrderGe2` (s=4, explicit, no shift) —
   copied the AB3 template, swapping s/Nat.two_mul/Fin and the method
   name. Closed with `simp [LMM.toGLM, adamsBashforth4, Fin.addCases,
   Fin.sum_univ_succ]; norm_num` per row.
2. `adamsBashforth5_toGLM_hasOrderGe1` — one-line wrapper around
   `adamsBashforth5.toGLM_hasOrderGe1 adamsBashforth5_consistent`.
3. `adamsMoulton3_toGLM_hasOrderGe2` (s=3, implicit) — copied the BDF2
   template. Surprise: AM3 U·𝟙 row closes with `simp` alone — adding
   `norm_num` (as in BDF2) caused "No goals to be solved". Removed the
   trailing `norm_num` only on that one branch.
4. `adamsMoulton3_toGLM_hasOrderGe1` — order-projection from level 2.
5. `bdf3_toGLM_hasOrderGe2` (s=3, implicit) — copied BDF2 template
   verbatim, swapping `bdf2` → `bdf3`. The `simp; norm_num` U-row
   pattern transferred unchanged.
6. `bdf3_toGLM_hasOrderGe1` — order-projection from level 2.

## Result
SUCCESS — all five new sorry-free theorems land. Two commits:
- `374ca234e2` — AB4 HasOrderGe2 + AB5 HasOrderGe1
- `bc0bbddf07` — AM3 + BDF3 HasOrderGe2/HasOrderGe1

Total file compile time after additions: ~90s, well under any time
budget. No `maxHeartbeats` adjustments.

## Dead ends
- **Stretch goal `adamsBashforth5_toGLM_hasOrderGe2` (s=5, ten cases
  per obligation) hits the 200000 heartbeat cap.** The first
  `all_goals simp` on the q'-row obligation triggered a deterministic
  whnf timeout. Per strategy, dropped without sorry and without
  raising heartbeats. The strategy correctly anticipated this risk.
- AM3 U-row `norm_num` was unnecessary (simp closes alone). Trivial
  one-line fix; not really a dead end, but worth noting since the
  BDF2 template includes `norm_num` there.

## Discovery
- The natural Nordsieck Taylor template (no shift) closes the
  HasOrderGe2 obligations cleanly for **every** s ≤ 4 method we have,
  whether explicit (AB2/AB3/AB4) or implicit (BDF2/BDF3/AM3). The
  `(Uq'')_0`-shift only matters at HasOrderGe3.
- The `Fin (2 * s)` whnf cost in `simp` apparently scales sharply at
  s = 5: AB4 (8 slots, 8 cases) finishes well within budget, but AB5
  (10 slots, 10 cases) blows past the cap. This caps the *natural*
  template's reach at s = 4 unless someone optimizes the simp set or
  generalizes via a structured tactic.
- AM3's U-row identity is `1 = 1` post-simp (β_s ≠ 0 doesn't matter
  there because `(B 𝟙)_0 = ∑ β_j · 1 = ∑ β_j`, which AM3's
  consistency `∑ β_j = ρ'(1) = 1` matches). BDF2 needed `norm_num`
  because `∑ β_j` for BDF2 reduces to a coefficient combination
  requiring numeric closure. Both methods are implicit but the
  post-simp leftover differs.

## Suggested next approach
1. **Extend HasOrderGe1 one-liners**: BDF4, BDF5, BDF6 still lack
   `_toGLM_hasOrderGe1` witnesses. These are one-line wrappers around
   `_consistent` lemmas (if they exist; check `OpenMath/BDF.lean`).
2. **AM4 / AM5 HasOrderGe2**: same template as AM3, s=4 / s=5. AM4
   should compile (s=4 is below the heartbeat cliff that hit AB5);
   AM5 likely won't.
3. **AB5 HasOrderGe2** revisit only if someone introduces a
   structured tactic (e.g. an `LMM.OrderGe2_via_template` API that
   pre-discharges the four obligations using closed-form Nordsieck
   identities, bypassing the per-case `Fin.sum_univ_succ` blow-up).
   Without infrastructure changes, AB5 HasOrderGe2 stays out of
   reach under the 200000 heartbeat cap.
4. **BDF3 HasOrderGe3** stays disproven-by-budget per cycle 780; do
   not retry without a structured tactic.

## Cycle counts
- New tracked theorems: **5**
- Commits: **2** (cycle-782 message style)
- Dropped without sorry: **1** (AB5 HasOrderGe2 stretch)
- maxHeartbeats raises: **0**
- New tracked files: **0**
