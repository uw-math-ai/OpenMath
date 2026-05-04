# Cycle 768 Results

## Worked on
§530 GLM order ≥ 3 layer: predicate + downward projection + RK bridge
+ four concrete witnesses, mirroring the cycle 766 order-2 layout.

## Approach
Followed the planner's strategy verbatim:

1. Added `HasOrderGe3` to `OpenMath/GeneralLinearMethod.lean` directly
   after `HasOrderGe2.toHasOrderGe1`. Same shape as `HasOrderGe2` plus
   one extra Nordsieck slot `q'''` and the third-derivative Taylor
   compatibility identity, with a `6 ·` leading factor matching the
   `h³/3!` coefficient.
2. Added the projection `HasOrderGe3.toHasOrderGe2` (5-line `obtain …
   exact`).
3. Added the §502 bridge `ButcherTableau.toGLM_hasOrderGe3` in
   `OpenMath/RKAsGLM.lean`. Witnesses `q ≡ 1`, `q' ≡ q'' ≡ q''' ≡ 0`
   collapse the four preconsistency / first-/second-derivative
   identities exactly as in `toGLM_hasOrderGe2`. The third-derivative
   identity reduces under the consistent-row-sum rewrite to
   `6 · ∑_j b_j (∑_i A_ji c_i) = 1`, which is `t.order3b` after the
   `Finset.mul_sum` reshape.
4. Added four concrete witnesses:
   - `rkSDIRK3_toGLM_hasOrderGe3` (uses `rkSDIRK3_order3`)
   - `rkRK4_toGLM_hasOrderGe3` (projects from `rk4_order4`, since
     `ExplicitRK` is not directly imported by `RKAsGLM`)
   - `rkGaussLegendre2_toGLM_hasOrderGe3` (projects from `_order4`)
   - `rkGaussLegendre3_toGLM_hasOrderGe3` (projects from `_order4`)

## Result
SUCCESS — all deliverables landed sorry-free. `lake build` is green
(8087 jobs).

## Dead ends
- The strategy suggested `rkRK4_toGLM_hasOrderGe3` could call
  `rk4_order3` directly, but `rk4_order3` lives in
  `OpenMath/ExplicitRK.lean`, which is **not** imported by
  `OpenMath/RKAsGLM.lean`. The strategy explicitly forbade adding
  imports, so the fix was to project order-3 directly out of
  `rk4_order4` (already in scope via `OpenMath.RungeKutta`), exactly
  as done for the Gauss–Legendre witnesses.
- After editing `GeneralLinearMethod.lean`, `lake env lean
  OpenMath/RKAsGLM.lean` initially returned a stale "Invalid field
  HasOrderGe3" error because the `.olean` for `GeneralLinearMethod`
  hadn't been rebuilt. Running `lake build OpenMath.GeneralLinearMethod`
  before the file-level check on `RKAsGLM.lean` fixed it. Worth
  remembering for future cycles that touch upstream definitions.

## Discovery
- The `Finset.mul_sum` + `mul_assoc` reshape that took `∑_j b_j (∑_i
  A_ji c_i)` to `∑_j ∑_i b_j A_ji c_i` and matched `order3b` worked on
  the first try; no `linear_combination` fallback was needed. The
  exact reshape:
  ```lean
  have hreshape : (∑ j, t.b j * ∑ i, t.A j i * t.c i)
                  = ∑ j, ∑ i, t.b j * t.A j i * t.c i := by
    simp [Finset.mul_sum, mul_assoc]
  ```
  This pattern should generalise to higher Taylor moments —
  `∑_j b_j (∑_i A_ji f(i))` reshaping to a flat double sum is a
  recurring shape and `simp [Finset.mul_sum, mul_assoc]` handles it.
- Pre-existing `simp` PANIC backtraces appear during `lake env lean
  OpenMath/RKAsGLM.lean` (at lines 436/491/512, all SDIRK2/SDIRK3
  stability-function proofs). They are non-fatal — compilation
  succeeds and `lake build` is clean. Not introduced by this cycle.

## Suggested next approach
Order-4 layer is the natural next step, but the §530 ladder gets
much harder beyond order 3:
- Order ≥ 4 needs *both* `order3a` (bushy) and `order3b` (tall) on the
  RK side, plus the four order-4 conditions, contracted into a fourth
  Taylor identity. The expansion has eight tree-monomial terms, not
  one, and the GLM-side identity is nontrivial.
- The order-2-sharp methods (`rkImplicitMidpoint`, `rkHeun`,
  `rkSDIRK2`, `rkMidpoint`) already have tracked `_not_order3` lemmas;
  adding any `_toGLM_hasOrderGe3` for them would be a guaranteed false
  target. The disproven-identities list should grow if anyone tries.
- Alternatively, additional order-3 witnesses (`rkLobattoIIIA3`,
  `rkLobattoIIIB3`, `rkLobattoIIIC3`, `rkRadauIIA3`, `rkRadauIA2`) are
  all in scope via existing imports; each is a one-line wrapper once
  the corresponding `_order3` or `_order4` certificate is named. Cheap
  cycle-padding work if needed.
- The order-4 GLM identity will involve a stage-level second-moment
  expression; consider extracting `ButcherTableau`-side helpers (e.g.
  `c_squared_row_sum`, `Ac_row_sum`) before attempting the bridge.
