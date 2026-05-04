# Cycle 762 Results

## Worked on
§530 GLM order ≥ 2 predicate + §502 RK bridge + concrete witness, per
the planner's strategy.md repeating the cycle 761 assignment.

## Approach
Followed the strategy literally:

1. Added `GeneralLinearMethod.HasOrderGe2` to
   `OpenMath/GeneralLinearMethod.lean` immediately after
   `HasOrderGe1` (lines 175–199). Bare `∃ q q' q''` predicate with
   four conjuncts (preconsistency-V, preconsistency-U, first-derivative
   compatibility, second-derivative compatibility), keeping the `2 *`
   form to stay division-free.

2. Added `ButcherTableau.toGLM_hasOrderGe2` to `OpenMath/RKAsGLM.lean`
   right after `toGLM_hasOrderGe1`. Witnesses `q ≡ 1`, `q' ≡ 0`,
   `q'' ≡ 0`. The first three goals collapsed exactly as in the cycle
   760 `toGLM_isConsistent` template. The fourth goal reduced via the
   `[toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
   Finset.sum_const_zero, add_zero]` simp set, then `simp_rw [hcj]`
   for the row-sum rewrite, then `rw [hb2]; norm_num` to land
   `2 * (1/2) = 1`.

3. Added `rkImplicitMidpoint_toGLM_hasOrderGe2` as a one-line
   composition of the bridge with `rkImplicitMidpoint_order2` and
   `rkImplicitMidpoint_consistent`.

## Result
SUCCESS — all three additions compile. `lake env lean` and
`lake build OpenMath.RKAsGLM` both succeed with no new errors and no
new sorries. The two unused-simp warnings I initially introduced
(`zero_add`, `mul_one`) were trimmed; only the three pre-existing
`linter.unusedSimpArgs` warnings on RKAsGLM lines 357 / 412 / 433
remain (cycle 760 also reported them; the new cycle 762 lines pushed
the prior 379 / 400 hits to 412 / 433).

Important detail: after editing `GeneralLinearMethod.lean`,
`lake env lean OpenMath/RKAsGLM.lean` initially failed with
`Invalid field HasOrderGe1: The environment does not contain
GeneralLinearMethod.HasOrderGe1`. The cause was a stale olean for
`GeneralLinearMethod`. Running `lake build OpenMath.GeneralLinearMethod`
to refresh the cache fixed it. Future cycles editing both files in
sequence: rebuild the upstream module's olean before running
`lake env lean` on the downstream file.

## Dead ends
None this cycle. The scaffold from the strategy worked first try once
the olean cache was refreshed.

## Discovery
* `lake env lean <file>` does NOT regenerate the olean — it only
  type-checks the file in-place. If a downstream file is affected by
  the edit, run `lake build` on the upstream module first or the
  downstream `lake env lean` will read stale `GeneralLinearMethod.olean`
  and report bogus "field doesn't exist" errors.
* `simp only [toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
  Finset.sum_const_zero, add_zero]` is the right minimal set for
  collapsing the second-derivative identity under `q' ≡ 0`, `q'' ≡ 0`.
  `zero_add` and `mul_one` are NOT needed — the residual after the
  above set is already `2 * ∑ j, t.b j * (∑ i, t.A j i) = 1`.

## Suggested next approach
The strategy's stated next target is cycle 763's `HasOrderGe3`
analogue with `rkGaussLegendre2` (order 4 sharp) as the witness.
That requires:
* A `GeneralLinearMethod.HasOrderGe3` predicate adding a `q'''`
  Nordsieck input and the third-derivative compatibility identity
  `6 · ∑ j, B k j · (½ c_j² + U·q'')_j + V q''' = q + 3q' + 3q'' + q'''`
  (or whichever rational-clearing form keeps `simp` happy).
* A `ButcherTableau.toGLM_hasOrderGe3` bridge that needs both order-3
  RK conditions: `order3a` (∑ b_i c_i² = 1/3) AND `order3b`
  (∑_{i,j} b_i a_{ij} c_j = 1/6). Witnesses still `q ≡ 1`, `q' ≡ 0`,
  `q'' ≡ 0`, `q''' ≡ 0`.
* The concrete `rkGaussLegendre2_toGLM_hasOrderGe3` witness — feed
  `rkGaussLegendre2_order4` (which `.left.right.right.left` gives
  `order3a` and `.left.right.right.right.left` gives `order3b`,
  modulo the actual conjunction shape; verify with `lean_hover_info`).

After that, an LMM-side `LMM.toGLM_hasOrderGe2` bridge (using the
`q''` Nordsieck embedding for the `2 * s` past-state input) and a
parallel `HasOrderGe2 → HasOrderGe1` projection lemma are natural
fillers.
