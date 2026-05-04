# Cycle 770 Results

## Worked on
§530 GLM order ≥ 4 — predicate, projection, RK bridge, and three concrete
witnesses, mechanical extension of the cycle 768 order-3 layout.

## Approach
Followed the cycle 770 strategy verbatim:

1. Added `HasOrderGe4` predicate to `OpenMath/GeneralLinearMethod.lean`
   immediately after `HasOrderGe3.toHasOrderGe2`. The predicate adds a
   fifth Nordsieck input vector `q''''` and the fourth-derivative Taylor
   compatibility identity with leading factor `24 ·` and binomial RHS
   `1, 4, 6, 4, 1`.
2. Added `HasOrderGe4.toHasOrderGe3` projection just below it (one
   `obtain`/`exact` line, mirroring the order-3 projection).
3. Added `ButcherTableau.toGLM_hasOrderGe4` RK bridge to
   `OpenMath/RKAsGLM.lean` immediately before `end ButcherTableau`. The
   sixth (fourth-derivative) identity branch reuses the same
   `simp [Finset.mul_sum, mul_assoc]` reshape pattern as the order-3
   bridge, with one extra nested `t.A` factor. Closed by quoting
   `t.order4d = h4.2.2.2.2.2.2.2` (the last conjunct of `HasOrderGe4`).
4. Added three direct one-line witnesses at the bottom of `RKAsGLM.lean`:
   `rkRK4_toGLM_hasOrderGe4`, `rkGaussLegendre2_toGLM_hasOrderGe4`,
   `rkGaussLegendre3_toGLM_hasOrderGe4`. All three wrap their existing
   RK-side `*_order4` certificates directly, no projection needed.

## Result
SUCCESS. `lake build` green. No new sorrys. All four targets land:

- `GeneralLinearMethod.HasOrderGe4` predicate.
- `HasOrderGe4.toHasOrderGe3` downward projection.
- `ButcherTableau.toGLM_hasOrderGe4` RK bridge.
- Three witnesses: `rkRK4_toGLM_hasOrderGe4`,
  `rkGaussLegendre2_toGLM_hasOrderGe4`,
  `rkGaussLegendre3_toGLM_hasOrderGe4`.

## Dead ends
None. One off-by-one in the strategy: it claimed `h4.2.2.2.2 : t.order3b`
but with `HasOrderGe4 = order1 ∧ order2 ∧ order3a ∧ order3b ∧ order4a
∧ order4b ∧ order4c ∧ order4d` the correct projector is `h4.2.2.2.1`.
Fixed during the file-level check.

## Discovery
The same `simp [Finset.mul_sum, mul_assoc]` reshape recipe used for the
order-3 RK bridge collapses the order-4 reshape one level deeper without
modification. The `RHS = q + 4 q' + 6 q'' + 4 q''' + q''''` cleanup with
`q' ≡ q'' ≡ q''' ≡ q'''' ≡ 0`, `q ≡ 1` is handled by the same
`norm_num` finisher (`24 * (1/24) = 1`).

## Suggested next approach
The §530 ladder has now reached order 4, which the strategy notes is the
last "easy ladder rung" before order 5/6. Several options for cycle 772:

1. **Order ≥ 5 GLM predicate** for `rkGaussLegendre3` (the only RK
   tableau on `main` with an order-5 certificate). The strategy text
   warns this is harder: the RK-side fifth-order condition has 9
   distinct tree monomial classes, each needing a separate `key`/
   `hreshape` block.
2. **Lobatto / Radau order-3 witnesses** — these are explicitly forbidden
   in the cycle 770 strategy as cherry-picking, but a follow-up cycle
   could legitimately revisit them if order-5 turns out to be too painful
   in one cycle.
3. **§530 sufficient-conditions converse** — turn the current
   `HasOrderGe N` predicates into "the GLM has classical order ≥ N"
   (Butcher §531). This requires lifting the Nordsieck identities to
   actual Taylor expansions and is a substantive direction shift.
