# Cycle 774 Results

## Worked on
- `GeneralLinearMethod.HasOrderGe6` predicate + projection
  `HasOrderGe6.toHasOrderGe5` in `OpenMath/GeneralLinearMethod.lean`.
- `ButcherTableau.toGLM_hasOrderGe6` RK→GLM bridge in
  `OpenMath/RKAsGLM.lean`.
- `rkGaussLegendre3_toGLM_hasOrderGe6` witness (the unique RK
  witness in the codebase for order 6).

## Approach
Followed the cycle 770/772 cadence: copied the cycle-772
`HasOrderGe5` definition and its projection verbatim, added one
extra Nordsieck input `q''''''`, one extra deeply-nested derivative
identity (binomial row `1, 6, 15, 20, 15, 6, 1`, leading factor
`720 ·`), and a one-line `obtain`/`exact` projection.

For the bridge, copied the seven existing bullets from
`toGLM_hasOrderGe5` and added the eighth bullet for `order6t`,
using the witness `q ≡ 1` and all higher derivatives ≡ 0. The
eighth bullet's reshape and `exact hb6` matched on the nose with
no `convert`/`ring_nf` fallback needed.

## Result
SUCCESS.

- `lake env lean OpenMath/GeneralLinearMethod.lean` — clean.
- `lake env lean OpenMath/RKAsGLM.lean` — clean (exit 0, 0
  errors). One spurious `simp` panic appears in stderr from a
  pre-existing `lobIIIC3` proof but is non-fatal and predates this
  cycle.
- `lake build` — green (8087 jobs), zero new errors, zero
  `sorry`s.

## Selector-chain notes (the recurring §530 trap)
The strategy explicitly warned about off-by-one chain errors. The
first draft made exactly that mistake: I treated `h6.1` as
projecting straight to `HasOrderGe4`, omitting the intermediate
`HasOrderGe5` layer.

Correct chains for the eighth bullet's `key` proof, given
`HasOrderGe6 = HasOrderGe5 ∧ order6a ∧ ... ∧ order6t` and
`HasOrderGe5 = HasOrderGe4 ∧ order5a ∧ ... ∧ order5i` and
`HasOrderGe4 = order1 ∧ order2 ∧ order3a ∧ order3b ∧ order4a ∧
order4b ∧ order4c ∧ order4d` (8 conjuncts):

| target  | chain                                                  |
|---------|--------------------------------------------------------|
| order1  | `h6.1.1.1`                                             |
| order2  | `h6.1.1.2.1`                                           |
| order3b | `h6.1.1.2.2.2.1`                                       |
| order4d | `h6.1.1.2.2.2.2.2.2.2`                                 |
| order5i | `h6.1.2.2.2.2.2.2.2.2.2`     (h6.1 + 9 `.2`s)          |
| order6t | `h6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2` (20 `.2`s)|

The strategy's "20 `.2`s total" count for `order6t` was correct.

## Dead ends
First-pass selector chains for `hb2`, `hb3`, `hb4`, `hb5` were all
off by one: I had treated `h6.1` as `HasOrderGe4` (skipping the
`HasOrderGe5` intermediate layer). Lean would have complained at
type-check time but the strategy's own warning made me re-derive
the chains before invoking `lean env lean`. Fixed in-edit, no
build failures recorded.

No fallback needed for the eighth bullet's reshape — the same
`simp [Finset.mul_sum, mul_assoc]` that closed the order-5i case
in cycle 772 also flattens the order-6t case cleanly, with `exact
hb6` matching the nested sum on the nose. The strategy's fallback
plan (manual `rw [Finset.mul_sum]` ladder, `convert hb6` with
`rfl`) was not exercised.

## Discovery
The cycle-770/772/774 ladder is genuinely mechanical: the only
hand-computation required per cycle is (a) the binomial row, (b)
the leading factorial, (c) one new selector chain into the
expanded conjunction. No new mathematical content. A future cycle
that wants to climb to order 7 would need 48 new tree conditions
(`order7a..order7??`) in `RungeKutta.lean` first; absent that, no
RK method in the codebase achieves order ≥ 7, so the bridge has
no witness even if defined.

The §530 ladder is now closed at order ≥ 6 with a sharp witness
(GL3, order = 6 = 2s, theoretical maximum).

## Suggested next approach
The strategy's "what NOT to do" lists §38, §388, §521 follow-ups,
§54/§55 IRKS, and §510 consistency/convergence as paused or
blocked. With the §530 GLM order ladder now closed at the GL3
ceiling, sensible next-cycle options are:

1. **§520/521 instantiations** — e.g. transport `IsAStable` to
   the `toGLM`-image of more RK methods (Lobatto IIIA-3 already has
   a stability function lemma in scope; cycle 740 closed the LMM
   iff bridge but RK-side instantiations may still be open). Check
   `plan.md` for the next specific ask.
2. **§511 / order conditions equivalence** — bridge between
   GLM Taylor-form `HasOrderGeN` and the RK tree-form `HasOrderGeN`
   in the converse direction (`toGLM_hasOrderGeN_iff` rather than
   the one-way `toGLM_hasOrderGeN` we have).
3. Open up the §530 ladder for **multistep methods** (BDF, AB,
   AM) embedded as GLMs, mirroring the `toGLM` bridge for RK.

Defer the order-7 jump until either (a) a 7-th order RK method
lands in the codebase or (b) the planner explicitly schedules the
20→48 tree expansion in `RungeKutta.lean`.

## File size status
- `OpenMath/GeneralLinearMethod.lean`: 720 → ~795 lines
  (well under cap).
- `OpenMath/RKAsGLM.lean`: 1238 → ~1373 lines (well under cap).
No splits required.
