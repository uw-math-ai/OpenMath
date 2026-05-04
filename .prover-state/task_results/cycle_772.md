# Cycle 772 Results

## Worked on
§530 GLM order ≥ 5 — `HasOrderGe5` predicate, `HasOrderGe5.toHasOrderGe4`
projection, `toGLM_hasOrderGe5` RK bridge, and three concrete RK
witnesses (Gauss–Legendre 3-stage, Radau IIA 3-stage, Radau IA 3-stage).

## Approach
Followed the cycle-770 cadence verbatim, one structural level deeper:

1. Appended `HasOrderGe5` to `OpenMath/GeneralLinearMethod.lean`
   right after `HasOrderGe4.toHasOrderGe3`. Six existential witness
   vectors `q, q', q'', q''', q'''', q'''''`, six derivative
   compatibility identities, leading factor `120 ·` for the new sixth
   bullet.
2. Appended `HasOrderGe5.toHasOrderGe4` projection — drops the new
   sixth bullet and the new Nordsieck input, reuses the order-≥ 4
   witness.
3. Appended `toGLM_hasOrderGe5` to `OpenMath/RKAsGLM.lean` before
   `end ButcherTableau`. Witnesses `q ≡ 1, q' = … = q''''' = 0`. The
   first six bullets are byte-for-byte copies of the
   `toGLM_hasOrderGe4` proof. The new seventh bullet uses the
   consistency rewrite `∑_{i'''} A_{i'' i'''} = c_{i''}` (via
   `simp_rw [hcj]`), then closes via the same `hreshape` pattern as
   cycle 770, with one extra inner sum, and `exact hb5` against
   `t.order5i`.
4. Added three witness theorems at the end of `RKAsGLM.lean`:
   `rkGaussLegendre3_toGLM_hasOrderGe5`, `rkRadauIIA3_toGLM_hasOrderGe5`,
   `rkRadauIA3_toGLM_hasOrderGe5`. Imported `OpenMath.RadauIA3` (the
   only file not already imported by `RKAsGLM.lean`).

## Result
SUCCESS — both files compile clean, full `lake build` succeeds in 8087
jobs with no new errors and no `sorry`. Task delivered exactly the
cycle-770-shaped increment: predicate + projection + bridge + three
witnesses.

## Dead ends
- The strategy's projection chain for `hb3 := h5.1.2.2.2` and
  `hb4 := h5.1.2.2.2.2.2.2` was off by one: those projections returned
  `order3b ∧ order4a ∧ … ∧ order4d` and `order4c ∧ order4d` instead of
  the desired `order3b` and `order4d`. Fixed by extending each chain
  by one selector — `h5.1.2.2.2.1` for `order3b` and
  `h5.1.2.2.2.2.2.2.2` for `order4d`. (HasOrderGe5 = HasOrderGe4 ∧ …,
  so `h5.1` already enters HasOrderGe4 and every projection inside it
  needs one extra `.1`/`.2` versus the cycle-770 chain on a bare h4.)
- After the first `lake env lean OpenMath/RKAsGLM.lean`, the witness
  block reported `GeneralLinearMethod.HasOrderGe5` not in environment
  because the new `GeneralLinearMethod.lean` had not yet been built
  into `.olean`. A `lake build OpenMath.GeneralLinearMethod` fixed it
  and the second `lake env lean` round-trip was clean.

## Discovery
The cycle 762 → 770 → 772 increment recipe is now stable:
- Predicate adds one fresh Nordsieck input, one extra `simp_rw` of
  the deepest `∑_l A_l c_l = c` identity, and bumps the leading
  factorial.
- Projection drops the last bullet and last witness; one-line
  `obtain`/`refine` swap.
- Bridge: copy the previous bridge verbatim into the first n−1
  bullets, then add one new bullet that ends in `exact h5.X` against
  the deepest `order5i`-shape (or `order4d`, `order3b` in lower
  cycles). The `hreshape` lemma works because `simp [Finset.mul_sum,
  mul_assoc]` flattens nested `b * (∑ … * (∑ …))` to the canonical
  fully-distributed form.
- Witness theorems are six-line term-level entries reusing the
  textbook `*_orderN` certificate plus the `*_consistent` instance.

The same pattern should land `HasOrderGe6` next cycle without
incident — the seventh bullet would need a sixth-derivative `order6t`
analogue (deepest tree, `1/720`), which would be a new Mathlib-style
order condition unless we already have it in `RungeKutta.lean`.

## Suggested next approach
- Cycle 774 should bump to `HasOrderGe6`. Inputs: check
  `OpenMath/RungeKutta.lean` for `order6t` (deepest tree, the analogue
  of `order5i`). If present, copy this cycle's recipe one level deeper
  with leading factor `720 ·` and binomial coefficients
  `1, 6, 15, 20, 15, 6, 1`. Witness candidates: Gauss–Legendre 3
  (order 6, exact). Radau IIA/IA 3 are only order 5 — they will not
  carry over as order-≥ 6 witnesses. The single order-6 witness is
  acceptable, matching the cycle 766 single-witness precedent for
  Midpoint and the cycle 770 pattern.
- If cycle 774's `simp_rw` chain for the sixth-deriv bullet starts
  blowing the stack (the cycle 772 simp run printed a long backtrace
  during one preceding `simpLocation` — non-fatal here), pre-collapse
  the inner consistency rewrite with explicit `rw [hcj]` per index
  level instead of `simp_rw [hcj]`.
