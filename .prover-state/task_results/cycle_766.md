# Cycle 766 Results

## Worked on
§530 GLM order ≥ 2 — additional concrete `rkXXX_toGLM_hasOrderGe2`
witnesses in `OpenMath/RKAsGLM.lean`, extending the cycle 762 / 764
ladder.

## Approach
Strategy was explicit: append three (plus one stretch) one-line
term-mode wrappers around the existing
`ButcherTableau.toGLM_hasOrderGe2` bridge, each fed by an existing
`HasOrderGe2` (or projected `HasOrderGe4`) witness and the matching
`IsConsistent` witness from `OpenMath/RungeKutta.lean` /
`OpenMath/GaussLegendre3.lean`.

For RK4 / Gauss–Legendre 2 / Gauss–Legendre 3 the existing facts give
`HasOrderGe4`, which unfolds as
`order1 ∧ order2 ∧ order3a ∧ order3b ∧ order4a ∧ order4b ∧ order4c ∧
order4d`, while `HasOrderGe2` unfolds as `order1 ∧ order2`. Inline
projection `⟨h.1, h.2.1⟩` is sufficient; no global projection lemma
was added (per strategy).

## Result
SUCCESS — four new lemmas land sorry-free in
`OpenMath/RKAsGLM.lean`:

- `rkMidpoint_toGLM_hasOrderGe2`
- `rkRK4_toGLM_hasOrderGe2`
- `rkGaussLegendre2_toGLM_hasOrderGe2`
- `rkGaussLegendre3_toGLM_hasOrderGe2` (stretch)

`lake env lean OpenMath/RKAsGLM.lean` runs clean (no errors, no new
warnings on the added block — the surviving warnings are pre-existing
unused-simp-arg lints on the cycle-755-era SDIRK3 stability proofs at
lines 453 and 474, untouched here).

## Dead ends
None — the four targets compiled on the first try via the
inline-projection pattern the strategy specified.

## Discovery
The inline `⟨h.1, h.2.1⟩` projection from `HasOrderGe4` to
`HasOrderGe2` is mechanical and syntactically uniform across
methods. If/when the cycle adds a fifth or sixth such RK-side
witness for an order-≥ 4 method, the same pattern will keep working;
a global `HasOrderGe4 → HasOrderGe2` (and `HasOrderGe3 → HasOrderGe2`)
projection in `OpenMath/RungeKutta.lean` only becomes worthwhile if
the call-site count grows past ~4–5 — at four call sites today the
inlined projection is still less scaffolding than a named lemma.

## Suggested next approach
The natural next §530 increment is **`HasOrderGe3`** in
`OpenMath/GeneralLinearMethod.lean`. Per the cycle 766 strategy, this
is genuine design work: order 3 has two independent rooted trees
(`node[leaf,leaf]` giving the `c²` identity and `node[node[leaf]]`
giving the `A·c` identity), so a faithful GLM `HasOrderGe3`
predicate must capture two compatibility identities (or one combined
identity that controls both elementary differentials). Recommend a
design-only cycle that produces the predicate plus the RK bridge
`toGLM_hasOrderGe3` and a single concrete witness (e.g.
`rk4_toGLM_hasOrderGe3` via `rk4_order4` projection, or
`rkGaussLegendre2_toGLM_hasOrderGe3`), with no attempt at the
projection-to-lower-order helpers until those land.

Alternatively, keep mining cheap order-2 witnesses (e.g. SDIRK3,
Lobatto IIIA/B/C, Radau IIA — each have a tracked `HasOrderGe?`
witness in their dedicated file and would each be one more one-line
wrapper). This is mechanical but stops being interesting after the
present batch; better to advance the predicate ladder than continue
listing RK methods.
