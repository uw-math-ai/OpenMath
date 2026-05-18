# Cycle 370 Results

## Worked on
§422 Phase D.3.b Step 2: `bushy` (order-4 broom) closed form witness ship.
Per cycle 370 strategy Option B (cycle 369 task results' "Suggested next
approach") — `bushy = mk [vertex, vertex, vertex]` is the fifth tree of
order ≤ 4 in the Route B witness ladder (after vertex / cherry / broom₃ /
mk [cherry]). Deliverables:
- `elementaryWeightQ_phi_inv_bushy` (closed form for `Φ_{η_q⁻¹}` at the
  order-4 broom tree `bushy = mk [vertex, vertex, vertex]`).
- `powRep_sum_eq_of_agreement_at_bushy_zero` (m=0 corollary specialising
  Sub-lemma A at `t = bushy`).
- Two non-vacuity `example`s on `explicitEuler` (closed-form witness +
  reflexive m=0 witness).

## Approach
Mechanical extension of cycle 368's broom₃ recipe with one extra cons-case
unfold layer for the third child. Strategy §B.2 paper-derived the closed
form before opening Lean; strategy §B.3 cross-checked on `explicitEuler`
(expected value: 1).

### Paper derivation (independently verified before coding)

Per cycle 358's `_inv_mk` representative formula:
```
Φ_{⟦M⟧⁻¹}(bushy) = −∑ᵢ M.b i · M.derivativeWeightWithSrc M.inverse i bushy
```

Three-layer `derivativeWeightWithSrcProd` unfold at `[vertex, vertex,
vertex]`. Each layer extracts a per-leaf factor
`(M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j · dws j vertex)`. Using
cycle 366 `derivativeWeightWithSrc_vertex = 1`, the inner sum collapses
to `∑ⱼ M.A i j`, so the per-leaf factor becomes
`(M.inverse.elementaryWeight vertex + Aᵢ)` (with `Aᵢ := ∑ⱼ M.A i j`).
The three layers multiply to give factor³:
```
M.derivativeWeightWithSrc M.inverse i bushy
  = (M.inverse.elementaryWeight vertex + Aᵢ)^3
```
Under `h_inv_v : M.inverse.elementaryWeight vertex = -M.elementaryWeight
vertex`, this is `(Aᵢ − v)^3` with `v = Φ_η(vertex) = ∑ b`.

Binomial expansion:
```
(Aᵢ − v)^3 = Aᵢ^3 − 3 Aᵢ^2 v + 3 Aᵢ v^2 − v^3
```

Summing termwise against `M.b i`:
```
∑ b·Aᵢ^3   = M.elementaryWeight bushy   (= w)
∑ b·Aᵢ^2   = M.elementaryWeight broom₃  (= b')
∑ b·Aᵢ     = M.elementaryWeight cherry  (= c)
∑ b        = M.elementaryWeight vertex  (= v)
```

So:
```
∑ b·(Aᵢ − v)^3 = w − 3v·b' + 3v²·c − v⁴
−∑ b·(Aᵢ − v)^3 = v⁴ − 3v²·c + 3v·b' − w
```

Headline closed form:
```
Φ_{η_q⁻¹}(bushy) = Φ_η(vertex)^4
                   − 3 · Φ_η(vertex)^2 · Φ_η(cherry)
                   + 3 · Φ_η(vertex) · Φ_η(broom₃)
                   − Φ_η(bushy)
```

### Sanity check on `explicitEuler`

`s = 1`, `b = ![1]`, `A = !![0]`. So:
- `v = 1`, `c = 0`, `b' = 0`, `w = 0`.
- RHS = `1 − 0 + 0 − 0 = 1`.
- Direct LHS via `_inv_mk`: `−∑ b · (0 − 1)^3 = −(−1) = 1`. ✓

### Lean ship

Followed strategy §B.4 recipe verbatim, mirroring cycle 368's broom₃ ship
with one additional cons-case unfold layer in each of `h_dw_bushy`,
`h_bushy`, `h_dws_bushy`. The h_sum block extracts three constants via
`← Finset.mul_sum` (vs. broom₃'s two), corresponding to the `3v`, `3v²`,
`v³` coefficients in the binomial expansion.

## Result
**SUCCESS** — `lake env lean OpenMath/Chapter4/Section422.lean` exits 0
with only the existing grandfathered Sub-lemma A body sorry warning at
line 2272. Both new theorems print axiom-clean
(`[propext, Classical.choice, Quot.sound]`). Both non-vacuity examples
compile cleanly.

### Verification

```
$ lake env lean OpenMath/Chapter4/Section422.lean
OpenMath/Chapter4/Section422.lean:2272:8: warning: declaration uses `sorry`
$ grep -c sorry OpenMath/Chapter4/Section422.lean
5
$ # 4 docstring references + 1 grandfathered Sub-lemma A body sorry
$ # Code-level sorry count = 1, unchanged from HEAD
```

Axiom check (via `lake build OpenMath.Chapter4.Section422` then
`lake env lean` on a `#print axioms` script):
```
'elementaryWeightQ_phi_inv_bushy' depends on axioms: [propext,
 Classical.choice, Quot.sound]
'powRep_sum_eq_of_agreement_at_bushy_zero' depends on axioms: [propext,
 Classical.choice, Quot.sound]
```

§422 axiom-clean streak: **35 → 36** (336–370).

LOC delta: Section422.lean grew from 3063 → 3351 lines (+288 LOC,
matching strategy §B.5's ~250 LOC estimate within reasonable tolerance).

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `elementaryWeightQ_phi_inv_bushy`

- **Entity ID**: not in `extraction/formalization_data/entities/` (this
  is a helper lemma not in Butcher — bushy is one of the order-4 broom-
  family trees Butcher does not name explicitly). The closed form is
  a Phase D.3.b Step 2 internal milestone toward Sub-lemma A's general
  body, derivable from cycle 358's `elementaryWeightQ_phi_inv_mk`
  representative formula combined with the §312 `derivativeWeightProd`
  recursion at `bushy = mk [vertex, vertex, vertex]`.
- **Lean statement captures**: same content as the paper derivation above.
  The closed form `Φ_{η_q⁻¹}(bushy) = v^4 − 3v²·c + 3v·b' − w` is a
  *theorem* derived from the §383 inverse-action structure, not a
  definitional shortcut.
- **Tautology check**: conclusion `(elementaryWeightQ_phi (η_q⁻¹) bushy =
  ...)` is genuinely new content; no hypothesis equals the conclusion
  (no hypotheses other than the `η_q` argument). ✓
- **Identity check**: proof is multi-step `Quotient.inductionOn` +
  helper-block construction + sum-algebra back-substitution + `ring`.
  No `exact h` re-export. ✓
- **Hypothesis strength check**: no extra hypotheses beyond the `η_q`
  argument. ✓
- **Definition smuggling check**: no new `def` or `structure`; this is a
  theorem about the existing `elementaryWeightQ_phi` (cycle 348). ✓

### `powRep_sum_eq_of_agreement_at_bushy_zero`

- **Entity ID**: not in `extraction/formalization_data/entities/` —
  this is the `m = 0, t = bushy` specialisation of Sub-lemma A
  `powRep_sum_eq_of_strict_subtree_agreement`. Sub-lemma A's body is
  itself a Phase D.3.b internal milestone (cycle 365's grandfathered
  sorry).
- **Lean statement captures**: same content as the m=0 case of Sub-lemma A
  at `t = bushy`. Hypotheses are the four agreement conditions
  (vertex, cherry, broom₃, bushy) corresponding to the four factors in
  the bushy closed form.
- **Tautology check**: conclusion is `Φ_{η_q^(-1)}(bushy) =
  Φ_{η_q'^(-1)}(bushy)`. Hypotheses are `Φ_η_q(t) = Φ_η_q'(t)` at four
  *different* trees. Conclusion is not verbatim a hypothesis. ✓
- **Identity check**: proof uses `elementaryWeightQ_phi_inv_bushy` on
  both sides to expose the closed form, then substitutes all four
  agreement hypotheses. Real mathematical work via the closed-form
  bridge. ✓
- **Hypothesis strength check**: the four hypotheses match the closed
  form's four factors; weakening any of them would invalidate the
  substitution chain (the `rw [h_vertex, h_cherry, h_broom₃, h_bushy]`
  fires only when all four are present). ✓
- **Definition smuggling check**: no new `def` or `structure`. ✓

## Dead ends

None this cycle. Strategy §B.2's paper derivation and §B.3's sanity
check were verified upfront, so the Lean ship proceeded without
significant detours. The three-layer cons-case unfold in `h_dws_bushy`
worked as the strategy §B.4 predicted: two sequential `have` blocks
(`h_prod_step_1` for `[vertex]`, `h_prod_step_2` for `[vertex, vertex]`)
build up to the bushy prod via cycle 368's pattern.

## Discovery

**`(Aᵢ − v)^k` per-row factor structure validated at k=3.** Cycle 368's
Discovery hypothesis (the per-row factor inside
`M.derivativeWeightWithSrc M.inverse i (mk [vertex, …, vertex])` for
a k-vertex broom is `(Aᵢ − v)^k`) is now confirmed at k=3 (bushy)
in addition to k=1 (cherry, cycle 367) and k=2 (broom₃, cycle 368).
The binomial expansion mechanically yields a (k+1)-term polynomial in
`Φ_η(vertex), Φ_η(cherry), Φ_η(broom₃), …, Φ_η(broomₖ)`, with
coefficients `(-1)^j · C(k,j)`.

**Generalised conjecture** (refined cycle 370): for the k-vertex broom
`broomₖ := mk [vertex, vertex, …, vertex]` (k children),
```
Φ_{η_q⁻¹}(broomₖ) = ∑_{j=0}^{k} (-1)^j · C(k,j) · v^{k-j} · w_j
```
where `v = Φ_η(vertex)` and `w_j = Φ_η(broomⱼ)` (with `broom₀ = vertex`,
`broom₁ = cherry`, `broom₂ = broom₃` (a name shift — the project's
`broom₃` is actually broom-with-2-vertex-children, i.e. order-3 with
2 leaves), `broom₃` (in this conjecture) = the project's `bushy`).
This is the Connes–Kreimer Hopf antipode formula at broom trees.

**Single-cycle ship reliability.** Five consecutive single-cycle closed-
form ships (cycle 366 vertex, 367 cherry, 368 broom₃, 369 mk [cherry],
370 bushy), all axiom-clean, confirms the recipe is robust. Each ship
extends the Sub-lemma A m=0 witness library by one tree and contributes
one structural data point toward Sub-lemma A's general body.

## Suggested next approach

Per cycle 370 strategy §F:

1. **Cycle 371**: ship `mk [broom₃]` closed form (depth-2 ladder of
   broom₃, an order-4 tree). Tests cycle 369's `_mkCherry`-style nested
   closed form at the next depth. Closed-form conjecture: structurally
   similar to `_mkCherry` with an extra ladder layer.

2. **Alternative cycle 371**: ship `mk [vertex, cherry]` closed form
   (first asymmetric order-4 tree, mixing one `vertex` leaf with one
   `cherry` subtree). This tests whether the cycle 368 `(Aᵢ − v)^k`
   pattern generalises from "k identical leaves" to "heterogeneous
   children" — the substantive structural step toward an inductive
   Sub-lemma A proof.

3. **Stretch cycle 371+**: with 5+ data points now in hand, the planner
   may consider a unified `broomₖ` inductive formulation (induction on
   `k`, with the binomial expansion as the inductive step). This is
   a multi-cycle effort and should be scoped in a separate planning
   document if attempted.

4. **Long-term**: Sub-lemma A's general body remains the multi-cycle
   blocker for Phase D.3.d. Continue accumulating closed-form witnesses
   (one per cycle) until 6–7 data points exist; then a separate planning
   cycle should re-scope the inductive attack with the now-richer
   witness library.

**Phase D.3.d (`underlyingOneStepMethod_aux`) remains blocked** on
Sub-lemma A's general body. Cycle 370's ship is purely additive to the
witness library and does not unblock D.3.d on its own.

Phase E sealing of `def:422B` continues to be projected for **cycle
380+** given Sub-lemma A's general body is the multi-cycle blocker.
