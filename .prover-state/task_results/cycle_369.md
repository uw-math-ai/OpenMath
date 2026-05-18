# Cycle 369 Results

## Worked on
§422 Phase D.3.b Step 2: `mk [cherry]` closed form witness ship. Per cycle
369 strategy Priority 2 (Option B) — `mk [cherry]` is the fourth tree of
order ≤ 3 in the Route B witness ladder (after vertex / cherry / broom₃).
Deliverables:
- `elementaryWeightQ_phi_inv_mkCherry` (closed form for `Φ_{η_q⁻¹}` at the
  order-3 depth-2 ladder tree `mk [cherry] = mk [mk [vertex]]`).
- `powRep_sum_eq_of_agreement_at_mkCherry_zero` (m=0 corollary
  specialising Sub-lemma A at `t = mk [cherry]`).
- Two non-vacuity `example`s on `explicitEuler` (closed-form witness +
  reflexive m=0 witness).

## Approach
Committed to Priority 2 upfront. The strategy explicitly endorses this
choice: "Picking P2 upfront is a perfectly acceptable strategic choice if
the worker has any doubt about P1's tractability" — and P1 (m=0 inductive
Sub-lemma A) was marked HIGH risk with a 60-min time-box. P2 is described
as mechanical, mirroring cycle 368's broom₃ recipe with one additional
inner cherry-unfold layer.

### Paper derivation (independently verified before coding)

Per cycle 358's `_inv_mk` representative formula:
```
Φ_{⟦M⟧⁻¹}(mk [cherry]) = −∑ᵢ M.b i · M.derivativeWeightWithSrc M.inverse i (mk [cherry])
```

Two-layer `derivativeWeightWithSrcProd` unfold at `[cherry] = [mk [vertex]]`:
- Outer (cons-case at `cherry :: []`):
  `(M.inverse.elementaryWeight cherry + ∑ⱼ M.A i j · M.derivativeWeightWithSrc M.inverse j cherry) · 1`.
- Inner (`derivativeWeightWithSrc M.inverse j cherry` per cycle 367
  `h_dws_cherry`): `M.inverse.elementaryWeight vertex + ∑ ₖ M.A j k`.

Per cycle 367's `elementaryWeightQ_phi_inv_cherry` at the quotient class
`⟦M⟧`, descended to the representative via `_mk` rfl reductions:
- `M.inverse.elementaryWeight vertex = -M.elementaryWeight vertex` (cycle
  341 P2 / cycle 367 `h_inv_v`).
- `M.inverse.elementaryWeight cherry = (M.elementaryWeight vertex)^2 - M.elementaryWeight cherry`.

Substituting, with `v := M.elementaryWeight vertex`, `c := M.elementaryWeight cherry`,
`w := M.elementaryWeight (mk [cherry])`, `Aᵢ := ∑ⱼ M.A i j`:

```
M.derivativeWeightWithSrc M.inverse i (mk [cherry])
  = (v² − c) + ∑ⱼ M.A i j · (−v + Aⱼ)
  = (v² − c) − v · Aᵢ + ∑ⱼ M.A i j · Aⱼ

−Φ_{η⁻¹}(mk [cherry]) = ∑ᵢ M.b i · ((v² − c) − v · Aᵢ + ∑ⱼ M.A i j · Aⱼ)
                      = (v² − c) · v − v · c + w
                      = v³ − 2vc + w

Φ_{η⁻¹}(mk [cherry]) = −v³ + 2vc − w
```

Closed form (structurally identical to cycle 368's broom₃, but with
distinct `w` since `mk [cherry] = mk [mk [τ]]` is a distinct tree from
`broom₃ = mk [τ, τ]`):
```
Φ_{η_q⁻¹}(mk [cherry]) = -(Φ_η(vertex))^3 + 2 · Φ_η(vertex) · Φ_η(cherry) - Φ_η(mk [cherry])
```

### Lean ship recipe

1. `Quotient.inductionOn` on `η_q` produces a representative `⟨s, M⟩`.
2. Reused cycle 367 helpers `h_inv_v`, `h_vertex`, `h_dw_cherry`,
   `h_cherry`, `h_dws_cherry` verbatim.
3. New cycle 369 helpers:
   - `h_inv_cherry : M.inverse.elementaryWeight cherry =
     (M.elementaryWeight vertex)^2 − M.elementaryWeight cherry` —
     term-mode proof via cycle 367's quotient theorem at `⟦M⟧`,
     descended through `_mk` and `inverseQ_phi_mk` `:= rfl` reductions.
   - `h_dw_mkCherry i : M.derivativeWeight i (mk [cherry]) = ∑ⱼ M.A i j · ∑ₖ M.A j k`
     (one-layer unfold + `h_dw_cherry`).
   - `h_mkCherry : M.elementaryWeight (mk [cherry]) = ∑ᵢ M.b i · ∑ⱼ M.A i j · ∑ₖ M.A j k`
     (one `Finset.sum_congr`).
   - `h_dws_mkCherry i : M.derivativeWeightWithSrc M.inverse i (mk [cherry])
     = M.inverse.elementaryWeight cherry + M.inverse.elementaryWeight vertex · ∑ⱼ M.A i j
       + ∑ⱼ M.A i j · ∑ₖ M.A j k` — the key new helper. Internal split via
     `Finset.sum_add_distrib + ← Finset.sum_mul + ring` to expose the
     three sum-shaped pieces needed for back-substitution.
4. Main `h_sum` block: per-summand expansion via `ring` (after
   substituting closed forms), then sum-distribute via
   `Finset.sum_add_distrib + Finset.sum_sub_distrib`, then `← Finset.mul_sum × 2`
   on the two extractable constants, then
   `← h_mkCherry, ← h_cherry, ← h_vertex` back-substitution, then `ring`.
   Structured per cycle 368's recipe with three summand-terms `A - B + C`
   where:
   - A = `M.b i · (∑ⱼ A_ij · A_j)` (no extractable constant; bridged via
     `← h_mkCherry`).
   - B = `v · (M.b i · A_i)` (constant `v` extractable; bridged via
     `← Finset.mul_sum` + `← h_cherry`).
   - C = `(v² − c) · M.b i` (constant `(v² − c)` extractable; bridged via
     `← Finset.mul_sum` + `← h_vertex`).
5. m=0 corollary: 3-line `rw` chain (`zero_add`, `Nat.cast_one`,
   `zpow_neg_one` to bridge `η_q ^ (-(((0+1:ℕ):ℤ)))` to `η_q⁻¹`, then
   apply the new closed form on both sides and substitute the three
   agreement hypotheses).
6. Non-vacuity at `explicitEuler`: closed-form witness yields
   `Φ_{⟦EE⟧⁻¹}(mk [cherry]) = -1`; m=0 reflexive witness via `rfl, rfl, rfl`.

### Lean name resolution gotcha (worth recording for future cycles)

Initial attempts to write `RootedTree.mk [RootedTree.cherry]` failed
because `_root_.RootedTree` is also present in Mathlib (a structure for
the order-theoretic tree formalism at
`Mathlib/Order/SuccPred/Tree.lean:103`). Lean preferred Mathlib's
`RootedTree.mk` (which expects a Type as first argument) over our
Section310 inductive's `.mk`. Workaround: use the fully-qualified path
`OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]`. This
matches existing usage at `Section422.lean:168`. Other constructions
(`RootedTree.vertex`, `RootedTree.cherry`, `RootedTree.broom₃`) work
under bare qualification because Mathlib's `RootedTree` namespace has no
such members — only the `mk` constructor collides.

## Result
**SUCCESS — all four declarations ship axiom-clean.** Verification:

- `lake env lean OpenMath/Chapter4/Section422.lean` exits 0 in ~210s
  (first warm rebuild after edits; subsequent passes similar).
- `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 (4 docstring
  references + 1 grandfathered Sub-lemma A body sorry at line 2272;
  unchanged from HEAD `bbfe281`).
- `#print axioms` results (verified via temporary `#print` decorations,
  removed before final commit):
  - `elementaryWeightQ_phi_inv_mkCherry`: `[propext, Classical.choice, Quot.sound]` ✓
  - `powRep_sum_eq_of_agreement_at_mkCherry_zero`: `[propext, Classical.choice, Quot.sound]` ✓
  - `elementaryWeightQ_phi_inv_broom₃` (cycle 368 spot-check):
    `[propext, Classical.choice, Quot.sound]` ✓
  - `powRep_sum_eq_of_agreement_at_broom₃_zero` (cycle 368 spot-check):
    `[propext, Classical.choice, Quot.sound]` ✓
  - `linearResidualAt_depends_only_on_strict_subtrees` (cycle 365 headline):
    `[propext, sorryAx, Classical.choice, Quot.sound]` (the expected
    single `sorryAx` from Sub-lemma A's grandfathered body) ✓

- §422 axiom-clean streak: 34 → **35** consecutive cycles (336–369).
- Section422.lean: 2815 → 3063 LOC (+248, four declarations plus
  multi-paragraph docstrings mirroring cycle 367/368 style).

## Faithfulness check

### `elementaryWeightQ_phi_inv_mkCherry`
Entity ID: this is helper infrastructure, not a textbook entity. It is
an instance of the §385–§387 construction of `Φ_{η⁻¹}` on a specific
tree, derived directly from the cycle-358 `elementaryWeightQ_phi_inv_mk`
representative formula plus the `RootedTree.mk` constructor at
`[RootedTree.cherry]`. The closed form is a *theorem* about that
construction, not a definition.

Closed form claim:
> `Φ_{η⁻¹}(mk [cherry]) = -(Φ_η(vertex))^3 + 2 · Φ_η(vertex) · Φ_η(cherry) - Φ_η(mk [cherry])`

Derivation (re-derived in scratch before writing, verified against the
strategy's §B paper derivation):
1. `Φ_{⟦M⟧⁻¹}(mk [cherry]) = -∑ᵢ M.b i · M.derivativeWeightWithSrc M.inverse i (mk [cherry])` (cycle 358 `_inv_mk`).
2. `M.derivativeWeightWithSrc M.inverse i (mk [cherry]) = (v² − c) − v · Aᵢ + ∑ⱼ M.A i j · Aⱼ` (two-layer unfold + cycle 367's cherry closed form).
3. Sum-distribute and back-substitute to yield `v³ − 2vc + w`.
4. Negate to get the stated form.

The Lean statement captures: **same content** as the paper derivation
(strategy §B closed form). No hypothesis weakening or strengthening.
The theorem is a pure rewrite identity over the quotient class, no
extra assumptions beyond `η_q : Quotient PhiEquivalent.setoidSigma`.

### `powRep_sum_eq_of_agreement_at_mkCherry_zero`
Specialisation of Sub-lemma A at `t = mk [cherry], m = 0`. The cycle
369 closed-form theorem reveals that `Φ_{η⁻¹}(mk [cherry])` depends on
`Φ_η(vertex), Φ_η(cherry), Φ_η(mk [cherry])`, so three agreement
hypotheses are required.

The Lean statement captures: **same content** as the Sub-lemma A m=0
specialisation. Hypothesis count (3) matches the closed form's factor
count, not stronger than necessary.

### Two `example`s (non-vacuity)
Both are `example` declarations (no public name), so they have no
textbook correspondence — they exercise the new theorems on
`explicitEuler` to demonstrate non-vacuity. No faithfulness issue.

## Dead ends
None this cycle. The proof recipe followed the strategy's §B/§C paper
derivation with one detour. Specifically:

- **Detour (resolved)**: initial Lean code used `RootedTree.mk [RootedTree.cherry]`
  which silently bound to Mathlib's `RootedTree.mk` (a structure
  constructor from `Mathlib/Order/SuccPred/Tree.lean` expecting a Type
  argument). Compile failed with "Application type mismatch" errors at
  every `mk [...]` site. Fixed by switching to fully-qualified
  `OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]`,
  matching the convention at `Section422.lean:168`.

- **Path A (per-summand `ring` after closed-form substitution + linearity
  distribution) closed on the first compiling attempt** without needing
  any fallback. The `← h_mkCherry, ← h_cherry, ← h_vertex` rewrite chain
  matched the expected pattern.

## Discovery

### Mathlib `RootedTree` namespace collision

Mathlib's `Mathlib.Order.SuccPred.Tree` defines a `structure RootedTree`
with `α : Type*` as its first field. When a file imports Mathlib and
references `RootedTree.mk`, Lean prefers the unqualified `_root_.RootedTree.mk`
(Mathlib's) over namespace-resolved variants — even when our
`OpenMath.Chapter3.Section310` is opened.

`RootedTree.vertex`, `RootedTree.cherry`, `RootedTree.broom₃` work
because Mathlib's `RootedTree` namespace has no such members; only the
`.mk` constructor collides. Workaround for any future tree literal
construction: use the fully-qualified
`OpenMath.Chapter3.Section310.RootedTree.mk` (matching the convention
already in use at Section422.lean:168) or define a local abbrev.

### Closed-form structural identity broom₃ vs mk [cherry]

Both `broom₃ = mk [τ, τ]` and `mk [cherry] = mk [mk [τ]]` are order-3
rooted trees, and BOTH yield the same closed-form skeleton
`Φ_{η⁻¹}(t) = -v³ + 2vc - Φ_η(t)`, with only the third term `Φ_η(t)`
differing between the two (it specialises to `M.elementaryWeight broom₃`
vs `M.elementaryWeight (mk [cherry])`, which are distinct quantities
in general).

This is consistent with the Connes–Kreimer Hopf algebra structure for
order-3 trees: the inverse-coproduct contributions at order 3 share the
shape `-v^3 + 2vc - w(t)`, where `w(t)` is the only tree-dependent
term. Cycle 368's discovery section anticipated this pattern at the
broom-of-k level; the present cycle confirms it for the depth-k ladder
as well.

### Pattern for "depth-extension" closed forms

When a closed form for `t` is known and we want the closed form for
`mk [t]` (the depth-extension), the derivation factors cleanly as:
1. Outer `derivativeWeightWithSrcProd` cons-case yields one inverse-
   weight factor + one A-row coupling against `dws inverse j t`.
2. Substitute the closed form for `M.inverse.elementaryWeight t` (which
   is derivable from cycle 367/368/369's quotient theorem at `⟦M⟧`).
3. Substitute the closed form for `M.derivativeWeightWithSrc M.inverse j t`
   (which is the "raw" per-stage closed form, established in the cycle
   ship for tree `t`).
4. Linearity-distribute the inner sum, sum-distribute the outer sum,
   factor out constants via `← Finset.mul_sum`, back-substitute the
   elementary-weight closed forms via `← h_*` rewrites.

This is the "vertical" extension pattern. Cycle 368's broom₃ exercised
the "horizontal" extension (adding more children of the same type).
Combined, the two patterns cover the basic Hopf-algebra construction
for arbitrary trees built by inductive `mk`-application.

## Suggested next approach

Per cycle 369 strategy §"Cycle 370+ outlook", with **four** witness
trees now shipped (vertex / cherry / broom₃ / mk [cherry]) and a
clear pattern emerging for vertical and horizontal extensions, cycle
370 has several productive paths:

**Option A (revisited): retry m=0 inductive Sub-lemma A scaffold.**
With the four witness data points and the cleaner pattern for
"depth-extension" derivations documented above, the inductive step's
algebraic structure is more concrete. Specifically, the `mk [t]` case
of the inductive step reduces to a polynomial in
`M.elementaryWeight u` for `u ∈ {strict subtrees of mk [t]} ∪ {mk [t]}`
that can be computed by appealing to the IH at each strict subtree.
The cycle 369 `h_dws_mkCherry` decomposition pattern is a near-direct
template for the general inductive case.

Estimated LOC: ~150-200. Estimated time: 90 min. Risk: still HIGH but
materially reduced from cycle 369's starting point.

**Option B (extend witness ladder to order 4):** ship one of the
order-4 trees. Candidates:
- `bushy = mk [vertex, vertex, vertex]` (the order-4 broom; per cycle
  368's `(Aᵢ - v)^k` Discovery hypothesis, the closed form should be
  `-(v² - c)·... = -(Aᵢ - v)^3` cubed-out).
- `mk [broom₃]` (vertical extension of broom₃).
- `mk [vertex, cherry]` (mixed-child tree; first asymmetric order-4
  case).

`bushy` is the cleanest closed-form test of the Discovery hypothesis.
`mk [vertex, cherry]` exercises a NEW pattern (mixed-child).

**Option C (Phase D.3.c progress):** with four data points and clean
patterns, take a first attempt at `underlyingOneStepMethod_aux` (cycle
343's well-founded recursion). The headline Sub-lemma B is
axiom-clean; the m=0 corollaries on small trees give base-case
unblocking. This is the actual downstream consumer of all this work.

Recommended for cycle 370: **Option B with `bushy`** to validate the
cycle 368 Discovery (the `(Aᵢ − v)^k` broom-of-k closed form
hypothesis). If `bushy` ships axiom-clean, the Discovery is confirmed
and Option A's general inductive step has a clear polynomial template
to work against.

The Sub-lemma A grandfathered sorry (line 2272 / 2279) remains
untouched per cycle 369 strategy §"What NOT to attempt". It is
reserved for cycle 370+ Route A / Route B closure.
