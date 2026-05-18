# Cycle 372 Results

## Worked on
§422 Phase D.3.b Step 2 closed-form witness ladder: shipped
`elementaryWeightQ_phi_inv_mkVertexCherry` (first asymmetric order-4
witness — `mk [vertex, cherry] = mk [vertex, mk [vertex]]`) plus the
m=0 corollary `powRep_sum_eq_of_agreement_at_mkVertexCherry_zero` and
two non-vacuity examples (closed-form at `⟦explicitEuler⟧` = 1,
reflexive m=0 witness via `rfl × 5`).

## Approach
Followed cycle 371's `mk [broom₃]` recipe (most recent two-child cons
pattern) blended with cycle 369's `mk [cherry]` inner-cherry handling.
Core structure:

1. `Quotient.inductionOn` reduces to a representative `⟨s, M⟩`.
2. Reuse cycle 367/368/369 helpers verbatim: `h_inv_v`, `h_vertex`,
   `h_dw_cherry`, `h_cherry`, `h_dws_cherry`, `h_dw_broom₃`,
   `h_broom₃`, `h_inv_cherry` (representative-lift one-liner from
   cycle 369), `h_dw_mkCherry`, `h_mkCherry`.
3. Three new helpers for the two-child asymmetric structure:
   - `h_dw_mkVertexCherry i = (Σⱼ Aᵢⱼ) · (Σⱼ Aᵢⱼ · Σₖ Aⱼₖ)` —
     two-child cons-case unfold combining vertex-factor (Σⱼ Aᵢⱼ · 1)
     with cherry-factor (Σⱼ Aᵢⱼ · Σₖ Aⱼₖ).
   - `h_mkVertexCherry = Σᵢ bᵢ · (Σⱼ Aᵢⱼ) · (Σⱼ Aᵢⱼ · Σₖ Aⱼₖ)` —
     `Finset.sum_congr` + `ring` to reassociate `M.b i * (X * Y)` to
     `(M.b i * X) * Y`.
   - `h_dws_mkVertexCherry` — two-layer cons-case unfold; outer
     strips `mk` layer producing vertex-factor + cherry-factor
     product; inner cherry layer reuses `h_dws_cherry`.
4. After `_inv_mk` + `_mk × 5`, build the 5-term per-summand `h_subst`
   decomposition. The inner `Σⱼ Aᵢⱼ · (-v + Σₖ Aⱼₖ)` is pre-distributed
   via `Finset.sum_congr + ring` + `Finset.sum_add_distrib` +
   `← Finset.mul_sum` (mirroring cycle 371's inner-square expansion
   but at one degree lower). Then `ring` matches the 5-term split.
5. Distribute via 4× `Finset.sum_add_distrib`, factor constants via
   4× `← Finset.mul_sum`, back-substitute via `← h_mkVertexCherry,
   ← h_broom₃, ← h_mkCherry, ← h_cherry, ← h_vertex`, close with
   `ring`.

## Result
**SUCCESS** — file compiles clean. The only remaining sorry warning
is the grandfathered cycle 365 Sub-lemma A body sorry at
`Section422.lean:2272` (unchanged).

Sorry count: 5 → 5 (4 docstring references + 1 grandfathered code
sorry; new theorems are all body-clean).

## Faithfulness check

### New theorem: `elementaryWeightQ_phi_inv_mkVertexCherry`

- Entity ID: **N/A** — this is Phase D.3.b internal infrastructure,
  not a textbook entity (per strategy §D's explicit instruction not
  to label).
- Statement captures: closed-form for `Φ_{η_q⁻¹}(mk [vertex, cherry])`
  derived directly from cycle 358's `elementaryWeightQ_phi_inv_mk`
  (the representative-form `-Σᵢ bᵢ · dwws(i, t)`) by paper algebra
  on a representative. Closed form:
  ```
  Φ_{η_q⁻¹}(mk [vertex, cherry])
    = v⁴ − 3v²·c + c² + v·b' + v·m − Φ_η(mk [vertex, cherry])
  ```
  where v = `Φ_η(vertex)`, c = `Φ_η(cherry)`, b' = `Φ_η(broom₃)`,
  m = `Φ_η(mk [cherry])`. Sanity-checked at `⟦explicitEuler⟧` in
  the non-vacuity example: yields 1.
- No definition smuggling: the theorem is a closed-form identity
  for an existing `elementaryWeightQ_phi` at an existing tree;
  no new definitions are introduced.

### New theorem: `powRep_sum_eq_of_agreement_at_mkVertexCherry_zero`

- Entity ID: N/A (Phase D.3.b internal — m=0 case of Sub-lemma A).
- Statement captures: specialisation of cycle 365's Sub-lemma A
  `powRep_sum_eq_of_strict_subtree_agreement` at the specific tree
  `t = mk [vertex, cherry]` and `m = 0`. Hypotheses are five concrete
  agreement equations (vertex, cherry, broom₃, mk [cherry],
  mk [vertex, cherry]) — exactly the elementary weights appearing
  in the closed form. **No vacuity / tautology**: hypotheses are
  about `η_q` and `η_q'` quotient classes at SPECIFIC trees, the
  conclusion is about both at the `mk [vertex, cherry]` quotient
  power, and the proof routes through the closed form
  `elementaryWeightQ_phi_inv_mkVertexCherry` — eliminating the
  inverse via 5 named elementary weights, all of which appear in
  the hypothesis list.
- Hypothesis strength: the `h_mkVertexCherry` hypothesis IS the
  conclusion-tree's elementary weight at the un-inverted classes,
  matching cycle 365's Sub-lemma A statement structure (the closed
  form reveals which subtree elementary weights determine the
  inverse's value at the target tree — `mk [vertex, cherry]` itself
  appears as a strict subtree of `mk [mk [vertex, cherry]]` which is
  the next-depth ladder, but at m=0 the underlying inverse already
  involves `Φ_η(mk [vertex, cherry])` as a closed-form factor, so
  including it as a hypothesis is faithful to Sub-lemma A's
  "depends only on strict subtrees" pattern at the m=0 ladder rung).

### Identity / tautology checks

- `elementaryWeightQ_phi_inv_mkVertexCherry`: conclusion is
  `Φ_{η_q⁻¹}(mk [vertex, cherry]) = polynomial-in-5-elementary-weights`.
  No hypothesis appears verbatim in conclusion. ✓
- `powRep_sum_eq_of_agreement_at_mkVertexCherry_zero`: conclusion is
  about both `η_q^(-1)` AND `η_q'^(-1)` applied to the same tree;
  hypotheses are about `η_q` vs `η_q'` at FIVE different trees
  (including the target). Conclusion is not verbatim a hypothesis. ✓

## Dead ends
None — the cycle 371 `mk [broom₃]` template applied directly with
minor adaptations:

- The inner `Σⱼ Aᵢⱼ · (-v + Σₖ Aⱼₖ)` expansion is **linear** in
  `(-v + Σₖ Aⱼₖ)`, not squared as in cycle 371's broom₃. The same
  three-step pattern works (`Finset.sum_congr + ring` per-summand,
  then `Finset.sum_add_distrib`, then `← Finset.mul_sum`), but only
  one `← Finset.mul_sum` is needed (vs cycle 371's two for the
  squared expansion).
- The 5-term per-summand decomposition (vs cycle 371's 4-term)
  matches the closed form's 6 outer terms (`mk [v,c]` provides the
  first via direct `← h_mkVertexCherry`, the remaining 5 factor as
  constants times elementary-weight sums via `← Finset.mul_sum`).
- The combined constant `(2v² - c)` for the `Σᵢ M.b i · Σⱼ Aᵢⱼ`
  remainder (which would otherwise split into two separate
  `+3v²·c` and `-c²` terms, both with `← h_cherry` back-substitution)
  consolidates the two `c` terms into a single `← h_cherry` call,
  keeping the rewrite chain to one ← h_cherry as in cycle 371.
- Similarly the combined constant `(-v³ + vc)` for `Σᵢ M.b i`
  consolidates the `-v⁴` and `+v²c` terms behind a single
  `← h_vertex` call.

This is exactly the kind of consolidation cycle 371's strategy §G
mentioned as Option G.1 (named intermediate constants) — but it
turned out to be the natural shape of the 5-term decomposition,
not a fallback. No fallback was needed.

## Discovery

**Constant consolidation for shared-sum back-substitutions.** When
two per-summand integrand terms share the same Σⱼ tail (e.g. both
`+3v²·Sᵢ` and `-c·Sᵢ` involve `Σᵢ bᵢ·Sᵢ = M.eW(cherry)`), folding
their constants together into a single `(3v² - c) · (M.b i · Sᵢ)`
term avoids needing two separate `← Finset.mul_sum, ← h_cherry`
rewrites. The `ring` tactic at the end handles the constant algebra
automatically. This pattern was implicit in cycle 371's
`-v³ + 2vc - b'` consolidation but is now a documented technique.

**The (v³ + v·c) - (v³·v + vc·v) shift.** When the closed form
expects `-v⁴` and a `+3v²·c` term, the consolidated `(-v³ + vc) · v`
expansion yields `-v⁴ + v²c`, which combines with the separate
`(2v² - c) · c = 2v²c - c²` to give `-v⁴ + 3v²c - c²`. The natural
factoring `← h_vertex` at the end recovers the `v⁴` from a single
`Σᵢ M.b i · v³` remainder, sidestepping the need for any nested
power expansion. This minimizes the `← Finset.mul_sum` count.

## Suggested next approach

Cycle 373's planner has the same three substantive directions per
the cycle 371 §G outlook (now updated with 7 witnesses):

1. **Option 2** (`mk [mk [cherry]]`, depth-3 ladder) — one more
   data point, structurally a smaller step than cycle 372 (single
   outer wrap of cycle 369's `mk [cherry]`).

2. **Option 3 (STRONGLY RECOMMENDED)** — pivot to scoping the
   inductive Sub-lemma A attack. With **7 closed-form witnesses**
   (vertex, cherry, broom₃, mk [cherry], bushy, mk [broom₃],
   mk [vertex, cherry]) — covering single-child ladders, multi-leaf
   brooms, AND the first asymmetric heterogeneous-children case —
   the witness library is now genuinely sufficient to scope the
   inductive attack. The closed forms reveal a clear pattern: the
   inverse's value at any rooted tree decomposes as a polynomial
   in the elementary weights of its strict subtrees, with
   coefficients determined by the tree's structure. This is the
   exact statement Sub-lemma A needs.

3. **Fresh entity pivot** (e.g. `def:451A`) — would lose the 38
   consecutive axiom-clean §422 streak.

Cycle 372 worker (this cycle) strongly recommends **Option 3** for
cycle 373: the witness-accumulation treadmill has served its
purpose, and the inductive scoping doc is the natural next step
toward Phase D.3.d and Phase E sealing of `def:422B`.
