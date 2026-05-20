# Cycle 494 Results

## Worked on

§422 Phase α'.5.1 P5 — combined ship of:

1. **Quotient-level closed form** `elementaryWeightQ_phi_inv_mkVertexVertexBroom₃`
   for `Φ_{η_q⁻¹}(mk [vertex, vertex, broom₃])` (order-6, 13
   monomials across 10 named sum-kernels).
2. **`trichildCrossTerm` extension** — new fifth `else if` branch
   `(vertex, vertex, broom₃)`, value back-computed from the
   closed form minus Blocks (1)+(2)+(3)+(4)+(8).
3. **Inverse-polynomial calibration witness**
   `inversePolyTree_mkVertexVertexBroom₃` — 14th Family C witness.
4. **m=0 corollary**
   `powRep_sum_eq_of_agreement_at_mkVertexVertexBroom₃_zero` (10
   agreement hypotheses; specialisation of Sub-lemma A).
5. **Two non-vacuity `example`s** on `⟦explicitEuler⟧` (closed form
   pins to `1` via leading `v⁶`; m=0 reflexive via 10 `rfl`s).

## Approach

Mirrored cycle 491/492/493's combined-ship template (closed form +
`trichildCrossTerm` extension + calibration witness + m=0 corollary
in one cycle). Key differences from cycle 493's `mk [v, v, mk [c]]`:

- Third child is `broom₃ = mk [vertex, vertex]` (depth-2 binary
  symmetric) instead of `mk [cherry]` (depth-2 single-child).
  Inner factor uses cycle 371's `dws_inv_j broom₃ = (inv_v + Aⱼ)²`
  (a square of a vertex-aggregate sum) rather than cycle 369's
  three-term `dws_inv_j mk[cherry] = inv_c + inv_v · Aⱼ + Bⱼ`.
- After substituting `inv_v = -v`, `inv_b' = -v³ + 2vc - b'`, the
  per-row factor `(-v + Aᵢ)² · (inv_b' + ∑ⱼ Aᵢⱼ · (-v + Aⱼ)²)`
  expands with the inner identity
  `∑ⱼ Aᵢⱼ · (-v + Aⱼ)² = v²·Aᵢ - 2v·∑ⱼ Aᵢⱼ·Aⱼ + ∑ⱼ Aᵢⱼ·Aⱼ²`,
  giving a 10-monomial decomposition in `(Aᵢ^p, βⱼ-aggregate)`.
- Closed form has 13 monomial terms across 10 kernels: 6 from
  cycle 403 (`v, c, b', bu, mc, mvc, mvvc`) plus 3 new ones from
  the depth-2 inner factor (`mb = Φ_η(mk [broom₃])` (cycle 371),
  `mvb = Φ_η(mk [vertex, broom₃])` (cycle 386), and the
  self-kernel `mvvb`).

Paper derivation:

```
Σ b·dws_inv i (mk [v, v, broom₃])
  = v · (-v⁵ + 2v³c - v²b')
  + c · (3v⁴ - 4v²c + 2vb')
  + b' · (-3v³ + 2vc - b')
  + bu · v²
  + mc · (-2v³)
  + mvc · 4v²
  + mvvc · (-2v)
  + mb · v²
  + mvb · (-2v)
  + mvvb · 1
```

Negating gives the closed form RHS:
```
Φ_{η_q⁻¹}(mk [v, v, broom₃])
  = v⁶ - 5v⁴c + 4v³b' + 4v²c² - 4vcb' + b'²
    - v²·bu + 2v³·mc - 4v²·mvc + 2v·mvvc
    - v²·mb + 2v·mvb - mvvb
```

Verified at `⟦explicitEuler⟧` (`v=1`, all others = 0): RHS = `1`. ✓

Lean proof: standard quotient-induction + 22 reused helpers from
cycles 367/368/369/370/371/372/386/403 + 3 new helpers
(`h_dw_mkVertexVertexBroom₃`, `h_mkVertexVertexBroom₃`,
`h_dws_mkVertexVertexBroom₃`) + `h_subst` with 10-monomial
decomposition + 9 `Finset.sum_add_distrib` + 9 `← Finset.mul_sum` +
per-kernel back-substitution + `ring`. About 700 LOC for the
closed-form theorem body alone.

`trichildCrossTerm` extension: the new branch's value computed by
subtracting Blocks (1)+(2)+(3)+(4)+(8) at `(inv_v, inv_v, inv_b')
= (-v, -v, -v³ + 2vc - b')` from the closed form RHS, giving:

```
trichildCrossTerm vertex vertex broom₃ f
  = -v⁴·c + 3v³·b' - 2v·c·b' + b'²
    - v²·bu + 2v³·mc - 4v²·mvc
    + 2v·mvvc + 2v·mvb
```

Calibration proof recipe (mirrors cycle 491/492/493):

```
rw [inversePolyTree, inversePolyTree_vertex, inversePolyTree_broom₃]
unfold trichildPolynomial
rw [show trichildCrossTerm vertex vertex broom₃ f = ... by
      unfold trichildCrossTerm
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
          if_neg (by decide), if_pos ⟨rfl, rfl, rfl⟩]]
show <bridge>
ring
```

The four `if_neg`s discharge the (v,v,v), (v,v,c), (v,c,c),
(v,v,mk[c]) preceding branches; `if_pos` matches the new fifth
branch.

## Result

**SUCCESS.** All three named theorems compile axiom-clean
(`[propext, Classical.choice, Quot.sound]`); the `trichildCrossTerm`
extension does NOT break cycles 400/491/492/493's earlier calibration
proofs (regression verified — `inversePolyTree_bushy`,
`inversePolyTree_mkVertexVertexCherry`,
`inversePolyTree_mkVertexCherryCherry`, and
`inversePolyTree_mkVertexVertexMkCherry` all still axiom-clean).
The two `example`s on `⟦explicitEuler⟧` close as expected.

- Sorry count: 5 (unchanged; only grandfathered cycle 365 sorry
  remains).
- §422 axiom-clean streak: 67 substantive + 4 doc → **68
  substantive + 4 doc** (cycles 336–494).
- LOC delta: ~971 lines added (10946 → 11917).
- Phase α'.5.1 closes the `k = 3` order-6 candidate list. Five
  witnesses shipped over cycles 400/403/491/492/493/494:
  `bushy`, `mk[v,v,c]`, `mk[v,c,c]`, `mk[v,v,mk[c]]`, `mk[v,v,b']`.

## Faithfulness check

For each new `def` / `theorem` introduced this cycle:

**1. `elementaryWeightQ_phi_inv_mkVertexVertexBroom₃`** (closed-form
quotient-level theorem):

- Entity ID: `def:422B` (Phase α'.5.1 P5 sub-deliverable).
- Textbook statement: Butcher's §383 defines the group inverse
  `η⁻¹` implicitly via `η⁻¹ · η = 1`; cycle 358's
  `elementaryWeightQ_phi_inv_mk` characterises `Φ_{η⁻¹}(mk [...])`
  as `-Σᵢ M.b i · dws M.inverse i (mk [...])`. The cycle 494
  theorem evaluates this characterisation at the specific tree
  `mk [vertex, vertex, broom₃]` to a closed polynomial form
  in `Φ_η` of the order ≤ 6 named subtrees.
- Lean statement captures: **same content** as the §383 group-inverse
  evaluation at `mk [v, v, broom₃]`. Hypothesis list: only `η_q :
  Quotient PhiEquivalent.setoidSigma` (the most general quotient
  class; no extra hypotheses beyond Butcher's `η ∈ G_1` group).
- Verified: explicit `⟦explicitEuler⟧` non-vacuity (closed form
  evaluates to `1` via the leading `v⁶` term, matches the
  hand-computed value at `v=1, c=b'=bu=mc=mvc=mvvc=mb=mvb=mvvb=0`).

**2. `trichildCrossTerm` extension (fifth branch)** (extends a
preexisting `noncomputable def` by adding one `else if` branch):

- Not a new theorem, just an extension of cycle 399's polynomial
  helper. The value is BACK-COMPUTED from the closed form, NOT
  invented — Blocks (1)+(2)+(3)+(4)+(8) of `trichildPolynomial`
  subtracted from the closed-form RHS gives the cross-term value.
- No new mathematical content; purely a polynomial identity
  rearrangement.

**3. `inversePolyTree_mkVertexVertexBroom₃`** (calibration witness):

- Asserts that the recursive `inversePolyTree`'s output at the tree
  matches the closed-form RHS of theorem (1), under `f = Φ_η`.
  This is a SYNTACTIC unfold-and-`ring` proof (no new math).
- Lean statement: same RHS form as theorem (1), with `Φ_η ·` →
  `f ·` substitution.
- Hypothesis list: just the polynomial function `f : RT → ℝ`. No
  extra hypotheses.

**4. `powRep_sum_eq_of_agreement_at_mkVertexVertexBroom₃_zero`**
(m=0 corollary):

- Specialisation of Sub-lemma A at `m = 0` and the specific tree.
- Hypothesis list: 10 agreement hypotheses (one per sum-kernel
  appearing in theorem (1)'s closed form). Each hypothesis weakens
  the full §382 subtree-agreement predicate to just the kernels
  the closed form depends on. NO extra hypotheses beyond the
  algebraic content of theorem (1).
- Hypothesis count (10) matches the kernel count (10) in
  theorem (1). The mapping is direct and faithful.

## Dead ends

None. The cycle 491/492/493 template generalised cleanly. Two
specific gotchas avoided per memory:

- **Kernel-count estimate match**: cycle 494 strategy estimated
  8–10 kernels; actual is 10 (upper bound of estimate matched).
  Paper-derivation per memory
  `feedback_dws_cherry_factor_includes_v_aᵢ.md` caught the full
  expansion BEFORE Lean ship — the per-row inner factor expansion
  `(-v + Aᵢ)² · (inv_b' + ∑ⱼ Aᵢⱼ · (-v + Aⱼ)²)` has 10 distinct
  (Aᵢ^p, βⱼ-aggregate) monomials.

- **`ring` def opacity (memory `feedback_ring_def_opacity.md`)**:
  the calibration proof needs a `show`-bridge to canonicalise
  `f (mk [vertex])` ↔ `f cherry` before `ring` can close. The
  `show` bridge mirrors cycle 491/492/493's pattern verbatim.

## Discovery

- The 10-kernel closed form for `mk [v, v, broom₃]` is the same
  kernel count as cycle 493's `mk [v, v, mk [cherry]]` (also 10).
  This confirms the empirical observation that depth-2 third
  children produce 10-kernel closed forms regardless of whether
  the depth-2 child is binary (broom₃) or single-child (mk [cherry]).
  Concrete count by third-child shape:
  * cherry (depth-1 leaf): cycle 403 / 491 → 7 kernels
  * cherry+cherry (depth-1, two leaves): cycle 492 → 9 kernels
  * broom₃ (depth-2, binary, vertex-only): cycle 494 → 10 kernels
  * mk [cherry] (depth-2, single-child): cycle 493 → 10 kernels

- The `trichildCrossTerm` `if-then-else` cascade pattern continues
  to scale linearly: each new branch's calibration proof needs one
  additional `if_neg (by decide)` before its `if_pos`. After
  cycle 494, the cascade has 5 active branches + default `else 0`.
  Future cycles adding `k = 3` order > 6 witnesses or extending
  to `k = 4` would require either further cascade extension
  (manageable for ≤ 10 branches) or a structural refactor.

- Phase α'.5.1 closure: the five witnesses shipped over cycles
  400/403/491/492/493/494 exhaust the `k = 3` order-6 candidates
  (per the scoping doc §6.2 enumeration: bushy + 4 non-symmetric).
  The unified `inversePolyTree` recursion + uniform kernel
  characterisation across all five gives substantial empirical
  surface for designing the Phase β/γ structural induction
  needed to close the cycle 365 sorry.

## Suggested next approach

Three principal paths for cycle 495's planner:

1. **Phase β/γ scoping doc** — markdown-only scoping doc for
   attacking the cycle 365 sorry at line 2279
   (`powRep_sum_eq_of_strict_subtree_agreement` general body).
   The unified recursion + uniform kernel characterisation across
   the 14 Family C calibration witnesses provides the empirical
   surface needed to design the structural induction. Multi-cycle
   deliverable; cycle 495 scopes, cycles 496+ implement.

2. **Phase α'.5.2 scoping doc** — extend `inversePolyTree` from
   triple-children to quad-children arity. Requires
   `tetrachildPolynomial` + `tetrachildCrossTerm` infrastructure
   analogous to cycle 387's `bichildPolynomial` and cycle 399's
   `trichildPolynomial`. Multi-cycle infrastructure. First witness
   target: `mk [v, v, v, cherry]` (order 6).

3. **Pivot to fresh entity** — natural inflection point after the
   `k = 3` ladder closes. Per `cycle_336_pivot_options.md`, the
   ready candidates are `def:451A`, `def:442A`, `thm:535A`,
   `thm:541A`. Picking one would break the §422 streak (currently
   68 substantive + 4 doc, cycles 336–494) but open new
   formalization territory.

The pivot decision belongs to cycle 495's planner.
