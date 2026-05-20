# Cycle 493 Results

## Worked on

§422 Phase α'.5.1 P4 — combined ship of:

1. **Quotient-level closed form** `elementaryWeightQ_phi_inv_mkVertexVertexMkCherry`
   for `Φ_{η_q⁻¹}(mk [vertex, vertex, mk [cherry]])` (order-6, 15
   monomials across 10 named sum-kernels).
2. **`trichildCrossTerm` extension** — new fourth `else if` branch
   `(vertex, vertex, mk [cherry])`, value back-computed from the
   closed form minus Blocks (1)+(2)+(3)+(4)+(8).
3. **Inverse-polynomial calibration witness**
   `inversePolyTree_mkVertexVertexMkCherry` — 13th Family C witness.
4. **m=0 corollary**
   `powRep_sum_eq_of_agreement_at_mkVertexVertexMkCherry_zero` (10
   agreement hypotheses; specialisation of Sub-lemma A).
5. **Two non-vacuity `example`s** on `⟦explicitEuler⟧` (closed form
   pins to `1` via leading `v⁶`; m=0 reflexive via 10 `rfl`s).

## Approach

Mirrored cycle 491/492's combined-ship template (closed form +
`trichildCrossTerm` extension + calibration witness + m=0 corollary
in one cycle). Key differences from cycle 403's `mk [v, v, cherry]`:

- Third child is `mk [cherry]` (depth-2) instead of `cherry`
  (depth-1) → inner factor uses cycle 369's
  `h_dws_mkCherry = inv_c + inv_v · Aᵢ + Bᵢ` at index j (not the
  cycle 367 cherry factor), giving four monomials in the inner sum
  (constant, `Aⱼ`, `Bⱼ`, `Dᵢ`) rather than two.
- After substituting `inv_v = -v`, `inv_c = v² - c`, `inv_mc =
  -v³ + 2vc - m`, the per-row factor `(inv_v + Aᵢ)² · (inv_mc + Σⱼ
  Aᵢⱼ · (inv_c + inv_v · Aⱼ + Bⱼ))` expands to a 10-monomial
  decomposition in `(Aᵢ^p, Bᵢ^q, Dᵢ^r)` for `p+q+r ≤ 2`.
- Closed form has 15 monomial terms across 10 kernels: 7 from
  cycle 403 (`v, c, b', bu, m, vc, vvc`) plus 3 new ones from the
  depth-3 recursion (`Mmc = Φ_η(mk [mk [cherry]])`, `vmc = Φ_η(mk
  [vertex, mk [cherry]])`, and the self-kernel `vvmc`).

Paper derivation:

```
Σ b i · dws_inv i (mk [v, v, mk[c]])
  = (-v⁵ + 2v³c - v²m)·v
    + (3v⁴ - 5v²c + 2vm)·c
    + (-3v³ + 4vc - m)·b'
    + (v² - c)·bu
    + (-v³)·m
    + (2v²)·vc
    + (-v)·vvc
    + v²·Mmc
    + (-2v)·vmc
    + 1·vvmc
```

Negating gives the closed form RHS. Verified at `⟦explicitEuler⟧`
(`v=1`, all others = 0): RHS = `1`. ✓

Lean proof: standard quotient-induction + 23 reused helpers from
cycles 367/368/369/370/372/378/403 + 5 new helpers
(`h_dw_mkVertexMkCherry`, `h_mkVertexMkCherry`,
`h_dw_mkVertexVertexMkCherry`, `h_mkVertexVertexMkCherry`,
`h_dws_mkVertexVertexMkCherry`) + `h_subst` with 10-monomial
decomposition + 9 `Finset.sum_add_distrib` + 9 `← Finset.mul_sum` +
per-kernel back-substitution + `ring`. About 600 LOC for the
closed-form theorem body alone.

`trichildCrossTerm` extension: the new branch's value computed by
subtracting Blocks (1)+(2)+(3)+(4)+(8) at `(inv_v, inv_v, inv_mc)
= (-v, -v, -v³ + 2vc - m)` from the closed form RHS, giving:

```
trichildCrossTerm vertex vertex (mk [cherry]) f
  = -v⁴·c + v³·m + v²·c² + 3v³·b' - 4v·c·b' + m·b'
    - v²·bu + c·bu - 2v²·vc + v·vvc + 2v·vmc
```

Calibration proof recipe (mirrors cycle 491/492):

```
rw [inversePolyTree, inversePolyTree_vertex, inversePolyTree_mkCherry]
unfold trichildPolynomial
rw [show trichildCrossTerm vertex vertex (mk [cherry]) f = ... by
      unfold trichildCrossTerm
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
          if_pos ⟨rfl, rfl, rfl⟩]]
show <bridge>
ring
```

The three `if_neg`s discharge the (v,v,v), (v,v,c), (v,c,c)
preceding branches; `if_pos` matches the new fourth branch.

## Result

**SUCCESS.** All three named theorems compile axiom-clean
(`[propext, Classical.choice, Quot.sound]`); the `trichildCrossTerm`
extension does NOT break cycles 400/491/492's earlier calibration
proofs (regression verified — `inversePolyTree_bushy`,
`inversePolyTree_mkVertexVertexCherry`, and
`inversePolyTree_mkVertexCherryCherry` all still axiom-clean).
The two `example`s on `⟦explicitEuler⟧` close as expected.

- Sorry count: 5 (unchanged; only grandfathered cycle 365 sorry
  remains).
- §422 axiom-clean streak: 66 substantive + 4 doc → **67
  substantive + 4 doc** (cycles 336–493).
- LOC delta: ~1100 lines added (9805 → 10946). Larger than the
  ~350 estimate because:
  - The closed-form theorem body (~620 LOC alone) included two
    extra new kernels (`h_dw/h_mkVertexMkCherry`, `h_dw/h_mkMkCherry`,
    `h_dw/h_mkVertexVertexMkCherry`) that the strategy underestimated
    (it estimated 6–7 kernels; actual is 10).
  - The non-vacuity example needed 10 zero-derivative subhypotheses
    (3 more than cycle 492's `mk [v, c, c]` example), each ~10 LOC.

## Faithfulness check

For each new `def` / `theorem` introduced this cycle:

**1. `elementaryWeightQ_phi_inv_mkVertexVertexMkCherry`** (closed-form
quotient-level theorem):

- Entity ID: `def:422B` (Phase α'.5.1 P4 sub-deliverable).
- Textbook statement: Butcher's §383 defines the group inverse
  `η⁻¹` implicitly via `η⁻¹ · η = 1`; cycle 358's
  `elementaryWeightQ_phi_inv_mk` characterises `Φ_{η⁻¹}(mk [...])`
  as `-Σᵢ M.b i · dws M.inverse i (mk [...])`. The cycle 493 theorem
  evaluates this characterisation at the specific tree
  `mk [vertex, vertex, mk [cherry]]` to a closed polynomial form
  in `Φ_η` of the order ≤ 6 named subtrees.
- Lean statement captures: **same content** as the §383 group-inverse
  evaluation at `mk [v, v, mk[c]]`. Hypothesis list: only `η_q :
  Quotient PhiEquivalent.setoidSigma` (the most general quotient
  class; no extra hypotheses beyond Butcher's `η ∈ G_1` group).
- Verified: explicit `⟦explicitEuler⟧` non-vacuity (closed form
  evaluates to `1` via the leading `v⁶` term, matches the
  hand-computed value at `v=1, c=b'=bu=m=vc=vvc=Mmc=vmc=vvmc=0`).

**2. `trichildCrossTerm` extension (fourth branch)** (extends a
preexisting `noncomputable def` by adding one `else if` branch):

- Not a new theorem, just an extension of cycle 399's polynomial
  helper. The value is BACK-COMPUTED from the closed form, NOT
  invented — Block (1)+(2)+(3)+(4)+(8) of `trichildPolynomial`
  subtracted from the closed-form RHS gives the cross-term value.
- No new mathematical content; purely a polynomial identity
  rearrangement.

**3. `inversePolyTree_mkVertexVertexMkCherry`** (calibration
witness):

- Asserts that the recursive `inversePolyTree`'s output at the tree
  matches the closed-form RHS of theorem (1), under `f = Φ_η`.
  This is a SYNTACTIC unfold-and-`ring` proof (no new math).
- Lean statement: same RHS form as theorem (1), with `Φ_η ·` →
  `f ·` substitution.
- Hypothesis list: just the polynomial function `f : RT → ℝ`. No
  extra hypotheses.

**4. `powRep_sum_eq_of_agreement_at_mkVertexVertexMkCherry_zero`**
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

None. The cycle 491/492 template generalised cleanly. Two
specific gotchas avoided per memory:

- **Kernel underestimate (strategy §D.3)**: strategy estimated 6–7
  kernels; actual is 10 (added `mk[mk[c]]`, `mk[v,mk[c]]`, plus the
  self-kernel `mk[v,v,mk[c]]`, plus also picked up `mk[v,v,c]` =
  `vvc` from cycle 403's kernel which doesn't appear in cycle 369's
  depth-2 closed form). Paper-derivation per memory
  `feedback_dws_cherry_factor_includes_v_aᵢ.md` caught this BEFORE
  Lean ship — the per-row inner factor expansion `(-v + Aᵢ)² · (...)`
  has 10 distinct monomials in `(Aᵢ^p, Bᵢ^q, Dᵢ^r)`.

- **`ring` def opacity (memory `feedback_ring_def_opacity.md`)**:
  the calibration proof needs a `show`-bridge to canonicalise
  `f (mk [vertex])` ↔ `f cherry` before `ring` can close. The
  `show` bridge mirrors cycle 491's pattern verbatim.

## Discovery

- The 10-kernel closed form for `mk [v, v, mk[c]]` confirms the
  cycle 492 hypothesis that `mk [cherry]`-tail children produce
  more kernels than `cherry`-tail children at the same depth.
  Concrete count: cycle 403's `mk [v, v, cherry]` needs 7 kernels;
  cycle 493's `mk [v, v, mk[cherry]]` needs 10. Three additional
  kernels arise from the depth-3 inner factor (`Mmc`, `vmc`, plus
  retaining the `vvc` kernel from the depth-2 part of the expansion).

- The `trichildCrossTerm` `if-then-else` cascade pattern scales
  linearly: each new branch's calibration proof needs one
  additional `if_neg (by decide)` before its `if_pos`. After
  cycle 493, the cascade has 4 active branches + default `else 0`.
  Future cycles adding `(v, v, broom₃)` etc. would extend the
  cascade further; no structural changes needed yet.

- LOC bloat insight: the non-vacuity example (`⟦explicitEuler⟧`)
  uses 10 zero-derivative + 10 zero-elementaryWeight subhypotheses,
  each ~5–10 LOC. This is a linear cost in the kernel count
  (cycle 403: 7 kernels, ~150 LOC example; cycle 492: 9 kernels,
  ~200 LOC; cycle 493: 10 kernels, ~250 LOC). Eventually it would
  be worth factoring out a generic `Φ_η_at_explicitEuler_zero`
  helper for any non-vertex tree, but that's a separate refactor
  cycle.

## Suggested next approach

**Phase α'.5.1 P5 — `mk [vertex, vertex, broom₃]`** (the only
remaining `k = 3` order-6 candidate per the scoping doc §6.2).
Structure: third child is `broom₃ = mk [vertex, vertex]` (depth-2
binary), so the inner factor is `dws M.inverse i broom₃`, which
unfolds via cycle 368 helper to a polynomial in `inv_v`, `Aᵢ`,
and... let me check. Actually `dws_broom₃ i = (inv_v + Σⱼ Aᵢⱼ ·
dws_j v) · (inv_v + Σⱼ Aᵢⱼ) = (inv_v + Aᵢ)²` since `dws_j v = 1`.
Hmm that gives only the `(-v + Aᵢ)²` factor (no inner cross-term
beyond what we've already seen). So `mk [v, v, broom₃]` per-row
factor is `(inv_v + Aᵢ)² · (inv_b' + Σⱼ Aᵢⱼ · dws_j broom₃)`
where `dws_j broom₃ = (inv_v + Aⱼ)² = inv_v² + 2·inv_v·Aⱼ + Aⱼ²`.

After distribution, kernels expected: `v, c, b', bu, m, vc, vvc,
b''` (where `b'' = Φ_η(mk[broom₃]) =  Φ_η(mk[mk[v,v]])`), plus
some new ones for depth-3 with `Aⱼ²`-bearing sums. Estimated
8–10 kernels (similar order to cycle 493). Estimated LOC ~700
(similar to cycle 493).

Paper-derive first per cycle 493 lesson. **Do NOT trust strategy
kernel-count estimates** — cycle 493 underestimated 6–7 → actual
10; cycle 494's strategy should explicitly enumerate kernels via
the symbolic expansion before drafting.

Alternative if cycle 494's scoping seems too costly: shift to
Phase β (Sub-lemma A body closure at line 2279), which is the
grandfathered cycle 365 sorry and the only remaining sorry in
§422. This is multi-cycle infrastructure work (cycle 366
sub-lemma B already in place + Phase β requires the induction
machinery for trees of `order < t.order` agreement → kernel
equality).

Stretch P5 candidate: also worth considering `k = 4` ladder
witnesses like `mk [vertex, vertex, vertex, cherry]` (Phase α'.5.2
per scoping doc §7), which would extend the `inversePolyTree`
recursion from triple-children to k-ary children. This is a
larger restructuring; defer until Phase α'.5.1 P5 is shipped.
