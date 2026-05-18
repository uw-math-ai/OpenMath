# Cycle 368 Results

## Worked on
§422 Phase D.3.b Step 2: broom₃ closed form. Per cycle 368 strategy:
- `elementaryWeightQ_phi_inv_broom₃` (closed form for `Φ_{η_q⁻¹}` at the
  order-3 two-child tree `broom₃ = mk [vertex, vertex]`).
- `powRep_sum_eq_of_agreement_at_broom₃_zero` (the m=0 corollary
  specialising Sub-lemma A at `t = broom₃`).
- Two non-vacuity `example`s on `explicitEuler`.

## Approach
Mirrored the cycle 367 cherry template with one additional unfold
layer for the two-child structure:

1. Closed-form identity (paper-derived, strategy §B.1):
   `Φ_{η_q⁻¹}(broom₃) = -(Φ_η(vertex))^3 + 2·Φ_η(vertex)·Φ_η(cherry) − Φ_η(broom₃)`.

2. Reused cycle 367 helpers `h_inv_v`, `h_vertex`, `h_dw_cherry`,
   `h_cherry` verbatim.

3. Added three new helpers for broom₃:
   - `h_dw_broom₃ i : M.derivativeWeight i broom₃ = (∑ⱼ M.A i j)^2`
     (two-layer unfold of `derivativeWeightProd i [vertex]` then
     `derivativeWeightProd i []`).
   - `h_broom₃ : M.elementaryWeight broom₃ = ∑ᵢ M.b i · (∑ⱼ M.A i j)^2`
     (one `Finset.sum_congr` substitution).
   - `h_dws_broom₃ i : M.derivativeWeightWithSrc M.inverse i broom₃
                       = (M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j)^2`
     (parallel to `h_dws_cherry` with one extra unfold; the
     `derivativeWeightWithSrcProd` factor collapses to the same
     `(M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j)` expression).

4. Main `h_sum` block: after substituting closed forms via
   `h_dws_broom₃` and `h_inv_v`, expanded `(x + Aᵢ)^2` per-summand
   via `ring`, then linearity-distributed via
   `Finset.sum_add_distrib + Finset.sum_sub_distrib +
    ← Finset.mul_sum × 2`, then `← h_broom₃, ← h_cherry, ← h_vertex`,
   then `ring`. Closed in one shot.

5. m=0 corollary: 3-line `rw` chain (`zero_add`, `Nat.cast_one`,
   `zpow_neg_one` to bridge `η_q ^ (-(((0+1:ℕ):ℤ)))` to `η_q⁻¹`,
   then apply the new closed form on both sides and substitute the
   three agreement hypotheses).

6. Non-vacuity at `explicitEuler`:
   - Closed-form witness: `Φ_{⟦EE⟧⁻¹}(broom₃) = -1`. Proof shape
     identical to cycle 367's cherry non-vacuity with an additional
     `h_broom₃_zero` step (the `simp [explicitEuler]` workaround
     from cycle 367 §I applies verbatim).
   - m=0 reflexive: closes by `rfl, rfl, rfl` on the three
     agreement hypotheses.

## Result
**SUCCESS — all four declarations ship axiom-clean.** Verification:

- `lake env lean OpenMath/Chapter4/Section422.lean` exits 0 in ~270s
  (warm rebuild ~4m29s first pass; subsequent rebuild ~5m43s with
  the temporary `#print axioms` decorations).
- `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 (4 docstring
  references + 1 grandfathered Sub-lemma A body sorry at line 2272;
  unchanged from HEAD `1d1422f`).
- `#print axioms` results:
  - `elementaryWeightQ_phi_inv_broom₃`: `[propext, Classical.choice, Quot.sound]` ✓
  - `powRep_sum_eq_of_agreement_at_broom₃_zero`: `[propext, Classical.choice, Quot.sound]` ✓
  - `elementaryWeightQ_phi_inv_cherry` (cycle 367 spot-check):
    `[propext, Classical.choice, Quot.sound]` ✓
  - `powRep_sum_eq_of_agreement_at_cherry_zero` (cycle 367 spot-check):
    `[propext, Classical.choice, Quot.sound]` ✓
  - `powRep_sum_eq_of_agreement_at_vertex` (cycle 366 spot-check):
    `[propext, Classical.choice, Quot.sound]` ✓
  - `linearResidualAt_depends_only_on_strict_subtrees` (cycle 365 headline):
    `[propext, sorryAx, Classical.choice, Quot.sound]` (the expected
    single `sorryAx` from Sub-lemma A's grandfathered body) ✓

- §422 axiom-clean streak: 33 → **34** consecutive cycles (336–368).
- Section422.lean: 2595 → 2815 LOC (+220, four declarations plus
  multi-paragraph docstrings mirroring cycle 367 style).

## Faithfulness check

### `elementaryWeightQ_phi_inv_broom₃`
Entity ID: this is helper infrastructure, not a textbook entity. It is
an instance of the §385–§387 construction of `Φ_{η⁻¹}` on a specific
tree, derived directly from the (cycle-358) `elementaryWeightQ_phi_inv_mk`
representative formula plus the `RootedTree.broom₃` definition. The
closed form is a *theorem* about that construction, not a definition.

Closed form claim:
> `Φ_{η⁻¹}(broom₃) = -(Φ_η(vertex))^3 + 2·Φ_η(vertex)·Φ_η(cherry) - Φ_η(broom₃)`

Derivation (re-derived in scratch before writing):
1. `Φ_{⟦M⟧⁻¹}(broom₃) = -∑ᵢ M.b i · M.derivativeWeightWithSrc M.inverse i broom₃` (cycle 358 `_inv_mk`).
2. `M.derivativeWeightWithSrc M.inverse i broom₃ = (M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j)^2` (two-layer unfold + `derivativeWeightWithSrc_vertex` + `derivativeWeightWithSrcProd []` collapse).
3. `M.inverse.elementaryWeight vertex = -M.elementaryWeight vertex` (cycle 367 `h_inv_v`).
4. Hence `Φ_{⟦M⟧⁻¹}(broom₃) = -∑ᵢ M.b i · (Aᵢ - v)^2` where `v := M.elementaryWeight vertex` and `Aᵢ := ∑ⱼ M.A i j`.
5. Expand: `(Aᵢ - v)^2 = Aᵢ^2 - 2·v·Aᵢ + v^2`. Sum-distribute: `∑ᵢ M.b i · (Aᵢ^2 - 2·v·Aᵢ + v^2) = ∑ᵢ M.b i·Aᵢ^2 - 2·v · ∑ᵢ M.b i·Aᵢ + v^2 · ∑ᵢ M.b i = M.elementaryWeight broom₃ - 2·v·M.elementaryWeight cherry + v^3`.
6. Negate to get the stated form.

The Lean statement captures: **same content** as the paper derivation
(strategy §B.1 closed form). No hypothesis weakening or strengthening.
The theorem is a pure rewrite identity over the quotient class, no
extra assumptions beyond `η_q : Quotient PhiEquivalent.setoidSigma`.

### `powRep_sum_eq_of_agreement_at_broom₃_zero`
Specialisation of Sub-lemma A at `t = broom₃, m = 0`. Sub-lemma A's
full statement requires agreement at all strict subtrees of `t`; for
broom₃ the strict subtrees are `vertex` and `cherry` (each appearing
as a child or as a partial-subterm of the closed form). The cycle 368
closed-form theorem reveals that `Φ_{η⁻¹}(broom₃)` depends on
`Φ_η(vertex), Φ_η(cherry), Φ_η(broom₃)`, so three agreement
hypotheses are required.

The Lean statement captures: **same content** as the Sub-lemma A
m=0 specialisation. Hypothesis count (3) matches the closed form's
factor count, not stronger than necessary.

### Two `example`s (non-vacuity)
Both are `example` declarations (no public name), so they have no
textbook correspondence — they exercise the new theorems on
`explicitEuler` to demonstrate non-vacuity. No faithfulness issue.

## Dead ends
None this cycle. The proof recipe followed strategy §C exactly with
no detours. Specifically:
- Path A (per-summand `ring` expansion via `Finset.sum_congr` then
  linearity-distribute) closed on the first attempt without needing
  Path B fallback.
- The `← h_broom₃, ← h_cherry, ← h_vertex` rewrite chain matched the
  expected pattern; no need to flip directions or insert intermediate
  rewrites.
- The non-vacuity `h_broom₃_zero` step followed the cycle 367 cherry
  template exactly with one extra `[RootedTree.vertex]` argument to
  `derivativeWeightProd`.

## Discovery
The two-child unfold for `broom₃ = mk [vertex, vertex]` reduces to
the *exact same algebraic factor* as the one-child unfold for
`cherry = mk [vertex]`:

`derivativeWeightWithSrcProd M.inverse i [vertex] = M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j`
                                                   * (a `*1` from the trailing `[]` base case)

This is because both children are `vertex`, so each evaluates the
same factor `M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j ·
M.derivativeWeightWithSrc M.inverse j vertex`, with the inner sum
collapsing via `derivativeWeightWithSrc_vertex = 1` to `∑ⱼ M.A i j`.
Hence `derivativeWeightWithSrc M.inverse i broom₃` factorises as a
*square* of that linear expression, and the closed form is a
polynomial of degree 3 in `(v, Aᵢ, M.b i)`-aggregates.

This pattern suggests the general broom-of-k tree `mk [vertex, …, vertex]`
(k copies of vertex) admits a degree-(k+1) closed form
`Φ_{η⁻¹}(broom_k) = -∑ᵢ M.b i · (Aᵢ - v)^k`, expandable per-summand
via `(a + b)^k`. This is potentially a Route B lever for higher-order
trees (cycle 369+ work).

The per-summand `ring` expansion (Path A) is far more reliable than
the `add_pow_two`-based Path B fallback. Reapply the Path A pattern
verbatim for any future order-k closed form attempt: substitute closed
forms in a single `Finset.sum_congr`, then sum-distribute, then
`← Finset.mul_sum` for each constant factor, then back-substitute via
`← h_*` rewrites, then `ring`.

## Suggested next approach

Per cycle 368 strategy §L, with the broom₃ closed form shipped cleanly
in one cycle, the **Route B Hypothesis** (cycle 366 §G) is now
supported by THREE data points (vertex, cherry, broom₃). Cycle 369
should consider one of these escalation paths:

**Option A (recommended, per strategy §L):** Attempt the **inductive
`t.order` formulation of Sub-lemma A**. The accumulating pattern
suggests a uniform `Φ_{η⁻¹}(t)` closed form indexed by tree depth.
Concretely:
- Define an auxiliary "Φ-polynomial extraction" predicate
  `closedFormAt η_q t` asserting that `Φ_{η_q^(-1)}(t)` is computable
  from `Φ_η` at strict subtrees of `t` via a fixed polynomial.
- Prove it by induction on `t.order`, with the inductive step using
  the `derivativeWeightWithSrcProd_cons` recursion to peel off one
  child at a time and reduce to a polynomial in `Φ_η(child)` and
  `∑ⱼ M.A i j · Φ-stuff`.
- The base cases are vertex (cycle 366), and the inductive step
  recovers the cherry / broom₃ patterns at `mk [t_i]` / `mk [t_1, …]`.

**Option B:** Continue the per-tree witness ladder with `mk [cherry]`
(the fourth order-3 tree). This is a "vertical" extension (root with
one child that is itself cherry) and exercises a different unfold
pattern. Useful as another data point if Option A's inductive
formulation needs more guidance.

**Option C (stretch, NOT recommended for cycle 369):** General-m
cherry closed form `powRep_inv_cherry_closed_form` per cycle 367 §C.2.
This needs a `Φ_{η₁·η₂}(cherry)` decomposition lemma that is itself
multi-cycle; defer until Option A's inductive scaffold is in place.

Cycle 369 should pick **Option A** for maximum forward progress: it
directly attacks the multi-cycle Route B closure rather than adding
another single-tree data point. If the inductive scaffold proves
intractable in one cycle, fall back to Option B as a cycle 370 backup.

The Sub-lemma A grandfathered sorry (line 2272 / 2279 depending on
post-edit numbering) remains untouched per cycle 368 strategy §H. It
is reserved for the cycle 369+ Route B / Route A closure.
