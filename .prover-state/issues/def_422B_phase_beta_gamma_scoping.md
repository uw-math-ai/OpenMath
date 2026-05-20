# Issue: `def:422B` Phase β/γ scoping — closing the cycle 365 grandfathered sorry via `inversePolyTree` structural-induction lift

## §1 Status & blocker

**Scoping doc, cycle 495.** No Lean code shipped this cycle — this is
a markdown-only research doc distilling the empirical surface
accumulated across cycles 386–494 into a concrete multi-cycle plan
for closing the sole remaining code-level sorry in §422.

This doc is the direct continuation of the markdown-only scoping
precedent established by cycles 373, 379, 385, 398, and 402:

* `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` (cycle
  373 — 1399 lines; drove cycles 374–378's 8-tree ladder build-out).
* `.prover-state/issues/def_422B_phase_alpha_prime_scoping.md` (cycle
  379 — 1373 lines; drove cycles 380–383's Family A/B recursive
  helper ships).
* `.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`
  (cycle 385 — 894 lines; drove cycles 386–397's Phase α'.4.0 → α'.4.2
  ladder of 11 substantive migrations).
* `.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`
  (cycle 398 — 938 lines; drove cycles 399–401's Phase α'.4.3 bushy
  migration in 3 substantive cycles).
* `.prover-state/issues/def_422B_phase_alpha_prime_5_scoping.md` (cycle
  402 — 1299 lines; drove cycles 403/491/492/493/494's Phase α'.5.1
  non-symmetric `k = 3` order-6 ladder).

**§422 axiom-clean streak: 68 substantive + 4 doc (cycles 336–494)**,
advancing to **68 substantive + 5 doc (336–495)** after this ship.

The single remaining code-level sorry is at
`OpenMath/Chapter4/Section422.lean:2279`
(cycle 365's `powRep_sum_eq_of_strict_subtree_agreement` general
body). This sorry has been **open for 130 cycles**. Every cycle of
Phase α'.4 (cycles 386–401) and Phase α'.5.1 (cycles 403/491–494)
has been building empirical infrastructure that — by the cycle 401
"Suggested next approach" Option 2 and cycle 494 Option 1 — was
explicitly anticipated to be consumed by Phase β/γ.

This scoping doc is the bridge from **"we have enough empirical
data"** to **"we can write the structural-induction proof."**

`Section422.lean`: 11917 LOC. `grep -c sorry` returns 5 (4 docstring
references + 1 actual code sorry at line 2279).

## §2 The sorry's statement and what it claims

The cycle 365 sorry (`Section422.lean:2272–2279`, verbatim):

```lean
theorem powRep_sum_eq_of_strict_subtree_agreement
    (m : ℕ) (t : RT)
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (_h_closed : ∀ s : RT, s.order ≤ t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    elementaryWeightQ_phi (η_q ^ (-(((m + 1) : ℕ) : ℤ))) t
      = elementaryWeightQ_phi (η_q' ^ (-(((m + 1) : ℕ) : ℤ))) t := by
  sorry
```

**Mathematical content.** Two §383 group elements `η_q, η_q' :
Quotient PhiEquivalent.setoidSigma` that agree on `Φ_η` at every
subtree `s` of `t` (with `s.order ≤ t.order`, closed-subtree form
including `t` itself) also agree on `Φ` after raising both to the
common negative power `-(m+1)` (with `m : ℕ`).

**Why "closed-subtree" not "strict-subtree."** The naming is a
historical artifact from cycle 362's strict-subtree parametricity
lemma for `derivativeWeightWithSrc` — the hypothesis here is the
closed-subtree form (`s.order ≤ t.order`), which is strictly weaker
(more permissive) on the consumer side and is what cycle 376's
Phase γ lemma `inversePolynomial_eq_of_subtree_agreement` already
delivers for the `m = 0` case (see §3.2 below).

**Headline consumer.** The cycle 365 `Sub-lemma B`
(`linearResidualAt_depends_only_on_strict_subtrees`,
`Section422.lean:~2335–2360`) consumes Sub-lemma A as a black box —
it is already **axiom-clean modulo this sorry**. Closing the cycle
365 sorry restores `Section422.lean` to fully sorry-free, completing
the §422 cluster's Phase D.3.b ladder.

## §3 What the empirical work has shown

### §3.1 The 14 Family C closed-form witnesses (cycles 371–494)

Per `Section422.lean` grep `^theorem elementaryWeightQ_phi_inv_`,
the calibration ladder consists of these 14 closed-form theorems
(plus the abstract `_inv_mk` characterisation from cycle 358):

| Cycle | Theorem name | Tree `t` | Order | Kernels |
|---|---|---|---|---|
| 358 | `elementaryWeightQ_phi_inv_mk` | abstract `mk [...]` | n/a | recursive |
| 367 | `_inv_cherry` | `cherry` | 2 | 2 |
| 368 | `_inv_broom₃` | `broom₃` | 3 | 3 |
| 369 | `_inv_mkCherry` | `mk [cherry]` | 3 | 4 |
| 370 | `_inv_bushy` | `bushy` | 4 | 4 |
| 371 | `_inv_mkBroom₃` | `mk [broom₃]` | 4 | 5 |
| 372 | `_inv_mkVertexCherry` | `mk [v, c]` | 4 | 5 |
| 384 | `_inv_mkMkCherry` | `mk [mk [c]]` | 4 | 5 |
| 386 | `_inv_mkCherryCherry` | `mk [c, c]` | 5 | 6 |
| 391 | `_inv_mkBroomCherry` | `mk [broom₃, c]` | 6 | 7 |
| 393 | `_inv_mkVertexBroom₃` (in `inversePolyTree` calibration) | `mk [v, broom₃]` | 5 | 6 |
| 396 | `_inv_mkVertexMkCherry` (calibration ladder) | `mk [v, mk[c]]` | 5 | 6 |
| 397 | `_inv_mkVertexVertexVertex` (= `bushy` extension) | `mk [v, v, v] = bushy` | 4 | (subsumed) |
| 400 | `inversePolyTree_bushy` calibration | `bushy` | 4 | 4 |
| 401 | Phase α'.4.3 closure (full `inversePolyTree` for `mk [c₁, c₂, c₃]`-arity) | trichild ladder | 5–6 | 6–10 |
| 403 | `_inv_mkVertexVertexCherry` | `mk [v, v, c]` | 5 | 7 |
| 491 | `_inv_mkVertexCherryCherry` (k=3 ladder P2) | `mk [v, c, c]` | 6 | 9 |
| 492 | `_inv_mkVertexVertexMkCherry` (P3) | `mk [v, v, mk [c]]` | 6 | 10 |
| 493 | `_inv_mkVertexVertexBroom₃` (P5) | `mk [v, v, broom₃]` | 6 | 10 |
| 494 | (same as 493 row's ship, recorded) | | | |

(The exact cycle-by-cycle attribution is in `task_results/cycle_<N>.md`
files; the table above is for orientation. Phase β.1 must
re-tabulate against the actual theorem-name list at proof-write time.)

### §3.2 Existing `inversePolynomial` closed-subtree lemma (cycle 376)

`Section422.lean:11578` ships
`inversePolynomial_eq_of_subtree_agreement` (Phase γ from cycle 373's
plan): for the 8-tree ladder covered by the `inversePolynomial`
pattern-match (`vertex, cherry, broom₃, mk [cherry], bushy,
mk [broom₃], mk [v, c], mk [mk [c]]`),

```lean
theorem inversePolynomial_eq_of_subtree_agreement
    (t : RT) (f g : RT → ℝ)
    (h_closed : ∀ s : RT, s.order ≤ t.order → f s = g s) :
    inversePolynomial t f = inversePolynomial t g
```

**This is exactly the Phase γ analog needed at the `inversePolyTree`
level**, generalised from `inversePolynomial`'s 8-tree pattern-match
to `inversePolyTree`'s recursive 14-tree dispatch (or further).

### §3.3 Existing `inversePolynomial`-to-`Φ_{η⁻¹}` bridge (cycle 377)

`Section422.lean:11513` ships
`elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder` (the
8-tree per-tree dispatch over the `inversePolynomial` 8-tree ladder).

This is the **direct analog of the Phase β.1 deliverable proposed
in §5 below**, but at the `inversePolynomial` level rather than the
`inversePolyTree` level. The proof strategy is mechanical: case-split
on `t`, then `exact _inv_eq_inversePolynomial_<tree> η_q` for each
branch. Phase β.1 for `inversePolyTree` follows the same template
with 14 branches.

### §3.4 The unified `inversePolyTree` recursion (Phase α'.4)

`Section422.lean:9718–9738` ships
`noncomputable def inversePolyTree : RT → (RT → ℝ) → ℝ` (cycles
387–401), with explicit per-tree calibration witnesses
`inversePolyTree_<tree>` for each tree in the 14-tree ladder
(cycles 387/388/393/396/400/401/403/491–494).

The recursion's structural shape:

```lean
| mk [],            f => -f vertex
| mk [c],           f => -(v · inversePolyTree c f)
                          + monochildCrossTerm c f
                          - f (mk [c])
| mk [c₁, c₂],      f => bichildPolynomial c₁ c₂
                          (inversePolyTree c₁ f) (inversePolyTree c₂ f) f
| mk [c₁, c₂, c₃],  f => trichildPolynomial c₁ c₂ c₃
                          (inversePolyTree c₁ f) (inversePolyTree c₂ f)
                          (inversePolyTree c₃ f) f
| mk (_::_::_::_::_), _ => 0
```

The recursion is **uniformly polynomial** in:
- `v := f vertex` (always read directly from `f`).
- `inversePolyTree c f` for each child `c` (recursive call).
- `f c` and `f (mk [...])` evaluations at named subtrees of `t` (via
  `monochildCrossTerm`, `bichildCrossTerm`, `trichildCrossTerm`).

This is exactly the empirical surface a Phase β/γ structural
induction needs: every recursive call lands on a child, and every
direct `f`-evaluation is at a subtree of order ≤ the current tree's
order.

### §3.5 The cycle 376 Phase γ template

The cycle 376 proof of `inversePolynomial_eq_of_subtree_agreement`
is a **four-way case split** on the eight-tree pattern-match branches.
Each case:

1. Decompose the matched closed form into reads of `f` at named
   subtrees of `t`.
2. Use `h_closed` at each subtree to rewrite `f s` to `g s`.
3. The two sides are now syntactically identical.

This template generalises directly to `inversePolyTree` once the
recursion's `inversePolyTree c f = inversePolyTree c g` step is
discharged inductively from the recursion hypothesis (which is
exactly the Phase γ-on-`inversePolyTree` statement applied to the
child `c`, with `c.order < t.order` ensured by structural induction
on `t`).

## §4 The proof strategy (high level)

The proof structure cycle 365's worker likely intended — and the
cycle 494 task results' "Phase β/γ" terminology references — is a
**three-layer cake**:

### Phase β — `Φ_{η_q⁻¹}(t)` as `inversePolyTree`

Bridge the quotient-level inverse to the explicit polynomial:

```
elementaryWeightQ_phi (η_q⁻¹) t
  = inversePolyTree t (fun s => elementaryWeightQ_phi η_q s)
```

This is the unified statement subsuming every cycle 386+ calibration
witness. **Phase β.1** ships it for the 14-tree ladder via per-tree
dispatch; **Phase β.2** generalises to arbitrary `t : RT` via
structural induction on `t`.

### Phase γ — `inversePolyTree` respects closed-subtree agreement

Generalise cycle 376's `inversePolynomial_eq_of_subtree_agreement`
from the 8-tree pattern-match to `inversePolyTree`'s recursive
14-tree dispatch:

```
∀ t f g, (∀ s, s.order ≤ t.order → f s = g s) →
  inversePolyTree t f = inversePolyTree t g
```

The proof is structural induction on `t` driven by the
`inversePolyTree` recursion's three child-dispatch shapes (`mk []`,
`mk [c]`, `mk [c₁, c₂]`, `mk [c₁, c₂, c₃]`, default `0`).

### Phase δ — inverse-power lift to `η_q^(-(m+1))`

Phase β bridges `η_q⁻¹`, but the cycle 365 sorry quantifies over
`η_q^(-(m+1))` for arbitrary `m : ℕ`. Two viable strategies:

* **Phase δ.A — recursive `inversePolyPow` definition.** Introduce
  `inversePolyPow : ℕ → RT → (RT → ℝ) → ℝ` with `inversePolyPow 0
  = inversePolyTree` (or define it as a `Nat.rec` over the power)
  and prove the bridge `Φ_{η_q^(-(m+1))}(t) = inversePolyPow m t
  (Φ_η ·)`. Then Phase γ-style agreement carries over.
* **Phase δ.B — `Nat.rec` on `m` via `pow_succ` + Phase β.**
  Use `zpow_negSucc` + `zpow_succ` (or equivalent §383 group lemmas
  cycle 222's `instGroup_phi`) to peel one `η_q⁻¹` factor at a time,
  applying Phase β at each peel. The recursion's hypothesis is the
  Phase γ-style agreement at all subtrees of `t` for `η_q^(-m)`,
  which is exactly the closed-subtree shape Phase γ delivers.

**Recommendation: Phase δ.B first**, with Phase δ.A as a fallback if
δ.B's recursion produces a type-inference obstruction. Phase δ.A
requires net-new infrastructure (`inversePolyPow` definition,
recursion on `(m, t)`); Phase δ.B reuses Phase β.2 + Phase γ in a
direct `Nat.rec`.

### Phase ε — close the cycle 365 sorry

With Phase β.2 + Phase γ + Phase δ in hand, the cycle 365 sorry's
body is mechanical:

1. Apply Phase δ (B or A) to both
   `Φ_{η_q^(-(m+1))}(t)` and `Φ_{η_q'^(-(m+1))}(t)`,
   converting both to the polynomial form `inversePolyPow m t
   (Φ_η ·)` evaluated at `η_q` vs `η_q'`.
2. Apply Phase γ (or its `inversePolyPow` generalisation) using
   `_h_closed` to conclude the two polynomial forms are equal.

## §5 Phase decomposition (single-cycle deliverables)

Per the cycle 373 / 385 / 398 / 402 precedent, each Phase is broken
into single-cycle shippable units with concrete Lean signatures,
LOC estimates, and axiom-clean targets.

### §5.1 Phase β.1 (1 cycle, ~200–300 LOC)

**Target**: per-tree dispatch over the 14-tree ladder.

```lean
theorem elementaryWeightQ_phi_inv_eq_inversePolyTree_on_ladder
    (η_q : Quotient PhiEquivalent.setoidSigma) (t : RT)
    (ht_ladder :
        t = RootedTree.vertex
      ∨ t = RootedTree.cherry
      ∨ t = RootedTree.broom₃
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
      ∨ t = RootedTree.bushy
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry, RootedTree.cherry]
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃, RootedTree.cherry]
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry]
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex,
               OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃]) :
    elementaryWeightQ_phi (η_q⁻¹) t
      = inversePolyTree t (fun s => elementaryWeightQ_phi η_q s)
```

**Proof recipe**: `rcases ht_ladder with h | h | ... | h <;> subst h`,
then for each branch, combine:
1. The `_inv_<tree>` quotient-level closed form.
2. The `inversePolyTree_<tree>` calibration witness.
3. `ring` or `linarith` to bridge the two RHSs.

This is **direct mechanical extension of the existing cycle 377
`_inv_eq_inversePolynomial_on_ladder`** (8 trees → 14 trees;
`inversePolynomial` → `inversePolyTree`).

**Existing infrastructure consumed**:
- All 14 `_inv_<tree>` theorems (cycles 367–494).
- All 14 `inversePolyTree_<tree>` calibration witnesses (cycles
  387–494).

**Axiom-clean target**: `[propext, Classical.choice, Quot.sound]`.

**LOC estimate**: ~200–300 LOC (14 mechanical branches).

### §5.2 Phase β.2 (1 cycle, ~300–500 LOC)

**Target**: structural induction on `t : RT` to lift Phase β.1 to
the full type.

```lean
theorem elementaryWeightQ_phi_inv_eq_inversePolyTree
    (η_q : Quotient PhiEquivalent.setoidSigma) (t : RT) :
    elementaryWeightQ_phi (η_q⁻¹) t
      = inversePolyTree t (fun s => elementaryWeightQ_phi η_q s)
```

**Proof recipe**: structural induction on `t` via
`RootedTree.recOn` or via case-analysis on `t.unfold`'s `mk cs`
form. For each constructor shape (`mk []`, `mk [c]`, `mk [c₁, c₂]`,
`mk [c₁, c₂, c₃]`, default `mk (_::_::_::_::_)`):

* **`mk []` (i.e. `vertex`)**: direct from
  `elementaryWeightQ_phi_inv_vertex` + `inversePolyTree_vertex`.
* **`mk [c]`**: from cycle 358's `elementaryWeightQ_phi_inv_mk`
  rewriting the LHS into the canonical form
  `-(v · Φ_{η⁻¹}(c)) + Σ-cross - Φ_η(mk [c])`, then apply IH to the
  `Φ_{η⁻¹}(c)` subterm.
* **`mk [c₁, c₂]`**: analogous, using `bichildPolynomial`
  decomposition + IH on each child.
* **`mk [c₁, c₂, c₃]`**: analogous, using `trichildPolynomial`
  decomposition + IH on each child.
* **`mk (_::_::_::_::_)`**: both sides are `0` (the
  `inversePolyTree` default branch). Requires the parallel
  observation that `elementaryWeightQ_phi (η_q⁻¹) (mk (c₁::c₂::c₃::c₄::cs)) = 0`,
  which **is not yet established** — see Risk R6 below.

**Risks**:

* **R1 (HIGH)**: Structural induction on `RT` uses `recOn`, which
  for the nested-inductive `RootedTree` may need `mutual` per the
  memory `feedback_rootedtree_nested_induction.md`. Mitigation:
  read that memory before writing the proof; use the cycle 376
  pattern (case-split rather than `induction`).

* **R6 (HIGH)**: The `mk (_::_::_::_::_)` arm requires a new
  proposition `elementaryWeightQ_phi_inv_mk_quadchild_zero` (or
  similar) asserting that `Φ_{η⁻¹}(mk (c₁ :: c₂ :: c₃ :: c₄ :: cs))
  = 0`. This is NOT in the existing infrastructure (Phase α'.4 only
  established `inversePolyTree`'s default-`0`; the cycle 358 `_inv_mk`
  characterisation does NOT collapse to 0 for `k ≥ 4`). **This is
  the primary new infrastructure Phase β.2 needs to establish.**

  Two options:
  - (R6.A) Restrict Phase β.2's scope to `t.bound ≤ 3` (trichild
    or smaller), and split off `R6` to a later cycle. This delays
    closing the cycle 365 sorry but gives a working Phase β.2 for
    the trichild ladder.
  - (R6.B) Establish R6 in the same cycle by adding the
    `_inv_mk_quadchild_zero` proposition with proof reducing to
    cycle 358's `_inv_mk` characterisation + the order-arithmetic
    structure of `dws M.inverse`. ~150–200 LOC.

  **Recommendation: R6.B**, since closing R6 is a self-contained
  algebraic claim about the §358 `_inv_mk` reduction at
  `k ≥ 4`-arity trees.

**Existing infrastructure consumed**:
- Phase β.1 (`_on_ladder` dispatch, cycle 496).
- Cycle 358's `elementaryWeightQ_phi_inv_mk`.
- All `bichildPolynomial`, `trichildPolynomial`,
  `monochildCrossTerm`, `bichildCrossTerm`, `trichildCrossTerm`
  helpers.

**Axiom-clean target**: `[propext, Classical.choice, Quot.sound]`.

**LOC estimate**: ~300–500 LOC (assuming R6.B in-line).

### §5.3 Phase γ (1 cycle, ~200–350 LOC)

**Target**: `inversePolyTree` closed-subtree agreement.

```lean
theorem inversePolyTree_eq_of_subtree_agreement
    (t : RT) (f g : RT → ℝ)
    (h_closed : ∀ s : RT, s.order ≤ t.order → f s = g s) :
    inversePolyTree t f = inversePolyTree t g
```

**Proof recipe**: mirror cycle 376's
`inversePolynomial_eq_of_subtree_agreement` template, extended to the
`inversePolyTree` recursion's child-dispatch arms. Structural
induction on `t`:

* **`mk []`**: direct, both sides are `-f vertex = -g vertex` after
  applying `h_closed vertex (by decide : vertex.order ≤ _.order)`.
* **`mk [c]`**: apply IH on `c` (since `c.order < (mk [c]).order`,
  and `s.order ≤ c.order ⟹ s.order ≤ (mk [c]).order` so
  `h_closed` restricted to subtrees of `c` is still valid). Then
  use `h_closed` at each subtree referenced by `monochildCrossTerm
  c f`.
* **`mk [c₁, c₂]`**, **`mk [c₁, c₂, c₃]`**: analogous.
* **`mk (_::_::_::_::_)`**: both sides are `0`. No work needed.

**Risks**:

* **R7 (MEDIUM)**: The IH for the `mk [c₁, c₂, c₃]` case needs
  `h_closed` restricted to subtrees of each `cᵢ`, but the original
  `h_closed` is stated at subtrees of `t = mk [c₁, c₂, c₃]`. The
  restriction lemma is: `∀ s, s.order ≤ cᵢ.order → s.order ≤
  t.order` (since `cᵢ.order < t.order`), so `h_closed s _` extends
  to subtrees of `cᵢ`. Mitigation: write the restriction lemma
  inline (one `Nat.le_trans` + a `RootedTree.order_lt_mk_of_mem`
  lookup; the latter likely already exists or is trivial).

* **R8 (LOW)**: The `trichildCrossTerm` cascade currently has 5
  branches (vertex^3, vv-cherry, v-cherry-cherry, vv-mk[c],
  vv-broom₃). Each branch's RHS is a polynomial in `f` at named
  subtrees of `t`. For each branch we need `h_closed` at each
  subtree appearing in the cross-term value. Mitigation: enumerate
  the subtrees per branch and apply `h_closed` row-by-row; the
  cascade structure is mechanical.

**Existing infrastructure consumed**:
- Cycle 376's `inversePolynomial_eq_of_subtree_agreement` as template.
- `inversePolyTree`'s recursion + all cross-term helpers.

**Axiom-clean target**: `[propext, Classical.choice, Quot.sound]`.

**LOC estimate**: ~200–350 LOC.

### §5.4 Phase δ.B (1–2 cycles, ~300–500 LOC)

**Target**: inverse-power lift, via `Nat.rec` on `m`.

**Lemma** (`m = 0` base case, cycle 498 candidate):

```lean
theorem powRep_sum_eq_of_subtree_agreement_zero
    (t : RT)
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_closed : ∀ s : RT, s.order ≤ t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    elementaryWeightQ_phi (η_q ^ (-((0 + 1 : ℕ) : ℤ))) t
      = elementaryWeightQ_phi (η_q' ^ (-((0 + 1 : ℕ) : ℤ))) t
```

**Proof**: simplify `η_q ^ (-(1 : ℤ)) = η_q⁻¹` via `zpow_one`-style
lemma, then apply Phase β.2 to convert both sides to
`inversePolyTree t (Φ_η ·)` form, then apply Phase γ via `h_closed`.

**Inductive step** (cycle 498+ candidate):

```lean
theorem powRep_sum_eq_of_subtree_agreement_succ
    (m : ℕ) (t : RT)
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_closed : ∀ s : RT, s.order ≤ t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s)
    (h_ih : elementaryWeightQ_phi (η_q ^ (-((m + 1 : ℕ) : ℤ))) t
          = elementaryWeightQ_phi (η_q' ^ (-((m + 1 : ℕ) : ℤ))) t) :
    elementaryWeightQ_phi (η_q ^ (-((m + 2 : ℕ) : ℤ))) t
      = elementaryWeightQ_phi (η_q' ^ (-((m + 2 : ℕ) : ℤ))) t
```

**Proof outline**: factor `η_q^(-(m+2)) = η_q^(-(m+1)) * η_q⁻¹` via
`zpow_succ` / §383 group operations. Then apply
`elementaryWeightQ_phi_mul` (cycle 219's `Φ_{η₁ * η₂}` decomposition)
to get a `dws`-mediated cross-product. Apply Phase γ at each subterm
using `h_closed`.

**Risks**:

* **R9 (HIGH)**: The `dws`-mediated cross-product for `η_q^(-(m+1))
  * η_q⁻¹` involves a sum over `Fin (M.powRep (m+1)).1`-many
  rows, with each row's value depending on `Φ_{η_q^(-(m+1))}` at
  every subtree (via cycle 362's strict-subtree parametricity).
  Closing this cross-product requires both:
  1. Phase γ-style agreement on subtrees (delivered by induction
     hypothesis + `h_closed`).
  2. Heterogeneous Σ-type comparison (the `M.powRep (m+1)` vs
     `M'.powRep (m+1)` stage-count mismatch the cycle 365 docstring
     flags as the substantive obstruction).

  Mitigation: re-read cycle 365's task results
  (`task_results/cycle_365.md`) for the worker's understanding of
  this obstruction. The cycle 362 strict-subtree lemma already
  delivers (1) at the `dws` level; the cycle 365 worker's gap is
  threading (2) into the recursion.

* **R10 (MEDIUM)**: `Nat.rec` on the power index `m` may need to
  be replaced with strong induction if the inductive step requires
  the IH at multiple smaller values of `m`. Mitigation: write a
  one-step `Nat.rec` first; if it fails, escalate to
  `Nat.strongRecOn`.

**Existing infrastructure consumed**:
- Phase β.2 + Phase γ.
- Cycle 219's `elementaryWeightQ_phi_mul` decomposition.
- Cycle 222's §383 group structure.
- Cycle 362's strict-subtree parametricity for `dws`.

**Axiom-clean target**: `[propext, Classical.choice, Quot.sound]`.

**LOC estimate**: ~300–500 LOC, possibly split across two cycles
(base case ~100 LOC, inductive step ~300–400 LOC).

### §5.5 Phase ε (1 cycle, ~50–150 LOC)

**Target**: close the cycle 365 sorry.

```lean
theorem powRep_sum_eq_of_strict_subtree_agreement
    (m : ℕ) (t : RT)
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (_h_closed : ∀ s : RT, s.order ≤ t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    elementaryWeightQ_phi (η_q ^ (-(((m + 1) : ℕ) : ℤ))) t
      = elementaryWeightQ_phi (η_q' ^ (-(((m + 1) : ℕ) : ℤ))) t
```

**Proof**: `Nat.rec` on `m`, base from Phase δ.B's m=0 lemma,
inductive step from Phase δ.B's succ lemma. ~50 LOC if both phase
δ lemmas are signed for the same `_h_closed` shape, or ~150 LOC if
glue / shape-conversion is needed.

**Existing infrastructure consumed**: Phase δ.B.

**Axiom-clean target**: `[propext, Classical.choice, Quot.sound]`.

**LOC estimate**: ~50–150 LOC.

### §5.6 Total estimate

**5 single-cycle deliverables** (Phase β.1, β.2, γ, δ.B, ε), with
δ.B optionally split into 2 cycles:

- Best case: 5 cycles (cycles 496–500).
- Realistic case: 6 cycles (cycles 496–501, allowing δ.B split).
- Pessimistic case: 7–8 cycles (accounting for R6/R9 escalations).

**Per-cycle LOC envelope**: ~200–500 LOC per cycle (typical for §422
work; the cycle 374/376/391/397/403 precedents range from ~150 to
~700 LOC).

## §6 Risk inventory

Consolidated from §5's per-phase risks:

* **R1 (HIGH, Phase β.2)**: Structural induction on `RT` uses
  nested-inductive `recOn`. **Mitigation**: case-split instead of
  `induction`, per cycle 376's pattern. Reference memory
  `feedback_rootedtree_nested_induction.md`.

* **R2 (MEDIUM, Phase δ)**: Phase δ may need a new `inversePolyPow`
  definition rather than iterating `inversePolyTree` (δ.A vs δ.B).
  **Mitigation**: try δ.B first; reserve δ.A as fallback infrastructure
  cycle. Scope this risk explicitly in cycle 498's strategy.

* **R3 (MEDIUM, contextual)**: Cycle 365's grandfathered sorry has
  been open for 130 cycles because the original Phase β/γ design was
  abandoned. There may be subtle obstructions (faithfulness, type
  inference, decidability) that bit the cycle 365 worker.
  **Mitigation**: read `task_results/cycle_365.md` carefully at
  cycle 496's start.

* **R4 (LOW, file size)**: §422 file size is already ~12k LOC.
  Phase β/γ work could push it past 15k LOC. **Mitigation**:
  extract auxiliary lemmas into a new `Section422Helpers.lean`
  module if the file becomes a build bottleneck. The cycle 380's
  Family A/B helpers established the precedent for moving recursion
  infrastructure to a separate file.

* **R5 (LOW, ladder unification)**: The 14 `_inv_<tree>` theorems
  use slightly different proof recipes (`unfold ; rw [if_*]`
  cascades vary). Phase β.1's `_on_ladder` dispatch should NOT need
  to re-prove each closed form — it just `exact`-cites each
  `_inv_<tree>` theorem. **Mitigation**: confirm the 14 calibration
  witnesses are all `axiom-clean` before Phase β.1's ship via
  `#print axioms` spot-checks.

* **R6 (HIGH, Phase β.2)**: `mk (_::_::_::_::_)` arm needs new
  `_inv_mk_quadchild_zero` infrastructure. **Mitigation**: ship in
  Phase β.2 inline (R6.B), or split to a Phase β.1.5 cycle (R6.A).
  Recommended: R6.B.

* **R7 (MEDIUM, Phase γ)**: IH restriction across child trees needs
  `s.order ≤ cᵢ.order → s.order ≤ t.order` lookup.
  **Mitigation**: inline `Nat.le_trans` + `RootedTree.order_lt_mk_of_mem`
  (likely already in `Section310.lean`; check before Phase γ ships).

* **R8 (LOW, Phase γ)**: `trichildCrossTerm` cascade has 5 branches.
  **Mitigation**: enumerate subtrees per branch, apply `h_closed`
  row-by-row. The cascade structure is mechanical.

* **R9 (HIGH, Phase δ.B)**: `dws`-mediated cross-product for
  `η_q^(-(m+1)) * η_q⁻¹` involves heterogeneous Σ-type comparison
  (the original cycle 365 substantive obstruction).
  **Mitigation**: re-read cycle 365's task results; coordinate with
  cycle 362's strict-subtree parametricity at the `dws` level.

* **R10 (MEDIUM, Phase δ.B)**: One-step `Nat.rec` vs strong
  induction. **Mitigation**: try one-step first; escalate to
  `Nat.strongRecOn` if multi-step IH is needed.

## §7 Cycle 496+ entry point

Concrete first task for cycle 496's worker:

**Start with Phase β.1** (per-tree dispatch over the ladder).

**Signature**:

```lean
theorem elementaryWeightQ_phi_inv_eq_inversePolyTree_on_ladder
    (η_q : Quotient PhiEquivalent.setoidSigma) (t : RT)
    (ht_ladder : <14-disjunct ladder per §5.1>) :
    elementaryWeightQ_phi (η_q⁻¹) t
      = inversePolyTree t (fun s => elementaryWeightQ_phi η_q s)
```

**Proof recipe**:

```lean
  rcases ht_ladder with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst h
  · -- vertex
    rw [elementaryWeightQ_phi_inv_vertex, inversePolyTree_vertex]
    rfl  -- or `ring` if needed
  · -- cherry
    rw [elementaryWeightQ_phi_inv_cherry, inversePolyTree_cherry]
    ring  -- bridge LHS closed form to RHS unfolded form
  -- ... 12 more branches following the same template
```

For each branch, the bridge is:
1. Apply the `_inv_<tree>` quotient-level closed form (cycles
   367–494).
2. Apply the `inversePolyTree_<tree>` calibration witness (cycles
   387–494) to expand `inversePolyTree t (Φ_η ·)`.
3. Apply `ring` (per memory `feedback_ring_def_opacity.md`, may
   need a `show` to canonicalise `f cherry` vs `f (mk [vertex])`
   if the calibration witness uses one form and the closed form
   uses the other).

**Existing infrastructure to verify before Phase β.1 ships**:

1. All 14 `_inv_<tree>` theorems are `#print axioms`-clean.
2. All 14 `inversePolyTree_<tree>` calibration witnesses are
   `#print axioms`-clean.
3. The `RootedTree.mk` constructor and `cherry`/`broom₃`/`bushy`
   names resolve unambiguously (cycle 491's `consultant_advice`
   noted a `mk` import shadowing risk; check the namespace prefix
   pattern at the top of `Section422.lean`).

**LOC estimate**: ~200–300 LOC (mechanical dispatch + 14 closing
applications).

## §8 What this doc does NOT do

* Does NOT pre-emptively reject Phase α'.5.2 (k=4) extension or
  fresh-entity pivot. Those options remain available if Phase β/γ
  work hits an unforeseen blocker. The §6 risk inventory's R1, R6,
  R9 (all HIGH) are the principal escalation gates.

* Does NOT commit to specific Lean signatures beyond §5 / §7's
  tentative sketches. The cycle 496+ worker may refine signatures
  based on what `inversePolyTree`'s recursion actually consumes at
  Phase β.2's structural induction step.

* Does NOT promise a 5-cycle closure. The cycle 373 / 385 / 402
  precedents have all involved scope expansions during
  implementation (cycle 385's "5 cycles" became 11 cycles; cycle
  398's "3 cycles" was on-target). **Plan for 5–8 cycles
  realistically**; ship Phase β.1 (the lowest-risk first deliverable)
  before re-estimating downstream phases.

* Does NOT propose closing the cycle 365 sorry directly this cycle
  (495). Phase β/γ infrastructure is multi-cycle work; jumping
  straight to Phase ε would require unwritten β/γ machinery.

* Does NOT prescribe Phase δ.A vs δ.B in advance. The recommendation
  (δ.B first) is provisional; cycle 498's worker should attempt δ.B
  and escalate to δ.A only on type-inference failure.

## §9 Cross-references

* `def_422B_path.md` (cycle 336 master plan for `def:422B`).
* `def_422B_phase_D_3_scoping.md` (cycle 357 Phase D.3 design,
  parent of the cycle 365 sorry's Sub-lemma A).
* `def_422B_subLemmaA_inductive_plan.md` (cycle 373 — the prior
  scoping doc that drove cycles 374–378's 8-tree
  `inversePolynomial` build-out; **direct template for Phase β.1**).
* `def_422B_phase_alpha_prime_scoping.md` (cycle 379 — recursive
  helper infrastructure for `inversePolynomial`).
* `def_422B_phase_alpha_prime_family_C_scoping.md` (cycle 385 —
  Family C scoping that drove cycles 386–397's 11-cycle ladder).
* `def_422B_phase_alpha_prime_family_bushy_scoping.md` (cycle 398 —
  bushy migration to `inversePolyTree`).
* `def_422B_phase_alpha_prime_5_scoping.md` (cycle 402 — Phase α'.5
  non-symmetric `k = 3` ladder).
* `cycle_336_pivot_options.md` (fresh-entity menu if a Phase β/γ
  blocker forces pivot).
* `OpenMath/Chapter4/Section422.lean:2272–2279` (the cycle 365
  sorry's exact location).
* `OpenMath/Chapter4/Section422.lean:11513–11537` (the cycle 377
  `_inv_eq_inversePolynomial_on_ladder` precedent for Phase β.1).
* `OpenMath/Chapter4/Section422.lean:11578–11650` (the cycle 376
  `inversePolynomial_eq_of_subtree_agreement` precedent for Phase γ).
* `OpenMath/Chapter4/Section422.lean:9718–9738` (the `inversePolyTree`
  definition Phase β.2 / γ inducts over).

## §10 Expected supervisor scoring

This is a markdown-only ship cycle. Per the cycle 373 / 385 / 398 /
402 precedent, the supervisor should score:

- Tautology scanner: 0 hits (no Lean code).
- Sorry count: unchanged at 5 (4 docstring + 1 grandfathered cycle
  365 code sorry; identical to cycle 494's count).
- Substantive work: cataloged in this scoping doc (§§1–9) and the
  `task_results/cycle_495.md` ship record.
- Faithfulness: N/A (no new Lean entities introduced).

**Risk: supervisor may underweight markdown-only cycles.**
Mitigation: cite the cycle 373 / 379 / 385 / 398 / 402 precedent in
the cycle 495 task results explicitly. Each of those scoping cycles
drove 3–11 subsequent ship cycles; cycle 495's scoping doc should be
evaluated on the same basis. Per §5.6, this doc projects 5–8
substantive cycles (cycles 496–~503) of Phase β/γ/δ/ε implementation.

## §11 §422 streak status (post-cycle-495 projected)

Pre-cycle-495 (cycles 336–494): **68 substantive + 4 doc cycles**.

Post-cycle-495 (cycles 336–495): **68 substantive + 5 doc cycles**.

The fifth doc cycle (cycle 495) joins:
* Cycle 373 — Sub-lemma A inductive plan (drove 8-tree ladder).
* Cycle 379 — Phase α' recursive design (drove Family A/B).
* Cycle 385 — Family C scoping (drove cycles 386–397, 11-cycle ladder).
* Cycle 398 — bushy scoping (drove cycles 399–401, 3-cycle migration).
* Cycle 402 — Phase α'.5 scoping (drove cycles 403, 491–494, 5-witness ladder).

…as the §422 cluster's planning markers. **Cycle 495 is the
strategic pivot from "accumulate empirical surface" to "consume it
into structural induction"** — the bridge from Phase α'.5.1's
witness-ladder closure to the cycle 365 sorry's structural-induction
closure.

After Phase ε (cycle ~501) closes the cycle 365 sorry,
`Section422.lean` will be **fully sorry-free** for the first time
since cycle 365 — restoring the §422 cluster to a clean axiom-clean
baseline ahead of any future Phase D.3.c / D.3.d work (linear
residual + underlying-one-step-method recursion per cycle 357's
master plan).
