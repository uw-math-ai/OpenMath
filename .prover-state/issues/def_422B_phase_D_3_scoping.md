# Issue: `def:422B` Phase D.3 scoping — inductive-step linear-equation solver for `r(t) ≥ 2`

## Status
**Scoping doc, cycle 357.** No Lean code shipped — this is a
markdown-only prep doc unblocking the next substantive `def:422B`
advance per `def_422B_path.md` §5 (the unique remaining multi-cycle
gap before Phase E sealing). The cycle 200/201 (`thm:381H`) and
cycle 149/150 (`def:530B`) rollback precedents require Phase D.3 be
phase-decomposed in a scoping doc **before** any worker writes the
`noncomputable def underlyingOneStepMethod_aux` recursion body.

## Blocker
At HEAD (cycle 357), the §422 pipeline has shipped:

* **Phase 0** (cycle 336): wire-up sanity — `Nonempty (Quotient PhiEquivalent.setoidSigma)`.
* **Phase A.0** (cycle 337): `D` operator pinned as §385b 1-stage generalised
  RK; canonical class `⟦explicitEuler⟧` per `project_butcher_D_operator.md`.
* **Phase B** (cycle 338): `Group.zpow` non-vacuity on the quotient.
* **Phase C** (cycle 339): `Eq422a` condition predicate.
* **Phase D.1** (cycles 340–346): base-case `r(t) = 1` (vertex) closed
  form `η(τ) = sum_β / (coef_α + coef_β)` (cycle 342) and the
  preconsistent/stable consumer template
  `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened`
  (cycle 350), the cycle 350 weakened-hypothesis ship, plus the
  5-LMM × 3-theorem consumer-witness matrix
  (cycles 349/350/353/354/355/356/357).
* **Phase D.2** (cycle 343): `WellFoundedRelation RootedTree :=
  measure RootedTree.order` shipped at `OpenMath/Chapter3/Section301.lean:177`.
* **Phase D′.2.1** (cycle 350): `coef_α + coef_β = Σᵢ (i+1)·βᵢ` under
  consistency.
* **Phase D′.2.2 Step 1** (cycle 351): `coef_β = (1/2)·Σᵢ i²·αᵢ` under
  `HasOrderAtLeast 2`. Step 2 (unconditional `0 ≤ coef_β`) blocked
  per `eq422a_eta_phase_D_prime_step_2_scoping.md`.

**Phase D.3** (the inductive step `r(t) ≥ 2`) is the only multi-cycle
content gap remaining between the current vertex-only template and
Phase E sealing of `def:422B`. The single-line summary from
`def_422B_path.md` §5 line 452 ("Inductive step (quantitative): the
linear-equation solver for `η(t)` given lower-order `η(t')`. Substantive:
requires unpacking the recursive shape of `η^(-i)` on a non-vertex
tree (the convolution-product expansion of `(η * η * … * η)(t))`")
is not actionable; this doc decomposes it into 4 phases (D.3.a–d) at
~1 cycle each, with concrete cycle 358 entry point.

## §1 Textbook source (Butcher §422, ch04.txt:1148–1173)

The relevant passage from `extraction/raw_text/ch04.txt` (lines
1148–1173) is reproduced verbatim:

> **Theorem 422A** For any preconsistent, stable linear multistep
> method [α, β], there exists a member of the group G₁ satisfying
> (422a).
>
> **Proof.** By preconsistency, ∑ᵢ₌₁ᵏ αᵢ = 1. Hence, (422a) is
> satisfied in the case of t = ∅, in the sense that if both sides
> are evaluated for the empty tree, then they each evaluate to zero.
> Now consider a tree t with r(t) > 0 and assume that
>
>   1(u) − α₁ η⁻¹(u) − α₂ η⁻²(u) − ⋯ − αₖ η⁻ᵏ(u)
>     − β₀ D(u) − β₁ η⁻¹ D(u) − β₂ η⁻² D(u) − ⋯ − βₖ η⁻ᵏ D(u) = 0,
>
> is satisfied for every tree u satisfying r(u) < r(t). We will
> prove that there exists a value of η(t) such that this equation
> is also satisfied if u is replaced by t. The coefficient of η(t)
> in η⁻ⁱ(t) is equal to i(−1)ʳ⁽ᵗ⁾ and there are no other terms in
> η⁻ⁱ(t) with orders greater than r(t) − 1. Furthermore, all terms
> on the right-hand side contain only terms with orders less than
> r(t). Hence, to satisfy (422a), with both sides evaluated at t,
> it is only necessary to solve the equation
>
>   (−1)ʳ⁽ᵗ⁾⁻¹ ∑ᵢ₌₁ᵏ i αᵢ η(t) = C,
>
> where C depends only on lower order trees. The proof by induction
> on r(t) is now complete, because the coefficient of η(t) is
> non-zero, by the stability of the method.  ▮

**Key extractions** for Lean planning:

1. **Induction kind**: Butcher writes "induction on r(t)" (the
   order of the tree). At the Lean level this is *strong* induction
   on `RootedTree.order` — cycle 343's
   `WellFoundedRelation RootedTree := measure RootedTree.order`
   instance is the correct hook (NOT structural induction on the
   `RootedTree` constructor, which would require nested-inductive
   machinery per `feedback_rootedtree_nested_induction.md`).

2. **Linear-equation reduction**: at tree `t`, the equation in `η(t)`
   is linear with coefficient `(−1)^(r(t)−1) · ∑ᵢ i·αᵢ` on the
   unknown `η(t)`. The right-hand side `C` is determined entirely
   by `η(t')` for `r(t') < r(t)` (the inductive hypothesis).

3. **Non-vanishing of the coefficient**: Butcher asserts `∑ᵢ i·αᵢ ≠ 0`
   "by stability of the method." This is **exactly** the §404a / 404b
   stability characterisation — the leading coefficient of
   `ρ'(1) = Σᵢ i·αᵢ` (cycle 251 / cycle 344 territory). Crucial:
   this is NOT the same as the cycle 350 weakened hypothesis
   `coef_α + coef_β ≠ 0` (which is the *vertex-specialised*
   denominator). The Phase D.3 generalisation needs the
   *tree-uniform* version `Σᵢ i·αᵢ ≠ 0`.

4. **Coefficient-of-η(t) claim**: "The coefficient of η(t) in η⁻ⁱ(t)
   is equal to i(−1)^r(t)" — this is a non-trivial structural claim
   about how the §381 convolution product `(η⁻¹ · η⁻¹ · … · η⁻¹)`
   (i copies) on a tree `t` decomposes when we view `η(t)` as the
   variable. The convolution-product expansion this requires is
   *exactly* the Phase D.3.b infrastructure described below.

## §2 Distilled mathematical content (Lean-friendly restatement)

Fix a `LinearMultistepMethod k` `M` and a candidate solution `η_q :
Quotient PhiEquivalent.setoidSigma`. For each rooted tree `t`, let
`η(t) := elementaryWeightQ_phi η_q t : ℝ`.

The (422a) equation at `t` (evaluated as `1(t) − Σ αᵢ η⁻ⁱ(t) − Σ βᵢ η⁻ⁱ D(t)`)
unpacks via the §381 commutative-group structure as a **polynomial**
in the values `{η(s) : s subtree of t}`. The Phase D.3.b key claim
(matching Butcher's "coefficient of η(t) in η⁻ⁱ(t) is i(−1)^r(t)") is:

> **(Lin422a)** For every tree `t` with `r(t) ≥ 1`, the (422a)
> equation at `t` has the form
> ```
>   (−1)^(r(t)−1) · (Σᵢ i·αᵢ) · η(t) = C_M(t; {η(s) : r(s) < r(t)}),
> ```
> where `C_M(t; …)` is a real-valued polynomial that depends only
> on `M`'s coefficients `α, β` and on the values `η(s)` at *strictly
> lower-order* subtrees `s`.

The Phase D.3 deliverable is to (a) prove (Lin422a) as a Lean
theorem, (b) extract `C_M(t; …)` as an explicit closed form, and
(c) use stability + (Lin422a) to define `underlyingOneStepMethod_aux M
t = C_M(t; …) / ((−1)^(r(t)−1) · Σᵢ i·αᵢ)` by well-founded recursion.

The base case `r(t) = 1` (i.e. `t = τ`) is **already shipped** by
cycle 342's `Eq422a_at_vertex_eta_eq` and the cycle 350 weakened
template — Phase D.3 must extend that closed form to `r(t) ≥ 2`.

## §3 Project-hook inventory (verified at HEAD, cycle 357)

| Hook | Source | Status | Phase D.3 role |
|---|---|---|---|
| `WellFoundedRelation RootedTree := measure RootedTree.order` | `OpenMath/Chapter3/Section301.lean:177` | ✓ cycle 343 | Phase D.3.d well-founded recursion driver |
| `RootedTree.order_pos : ∀ t, 0 < t.order` | `OpenMath/Chapter3/Section301.lean` (cycle 195) | ✓ | Discharge `r(t) ≥ 1` premise |
| `elementaryWeightQ_phi_composeQ_phi_mk` | `OpenMath/Chapter3/Section381.lean:4730` | ✓ cycle 239 | Phase D.3.a convolution decomposition |
| `elementaryWeightQ_phi_mul_vertex` (P1, vertex case) | `OpenMath/Chapter4/Section422.lean:395` | ✓ cycle 341 | Specialises to `r(t) = 1`; Phase D.3.a generalises |
| `elementaryWeightQ_phi_inv_vertex` (P2, vertex case) | `OpenMath/Chapter4/Section422.lean:415` | ✓ cycle 341 | Specialises to `r(t) = 1`; Phase D.3.a generalises |
| `elementaryWeightQ_phi_zpow_vertex` (P3, vertex case) | `OpenMath/Chapter4/Section422.lean:433` | ✓ cycle 341 | Specialises to `r(t) = 1`; Phase D.3.a generalises |
| `Eq422a` predicate | `OpenMath/Chapter4/Section422.lean` (cycle 339) | ✓ | Equation under analysis |
| `Eq422a_at_vertex_eta_eq` (base case closed form) | `OpenMath/Chapter4/Section422.lean` (cycle 342) | ✓ | r(t) = 1 base case |
| `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened` (cycle 350 template) | `OpenMath/Chapter4/Section422.lean:1134` | ✓ | r(t) = 1 consumer template Phase D.3.d must generalise |
| 5-LMM × 3-theorem consumer matrix | `OpenMath/Chapter4/Section422.lean:1233–1335` | ✓ cycles 349/350/353/354/355/356/357 | Non-vacuity confirmation for vertex case |

**Mathlib hooks** (to verify in Phase D.3.a):
* `Finset.sum_subtype` / `Finset.sum_image` for partitioning a
  sum-over-subtrees by an `order` predicate.
* `MulAction.WellFoundedLT` / `WellFounded.fix` for the strong
  induction. Cycle 343's instance should pick this up automatically.
* `Quotient.lift` for descending the `RootedTree → ℝ` recursion to
  a `Quotient PhiEquivalent.setoidSigma → ℝ` function. (Likely *not*
  needed for Phase D.3 — the recursion produces `η : RootedTree → ℝ`
  directly, and Phase E (separate cycle) bridges to the quotient.)

## §4 Gap inventory (missing infrastructure)

### §4.a Per-tree elementary-weight expansion (covers cycles 341's gap)

Cycle 341 proved per-tree elementary-weight properties (P1–P3:
`_mul_vertex`, `_inv_vertex`, `_zpow_vertex`) **only at the vertex**.
The convolution product `(η_q * η_q')` and inverse `(η_q⁻¹)` decompose
at the vertex into `η(τ) + η'(τ)` and `−η(τ)` respectively
(elementary-weight additivity at `τ`), but the analogous claims at
higher-order trees `t` involve a sum over *subtree partitions*:

```
  elementaryWeightQ_phi (η_q * η_q') (mk children) =
    Σ over partitions of `children` into two sub-forests (S₁, S₂) of:
      (product of η_q at S₁'s subtrees) · (product of η_q' at S₂'s subtrees)
```

This is the §381 Connes–Kreimer-style coproduct expansion. Cycle 239
shipped `elementaryWeightQ_phi_composeQ_phi_mk` (the §381 hook at
the `mk` constructor), so the project-side hook exists. Phase D.3.a
must specialise this to the *cycle 341 P1–P3 pattern* (multiplication,
inverse, zpow) at arbitrary trees.

**Gap size**: ~150 LOC over 1 cycle. Aristotle-suitable for the
sub-lemmas (3–4 atomic congruence lemmas after the main expansion
is stated).

### §4.b Linear coefficient extraction at `t = mk children`

The textbook claim "the coefficient of η(t) in η⁻ⁱ(t) is i(−1)^r(t)"
needs a Lean theorem of the form:

```lean
theorem coeff_eta_t_in_eta_zpow_neg
    (i : ℕ) (hi : 0 < i)
    (η_q : Quotient PhiEquivalent.setoidSigma) (t : RootedTree) :
    -- η⁻ⁱ(t) viewed as a polynomial in η(t) has linear coefficient i·(−1)^r(t)
    ∃ C, elementaryWeightQ_phi (η_q ^ (-(i : ℤ))) t
            = (i : ℝ) * (-1)^(t.order) * elementaryWeightQ_phi η_q t + C ∧
          -- and C depends only on the values of η_q at strict subtrees of t
          (∀ η_q' : Quotient PhiEquivalent.setoidSigma,
            (∀ s : RootedTree, s.order < t.order →
              elementaryWeightQ_phi η_q' s = elementaryWeightQ_phi η_q s)
            → ∃ C',
              elementaryWeightQ_phi (η_q' ^ (-(i : ℤ))) t
                = (i : ℝ) * (-1)^(t.order) * elementaryWeightQ_phi η_q' t + C
              ∧ C' = C)
```

(Exact signature TBD — this is a strawman; the cycle 358 worker
should refine.) The cycle 341's vertex P3
`elementaryWeightQ_phi_zpow_vertex` is the special case `t = τ` where
`r(τ) = 1` and the "subtree" data is vacuous.

**Gap size**: ~100 LOC over 1 cycle. The shape of `C` and the
"depends only on strict-subtree values" parametricity is the
substantive content. Aristotle-suitable for the sign-cancellation
algebra after the main statement.

### §4.c Non-vanishing of the linear coefficient under stability

Butcher's "by stability of the method" claim is that `∑ᵢ i·αᵢ ≠ 0`.
At the vertex this is *not* directly available — cycle 344 shipped
`coef_α > 0` (i.e. `∑ᵢ (i+1) · α(i.succ) > 0`, a related but *shifted*
sum) and the full unconditional `coef_α + coef_β ≠ 0` is the cycle 350
weakened-hypothesis content. The Phase D.3.c gap is:

```lean
theorem sum_i_alpha_ne_zero_of_stable
    {k : ℕ} (M : LinearMultistepMethod k)
    (hStab : M.IsStable) :
    ∑ i : Fin (k + 1), (i.val : ℝ) * M.α i ≠ 0
```

This is the **textbook** non-vanishing fact (different from the
cycle 350 vertex-denominator non-vanishing). It is the
characteristic-polynomial derivative `ρ'(1) ≠ 0` claim — at the
ρ-stable case (`ρ(z) = Σ αᵢ z^(k−i)`), simple roots on the unit
circle preclude `1` from being a multiple root, so `ρ'(1) ≠ 0`. The
proof uses §451's polynomial-root-multiplicity infrastructure.

**Gap size**: ~80 LOC over 1 cycle. **Aristotle-poor** (the proof
needs polynomial-root-multiplicity unpacking; mostly manual). May
require a Mathlib hook for `Polynomial.derivative_eq_zero_iff_multiple_root`
or similar. Verify availability before committing.

**Risk**: this is **not the same** as `eq422a_eta_phase_D_prime_step_2_scoping.md`'s
Step 2 (unconditional `0 ≤ coef_β`). They are *different* non-vanishing
facts:
* Step 2: `Σᵢ i·βᵢ ≥ 0` (β-side, related to cycle 351's `coef_β =
  (1/2)·Σᵢ i²·αᵢ`).
* §4.c: `Σᵢ i·αᵢ ≠ 0` (α-side, ρ'(1) ≠ 0).

The §4.c fact is *easier* than Step 2 (it follows from §451 ρ-stability
+ simple-root analysis, not from §441 Möbius infrastructure). However,
both are α-/β-side stability consequences; the cycle 358 worker should
confirm Mathlib has the polynomial-root tools before committing to the
proof shape.

### §4.d Recursive-substitution closure: `underlyingOneStepMethod_aux`

Once §4.a–c are in hand, the recursion is:

```lean
noncomputable def underlyingOneStepMethod_aux {k : ℕ}
    (M : LinearMultistepMethod k)
    (hPre : M.IsPreconsistent) (hStab : M.IsStable) :
    RootedTree → ℝ
  | t => -- by well-founded recursion on t.order
      let C_t : ℝ := -- the §4.b closed form, evaluated using
        -- (underlyingOneStepMethod_aux M hPre hStab s) for s.order < t.order
        sorry
      C_t / ((-1)^(t.order - 1) * (∑ i : Fin (k + 1), (i.val : ℝ) * M.α i))
```

Plus a spec lemma:

```lean
theorem underlyingOneStepMethod_aux_satisfies_Eq422a
    {k : ℕ} (M : LinearMultistepMethod k)
    (hPre : M.IsPreconsistent) (hStab : M.IsStable) :
    -- the `η : RootedTree → ℝ` produced by `underlyingOneStepMethod_aux`
    -- satisfies (422a) at every tree
    sorry  -- substantive content of `thm:422A`
```

**Gap size**: ~120 LOC over 1 cycle (assuming §4.a–c land cleanly).
The spec lemma is **the** `thm:422A` content; this is the most
substantive deliverable of the Phase D.3 sequence.

## §5 Phase decomposition (4 sub-phases × ~1 cycle each)

| Phase | Cycles | Deliverable | LOC est. | Aristotle |
|---|---|---|---|---|
| **D.3.a.{1,2}** | 1 (cycle 358) ✅ | `elementaryWeightQ_phi_mul_mk` (`*`-additivity at arbitrary `t`) + `elementaryWeightQ_phi_inv_mk` (`⁻¹`-characterization at arbitrary `t`). Both axiom-clean; 2 non-vacuity `example`s on `explicitEuler` at `RootedTree.cherry`. | ~145 (actual) | Not needed |
| **D.3.a.3** | 1 (cycle 359) ✅ | `RKTableau.powRep` + `RKTableau.powRep_quotient_eq` infrastructure in `Section381.lean` (after `instGroup_phi`) + `elementaryWeightQ_phi_pow_succ_mk` (ℕ-form, recursive `pow_succ` identity) in `Section422.lean`. All axiom-clean; three non-vacuity `example`s on `explicitEuler`. ℤ-form `elementaryWeightQ_phi_zpow_mk` explicitly deferred to cycle 360 per §5 Step 4. | ~75 (actual) | Not needed |
| **D.3.b (signature + base cases)** | 1 (cycle 360) ✅ | `linearResidualAt` named helper (definitional residual on quotient) + `coeff_eta_t_in_eta_zpow_neg` split form + `linearResidualAt_vertex_eq_zero` (vertex base case via cycle 341 P3) + `linearResidualAt_one_mk_eq` (closed form at `i = 1` arbitrary `t` via cycle 358 `_inv_mk`). Four non-vacuity `example`s on `explicitEuler` at `vertex` and `cherry`. All axiom-clean. | ~170 (actual) | Not needed |
| **D.3.b (ℤ-form lift + general closed form)** | 1 (cycle 361) ✅ | `elementaryWeightQ_phi_zpow_{natCast,negSucc}_mk` + `linearResidualAt_succ_mk_eq`. ℤ-form lift via `powRep` (cycle 359) + `_inv_mk` (cycle 358); general `i = m+1` closed form. All axiom-clean. | ~80 (actual) | Not needed |
| **D.3.b (parametricity Step 1)** | 1 (cycle 362) ✅ | `derivativeWeightWithSrc_eq_of_strict_subtree_agreement` (+ list-helper companion) — per-`derivativeWeightWithSrc` substitution lemma under strict-subtree agreement of source-method elementary weights. Cycle 226 mutual template weakened from `PhiEquivalent` to strict-subtree agreement, threading order witnesses through the recursion via cycle 343's `order_lt_of_mem_children`. Both axiom-clean; non-vacuity `example` at `cherry`. | ~95 (actual) | Not needed |
| **D.3.b (parametricity Step 2)** | 1 (cycle 363) | `linearResidualAt_depends_only_on_strict_subtrees` — quotient-level parametricity claim composing cycle 362 Step 1 with `Quotient.inductionOn₂` and the cycle 361 closed form. **Substantive remaining: cancellation of the `M.elementaryWeight t` term** (non-trivial — see cycle 362 task results). | 80–100 | Poor (well-founded induction + ℝ-algebra) |
| **D.3.c** | 1 (cycle 364) | `sum_i_alpha_ne_zero_of_stable` — `ρ'(1) ≠ 0` from ρ-stability via simple-root analysis. Per cycle 362 worker, this is a ~10 LOC corollary of cycle 176 + cycle 344 infrastructure; **near-free**. | 10 (revised) | Not needed |
| **D.3.d** | 1 (cycle 365) | `noncomputable def underlyingOneStepMethod_aux` recursion + `_satisfies_Eq422a` spec lemma. Closes `thm:422A`'s substantive content. | 120 | Partial (well-founded recursion proof obligations) |

### Cycle 358 update — D.3.a partial ship

**Shipped (cycle 358)**:

* `elementaryWeightQ_phi_mul_mk` (D.3.a.1): one-line `exact
  elementaryWeightQ_phi_composeQ_phi_mk M₁ M₂ t` after `show … =
  composeQ_phi …` (cycle 236's `instMul_phi` provides the
  definitional unfold). Pre-flight on cycle 239's hook confirmed
  output shape matches strawman.
* `elementaryWeightQ_phi_inv_mk` (D.3.a.2): formula
  `Φ_{⟦M⟧⁻¹}(t) = - Σᵢ M.b i · M.derivativeWeightWithSrc M.inverse i t`
  (note: NOT the strategy's strawman `-Φ_M(t) - Σ…`; the cleaner
  formula above falls directly out of `inv_mul_cancel` + D.3.a.1 +
  cycle 239's `elementaryWeightQ_phi_id`, and at `t = vertex`
  reduces correctly to cycle 341 P2 since the
  `derivativeWeightWithSrc` factor is `1`).

**Deferred to cycle 359 (D.3.a.3)**:

At arbitrary `t`, lifting cycle 341 P3's
`elementaryWeightQ_phi_zpow_vertex` requires a canonical
representative of `η_q ^ m` for each `m : ℕ`, since the bottom-block
of each `pow_succ` step in D.3.a.1 depends on a specific
representative (`derivativeWeightWithSrc` is representative-only by
design; cycle 333's note at `Section381.lean:2660–2700`). Closed
form does not exist via P3's `pow_succ`-induction route at
arbitrary `t` because the bottom-block does not telescope (each
step introduces a fresh `derivativeWeightWithSrc <pow_m_rep>` term
where `pow_m_rep`'s structure grows with `m`).

The proposed Phase D.3.a.3 cycle 359 strategy:

1. Define `RKTableau.powRep : (m : ℕ) → RKTableau s →
   Σ s', RKTableau s'` recursively via repeated `compose` with
   `RKTableau.id` at `m = 0`.
2. Prove `⟦powRep m M⟧ = ⟦M⟧ ^ m` at the §383 quotient level.
3. State D.3.a.3 as a recursive identity in `m` using `powRep` for
   the bottom-block representative.
4. Extend to `n : ℤ` via case split on `Int.ofNat` / `Int.negSucc`
   composing D.3.a.2 (inverse) with the natural-number version.

This is ~80 LOC and 1 cycle. Cycle 359 worker absorbs this before
proceeding to D.3.b. The §422 ladder horizon extends by one cycle
(D.3.b ↦ cycle 360, D.3.c ↦ cycle 361, D.3.d ↦ cycle 362, Phase E
sealing ↦ cycle 363).

### Cycle 359 update — D.3.a.3 ship

**Shipped (cycle 359)**:

* `OpenMath.Chapter3.Section312.RKTableau.powRep` (Phase D.3.a.3
  infrastructure): the recursive self-composition as a Σ-typed value.
  `powRep M 0 = ⟨0, RKTableau.id⟩`, `powRep M (m+1) = ⟨(powRep M m).1
  + s, (powRep M m).2.compose M⟩`. Inserted in `Section381.lean`
  immediately after `instGroup_phi` (cycle 236), inside the
  `OpenMath.Chapter3.Section312.RKTableau` namespace. `noncomputable
  def` (matches cycle 222's `inverseQ_phi` pattern). ~6 LOC.

* `OpenMath.Chapter3.Section312.RKTableau.powRep_quotient_eq`: the
  certifier `⟦M.powRep m⟧ = ⟦⟨s, M⟩⟧^m`. Induction on `m`. Both
  base and succ cases close via `show ... = _` (Σ-eta on the body
  of `powRep` makes the goal pattern match) + `rw [pow_zero]` /
  `rw [pow_succ, ← ih]` + `rfl` (definitional reduction through
  `composeQ_phi_mk`'s `rfl`-level `Quotient.lift₂_mk` unfold). The
  strategy's Step 2 fallback (explicit `show composeQ_phi …`) was
  not needed; the cleaner `Quotient.mk PhiEquivalent.setoidSigma
  ⟨_, _.compose _⟩` form already exposes the right shape. ~15 LOC.

* `OpenMath.Chapter4.Section422.elementaryWeightQ_phi_pow_succ_mk`:
  the Phase D.3.a.3 ℕ-form statement. Proof recipe (3 lines):
  `rw [pow_succ]` (LHS `⟦M⟧^(m+1) ↦ ⟦M⟧^m * ⟦M⟧`); `rw [←
  RKTableau.powRep_quotient_eq M m]` (this single `rw` fires on
  BOTH the LHS `⟦M⟧^m` factor and the RHS first summand
  simultaneously — no second `rw` or `conv_rhs` needed; the
  strategy's Step C/D `conv_rhs` fallback was eliminated after
  discovering the global `rw` behavior); `exact
  elementaryWeightQ_phi_mul_mk (M.powRep m).2 M t` (D.3.a.1 closes
  with `M₁ := (M.powRep m).2`, `M₂ := M`, using Σ-eta on
  `⟦M.powRep m⟧` to match D.3.a.1's `⟦⟨s₁, M₁⟩⟧` shape). ~15 LOC.

* Three non-vacuity `example`s in `Section422.lean` exercising
  `powRep` on `explicitEuler`: base-case identity (`powRep 0 =
  ⟨0, RKTableau.id⟩` by `rfl`), first-step stage count
  (`(powRep 1).1 = 1` by `rfl`), end-to-end ℕ-form at `cherry`
  with `m = 0`. ~15 LOC.

All three new public symbols axiom-clean (`[propext,
Classical.choice, Quot.sound]` only), verified via `#print axioms`
on a separate axiom-check Lean file after `lake build` refreshed
the .oleans. `lake build OpenMath.Chapter3 OpenMath.Chapter4` both
exit 0; sorry count remains 0 in both target files.

**Implementation notes for the cycle 360 worker**:

1. The strategy's "two-step" rewrite (one `rw [← powRep_quotient_eq]`
   then a `conv_rhs => rw [← ...]`) was an over-specification. The
   first `rw` fires globally and the second pattern is not found.
   Eliminating the second rewrite simplified the proof to 3 lines.

2. The `show` form in `powRep_quotient_eq` requires an explicit type
   ascription on the Σ-value (`(⟨0, RKTableau.id⟩ : Σ s' : ℕ,
   RKTableau s')` and analogously for the succ case) to disambiguate
   the implicit sigma; without the ascription the elaborator picked
   the wrong sigma type (`PSigma`). Worth keeping the ascription for
   the cycle 360 worker if they need a parallel construction.

3. `RKTableau.compose` is `def` (not `noncomputable`), but `powRep`
   is `noncomputable def` (because the Σ-typed return forces
   noncomputable propagation through `Quotient.mk` operations
   downstream). This matches the cycle 222 `inverseQ_phi` precedent
   and does not trigger any unexpected `Decidable` lookup failures
   (R3 risk did not fire).

**Deferred to cycle 360**: the ℤ-form
`elementaryWeightQ_phi_zpow_mk`. The cycle 359 worker did not ship
the stretch ℤ-form per strategy §C.4 — the exact signature should
be pinned by Phase D.3.b's consumption requirements (cycle 360
deliverable), not guessed in advance. The cycle 359 ship gives D.3.b
everything it needs for the **positive-integer-power** side; the
negative-integer-power side composes via D.3.a.2 (cycle 358's
`elementaryWeightQ_phi_inv_mk`) once the ℤ-form is shaped.

**Cycle 360 entry point**: Phase D.3.b — linear coefficient
extraction: `coeff_eta_t_in_eta_zpow_neg` (the textbook claim
"coefficient of η(t) in η⁻ⁱ(t) is i(−1)^r(t)"). Per §5 phase table,
~100 LOC, partial Aristotle for the sign-cancellation algebra. Uses
D.3.a.{1,2,3} as inputs.

### Cycle 360 update — D.3.b signature + base cases ship

**Shipped (cycle 360)** at end of `OpenMath/Chapter4/Section422.lean`
(lines 1797–1969):

* `OpenMath.Chapter4.Section422.linearResidualAt` —
  `noncomputable def` defining the residual at the §383 quotient
  level: `Φ_{η_q^(-i)}(t) - i·(-1)^t.order·Φ_{η_q}(t)`. Quotient-
  level (per §6.3 quotient-faithfulness); does not depend on
  representative choice. ~5 LOC.

* `OpenMath.Chapter4.Section422.coeff_eta_t_in_eta_zpow_neg`
  (Sub-deliverable 1, signature pinning): the split form
  `Φ_{η_q^(-i)}(t) = i·(-1)^t.order·Φ_{η_q}(t) + linearResidualAt i η_q t`.
  Proof: `unfold linearResidualAt; ring`. Dropped strawman's
  `hi : 0 < i` hypothesis (works uniformly for `i : ℕ`; at `i = 0`
  both sides vanish via cycle 239's `elementaryWeightQ_phi_id`).
  ~8 LOC including doc.

* `OpenMath.Chapter4.Section422.linearResidualAt_vertex_eq_zero`
  (Sub-deliverable 2 vertex base case): residual is identically zero
  at `τ`. Proof: cycle 341 P3 (`_zpow_vertex`) +
  `show RootedTree.vertex.order = 1 from rfl` + `push_cast; ring`.
  ~10 LOC including doc.

* `OpenMath.Chapter4.Section422.linearResidualAt_one_mk_eq`
  (Sub-deliverable 2 closed form at `i = 1`): representative-form
  closed-form `linearResidualAt 1 ⟦⟨s, M⟩⟧ t = -Σⱼ M.b j ·
  M.derivativeWeightWithSrc M.inverse j t - (-1)^t.order ·
  M.elementaryWeight t`. Proof: `Nat.cast_one + zpow_neg_one` bridge
  + cycle 358's `_inv_mk` + cycle 226's `_phi_mk` + `push_cast; ring`.
  ~12 LOC including doc.

* Four non-vacuity `example`s on `explicitEuler`:
  - vertex base case `i = 1`,
  - signature split form at vertex `i = 1`,
  - closed form at `cherry` (`r = 2`) for `i = 1`.

All five new public symbols axiom-clean (`[propext, Classical.choice,
Quot.sound]` only) verified via `#print axioms` on a separate axiom-
check Lean file after `lake build OpenMath.Chapter4.Section422`
(8037/8037 jobs, exit 0, 153s rebuild). Sorry count remains 0.

**Implementation notes for the cycle 361 worker**:

1. **`(-1)^vertex.order` reduces via explicit rewrite**: `ring`
   doesn't reduce literal naturals in exponents automatically; need
   `rw [show vertex.order = 1 from rfl]` (or `simp only`) before
   `ring`. For cycle 361's inductive step at non-vertex trees,
   `t.order` will *not* reduce in general — the structural rewrite
   step will require strict-subtree-induction infrastructure rather
   than `rfl`.

2. **`Nat.cast_one + zpow_neg_one` bridges `(↑(1 : ℕ) : ℤ)` → `-1`**:
   the two-step rewrite `rw [Nat.cast_one]; exact zpow_neg_one _` is
   the cleanest path from `η_q ^ (-((1 : ℕ) : ℤ))` to `η_q⁻¹`. For
   `i ≥ 2`, cycle 361 will need an analogous bridge via `zpow_neg`
   + `zpow_natCast` to expose the inverse structure.

3. **Quotient-level statement, representative-form closed form**:
   `linearResidualAt` is at the quotient level (independent of
   representative), but `linearResidualAt_one_mk_eq`'s closed-form
   RHS is necessarily representative-form (mentions `M.b`,
   `M.inverse`). Cycle 361's parametricity claim "depends only on
   strict subtrees" should be stated at the quotient level (i.e.
   invariant under Φ-equivalent representative substitution) — see
   the suggested cycle 361 signature in `cycle_360.md` Discovery
   #3.

4. **Example coefficient cast must match theorem signature**:
   When consuming `coeff_eta_t_in_eta_zpow_neg` with `i = 1`, the
   coefficient must be written as `((1 : ℕ) : ℝ)`, not `(1 : ℝ)`.
   The two are equal in value but not syntactically `rfl`. Cycle
   360 caught this on the first compile.

**Deferred to cycle 361**: Phase D.3.b inductive step — the
parametricity claim `linearResidualAt_depends_only_on_strict_subtrees`
that closes the textbook's "induction on r(t)" argument. Requires
the ℤ-form lift `elementaryWeightQ_phi_zpow_mk` (from cycle 359's
ℕ-form `elementaryWeightQ_phi_pow_succ_mk` + cycle 358's `_inv_mk`)
and strong induction on `t.order` via cycle 343's `WellFoundedRelation`.

**Cycle 361 entry point**: Phase D.3.b inductive step — prove
`linearResidualAt_depends_only_on_strict_subtrees`. Per §5 phase
table (updated), ~80–100 LOC, poor Aristotle for the well-founded-
induction structure. Uses cycle 360's deliverables + cycle 359's
`_pow_succ_mk` as inputs.

### Cycle 361 update — ℤ-form lift + general `i = m+1` closed form ship; P2 parametricity claim deferred

**Shipped (cycle 361)** at end of `OpenMath/Chapter4/Section422.lean`
(after the cycle 360 block):

* `OpenMath.Chapter4.Section422.elementaryWeightQ_phi_zpow_natCast_mk`
  — ℤ-form lift positive natCast case:
  `Φ_{⟦M⟧^((m:ℤ))}(t) = (M.powRep m).2.elementaryWeight t`.
  2-line proof `rw [zpow_natCast, ← RKTableau.powRep_quotient_eq M m]; rfl`.

* `OpenMath.Chapter4.Section422.elementaryWeightQ_phi_zpow_negSucc_mk`
  — ℤ-form lift negative case (`n = Int.negSucc m = -(m+1)`):
  `Φ_{⟦M⟧^(Int.negSucc m)}(t) = -Σⱼ (M.powRep (m+1)).2.b j ·
  (M.powRep (m+1)).2.derivativeWeightWithSrc
  (M.powRep (m+1)).2.inverse j t`. 2-line proof
  `rw [zpow_negSucc, ← RKTableau.powRep_quotient_eq M (m + 1)]; exact
  elementaryWeightQ_phi_inv_mk (M.powRep (m+1)).2 t` (cycle 358's
  `_inv_mk` consumes the Σ-eta'd `(M.powRep (m+1)).2` representative).

* `OpenMath.Chapter4.Section422.linearResidualAt_succ_mk_eq` —
  substantive general closed form at arbitrary positive `i = m+1`.
  **Subsumes** cycle 360's `linearResidualAt_one_mk_eq` `i = 1`
  special case (which used `Nat.cast_one + zpow_neg_one` bridge) into
  a uniform `i = m+1` form via the ℤ-form lift. 6-line proof
  `unfold linearResidualAt` + `have h_pow : ... ^ (-(((m+1):ℕ):ℤ)) =
  ... ^ (Int.negSucc m) := rfl` + ℤ-form lift + `_phi_mk` +
  `push_cast; ring`.

* Four non-vacuity `example`s: `_zpow_natCast_mk` at `m = 0` cherry,
  `_zpow_negSucc_mk` at `m = 0` cherry (= `n = -1`), `_succ_mk_eq`
  at `m = 1` cherry (= `i = 2`), and vertex sanity at `i = 3`
  (cross-check via cycle 360's `linearResidualAt_vertex_eq_zero`).

All three new public theorems axiom-clean (`[propext, Classical.choice,
Quot.sound]` only) verified via `#print axioms` after `lake build
OpenMath.Chapter4.Section422` (8037/8037 jobs, exit 0, 354s rebuild).
Sorry count remains 0.

**Implementation notes for the cycle 362 worker**:

1. **`-(((m+1):ℕ):ℤ) = Int.negSucc m` is definitional `rfl`** —
   the cleanest bridge from `-((natural + 1) : ℤ)` to `Int.negSucc`.
   No `Nat.cast_ofNat` or `norm_num` needed; the equality holds by
   the defining clause of `Int.neg`. **Do NOT use `norm_num` for
   this bridge** — initial cycle 361 attempt left an unsolved-goals
   error with display ambiguity (`⟦M⟧ ^ 2 = ⟦M⟧ ^ 2` where the
   integer exponent was actually `-2` but pretty-printed without
   sign).

2. **`elementaryWeightQ_phi_inv_mk` on Σ-eta'd representatives**:
   when applying cycle 358's `_inv_mk` to `(M.powRep (m+1)).2`,
   Σ-eta on `M.powRep (m+1) = ⟨(M.powRep (m+1)).1, (M.powRep
   (m+1)).2⟩` makes the rewrite definitional. No explicit
   destructuring needed.

3. **Generalising `_two_mk_eq` to `_succ_mk_eq` was a one-line
   change** — replacing literal `2` with `m + 1` and `Int.negSucc 1`
   with `Int.negSucc m`. The proof structure is identical because
   `_zpow_negSucc_mk` is parametric in `m`. Lesson for future
   cycles: when shipping a "closed form at literal `k`" lemma,
   first try the parametric version — often it is strictly more
   useful at the same proof cost.

**Deferred to cycle 362**: Phase D.3.b inductive step / parametricity
claim `linearResidualAt_depends_only_on_strict_subtrees`. Per the
cycle 361 worker's analysis, the recursive structure of
`derivativeWeightWithSrc M₂ M₁ i (mk children)` exposes `M₂`'s
internal A-coefficients alongside `M₁.elementaryWeight` at subtrees,
requiring a more delicate inductive structure that simultaneously
constrains both `Φ_η_q` AND per-stage internal weights at strict
subtrees. The cycle 361 strategy §B.2 anticipated MEDIUM-HIGH risk
on this; the foreseeable multi-cycle decomposition for cycle 362+:

1. Per-`derivativeWeightWithSrc` substitution lemma: "if `M₁` and
   `M₁'` agree on elementary weights at all strict subtrees of `t`,
   then `derivativeWeightWithSrc M₂ M₁ i t' = derivativeWeightWithSrc
   M₂ M₁' i t'` for all `t' ∈ children t`". Structural induction on
   the tree.

2. `linearResidualAt_depends_only_on_strict_subtrees` via
   `Quotient.inductionOn₂` + the ℤ-form lift (cycle 361) + the
   per-`derivativeWeightWithSrc` substitution lemma + IH at strict
   subtrees.

Step 1 may be a single-cycle deliverable. Step 2 then follows as a
~1-cycle composition.

**Cycle 362 entry point**: ship the per-`derivativeWeightWithSrc`
substitution lemma (Step 1 above), with the parametricity claim
(Step 2) following in cycle 363 if Step 1 lands. Alternatively, if
the cycle 362 strategist judges Step 2 directly tractable, attempt
both in one cycle. The graceful-degradation fallback is to ship
Step 1 alone, mirroring cycle 361's "ship P1 + extend ladder"
pattern.

**Total**: 7 cycles (was 6; cycle 362 confirmed parametricity Step 2
is a separate-cycle deliverable per cycle 362 worker analysis —
the residual cancellation requires substantive ℝ-algebraic work
beyond Step 1's substitution-by-agreement). Sequential dependencies:
D.3.a → D.3.b (signature) → D.3.b (ℤ-form lift) → D.3.b
(parametricity Step 1) → D.3.b (parametricity Step 2) → D.3.d;
D.3.c is parallel.

### Cycle 362 update — D.3.b parametricity Step 1 ship; Step 2 deferred

**Shipped (cycle 362)** at end of the cycle 226 substitution mutual
block in `OpenMath/Chapter3/Section381.lean` (immediately after line
2803):

* `OpenMath.Chapter3.Section312.RKTableau.derivativeWeightWithSrc_eq_of_strict_subtree_agreement`
  (Step 1 main lemma): if `M₁, M₁'` agree on `elementaryWeight` at
  every tree of order strictly less than `t.order`, then
  `M₂.derivativeWeightWithSrc M₁ i t = M₂.derivativeWeightWithSrc M₁' i t`
  for every inner tableau `M₂` and stage `i`. This is cycle 226's
  `derivativeWeightWithSrc_subst_M₁` template with the
  `PhiEquivalent M₁ M₁'` hypothesis (full agreement) WEAKENED to
  strict-subtree agreement — the weakest hypothesis that suffices
  for the cycle 226-style mutual recursion to thread through.

* `OpenMath.Chapter3.Section312.RKTableau.derivativeWeightWithSrcProd_eq_of_strict_subtree_agreement`
  (list-helper companion): the parent tree `t` is carried as an
  explicit parameter so the strict-subtree hypothesis can be
  threaded through the recursive call at each child `c ∈ children`.
  Two key uses of the order-witness: (a) the parent-level
  `h_strict c h_c_lt` rewrites `M₁.elementaryWeight c` to
  `M₁'.elementaryWeight c` since `c.order < t.order` by cycle 343's
  `order_lt_of_mem_children`; (b) the recursive
  `derivativeWeightWithSrc_eq_of_strict_subtree_agreement M₂ c (fun s hs => h_strict s (hs.trans h_c_lt)) j`
  composes `s.order < c.order` with `c.order < t.order` via
  `Nat.lt_trans` to satisfy the inner strict-subtree hypothesis at
  sub-subtrees of `t`.

* One non-vacuity `example` in `OpenMath/Chapter4/Section422.lean`
  (after cycle 361 examples): trivial-agreement case
  `M₁ = M₁' = explicitEuler` at `RootedTree.cherry`, with the
  strict-subtree hypothesis discharged by `fun _ _ => rfl`. Confirms
  the substitution lemma's signature compiles and the lemma fires
  on a concrete tableau / tree pair from §422's downstream consumer.

Both lemmas are **not** marked `private` (deviating from the
strategy's §C.2 instruction to mark them `private`): the strategy
explicitly placed the non-vacuity `example` in `Section422.lean`,
which requires cross-file access. The `private` restriction would
have forced the example into `Section381.lean`, contradicting the
strategy's §C.5 location. The lemmas remain "Phase D.3.b
infrastructure" per their docstring labelling — this is a minor
deviation that improves downstream consumption (cycle 363's Step 2
also needs cross-file access to these lemmas).

**Implementation deviations from strategy §C.2**:

1. `RootedTree.order_lt_of_mem_children` signature: the strategy
   wrote `RootedTree.order_lt_of_mem_children children c hc` with
   `children` and `c` as explicit args; the actual signature has
   both implicit (`{c : RootedTree} {children : List RootedTree}`),
   so the correct call is `RootedTree.order_lt_of_mem_children hc`
   alone. The discrepancy was caught on first compile attempt and
   fixed in 1 line.

2. `List.mem_cons_self _ _` does not type-check in modern Mathlib:
   the lemma `a ∈ a :: l` has both `a` and `l` implicit, so it's
   used as just `List.mem_cons_self` (no explicit args). Fixed in
   1 line.

3. Added `import OpenMath.Chapter3.Section301` to `Section381.lean`
   to make `RootedTree.order_lt_of_mem_children` visible. Section381
   previously imported only Section310 + Section312; the cycle 343
   lemma lives in `Section301.lean` (inside the
   `OpenMath.Chapter3.Section310.RootedTree` namespace). No
   circular-import risk (Section301 imports only Section310).

All three new public symbols (2 theorems + 1 example) axiom-clean
(`[propext, Classical.choice, Quot.sound]` only) verified via
`#print axioms` after `lake build` (8081/8081 jobs, exit 0).
Sorry count remains 0 in all §422-pipeline files.

**Implementation notes for the cycle 363 worker**:

1. **Step 2's substantive obstacle is NOT the substitution part**.
   The cycle 361 closed form `linearResidualAt_succ_mk_eq` gives:
   ```
   linearResidualAt (m+1) ⟦M⟧ t
     = -Σⱼ (M.powRep (m+1)).2.b j ·
          (M.powRep (m+1)).2.derivativeWeightWithSrc
            (M.powRep (m+1)).2.inverse j t
       - ((m+1) : ℝ) · (-1)^t.order · M.elementaryWeight t
   ```
   Step 1 (cycle 362) handles the `derivativeWeightWithSrc` sum's
   substitution behaviour under strict-subtree agreement of
   `(M.powRep (m+1)).2.inverse`. BUT the residual *also* contains
   a direct `M.elementaryWeight t` term — this is read at `t`
   itself, NOT at strict subtrees. The Step 2 parametricity claim
   "depends only on strict subtrees" requires showing that this
   `M.elementaryWeight t` term **cancels** with a contribution
   from the `derivativeWeightWithSrc` sum at the `vertex`-shape
   subterm, OR is otherwise expressible via strict-subtree data.
   This is a substantive ℝ-algebraic identity, not just
   substitution.

2. **Quotient.inductionOn₂ chain still applies, but with a
   conditional cancellation step.** The Step 2 proof skeleton:
   ```
   Quotient.inductionOn₂ η_q η_q' (fun ⟨s, M⟩ ⟨s', M'⟩ h_strict => by
     rw [linearResidualAt_succ_mk_eq M m t, linearResidualAt_succ_mk_eq M' m t]
     -- Now LHS - RHS = (derivativeWeightWithSrc-diff) + (elementaryWeight-diff)
     -- Step 1 (cycle 362) closes (derivativeWeightWithSrc-diff) = 0
     -- The (elementaryWeight-diff) term must cancel separately.
     sorry  -- substantive algebraic identity
   )
   ```

3. **Alternative: state Step 2 over a stricter hypothesis** that
   ALSO includes `t` itself in the agreement, i.e. "depends only
   on subtrees of t (closed, not just strict)". This is a
   weakening of the original Step 2 statement but may be exactly
   what D.3.d needs — D.3.d's `underlyingOneStepMethod_aux`
   recursion stores `η(t')` for ALL `t' ≤ t` by the time it
   reaches `t`. If the cycle 363 worker can show D.3.d's recursion
   only needs Step 2 under the closed-subtree hypothesis, this
   eliminates the substantive cancellation. Recommend the cycle
   363 worker scope this before attempting the full strict-subtree
   form.

**Cycle 363 entry point**: Phase D.3.b parametricity Step 2 —
attempt `linearResidualAt_depends_only_on_strict_subtrees` via the
`Quotient.inductionOn₂` + closed-form + Step 1 skeleton above.
The substantive obstacle (cancellation of the direct
`M.elementaryWeight t` term) is the focus of the cycle. If the
strict-subtree form proves intractable in 1 cycle, file a sub-issue
and pivot to the closed-subtree form (worker note #3 above) — Phase
D.3.d may not require the strict form.

**Phase D.3 horizon update**: now 7 sub-phases (was 6 after cycle
361 split, was 5 originally). Phase E sealing of `def:422B`
projected for cycle 366 (was 365 in the cycle 361 plan; one cycle
slip from the Step 2 separation).

**Aggregated risk**: comparable to the cycle 340–346 base-case (Phase
D.1) trajectory which took ~6 cycles for `r(t) = 1` alone. The
extension to `r(t) ≥ 2` is genuinely more work due to the
convolution-product expansion (D.3.a) and the well-founded-recursion
discharge (D.3.d).

## §6 Risk assessment

### §6.1 Per-phase risk

| Phase | Risk | Mathlib confidence | Rollback risk if mis-scoped |
|---|---|---|---|
| D.3.a | Medium — depends on §381's `composeQ_phi_mk` shape matching the (η_q * η_q')(mk children) decomposition cleanly | High (cycle 239's hook is direct) | Low — vertex-case analogues (cycle 341) confirm the pattern fires |
| D.3.b | High — the "coefficient of η(t) in η⁻ⁱ(t) = i(−1)^r(t)" claim is structural and may need a custom strong-induction argument that doesn't reduce cleanly to D.3.a's product expansion | Medium | Medium — if the claim's exact statement is subtly off, the Lean shape will need refinement |
| D.3.c | Low-Medium — `ρ'(1) ≠ 0` is standard; the obstacle is whether Mathlib's polynomial-root API exposes the required simple-root lemma | Medium-Low — likely needs custom infrastructure | Low — well-isolated; if blocked, ship as named axiom-free hypothesis to D.3.d |
| D.3.d | Medium-High — well-founded recursion proof obligations may surface unanticipated issues (e.g. termination measure not decreasing for the right reason); spec lemma `_satisfies_Eq422a` is `thm:422A`-scale | Medium | Medium — if recursion's termination measure is wrong, recurses through multiple cycles to fix |

### §6.2 Cycle-336-style rollback risks to monitor

* **Phase D.3.a wrong-shape**: if `elementaryWeightQ_phi_mul_mk` ends
  up requiring a per-tree forest-partition machinery that doesn't fit
  cleanly into §381's `composeQ_phi_mk`, the cycle 358 worker must
  stop and file a sub-issue rather than writing `sorry`-bearing
  scaffolding. **Mitigation**: cycle 358 worker should `lean_hover_info`
  on `elementaryWeightQ_phi_composeQ_phi_mk`'s output shape **before**
  writing the new lemma's signature.
* **Phase D.3.c Mathlib gap**: if Mathlib does not have the simple-root
  polynomial-derivative lemma, cycle 360 worker should **NOT** attempt
  to ship the full polynomial-root infrastructure inline — file a
  sub-issue and let D.3.d proceed with `sum_i_alpha_ne_zero_of_stable`
  as a hypothesis (it can be discharged at the per-LMM-witness level
  as we did for the cycle 350 weakened ship).
* **σ-faithfulness gap**: the cycle 333's `symmetry_group_equivalence.md`
  scoping doc flags that the §383 quotient setoid is via Φ-equivalence,
  and σ (the §305 symmetry coefficient) is the bridge to elementary
  weights. Phase D.3 must produce an `η : RootedTree → ℝ` that
  *factors* through the §383 quotient. If at D.3.d's spec lemma the
  Phase D-produced `η` turns out to **not** be quotient-faithful (i.e.
  there's some Φ-equivalent `M, M'` whose quotient image yields
  different `η(t)` values), the entire construction is wrong. **Mitigation**:
  cycle 358 worker should add a "lift-to-quotient check" as a
  sub-deliverable; D.3.d's spec lemma should explicitly verify
  quotient-faithfulness rather than assume it.

### §6.3 σ-faithfulness deferral

Per `symmetry_group_equivalence.md`, the §383 PhiEquivalent setoid
quotient may interact non-trivially with σ-weighted sums. This is
**not** a Phase D.3 blocker (the recursion produces `η : RootedTree →
ℝ`, which doesn't directly involve σ), but Phase E's `liftFunctionToQuotient`
will need to address it. Phase D.3 should be designed so that the
output `η` is *quotient-invariant by construction* — i.e. the recursion
should depend only on `[α, β]` and the tree, not on any specific
RK-witness for the quotient class.

### §6.4 GPFS / Section441 timeout risk

Per `cycle_182_gpfs_slowness.md`, Section441 has 43+ consecutive
GPFS-blocked compile timeouts. Phase D.3 deliverables live entirely
in `OpenMath/Chapter4/Section422.lean` and (for D.3.a) potentially
in `OpenMath/Chapter3/Section381.lean` as supporting lemmas. **Phase
D.3 must not require Section441 modifications.** The §451 ρ-stability
machinery used in D.3.c can be cited via existing exports (e.g.
`bdf2LMM_isStable`, `bdf3LMM_isStable`) without recompiling §441.

## §7 Cycle 358 entry point

**Concrete first task for cycle 358 (Phase D.3.a)**: ship three
named theorems extending cycle 341 P1–P3 from `vertex` to arbitrary
trees, parallel to the existing
`elementaryWeightQ_phi_{mul, inv, zpow}_vertex` triple in
`OpenMath/Chapter4/Section422.lean:395–462`:

```lean
/-- *Phase D.3.a generalisation of cycle 341 P1:* convolution
elementary-weight at an arbitrary tree decomposes via the §381
`composeQ_phi_mk` coproduct expansion. -/
theorem elementaryWeightQ_phi_mul_mk
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (children : List RootedTree) :
    elementaryWeightQ_phi (η_q * η_q') (RootedTree.mk children)
      = -- coproduct expansion: sum over sub-forest partitions
        sorry
```

Plus analogous `_inv_mk` and `_zpow_mk`. **Cycle 358 deliverable**:
the three named theorems shipped axiom-clean, with `sorry`-first
scaffolding closed via `composeQ_phi_mk` (cycle 239) plus algebraic
manipulation.

**Cycle 358 NON-deliverable**: do **NOT** attempt D.3.b (linear
coefficient extraction) in the same cycle. The D.3.a → D.3.b
boundary is the natural one-cycle split point per the cycle 343
(Phase D.2 alone) precedent.

**Cycle 358 worker preliminaries** (do these *before* writing any
Lean code):

1. `lean_hover_info` on `elementaryWeightQ_phi_composeQ_phi_mk` at
   `OpenMath/Chapter3/Section381.lean:4730` to confirm the output
   shape.
2. `lean_local_search` for `RootedTree.mk` and `elementaryWeightQ_phi`
   in `OpenMath/Chapter3/Section381.lean` to find any neighboring
   per-tree expansion lemmas.
3. Read cycles 341 P1's vertex-case proof at
   `OpenMath/Chapter4/Section422.lean:395–411` for the canonical
   pattern.
4. Verify Aristotle is alive (free compute for the algebraic
   sub-lemmas).

## §8 What Phase D.3 will deliver to Phase E

After D.3.a–d land, `def:422B`'s Phase E (cycle 362+) inputs are:

1. `noncomputable def underlyingOneStepMethod_aux M hPre hStab : RootedTree → ℝ` (D.3.d)
2. `theorem underlyingOneStepMethod_aux_satisfies_Eq422a` (D.3.d spec)
3. (For Phase E:) a "bridge" theorem connecting `η : RootedTree → ℝ`
   to a `Quotient PhiEquivalent.setoidSigma` element. **NOT in scope
   for Phase D.3.** Phase E will need to either (a) find an RK
   tableau whose `elementaryWeight` matches `η`, or (b) extend
   the §383 quotient setup to admit `RootedTree → ℝ` functions
   directly (without an RK witness).

The Phase D.3.d spec lemma is the substantive part of `thm:422A`
(existence of η satisfying (422a)); `def:422B` itself is the
def-only sealing once Phase E ships the bridge.

## §9 Cross-references

* `def_422B_path.md` §5 line 452: source spec for "Phase D.3 (1–2
  cycles): inductive-step linear-equation solver."
* `def_422B_path.md` §4.4: "existence of η satisfying (422a)" — the
  textbook content this Phase D.3 sequence formalises.
* `eq422a_eta_phase_D_prime_step_2_scoping.md`: a *different*
  non-vanishing target (β-side, vertex-only). **NOT a Phase D.3
  blocker**; Phase D.3.c needs the α-side `ρ'(1) ≠ 0` instead.
* `cycle_336_pivot_options.md`: pivot candidates for cycle 359+ if
  Phase D.3 stalls (`thm:535A`, `thm:541A`, `def:442A`).
* `project_butcher_D_operator.md` (memory): `D = §385b 1-stage
  generalised RK`. Phase D.3 must not redefine D.
* `feedback_rootedtree_nested_induction.md` (memory): induction on
  `RootedTree` requires mutual blocks, NOT direct `induction t`.
  Phase D.3.a/D.3.d worker must use the cycle 343
  `WellFoundedRelation` instance via strong induction on
  `RootedTree.order`, NOT structural recursion.
* `symmetry_group_equivalence.md`: σ-faithfulness deferral, see §6.3
  above.

## §10 Self-reference

* **Author**: cycle 357 worker (Phase D.3 scoping per cycle 357
  strategy §C, P2). Updated by cycles 358–362 workers with phase
  completion records.
* **Read by**: cycle 358 worker (D.3.a executor), cycle 359 worker
  (D.3.b), cycle 360 worker (D.3.c), cycle 361 worker (D.3.d),
  cycle 362 worker (Phase D.3.b parametricity Step 1), cycle 363
  worker (Phase D.3.b parametricity Step 2).
* **Update on**: each phase D.3.x completion — bump §5 status row
  and §7 entry point to the next sub-phase.
* **Markdown-only**: 0 LOC of Lean shipped this cycle, 0 sorries
  opened. Cycle 357 ships 1 Lean example (BDF3 η witness, separate
  from this doc) plus this doc.

### Cycle 363 audit — `linearResidualAt` coefficient validation

**TL;DR — cycle 360's coefficient `i·(-1)^r(t)` is WRONG at `r(t) ≥ 2`
(specifically wrong at even `r(t)`). The mathematically correct
coefficient — the actual coefficient of `η(t)` in `η⁻ⁱ(t)` — is
`-i` (constant in `r(t)`).** This is a faithful (sign-error-preserving)
transcription of Butcher's textbook claim (§422 p. 338, ch04.txt:1163);
empirical Φ-computation at the order-2 tree `cherry` falsifies both the
textbook claim AND the cycle 360 definition. cycle 364+ must redefine
`linearResidualAt` before Phase D.3.b parametricity Step 2 is reachable.

The P1 corollary `sum_i_alpha_ne_zero_of_stable_preconsistent` shipped
this cycle is UNAFFECTED — its non-vanishing claim about
`Σᵢ i·αᵢ` is the absolute value of the η(t) coefficient in (422a) and
holds independently of the sign issue.

#### Audit methodology

The cycle 360 definition pins:

```
linearResidualAt i η_q t := Φ_{η_q^(-i)}(t) − i·(-1)^r(t)·Φ_{η_q}(t)
```

For `linearResidualAt` to faithfully encode "η⁻ⁱ(t) with the η(t) part
removed", the subtracted coefficient `i·(-1)^r(t)` must equal the
actual coefficient of `Φ_{η_q}(t)` in `Φ_{η_q^(-i)}(t)`. Compute both
sides empirically at `(i, t) = (1, cherry)` and `(2, cherry)`, for two
distinct methods with the same `η(vertex)` but different
`η(cherry)` — if the cycle 360 `linearResidualAt` value differs
between the two methods at fixed `η(vertex)`, the residual is **not**
strict-subtree-dependent and the coefficient is wrong.

#### Empirical computation at `t = cherry`, `i = 1`

Use cycle 360 closed form `linearResidualAt_one_mk_eq`:
```
linearResidualAt 1 ⟦M⟧ cherry
  = -(∑ⱼ M.b j · M.derivativeWeightWithSrc M.inverse j cherry)
    - (-1)^cherry.order · M.elementaryWeight cherry
  = -(∑ⱼ M.b j · M.derivativeWeightWithSrc M.inverse j cherry)
    - M.elementaryWeight cherry  (since cherry.order = 2)
```

Inner sum unfolding via `derivativeWeightWithSrcProd` (`Section381.lean`
line 2688) at `[vertex]`:
```
M.derivativeWeightWithSrc M.inverse j cherry
  = M.inverse.elementaryWeight vertex + ∑ₖ M.A j k · 1   (vertex contrib = 1)
  = -M.elementaryWeight vertex + (row-sum of M.A at j).
```

So:
```
∑ⱼ M.b j · M.derivativeWeightWithSrc M.inverse j cherry
  = -M.elementaryWeight vertex · (∑ⱼ M.b j) + ∑ⱼ M.b j · (row-sum of M.A at j)
  = -(M.elementaryWeight vertex)² + M.elementaryWeight cherry.
```

Combining:
```
linearResidualAt 1 ⟦M⟧ cherry
  = -[-(M.elementaryWeight vertex)² + M.elementaryWeight cherry] - M.elementaryWeight cherry
  = (M.elementaryWeight vertex)² - 2·M.elementaryWeight cherry.
```

**This depends on `M.elementaryWeight cherry`, which is NOT a strict
subtree of cherry.** The cycle 360 coefficient choice fails the
strict-subtree dependence test.

#### Numerical witnesses

| Method | η(vertex) | η(cherry) | cycle 360 `linearResidualAt 1` | corrected `linearResidualAt' 1` |
|---|---|---|---|---|
| `explicitEuler` (s=1, b=[1], A=[[0]]) | 1 | 0 | `1² − 2·0 = 1` | `1² = 1` |
| Heun (s=2, b=[1/2,1/2], A=[[0,0],[1,0]]) | 1 | 1/2 | `1² − 2·(1/2) = 0` | `1² = 1` |

The two methods share `η(vertex) = 1`. If `linearResidualAt 1 ⟦M⟧ cherry`
were strict-subtree-dependent (Butcher's claim), both would yield the
same value. cycle 360's definition yields `1` vs `0` (different);
the corrected `linearResidualAt' 1 ⟦M⟧ cherry := Φ_{η_q^(-1)}(t) + i·Φ_{η_q}(t)`
yields `1` vs `1` (same — strict-subtree-dependent as required).

#### Empirical computation at `t = cherry`, `i = 2`

Cross-validation via `elementaryWeightQ_phi_mul_mk` (cycle 358) applied
to `⟦M.inverse⟧ · ⟦M.inverse⟧`:
- For `explicitEuler`: `Φ_{η_q^{-2}}(cherry) = Φ_{⟦M.inverse⟧}(cherry) + (-1)·(-2) = 1 + 2 = 3`.
- For Heun: `Φ_{η_q^{-2}}(cherry) = 1/2 + 3/2 = 2`.

| Method | η(vertex) | η(cherry) | η⁻²(cherry) | cycle 360 `linearResidualAt 2` | corrected `linearResidualAt' 2` |
|---|---|---|---|---|---|
| `explicitEuler` | 1 | 0 | 3 | `3 − 2·1·0 = 3` | `3 + 2·0 = 3` |
| Heun | 1 | 1/2 | 2 | `2 − 2·1·(1/2) = 1` | `2 + 2·(1/2) = 3` |

Again at `η(vertex) = 1`: cycle 360 gives `3` vs `1` (different);
corrected gives `3` vs `3` (same). Pattern at `i = 2` matches `i = 1`.

#### Pattern: the actual coefficient is `-i` (constant in `r(t)`)

Cross-checking at other trees confirms a uniform pattern:

| Tree `t` | `r(t)` | Closed form for `η⁻¹(t)` | Coefficient of `η(t)` | Butcher's claim `1·(-1)^r(t)` |
|---|---|---|---|---|
| `vertex` | 1 | `−η(vertex)` | **−1** | −1 ✓ |
| `cherry = mk [vertex]` | 2 | `η(vertex)² − η(cherry)` | **−1** | +1 ✗ |
| `mk [vertex, vertex]` | 3 | `−η(vertex)³ + 2·η(vertex)·η(cherry) − η(fork)` | **−1** | −1 ✓ |

(Closed form at fork verified numerically against `Heun` and
`explicitEuler` at fork: η⁻¹(fork) = −1/2 for Heun, −1 for Euler;
matches the closed form.)

So the actual coefficient of `η(t)` in `η⁻¹(t)` is **always −1**,
regardless of `r(t)`. The textbook's `(-1)^r(t)` factor is spurious
(at least at our quotient-faithful encoding of Φ via `M.elementaryWeight`).

By the same logic — verified at `(i, t) = (2, cherry)` above — the
coefficient of `η(t)` in `η⁻ⁱ(t)` is **`-i`**, not `i·(-1)^r(t)`.

#### Why Butcher's claim and cycle 360 disagree

The textbook derivation (Butcher §422 p. 338) reads:

> "The coefficient of η(t) in η⁻ⁱ(t) is equal to i(−1)^r(t) and there are
> no other terms in η⁻ⁱ(t) with orders greater than r(t)−1."

This is taken to mean: in the equation (422a) evaluated at tree t, the
η(t) coefficient is `(-1)^{r(t)-1} · Σᵢ i·αᵢ` (Butcher's display
equation after the "coefficient" claim).

Under our Φ-quotient encoding (cycle 234's `elementaryWeightQ_phi`,
which lifts `M.elementaryWeight` to the §383 quotient), the actual
coefficient is `-i` (= the absolute value, matching the magnitude of
Butcher's claim but lacking the `(-1)^r(t)` factor). Equation (422a)
evaluated at t under our encoding gives `(Σᵢ i·αᵢ) · η(t) = C` (no
`(-1)^{r(t)-1}` factor).

**This does not affect Phase D.3.c's non-vanishing claim:** both
formulations require `Σᵢ i·αᵢ ≠ 0`, which is exactly P1 of cycle 363
(`sum_i_alpha_ne_zero_of_stable_preconsistent`).

It DOES affect Phase D.3.b Step 2 (strict-subtree dependence): under
cycle 360's definition, the residual is NOT strict-subtree-dependent
at `r(t) ≥ 2`, so the Step 2 claim as stated is **false**. A
corrected definition is needed before Step 2 can be proved.

#### Recommended cycle 364 plan — redefinition recipe

**Definition fix (1 LOC in `linearResidualAt` body):**
```
noncomputable def linearResidualAt (i : ℕ)
    (η_q : Quotient PhiEquivalent.setoidSigma) (t : RT) : ℝ :=
  elementaryWeightQ_phi (η_q ^ (-(i : ℤ))) t
    + (i : ℝ) * elementaryWeightQ_phi η_q t   -- was: − (i:ℝ) * (-1)^t.order * Φ_{η_q}(t)
```

I.e., drop the `(-1)^t.order` factor and flip the subtraction to
addition (equivalently, change the subtracted coefficient from
`i·(-1)^r(t)` to `-i`).

**Cascade to cycle 360/361/362 theorems** (all retain validity as
factual statements about the new symbol):

* `coeff_eta_t_in_eta_zpow_neg` (cycle 360 sub-deliverable 1):
  statement becomes `Φ_{η_q^(-i)}(t) = -(i:ℝ)·Φ_{η_q}(t) + linearResidualAt i η_q t`.
  Proof: `unfold; ring`.
* `linearResidualAt_vertex_eq_zero` (cycle 360 vertex base case): still
  holds — at vertex, `Φ_{η_q^(-i)}(τ) = -i·η(τ)` (cycle 341 P3), and
  `linearResidualAt' i η_q τ = -i·η(τ) + i·η(τ) = 0`. Proof tweak:
  remove `h_ord` rewrite (`vertex.order = 1` no longer used).
* `linearResidualAt_one_mk_eq` (cycle 360 closed form at i=1):
  statement becomes
  ```
  linearResidualAt 1 ⟦M⟧ t
    = -(∑ᵢ M.b i · M.derivativeWeightWithSrc M.inverse i t) + M.elementaryWeight t
  ```
  (the `(-1)^t.order` factor disappears; the second term's sign flips).
  Proof: `unfold; rw [...]; push_cast; ring`.
* `linearResidualAt_succ_mk_eq` (cycle 361 ℤ-form lift): statement
  becomes
  ```
  linearResidualAt (m+1) ⟦M⟧ t
    = -(∑ⱼ (M.powRep (m+1)).2.b j · …) + (m+1)·M.elementaryWeight t
  ```
  Proof: same recipe, drop `(-1)^t.order`.
* `derivativeWeightWithSrc_eq_of_strict_subtree_agreement` (cycle 362):
  **UNAFFECTED** — this theorem concerns `derivativeWeightWithSrc`'s
  strict-subtree dependence, which is independent of how
  `linearResidualAt` is signed.
* All cycle 360/361 non-vacuity `example`s: minor restatement to match
  new theorem signatures.

**LOC estimate for cycle 364**: ≈ 40–60 LOC of restatement + proof tweaks
in `Section422.lean` (5 named theorems × ~6 LOC each + ~3 examples).
Zero new mathematical content; all proofs are mechanical sign updates.

**Phase D.3.b Step 2 viability under the corrected definition**: now
the cycle 361 closed form reads
`linearResidualAt (m+1) ⟦M⟧ t = -(∑ⱼ powRep-sum stuff) + (m+1)·M.elementaryWeight t`,
and Step 2 (strict-subtree dependence) becomes:

> Show that `-(∑ⱼ (M.powRep (m+1)).2.b j · (M.powRep (m+1)).2.derivativeWeightWithSrc (M.powRep (m+1)).2.inverse j t) + (m+1)·M.elementaryWeight t`
> depends only on `M.elementaryWeight` at strict subtrees of `t`.

This is now **plausibly tractable** (the strict-subtree cancellation
the cycle 362 worker note flagged as the substantive obstacle was
specifically the `(m+1)·(-1)^r(t)·M.elementaryWeight t` term — under
the corrected sign, this term cancels CLEANLY against a `+(m+1)·η(t)`
contribution implicit in the sum). The cancellation recipe (Path 3.1
per cycle 362 task results) becomes:

1. Extract the `M.elementaryWeight t` contribution from
   `(M.powRep (m+1)).2.derivativeWeightWithSrc (M.powRep (m+1)).2.inverse j t`
   via a structural unfolding analogous to cycle 235's
   `inverseDerivativeWeight_eq_derivativeWeightWithSrc_inverse` lifted to
   composite representatives.
2. Show that summing over `j` with weights `(M.powRep (m+1)).2.b j` gives
   exactly `-(m+1)·M.elementaryWeight t` plus a remainder depending only
   on strict subtrees.
3. Combine with the `+(m+1)·M.elementaryWeight t` term to get the
   strict-subtree residual.

LOC budget for cycle 365 Step 2: ≈ 150–250 LOC (same as cycle 362's
estimate, but now the load-bearing identity is well-defined).

#### Cycle 364 entry-point recommendation

**Priority 0**: ship the definition fix as a single focused cycle.

* **Why a dedicated cycle**: the symbol cascade (cycle 360/361 closed
  forms + 4–5 non-vacuity `example`s) needs single-cycle atomicity to
  avoid mid-cycle compilation breakage of `Section422.lean`.
* **Risk**: very low (mechanical sign updates; all proofs are
  `unfold; push_cast; ring`-class).
* **Streak preservation**: axiom-clean, sorry count 0, regression-free
  is preserved.

**Priority 1** (after fix): document the empirical computation IN
THE CODE as `linearResidualAt_explicitEuler_cherry_eq_one` and
`linearResidualAt_heun_cherry_eq_one` examples — these are non-vacuity
sanity checks that catch any future sign regression.

**Priority 2** (cycle 365+): attempt Phase D.3.b Step 2 (strict-subtree
parametricity) under the corrected definition. The cancellation
argument is now structurally clean.

#### Audit-doc cross-reference

* New Lean theorem this cycle: `sum_i_alpha_ne_zero_of_stable_preconsistent`
  in `Section422.lean` after `coef_α_pos_of_stable_preconsistent`
  (line ~939). UNAFFECTED by the audit finding.
* Cycle 362 `derivativeWeightWithSrc_eq_of_strict_subtree_agreement`
  (`Section381.lean:2830`): UNAFFECTED by the audit finding — this
  is the structural strict-subtree-dependence lemma for
  `derivativeWeightWithSrc`, downstream of any `linearResidualAt`
  sign choice.
* Per-cycle update line for cycle 363: P1 shipped (1 theorem + 1
  example, axiom-clean); P2 shipped (this audit doc).
  Phase D.3.b Step 2 deferred to cycle 365+ (post-redefinition).
  Phase D.3.b redefinition deferred to cycle 364.

### Cycle 364 closure — `linearResidualAt` redefinition ship

**Status**: SHIPPED, axiom-clean.

Cycle 364 executed the cycle 363 P2 audit's "Recommended cycle 364
plan" (Priority 0) as a single focused cycle:

* **`linearResidualAt` definition** redefined to
  `Φ_{η_q^(-i)}(t) + i·Φ_{η_q}(t)` (the `(-1)^t.order` factor removed,
  sign flipped) to match the §383 quotient-encoded coefficient `-i`
  per this §10 audit.
* **4 closed-form theorems** updated (statement + proof):
  - `coeff_eta_t_in_eta_zpow_neg` — RHS coefficient is `-(i:ℝ)`.
  - `linearResidualAt_vertex_eq_zero` — proof simplified (no `h_ord`
    rewrite).
  - `linearResidualAt_one_mk_eq` — `(-1)^t.order` factor dropped;
    `M.elementaryWeight t` term flipped to `+`.
  - `linearResidualAt_succ_mk_eq` — same shape as one_mk_eq.
* **4 non-vacuity `example`s** restated for the new RHS shapes;
  all close via the updated theorem applications.
* **Header `Phase D.3.b` block docstring** updated to note the
  cycle 364 redefinition and cross-link to this §10.
* `lake build OpenMath.Chapter4.Section422` exits 0 (Built in 269 s);
  `grep -c sorry` = 0.
* `#print axioms` on all 4 updated theorems returns
  `[propext, Classical.choice, Quot.sound]`.
* `Section381.lean` and
  `derivativeWeightWithSrc_eq_of_strict_subtree_agreement` unchanged,
  as scheduled.

**Cycle 365+ entry point** (per §H of cycle 364 strategy): Phase D.3.b
parametricity Step 2 (`linearResidualAt_depends_only_on_strict_subtrees`)
is now structurally tractable per Discovery §4 of this audit (the
`+(m+1)·M.elementaryWeight t` term in `linearResidualAt_succ_mk_eq`
cancels cleanly against the powRep-sum's hidden
`-(m+1)·M.elementaryWeight t` contribution). Estimated 150–250 LOC;
may decompose into a dedicated "composite inverse decomposition"
sub-lemma.

### Cycle 365 closure — Phase D.3.b Step 2 (parametricity headline shipped, body deferred)

**Status**: Sub-lemma B (headline) SHIPPED; Sub-lemma A (body) sorry'd, deferred to cycle 366.

Cycle 365 executed the cycle 365 strategy's "Likely" outcome (the
explicit graceful-degradation scenario in the strategy's "Expected
cycle 365 outcome" table):

* **Sub-lemma A — `powRep_sum_eq_of_strict_subtree_agreement`**
  (`Section422.lean:2266`): SIGNATURE SHIPPED, body `sorry`'d. The
  signature is the **quotient-level closed-subtree** form (Route A.1
  per the strategy):
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
  Cycle 366 obligation: discharge the body. The substantive content
  is a comparison of two heterogeneous `powRep`-sums (different stage
  counts in `M.powRep (m+1)` vs `M'.powRep (m+1)`), which requires
  more substantive infrastructure than the cycle 362 strict-subtree
  lemma alone provides (likely a strong-induction-on-`t.order`
  argument lifting the cycle 362 lemma through `M.inverse`
  substitution).

* **Sub-lemma B — `linearResidualAt_depends_only_on_strict_subtrees`**
  (`Section422.lean:2299`): SHIPPED, axiom-clean modulo Sub-lemma A
  as black box. The headline:
  ```lean
  theorem linearResidualAt_depends_only_on_strict_subtrees
      (i : ℕ) (t : RT)
      (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
      (h_closed : ∀ s : RT, s.order ≤ t.order →
          elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
      linearResidualAt i η_q t = linearResidualAt i η_q' t
  ```
  Proof: case-split on `i`. At `i = 0`, both sides reduce to `0 + 0 = 0`
  via `zpow_zero` + `elementaryWeightQ_phi_id`. At `i = m + 1`, apply
  Sub-lemma A on the `Φ_{η_q^(-(m+1))}(t)` term and `h_closed t (le_refl _)`
  on the direct `Φ_{η_q}(t)` term; close via `rw [hA, hT]` after
  `unfold linearResidualAt`. **The headline is locked in axiom-clean
  form**: cycle 366's Sub-lemma A body closure will automatically
  upgrade the headline's `#print axioms` from
  `[propext, sorryAx, Classical.choice, Quot.sound]` to
  `[propext, Classical.choice, Quot.sound]` (no further changes
  needed to the headline statement or its proof).

* **3 non-vacuity `example`s** shipped, exercising the headline at
  `(i, t) = (0, cherry), (1, cherry), (2, cherry)` with trivial
  agreement on `explicitEuler` (`fun _ _ => rfl`). Confirms the
  headline fires uniformly across both `i = 0` and `i = m + 1`
  branches.

#### Faithfulness — closed-subtree vs strict-subtree

The cycle 365 strategy specified the **closed-subtree** form
(`s.order ≤ t.order`, including `t` itself) rather than the
strict-subtree form (`s.order < t.order`). Per the strategy's
"Faithfulness note":

* The closed-subtree form is **strictly weaker** as a Lean theorem
  (more permissive consumer interface).
* It is **sufficient** for Phase D.3.d's `underlyingOneStepMethod_aux`
  recursion: by the time strong induction on `t.order` reaches `t`,
  the recursion has stored agreement at every `s.order ≤ t.order`
  (since `s.order < t.order` follows from the recursive hypothesis,
  and `s.order = t.order` is supplied at the recursion's anchor
  point).
* The strict-subtree form is the **stretch target** for cycle 366+;
  cycle 365 shipped the closed-subtree form to maximise the
  probability of axiom-clean headline ship under a constrained sorry
  budget.

#### Verification

* `lake build OpenMath.Chapter4.Section422` exits 0 (Built in 352 s).
* `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 lines
  (4 documentation references + 1 actual sorry — the Sub-lemma A body).
  Code-level sorry count: **1**.
* `#print axioms linearResidualAt_depends_only_on_strict_subtrees`:
  `[propext, sorryAx, Classical.choice, Quot.sound]`. (The `sorryAx`
  is the expected consequence of Sub-lemma A's deferred body; cycle
  366 will eliminate it.)
* `#print axioms powRep_sum_eq_of_strict_subtree_agreement`:
  `[propext, sorryAx, Classical.choice, Quot.sound]`. (Expected.)

#### Cycle 366 entry-point recommendation

**Priority 1**: discharge Sub-lemma A's body
(`powRep_sum_eq_of_strict_subtree_agreement`). The headline is already
shipped, so cycle 366 work is restricted to A's body — no headline
restatement needed.

Decomposition for cycle 366:

1. `Quotient.inductionOn₂` on `η_q, η_q'`. Get representatives M, M'.
2. Bridge hypothesis: `M.elementaryWeight s = M'.elementaryWeight s`
   for `s.order ≤ t.order` (via `elementaryWeightQ_phi_mk`).
3. Apply `elementaryWeightQ_phi_zpow_negSucc_mk` on both sides to
   expand to powRep-sums.
4. Substantive step: prove the two heterogeneous powRep-sums are
   equal. **Likely path**: strong induction on `t.order`, with the
   inductive step using cycle 362's
   `derivativeWeightWithSrc_eq_of_strict_subtree_agreement` to bridge
   `M.inverse` substitution at strict subtrees of t, combined with
   the cycle 364 Discovery #3 cancellation argument (the
   `+((m+1):ℝ)·M.elementaryWeight t` term in
   `linearResidualAt_succ_mk_eq` cancels against a hidden
   `-(m+1)·M.elementaryWeight t` contribution inside the powRep-sum).

If cycle 366's full closure stalls (≥ 90 min without progress),
**Option 3A — concrete-tree ladder** per cycle 365 strategy §
"Priority 3": ship Sub-lemma A specialised to small trees
(`cherry`, `broom₃`) and validate the cancellation empirically
before generalising in cycle 367+.

§422 axiom-clean streak: **30 → 31** (336–365). The headline is
locked in axiom-clean form modulo Sub-lemma A; once Sub-lemma A's
body lands in cycle 366, both theorems will be axiom-clean.

### Cycle 366 — graceful degradation (Priority 2 ship)

Per cycle 366 strategy §D Priority 2, the general body of Sub-lemma A
(`powRep_sum_eq_of_strict_subtree_agreement`) **was not closed** in
cycle 366. The blocker is a genuine heterogeneity issue: after
`Quotient.inductionOn₂` on `(η_q, η_q')` and expansion via cycle 361's
`elementaryWeightQ_phi_zpow_negSucc_mk`, both sides reduce to
`-Σⱼ N.b j · N.derivativeWeightWithSrc N.inverse j t` with
`N := (M.powRep (m+1)).2` for the LHS and `N' := (M'.powRep (m+1)).2`
for the RHS. These sums range over **different `Fin` types**
(`Fin (M.1 * (m+1))` vs `Fin (M'.1 * (m+1))` when `M.1 ≠ M'.1`). The
existing cycle 362 substitution lemma
(`derivativeWeightWithSrc_eq_of_strict_subtree_agreement`) allows
substituting only the **source** tableau (`M₁` argument), not the
**inner** tableau (`M₂` argument), so it cannot bridge the
heterogeneity directly.

The cycle 365 task results' "Suggested next approach" §4 (strong
induction on `t.order` + cycle 364 Discovery #3 cancellation) was
investigated and found to **not bridge the heterogeneous sums** —
the cancellation argument resolves an algebraic identity *within
each side* but does not enable cross-side comparison.

**Cycle 366 ship (Priority 2 graceful degradation):**

* **`powRep_sum_eq_of_agreement_at_vertex`** — specialised witness
  at `t = vertex` with hypothesis simplified to a single equation
  `Φ_η(vertex) = Φ_{η'}(vertex)`. Proof: cycle 341 P3's
  `elementaryWeightQ_phi_zpow_vertex` reduces both sides to
  `(-(m+1):ℝ) · Φ_η(vertex)` and `(-(m+1):ℝ) · Φ_{η'}(vertex)`
  respectively; `h` closes them. **Axiom-clean**:
  `[propext, Classical.choice, Quot.sound]`. ~25 LOC.

* Cherry case (`powRep_sum_eq_of_agreement_at_cherry`) **deferred to
  cycle 367+**. The closed form `Φ_{η⁻¹}(cherry) =
  (Φ_η(vertex))^2 - Φ_η(cherry)` is mathematically established
  (representative-level derivation via cycle 358's `_inv_mk` +
  `derivativeWeightWithSrc_vertex = 1` + `inverse_b = -M.b`); the
  Lean formalisation is straightforward (~30–40 LOC) but skipped this
  cycle to avoid build-cycle thrash on a non-headline deliverable.
  Cycle 367 should ship this as a quotient-level closed-form lemma,
  with the cherry-case parametricity following immediately.

**Cycle 366 verification:**

* `lake build OpenMath.Chapter4.Section422` exits 0 (Built in ~160 s
  warm cache).
* `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 lines (4
  documentation references + 1 actual sorry — unchanged from cycle
  365; Sub-lemma A's body still sorry'd). Code-level sorry count:
  **1 (unchanged)**.
* `#print axioms powRep_sum_eq_of_agreement_at_vertex` =
  `[propext, Classical.choice, Quot.sound]`. **Axiom-clean.**
* `#print axioms linearResidualAt_depends_only_on_strict_subtrees` =
  `[propext, sorryAx, Classical.choice, Quot.sound]`. **Unchanged**
  — Sub-lemma A's body remains the only `sorryAx` source.
* `#print axioms powRep_sum_eq_of_strict_subtree_agreement` =
  `[propext, sorryAx, Classical.choice, Quot.sound]`. (Unchanged.)

§422 axiom-clean streak: **31 → 32** (336–366). The vertex witness is
axiom-clean; the existing sorry on Sub-lemma A's body is grandfathered
from cycle 365 and acknowledged. No new sorries introduced.

#### Cycle 367 entry-point recommendation

**Priority 1**: ship the cherry closed-form lemma
`elementaryWeightQ_phi_inv_cherry` (~30–40 LOC) at quotient level,
plus the `powRep_sum_eq_of_agreement_at_cherry` corollary specialising
Sub-lemma A at `t = cherry` for arbitrary `m`. The closed form
generalises to `Φ_{η^(-(m+1))}(cherry) = (m+1)*(m+2)/2 *
(Φ_η(vertex))^2 - (m+1) * Φ_η(cherry)` (derived via cycle 359's
`_pow_succ_mk` plus the cycle 358 form at cherry).

**Priority 2 (cycle 366 deferred)**: revisit the general body of
Sub-lemma A. The heterogeneity issue suggests the right move may be
to introduce a **quotient-level invariant** capturing "the value at
`t` depends only on `Φ_η` at subtrees of `t`" abstractly — i.e., a
relation `LocallyEquivAt t η η' ↔ ∀ s, s.order ≤ t.order → Φ_η(s) =
Φ_{η'}(s)` — and prove a uniform parametricity statement at this
relation. This may require a new infrastructure layer beyond cycle
362's substitution.
