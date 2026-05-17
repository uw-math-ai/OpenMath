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
| **D.3.a.3** | 1 (cycle 359, deferred) | `elementaryWeightQ_phi_zpow_mk` (`^ (· : ℤ)` at arbitrary `t`). Requires a `RKTableau.powRep : (m : ℕ) → Σ s', RKTableau s'` construction (recursive composition + quotient-equality lemma) since the bottom-block at each `pow_succ` step depends on the chosen representative of the previous power. | ~80 | Partial |
| **D.3.b** | 1 (cycle 360) | Linear coefficient extraction: `coeff_eta_t_in_eta_zpow_neg` — the textbook claim "coefficient of η(t) in η⁻ⁱ(t) is i(−1)^r(t)". Uses D.3.a.{1,2,3}. | 100 | Partial (sign algebra) |
| **D.3.c** | 1 (cycle 361) | `sum_i_alpha_ne_zero_of_stable` — `ρ'(1) ≠ 0` from ρ-stability via simple-root analysis. **Mathlib hook check required first.** | 80 | Poor (polynomial roots) |
| **D.3.d** | 1 (cycle 362) | `noncomputable def underlyingOneStepMethod_aux` recursion + `_satisfies_Eq422a` spec lemma. Closes `thm:422A`'s substantive content. | 120 | Partial (well-founded recursion proof obligations) |

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

**Total**: 4 cycles. Sequential dependencies (D.3.a → D.3.b → D.3.d
must be in order; D.3.c is parallel to D.3.a/D.3.b).

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
  strategy §C, P2).
* **Read by**: cycle 358 worker (D.3.a executor), cycle 359 worker
  (D.3.b), cycle 360 worker (D.3.c), cycle 361 worker (D.3.d).
* **Update on**: each phase D.3.x completion — bump §5 status row
  and §7 entry point to the next sub-phase.
* **Markdown-only**: 0 LOC of Lean shipped this cycle, 0 sorries
  opened. Cycle 357 ships 1 Lean example (BDF3 η witness, separate
  from this doc) plus this doc.
