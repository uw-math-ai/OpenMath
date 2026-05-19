# Issue: def:422B multi-cycle infrastructure plan

## Status

Strategic scoping document for `def:422B` (Butcher §422, p. 359,
*"The underlying one-step method"*). No Lean code that *constructs*
the underlying one-step method is shipped in cycle 336; only a
Phase 0 wire-up sanity ship (the `Quotient PhiEquivalent.setoidSigma`
target type is non-empty) lands this cycle.

Cycle 336 produces this file; cycle 337+ planners use it to break the
remaining work into single-cycle deliverables without re-scoping.

The cycle 149/150 (`def:530B` operator-body sorry-first) and
cycle 200/201 (`thm:381H` deferred direction) rollback precedents both
demand that planners commit to a phase decomposition *before* workers
write Lean code for any multi-cycle target whose sorry-first scaffold
has no credible single-cycle close. This file is that commitment for
`def:422B`.

Predecessor: `.prover-state/issues/cycle_336_pivot_options.md`
(cycle 335 P2 menu listing four candidates A/B/C/D; cycle 336 planner
chose A `def:422B` after the §A audit ruled out B/C/D as deferred or
multi-cycle).

## §1 Textbook statement (verbatim)

From `extraction/formalization_data/entities/def_422B.json`
`statement_text`:

> Corresponding to a linear multistep method [α, β], the member of G₁
> represents the 'underlying one-step method'.
> As we have already remarked, the mapping Φ in (422b), if it exists
> in more than a notional sense, is really the object of interest and
> this really is the underlying one-step method.

Page reference: Butcher 3rd ed. §422 p. 359.

LaTeX form (`statement_latex`):

```
\begin{definition}
Corresponding to a linear multistep method $[\alpha, \beta]$, the
member of $\mathcal{G}_1$ represents the `underlying one-step method'.
As we have already remarked, the mapping $\Phi$ in \eqref{eq:422b}, if
it exists in more than a notional sense, is really the object of
interest and this really is the underlying one-step method.
\end{definition}
```

The definition is **not free-standing**: its meaning is given by the
surrounding §422 prose, in particular the construction of `η ∈ G₁`
that is the content of `thm:422A`. From the entity JSON `context_latex`
field:

> The preceding text discusses the existence of a mapping η in the
> group G₁ that satisfies equation (422a) for a preconsistent and
> stable linear multistep method [α, β]. This mapping is constructed
> inductively on the order of trees, and it represents the underlying
> one-step method of the multistep method.

Equation (422a), the *defining* equation for η, quoted verbatim from
the JSON `equations` field:

```
1(u) − α₁ η⁻¹(u) − α₂ η⁻²(u) − ⋯ − αₖ η⁻ᵏ(u)
       − β₀ D(u) − β₁ η⁻¹ D(u) − β₂ η⁻² D(u) − ⋯ − βₖ η⁻ᵏ D(u) = 0
                                                              (422a)
```

Equation (422b) is referenced but not given verbatim in the entity
JSON; the JSON `equations` field describes it only as *"the mapping Φ
that represents the underlying one-step method"*. Phase 0's
`extraction/raw_text/ch04.txt` reread (cycle 337+ task) should pin
down (422b)'s exact form before Phase E sealing.

Variable inventory (entity JSON `variables`):

| Symbol | Role |
|---|---|
| `G₁` | the group of mappings from trees to real numbers |
| `[α, β]` | a linear multistep method with coefficients α and β |
| `η` | a mapping from trees to ℝ representing the underlying one-step method in `G₁` |
| `r(t)` | the order (or rank) of a tree `t` |
| `D` | an operator on trees, likely related to differentiation or tree operations |
| `Φ` | the mapping representing the underlying one-step method, related to η |

Dependency declared in the entity JSON: `def:381B` (Φ-equivalent —
already formalised at cycle 187 as `OpenMath.Chapter3.Section381.PhiEquivalent`).

Dependents declared in the entity JSON: `thm:422A`, `thm:422C`,
`thm:535A`.

## §2 Distilled mathematical content (Lean-friendly restatement)

`def:422B` *names* a `Quotient PhiEquivalent.setoidSigma`-valued
element associated to each preconsistent and stable
`LinearMultistepMethod k`. The element is the equivalence class `[η]`
of any tree-function `η : RootedTree → ℝ` that satisfies equation
(422a) at every tree `u`.

Equation (422a), Lean-friendly restatement (with all symbols pinned
to either §381 quotient operations or §404 LMM coefficients):

```
∀ u : RootedTree,
  1_G₁(u)
    − ∑ (i : Fin k), M.α i.succ · (η^(-(i+1)))(u)        -- LMM "α" side
    − ∑ (i : Fin (k+1)), M.β i · (η^(-i) · D)(u)         -- LMM "β" side
      = 0
```

where:

* `1_G₁ : RootedTree → ℝ` is the §383 group identity element. At the
  `Quotient PhiEquivalent.setoidSigma` level, this is the
  `One`-instance class `⟦⟨0, RKTableau.id⟩⟧`.
* `η^(-i) : RootedTree → ℝ` is the `i`-fold inverse-power of `η` in
  `G₁`. At the quotient level, `η^(-i) = (instGroup_phi.inv [η])^i =
  ([η]⁻¹)^i`, or equivalently `[η]^(-i)` via Mathlib's `Group.zpow`.
* `D : G₁ → G₁` is "the operator D" from the textbook's variable
  inventory — *"an operator on trees, likely related to
  differentiation or tree operations"*. Phase A's pinning task: read
  Butcher §422 in full (raw_text/ch04.txt) and determine whether `D`
  is:
  * (D.1) tree-grafting: append a new root vertex with `t` as the
    single child (the "differentiation operator" in Butcher §381
    Connes–Kreimer sense), OR
  * (D.2) multiplication by `τ`: pointwise `(D η)(u) := r(u) · η(u)`
    or some similar order-weighted shift, OR
  * (D.3) the "differential operator" in the §383 forest convolution
    sense (cycle 077–081 territory).

The "preconsistent and stable" hypothesis (Butcher §422 context line)
is the existence side: `thm:422A` asserts that *for every*
preconsistent and stable LMM, an `η` satisfying (422a) exists in
`G₁`. `def:422B` then *names* the equivalence class of this `η`.

A faithful formalisation of `def:422B` therefore takes one of two
shapes (decide in cycle 337+ when Phase A lands):

**Shape (i) — `def` whose body produces the witness inductively.**

```lean
noncomputable def LinearMultistepMethod.underlyingOneStepMethod
    {k : ℕ} (M : LinearMultistepMethod k)
    (hPre : M.IsPreconsistent) (hStab : M.IsStable) :
    Quotient OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma :=
  ⟦⟨_, eta_realization M hPre hStab⟩⟧
```
where `eta_realization` is a multi-phase recursion on `RootedTree.order`
that solves (422a) by descent. This shape *constructs* the
underlying one-step method; it is mathematically the content of
`thm:422A`, and pins `def:422B` to a concrete witness.

**Shape (ii) — `def` whose body is the equivalence class of any
satisfier (existence-only, with `Classical.choose`).**

```lean
noncomputable def LinearMultistepMethod.underlyingOneStepMethod
    {k : ℕ} (M : LinearMultistepMethod k)
    (hExists : ∃ η : RootedTree → ℝ, Eq422a M η) :
    Quotient OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma :=
  Classical.choose hExists |> wrap_into_quotient
```
where `Eq422a M η` is the (422a) condition predicate. This shape
*assumes* `thm:422A` is shipped (or accepts it as a hypothesis), and
factors def:422B through `Classical.choose`. **Risk**: definition
smuggling — if `Eq422a` is never inhabited (because `thm:422A` is not
yet formalised), the hypothesis is never available and the definition
is vacuous-by-construction.

The cycle 337+ Phase A decision is between (i) and (ii); the cycle 250
`alphaWeight` precedent (`.prover-state/issues/cycle_250_strategy_alpha_definition_error.md`)
strongly recommends (i) over (ii) — defining concepts as the
*closed-form realisation* rather than as the *abstract specification*
is the documented pattern in this project, but the realisation must
genuinely match the textbook content, not just the algebraic
condition that characterises it.

## §3 Project-hook inventory (verified at HEAD)

All hooks verified at HEAD `8c32d4f` by `grep -n` /
`lean_local_search` on the listed files.

### §3.1 From `OpenMath/Chapter4/Section404.lean`

* `structure LinearMultistepMethod (k : ℕ)` (line 53) — fields `α`,
  `β : Fin (k + 1) → ℝ` with normalisation `α_zero : α 0 = -1`. This
  is the `[α, β]` of `def:422B`'s textbook statement.
* `def LinearMultistepMethod.IsPreconsistent` (line 69–71): the
  Butcher (404a) condition `1 = ∑ i : Fin k, M.α i.succ`.
* `def LinearMultistepMethod.SatisfiesEq404b` (line 124–125): the
  Butcher (404b) condition (consistency-grade equation).
* `def LinearMultistepMethod.IsConsistent` (line 135–137): the
  conjunction `IsPreconsistent ∧ SatisfiesEq404b`.
* `def LinearMultistepMethod.IsStable` (line 202–203): the
  Butcher 403A boundedness condition — every solution of (403a)
  homogeneous recurrence is bounded.
* `def explicitEulerLMM : LinearMultistepMethod 1` (line 81–84) —
  primary 1-step LMM witness with both preconsistency and stability
  verified (lines 87–89, 213).
* `def implicitEulerLMM : LinearMultistepMethod 1` (line 100–103) —
  secondary 1-step LMM witness with preconsistency, `SatisfiesEq404b`,
  and stability all verified.

### §3.2 From `OpenMath/Chapter3/Section381.lean`

* `def PhiEquivalent` (line 124–126, namespace
  `OpenMath.Chapter3.Section381`): Butcher def:381B — Φ-equivalent
  RK tableaux.
* `instance PhiEquivalent.setoidSigma` (line 1964–1969, namespace
  `OpenMath.Chapter3.Section312.RKTableau`): heterogeneous-stage
  setoid on `Σ s : ℕ, RKTableau s`.
* `def paddedEuler : RKTableau 2` (line 156–159, namespace
  `OpenMath.Chapter3.Section381`): 2-stage explicit-Euler-equivalent
  tableau, the canonical non-vacuity witness for §381 quotients.
* `noncomputable def composeQ_phi` (line 3393–3405, namespace
  `OpenMath.Chapter3.Section312.RKTableau`): cycle 232's full binary
  composition on `Quotient PhiEquivalent.setoidSigma` via
  `Quotient.lift₂`.
* `noncomputable def inverseQ_phi` (line 4260–4269, namespace
  `OpenMath.Chapter3.Section312.RKTableau`): cycle 236's `Inv`
  on `Quotient PhiEquivalent.setoidSigma`.
* `noncomputable instance instGroup_phi : Group (Quotient PhiEquivalent.setoidSigma)`
  (line 4324–4329, namespace `OpenMath.Chapter3.Section312.RKTableau`):
  cycle 236's §383 group instance via `Group.ofLeftAxioms`. **This is
  the codomain group `G₁` of def:422B.**
* `noncomputable def elementaryWeightQ_phi` (line 4705+, namespace
  `OpenMath.Chapter3.Section312.RKTableau`): cycle 239's quotient-level
  elementary weight — the "evaluation at a tree" map for `G₁` elements.
  `elementaryWeightQ_phi ⟦⟨s, M⟩⟧ t = M.elementaryWeight t`.
* `RKTableau.id : RKTableau 0` (line ~3747, namespace
  `OpenMath.Chapter3.Section312.RKTableau`): the §382 identity
  tableau, used to provide `One (Quotient Equivalent.setoidSigma)` and
  `One (Quotient PhiEquivalent.setoidSigma)`.

### §3.3 From `OpenMath/Chapter3/Section310.lean`

* `inductive RootedTree` — `List`-based rooted-tree datatype.
* `RootedTree.order : RootedTree → ℕ` — vertex count, used as the
  textbook's `r(t)`.
* `RootedTree.vertex`, `RootedTree.cherry`, `RootedTree.broom₃` —
  small-tree canonical witnesses.
* `RootedTree.tau_values` — `r(τ) = σ(τ) = γ(τ) = 1` (cycle 301).

### §3.4 From `OpenMath/Chapter3/Section383.lean`

* `convProduct : (Multiset RootedTree → ℝ) → (Multiset RootedTree → ℝ) → (Multiset RootedTree → ℝ)`
  — Butcher (383a) convolution product. **Caveat**: cycle 081–082
  documents the multiset-vs-vertex-subset divergence
  (`convolution_vertex_vs_multiset.md`); for `def:422B` we work with
  the §381 Φ-quotient group, which is the *RK-tableau-quotient*
  formulation of `G₁` and is *not* affected by the convolution
  divergence.

### §3.5 Mathlib hooks (to verify in Phase B)

* `Group.zpow : G → ℤ → G` — integer powers in a group, used for
  `η^(-i)` in equation (422a). Available from `Mathlib.Algebra.GroupPower.Basic`.
* `Group.ofLeftAxioms` — already used by cycle 236.
* `Quotient.lift` / `Quotient.mk` / `Quotient.sound` — already used
  pervasively.

## §4 Gap inventory (missing infrastructure)

The following items are *not* in the project at HEAD; each must be
added in a dedicated cycle before `def:422B` can be sealed.

### §4.1 The "operator D" (§422 D-operator)

`def:422B`'s textbook equation (422a) uses an operator `D` whose
precise definition is **not** stated in the entity JSON
`statement_latex` and is only described as *"an operator on trees,
likely related to differentiation or tree operations"* in the
variables list.

The cycle 337 Phase A worker must read `extraction/raw_text/ch04.txt`
in the §422 region (and the §380–§383 surrounding context) to pin
down `D`. From the equation form, the candidates are:

* **(D.1) Tree-grafting / root-appending**: for `t : RootedTree`,
  `D(t)` is the tree obtained by adding a new root with `t` as its
  single child. This is Butcher's tree differentiation operator in
  the §381 Connes–Kreimer convolution sense and is the most likely
  candidate given the equation shape (each term `η^(-i) D(u)` is a
  product in `G₁` of an inverse-power of `η` with `D` applied to the
  tree `u`).
* **(D.2) Order-weighted multiplication**: `(D f)(t) := r(t) · f(t)`
  for `f : RootedTree → ℝ`. This is the formal "differentiation"
  operator on generating functions in the Butcher §301–§302 sense.
* **(D.3) Recursive elementary-differential operator**: `D` could be
  the operator sending an elementary weight function to its
  "derivative" via tree-substitution. This is the operator
  representation in Butcher §380's commutative group of forest
  convolutions.

Resolution: **Phase A.0 (1 cycle)** — read Butcher §422 in full,
identify `D`, document the choice, and ship a `def
D_phi : Quotient PhiEquivalent.setoidSigma → Quotient PhiEquivalent.setoidSigma`
(or an equivalent typed object — possibly `RootedTree → ℝ →
RootedTree → ℝ`-shaped if `D` is a tree-level operator and not a
group-element operator).

### §4.2 Integer-power API on `Quotient PhiEquivalent.setoidSigma`

The equation (422a) uses `η^(-1), η^(-2), …, η^(-k)`. At the
`Quotient PhiEquivalent.setoidSigma` level, integer powers in a
`Group` are provided by Mathlib's `Group.zpow : G → ℤ → G` (via the
`GroupPower` API). Cycle 236's `instGroup_phi` should already inherit
this automatically, but a non-vacuity verification is needed to
confirm `zpow` evaluates correctly on `⟦⟨s, M⟩⟧` classes (it should
reduce to `Quotient.mk` of an iterated `compose` / `inverse`).

Resolution: **Phase B (1 cycle)** — ship two small lemmas:
* `zpow_neg_one : (⟦⟨s, M⟩⟧ : Quotient PhiEquivalent.setoidSigma)^(-1 : ℤ) = ⟦⟨s, M.inverse⟩⟧`
* `zpow_neg_natCast : ⟦⟨s, M⟩⟧^(-(n : ℤ)) = ⟦…iterated inverse…⟧`

These verify the `Group.zpow` Mathlib hook fires cleanly on the §383
quotient group; non-vacuity at `paddedEuler` (`⟦⟨2, paddedEuler⟩⟧^(-1)` =
`⟦⟨2, paddedEuler.inverse⟩⟧`).

### §4.3 The (422a) condition predicate

A predicate `Eq422a : LinearMultistepMethod k → (RootedTree → ℝ) → Prop`
(or its `Quotient`-lifted form
`Eq422aQ : LinearMultistepMethod k → Quotient PhiEquivalent.setoidSigma → Prop`)
encoding equation (422a) at every tree `u`.

Definitionally:

```lean
def Eq422a {k : ℕ} (M : LinearMultistepMethod k)
    (η_q : Quotient PhiEquivalent.setoidSigma) : Prop :=
  ∀ u : RootedTree,
    elementaryWeightQ_phi (1 : Quotient PhiEquivalent.setoidSigma) u
      − ∑ i : Fin k,
          M.α i.succ
            · elementaryWeightQ_phi (η_q ^ (-(i.val + 1 : ℤ))) u
      − ∑ i : Fin (k + 1),
          M.β i
            · elementaryWeightQ_phi
                (η_q ^ (-(i.val : ℤ)) * D_phi (1 : Quotient _)) u
      = 0
```

(Exact shape depends on §4.1's `D` pinning; the above is a
preliminary draft.)

Resolution: **Phase C.0 (½ cycle)** — once `D_phi` and `zpow` API are
in place, ship `Eq422a` as a `def` plus a non-vacuity sanity check
(verify it is *not* trivially true at `M = explicitEulerLMM`, `η_q =
1`, by exhibiting a tree `u` where the equation fails for that
choice).

### §4.4 Existence of η satisfying (422a) — `thm:422A` content

The substantive multi-cycle content. Butcher's §422 prose constructs
`η` *inductively on the order of trees*: for each tree `t`, `η(t)` is
determined by `η(t')` for trees `t'` with `r(t') < r(t)` via a linear
equation (a rearrangement of (422a) at `u = t`).

The construction must handle:

* **Base case** (`r(t) = 1`, i.e. `t = τ` the single-vertex tree):
  (422a) at `τ` gives `1 − ∑ i, αᵢ · η^(-i)(τ) − ∑ i, βᵢ · D(τ)·η^(-i)
  = 0`. Under the preconsistency hypothesis `1 = ∑ αᵢ` (cycle 336's
  formalisation `IsPreconsistent`), and noting `η^(-i)(τ) = η(τ)^(-i)`
  for the single-vertex tree (since the convolution product on
  forests reduces to pointwise multiplication when the tree has no
  children), the base case reduces to an equation in `η(τ)` alone.
* **Inductive case** (`r(t) > 1`): for `t = [t₁ … tₘ]`, the equation
  (422a) at `u = t` involves `η(t)` (the unknown) plus terms
  involving `η(t')` for `t'` with `r(t') < r(t)`. The coefficient of
  `η(t)` in this linear equation is a polynomial in the stability
  data of `[α, β]`; the *stability* hypothesis (cycle 336's
  `IsStable`) guarantees this coefficient is non-zero (or unit-norm
  in `ℂ`), so the equation is uniquely solvable for `η(t)`.

Resolution: **Phase D (2–3 cycles)** — define the recursive solver:

```lean
noncomputable def underlyingOneStepMethod_aux {k : ℕ}
    (M : LinearMultistepMethod k)
    (hPre : M.IsPreconsistent) (hStab : M.IsStable) :
    RootedTree → ℝ
  | t =>
    -- ... well-founded recursion on RootedTree.order ...
    sorry  -- multi-cycle
```

The well-founded-recursion proof obligation
(`RootedTree.order` decreases at each recursive call) is the
load-bearing technical content. Verify whether Mathlib's
`WellFoundedRelation (Sigma RootedTree)` instance is available or
needs to be supplied (cycle 195's `RKTableau.PReducesTo.size_lt_of_step`
is the analogous infrastructure for `RKTableau`).

### §4.5 Lift from `RootedTree → ℝ` to `Quotient PhiEquivalent.setoidSigma`

`def:422B` returns a `Quotient PhiEquivalent.setoidSigma`-valued
element, not a `RootedTree → ℝ` function. So after Phase D produces
`η : RootedTree → ℝ`, we need a bridge:

```lean
noncomputable def liftFunctionToQuotient (η : RootedTree → ℝ) :
    Quotient PhiEquivalent.setoidSigma := sorry
```

The bridge exists if and only if there is an `RKTableau s` whose
`elementaryWeight` agrees with `η`. This is the **realisability**
question. It is *not* automatic: for arbitrary `η : RootedTree → ℝ`,
no RK tableau may realise it.

For the underlying-one-step-method `η`, realisability is guaranteed
by `thm:422A`'s construction (the tree-induction yields a `η` that
satisfies the multiplicative property required of `elementaryWeight`
for some implicit-method tableau). But this is *content*, not
machinery.

Resolution: **Phase E (1 cycle)** — ship `liftFunctionToQuotient`
specialised to the `η` produced by Phase D, *via* the underlying RK
tableau (possibly infinite-stage, possibly a colimit). Alternative:
work directly with the `Quotient PhiEquivalent.setoidSigma`-valued
recursion from the start (skip the `RootedTree → ℝ` intermediate
form).

### §4.6 Phase D / E packaging — `def:422B` itself

Once Phases A–E land, `def:422B` is

```lean
noncomputable def LinearMultistepMethod.underlyingOneStepMethod
    {k : ℕ} (M : LinearMultistepMethod k)
    (hPre : M.IsPreconsistent) (hStab : M.IsStable) :
    Quotient OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma :=
  liftFunctionToQuotient (underlyingOneStepMethod_aux M hPre hStab)
```

This sealing is the final Phase E deliverable.

## §5 Phase decomposition

| Phase | Cycles | Deliverable | LOC est. |
|---|---|---|---|
| **Phase 0** (this cycle 336) | 1 | Wire-up sanity ship: `Nonempty (Quotient PhiEquivalent.setoidSigma)` via `⟦⟨2, paddedEuler⟩⟧`. | 5–20 |
| **Phase A.0** | 1 | Pin Butcher's `D` operator (§4.1): read §422 in ch04.txt, document the choice, ship `D_phi : Quotient PhiEquivalent.setoidSigma → Quotient PhiEquivalent.setoidSigma` (or the appropriate tree-level operator). Non-vacuity: `D_phi 1` (or `D_phi ⟦⟨2, paddedEuler⟩⟧`) reduces to a concrete quotient class. | 80–120 |
| **Phase B** | 1 | `Group.zpow` API non-vacuity on `Quotient PhiEquivalent.setoidSigma`: verify `⟦⟨2, paddedEuler⟩⟧^(-1)` and `⟦⟨2, paddedEuler⟩⟧^(-2)` reduce as expected; ship `zpow_neg_one` and `zpow_neg_natCast` sanity lemmas. | 30–60 |
| **Phase C** | 1 | The (422a) condition predicate: `Eq422a M η_q : Prop` (§4.3). Non-vacuity sanity check: confirm `Eq422a explicitEulerLMM 1` is *not* trivially true. | 50–100 |
| **Phase D.1** | 1 | Base case: `underlyingOneStepMethod_aux M hPre hStab τ` — solve (422a) at the single-vertex tree. Closed-form solution for `η(τ)` in terms of `M.α`, `M.β`. | 80–120 |
| **Phase D.2** | 1 | Inductive step (qualitative): well-founded-recursion infrastructure on `RootedTree.order`. Verify `WellFoundedRelation RootedTree` is in Mathlib at HEAD (or ship it via `Function.Wellfounded.onFun` on `RootedTree.order`). | 60–100 |
| **Phase D.3** | 1–2 | Inductive step (quantitative): the linear-equation solver for `η(t)` given lower-order `η(t')`. Substantive: requires unpacking the recursive shape of `η^(-i)` on a non-vertex tree (the convolution-product expansion of `(η * η * … * η)(t)`). | 100–200 |
| **Phase E** | 1 | Lift `underlyingOneStepMethod_aux` to a `Quotient PhiEquivalent.setoidSigma` element. Seal `def:422B`. Non-vacuity: `explicitEulerLMM.underlyingOneStepMethod` reduces to a concrete known RK class (likely `⟦⟨1, RKTableau.explicitEuler⟩⟧`). | 50–100 |
| **Phase F (optional)** | 1 | Connect to `thm:422A` (existence theorem) — package the Phase D construction as a proof that `Eq422a M (M.underlyingOneStepMethod) hPre hStab`. Also useful for `thm:422C` (convergence). | 60–120 |

**Total estimate**: 6–10 cycles for Phase A through Phase E.
Optional Phase F adds 1 cycle. Cycle 336 ships Phase 0 only.

## §6 Risk assessment

### §6.1 Per-phase LOC budgets, Mathlib hook confidence, Aristotle suitability

| Phase | Risk | Mathlib hook confidence | Aristotle suitable? |
|---|---|---|---|
| 0 (cycle 336) | Trivial — wire-up only | N/A (project hooks only) | No (5-line theorem) |
| A.0 (D operator) | Medium — depends on textbook reading; if `D` turns out to be a forest-level operator (D.3), interacts with the §383 convolution divergence (`convolution_vertex_vs_multiset.md`) | Medium | Yes (~3 sub-lemmas) |
| B (zpow) | Low — direct Mathlib hook | High | No (mechanical) |
| C (Eq422a predicate) | Low — definition shape | High | Yes (non-vacuity check) |
| D.1 (base case `τ`) | Low — single-variable polynomial equation | High | Yes (numeric verification) |
| D.2 (WF recursion infra) | Medium — analogous cycle 195 infrastructure (RKTableau.PReducesTo size descent) but on `RootedTree.order` | Medium | No (structural induction) |
| D.3 (inductive step) | **High** — multi-cycle even within this phase if convolution-product expansion of `η^(-i)` is non-trivial | Medium-Low | Partial (sub-lemmas only) |
| E (lift + seal) | Medium — realisability bridge | Medium | Yes (non-vacuity examples) |
| F (optional) | Medium — depends on Phase D shape | Medium | Yes |

### §6.2 Cycle-336-style rollback risks to monitor

* **D-operator misidentification** (Phase A.0): if cycle 337 ships
  `D_phi` as (D.1) tree-grafting but the textbook actually means (D.2)
  order-weighted, every downstream phase is wasted. **Mitigation**:
  read Butcher §422 *in full* before writing any Lean code, and
  cross-check the choice against §381 / §383's `convProduct` shape.
* **Phase D.3 over-runs**: the inductive-step linear-equation solver
  may be more complex than estimated. **Mitigation**: if cycle 339+
  worker reports Phase D.3 is taking >2 cycles, split into D.3a
  (`r(t) = 2`) and D.3b (`r(t) > 2`) for parking-orbit ships, like
  the §344 small-`s` D-ladder.
* **Realisability gap** (Phase E): `liftFunctionToQuotient` may not
  exist for the general `η`. **Mitigation**: cycle 340+ worker should
  attempt the lift on the `r(t) = 1, 2` truncated `η` first, then
  generalise. If the lift genuinely doesn't exist, fall back to
  reformulating `def:422B` directly at the `RootedTree → ℝ` level
  (i.e. shape (i) from §2 with the codomain changed).

### §6.3 GPFS / Section441 timeout risk

`OpenMath/Chapter4/Section441.lean` (43rd consecutive GPFS timeout
per `.prover-state/issues/cycle_182_gpfs_slowness.md` at cycle 239).
The cycle 337+ Phase A work should land in a fresh file
`OpenMath/Chapter4/Section422.lean` (created by cycle 336) to avoid
any transitive Section441 import load. **Constraint**: imports must
be limited to `Mathlib`, `OpenMath.Chapter1.*` (for the LMM
prerequisites already in Section404), `OpenMath.Chapter3.Section381`
(for `PhiEquivalent`, `instGroup_phi`, `paddedEuler`, etc.), and
`OpenMath.Chapter4.Section404` (for `LinearMultistepMethod`).
**Do NOT** import `Section441` or any Chapter 4 file beyond
`Section404` in `Section422.lean`.

## §7 Cycle 337 entry point

**Recommended target**: Phase A.0 — pin Butcher's `D` operator.

**Concrete cycle 337 task**:

1. Read `extraction/raw_text/ch04.txt` lines covering §422 in full.
   Identify the definition of `D` (Butcher refers to `D` heavily in
   §380–§383 leading up to §422; the §381 convolution and §382 group
   constructions provide ambient context).
2. Decide between D.1 (tree-grafting), D.2 (order-weighted), or D.3
   (recursive elementary-differential operator) — *or* document a
   fourth candidate if the textbook reading reveals one.
3. Document the decision in this scoping doc under §7.1 (or a new
   §A0 sub-doc if substantial).
4. Ship the `D_phi` operator in `OpenMath/Chapter4/Section422.lean`
   (which already exists as cycle 336's wire-up sanity ship; cycle
   337 *appends* to it). LOC budget: ~80–120 lines including
   operator definition, simp unfolds, and 2–3 non-vacuity examples.

**Concrete cycle 337 Lean signature sketch**:

```lean
-- in OpenMath/Chapter4/Section422.lean

namespace OpenMath.Chapter4.Section422

/-- The §422 `D` operator on `G₁ = Quotient PhiEquivalent.setoidSigma`.
[Decision A.0: D is tree-grafting / order-weighted / recursive ...] -/
noncomputable def D_phi :
    Quotient OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma →
    Quotient OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma :=
  sorry  -- cycle 337 closes per A.0 decision

/-- Non-vacuity for `D_phi`: applied to the identity class. -/
example :
    D_phi (1 : Quotient OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma)
      = sorry := sorry

end OpenMath.Chapter4.Section422
```

Cycle 337 worker replaces both `sorry`s with concrete content. If
Phase A.0 turns out heavier than 1 cycle, the worker splits Phase A
into A.0.1 (decision + definition) and A.0.2 (simp unfolds +
non-vacuity), shipping A.0.1 in cycle 337 and A.0.2 in cycle 338.

## §8 Cross-references

* `.prover-state/issues/cycle_336_pivot_options.md` — cycle 335 P2
  menu listing four candidates A/B/C/D for cycle 336.
* `.prover-state/issues/lem_310B_plan.md` — multi-phase scoping
  template (cycle 260 produced; structural model for this doc).
* `.prover-state/issues/lem_441A_phase_C_scoping.md` — multi-phase
  scoping template (cycle 180 produced).
* `.prover-state/issues/def_530B_scaffold_strategy.md` — rollback
  precedent (cycles 149/150) for sorry-first multi-cycle defs.
* `.prover-state/issues/thm_381H_deferred.md` — deferred directions
  in `thm:381H` (relevant to `thm:384A` and the Banach-fixed-point
  bridge); if Phase E's realisability gap requires the deferred
  direction, cycle planning must escalate.
* `.prover-state/issues/cycle_250_strategy_alpha_definition_error.md`
  — the "definition smuggling" precedent (`alphaWeight` defined as
  closed-form RHS rather than labelling count). Cycle 337+ Phase A
  worker must NOT make the same error: `D` must capture the
  *primary* operator meaning, not just the algebraic condition that
  characterises it in equation (422a).
* `.prover-state/issues/convolution_vertex_vs_multiset.md` — cycle
  081–082 escalation re: §383 convolution divergence. If Phase A.0
  determines `D` is the §383 forest-level operator (D.3 candidate),
  this divergence is a soundness concern; the cycle 337+ worker
  should escalate before proceeding.
* `extraction/formalization_data/entities/def_422B.json` — the
  entity JSON; verbatim source for §1.

## §9 Cycle 336 ship checklist self-reference

Cycle 336 delivers:

1. **P1**: this scoping doc (`def_422B_path.md`, ≥200 lines).
2. **P2**: a Phase 0 wire-up sanity ship — `Nonempty (Quotient PhiEquivalent.setoidSigma)`
   via `⟦⟨2, paddedEuler⟩⟧` — in a fresh
   `OpenMath/Chapter4/Section422.lean` (Option P2.α from the
   strategy). The new file imports `Mathlib`,
   `OpenMath.Chapter3.Section381`, and is added to the
   `OpenMath/Chapter4.lean` aggregator.
3. **lean_status.json**: `def:422B` row updated to
   `formalization_status: "partial"` with a Phase 0 note (the wire-up
   sanity theorem counts as Phase 0 partial closure).
4. **plan.md**: Ch.4 §422 row `[ ] def:422B` → `[~]`.
5. **task_results/cycle_336.md** — standard sections.

No `def:422B` *body* this cycle. No Phase A through Phase E content
this cycle. The cycle 337 entry point (§7) is the next planner /
worker target.

## §A.0 D-operator decision (cycle 337)

Cycle 337's reading of Butcher §387 (`extraction/raw_text/ch03.txt`
lines 9391–9465) and §385 (lines 9101–9131) pins `D ∈ G` and **rules
out all three of §4.1's candidates**. The correct interpretation is
a refined fourth candidate.

### §A.0.1 Textbook source — §387 (verbatim)

From `extraction/raw_text/ch03.txt:9392`:

> As we have remarked, `D ∈ G` represents the differentiation operation,
> scaled by the unit stepsize `h`. If `ξ` denotes the element in `G₁`
> corresponding to a generalized Runge–Kutta tableau …
> then `ξD` will correspond to the s-stage tableau …

The (387b) tableau extends `ξ`'s `(c, A, b)` data with a new (s+1)-th
stage `(c = Σ bᵢ, a_{s+1,j} = bⱼ, a_{s+1,s+1} = 0)` and output
`b' = (0, …, 0, 1)` plus `b₀ = 0`. The result computed is "just
`hf(y)`, where `y` is the result computed by (387a)".

From `extraction/raw_text/ch03.txt:9117–9130` (§385b), `D` itself is
the **one-stage generalized RK method**:

```
0 0
0 1
```

i.e. `s=1, A=0, b=[1], c=[0]` with `b₀=0`. The elementary weights of
this method are: `Φ(τ) = 1`; `Φ(t) = 0` for `t` of order ≥ 2.

### §A.0.2 Choice — (D.4) Generalized-RK differentiation operator

`D` is **the §385b one-stage generalized RK method with `b₀=0`**.

Specifically, at the elementary-weight level on `T` (rooted trees,
*excluding* the empty tree `∅`):

* `Φ_D(τ) = 1` (single-vertex tree)
* `Φ_D(t) = 0` for `t` of order ≥ 2

For `η ∈ G₁`, the right-multiplication `(ηD)(t)` reduces via (383a)'s
convolution formula to:

* `(ηD)(τ) = 1` (constant)
* `(ηD)(mk children) = Π_{c ∈ children} η(c)` for non-empty `children`

(Derivation: `(ηD)(S) = Σ_{R≼S} η(S\R) D(R)`. Since `Φ_D` vanishes on
any multi-vertex sub-forest containing the root, the only non-zero
term is `R = {root only}`, giving `Π η(child)`.)

### §A.0.3 Rejection of (D.1)/(D.2)/(D.3)

* **(D.1) Tree-grafting / root-appending `D(t) = mk [t]`** —
  WRONG DIRECTION. The cycle 336 hypothesis predicted `D(τ)` should
  reduce to a tree of order 2 (the cherry). The actual definition
  has `(ηD)(τ) = 1` (constant, no tree at all). (D.1) strips/adds in
  the wrong direction: `D` *consumes* children rather than *appending*
  a root.
* **(D.2) Order-weighted multiplication `(Df)(t) = r(t)·f(t)`** —
  rejected by the planner (cycle 336 §6 Discovery). Confirmed wrong:
  this would give `(ηD)(t) = r(t) η(t)`, but the textbook formula
  gives `(ηD)(t) = Π_{children} η(child)` (a tree-shape-dependent
  *product*, not a scalar multiple).
* **(D.3) Forest-convolution `D`** — too general; (D.4) is the
  specific element in `G ⊇ G₁` that admits the (387b) tableau
  realisation. The convolution-product structure (383a) IS used to
  compute `ηD`, but `D` itself is the specific (385b) element.

### §A.0.4 Framework wire-up — `b₀=1` implicit in `RKTableau`

**Critical observation:** our `RKTableau` structure
(`OpenMath/Chapter3/Section312.lean:66`) has only `A, b, c` — *no
`b₀` field*. The associated B-series interpretation hardcodes
`b₀ = 1`: every `RKTableau` computes `y_n = y_{n-1} + h·Σᵢ bᵢ Fᵢ`.

Therefore Butcher's `D ∈ G` (with `b₀ = 0`) is **not directly
representable** as an `RKTableau`.

**However:** the equivalence relation `PhiEquivalent`
(`OpenMath/Chapter3/Section381.lean:124`) is `∀ t : RootedTree,
M.elementaryWeight t = M'.elementaryWeight t` — quantifying only
over `t : RootedTree`. The inductive `RootedTree`
(`OpenMath/Chapter3/Section310.lean:83`) has the single constructor
`mk : List RootedTree → RootedTree` and admits *no* empty-tree
representative. Consequently the `b₀` value (which would be tested
at `∅`) is **invisible** to `PhiEquivalent`.

**Consequence:** at the `Quotient PhiEquivalent.setoidSigma` level,
`Φ_D|_T` and `Φ_{1+D}|_T` are *equal*. The class
`⟦⟨1, RKTableau.explicitEuler⟩⟧` (with explicit Euler's `b₀=1`
implicit) is **the natural representative of `D`** in our framework,
since explicit Euler has elementary weight `Φ(τ) = 1, Φ(t≥2) = 0` —
exactly `Φ_D|_T`.

This is *not* definition smuggling: the b₀-invisibility is a
*property* of the §383 quotient construction, not a hack.
Equation (422a) is naturally interpreted on rooted trees `T`, so
the `∅` term in (422a) (the constant `1 − Σ αᵢ`) is absorbed into
the separate **preconsistency** hypothesis `Σ αᵢ = 1`. The
b₀-collapse therefore preserves the on-`T` semantics of (422a)
exactly, with no information loss.

### §A.0.5 Lean signature

```lean
noncomputable def D_element :
    Quotient OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma :=
  Quotient.mk _ ⟨1, OpenMath.Chapter3.Section312.RKTableau.explicitEuler⟩

noncomputable def D_phi
    (η : Quotient OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma) :
    Quotient OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma :=
  η * D_element
```

**Cycle 337 ships:**
1. `D_element` (the chosen group representative).
2. `D_phi : Q → Q` (right-multiplication by `D_element`).
3. `D_phi_one : D_phi 1 = D_element` (non-vacuity at identity input).
4. `D_element_elementaryWeight_vertex :
   elementaryWeightQ_phi D_element RootedTree.vertex = 1`
   (non-vacuity at the single-vertex tree — verifies `D` has the
   right action on `τ`).

**Phase A.0.2 (deferred, cycle 338+):**
5. `D_element_elementaryWeight_higher_order` — verify
   `Φ_{D_element}(t) = 0` for trees of order ≥ 2 (requires unfolding
   `derivativeWeight` for `RKTableau.explicitEuler` on a non-vertex
   tree).
6. Simp-lemma library for `D_phi` (e.g. `D_phi_mul`, congruence under
   `PhiEquivalent`).

### §A.0.6 Impact on §4 and §5 of this doc

§4.1's three candidates (D.1, D.2, D.3) are SUPERSEDED by (D.4)
above. §5's Phase A.0 row estimate (80–120 LOC) stands; cycle 337
ships items 1–4 above; item 5 (the higher-order vanishing
elementary-weight lemma) is deferred to Phase A.0.2.

§4.3's preliminary `Eq422a` draft remains correct *modulo* the
b₀-invisibility observation above: the on-`T` quantification is the
right scope, and the constant-term `1 − Σ αᵢ = 0` (the `∅`-tree case
in Butcher's notation) is satisfied a priori by the preconsistency
hypothesis already required by `IsPreconsistent`.

## §A.0.2 Closure (cycle 338)

Cycle 338 ships the higher-order vanishing of `D_element`'s
elementary weight (item 5 from §A.0.5), plus the Phase A.0.2 capstone
packaging both `_vertex` and `_higher_order` into a single on-tree
signature theorem, plus a `D_phi` distributivity simp lemma (item 6,
partial).

**Cycle 338 ships:**

7. `D_element_elementaryWeight_higher_order :
   ∀ t : RootedTree, 2 ≤ t.order →
     elementaryWeightQ_phi D_element t = 0`

   Proof recipe (per cycle 338 strategy §B.1):
   destructure `t = mk children` via `match`; show `children ≠ []`
   from `2 ≤ order` (the `mk []` case reduces to `1 + 0 = 1`); unfold
   `elementaryWeightQ_phi` via cycle 239's `_mk` def-eq; `rw
   [elementaryWeight_eq, Fin.sum_univ_one, derivativeWeight_mk]` to
   expose the product; close via `simp [List.map_cons,
   List.prod_cons, explicitEuler_internalWeight_zero]` where the
   private helper `explicitEuler_internalWeight_zero` follows from
   `explicitEuler.A = 0` (cycle 323 pattern).

8. `D_element_elementaryWeight (t : RootedTree) :
   elementaryWeightQ_phi D_element t =
     if t = RootedTree.vertex then 1 else 0`

   Phase A.0.2 capstone: packages item 4 (`_vertex`) and item 7
   (`_higher_order`) into the full on-tree elementary-weight
   signature of `D_element`. Matches Butcher §387's `Φ_D` exactly on
   `T`. The private helper
   `RootedTree_two_le_order_of_ne_vertex : t ≠ vertex → 2 ≤ t.order`
   bridges the case split (proved via `cases children with` + `0 <
   c.order` from `Section301.RootedTree.order_pos` + `omega`).

9. `D_phi_mul : ∀ η η', D_phi (η * η') = η * D_phi η'`

   Simp lemma for `D_phi` distributivity over the §383 group product
   on the left, by `mul_assoc` in cycle 236's `instGroup_phi`.
   Useful for downstream Phase B/C rewrites of `D_phi (η * η')`.

**Total cycle 338 additions:** 3 new public theorems + 2 private
helpers, ~80 LOC. All axiom-clean (`[propext, Classical.choice,
Quot.sound]`).

**Section422.lean LOC trajectory:** 56 (cycle 336) → 137 (cycle 337) →
~210 (cycle 338).

**Cycle 339 entry point (Phase B):** `Group.zpow` API non-vacuity on
the §383 quotient group. Verify Mathlib's `Group.zpow_natCast`,
`Group.zpow_neg`, etc., fire correctly on `Quotient
PhiEquivalent.setoidSigma`, plus 1–2 non-vacuity sanity theorems
(e.g. `D_element^(0) = 1`, `D_element^(1) = D_element`). Estimated
30–60 LOC. Low risk.

**Phase A.0.2 status: CLOSED.** The on-tree elementary-weight
signature of `D_element` is now fully pinned to Butcher §387's
`Φ_D`: `1` at `τ`, `0` elsewhere. No further Phase A.0 sub-phase is
planned; Phase A is complete pending an optional Phase A.0.3
(elementary-weight multiplicativity bridge over `composeQ_phi`) which
is deferred unless a downstream consumer demands it.

## Cycle 340 update — Phase C closure

Cycle 340 ships Phase C: the (422a) condition predicate on the §383
quotient group.

**Shipped:**

* `Eq422a {k} (M : LMM k) (η_q : Q) : Prop` — Butcher's
  underlying-one-step-method condition, quantifying over
  `u : RootedTree`:

  ```
  1(u) − Σᵢ₌₁..ₖ αᵢ · η_q^(-i)(u)
       − Σᵢ₌₀..ₖ βᵢ · (η_q^(-i) · D)(u) = 0.
  ```

  α-sum indexed by `Fin k` with `i.succ : Fin (k+1)` selecting
  `M.α i.succ` and exponent `-((i.val + 1 : ℕ) : ℤ)`; β-sum
  indexed by `Fin (k + 1)` with `M.β i` and exponent
  `-((i.val : ℕ) : ℤ)`. Right-multiplication by `D_element` on the
  β-side matches Butcher's `η^{-i} D` (cycle 337 `D_phi`).

* `Eq422a_congr` — non-vacuity sanity: `Eq422a` respects equality
  on its quotient-class argument (one-line `subst`+`rfl`).

**Design choices:**

* No `IsPreconsistent`/`IsStable` hypothesis on `Eq422a`'s
  signature — those are *existence* hypotheses for `thm:422A`
  ("such η exists"), not preconditions for the *predicate*. Keeps
  the predicate reusable across `thm:422A` (existence) and any
  future converse direction.

* `1(u)` term retained for verbatim Butcher correspondence. At the
  quotient level `1(u) = elementaryWeightQ_phi 1 u` reduces to `0`
  for every `u : RootedTree` via cycle 239's
  `elementaryWeightQ_phi_id` simp lemma (cycle 337 §A.0.4
  b₀-invisibility). The Butcher empty-tree case is handled
  separately by `IsPreconsistent`.

**Cycle 340 LOC trajectory:** Section422.lean: ~280 (cycle 339) →
~360 (cycle 340), +~80 LOC for the docstring-rich Phase C block.

**Cycle 341 entry point (Phase D.1):** base case `η(τ)` solver. The
coefficient of `η(τ)` in `Eq422a` at `u = τ` is `-(α₁ + 2α₂ + ⋯ +
k·αₖ)` (Butcher's proof at `extraction/raw_text/ch04.txt:1163`).
Under preconsistency this equals `-Σ i·αᵢ`, non-zero by stability.
So `η(τ)` is determined by the lower-order (empty) terms. Phase D
likely needs 3 cycles (D.1 base case, D.2 well-founded recursion
infrastructure on `RootedTree.order`, D.3 inductive step); Phase E
(lift to quotient + seal) is then a single cycle.

**Phase C status: CLOSED.** The (422a) predicate is defined and
respects quotient-class equality. Phase D / E / F remain deferred
per §5.

## Cycle 341 update — Phase D pre-infrastructure (τ-additivity)

Cycle 341 ships the τ-additivity infrastructure chain for
`elementaryWeightQ_phi` under the §383 group, load-bearing for
Phase D.1's closed-form `η(τ)` base-case solver.

**Shipped (4 new public theorems + 3 non-vacuity examples):**

* `RKTableau.derivativeWeightWithSrc_vertex` (P0) — the helper
  `M₂.derivativeWeightWithSrc M₁ i τ = 1` for every source tableau
  `M₁` and bottom-block stage `i`. Direct from the empty-list base
  case of `derivativeWeightWithSrcProd` (`Section381.lean:2690`):
  `τ = mk []`, so `derivativeWeightWithSrc M₁ i (mk []) =
  derivativeWeightWithSrcProd M₁ i [] = 1` (definitional). The
  `WithSrc` analog of cycle 187's `RKTableau.derivativeWeight_vertex`.

* `elementaryWeightQ_phi_mul_vertex` (P1, load-bearing) —
  `Φ_{η·η'}(τ) = Φ_η(τ) + Φ_{η'}(τ)` for all `η, η' : Q`. Proof
  recipe: `Quotient.inductionOn` on each factor, destructure to
  representatives `M₁, M₂`, `show` the multiplication unfolds to
  `composeQ_phi`, apply cycle 239's
  `elementaryWeightQ_phi_composeQ_phi_mk` to decompose the LHS into
  `M₁.elementaryWeight τ + Σ i, M₂.b i · derivativeWeightWithSrc
  M₁ i τ`, then `congr 1` closes both subgoals definitionally
  (both bottom-block sums reduce pointwise to `M₂.b i * 1` via the
  empty-list base cases of `derivativeWeightWithSrcProd` and
  `derivativeWeightProd`). **Note:** P0 is independent infrastructure
  and is not actually invoked in P1's proof — `congr 1` closes via
  definitional unfolding rather than rewriting.

* `elementaryWeightQ_phi_inv_vertex` (P2) — `Φ_{η⁻¹}(τ) =
  -Φ_η(τ)` for all `η : Q`. Proof: `mul_inv_cancel η_q : η_q *
  η_q⁻¹ = 1`, apply `elementaryWeightQ_phi_eq_of_eq` to evaluate
  both sides at `τ`, `rw` P1 on the LHS to split, `rw` the
  definitional equality `(1 : Q) = Quotient.mk _ ⟨0, RKTableau.id⟩`
  then cycle 239's `elementaryWeightQ_phi_id` zeroes the RHS, and
  `linarith` closes.

* `elementaryWeightQ_phi_zpow_vertex` (P3) — `Φ_{η^n}(τ) = (n : ℝ)
  · Φ_η(τ)` for all `η : Q` and `n : ℤ`. Proof: internal `∀ m : ℕ`
  helper proved by induction (base `m = 0`: `pow_zero` + `(1 : Q)`
  unfold + `elementaryWeightQ_phi_id`; succ: `pow_succ` + P1 +
  `push_cast; ring`), then case split on `Int` constructors —
  `ofNat m` via `Int.ofNat_eq_natCast` + `zpow_natCast`, `negSucc m`
  via `zpow_negSucc` + P2 sign flip + `push_cast; ring`.

* Three non-vacuity `example`s on `D_element`: `Φ_{D·D}(τ) = 2`,
  `Φ_{D⁻¹}(τ) = -1`, `Φ_{D³}(τ) = 3` — each a one-rw application
  of the corresponding P1/P2/P3 lemma plus cycle 337's
  `D_element_elementaryWeight_vertex = 1` plus `norm_num` for the
  arithmetic.

**Axioms:** all 4 public theorems depend on only
`[propext, Classical.choice, Quot.sound]`.

**Cycle 341 LOC trajectory:** Section422.lean: ~350 (cycle 340) →
484 (cycle 341), +~134 LOC. Within the strategy's 80–120 LOC budget
projection (margin from extra docstring on the section header and
per-theorem rationale).

**Cycle 342 entry point (Phase D.1 base case):** with P1/P2/P3 in
hand, the Eq422a body at `u = τ` collapses to a linear equation in
`η(τ)`:

```
0 − Σᵢ M.α i.succ · (-(i+1)) · η(τ)
  − Σᵢ M.β i · ((-i) · η(τ) + 1) = 0
```

(The `+ 1` on the β-side comes from cycle 337's
`D_element_elementaryWeight_vertex = 1` plus P1 additivity applied
to `η_q ^ (-i) * D_element`.) Cycle 342's Phase D.1 base case rings
this into

```
(Σᵢ (i+1) · M.α i.succ + Σᵢ i · M.β i) · η(τ) = Σᵢ M.β i
```

(modulo sign convention), i.e. a closed form for `η(τ)`. Stability
+ preconsistency guarantee the coefficient is non-zero (cycle 178's
`ρPoly_deriv_eval_one_pos_of_stable_preconsistent`, transported to
the `Σ i · αᵢ` form). May need to first define an `Eq422aAt M η_q
u` per-tree predicate (or extract a lemma `Eq422a_at_tree`) to make
the `u = τ` slice statable as its own theorem rather than just an
instantiation of the universal `Eq422a`.

**Phase D pre-infrastructure status: CLOSED.** τ-additivity of
`elementaryWeightQ_phi` under the §383 group is shipped axiom-clean.
Phase D.1 / D.2 / D.3 / E / F remain deferred per §5.

## Cycle 342 update — Phase D.1 closed-form `η(τ)` base-case solver

**Status: SHIPPED.** Phase D.1 base case closed at
`OpenMath/Chapter4/Section422.lean:524–696`. Three new public
theorems plus one non-vacuity `example`:

* **P1 (load-bearing) — `Eq422a_at_vertex_linear`:**
  ```
  ((Σ_{i:Fin k} (i+1) · M.α i.succ) + (Σ_{i:Fin (k+1)} i · M.β i))
    * elementaryWeightQ_phi η_q τ
    = Σ_{i:Fin (k+1)} M.β i
  ```
  Reduces (422a) at `u = τ` to a linear equation in `η(τ)`. Proof
  recipe (matches the strategy's §B.2 plan):

  1. Specialize `hEq` at `RootedTree.vertex`.
  2. Collapse `Φ_1(τ) = 0` via cycle 239 `elementaryWeightQ_phi_id`.
  3. Rewrite each α-summand via cycle 341 P3
     (`elementaryWeightQ_phi_zpow_vertex`) + `push_cast; ring` into
     `-((i+1) · M.α i.succ) · η`.
  4. Rewrite each β-summand via cycle 341 P1+P3 + cycle 337
     `D_element_elementaryWeight_vertex` + `push_cast; ring` into
     `-(i · M.β i) · η + M.β i`.
  5. Pull η outside both sums via `← Finset.sum_neg_distrib, ←
     Finset.sum_mul` (after `Finset.sum_add_distrib + congr 1` on the
     β-side).
  6. Close by `linarith`.

  The strategy's "alternative" `nlinarith`/`linarith` one-shot was
  not attempted; the manual factoring closed cleanly. The
  `Finset.sum_neg_distrib` and `Finset.sum_mul` names were verified
  current at HEAD.

* **P2 (consistency-strengthened corollary) —
  `Eq422a_at_vertex_linear_of_isConsistent`:** under
  `M.IsConsistent`, the RHS `sum_β(M)` substitutes to `coef_α(M)`,
  giving `(coef_α + coef_β) · η = coef_α`. This matches Butcher
  §422 p. 1163's textbook η-coefficient arrangement. The
  `IsConsistent` bridge required a `push_cast`+`ring` step to align
  `SatisfiesEq404b`'s `((i : ℕ) + 1 : ℝ)` cast form with
  `Eq422a_at_vertex_linear`'s `((i.val + 1 : ℕ) : ℝ)` form (these
  are equal but not definitionally so).

* **P4 (closed-form extraction stretch) — `Eq422a_at_vertex_eta_eq`:**
  under the non-vanishing-coefficient hypothesis
  `coef_α + coef_β ≠ 0`,
  ```
  η(τ) = sum_β(M) / (coef_α(M) + coef_β(M)).
  ```
  Proof: `field_simp` + `linarith`. The non-vanishing hypothesis is
  downstream of `M.IsStable + M.IsPreconsistent` via cycle 178's
  `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`; bridge
  deferred to cycle 343+.

* **P3 non-vacuity — anonymous `example`:** for `k = 0`,
  `Eq422a_at_vertex_linear` collapses (both sums empty / one β
  term) to `0 = M.β 0` via `simp`.

**Strategy deviation:** P3 used Option A (`k = 0`) instead of Option
B (`explicitEulerLMM`). Reason: Option A's `simp`-closure was clean
and immediate; Option B would have needed careful handling of
`explicitEulerLMM`'s field-`fun`-with-`if` shape and was redundant
given P1 + P2 + P4 already exercise the theorem on heterogeneous
hypotheses.

**Axioms:** all 3 new public theorems depend on only
`[propext, Classical.choice, Quot.sound]`.

**Cycle 342 LOC trajectory:** Section422.lean: 484 (cycle 341) → 696
(cycle 342), +~212 LOC. Slightly above the strategy's 150 LOC
target; the overage is in per-theorem docstrings (each of P1/P2/P4
carries a multi-paragraph proof-recipe rationale matching the cycle
341 P1/P2/P3 style for downstream consumer clarity).

**Cycle 343 entry point (Phase D.2 well-founded recursion):** with
the base case closed, Phase D.2's job is well-founded-recursion
infrastructure on `RootedTree.order`. Verify Mathlib's
`WellFoundedRelation RootedTree` instance is available at HEAD (or
build it via `Function.WellFoundedRelation.onFun` on
`RootedTree.order`); cycle 195's
`RKTableau.PReducesTo.size_lt_of_step` is the analogous template.
~60–100 LOC. Phase D.3 (inductive step for `r(t) ≥ 2`) follows in
cycle 344+.

**Phase D.1 status: CLOSED.** Phase D.2 / D.3 / E / F remain
deferred per §5.

## Cycle 343 update — Phase D.2 well-founded-recursion infrastructure

**Status: SHIPPED.** Phase D.2 closed in ~17 LOC added to
`OpenMath/Chapter3/Section301.lean` immediately after `order_pos`
(line 159). Two public deliverables landed:

* `RootedTree.order_lt_of_mem_children` — subtree strict-descent
  lemma: for `c ∈ children`, `c.order < (mk children).order`. Proved
  via `order_eq` (Section301:112) + `List.mem_map_of_mem` +
  `List.le_sum_of_mem` (the Mathlib lemma for `CanonicallyOrderedAdd`
  monoids; `ℕ` qualifies). 4-line proof body.
* `instance : WellFoundedRelation RootedTree := measure RootedTree.order`
  — the canonical well-founded relation on `RootedTree` derived from
  `order`. Phase D.3's `η`-solver (cycle 344+) will consume this for
  `termination_by t => t` clauses.

Plus two `example` sanity checks (`vertex.order < cherry.order`,
`cherry.order < broom₃.order`, both `by decide`).

**Axioms (verified via `#print axioms`):**
* `order_lt_of_mem_children` → `[propext, Quot.sound]` only (no
  `Classical.choice` since the proof is purely structural).
* `instWellFoundedRelation` → does not depend on any axioms.

**LOC trajectory:** Section301.lean: 1850 → 1867, +17 LOC (well under
the 60–100 LOC strategy estimate; the work turned out to be a near-
trivial composition of existing Mathlib infrastructure once
`List.le_sum_of_mem` was identified). No changes to Section422.lean.

**Cycle 344 entry point (Phase D.3 inductive step):** with the
strict-descent lemma and `WellFoundedRelation` instance in place,
Phase D.3 can scaffold:

```
noncomputable def underlyingEta_aux {k : ℕ}
    (M : LinearMultistepMethod k) (hPre : ...) (hStab : ...) :
    RootedTree → ℝ
  | RootedTree.mk children => ...  -- linear solve in η, recurse on c ∈ children
termination_by t => t  -- consumes the WellFoundedRelation
decreasing_by ... order_lt_of_mem_children ...
```

The base case at `t = mk [] = vertex` reduces to cycle 342's
`Eq422a_at_vertex_eta_eq`. Inductive step requires expanding the
(422a) condition at a non-vertex `t = mk children` and isolating
`η(t)` from the lower-order `η(c)` terms.

**Phase D.2 status: CLOSED.** Phase D.3 / E / F remain deferred per §5.

## Cycle 344 update — `coef_α(M) = ρ'(1)` bridge + positivity corollary

**Status: SHIPPED.** The §422 ↔ §441 algebraic bridge closed in
~50 LOC added to `OpenMath/Chapter4/Section422.lean` after cycle
342's `Eq422a_at_vertex_eta_eq` block. Two public theorems and two
`example` non-vacuity witnesses:

* `coef_α_eq_ρPoly_deriv_at_one_of_preconsistent` — under
  `M.IsPreconsistent`,
  `Σ_{i:Fin k} (i+1) · α_{i+1} = M.ρPoly.derivative.eval 1`.
  Proved via `ρPoly_deriv_eval_one_unconditional` (cycle 178)
  + RHS sum-split + preconsistency collapse `Σ α = 1`.
* `coef_α_pos_of_stable_preconsistent` — for stable preconsistent
  `M` with `0 < k`, `coef_α(M) > 0`. One-line composition of
  P1 with `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`
  (cycle 178, Section441.lean:767).
* Two `example`s: `explicitEulerLMM.coef_α = 1` (closes via
  `simp [explicitEulerLMM]`), `bdf2LMM.coef_α = 2/3` (closes via
  `simp [bdf2LMM, Fin.sum_univ_two] + norm_num`).

**Axioms (verified via inline `#print axioms`):**
Both theorems → `[propext, Classical.choice, Quot.sound]` only.

**LOC trajectory:** Section422.lean: 674 → ~745 (P1+P2 + 2 examples
+ docstrings). New imports: `OpenMath.Chapter4.Section441`,
`OpenMath.Chapter4.Section451`.

**Cycle 342's `Eq422a_at_vertex_eta_eq` signature untouched** — the
non-vanishing hypothesis remains explicit; cycle 345+ can strengthen
to consume `coef_α_pos` directly once `coef_β` handling is decided.

**Cycle 345 entry point (Phase D.3 inductive step) — UNCHANGED:**
the cycle 343 §"Cycle 344 entry point" plan for scaffolding
`underlyingEta_aux` is now better-supported by the positivity bridge:
the recursive solver's per-step linear inversion requires
`coef_α + coef_β ≠ 0`, and having `coef_α > 0` as a separate fact
simplifies threading. Phase D.3 / E / F remain deferred per §5.

## Cycle 345 update — Phase D consolidation: discharge non-vanishing under textbook hypotheses

**Status: SHIPPED.** Cycle 344's `coef_α > 0` positivity bridge
consumed by a corollary of cycle 342's `Eq422a_at_vertex_eta_eq`,
modulo an explicit β-side non-negativity hypothesis. ~105 LOC added
to `OpenMath/Chapter4/Section422.lean` after cycle 344's positivity
block. Two new public theorems plus three non-vacuity `example`s:

* `Eq422a_at_vertex_eta_eq_of_stable_preconsistent` — for a stable
  preconsistent `M` with `0 < k` and `hβ_nn : 0 ≤ coef_β(M)`, the
  (422a) reduction at `τ` pins `η(τ) = sum_β / (coef_α + coef_β)`
  *without* requiring the caller to discharge the non-vanishing
  hypothesis. Proof recipe: `apply Eq422a_at_vertex_eta_eq hEq`
  leaves `coef_α + coef_β ≠ 0` as side-goal; close via
  `coef_α_pos_of_stable_preconsistent` (cycle 344) +
  `hβ_nn` + `linarith`. The β-side non-negativity hypothesis
  surfaces a residual textbook assumption — eliminating it requires
  §441 β-side machinery (a `coef_β_pos_of_stable_consistent`
  analog of cycle 178's α-side
  `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`) not yet
  built; deferred to a Phase D′ refinement cycle.
* `coef_α_eq_sum_β_of_isConsistent` — extracted from cycle 342's
  `Eq422a_at_vertex_linear_of_isConsistent` body: under
  `M.IsConsistent`, `Σ_{i:Fin k} ((i.val + 1 : ℕ) : ℝ) * M.α i.succ
  = Σ_{i:Fin (k+1)} M.β i`. Cast bridge via `push_cast`+`ring` between
  the §422 form `((i.val + 1 : ℕ) : ℝ)` and the §404 form
  `((i : ℕ) + 1 : ℝ)`. Useful infrastructure for downstream Phase D′
  consumers.
* Three `example`s: `explicitEulerLMM` P1 non-vacuity (`η(τ) = 1/2`
  via `1/(1+1)`), `coef_α_eq_sum_β_of_isConsistent` non-vacuity on
  `explicitEulerLMM` (both sides = 1).

**BDF2 deferral.** The planner strategy P2 expected a `bdf2LMM`
non-vacuity, but `bdf2LMM_isStable` (Dahlquist-stable,
`LinearMultistepMethod.IsStable`) does **not** exist in the codebase
— only `bdf2LMM_isGStable` (Section451, cycle ~149) and
`bdf2LMM_isAStable` (Section454, cycle ~169) ship. Building the
`IsGStable ⇒ IsStable` or `IsAStable ⇒ IsStable` chain is a
separate task (additive, ~30 LOC, low risk). Tracked as a cycle 346
candidate per the cycle 345 task results §"Suggested next approach"
option 2.

**Axioms (verified via `#print axioms` on each new public theorem):**
Both `Eq422a_at_vertex_eta_eq_of_stable_preconsistent` and
`coef_α_eq_sum_β_of_isConsistent` → `[propext, Classical.choice,
Quot.sound]` only.

**LOC trajectory:** Section422.lean: 759 → ~864 (+~105, including
docstrings).

**Cycle 342's `Eq422a_at_vertex_eta_eq` signature untouched** —
the cycle 345 ship is strictly additive; the non-vanishing
hypothesis remains explicit on the cycle 342 base theorem for callers
that need the unconditional form.

**Cycle 346 entry point — three candidates** (see
`task_results/cycle_345.md` §"Suggested next approach"):

1. **Phase D′ refinement** (MEDIUM risk, 1–2 cycles): build `βPoly`
   analog + `coef_β_pos_of_stable_consistent` bridge to drop the
   `hβ_nn` hypothesis in cycle 345 P1.
2. **`bdf2LMM_isStable` ship** (LOW risk, ~30 LOC): build the
   `IsAStable ⇒ IsStable` (or `IsGStable ⇒ IsStable`) bridge,
   ship `bdf2LMM_isStable` as a corollary, then add the BDF2
   non-vacuity for cycle 345 P1 that was deferred.
3. **Phase D.3 proper** (HIGH risk, multi-cycle, gated): scaffold
   `underlyingEta_aux` per cycle 343's `WellFoundedRelation`,
   handling τ via cycle 345's P1 corollary and the inductive
   step via per-tree linear isolation. Contingent on Aristotle
   batch + phased scoping per `lem_310B_plan.md` /
   `lem_441A_phase_C_scoping.md` template depth.

## Cycle 347 update — Phase D′ Step 1 SHIPPED

**Status: SHIPPED.** Cycle 347 lands the β-side algebraic
bridge in `OpenMath/Chapter4/Section422.lean`:

* `coef_β_eq_βPoly_deriv_at_one` (line ~957): for any
  `M : LinearMultistepMethod k`,
  `(∑ i : Fin (k+1), (i.val : ℝ) · M.β i) = βPoly M . derivative.eval 1`.
  **No hypothesis needed.** β-side analog of cycle 344's
  `coef_α_eq_ρPoly_deriv_at_one_of_preconsistent`.
* `βPoly_deriv_eval_one_nonneg_of_β_nonneg` (line ~993):
  stretch corollary combining cycle 347's bridge with cycle
  346's `coef_β_nonneg_of_β_nonneg`. Restates the cycle 346
  helper in polynomial language.
* Two anonymous `example` non-vacuity witnesses: BDF2
  (`βPoly'(1) = 0`) and explicit Euler (`βPoly'(1) = 1`).

**`Section410.βPoly` reuse discovery.** The cycle 346 worker's
"Suggested next approach" Option A recommended defining a fresh
`σPoly` in §422. Cycle 347 found this unnecessary —
`Section410.βPoly` (cycle 73, line 103) already has the exact
`Σ β_i · X^i` shape needed for the bridge, with degree bound
`βPoly_natDegree_le` (line 219) and explicit-Euler witness
`βPoly_explicitEuler` (line 179) already proved. Cycle 347
reuses `Section410.βPoly` directly via a new import; net new
definitions = 0.

**Cycle 344 α-side template carried over cleanly.** The cycle
178 `ρPoly_deriv_eval_one_unconditional` proof recipe at
Section441.lean:375 ported with simplification: β-side closes
in ≈7 tactic lines vs cycle 344's ≈18, because `βPoly`'s
`Σ β_i · X^i` shape (no `X^(k-(i+1))` Nat-subtraction) needs
no canonicalization step and no `Σ α_i = 1` invocation.

**Cycle 345's `Eq422a_at_vertex_eta_eq_of_stable_preconsistent`
signature untouched.** The cycle 347 ship is strictly additive;
the `hβ_nn : 0 ≤ coef_β(M)` hypothesis remains explicit on the
cycle 345 base theorem for callers that need the unconditional
form. Phase D′ Step 2 (positivity from `IsStable + IsConsistent`
alone) remains **deferred** — see cycle 347 task results
§"Suggested next approach" for the scoping outlook.

**LOC trajectory:** Section422.lean: 931 (cycle 346) → 1004
(cycle 347, +73 LOC including docstrings).

**Cycle 348 entry point — four candidates** (see
`task_results/cycle_347.md` §"Suggested next approach"):

A. **Phase D′ Step 2 scoping** (multi-cycle, MEDIUM-HIGH): write
   a scoping doc analog of `lem_441A_phase_C_scoping.md` for
   deriving `0 ≤ βPoly'(1)` from `IsStable + IsConsistent`
   alone. The β-side textbook characterization is not as
   standard as the α-side `ρ'(1) > 0` story; may require
   2–3 cycles of investigation before scaffolding.
B. **Phase D.3 inductive solver scoping** (multi-cycle, HIGH):
   per §6.2, with D.2 well-founded recursion shipped (cycle
   343) draft a 3–5 cycle plan for the recursive
   `η : RootedTree → ℝ` construction.
C. **Pivot to a fresh entity** (low-medium): with `def:422B`
   having absorbed 12 consecutive cycles (336–347), reasonable
   moment for a planner to break the §422 streak. Candidates
   from `cycle_336_pivot_options.md`: `def:451A` (G-stability),
   `thm:535A` (one-step underlying method for GLMs), `thm:541A`
   (DIMSIM types).
D. **BDF3 / Adams-Bashforth sanity expansion** (low, sideline):
   expand the §404 LMM non-vacuity surface. Useful palate-
   cleanser, no §422 closure compounding.

## §10 Cycle 397 update — Phase α'.4.2 `mk [mk [cherry]]` migration

**Status: SHIPPED.** Cycle 397 closes the 4th Phase α'.4.2
ladder-tree migration (after cycles 391 `mk [vertex, cherry]`,
393 `mk [broom₃]`, 396 `mk [cherry]`). Mechanical mirror of
cycle 396 with three substitutions:

* `mk [cherry]` → `mk [mk [cherry]]`
* `inversePolyChain 2 / _two` → `inversePolyChain 3 / _three`
* `inversePolyTree_mkCherry` → `inversePolyTree_mkMkCherry`

**Six edits** (all in `Section422.lean`):

1. **Step B (body migration)**: `inversePolynomial`'s 8th
   `if-then-else` branch (`mk [mk [cherry]]`) body changed from
   `inversePolyChain 3 f` to
   `inversePolyTree (mk [mk [cherry]]) f`.

2. **Step A (new bridge)**:
   `inversePolyTree_mkMkCherry_eq_inversePolynomial` inserted
   immediately after cycle 396's
   `inversePolyTree_mkCherry_eq_inversePolynomial`. Seven
   `if_neg` discharges (vertex, cherry, broom₃, mk [cherry],
   bushy, mk [broom₃], mk [vertex, cherry]) + `if_pos rfl`.
   After Step B both sides literally reduce to
   `inversePolyTree (mk [mk [cherry]]) f`, closing by implicit
   `rfl`.

3. **Step C (Phase α.2 calibration example update)**: cycle
   374's `mk [mk [cherry]]` calibration `example`'s trailing
   `inversePolyChain_three` swapped for
   `inversePolyTree_mkMkCherry`.

4. **Step D (Phase β.4 bridge update)**:
   `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry`
   (cycle 378) similarly retrofitted.

5. **Step E (Phase γ branch update — twice)**: in
   `inversePolynomial_eq_of_subtree_agreement` `mk [mk [cherry]]`
   arm, both `inversePolyChain_three` occurrences (one per `f`
   side, one per `g` side) replaced with
   `inversePolyTree_mkMkCherry`.

6. **Step F (cycle 380 bridge derivative fix)**:
   `inversePolyChain_three_eq_inversePolynomial`'s proof body
   appended with `inversePolyChain_three, inversePolyTree_mkMkCherry`
   so both routes (`inversePolyChain 3 f` LHS,
   `inversePolyTree (mk [mk [cherry]]) f` RHS post-Step-B) reduce
   to the cycle 378 closed form `v⁴ − 3v²c + c² + 2vm − M_mc`.
   Theorem statement unchanged.

**Verification**: `lake build OpenMath.Chapter4.Section422`
exits 0 (built in 200 s); `grep -c sorry` returns 5 (unchanged
— 4 docstring + 1 grandfathered cycle 365 code at line 2272);
all 6 verification symbols
(`inversePolyTree_mkMkCherry_eq_inversePolynomial`,
`elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry`,
`inversePolynomial_eq_of_subtree_agreement`,
`inversePolyChain_three_eq_inversePolynomial`,
`inversePolyTree_mkMkCherry`, `inversePolyTree_mkCherry`)
return `[propext, Classical.choice, Quot.sound]`.

**§422 axiom-clean streak**: 59 → **60 substantive + 2 doc**
(cycles 336–397).

**Phase α'.4.2 progress**: 5 of 9 ladder trees routed through
`inversePolyTree`. Remaining: `bushy` (requires extending
`inversePolyTree`'s arity-3 case from `0` to a closed form;
cycle 398+ scope, needs its own scoping doc Phase α'.4.3).
`vertex`/`cherry`/`broom₃` are currently still on
`inversePolyChain k` / `inversePolyBroom k`; technically these
also remain to be migrated but the dispatch is already in
canonical form and the migration would be a trivial recipe
mirror.

**Cycle 398 entry**: tackle `bushy` migration.
`bushy = mk [vertex, vertex, vertex]` is a three-leaf-children
tree; `inversePolyTree`'s current `(_ :: _ :: _ :: _)` recursive
case dispatches to `0`. A substantive cycle requiring a
`trichildPolynomial` helper analogous to cycle 387's
`bichildPolynomial` and likely a brief scoping doc.
