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
