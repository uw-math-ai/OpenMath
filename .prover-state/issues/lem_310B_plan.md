# Issue: lem:310B multi-cycle infrastructure plan

## Status

Strategic scoping document for `lem:310B` (Butcher §310, p. 173,
"Elementary Differential Weight Formula"). No Lean code shipped in
this cycle (cycle 260). Cycle 261+ planners use this doc to break the
remaining work into single-cycle deliverables without re-scoping.

The cycle 200/201 rollback precedent (sorry-first scaffold for a
multi-cycle target without a credible single-cycle close) and the
cycle 138/139 rollback (sorry'd general-`n` `thm:550A`) both demand
that planners commit to a phase decomposition before workers write
Lean code. This file is that commitment for `lem:310B`.

## §1 Textbook statement (verbatim)

From `extraction/formalization_data/entities/lem_310B.json`:

> **Lemma 310B.** The value of (310i) is
>
>     ∑_{t ∈ T} (h^{r(t)} / σ(t)) · θ(t) · F(t)(y₀),
>
> where `θ` is defined by
>
>     θ(t) = 1                                  if t = τ,
>     θ(t) = ∏_{i=1}^{k} θ(t_i)                 if t = [t₁ t₂ ⋯ t_k].

Equation (310i) is the formal series being evaluated, from the
preceding §310 text (Butcher 3rd ed., p. 172):

> As part of the equipment we need to manipulate expressions
> involving elementary differentials we consider the value of
>
>     h · f(y₀ + Σ_{t ∈ T} θ(t) · (h^{r(t)} / σ(t)) · F(t)(y₀))      (310i)
>
> As a formal series, this can be evaluated using the following
> result: [Lemma 310B]

The proof (Butcher p. 173) is:

> Use Theorem 306A. The case `t = τ` is obvious. For
> `t = [t_1^{m_1} t_2^{m_2} ⋯ t_j^{m_j}]`, where `t_1, t_2, …, t_j`
> are distinct, the factor
>
>     σ(I) · (∏_{i=1}^{j} σ(t_i)^{m_i})^{-1},
>
> where `I` is the index set consisting of `m_1` copies of `1`, `m_2`
> copies of `2`, …, and `m_j` copies of `j`, is equal to `σ(t)^{-1}`.

The "Theorem 306A" reference is Butcher's multinomial Taylor theorem
(p. 170): for `f` analytic near `a`,

    f(a + δ₁ + δ₂ + … + δ_m) = ∑_{I ∈ I_m} (1/σ(I)) · f^{(#I)}(a) · δ^I,

where `I_m` is the set of all sequences from `{1, …, m}`, `σ(I) =
∏_i k_i!` is the multinomial symmetry factor, and `δ^I = (δ_{i_1}, …,
δ_{i_k})` is the tuple of operands. `thm:306A` is itself unformalised
(entry in `formalization_data/entities/thm_306A.json` has
`formalization_status: "unformalized"`); its formalisation is a
genuine prerequisite, not a citation to existing Mathlib content.

## §2 Distilled mathematical content (Lean-friendly restatement)

`lem:310B` asserts a *closed-form evaluation* of the right-hand side
of (310i):

    h · f(y₀ + Σ_{t ∈ T} θ(t) · (h^{r(t)} / σ(t)) · F(t)(y₀))
      = Σ_{t ∈ T} θ(t) · (h^{r(t)} / σ(t)) · F(t)(y₀).            (∗)

The two sides are both sums indexed by `t ∈ T`. The LHS arises by
applying Theorem 306A's multinomial expansion to `f` evaluated at
`y₀` plus a series of small perturbations indexed by trees; the RHS
is the same series with one extra layer of tree-attachment (the new
root carrying the leading `h · f(…)` term, which is exactly the new
root vertex of the augmented tree). After Theorem 306A expansion,
each term on the LHS corresponds to a labelled rooted tree (`def:300C`
labelling of `t`), and the bridge to the unlabelled-tree RHS uses the
orbit-stabilizer theorem applied to the symmetric-group action on
labellings: the labelling orbit of `t` has size `r(t)! / σ(t)`, and
collapsing labelled trees by this orbit equivalence introduces the
factor `σ(t)^{-1}` that Butcher's proof identifies.

Components our formalisation will need:

- **(2.1) Labelled rooted trees with quotient structure** — Butcher
  `def:300C` content (currently no Lean analogue). See §4.1.
- **(2.2) `θ`-rewriting bridge** — cycle 254's
  `bseriesTerm_eq_theta_smul_bseriesTerm` already provides the
  pointwise version; under `theta_eq_one` (cycle 249) the recursion
  collapses to `θ ≡ 1`, but the recursion *shape* is what
  participates in the §310 proof (it must be matched against
  Butcher's product over children before `theta_eq_one` collapses
  it).
- **(2.3) `α(t)` closed form (302a)** — cycle 250's `alphaWeight`,
  with `α(t) = r(t)! / (σ(t) · γ(t))`. The denominator `γ(t)`
  cancels against the orbit-count in the labelled-to-unlabelled
  reindexing.
- **(2.4) `thm:306A` Taylor / multinomial expansion** — currently
  unformalised. See §4.2.
- **(2.5) Orbit-counting bridge** — given the labelled-tree sum on
  the LHS of `(∗)`, the bridge collapses each labelled-tree orbit to
  the unlabelled tree with weight `r(t)! / σ(t)`. See §4.3.
- **(2.6) Multilinear connection to elementary differentials** — the
  textbook (310i) factors through `F(t)(y₀)` which is multilinear in
  `N`-spaces; cycles 248–259 only address scalar `ℝ → ℝ` instances.
  See §4.4.

## §3 Mathlib + project hooks already in place

All entries below were verified at HEAD (`d889695 Cycle 259 …`) by
reading `OpenMath/Chapter3/Section{301,310,311}.lean`.

### From `OpenMath/Chapter3/Section310.lean`

- `RootedTree` inductive datatype (line 83–84) — `List`-based
  representation, strict-positivity-compatible.
- `RootedTree.order` / `orderSum` (line 98–105) — vertex count
  recursion.
- `RootedTree.vertex` / `cherry` / `broom₃` (line 108, 111, 114) —
  small-tree canonical witnesses used downstream.
- `RootedTree.theta` / `thetaProd` (line 137–143) — exact-solution
  operator weight (recursive shape used by `lem:310B`'s RHS).
- `RootedTree.theta_eq_one` (line 154–165) — `θ ≡ 1` closure (cycle
  249).
- `elementaryDiff` (line 187–197) — Butcher `def:310A` recursion,
  polymorphic over `E : Type*` with `[NormedAddCommGroup E]`,
  `[NormedSpace ℝ E]`. Already lifted to the polymorphic setting
  `def:310A` requires.

### From `OpenMath/Chapter3/Section301.lean`

- `instance : DecidableEq RootedTree` (line 92, mutual recursion at
  73–90) — enables `Finset RootedTree` reasoning.
- `RootedTree.order_eq` (line 112–115) — order recursion in
  `List.sum` form.
- `RootedTree.density` / `densityProd` (line 134–139),
  `density_eq` (line 150–155), `density_pos` (line 168–179) —
  Butcher `γ(t)` and (301c).
- `RootedTree.symmetry` / `symmetryProd` (line 204–220),
  `σ_recursion` (line 240–241), `symmetry_pos` (line 247–263) —
  Butcher `σ(t)` and (301b) (stipulative definition; faithfulness
  gap in `.prover-state/issues/symmetry_group_equivalence.md`).
- `RootedTree.tau_values` (line 267–269) — `r(τ) = σ(τ) = γ(τ) = 1`.
- `RootedTree.alphaWeight` (line 305–306), `alphaWeight_vertex`
  (line 311–315), `alphaWeight_pos` (line 320–326) — Butcher `α(t)`
  via closed form (302a). Twelve α-witness `example`s for trees
  through `r = 5` in lines 328–518.
- `RootedTree.bseriesTerm` (line 548–551), `bseriesTerm_vertex`
  (line 559–566), `bseriesTerm_eq_theta_smul_bseriesTerm` (line
  581–585) — cycle 254 `θ`-rewriting scaffold (polymorphic `E`).
- `RootedTree.TruncatedRootedTree N` (line 620–621),
  `TruncatedRootedTree.order` (line 626–627),
  `TruncatedRootedTree.order_le` (line 629–630) — cycle 255 subtype
  scaffold.
- `RootedTree.bseriesPartialSum` (line 637–640),
  `bseriesPartialSum_empty` (line 643–647, `@[simp]`),
  `bseriesPartialSum_insert` (line 649–655) — cycle 255 partial-sum
  algebra.
- `RootedTree.exists_truncated_of_forall_order_le` (line 677–682) —
  cycle 255 Finset-to-subtype bridge.
- `RootedTree.bseriesAlphaTerm` (line 700–703),
  `bseriesAlphaTerm_vertex` (line 708–714) — cycle 256 α-weighted
  per-tree summand.
- `RootedTree.bseriesAlphaPartialSum` (line 720–723),
  `bseriesAlphaPartialSum_empty` (line 726–730, `@[simp]`),
  `bseriesAlphaPartialSum_insert` (line 732–738) — cycle 256
  α-weighted partial-sum algebra.

### From `OpenMath/Chapter3/Section311.lean`

- `F_tau_eval` (line 72–77) — base case of `def:310A`:
  `F(τ)(y₀) = f(y₀)` for polymorphic `N`-space target.
- `bseriesOrderOne` (cycle 248) and the chain
  `lem_311A_order_one` … `lem_311A_order_five` (cycles 248, 256,
  257, 258, 259) — scalar `ℝ → ℝ` Taylor specialisations through
  order 5. Each ships an `iteratedDeriv_*_via_ode` private helper
  for the Faà-di-Bruno chain rule.

### Mathlib hooks (verified via `lean_local_search` / Mathlib reads)

- `Finset.sum_insert`, `Finset.sum_singleton`, `Finset.sum_union`,
  `Finset.sum_image`, `Finset.sum_congr` — used pervasively in cycle
  254/255/256 partial-sum reasoning.
- `iteratedFDeriv ℝ k f y` (`Mathlib.Analysis.Calculus.IteratedDeriv.Defs`)
  — multilinear derivative used by `elementaryDiff`.
- `taylor_isLittleO` (`Mathlib.Analysis.Calculus.Taylor`) — Peano
  remainder form, consumed by `lem_311A_order_*` (cycles 248–259).
- `Asymptotics.IsBigO` / `IsLittleO` — used at every `O(h^k)` step.
- `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` (verify) —
  the orbit-stabilizer theorem; Mathlib has this for group actions,
  but the precise name and namespace may have drifted in recent
  Mathlib. Cycle 261+ Phase C work should re-verify before citing.

## §4 Missing infrastructure (the gap inventory)

### §4.1 `def:300C` Labelled rooted trees + quotient

Butcher's `def:300C` (Section 300, around p. 140) introduces
*labelled* rooted trees: a rooted tree with vertex set `V` carries a
bijection `V → {1, 2, …, |V|}`. Two labellings are equivalent if
they differ by an automorphism of the underlying tree (which is what
makes the orbit have size `r(t)! / σ(t)`).

Our current `RootedTree` (`List`-based, `OpenMath/Chapter3/Section310.lean`
line 83–84) carries an implicit vertex-order from the `List`
representation, but does *not* carry a separate labelling. To
faithfully formalise (310i) we need:

- A `LabelledRootedTree` datatype with fields:
  - `underlying : RootedTree`
  - `labelling : ?Vertex underlying → Fin (RootedTree.order underlying)`
- A `?Vertex` notion of "vertex of a rooted tree" — likely an
  inductive predicate `RootedTree.Vertex : RootedTree → Type` with
  constructors for the root and for descending into a child
  position.
- A `Setoid LabelledRootedTree` whose equivalence is "differ by a
  tree automorphism". The automorphism group action is the one
  whose order is `σ(t)` (Butcher §300; cf.
  `symmetry_group_equivalence.md`).
- The canonical map `RootedTree → Quotient labelledSetoid` (any
  labelling representing the unique quotient class).
- The orbit-count theorem `Nat.card (Quotient labelledSetoid …) =
  r(t)! / σ(t)` (this is the σ-faithfulness identity from cycle
  017's deferred issue, surfaced again).

Estimate: **2–4 cycles** for Phase A. Constituents:
- Phase A.1 (1 cycle): `Vertex` predicate + decidable equality + the
  bare `LabelledRootedTree` datatype with a `Fin n` labelling field.
  Non-vacuity: explicit labelling on `cherry`, `broom₃`,
  `mk [vertex, cherry]`.
- Phase A.2 (1–2 cycles): tree-automorphism `Setoid` + quotient,
  plus the constructor `RootedTree → Quotient`. Non-vacuity: prove
  two labelings of `mk [vertex, vertex, vertex]` (two leaves swapped)
  are equivalent.
- Phase A.3 (optional, 1 cycle): orbit-size theorem
  `Nat.card (orbit …) = r(t)! / σ(t)`. This is the σ-faithfulness
  identity. If still hard, accept the σ-faithfulness gap (per
  `symmetry_group_equivalence.md`) and proceed with the stipulative
  σ definition — the bridge then becomes a Phase F obligation.

### §4.2 `thm:306A` Taylor theorem / multinomial expansion

Butcher's `thm:306A` (p. 170) is a multinomial Taylor expansion:

    f(a + δ₁ + δ₂ + … + δ_m) = ∑_{I ∈ I_m} (1/σ(I)) · f^{(#I)}(a) · δ^I,

with `I_m` the set of all sequences from `{1, …, m}` and `σ(I) =
∏_i k_i!` the multinomial symmetry factor. The expansion is over
multi-indices with arbitrary length.

Mathlib has:
- `Polynomial.taylor` — Taylor polynomial (formal, for polynomial
  rings) — wrong domain.
- `taylorWithinEval` / `taylor_isLittleO`
  (`Mathlib.Analysis.Calculus.Taylor`) — the Peano-remainder form
  used pervasively in cycles 248–259. This is the *single-variable*
  Taylor expansion.
- `iteratedFDeriv ℝ k f y` — the multilinear derivative.

Mathlib does *not* (as of HEAD) have the multinomial Taylor theorem
in the shape `thm:306A` requires (an infinite sum indexed by
sequences, with the `σ(I)` denominator). We need to construct it.

Estimate: **1–3 cycles**. Constituents:
- Phase B.1 (1 cycle): two-variable Taylor expansion as a special
  case, with finite-multi-index parameter. State as a finite-sum
  identity, not an infinite series.
- Phase B.2 (1 cycle): `m`-variable generalisation by induction on
  `m` (or by direct application of `iteratedFDeriv` symmetry).
- Phase B.3 (optional, 1 cycle): connection to the Butcher
  `σ(I) = ∏_i k_i!` denominator. This is where the multinomial
  coefficient appears.

If Phase B turns out to be hard, an alternative is to bypass
`thm:306A` entirely in `lem:310B` by working with the multilinear
elementary-differential form directly — see §4.4. This is the more
realistic path; the multinomial Taylor expansion is Butcher's proof
*technique*, not the *content* of `lem:310B`.

### §4.3 Orbit-counting combinatorial bridge

The LHS of (310i) (after `thm:306A` expansion) is a sum over labelled
rooted trees with multiplicity weights; the RHS is a sum over
unlabelled trees `T` with weight `r(t)!/σ(t)`. The bridge is the
orbit-stabilizer theorem applied to the symmetric-group action on
labellings.

Mathlib provides:
- `MulAction.orbit` / `MulAction.stabilizer` / `MulAction.fintype` —
  basic orbit machinery.
- `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` (verify
  name at HEAD) — the orbit-stabilizer theorem itself.

Estimate: **1–2 cycles** once Phase A lands. Constituents:
- Phase C.1 (1 cycle): define the `Equiv.Perm (Fin (order t))`
  action on `LabelledRootedTree` (it permutes the labelling fibres),
  prove the stabilizer is exactly the tree-automorphism group, so
  the orbit has size `r(t)! / σ(t)`.
- Phase C.2 (1 cycle): re-summation identity
  `∑_{labelled} … = ∑_{unlabelled} (r(t)!/σ(t)) · …`, via
  `Finset.sum_image` (orbit selection) + the orbit-count from C.1.

### §4.4 Multilinear connection to elementary differentials

Butcher's (310i) writes `h · f(y₀ + …)` as a sum over `T` of
`(h^{r(t)}/σ(t)) · α(t) · F(t)(y₀)`, where `F(t)(y₀) : N` (the
codomain `N`-space, not scalar). Cycles 248–259's
`iteratedDeriv_*_via_ode` chain proved the scalar `ℝ → ℝ` analogue
at orders 1–5; for the general `lem:310B` we need the multilinear
version on `N`-spaces (per `def:310A`).

Specifically: `elementaryDiff f y₀ t : N` is already polymorphic
(line 187–197 of `Section310.lean`), but the chain-rule
identities `iteratedDeriv_*_via_ode` are scalar-specific (they go
through `deriv` rather than `fderiv`). Lifting these to the
polymorphic setting requires:
- Replacing `deriv f y₀ * f y₀` with `(fderiv ℝ f y₀) (f y₀) : N`.
- Replacing `HasDerivAt` with `HasFDerivAt` everywhere.
- Lifting the `HasDerivAt.comp` scalar-→-scalar idiom (cycle 259
  discovery) to the polymorphic `HasFDerivAt.comp` setting.

Estimate: **1–2 cycles** for Phase D (lifting the chain-rule
identities). This is bookkeeping-heavy multilinear-map plumbing;
the cycle 248 task results documented it as a multi-cycle effort.

### §4.5 Putting it together — the (∗) identity

Once Phases A, B (or A + multilinear bypass), C, D are in place,
`lem:310B` itself reduces to:

1. Apply `thm:306A` (Phase B) to `f(y₀ + Σ…)` on the LHS of (310i).
   This produces a sum over multi-indices `I ∈ I_m`.
2. Re-index by labelled rooted trees (Phase C bridge).
3. Collapse to unlabelled trees with the `r(t)!/σ(t)` weight.
4. Match against the RHS of (∗), which is the `α`-weighted
   `bseriesAlphaPartialSum` summed over the full `Finset` (or
   countable enumeration) of `T`.

The final step (4) requires either a
`Finset.sum_toFinset / Multiset.sum` over the countable but infinite
set `T`, or a `lem:310B` statement bounded at finite order via
`TruncatedRootedTree N`. The latter avoids unfunneled questions
about infinite series convergence.

Estimate: **1–2 cycles** for Phase F (capstone), of which one cycle
is the small-`r` cases on `TruncatedRootedTree 2` / `3` (Phase E,
below) as stepping stones.

## §5 Proposed phase decomposition

The full `lem:310B` is a 6-phase, 8–14 cycle effort. Each phase
should ship axiom-clean, sorry count 0, with a concrete non-vacuity
witness. Each cycle's deliverable must close the phase or a clean
sub-phase — no partial sorry'd scaffolds.

### Phase A — `LabelledRootedTree` datatype + quotient (2–4 cycles)

- **Phase A.1** (1 cycle, single-cycle close achievable):
  `RootedTree.Vertex : RootedTree → Type` inductive predicate with
  decidable equality, plus `RootedTree.vertices : (t : RootedTree)
  → Finset (Vertex t)`. Prove `(vertices t).card = order t`.
  Non-vacuity: enumerate vertices of `cherry`, `broom₃`,
  `mk [vertex, cherry]`. Axiom-clean target. ~80–120 LOC.

- **Phase A.2** (1–2 cycles):
  `LabelledRootedTree` structure with `underlying : RootedTree` and
  `labelling : Equiv (Vertex underlying) (Fin (order underlying))`,
  plus the tree-automorphism `Setoid` (two labellings equivalent if
  related by a tree-automorphism). Witness: exhibit two labellings
  of `mk [vertex, vertex]` that are equivalent (swap the two
  leaves). Axiom-clean target. ~150–200 LOC.

- **Phase A.3** (optional, 1 cycle):
  `orbit_size_eq : Nat.card (Quotient labelledSetoid …) =
  Nat.factorial (order t) / symmetry t`. This is the σ-faithfulness
  identity from cycle 017's deferred issue. Defer if hard; the gap
  becomes a Phase F obligation. Axiom-clean target. ~100–150 LOC.

#### Cycle 263 update — Phase A.2 completion shipped (with weakening)

Cycle 263 shipped the `LabelledRootedTree`-tree-automorphism `Setoid`
infrastructure in `OpenMath/Chapter3/Section300.lean`, appended to
cycle 262's `LabelledRootedTree` structure + canonical labelling
witnesses.

Shipped this cycle (all axiom-clean, depending only on `Quot.sound`):
- `RootedTree.Vertex.rootOf : (t : RootedTree) → Vertex t` — helper
  exposing the root vertex of an arbitrary `t` (case-matches `t = mk cs`
  to dodge implicit `cs` inference failure on generic `t`).
- `RootedTree.TreeAutomorphism (t : RootedTree) : Type` — structure
  with fields `perm : Equiv.Perm (Vertex t)` and `perm_root :
  perm (Vertex.rootOf t) = Vertex.rootOf t`. The single root-fixing
  field is **strictly weaker** than Butcher's tree-automorphism
  group: full recursive structure preservation on child subtrees is
  NOT required. This dodges the nested-inductive mutual-recursion
  pitfall flagged in `feedback_rootedtree_nested_induction.md`.
- `TreeAutomorphism.id` / `.trans` / `.symm` — group-theoretic API
  (identity / composition / inverse).
- `LabelledRootedTree.Equiv` — pointwise-encoded equivalence
  (existence of underlying-tree equality plus a tree-automorphism
  realising the labelling difference). Pointwise avoids
  dependent-typing issues with `Equiv` equality across heterogeneous
  `Vertex` types.
- `LabelledRootedTree.Equiv.refl` / `.symm` / `.trans` — the three
  Setoid axioms. `symm` and `trans` destructure `a`/`b`/`c` first to
  expose `underlying : RootedTree` as a free variable, then `cases
  hEq` performs the type-level substitution.
- `LabelledRootedTree.setoid : Setoid LabelledRootedTree`.
- Three reflexivity non-vacuity witnesses (`canonicalVertex`,
  `canonicalCherry`, `canonicalBroom₃`).

**What is NOT claimed by this Setoid**:
- The σ-faithfulness orbit-count `Nat.card (orbit …) = r(t)! / σ(t)`
  (Phase A.3 above). The Setoid is **coarser** than Butcher's
  quotient because `TreeAutomorphism` doesn't enforce recursive
  structure preservation — any root-fixing permutation of vertices
  qualifies.
- Heterogeneous (genuinely-different-labelling) non-vacuity. This
  requires evaluating `Fintype.equivFinOfCardEq` on concrete trees,
  which won't reduce cleanly; deferred to Phase A.2.1 (cycle 264+).

**Cycle 264+ strengthening task**: Replace the weakened
`TreeAutomorphism` with the full recursive structure-preservation
predicate. Requires a `mutual` block of definitions through
`List RootedTree` per `feedback_rootedtree_nested_induction.md`.
Once shipped, the Setoid recovers Butcher's `def:300C` quotient
faithfully, and Phase A.3's orbit-count theorem becomes meaningful.

`lem:310B` remains `[ ]` / `unformalized` in `plan.md` and
`extraction/formalization_data/lean_status.json` — this cycle is
infrastructure-only.

### Phase B — `thm:306A` Taylor / multinomial (1–3 cycles, deferrable)

- **Phase B.1** (1 cycle):
  `m`-variable Taylor expansion in single-variable form: for `m = 1`,
  this is the existing cycle 248 machinery (`taylor_isLittleO`).
  Generalise to `m = 2` using `iteratedFDeriv` symmetry.
  Non-vacuity: explicit expansion at `m = 2`, polynomial degree 2,
  matching the Butcher Table 306(I) example. Axiom-clean. ~100 LOC.

- **Phase B.2** (1 cycle):
  Generalise to arbitrary `m` by induction on `m`. The Butcher
  `σ(I)` multinomial denominator appears here. Non-vacuity:
  recovery of `m = 2` Phase B.1 as a corollary. ~150 LOC.

- **Phase B.3** (1 cycle, optional):
  Reformulate as the textbook closed form (sum over multi-indices
  with `f^{(#I)}` and `σ(I)^{-1}`). ~50 LOC. Or **skip Phase B
  entirely** and route `lem:310B` through the multilinear
  elementary-differential form (§4.4) directly — see Phase D below.

### Phase C — Orbit-counting combinatorial bridge (1–2 cycles)

Requires Phase A.

- **Phase C.1** (1 cycle):
  `Equiv.Perm (Fin (order t))` action on `LabelledRootedTree t`,
  stabilizer = tree-automorphism group, orbit size = `r(t)!/σ(t)`
  via `card_orbit_mul_card_stabilizer_eq_card_group`. Non-vacuity:
  count the labelling orbit of `cherry` (2 labellings, σ = 1, so 2
  orbits each of size 1; or 1 orbit of size 2 if we consider the
  two-vertex tree). Axiom-clean. ~100–150 LOC.

- **Phase C.2** (1 cycle):
  Re-summation identity
  `Σ_{labelled trees} ψ(t) = Σ_{unlabelled t ∈ T} (r(t)!/σ(t)) · ψ(t)`
  for any `ψ : RootedTree → A` (additive monoid `A`). Closure via
  `Finset.sum_image` + Phase C.1. Non-vacuity: `r ≤ 3` case
  expanded explicitly. ~80–120 LOC.

### Phase D — Multilinear elementary-differential lift (1–2 cycles)

- **Phase D.1** (1 cycle):
  `iteratedFDeriv_via_ode` polymorphic version of cycles 248/256/257/258/259
  scalar identities. Conclusion: under
  `∀ x, HasFDerivAt yex (... f (yex x) ... fderiv chain ...) x`,
  the `k`-fold iterated `fderiv` of `yex` at `x₀` is a multilinear
  polynomial in `fderiv^j f y₀` and `f y₀`. State for `k = 2, 3`
  as a starter; defer `k ≥ 4` to Phase D.2. ~150–200 LOC.

- **Phase D.2** (optional, 1 cycle):
  General `k` via Faà di Bruno. Mathlib's
  `iteratedFDeriv` machinery (`Mathlib.Analysis.Calculus.IteratedDeriv`)
  may have partial Faà-di-Bruno support; verify before re-deriving.
  ~150–250 LOC.

### Phase E — Small-`r` `lem:310B` instances on `TruncatedRootedTree N` (1–3 cycles, stepping stones)

Requires Phases A, C (and either B or D, depending on the route
chosen).

- **Phase E.1** (1 cycle):
  `lem_310B_truncated_r_le_two` — the identity (∗) restricted to
  trees of order ≤ 2 (just `vertex` and `cherry`). This is the
  scalar order-2 specialisation we have already (cycle 256
  `lem_311A_order_two`), reformulated in the polymorphic
  multilinear setting from Phase D. ~100–150 LOC.

- **Phase E.2** (1 cycle):
  `lem_310B_truncated_r_le_three` — order ≤ 3, four trees total
  (`vertex`, `cherry`, `broom₃`, `mk [cherry]`). Uses Phase C.2's
  orbit re-summation for the first time non-trivially (the labelling
  count for `broom₃` is non-trivial). ~150–200 LOC.

- **Phase E.3** (optional, 1 cycle):
  `lem_310B_truncated_r_le_four` or `r_le_five` as additional
  evidence. ~150 LOC each.

### Phase F — General `lem:310B` capstone (1–2 cycles)

Requires Phases A, C, D, E (and ideally B, but can route around).

- **Phase F.1** (1 cycle):
  State and prove the textbook (∗) on `TruncatedRootedTree N` for
  arbitrary `N`. Closure via Phase C.2's orbit re-summation +
  Phase D's multilinear chain rule + Phase E's small-`r`
  inductive base. ~200–300 LOC.

- **Phase F.2** (optional, 1 cycle):
  Extend to the unbounded form (Butcher's formal series). This
  requires a careful statement of "formal series over the countable
  set `T`"; Mathlib's `HahnSeries` or `MvPowerSeries` may apply, or
  we can stay at `TruncatedRootedTree N` and let `N → ∞` implicitly.
  ~150–250 LOC.

**Total estimate**: 6 phases, 8–14 single-cycle deliverables. The
range reflects whether Phases A.3, B (entirely), D.2, E.3, F.2 are
attempted.

## §6 Risk assessment

### Phase A risks

- **`Vertex` predicate motive issues.** Inductive predicates on
  `List`-based recursive types (our `RootedTree`) historically
  trigger nested-induction motive failures (see
  `feedback_rootedtree_nested_induction.md` in memory). Mitigation:
  use a `mutual` block of `theorems` with explicit constructor
  pattern matching, as established in the cycle 017 σ-recursion
  pattern.
- **`Equiv (Vertex t) (Fin (order t))` decidability.** Decidable
  equality on `Equiv` requires both sides to be decidable; Mathlib
  has `Equiv.decEq` for `Fin n` but the `Vertex t` decidability
  needs to be established at Phase A.1. Mitigation: in Phase A.1's
  axiom-clean check, run `lean_verify` on the `decEq` instance.
- **σ-faithfulness divergence.** Per
  `.prover-state/issues/symmetry_group_equivalence.md`, our
  `RootedTree.symmetry` is *stipulatively* defined via (301b)
  rather than as the automorphism-group order. Phase A.3's orbit-
  count theorem `Nat.card (orbit …) = r(t)!/symmetry t` would close
  this gap — but it might be hard, and could be deferred to Phase F.
  Risk: any phase that needs the orbit-count theorem to hold in the
  "symmetry-group order" sense (not just as `(301b)` recursion) is
  blocked by this gap. Accept the gap or fix it in Phase A.3.

### Phase B risks

- **Mathlib gap.** Multinomial Taylor expansion is not in Mathlib
  (verified at HEAD). We must build it ourselves. The single-
  variable form (`taylor_isLittleO`) is the cycle 248–259 starting
  point; lifting to multi-variable is a moderate effort.
- **Bypass route.** Phase B can be entirely *skipped* if we route
  `lem:310B`'s proof through Phase D's multilinear identity
  directly. Butcher uses `thm:306A` as the proof technique, but the
  *content* of `lem:310B` is the closed-form evaluation of (310i),
  not the multinomial expansion itself. Sorry-first scaffolds for
  Phase B should be forbidden; the bypass is the lower-risk path.

### Phase C risks

- **Orbit-stabilizer name drift.** `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`
  is the established Mathlib name (verify); a recent Mathlib refactor
  may have renamed it (e.g. `MulAction.orbit_card_eq` or similar).
  Mitigation: `lean_local_search` for "orbit" + "stabilizer" before
  citing.
- **Action type plumbing.** The `Equiv.Perm (Fin (order t))` action
  on `LabelledRootedTree t` requires care with the dependent type
  `LabelledRootedTree t` (depending on `t`). Mitigation: avoid
  dependent types where possible; use an `attach` / `subtype`
  pattern for the labelling field.

### Phase D risks

- **`HasFDerivAt.comp` semantics.** Cycle 259 discovered that scalar
  `HasDerivAt.comp` returns `outer_deriv * inner_deriv` despite the
  type-class signature `h' • g'`. The polymorphic
  `HasFDerivAt.comp` does NOT have this scalar-coincidence: it's
  genuinely `outer ∘L inner` (continuous-linear composition). The
  Faà-di-Bruno chain rule for `iteratedFDeriv` involves Bell-
  polynomial-indexed sums of multilinear compositions; this is
  combinatorially more complex than the scalar version.
- **Bell coefficients in the multilinear setting.** Cycle 259's
  scalar order-5 closed form has Bell coefficients `(1, 7, 4, 11, 1)`.
  In the multilinear setting, these coefficients become labelled
  rooted tree counts (cf. Butcher Table 310(II)) — precisely the
  bridge to `lem:310B`. Phase D.2 (general `k`) is therefore a
  near-restatement of `lem:310B` itself; it may be cleaner to skip
  D.2 and go straight to Phase F.

### Phase E/F risks

- **Sorry-first forbidden.** Per the cycle 200/201 rollback (and the
  138/139 `thm:550A` precedent), Phases E and F must close
  axiom-clean in a single cycle each. If Phase F looks too large
  (estimated > 1 cycle), split it as Phase F.1 (state + partial
  proof on small `N`) and F.2 (full closure). Use the cycle
  149/150 `def:530B` rollback as the concrete cautionary precedent:
  cycle 149 wrote a sorry-first scaffold with `applyStartingThenStep`
  / `applyExactThenStarting` operator bodies as `sorry`; sorry
  count went 0 → 3; cycle 150 rolled back. The fix was the multi-
  phase Path A decomposition in
  `.prover-state/issues/def_530B_scaffold_strategy.md` (cycles
  151–164: 14 cycles, all axiom-clean). `lem:310B` plan should
  follow that template.

### Cross-cutting risks

- **σ-faithfulness gap impact.** The deferred orbit-count theorem
  (Phase A.3) is the same gap as the cycle 017 stipulative
  symmetry definition. If `lem:310B`'s Phase F.1 needs to invoke
  "σ(t) is the automorphism count" rather than "σ(t) satisfies the
  (301b) recursion", we must either prove A.3 or route around it
  (use the (301b) recursion all the way through the proof, never
  invoking the group-theoretic identity directly). The latter is
  achievable per Butcher's actual proof, which only uses the
  multinomial-symmetry identity `σ(I) · (∏ σ(t_i)^{m_i})^{-1} =
  σ(t)^{-1}` — a recursion-level statement, not a group-theoretic
  one.

- **Multi-cycle drift.** A 6-phase, 8–14 cycle plan extends well
  beyond the textbook section being formalised. The planner should
  re-validate this scoping doc every 3–4 cycles and adjust phase
  estimates based on observed velocity. Reference the cycle
  149–164 `def:530B` precedent: the original 3-phase Path A
  estimate (cycles 151–153) ballooned to 14 cycles with helper
  extractions and r-parametric refactors. Plan for similar drift
  here.

## §7 Suggested cycle 261 entry point

**Phase A.1**: scaffold `RootedTree.Vertex : RootedTree → Type` and
`RootedTree.vertices : (t : RootedTree) → Finset (Vertex t)`,
prove `(vertices t).card = order t` (the "order counts vertices"
identity). Non-vacuity: enumerate the vertices of `cherry`
(2 vertices), `broom₃` (3 vertices), and `mk [vertex, cherry]`
(4 vertices), confirming `vertices.card = order` in each case.

**Concrete deliverables**:
- `def RootedTree.Vertex : RootedTree → Type` (inductive predicate
  with `root` constructor and `child : (cs : List RootedTree) → (i :
  Fin cs.length) → Vertex (cs.get i) → Vertex (mk cs)`).
- `instance : DecidableEq (Vertex t)` (via mutual decidability with
  `Vertex_in_list`).
- `def RootedTree.vertices (t : RootedTree) : Finset (Vertex t)`
  (built via mutual recursion over the children list).
- `theorem RootedTree.vertices_card (t : RootedTree) :
  (vertices t).card = order t` (by structural induction with the
  cycle 017 `mutual` block pattern).
- Three `example`s exercising `vertices_card` on small trees.

**Axiom-clean target**: `[propext, Classical.choice, Quot.sound]`.
**Sorry count**: 0 → 0 (must remain). **Estimated LOC**: ~80–120.
**File placement**: new file `OpenMath/Chapter3/Section300.lean`
(or extend `Section310.lean`; place per cycle 261's planner choice).

If Phase A.1 closes cleanly in cycle 261, cycle 262 ships Phase A.2
(`LabelledRootedTree` + tree-automorphism `Setoid`). If A.1 stalls
or splits, cycle 262 re-scopes Phase A.

## §8 Alternative cycle 261 targets (entity-pivot scouting)

Cycle 259 task results suggested three entities outside the §310
cluster as potential fresh-entity pivots. Below I scout their
JSONs and verify dependency structure against the
`extraction/formalization_data/entities/<id>.json` schema.

### §8.1 `thm:351B` — A-stability criterion for Runge-Kutta methods

- **Statement** (from `entities/thm_351B.json`):
  > A Runge–Kutta method with stability function `R(z) = N(z)/D(z)`
  > is A-stable if and only if (a) all poles of `R` (i.e. zeros of
  > `D`) are in the right half-plane and (b) `E(y) ≥ 0` for all
  > real `y`, where `E(y) = D(iy)D(-iy) - N(iy)N(-iy)`.

- **Dependencies** (from JSON `transitive_dependencies` field):
  `[]` — empty.
- **Dependents**: `lem:351A`, `thm:355F`.
- **`formalization_status`**: `unformalized`.
- **`lean_file` / `lean_symbol`**: `null`.

- **Verdict**: Independent of `lem:310B` — no transitive
  dependency. However, the statement requires substantial new
  prerequisite infrastructure not currently in the repo:
  - A-stability definition (`def:351A`, also unformalised).
  - Stability function `R(z) = N(z)/D(z)` of a Runge-Kutta method.
  - `E(y)`-polynomial machinery.
  - Maximum-modulus principle (Mathlib's
    `Complex.MaximumModulusPrinciple` — verify name).
  - Open-mapping / pole-of-meromorphic-function machinery.

  Net: NOT a single-cycle entry point. Estimate ~5–8 cycles to
  build the prerequisite machinery before `thm:351B` itself can be
  shipped. The scale is similar to `lem:310B`'s plan above.

### §8.2 `lem:342A` — Properties of shifted Legendre polynomials

- **Statement** (from `entities/lem_342A.json`):
  > There exist polynomials `P_n^* : [0,1] → ℝ` of degree `n` such
  > that `∫₀¹ P_m^* P_n^* dx = 0` for `m ≠ n` (342a) and
  > `P_n^*(1) = 1` (342b). Plus five further properties (342c–g):
  > parity `P_n^*(1-x) = (-1)^n P_n^*(x)`, norm `∫ P_n^*² = 1/(2n+1)`,
  > Rodrigues formula, three-term recurrence, real-zeros-in-(0,1).

- **Dependencies** (from JSON `transitive_dependencies`):
  `[cor:342D, lem:342B, thm:342C]` — none are `lem:310B`.
- **Dependents**: `lem:359A`, `thm:324C`, `thm:344A`, `thm:358A`,
  `thm:363A`.
- **`formalization_status`**: `unformalized`.

- **Verdict**: Independent of `lem:310B`. The shifted Legendre
  polynomial machinery is pure single-variable real-analysis;
  Mathlib has `Polynomial.legendre` and related machinery in
  `Mathlib.Analysis.SpecialFunctions.Polynomials.Legendre` (verify
  exact path). Each of the seven (342a–g) properties could
  plausibly ship as a single-cycle deliverable (or as a small
  cluster of 2–3 cycles).

  **Single-cycle entry point: YES**, conditional on Mathlib's
  Legendre infrastructure being usable. The recommended first
  cycle target is (342a) orthogonality on `[0,1]` (a definitional
  shift of Mathlib's `[-1,1]` Legendre), with (342b) `P_n^*(1) = 1`
  as a one-line corollary.

  Note: `lem:342A` depends on `lem:342B` and `thm:342C` per the
  JSON. `lem:342B` (Gaussian quadrature exactness) in turn depends
  on `thm:342C` (order-conditions equivalence). The JSON's
  `transitive_dependencies` ordering is non-trivial — verify by
  reading `extraction/formalization_data/topo_order.json`
  before planning a 342-cluster sequence.

### §8.3 `lem:342B` — Gaussian quadrature exactness

- **Statement** (from `entities/lem_342B.json`):
  > Let `c_1, …, c_s` denote the zeros of `P_s^*`. Then there
  > exist positive numbers `b_1, …, b_s` such that
  > `∫₀¹ φ(x) dx = ∑_{i=1}^s b_i · φ(c_i)` (342h)
  > for any polynomial of degree `< 2s`. The `b_i` are unique.

- **Dependencies** (from JSON `transitive_dependencies`):
  `[thm:342C]` — does NOT include `lem:310B`.
- **Dependents**: `lem:342A`, `lem:359A`, `thm:324C`, `thm:344A`,
  `thm:358A`, `thm:363A`.
- **`formalization_status`**: `unformalized`.

- **Verdict**: Independent of `lem:310B`. However, this lemma
  consumes the zeros of `P_s^*` (so depends on `lem:342A`'s
  (342g)) and requires polynomial-division / Euclidean-algorithm
  machinery on `ℝ[X]`.

  **Single-cycle entry point: NO** as a standalone target —
  `lem:342B` requires `lem:342A` (specifically 342g, the real-
  zeros-in-(0,1) property) as a hard prerequisite. The
  Gaussian-quadrature uniqueness argument is also substantive
  (~150–200 LOC alone).

  If the §342 cluster is the chosen pivot direction, the
  natural single-cycle entry point is `lem:342A` (342a) or (342b),
  not `lem:342B`.

### §8.4 Summary verdict

All three candidates (`thm:351B`, `lem:342A`, `lem:342B`) are
**independent of `lem:310B`** at the dependency-graph level, so any
of them could in principle be pursued in parallel with the `lem:310B`
phase plan above.

**Best single-cycle entry point among the three**: `lem:342A`
property (342a) — orthogonality of shifted Legendre polynomials on
`[0,1]`. This routes through Mathlib's Legendre polynomial
machinery (verify) and yields a concrete one-cycle target.

**`thm:351B`**: Substantive entity with ~5–8 cycle prerequisite
machinery needed. Not single-cycle.

**`lem:342B`**: Requires `lem:342A` (342g) as a prerequisite.
Sequential after `lem:342A`, not single-cycle.

The cycle 261 planner has three credible directions:
1. **Phase A.1 of this plan** (`lem:310B` infrastructure) — see §7.
2. **`lem:342A` (342a) orthogonality** — single-cycle pivot to the
   §342 Gaussian quadrature cluster.
3. **`thm:351B` prerequisite scoping** — write a similar
   multi-phase plan for `thm:351B`. Lower-priority unless the
   `lem:310B` and `lem:342A` paths are both blocked.

Recommended: option 1 if the planner wants to maintain §310/§311
strategic momentum; option 2 if the planner wants a quick clean
ship for cycle 261 while reserving `lem:310B` infrastructure for
cycles 262+.

## Cross-references

- `extraction/formalization_data/entities/lem_310B.json` — target
  entity.
- `extraction/formalization_data/entities/thm_306A.json` —
  multinomial Taylor (Phase B prerequisite, unformalised).
- `extraction/formalization_data/entities/lem_311A.json` — adjacent
  partial-formalisation entity, cycles 248–259.
- `extraction/raw_text/ch03.txt` lines 730–840 — Butcher's §310 +
  §311 text including (310i) (line 748), `def:310A` (line 730–735),
  `lem:310B` (line 805–834), `lem:311A` (line 848+).
- `OpenMath/Chapter3/Section310.lean` — `RootedTree`, `order`,
  `theta`, `theta_eq_one`, `elementaryDiff` (polymorphic).
- `OpenMath/Chapter3/Section301.lean` — `density`, `symmetry`,
  `alphaWeight`, `bseriesTerm`, `bseriesPartialSum`,
  `bseriesAlphaTerm`, `bseriesAlphaPartialSum`,
  `TruncatedRootedTree`.
- `OpenMath/Chapter3/Section311.lean` — `F_tau_eval`,
  `bseriesOrderOne`, `lem_311A_order_{one,two,three,four,five}`.
- `.prover-state/task_results/cycle_259.md` — most recent task
  results recommending option 1 (this plan).
- `.prover-state/issues/symmetry_group_equivalence.md` — cycle 017
  σ-faithfulness divergence (Phase A.3 risk).
- `.prover-state/issues/def_530B_scaffold_strategy.md` — multi-
  phase scoping precedent (cycles 149/150 rollback → 151/152/.../164
  Path A). Template for `lem_310B_plan.md` phase decomposition.
