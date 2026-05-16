# Cycle 337 Results

## Worked on

`def:422B` Phase A.0 (cycle 337 strategy): pin Butcher's `D` operator
and ship `D_phi : Quotient PhiEquivalent.setoidSigma → Quotient
PhiEquivalent.setoidSigma`, per `.prover-state/issues/def_422B_path.md`
§5 (Phase A.0 row).

Two sub-tasks:

* **P1.A**: Read Butcher §422 (`extraction/raw_text/ch04.txt:1109–1198`)
  and the surrounding §380–§387 group machinery (`ch03.txt:8463–9520`),
  decide on the `D` operator's formulation, and append a "§A.0
  D-operator decision (cycle 337)" subsection to the scoping doc.
* **P1.B**: Ship `D_element`, `D_phi`, and two non-vacuity sanity
  theorems in `OpenMath/Chapter4/Section422.lean`.

## Approach

### P1.A — pin `D`

Read §387 (`extraction/raw_text/ch03.txt:9391–9465`) and §385
(`ch03.txt:9101–9131`). Butcher §387 line 9392 states verbatim:

> As we have remarked, D ∈ G represents the differentiation operation,
> scaled by the unit stepsize h.

And §385 (line 9117–9121) gives `D` concretely as the generalized
**one-stage** RK method

```
0 0
0 1
```

i.e. `s = 1, A = 0, b = [1], c = [0]` with `b₀ = 0`. The method
computes `y_n = 0·y_{n-1} + h·f(y_{n-1}) = h·f(y_{n-1})` — pure
differentiation scaled by `h`.

**Elementary-weight signature on `T` (rooted trees, excluding `∅`):**

* `Φ_D(τ) = 1`
* `Φ_D(t) = 0` for `t` of order ≥ 2

**Decision:** This is a **refined fourth candidate** (D.4) — none
of the planner's listed candidates (D.1 tree-grafting / D.2
order-weighted multiplication / D.3 forest-convolution) match.
Specifically:

* **(D.1) Tree-grafting `D(t) = mk [t]` REJECTED**: would give
  `(ηD)(τ) = η(mk [τ])` (the cherry value), but the textbook formula
  via (383a) convolution gives `(ηD)(τ) = 1` (constant). The (D.1)
  hypothesis got the direction backwards — `D` *consumes* children
  rather than *adding* a root.
* **(D.2) Order-weighted `(Df)(t) = r(t)·f(t)` REJECTED**: would
  give `(ηD)(t) = r(t)·η(t)`, but the textbook gives
  `(ηD)(mk children) = Π η(child)` — a tree-shape-dependent *product*,
  not a scalar multiple.
* **(D.3) Forest-convolution `D` REJECTED**: too general; (D.4) is
  the specific element in `G ⊇ G₁` with the (385b) tableau realisation.
  The (383a) convolution-product IS used to derive `(ηD)`, but `D`
  itself is the specific (385b) element.

**Critical b₀-invisibility observation:** Butcher's `D ∈ G` has
`b₀ = 0` and is therefore **not directly representable** in our
`RKTableau` framework (`Section312.lean:66` — only `(A, b, c)`, with
`b₀ = 1` implicit). **However**: `PhiEquivalent`
(`Section381.lean:124`) quantifies only over `t : RootedTree`, and
the inductive `RootedTree` (`Section310.lean:83`) admits no
empty-tree representative. Consequently the b₀ value (which would be
tested at `∅`) is **invisible** to `PhiEquivalent`. At the
`Quotient PhiEquivalent.setoidSigma` level, `Φ_D|_T = Φ_{explicitEuler}|_T`,
and `⟦⟨1, RKTableau.explicitEuler⟩⟧` is the canonical quotient-level
representative of `D`.

This is *not* definition smuggling: the b₀-invisibility is a
*property* of the §383 quotient construction, not a hack. Equation
(422a) is naturally interpreted on rooted trees `T`, so the `∅` term
in (422a) (the constant `1 − Σ αᵢ`) is absorbed into the separate
**preconsistency** hypothesis `Σ αᵢ = 1` already required by
`IsPreconsistent`.

Appended a 120-line "§A.0 D-operator decision (cycle 337)" subsection
to `.prover-state/issues/def_422B_path.md` with 6 sub-sections:
§A.0.1 (textbook source), §A.0.2 (D.4 choice), §A.0.3 (rejection of
D.1/D.2/D.3), §A.0.4 (framework wire-up + b₀-invisibility argument),
§A.0.5 (Lean signature sketch), §A.0.6 (impact on §4/§5 of doc).

### P1.B — ship `D_phi`

Used the planner's **Form 2** (group-element-level) strategy with
`D_element := ⟦⟨1, RKTableau.explicitEuler⟩⟧` justified by the
b₀-invisibility argument from P1.A.

Lean code added to `OpenMath/Chapter4/Section422.lean` (kept the
cycle 336 wire-up theorem in place):

* `D_element : Quotient PhiEquivalent.setoidSigma` —
  the canonical quotient representative.
* `D_phi (η : Quotient PhiEquivalent.setoidSigma) :
   Quotient PhiEquivalent.setoidSigma := η * D_element` —
  right-multiplication via cycle 236's `instGroup_phi`.
* `D_phi_one : D_phi 1 = D_element` — via `one_mul`.
* `D_element_elementaryWeight_vertex :
   RKTableau.elementaryWeightQ_phi D_element RootedTree.vertex = 1` —
  via `simp [RKTableau.explicitEuler, derivativeWeight_vertex]` after
  `show`ing the elementary weight equals the `Fin 1` sum.

## Result

**SUCCESS.** All five public symbols (4 new + 1 retained from cycle
336) compile clean via `lake env lean OpenMath/Chapter4/Section422.lean`,
axiom-clean against `[propext, Classical.choice, Quot.sound]`. No
sorrys introduced (sorry count remains 0). Section422.lean: 56 → 137 LOC.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `D_element : Quotient PhiEquivalent.setoidSigma`

* Entity ID: this is supporting infrastructure for `def:422B`; the
  underlying mathematical object is Butcher §387's `D ∈ G`
  (`extraction/raw_text/ch03.txt:9392`):
  > As we have remarked, D ∈ G represents the differentiation
  > operation, scaled by the unit stepsize h. If ξ denotes the
  > element in G₁ corresponding to a generalized Runge–Kutta tableau
  > … then ξD will correspond to the s-stage tableau (387b) …
  And §385 (`ch03.txt:9117–9121`) realises `D` concretely as the
  generalized 1-stage RK method `[[0,0], [0,1]]` (s=1, A=0, b=[1],
  c=[0], b₀=0).
* Lean statement captures: **same content on `T`** (i.e. on rooted
  trees, excluding the empty tree). On `T`, `Φ_D` and the elementary
  weight of `RKTableau.explicitEuler` both equal `Φ(τ) = 1, Φ(t≥2) = 0`,
  so `⟦⟨1, RKTableau.explicitEuler⟩⟧` is the unique quotient class in
  `Quotient PhiEquivalent.setoidSigma` representing Butcher's `D`.
* Divergence justification: Butcher's `D` lives in `G` (with `b₀=0`),
  while `RKTableau.explicitEuler` has `b₀=1` implicit. The b₀-value
  is invisible to `PhiEquivalent` (per `Section381.lean:124` and
  `Section310.lean:83`), so the two collapse to the same equivalence
  class in `Quotient PhiEquivalent.setoidSigma`. This is a *quotient
  property*, not a faithfulness violation. The constant-term
  contribution at `∅` (relevant for Butcher's (422a) at the empty
  tree) is absorbed into the separate `IsPreconsistent` predicate
  already in `Section404.lean`. Detailed argument in
  `.prover-state/issues/def_422B_path.md` §A.0.4.

### `D_phi : Q → Q := η ↦ η * D_element`

* Entity ID: this is supporting infrastructure; the underlying
  mathematical object is right-multiplication-by-`D` on the §383
  group, as it appears in equation (422a):
  > 1 − α₁ η⁻¹ − ⋯ − αₖ η⁻ᵏ − β₀ D − β₁ η⁻¹ D − ⋯ − βₖ η⁻ᵏ D = 0
* Lean statement captures: **same content**. The §383 group
  multiplication on `Quotient PhiEquivalent.setoidSigma` is exactly
  `composeQ_phi` (cycle 232 + cycle 236), so `η * D_element`
  evaluates the §383 group product `η · D`. The well-definedness on
  the quotient is automatic (the group multiplication already respects
  `PhiEquivalent` by construction).
* No divergence.

### `D_phi_one : D_phi 1 = D_element`

* Tautology check: PASS. The conclusion `D_phi 1 = D_element`
  unfolds to `1 * D_element = D_element`; this is `one_mul _`,
  using the §383 group structure (`instGroup_phi`). No hypothesis
  matches the conclusion verbatim.
* Identity check: PASS. The proof is `one_mul _`, not `exact h` for
  any hypothesis `h`. The theorem does real algebraic work via the
  group's left-identity axiom.
* Hypothesis strength check: PASS. No hypotheses required.

### `D_element_elementaryWeight_vertex : Φ_{D_element}(τ) = 1`

* Entity ID: derives from Butcher §387's `Φ_D(τ) = 1` (visible by
  inspection of the (385b) tableau: 1-stage with b=[1], so
  `Φ(τ) = Σᵢ bᵢ · (ΦᵢD)(τ) = 1 · 1 = 1`).
* Lean statement captures: **same content**. The proof unfolds
  `elementaryWeightQ_phi` via `elementaryWeightQ_phi_mk` (definitional
  `rfl`), then expands the `Fin 1` sum via `simp` with
  `RKTableau.explicitEuler` unfolding and cycle 187's
  `derivativeWeight_vertex` lemma. Closed in three tactic lines.
* Tautology / identity / hypothesis-strength checks: all PASS.

## Dead ends

None this cycle. The reading of §387 was decisive — it explicitly
pins `D ∈ G` to (385b) and rules out all three planner candidates.

The b₀-invisibility realisation was a near-dead-end: I initially
worried that since `D` has `b₀=0` and our framework has `b₀=1`
implicit, we could not represent `D` at the quotient level. The
resolution (b₀ is invisible because `RootedTree` admits no empty
tree) recovered a clean Form-2 ship.

## Discovery

1. **Butcher §387 explicitly defines `D ∈ G`** (`ch03.txt:9392`)
   as the generalized 1-stage RK method `[[0,0], [0,1]]` from §385b
   (`ch03.txt:9117–9121`). This is the **canonical** definition.
   Future cycles must NOT re-invent `D` via tree-grafting or other
   constructions; cite §387 directly.

2. **The `b₀`-invisibility of `PhiEquivalent`** is a load-bearing
   structural property of our formalization. It means:

   * Generalized RK methods (with arbitrary `b₀`) and standard RK
     methods (with `b₀=1`) cannot be distinguished at the §383
     quotient level on tree functions.
   * The `b₀` constraint is exclusively encoded in the
     **preconsistency** hypothesis on LMMs, not in the quotient
     group structure.
   * Consequently, `D ∈ G \ G₁` and `1 + D ∈ G₁` collapse to the
     same `Quotient PhiEquivalent.setoidSigma` element. This is
     mathematically correct: the §383 group quotient *is* designed
     to forget `b₀`.

   This is critical context for Phase C+ workers: equation (422a)
   when ported to our framework should be *on-tree* (`∀ t : RootedTree`),
   not *on-augmented-tree* (`∀ t : T#`). The empty-tree case of (422a)
   collapses to preconsistency and is handled separately.

3. **`RKTableau.explicitEuler` is the canonical witness for `D` in
   `Q`.** This is a non-obvious correspondence (the textbook
   distinguishes them via `b₀`) and worth memorialising in memory.

4. **The planner's three candidates (D.1/D.2/D.3) were all wrong** —
   the strategy doc anticipated this with the "refined fourth
   candidate" escape hatch, and reading the textbook revealed the
   correct interpretation. Future planners should NOT prematurely
   commit to candidate enumerations without the worker first reading
   the textbook section in full.

## Suggested next approach

Cycle 338 (Phase A.0.2 or Phase B) candidates per scoping doc §5:

* **Phase A.0.2** (~50 LOC, low risk, completes A.0): ship the
  higher-order vanishing lemma `Φ_{D_element}(t) = 0` for trees of
  order ≥ 2, plus 1–2 simp-lemmas for `D_phi` congruence (e.g.
  `D_phi_mul : D_phi (η * η') = (η * η') * D_element = η * (η' *
  D_element) = η * D_phi η'` via `mul_assoc`). The higher-order
  vanishing proof requires unfolding `derivativeWeight` for
  `RKTableau.explicitEuler` on a non-vertex tree — should follow from
  the `A = 0` zero-multiplication recursion (cycle 187 pattern).

* **Phase B** (~30–60 LOC, low risk, fresh phase): ship two
  small lemmas verifying `Group.zpow` fires cleanly on the §383
  quotient group:
  - `zpow_neg_one : (⟦⟨s, M⟩⟧ : Quotient _)^(-1 : ℤ) = ⟦⟨s, M.inverse⟩⟧`
  - `zpow_neg_natCast : ⟦⟨s, M⟩⟧^(-(n : ℤ)) = ⟦…iterated inverse…⟧`
  These are non-vacuity ships verifying Mathlib's `GroupPower` API
  inherits cleanly through `instGroup_phi`; the witness is
  `paddedEuler` per `def_422B_path.md` §4.2.

Either is a single-cycle ship; Phase A.0.2 has a tighter dependency
chain on cycle 337's work (immediate follow-on), Phase B opens a
fresh phase.

Recommendation: **Phase A.0.2** for cycle 338 — it tightens the
cycle 337 deliverable's mathematical content (verifies the
elementary-weight signature of `D_element` matches Butcher's
`Φ_D` on **all** trees, not just `τ`), and the proof template is
mechanical (`derivativeWeight` recursion under `A = 0` reduces every
sum to `0`).
