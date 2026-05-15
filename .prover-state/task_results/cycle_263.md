# Cycle 263 Results

## Worked on

Phase A.2 completion of `lem_310B_plan.md` — the tree-automorphism
equivalence relation on `LabelledRootedTree`. Cycle 262 shipped the
`LabelledRootedTree` structure + canonical labelling; cycle 263
closes Phase A.2 by adding the (weakened) `TreeAutomorphism`
structure + group-theoretic API and the `Setoid LabelledRootedTree`
instance derived from it.

## Approach

Followed the cycle 263 strategy verbatim. Five priority blocks
shipped to `OpenMath/Chapter3/Section300.lean`:

* **P1** `TreeAutomorphism (t : RootedTree) : Type` — structure with
  `perm : Equiv.Perm (Vertex t)` and root-fixing field
  `perm_root : perm (Vertex.rootOf t) = Vertex.rootOf t`. Deliberately
  weakened relative to Butcher's tree-automorphism group (no
  recursive structure preservation on child subtrees) to dodge the
  nested-inductive mutual-recursion pitfall flagged in
  `feedback_rootedtree_nested_induction.md`.
* **P2** `TreeAutomorphism.id / .trans / .symm` — group-theoretic API
  built on `Equiv.refl / .trans / .symm` plus `Equiv.symm_apply_apply`
  for the inverse's `perm_root`.
* **P3** `LabelledRootedTree.Equiv` (pointwise) + `Equiv.refl /
  .symm / .trans` + `LabelledRootedTree.setoid : Setoid
  LabelledRootedTree`.
* **P4** Three reflexivity non-vacuity witnesses on `canonicalVertex`,
  `canonicalCherry`, `canonicalBroom₃`.
* **P5** File docstring update + cycle 263 subsection appended to
  `.prover-state/issues/lem_310B_plan.md` §4.1.

In addition, a small **prerequisite helper** was needed:
`Vertex.rootOf : (t : RootedTree) → Vertex t` (pattern-matches `t =
mk cs` to expose the implicit `cs` argument of the `Vertex.root`
constructor for an arbitrary `t`). Without this helper, the strategy's
`perm Vertex.root = Vertex.root` field failed to elaborate.

Two further adjustments relative to the strategy's recipes:

1. `TreeAutomorphism` was declared as `: Type` explicitly to avoid a
   universe-polymorphism inference failure in
   `LabelledRootedTree.Equiv`'s ∃-quantifier.
2. `Equiv.symm` and `Equiv.trans` use `obtain ⟨ua, la⟩ := a; obtain
   ⟨ub, lb⟩ := b; …; cases hEq` (destructure first, then `cases` on
   the projection equality) because `subst hEq` rejects `a.underlying
   = b.underlying` (the LHS is not a free variable). After
   destructuring, the structure field becomes a free variable and the
   case analysis goes through.

## Result

**SUCCESS** — All deliverables shipped axiom-clean. File grew from
272 LOC to 389 LOC (+117 LOC, within strategy's ~100 LOC budget).

`#print axioms` verified:

```
LabelledRootedTree.Equiv               : [Quot.sound]
LabelledRootedTree.Equiv.refl          : [Quot.sound]
LabelledRootedTree.Equiv.symm          : [Quot.sound]
LabelledRootedTree.Equiv.trans         : [Quot.sound]
LabelledRootedTree.setoid              : [Quot.sound]
TreeAutomorphism.id                    : [Quot.sound]
TreeAutomorphism.trans                 : [Quot.sound]
TreeAutomorphism.symm                  : [Quot.sound]
Vertex.rootOf                          : (none)
```

All within the acceptable `[propext, Classical.choice, Quot.sound]`
set. `Quot.sound` comes through `Equiv`/`Equiv.Perm` ambient
machinery, not from anything we introduced. Sorry count: 0 → 0.

`lake env lean OpenMath/Chapter3/Section300.lean` and
`lake env lean OpenMath/Chapter3.lean` both succeed silently.

## Faithfulness check

### `Vertex.rootOf : (t : RootedTree) → Vertex t`

- Not a Butcher-named concept; project-internal helper extending
  cycle 261's `Vertex.root` constructor to a function of arbitrary
  `t : RootedTree`. Captures the trivial recursion
  `mk _ ↦ Vertex.root`. No textbook divergence.

### `TreeAutomorphism (t : RootedTree)`

- Butcher §300 (around p. 140) implicitly references "tree
  automorphisms" as the symmetry group whose order is `σ(t)`.
  Explicit textbook definition is informal; the rigorous form
  appears in Butcher's `def:300C` discussion of labelled rooted
  trees modulo equivalence.
- Lean statement captures: **weaker** — only root-fixing
  permutation of `Vertex t`, no recursive structure preservation
  on child subtrees.
- Justification for divergence: deliberate weakening to ship the
  Setoid axiom-clean this cycle. Documented prominently in the file
  docstring and in `.prover-state/issues/lem_310B_plan.md` §4.1's
  cycle 263 update subsection. Strengthening to the full recursive
  predicate is queued for cycle 264+ (see Suggested next approach
  below).

### `TreeAutomorphism.id / .trans / .symm`

- Standard group-theoretic API; no textbook ID. Captures: same
  content as Mathlib's `Equiv.refl / .trans / .symm` lifted to
  `TreeAutomorphism`.

### `LabelledRootedTree.Equiv`

- Not a directly-Butcher-named definition; encodes the
  "labellings related by a tree-automorphism" equivalence implicit
  in `def:300C`.
- Lean statement captures: **weaker** than Butcher's quotient —
  uses the weakened `TreeAutomorphism` (see above). The resulting
  `Setoid` is coarser than Butcher's `def:300C` quotient.
- Justification for divergence: same as `TreeAutomorphism`.
  Documented in docstring and issue file.

### `LabelledRootedTree.Equiv.refl / .symm / .trans` and `LabelledRootedTree.setoid`

- The three `Setoid` axioms + the `Setoid` instance. These are
  standard equivalence-relation lemmas. Their content is *correct*
  for the equivalence relation as defined; they faithfully prove
  reflexivity/symmetry/transitivity of `LabelledRootedTree.Equiv`.
  The (acknowledged, documented) weakening lives in the definition
  of `TreeAutomorphism`, not in these lemmas.

### Non-vacuity examples

Three `example` declarations exercising
`LabelledRootedTree.Equiv.refl` on the canonical labelling of
`vertex`, `cherry`, `broom₃`. Pure reflexivity; no surprises.

## Dead ends

1. **Direct `Vertex.root` reference**: the strategy's initial draft
   used `perm Vertex.root = Vertex.root` literally in the structure
   field. Failed with "Application type mismatch: Vertex.root has
   type (mk ?m.2).Vertex but is expected to have type t.Vertex". The
   implicit `cs : List RootedTree` argument of the `Vertex.root`
   constructor is not inferrable from a generic `t : RootedTree`
   because `RootedTree` has no field accessor — every `t` is
   `mk cs` for some `cs`, but the type-checker doesn't auto-unfold.
   Fix: introduce `Vertex.rootOf : (t : RootedTree) → Vertex t`
   helper that pattern-matches `t = mk _ ↦ Vertex.root`. Use
   `Vertex.rootOf t` in `perm_root`'s statement.

2. **`subst hEq` on projection equality**: the strategy's `.symm` /
   `.trans` recipes used `subst hEq` directly on `hEq :
   a.underlying = b.underlying`. Failed with "Tactic `subst` failed:
   invalid equality proof, it is not of the form (x = t) or (t = x)"
   because `a.underlying` is a projection, not a free variable. Fix:
   destructure `a`/`b` first (`obtain ⟨ua, la⟩ := a`) so the
   `underlying` field becomes a free variable, then `cases hEq`
   performs the substitution.

3. **Universe-polymorphism inference failure**: without an explicit
   `: Type` annotation on `TreeAutomorphism`, Lean introduced an
   uninferred universe variable that surfaced as "Failed to infer
   universe levels in type of binder φ" in
   `LabelledRootedTree.Equiv`'s ∃-quantifier. Fix: declare
   `structure TreeAutomorphism (t : RootedTree) : Type where …`.

## Discovery

* **Pattern-match-then-cases dodges projection-equality subst**. For
  any `subst hEq` situation where `hEq` is an equality of structure
  *projections* (e.g. `a.field = b.field`), the canonical workaround
  is `obtain ⟨…⟩ := a; obtain ⟨…⟩ := b; cases hEq`. This converts
  the projection equality into an equality of free variables, which
  `cases` (or `subst`) can then eliminate. Useful pattern to
  remember for future Setoid / Equiv work on structures with one
  type-level field.

* **`Vertex.root` constructor inference is fragile**. The
  `Vertex.root` constructor has implicit `{cs : List RootedTree}`,
  but for a generic `t : RootedTree` (not pattern-matched as
  `mk cs`), Lean's elaborator can't recover `cs`. The
  `Vertex.rootOf` helper is the right pattern for downstream lemmas
  that need to refer to "the root of an arbitrary `t`" without
  pattern-matching at every call site.

* **Equiv.Perm on a generic-`α` type is universe-polymorphic by
  default**. Adding an explicit `: Type` annotation to the parent
  structure is the simplest way to pin the universe.

## Suggested next approach

Per strategy §H, two priority options for cycle 264:

* **Option 1 (recommended)**: **Phase A.2.1** — heterogeneous-labelling
  non-vacuity. Exhibit two genuinely-different labellings of
  `mk [vertex, vertex]` that are related via the leaf-swap
  permutation. This is the natural non-vacuity check for the
  weakened Setoid (proves it's not trivially `Eq`). ~30–50 LOC. The
  technical hurdle: evaluating `Fintype.equivFinOfCardEq` on
  concrete trees may not reduce by `rfl`; may need explicit
  labellings via `Fin.mk` rather than the canonical-labelling
  shortcut.

* **Option 2**: **Phase A.3** — strengthen `TreeAutomorphism` with
  the full recursive structure-preservation field; reprove
  `TreeAutomorphism.{id, trans, symm}` and `LabelledRootedTree.Equiv`
  in the strengthened setting. This is multi-cycle (likely 2–3
  cycles) because it requires a `mutual` block of definitions
  through `List RootedTree` per
  `feedback_rootedtree_nested_induction.md`. Closes the
  σ-faithfulness gap from
  `.prover-state/issues/symmetry_group_equivalence.md`.

* **Option 3**: Proceed to Phase B (`thm:306A` multinomial Taylor)
  per `lem_310B_plan.md` §5. Phase B.1 single-variable two-input
  form is the natural starting point (~100 LOC).

* **Option 4 (pivot)**: ship `lem:342A` (342a) shifted Legendre
  orthogonality on `[0,1]`. Single-cycle clean ship; defer further
  `lem:310B` infrastructure to cycle 265+.

Recommended: **Option 1** — keep §310 momentum, close out the
"non-vacuity for the weakened Setoid" check before pivoting to either
strengthening or Phase B. Heterogeneous non-vacuity is the obvious
next missing piece; without it the Setoid is suspicious (could be a
re-statement of equality). After Option 1 ships, Option 2 vs.
Option 3 becomes the cycle 265 planner's choice.
