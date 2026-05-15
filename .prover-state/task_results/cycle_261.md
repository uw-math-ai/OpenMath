# Cycle 261 Results

## Worked on

Phase A.1 of `lem_310B_plan.md` — `RootedTree.Vertex` inductive predicate,
`RootedTree.vertices` Finset enumeration, and the cardinality identity
`(vertices t).card = order t`. Shipped in a new file
`OpenMath/Chapter3/Section300.lean` (179 LOC).

Per the cycle 261 strategy (Direction 1), this is engineering
infrastructure for the eventual multi-cycle `lem:310B` capstone, not
the lemma itself. `plan.md` and `extraction/formalization_data/lean_status.json`
are deliberately unchanged for this cycle.

## Approach

Followed the cycle 261 strategy §B (Direction 1) and the
`lem_310B_plan.md` §7 entry point. The key design decisions:

1. **Indexed inductive `Vertex : RootedTree → Type`** with two
   constructors:
   - `root {cs : List RootedTree} : Vertex (mk cs)`
   - `child {cs : List RootedTree} (i : Fin cs.length) : Vertex (cs.get i) → Vertex (mk cs)`

2. **DecidableEq via `Classical.decEq`** (Route B from the plan).
   A constructive mutual-decidability block (Route A) was deferred;
   the cardinality theorem doesn't need a computable instance, and
   the strategy explicitly permits Route B. Instance is declared
   right after the `Vertex` inductive so it's in scope before
   `Finset.image (Vertex.child i)` usages.

3. **`vertices` by well-founded recursion** (template:
   `elementaryDiff` in `Section310.lean:187-197`). Each child case
   produces `(vertices (cs.get i)).image (Vertex.child i)`, unioned
   via `Finset.biUnion` over `Fin cs.length`, and `Vertex.root` is
   `insert`ed. Termination via `List.sizeOf_get + Nat.lt_add_left 1`,
   mirroring `elementaryDiff`'s `decreasing_by` block.

4. **`vertices_card` by well-founded recursion on `t`**. Steps:
   - `rw [vertices, Finset.card_insert_of_notMem (Vertex.root_notin_biUnion cs)]`
     reduces to `(biUnion ...).card + 1 = order (mk cs)`.
   - `Finset.card_biUnion + Vertex.child_image_disjoint` reduces
     the biUnion to a Fin-indexed sum of image cards.
   - `Finset.card_image_of_injective + Vertex.child_injective`
     reduces image cards to `(vertices (cs.get i)).card`.
   - Recursive IH `vertices_card (cs.get i)` (well-founded via
     the same `termination_by` block) collapses to `order (cs.get i)`.
   - `orderSum_eq_sum_fin cs` (proved separately by list induction
     using `Fin.sum_univ_succ`) bridges to `orderSum cs`.
   - `omega` closes the final `orderSum cs + 1 = 1 + orderSum cs`.

5. **Three non-vacuity witnesses** on `cherry`, `broom₃`, and
   `mk [vertex, cherry]` — all close by `rw [vertices_card]; rfl`,
   relying on the `Section310.lean` `rfl` reductions of
   `order cherry = 2`, `order broom₃ = 3`,
   `order (mk [vertex, cherry]) = 4`.

## Result

SUCCESS — axiom-clean, sorry-clean, all success criteria met:

- `OpenMath/Chapter3/Section300.lean`: 179 LOC, builds in ~2.6s.
- `lake env lean OpenMath/Chapter3/Section300.lean` exits 0.
- `lake env lean OpenMath/Chapter3.lean` exits 0.
- `lake build OpenMath.Chapter3.Section300` exits 0.
- `grep -c sorry OpenMath/Chapter3/Section300.lean` returns 0.
- Sorry count on `Section{301,310,311}.lean` unchanged at 0.
- `#print axioms OpenMath.Chapter3.Section310.RootedTree.vertices_card`
  returns `[propext, Classical.choice, Quot.sound]`.
- Tautology-scanner regex returns no matches.
- All three non-vacuity examples verify.
- `OpenMath/Chapter3.lean` aggregator imports `Section300`.

## Faithfulness check

Cycle 261 introduced one inductive type, one definition, two helper
defs, six theorems (`idxOpt_root`, `idxOpt_child`, `child_injective`,
`child_image_disjoint`, `root_notin_biUnion`, `orderSum_eq_sum_fin`),
and one main theorem (`vertices_card`).

### `inductive Vertex` (Phase A.1, no Butcher entity ID)

- Entity: engineering scaffold for `lem:310B`. No direct Butcher
  textbook entity. Butcher §300 (p. 139) describes vertices
  informally:
  > "The graph of a rooted tree is described by a set V of vertices
  > and a set E of pairs of vertices."
- Lean statement captures: same content. Each `Vertex (mk cs)` is
  literally a position in the tree — either the root, or `(i, v)`
  where `v` is a vertex of the i-th child. The `child` constructor's
  `Fin cs.length` index plus the dependent `Vertex (cs.get i)` arg
  matches Butcher's "vertex of the i-th subtree" framing verbatim.
- The σ-faithfulness gap (`symmetry_group_equivalence.md`) does NOT
  bite: `Vertex` is the literal vertex set, not the
  symmetry-group-quotient construction.

### `noncomputable def vertices : RootedTree → Finset (Vertex t)`

- Engineering scaffold. The set of vertices as a `Finset` directly
  represents "the set of vertices V" Butcher refers to in §300.
- Lean statement captures: same content. Each vertex appears
  exactly once in the Finset (Finset = duplicate-free by
  construction).

### `theorem vertices_card : ∀ t, (vertices t).card = order t`

- Engineering scaffold; mathematically the "|V(t)| = r(t)" identity.
  Butcher §300 (p. 139) defines `r(t)` as:
  > "the number of vertices of t"
- Lean statement captures: same content — the cardinality of the
  vertex Finset equals the previously-defined `RootedTree.order`.
  Note `order` was already shipped in `Section310.lean` via the
  mutual recursion `order(mk cs) = 1 + orderSum cs`. The cardinality
  identity is the formalization of the textbook *definition* of
  `r(t)`, which is why the proof goes via the recursive
  `vertices = {root} ∪ ⋃ᵢ children_vertices` structure.
- **No definition smuggling.** `order` was *defined* via the
  recursion `1 + Σ r(tᵢ)`, not as `vertices.card`. The theorem
  proves these two formulations agree — genuine mathematical content.

### `idxOpt`, `idxOpt_root`, `idxOpt_child`, `child_injective`, `child_image_disjoint`, `root_notin_biUnion`, `orderSum_eq_sum_fin`

- Pure helper lemmas. No textbook content.
- `child_injective`: constructor injectivity of an indexed
  inductive — Lean-level proof obligation, no textbook claim.
- `child_image_disjoint`: extends constructor injectivity from
  unary `child i` to images under distinct `child i` and `child j` —
  Lean-level proof obligation. Uses `idxOpt` for first-level child
  extraction.
- `root_notin_biUnion`: distinct-constructor disjointness — Lean
  proof obligation.
- `orderSum_eq_sum_fin`: bridges between `Finset.univ` over
  `Fin cs.length` and `orderSum` (List-indexed recursive sum from
  `Section310.lean:102-104`) — bookkeeping lemma, no textbook
  content.

### Hypothesis strength check

- `vertices_card` has zero hypotheses (other than the universal
  quantifier over `t`). Matches Butcher §300 exactly.
- `child_image_disjoint` requires `i ≠ j` — minimal, can't be
  weakened.

### Tautology / identity / definition-smuggling checks: all clear

- No theorem conclusion appears verbatim as one of its hypotheses.
- No proof is a single `exact h`, `:= h_…`, or `:= id`. Tautology
  regex returns no matches.
- `vertices` is `noncomputable def`, no structure-with-Prop-field
  added.

## Dead ends

### Initial DecidableEq placement error

First draft declared `instDecidableEqVertex` AFTER the `Vertex`
namespace (which contains `child_image_disjoint`). Inside that
namespace, `S.image (Vertex.child i)` requires
`DecidableEq (Vertex (mk cs))`, which couldn't be synthesised
because the instance wasn't yet in scope. Fix: move the
`noncomputable instance` immediately after the `inductive Vertex`
declaration, before opening the `Vertex` namespace.

### `Option.noConfusion` direct call fails

First draft of `Vertex.root_notin_biUnion` ended with
`Option.noConfusion (h1.symm.trans h2)` where
`h1 : root.idxOpt = none` and `h2 : root.idxOpt = some i`.
Lean rejected this: `Option.noConfusion` returns
`Option.noConfusionType P _ _`, not directly `False`. Switched to
`cases hv` where `hv : Vertex.child i v = Vertex.root` — Lean 4's
`cases` on an equation between distinct constructors of an indexed
inductive auto-closes the goal via the auto-generated
`Vertex.noConfusion`. Cleaner and avoids the `idxOpt` detour for
this lemma (though `idxOpt` still pays for itself in
`child_image_disjoint`).

### `Fin.sum_univ_succ` motive failure

The `orderSum_eq_sum_fin` proof initially used
`rw [show (t :: ts).length = ts.length + 1 from rfl]` to coerce
`Fin (t :: ts).length` to `Fin (ts.length + 1)` before applying
`Fin.sum_univ_succ`. Lean rejected with a motive-not-type-correct
error: rewriting `(t :: ts).length` inside the sum's binder
type would change the type of the bound variable while the body
`((t :: ts).get i).order` still references `i` at the original
type. Fix: use `show (∑ i : Fin (ts.length + 1), …) = …` to
definitionally convert the goal's binder type, then
`rw [Fin.sum_univ_succ]` applies cleanly. The `show` works because
`(t :: ts).length = ts.length + 1` is definitional (by
`List.length`'s recursive definition), not propositional.

### `cases hv` worked for `Vertex.child i v = Vertex.root`

I was worried that `cases` on an equation between distinct
constructors of an indexed inductive might fail because of the
shared `cs` index. It worked. Lean 4 auto-generates the
`Vertex.noConfusion` term for indexed inductives with the same
target indices and uses it during `cases`. Saved to memory below.

## Discovery

### `Fin.sum_univ_succ` requires explicit `show` to coerce list-length binders

When applying `Fin.sum_univ_succ` to a sum indexed by
`Fin (t :: ts).length`, the rewrite needs the binder type to be
syntactically `Fin (n + 1)`. `(t :: ts).length` is definitionally
`ts.length + 1` but does NOT automatically reduce during the
pattern-matching of `rw`. The workaround is to prepend a
`show (∑ i : Fin (ts.length + 1), …) = …` which uses definitional
equality to coerce the binder type explicitly. After that,
`rw [Fin.sum_univ_succ]` matches.

This pattern will recur whenever Phase A or later cycles need to
manipulate `Fin (cs.length)`-indexed sums via `Fin.sum_univ_succ`
or `Fin.sum_univ_castSucc`. Save as memory for reuse.

### `cases h` works on distinct-constructor equality of indexed inductives (with matching index)

For `inductive Vertex : RootedTree → Type | root | child i _`, an
equation `h : Vertex.child i v = Vertex.root` in `Vertex (mk cs)`
can be closed via `cases h`. Lean 4 auto-generates
`Vertex.noConfusion` for indexed inductives where the target
indices match (here both sides are `Vertex (mk cs)`), and `cases`
uses it to derive False from distinct constructors. This is
robust even without manually invoking `Vertex.noConfusion` (which
has a clunkier API — returns `noConfusionType`, not `False`
directly).

### `Classical.decEq` is the right fallback for nested-inductive `DecidableEq`

The plan flagged Route B (Classical.decEq) as a clean fallback for
the `Vertex` DecidableEq. It works because (a) `vertices` is
`noncomputable` anyway (the Finset uses Classical for image
deduplication), and (b) `Classical.choice` is already in the
project's axiom baseline. Route A (mutual structural
`decEqVertex`) would have been ~30 LOC and risked the index-shift
typing issues that derailed earlier sketches of
`verticesFromChildren`. Saved ~30 LOC by using Route B.

## Suggested next approach

**Cycle 262 (recommended): Phase A.2 of `lem_310B_plan.md` —
`LabelledRootedTree`.** Cycle 261's `Vertex` type is the natural
substrate. The labelled-tree structure can be built as:

```lean
structure LabelledRootedTree (n : ℕ) where
  tree : RootedTree
  label : Vertex tree ≃ Fin n  -- vertex-to-label bijection
  -- with implicit constraint label.val ∈ Fin (order tree)
```

Or as a quotient: `LabelledRootedTree = Σ t : RootedTree, Vertex t ≃ Fin (order t)`.
Both formulations require `Vertex.equivOfCardEq` or similar — a
small extension of cycle 261's API. The plan's §A.2 (LOC budget
150-200) should be achievable in one cycle.

**Alternative for cycle 262**: extend cycle 261's API with
`Vertex.subtree : (t : RootedTree) → (v : Vertex t) → RootedTree`
and `Vertex.subtreeOrder`. These are needed for the orbit-counting
machinery in Phase C/D and would be a smaller (~50 LOC) ship.

**Do not start cycle 262 by writing Phase F (the `lem:310B`
capstone) sorry-first scaffolds.** Cycle 200 rollback discipline
applies — Phase F needs Phases A through E proved axiom-clean
first.

**Memory updates to save**:
- `feedback-fin-sum-univ-succ-coerce`: show-to-Fin-n+1 coercion
  pattern for Fin.sum_univ_succ with List.length binders.
- `feedback-classical-deceq-nested-inductive`: Route B vs Route A
  decision for indexed-inductive DecidableEq.
