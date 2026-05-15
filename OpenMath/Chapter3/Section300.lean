import OpenMath.Chapter3.Section310
import Mathlib.Algebra.BigOperators.Fin

/-!
# Butcher §300 — Vertices of rooted trees

Phase A.1 of `lem_310B_plan.md`: the inductive `Vertex` type, the
`Finset` enumeration `vertices`, and the cardinality identity
`(vertices t).card = order t`.

## Faithfulness

Butcher §300 (p. 139) describes the vertex set of a rooted tree
informally as "the points of t". Our inductive `Vertex` captures
this: each vertex is either the root of `t`, or a vertex of one of
its children. The `child` constructor packages a child index
`i : Fin cs.length` together with a vertex `v : Vertex (cs.get i)`
of the `i`-th child.

The cardinality identity `vertices_card` matches Butcher's
definition of `r(t)` as "the number of vertices of t" (§300, p. 139).

## Design choices

* `DecidableEq (Vertex t)` is provided noncomputably via
  `Classical.decEq`. A constructive decidable-equality block
  (mirroring `decEqTree`/`decEqList` from `Section301.lean`) is
  deferred — `vertices` is `noncomputable` and the cardinality
  identity does not need a computable instance.
* `vertices` is defined by well-founded recursion (template:
  `elementaryDiff` in `Section310.lean`). The `mk cs` step
  recurses into each child `cs.get i` via `Vertex.child i` images,
  unioned with the singleton `{Vertex.root}`.
* `vertices_card` is proved by well-founded recursion. At the
  leaves (`mk []`), `vertices = {root}` and `card = 1 = order (mk [])`.
-/

namespace OpenMath.Chapter3.Section310

namespace RootedTree

/-- The type of vertices of a rooted tree.

`Vertex.root` is the root; `Vertex.child i v` is the vertex `v` sitting
inside the `i`-th child of the root. -/
inductive Vertex : RootedTree → Type
  | root {cs : List RootedTree} : Vertex (mk cs)
  | child {cs : List RootedTree} (i : Fin cs.length) :
      Vertex (cs.get i) → Vertex (mk cs)

/-- Decidable equality on `Vertex t` via classical choice. Declared
ahead of `Vertex.child_image_disjoint` and `vertices` because both rely
on `Finset.image` over `Vertex (mk cs)`. -/
noncomputable instance instDecidableEqVertex {t : RootedTree} :
    DecidableEq (Vertex t) :=
  Classical.decEq _

namespace Vertex

/-- The first-level child index of a vertex: `none` for the root,
`some i` for `child i _`. Used to distinguish root-vs-child and to
extract the child index of a non-root vertex. -/
def idxOpt : {cs : List RootedTree} → Vertex (mk cs) → Option (Fin cs.length)
  | _, root => none
  | _, child i _ => some i

theorem idxOpt_root {cs : List RootedTree} :
    (root : Vertex (mk cs)).idxOpt = none := rfl

theorem idxOpt_child {cs : List RootedTree} (i : Fin cs.length)
    (v : Vertex (cs.get i)) :
    (child i v : Vertex (mk cs)).idxOpt = some i := rfl

/-- The root vertex of `t : RootedTree`, exposed as a function of `t`.
Pattern-matches `t = mk cs` so `Vertex.root`'s implicit `cs` is
inferrable from a generic `t`. -/
def rootOf : (t : RootedTree) → Vertex t
  | mk _ => Vertex.root

/-- `Vertex.child i` is injective in its second argument. -/
theorem child_injective {cs : List RootedTree} (i : Fin cs.length) :
    Function.Injective (Vertex.child (cs := cs) i) := by
  intro v w h
  cases h
  rfl

/-- The images of `Vertex.child i` and `Vertex.child j` over arbitrary
child-vertex Finsets are disjoint when `i ≠ j`. -/
theorem child_image_disjoint {cs : List RootedTree}
    {i j : Fin cs.length} (hij : i ≠ j)
    (S : Finset (Vertex (cs.get i))) (T : Finset (Vertex (cs.get j))) :
    Disjoint (S.image (Vertex.child i)) (T.image (Vertex.child j)) := by
  rw [Finset.disjoint_left]
  intro v hvS hvT
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hvS
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hvT
  apply hij
  have h1 : v.idxOpt = some i := by rw [← ha]; rfl
  have h2 : v.idxOpt = some j := by rw [← hb]; rfl
  exact Option.some.inj (h1.symm.trans h2)

end Vertex

/-- The Finset of all vertices of a rooted tree.

Recursive structure: for `t = mk cs`, the vertex set is
`{root} ∪ ⋃ᵢ (Vertex.child i) '' vertices (cs.get i)`. -/
noncomputable def vertices : (t : RootedTree) → Finset (Vertex t)
  | mk cs =>
      insert Vertex.root
        ((Finset.univ : Finset (Fin cs.length)).biUnion
          (fun i => (vertices (cs.get i)).image (Vertex.child i)))
termination_by t => t
decreasing_by
  simp_wf
  exact Nat.lt_add_left 1 (List.sizeOf_get cs i)

/-- The biUnion-of-images of `Vertex.child` does not contain
`Vertex.root` — every element of the biUnion is constructed by some
`Vertex.child i _`. -/
theorem Vertex.root_notin_biUnion (cs : List RootedTree) :
    (Vertex.root : Vertex (mk cs)) ∉
      (Finset.univ : Finset (Fin cs.length)).biUnion
        (fun i => (vertices (cs.get i)).image (Vertex.child i)) := by
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hi
  cases hv

/-- Helper: `∑ i : Fin cs.length, order (cs.get i) = orderSum cs`. -/
theorem orderSum_eq_sum_fin (cs : List RootedTree) :
    (∑ i : Fin cs.length, order (cs.get i)) = orderSum cs := by
  induction cs with
  | nil => simp [orderSum]
  | cons t ts ih =>
      show (∑ i : Fin (ts.length + 1), order ((t :: ts).get i)) = orderSum (t :: ts)
      rw [Fin.sum_univ_succ]
      show order t + (∑ i : Fin ts.length, order (ts.get i)) = orderSum (t :: ts)
      rw [ih]
      rfl

/-- **(lem:310B Phase A.1)** The number of vertices of a rooted tree
equals its order.

The proof is well-founded recursion on `t`: for `t = mk cs`,
`vertices (mk cs) = {root} ∪ ⋃ᵢ (Vertex.child i) '' vertices (cs.get i)`,
so its cardinality is `1 + ∑ᵢ (vertices (cs.get i)).card`. By IH, the
inner card is `order (cs.get i)`, and the sum equals `orderSum cs`,
yielding `1 + orderSum cs = order (mk cs)`. -/
theorem vertices_card : ∀ t : RootedTree, (vertices t).card = order t
  | mk cs => by
      have IH : ∀ i : Fin cs.length,
          (vertices (cs.get i)).card = order (cs.get i) :=
        fun i => vertices_card (cs.get i)
      rw [vertices, Finset.card_insert_of_notMem (Vertex.root_notin_biUnion cs)]
      have hcard_eq : ∀ i : Fin cs.length,
          ((vertices (cs.get i)).image (Vertex.child i)).card =
            (vertices (cs.get i)).card :=
        fun i => Finset.card_image_of_injective _ (Vertex.child_injective i)
      rw [Finset.card_biUnion (fun i _ j _ hij =>
            Vertex.child_image_disjoint hij _ _)]
      simp_rw [hcard_eq, IH]
      rw [orderSum_eq_sum_fin cs]
      show orderSum cs + 1 = 1 + orderSum cs
      omega
termination_by t => t
decreasing_by
  simp_wf
  exact Nat.lt_add_left 1 (List.sizeOf_get cs i)

-- §300 vertex-set non-vacuity witnesses (Phase A.1)

example : (RootedTree.vertices RootedTree.cherry).card = 2 := by
  rw [RootedTree.vertices_card]; rfl

example : (RootedTree.vertices RootedTree.broom₃).card = 3 := by
  rw [RootedTree.vertices_card]; rfl

example : (RootedTree.vertices
            (RootedTree.mk [RootedTree.vertex, RootedTree.cherry])).card = 4 := by
  rw [RootedTree.vertices_card]; rfl

/-! ### Phase A.2 (partial) — `LabelledRootedTree` + canonical labelling

`Vertex.mem_vertices` proves the completeness of the `vertices`
enumeration; this powers a `Fintype (Vertex t)` instance, in turn
yielding `Fintype.card (Vertex t) = order t` as a reframing of
`vertices_card`. We then introduce the `LabelledRootedTree`
structure (a rooted tree with a chosen `Vertex ≃ Fin (order)`
bijection) and the canonical labelling derived from the `Fintype`
infrastructure via `Fintype.equivFinOfCardEq`.

Faithfulness divergence: Butcher's `def:300C` treats labelled rooted
trees up to tree-automorphism (a *quotient* by the symmetry group).
The structure exposed here singles out one *raw* labelling per
underlying tree; the tree-automorphism `Setoid` recovering Butcher's
quotient is deferred to cycle 263+ per
`.prover-state/issues/lem_310B_plan.md` §4.1.

Cycle 263 update: `TreeAutomorphism t` is weakened to "permutation of
`Vertex t` fixing `root`" (only one structure-preservation field), which
is strictly weaker than Butcher's full tree-automorphism group. The
σ-faithfulness orbit-count identity (Phase A.3 per
`.prover-state/issues/lem_310B_plan.md` §4.1) is NOT claimed by
`LabelledRootedTree.setoid`. Strengthening to the full recursive
structure preservation is deferred to a future cycle. -/

/-- Completeness: every vertex of `t` is in the `vertices t` Finset. -/
theorem Vertex.mem_vertices : ∀ {t : RootedTree} (v : Vertex t),
    v ∈ vertices t
  | mk cs, Vertex.root => by
      rw [vertices]
      exact Finset.mem_insert_self _ _
  | mk cs, Vertex.child i v => by
      rw [vertices]
      refine Finset.mem_insert_of_mem ?_
      rw [Finset.mem_biUnion]
      refine ⟨i, Finset.mem_univ _, ?_⟩
      rw [Finset.mem_image]
      exact ⟨v, Vertex.mem_vertices v, rfl⟩
termination_by t _ => t
decreasing_by
  simp_wf
  exact Nat.lt_add_left 1 (List.sizeOf_get cs i)

/-- `Vertex t` is a (noncomputable) finite type with `vertices t` as
its universe Finset. -/
noncomputable instance instFintypeVertex (t : RootedTree) :
    Fintype (Vertex t) :=
  ⟨vertices t, fun v => Vertex.mem_vertices v⟩

/-- `Fintype.card (Vertex t) = order t`, an `API`-side reframing of
cycle 261's `vertices_card`. -/
theorem Fintype.card_vertex_eq_order (t : RootedTree) :
    Fintype.card (Vertex t) = order t := by
  show (vertices t).card = order t
  exact vertices_card t

/-- A rooted tree together with a chosen bijective labelling of its
vertices by `Fin (order t)`. The labelling is a structural choice
(not canonically determined by `t`); two labellings related by a
tree-automorphism are textbook-equivalent, but the tree-automorphism
`Setoid` is deferred to cycle 263+. -/
structure LabelledRootedTree where
  underlying : RootedTree
  labelling : Vertex underlying ≃ Fin (order underlying)

/-- The canonical labelling of a rooted tree, derived from the
`Fintype` instance on `Vertex t` via Mathlib's
`Fintype.equivFinOfCardEq`. Engineering scaffold; Butcher does not
single out a canonical labelling. -/
noncomputable def canonicalLabelling (t : RootedTree) :
    Vertex t ≃ Fin (order t) :=
  Fintype.equivFinOfCardEq (Fintype.card_vertex_eq_order t)

/-- The canonical labelling of the singleton tree `vertex`. -/
noncomputable def canonicalVertex : LabelledRootedTree where
  underlying := vertex
  labelling := canonicalLabelling vertex

/-- The canonical labelling of `cherry`. -/
noncomputable def canonicalCherry : LabelledRootedTree where
  underlying := cherry
  labelling := canonicalLabelling cherry

/-- The canonical labelling of `broom₃`. -/
noncomputable def canonicalBroom₃ : LabelledRootedTree where
  underlying := broom₃
  labelling := canonicalLabelling broom₃

example : canonicalVertex.underlying.order = 1 := rfl
example : canonicalCherry.underlying.order = 2 := rfl
example : canonicalBroom₃.underlying.order = 3 := rfl

/-! ### Phase A.2 completion — `TreeAutomorphism` + `LabelledRootedTree.setoid`

The tree-automorphism `Setoid` on `LabelledRootedTree` is built from a
*weakened* `TreeAutomorphism` predicate: a permutation of `Vertex t`
that fixes `Vertex.root`. This is strictly weaker than Butcher's
tree-automorphism group, which additionally recursively preserves
each subtree's structure. The weakening is deliberate to dodge the
nested-inductive mutual-recursion pitfall in
`feedback_rootedtree_nested_induction.md`; it makes the Setoid
**coarser** than Butcher's quotient, and the σ-faithfulness orbit
count `r(t)!/σ(t)` is NOT claimed here. -/

/-- A *(weak) tree automorphism* of `t` is a permutation of `Vertex t`
that fixes the root. Strictly weaker than Butcher's tree-automorphism
group (full recursive structure preservation is deferred — see file
docstring). -/
structure TreeAutomorphism (t : RootedTree) : Type where
  perm : Equiv.Perm (Vertex t)
  perm_root : perm (Vertex.rootOf t) = Vertex.rootOf t

/-- The identity (weak) tree automorphism. -/
def TreeAutomorphism.id (t : RootedTree) : TreeAutomorphism t where
  perm := Equiv.refl _
  perm_root := rfl

/-- Composition of (weak) tree automorphisms. -/
def TreeAutomorphism.trans {t : RootedTree}
    (φ ψ : TreeAutomorphism t) : TreeAutomorphism t where
  perm := φ.perm.trans ψ.perm
  perm_root := by
    show ψ.perm (φ.perm (Vertex.rootOf t)) = Vertex.rootOf t
    rw [φ.perm_root, ψ.perm_root]

/-- Inverse of a (weak) tree automorphism. -/
def TreeAutomorphism.symm {t : RootedTree}
    (φ : TreeAutomorphism t) : TreeAutomorphism t where
  perm := φ.perm.symm
  perm_root := by
    have h := congrArg φ.perm.symm φ.perm_root
    rw [Equiv.symm_apply_apply] at h
    exact h.symm

/-- Two labelled rooted trees are equivalent if they share an underlying
tree and one labelling is obtained from the other by composing with some
(weak) tree-automorphism.

Encoded pointwise to avoid dependent-typing issues with `Equiv` equality
across heterogeneous `Vertex` types. -/
def LabelledRootedTree.Equiv (a b : LabelledRootedTree) : Prop :=
  ∃ (h : a.underlying = b.underlying)
    (φ : TreeAutomorphism a.underlying),
    ∀ (v : Vertex a.underlying),
      a.labelling v = (h ▸ b.labelling) (φ.perm v)

theorem LabelledRootedTree.Equiv.refl (a : LabelledRootedTree) :
    LabelledRootedTree.Equiv a a := by
  refine ⟨rfl, TreeAutomorphism.id _, ?_⟩
  intro v
  rfl

theorem LabelledRootedTree.Equiv.symm {a b : LabelledRootedTree}
    (hab : LabelledRootedTree.Equiv a b) :
    LabelledRootedTree.Equiv b a := by
  obtain ⟨ua, la⟩ := a
  obtain ⟨ub, lb⟩ := b
  obtain ⟨hEq, φ, hLab⟩ := hab
  cases hEq
  refine ⟨rfl, φ.symm, ?_⟩
  intro v
  have h := hLab (φ.perm.symm v)
  show lb v = la (φ.perm.symm v)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem LabelledRootedTree.Equiv.trans {a b c : LabelledRootedTree}
    (hab : LabelledRootedTree.Equiv a b)
    (hbc : LabelledRootedTree.Equiv b c) :
    LabelledRootedTree.Equiv a c := by
  obtain ⟨ua, la⟩ := a
  obtain ⟨ub, lb⟩ := b
  obtain ⟨uc, lc⟩ := c
  obtain ⟨hEq_ab, φ, hLab_ab⟩ := hab
  obtain ⟨hEq_bc, ψ, hLab_bc⟩ := hbc
  cases hEq_ab
  cases hEq_bc
  refine ⟨rfl, φ.trans ψ, ?_⟩
  intro v
  show la v = lc (ψ.perm (φ.perm v))
  rw [hLab_ab v, hLab_bc (φ.perm v)]

/-- The `Setoid` of labelled rooted trees modulo (weak) tree automorphism.

Faithfulness divergence: this Setoid is **coarser** than Butcher's
`def:300C` quotient (which uses the full recursive tree-automorphism
group). See the file docstring and
`.prover-state/issues/lem_310B_plan.md` §4.1. -/
instance LabelledRootedTree.setoid : Setoid LabelledRootedTree where
  r := LabelledRootedTree.Equiv
  iseqv := ⟨LabelledRootedTree.Equiv.refl,
            LabelledRootedTree.Equiv.symm,
            LabelledRootedTree.Equiv.trans⟩

-- Non-vacuity: reflexivity on each canonical labelling.
example : LabelledRootedTree.Equiv canonicalVertex canonicalVertex :=
  LabelledRootedTree.Equiv.refl _

example : LabelledRootedTree.Equiv canonicalCherry canonicalCherry :=
  LabelledRootedTree.Equiv.refl _

example : LabelledRootedTree.Equiv canonicalBroom₃ canonicalBroom₃ :=
  LabelledRootedTree.Equiv.refl _

/-! ### Phase A.2 — heterogeneous-labelling non-vacuity (cycle 264)

The reflexivity-only witnesses above are insufficient to demonstrate the
Setoid is non-trivial: they hold for the trivial `Eq` setoid too. The
following definitions witness two *genuinely-distinct* labellings of the
two-leaf tree `mk [vertex, vertex]` that are nonetheless identified by the
weak-`TreeAutomorphism` Setoid under the leaf-swap permutation. -/

/-- The two-leaf tree, definitionally identical to `broom₃`. The
alias clarifies the role of vertex naming in the leaf-swap construction. -/
def doubleVertex : RootedTree := mk [vertex, vertex]

/-- The leaf at child position `0` of `doubleVertex`. -/
def leftLeaf : Vertex doubleVertex :=
  Vertex.child ⟨0, by show 0 < 2; omega⟩ Vertex.root

/-- The leaf at child position `1` of `doubleVertex`. -/
def rightLeaf : Vertex doubleVertex :=
  Vertex.child ⟨1, by show 1 < 2; omega⟩ Vertex.root

theorem leftLeaf_ne_rightLeaf : leftLeaf ≠ rightLeaf := by
  intro h
  cases h

theorem leftLeaf_ne_root : leftLeaf ≠ Vertex.rootOf doubleVertex := by
  intro h
  cases h

theorem rightLeaf_ne_root : rightLeaf ≠ Vertex.rootOf doubleVertex := by
  intro h
  cases h

/-- The leaf-swap (weak) tree automorphism of `doubleVertex`: swap the
two leaves, fix the root. `noncomputable` because `Equiv.swap` requires
`DecidableEq` on `Vertex`, and `instDecidableEqVertex` is noncomputable. -/
noncomputable def leafSwapAutomorphism : TreeAutomorphism doubleVertex where
  perm := Equiv.swap leftLeaf rightLeaf
  perm_root :=
    Equiv.swap_apply_of_ne_of_ne
      (fun h => leftLeaf_ne_root h.symm)
      (fun h => rightLeaf_ne_root h.symm)

/-- The canonical labelling of `doubleVertex`. -/
noncomputable def canonicalDoubleVertex : LabelledRootedTree where
  underlying := doubleVertex
  labelling := canonicalLabelling doubleVertex

/-- The canonical labelling of `doubleVertex` post-composed with the
leaf-swap permutation. Distinct from the canonical labelling as a
function (witnessed by `labellings_distinct`) but Setoid-equivalent to
it under the leaf-swap automorphism (witnessed by
`canonical_equiv_swapped`). -/
noncomputable def swappedDoubleVertex : LabelledRootedTree where
  underlying := doubleVertex
  labelling :=
    (Equiv.swap leftLeaf rightLeaf).trans (canonicalLabelling doubleVertex)

theorem canonical_equiv_swapped :
    LabelledRootedTree.Equiv canonicalDoubleVertex swappedDoubleVertex := by
  refine ⟨rfl, leafSwapAutomorphism, ?_⟩
  intro v
  show canonicalLabelling doubleVertex v =
      ((Equiv.swap leftLeaf rightLeaf).trans (canonicalLabelling doubleVertex))
        (Equiv.swap leftLeaf rightLeaf v)
  simp [Equiv.trans_apply, Equiv.swap_apply_self]

theorem labellings_distinct :
    canonicalDoubleVertex.labelling ≠ swappedDoubleVertex.labelling := by
  intro h
  apply leftLeaf_ne_rightLeaf
  apply (canonicalLabelling doubleVertex).injective
  have heval : canonicalDoubleVertex.labelling leftLeaf =
               swappedDoubleVertex.labelling leftLeaf :=
    congrArg (fun e : Vertex doubleVertex ≃ Fin (order doubleVertex) =>
                e leftLeaf) h
  simpa [canonicalDoubleVertex, swappedDoubleVertex,
         Equiv.trans_apply, Equiv.swap_apply_left] using heval

/-- Bottom-line non-vacuity: the weak-`TreeAutomorphism` Setoid genuinely
identifies distinct labellings. The conjunction is stated against the two
named witnesses (not behind an existential) because
`a.labelling ≠ b.labelling` is heterogeneously typed when `a.underlying`
and `b.underlying` are not unified; with concrete `canonicalDoubleVertex`
and `swappedDoubleVertex` both reducing to `doubleVertex`, the `≠` is
well-typed. -/
example :
    LabelledRootedTree.Equiv canonicalDoubleVertex swappedDoubleVertex ∧
      canonicalDoubleVertex.labelling ≠ swappedDoubleVertex.labelling :=
  ⟨canonical_equiv_swapped, labellings_distinct⟩

end RootedTree

end OpenMath.Chapter3.Section310
