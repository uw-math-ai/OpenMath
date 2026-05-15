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

end RootedTree

end OpenMath.Chapter3.Section310
