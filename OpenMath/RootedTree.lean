import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-- Rooted trees in the sense of Butcher, Section 300.
`leaf` is the elementary tree `τ`.
`node children` attaches the list of subtrees `children` to a new root.

Children are stored as a `List`, so two trees that differ only by child order
are distinct values in this fallback representation. -/
inductive BTree : Type
  | leaf : BTree
  | node : List BTree → BTree
  deriving BEq, Repr

namespace BTree

/-- Order `r(t)`: the number of vertices of the rooted tree `t`. -/
def order : BTree → ℕ
  | .leaf => 1
  | .node children => 1 + children.foldr (fun t n => t.order + n) 0
termination_by t => sizeOf t
decreasing_by
  have hmem : sizeOf t < sizeOf children := by
    exact List.sizeOf_lt_of_mem (a := t) (by assumption)
  have hnode : sizeOf children < sizeOf (BTree.node children) := by
    simp
  exact Nat.lt_trans hmem hnode

/-- Density `γ(t)`: the product of the orders of all rooted subtrees of `t`. -/
def density : BTree → ℕ
  | .leaf => 1
  | .node children =>
      (BTree.node children).order * children.foldr (fun t n => t.density * n) 1
termination_by t => sizeOf t
decreasing_by
  have hmem : sizeOf t < sizeOf children := by
    exact List.sizeOf_lt_of_mem (a := t) (by assumption)
  have hnode : sizeOf children < sizeOf (BTree.node children) := by
    simp
  exact Nat.lt_trans hmem hnode

mutual
  /-- Symmetry `σ(t)`: the order of the automorphism group of `t`.
  In the list-based fallback, this is computed by scanning the child list from the right
  and adding one factor for the final occurrence of each isomorphism class. -/
  def symmetry : BTree → ℕ
    | .leaf => 1
    | .node children => symmetryScan children children
  termination_by t => sizeOf t + 1
  decreasing_by
    simp

  /-- Auxiliary scan used to define `symmetry` for the list-based child representation. -/
  def symmetryScan (allChildren : List BTree) : List BTree → ℕ
    | [] => 1
    | t :: ts =>
        let tail := symmetryScan allChildren ts
        if ts.contains t then
          tail
        else
          (allChildren.count t).factorial * t.symmetry ^ (allChildren.count t) * tail
  termination_by remaining => sizeOf remaining
  decreasing_by
    try simp
    have hpos : 0 < sizeOf ts := by
      cases ts <;> simp
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Nat.lt_add_of_pos_right (n := sizeOf t + 1) (k := sizeOf ts) hpos)
end

/-- `β(t) = r(t)! / σ(t)`: the number of distinct labellings. -/
def beta (t : BTree) : ℕ :=
  t.order.factorial / t.symmetry

/-- `α(t) = r(t)! / (σ(t) * γ(t))`: the number of monotone labellings. -/
def alpha (t : BTree) : ℕ :=
  t.order.factorial / (t.symmetry * t.density)

@[simp] theorem order_leaf : BTree.leaf.order = 1 := by
  unfold order
  rfl

@[simp] theorem symmetry_leaf : BTree.leaf.symmetry = 1 := by
  unfold symmetry
  rfl

@[simp] theorem density_leaf : BTree.leaf.density = 1 := by
  unfold density
  rfl

@[simp] theorem order_node (children : List BTree) :
    (BTree.node children).order = 1 + children.foldr (fun t n => t.order + n) 0 := by
  simp [order]

@[simp] theorem symmetry_node (children : List BTree) :
    (BTree.node children).symmetry = symmetryScan children children := by
  simp [symmetry]

@[simp] theorem density_node (children : List BTree) :
    (BTree.node children).density =
      (BTree.node children).order * children.foldr (fun t n => t.density * n) 1 := by
  simp [density]

/-- `[τ]`: the unique tree of order `2`. -/
def t2 : BTree := .node [.leaf]

/-- `[τ²]`: the bushy tree of order `3`. -/
def t3a : BTree := .node [.leaf, .leaf]

/-- `[[τ]]`: the chain of order `3`. -/
def t3b : BTree := .node [t2]

/-- `[τ³]`: the bushy tree of order `4`. -/
def t4a : BTree := .node [.leaf, .leaf, .leaf]

/-- `[τ, [τ]]`: the mixed tree of order `4`. -/
def t4b : BTree := .node [.leaf, t2]

/-- `[[τ²]]`: the rooted tree obtained by grafting `t3a` to a new root. -/
def t4c : BTree := .node [t3a]

/-- `[[[τ]]]`: the chain of order `4`. -/
def t4d : BTree := .node [t3b]

example : BTree.leaf.order = 1 := by
  exact order_leaf

example : BTree.leaf.symmetry = 1 := by
  exact symmetry_leaf

example : BTree.leaf.density = 1 := by
  exact density_leaf

example : t2.order = 2 := by native_decide

example : t2.symmetry = 1 := by native_decide

example : t2.density = 2 := by native_decide

example : t3a.order = 3 := by native_decide

example : t3a.symmetry = 2 := by native_decide

example : t3a.density = 3 := by native_decide

example : t3b.order = 3 := by native_decide

example : t3b.symmetry = 1 := by native_decide

example : t3b.density = 6 := by native_decide

example : t4a.order = 4 := by native_decide

example : t4a.symmetry = 6 := by native_decide

example : t4a.density = 4 := by native_decide

example : t4b.order = 4 := by native_decide

example : t4b.symmetry = 1 := by native_decide

example : t4b.density = 8 := by native_decide

example : t4c.order = 4 := by native_decide

example : t4c.symmetry = 2 := by native_decide

example : t4c.density = 12 := by native_decide

example : t4d.order = 4 := by native_decide

example : t4d.symmetry = 1 := by native_decide

example : t4d.density = 24 := by native_decide

end BTree
