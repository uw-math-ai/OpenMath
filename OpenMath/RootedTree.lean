import Mathlib.Data.Multiset.Basic
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

/-- The current ordered child list representation. -/
def childrenList : BTree → List BTree
  | .leaf => []
  | .node children => children

/-- Unordered child multiplicities for a rooted tree. This is the intended
future interface; the current `List`-based representation is retained only as
an implementation detail for recursive definitions. -/
def childrenBag (t : BTree) : Multiset BTree :=
  t.childrenList

@[simp] theorem childrenList_leaf : BTree.leaf.childrenList = [] := rfl

@[simp] theorem childrenList_node (children : List BTree) :
    (BTree.node children).childrenList = children := rfl

@[simp] theorem childrenBag_leaf : BTree.leaf.childrenBag = (0 : Multiset BTree) := rfl

@[simp] theorem childrenBag_node (children : List BTree) :
    (BTree.node children).childrenBag = (children : Multiset BTree) := rfl

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

/-! ### Order-5 trees

The 9 rooted trees of order 5 enumerate all order conditions at fifth order.
Reference: Hairer–Nørsett–Wanner, Table II.2.1; Iserles, Section 2.3. -/

/-- `[τ⁴]`: the bushy tree of order `5` (4 leaves). -/
def t5a : BTree := .node [.leaf, .leaf, .leaf, .leaf]

/-- `[τ², [τ]]`: two leaves plus a chain-2 subtree, order `5`. -/
def t5b : BTree := .node [.leaf, .leaf, t2]

/-- `[τ, [τ²]]`: leaf plus bushy-3 subtree, order `5`. -/
def t5c : BTree := .node [.leaf, t3a]

/-- `[τ, [[τ]]]`: leaf plus chain-3 subtree, order `5`. -/
def t5d : BTree := .node [.leaf, t3b]

/-- `[[τ], [τ]]`: two chain-2 subtrees, order `5`. -/
def t5e : BTree := .node [t2, t2]

/-- `[[τ³]]`: bushy-4 grafted to a new root, order `5`. -/
def t5f : BTree := .node [t4a]

/-- `[[τ, [τ]]]`: mixed-4 grafted to a new root, order `5`. -/
def t5g : BTree := .node [t4b]

/-- `[[[τ²]]]`: `t4c` grafted to a new root, order `5`. -/
def t5h : BTree := .node [t4c]

/-- `[[[[τ]]]]`: the chain of order `5`. -/
def t5i : BTree := .node [t4d]

-- Verify order, symmetry, density, beta, alpha for all order-5 trees.
example : t5a.order = 5 := by native_decide
example : t5a.symmetry = 24 := by native_decide
example : t5a.density = 5 := by native_decide
example : t5a.beta = 5 := by native_decide
example : t5a.alpha = 1 := by native_decide

example : t5b.order = 5 := by native_decide
example : t5b.symmetry = 2 := by native_decide
example : t5b.density = 10 := by native_decide
example : t5b.beta = 60 := by native_decide
example : t5b.alpha = 6 := by native_decide

example : t5c.order = 5 := by native_decide
example : t5c.symmetry = 2 := by native_decide
example : t5c.density = 15 := by native_decide
example : t5c.beta = 60 := by native_decide
example : t5c.alpha = 4 := by native_decide

example : t5d.order = 5 := by native_decide
example : t5d.symmetry = 1 := by native_decide
example : t5d.density = 30 := by native_decide
example : t5d.beta = 120 := by native_decide
example : t5d.alpha = 4 := by native_decide

example : t5e.order = 5 := by native_decide
example : t5e.symmetry = 2 := by native_decide
example : t5e.density = 20 := by native_decide
example : t5e.beta = 60 := by native_decide
example : t5e.alpha = 3 := by native_decide

example : t5f.order = 5 := by native_decide
example : t5f.symmetry = 6 := by native_decide
example : t5f.density = 20 := by native_decide
example : t5f.beta = 20 := by native_decide
example : t5f.alpha = 1 := by native_decide

example : t5g.order = 5 := by native_decide
example : t5g.symmetry = 1 := by native_decide
example : t5g.density = 40 := by native_decide
example : t5g.beta = 120 := by native_decide
example : t5g.alpha = 3 := by native_decide

example : t5h.order = 5 := by native_decide
example : t5h.symmetry = 2 := by native_decide
example : t5h.density = 60 := by native_decide
example : t5h.beta = 60 := by native_decide
example : t5h.alpha = 1 := by native_decide

example : t5i.order = 5 := by native_decide
example : t5i.symmetry = 1 := by native_decide
example : t5i.density = 120 := by native_decide
example : t5i.beta = 120 := by native_decide
example : t5i.alpha = 1 := by native_decide

/-! ### Structural Properties -/

/-- The order (number of vertices) of any rooted tree is positive. -/
theorem order_pos (t : BTree) : 0 < t.order := by
  cases t with
  | leaf => simp
  | node children => simp only [order_node]; omega

/-- Alternative characterization: the order of a node equals 1 plus the sum of child orders. -/
theorem order_node_sum (children : List BTree) :
    (BTree.node children).order = 1 + (children.map BTree.order).sum := by
  simp only [order_node]
  induction children with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldr, List.map, List.sum_cons]
    omega

/-- The order of a node depends only on the multiset of its children. -/
theorem order_node_perm {children₁ children₂ : List BTree}
    (hperm : children₁.Perm children₂) :
    (BTree.node children₁).order = (BTree.node children₂).order := by
  have hfold :
      children₁.foldr (fun t n => t.order + n) 0 =
        children₂.foldr (fun t n => t.order + n) 0 :=
    hperm.foldr_eq (lcomm := ⟨fun _ _ _ => by omega⟩) 0
  simp [order_node, hfold]

private theorem foldr_density_pos (children : List BTree)
    (ih : ∀ t ∈ children, 0 < t.density) :
    0 < children.foldr (fun t n => t.density * n) 1 := by
  induction children with
  | nil => simp
  | cons hd tl ih_list =>
    simp only [List.foldr]
    exact Nat.mul_pos (ih hd (.head ..))
      (ih_list (fun t ht => ih t (.tail _ ht)))

/-- The density of any rooted tree is positive. -/
theorem density_pos : ∀ (t : BTree), 0 < t.density
  | .leaf => by simp
  | .node children => by
    simp only [density_node]
    exact Nat.mul_pos (order_pos _) (foldr_density_pos children fun t _ => density_pos t)
termination_by t => sizeOf t
decreasing_by
  have hmem : sizeOf t < sizeOf children :=
    List.sizeOf_lt_of_mem (by assumption)
  have hnode : sizeOf children < sizeOf (BTree.node children) := by simp
  exact Nat.lt_trans hmem hnode

/-- Alternative characterization: the density of a node is its order times the
product of its child densities. -/
theorem density_node_prod (children : List BTree) :
    (BTree.node children).density =
      (BTree.node children).order * (children.map BTree.density).prod := by
  simp only [density_node]
  congr 1
  induction children with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldr, List.map, List.prod_cons]
    rw [ih]

/-- The density of a node depends only on the multiset of its children. -/
theorem density_node_perm {children₁ children₂ : List BTree}
    (hperm : children₁.Perm children₂) :
    (BTree.node children₁).density = (BTree.node children₂).density := by
  rw [density_node_prod, density_node_prod, order_node_perm hperm,
      (hperm.map BTree.density).prod_eq]

private theorem symmetryScan_pos (allChildren remaining : List BTree)
    (ih_sym : ∀ t ∈ allChildren, 0 < t.symmetry)
    (hsub : ∀ t ∈ remaining, t ∈ allChildren) :
    0 < symmetryScan allChildren remaining := by
  induction remaining with
  | nil => simp [symmetryScan]
  | cons hd tl ih_list =>
    simp only [symmetryScan]
    split
    · exact ih_list (fun t ht => hsub t (.tail _ ht))
    · apply Nat.mul_pos
      apply Nat.mul_pos
      · exact Nat.factorial_pos _
      · exact pow_pos (ih_sym hd (hsub hd (.head ..))) _
      · exact ih_list (fun t ht => hsub t (.tail _ ht))

/-- The symmetry of any rooted tree is positive. -/
theorem symmetry_pos : ∀ (t : BTree), 0 < t.symmetry
  | .leaf => by simp
  | .node children => by
    simp only [symmetry_node]
    exact symmetryScan_pos children children
      (fun t _ => symmetry_pos t) (fun t ht => ht)
termination_by t => sizeOf t
decreasing_by
  have hmem : sizeOf t < sizeOf children :=
    List.sizeOf_lt_of_mem (by assumption)
  have hnode : sizeOf children < sizeOf (BTree.node children) := by simp
  exact Nat.lt_trans hmem hnode

end BTree
