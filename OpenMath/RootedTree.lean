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
  deriving Repr

namespace BTree

mutual
  private def beq : BTree → BTree → Bool
    | .leaf, .leaf => true
    | .node children₁, .node children₂ => beqList children₁ children₂
    | _, _ => false

  private def beqList : List BTree → List BTree → Bool
    | [], [] => true
    | t₁ :: ts₁, t₂ :: ts₂ => beq t₁ t₂ && beqList ts₁ ts₂
    | _, _ => false
end

instance : BEq BTree := ⟨beq⟩

mutual
  private theorem beq_eq_true_iff : ∀ t₁ t₂ : BTree, beq t₁ t₂ = true ↔ t₁ = t₂
    | .leaf, .leaf => by simp [beq]
    | .leaf, .node _ => by simp [beq]
    | .node _, .leaf => by simp [beq]
    | .node children₁, .node children₂ => by
        simpa [beq] using beqList_eq_true_iff children₁ children₂

  private theorem beqList_eq_true_iff :
      ∀ children₁ children₂ : List BTree, beqList children₁ children₂ = true ↔ children₁ = children₂
    | [], [] => by simp [beqList]
    | [], _ :: _ => by simp [beqList]
    | _ :: _, [] => by simp [beqList]
    | t₁ :: ts₁, t₂ :: ts₂ => by
        simp [beqList, beq_eq_true_iff t₁ t₂, beqList_eq_true_iff ts₁ ts₂]
end

instance : ReflBEq BTree where
  rfl := by
    intro t
    exact (beq_eq_true_iff t t).2 rfl

instance : LawfulBEq BTree where
  eq_of_beq := by
    intro a b h
    exact (beq_eq_true_iff a b).1 h

noncomputable instance : DecidableEq BTree := Classical.decEq _

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

/-- Bag-first recovery witness for the order-3 classifier. This records only
the canonical child bag and the low-order facts needed downstream. -/
inductive OrderThreeRecoveryWitness (t : BTree) : Type where
  | chain3 (d : BTree)
      (hbag : t.childrenBag = (BTree.node [d]).childrenBag)
      (hd : d.order = 2) :
      OrderThreeRecoveryWitness t
  | bushy3 (d₁ d₂ : BTree)
      (hbag : t.childrenBag = (BTree.node [d₁, d₂]).childrenBag)
      (hd₁ : d₁.order = 1) (hd₂ : d₂.order = 1) :
      OrderThreeRecoveryWitness t

/-- Package the order-3 rooted-tree classification in recovery-first form. -/
theorem order_three_recovery_witness_nonempty (t : BTree) (ht : t.order = 3) :
    Nonempty (OrderThreeRecoveryWitness t) := by
  cases t with
  | leaf => simp at ht
  | node children =>
    simp only [order_node] at ht
    have hfoldr : children.foldr (fun c n => c.order + n) 0 = 2 := by omega
    cases children with
    | nil => simp at hfoldr
    | cons hd tl =>
      simp only [List.foldr] at hfoldr
      have hhd_pos : 0 < hd.order := by
        cases hd <;> simp [order_node]
      cases tl with
      | nil =>
        exact ⟨.chain3 hd rfl (by simpa using hfoldr)⟩
      | cons hd2 tl2 =>
        have hhd2_pos : 0 < hd2.order := by
          cases hd2 <;> simp [order_node]
        have hhd : hd.order = 1 := by
          simp only [List.foldr] at hfoldr
          omega
        have hrest : hd2.order + tl2.foldr (fun c n => c.order + n) 0 = 1 := by
          simp only [List.foldr] at hfoldr
          omega
        cases tl2 with
        | nil =>
          exact ⟨.bushy3 hd hd2 rfl hhd (by simpa using hrest)⟩
        | cons hd3 tl3 =>
          simp only [List.foldr] at hrest
          have hhd3_pos : 0 < hd3.order := by
            cases hd3 <;> simp [order_node]
          omega

/-- Noncomputably choose the recovery-first order-3 witness. -/
noncomputable def order_three_recovery_witness (t : BTree) (ht : t.order = 3) :
    OrderThreeRecoveryWitness t :=
  Classical.choice (order_three_recovery_witness_nonempty t ht)

/-- Legacy list-payload witness for order-3 rooted trees. The payload records
the exact ordered child list together with a canonical low-order representative. -/
inductive OrderThreeBagWitness : BTree → Type where
  | chain3 (children : List BTree) (c : BTree) (hc : c.order = 2)
      (hbag : (BTree.node children).childrenBag = (BTree.node [c]).childrenBag) :
      OrderThreeBagWitness (.node children)
  | bushy3 (children : List BTree) (c₁ c₂ : BTree)
      (hc₁ : c₁.order = 1) (hc₂ : c₂.order = 1)
      (hbag : (BTree.node children).childrenBag = (BTree.node [c₁, c₂]).childrenBag) :
      OrderThreeBagWitness (.node children)

def order_three_bag_witness_recover {t : BTree} (hw3 : OrderThreeBagWitness t) :
    OrderThreeRecoveryWitness t := by
  cases hw3 with
  | chain3 children d hd hbag =>
      exact .chain3 d hbag hd
  | bushy3 children d₁ d₂ hd₁ hd₂ hbag =>
      exact .bushy3 d₁ d₂ hbag hd₁ hd₂

/-- Recover the legacy list-payload order-3 witness from the recovery-first
classifier. -/
theorem order_three_bag_witness_nonempty (t : BTree) (ht : t.order = 3) :
    Nonempty (OrderThreeBagWitness t) := by
  cases t with
  | leaf => simp at ht
  | node children =>
      rcases order_three_recovery_witness_nonempty (.node children) ht with ⟨hw3⟩
      cases hw3 with
      | chain3 d hbag hd =>
          exact ⟨.chain3 children d hd hbag⟩
      | bushy3 d₁ d₂ hbag hd₁ hd₂ =>
          exact ⟨.bushy3 children d₁ d₂ hd₁ hd₂ hbag⟩

/-- Noncomputably choose the legacy list-payload order-3 witness. -/
noncomputable def order_three_bag_witness (t : BTree) (ht : t.order = 3) :
    OrderThreeBagWitness t :=
  Classical.choice (order_three_bag_witness_nonempty t ht)

theorem singleton_children_eq_of_childrenBag_eq {children : List BTree} {d : BTree}
    (hbag : (BTree.node children).childrenBag = (BTree.node [d]).childrenBag) :
    children = [d] := by
  have hperm : children.Perm [d] := Quotient.exact hbag
  have hlen : children.length = 1 := by simpa using hperm.length_eq
  cases children with
  | nil => simp at hlen
  | cons child rest =>
      cases rest with
      | nil =>
          have hmem : d ∈ [child] := hperm.symm.subset (by simp)
          have hd : d = child := by simpa using hmem
          subst d
          rfl
      | cons child₂ rest₂ => simp at hlen

theorem pair_children_exists_of_childrenBag_eq {children : List BTree} {d₁ d₂ : BTree}
    (hbag : (BTree.node children).childrenBag = (BTree.node [d₁, d₂]).childrenBag) :
    ∃ e₁ e₂, children = [e₁, e₂] := by
  have hperm : children.Perm [d₁, d₂] := Quotient.exact hbag
  have hlen : children.length = 2 := by simpa using hperm.length_eq
  simpa [List.length_eq_two] using hlen

theorem triple_children_exists_of_childrenBag_eq {children : List BTree}
    {d₁ d₂ d₃ : BTree}
    (hbag : (BTree.node children).childrenBag = (BTree.node [d₁, d₂, d₃]).childrenBag) :
    ∃ e₁ e₂ e₃, children = [e₁, e₂, e₃] := by
  have hperm : children.Perm [d₁, d₂, d₃] := Quotient.exact hbag
  have hlen : children.length = 3 := by simpa using hperm.length_eq
  simpa [List.length_eq_three] using hlen

theorem four_children_exists_of_childrenBag_eq {children : List BTree}
    {d₁ d₂ d₃ d₄ : BTree}
    (hbag : (BTree.node children).childrenBag = (BTree.node [d₁, d₂, d₃, d₄]).childrenBag) :
    ∃ e₁ e₂ e₃ e₄, children = [e₁, e₂, e₃, e₄] := by
  have hperm : children.Perm [d₁, d₂, d₃, d₄] := Quotient.exact hbag
  have hlen : children.length = 4 := by simpa using hperm.length_eq
  simpa [List.length_eq_four] using hlen

private theorem order_eq_of_childrenBag_eq_local {children₁ children₂ : List BTree}
    (hbag : (BTree.node children₁).childrenBag = (BTree.node children₂).childrenBag) :
    (BTree.node children₁).order = (BTree.node children₂).order := by
  have hperm : children₁.Perm children₂ := Quotient.exact hbag
  have hfold :
      children₁.foldr (fun t n => t.order + n) 0 =
        children₂.foldr (fun t n => t.order + n) 0 :=
    hperm.foldr_eq (lcomm := ⟨fun _ _ _ => by omega⟩) 0
  simp [order_node, hfold]

private theorem order_threeRecoveryWitness_order_eq {t : BTree} (hw3 : OrderThreeRecoveryWitness t) :
    t.order = 3 := by
  cases hw3 with
  | chain3 d hbag hd =>
      cases t with
      | leaf =>
          have hfalse : False := by
            have hcard := congrArg Multiset.card hbag
            simp at hcard
          exact hfalse.elim
      | node children =>
          have horder := order_eq_of_childrenBag_eq_local hbag
          simpa [hd] using horder
  | bushy3 d₁ d₂ hbag hd₁ hd₂ =>
      cases t with
      | leaf =>
          have hfalse : False := by
            have hcard := congrArg Multiset.card hbag
            simp at hcard
          exact hfalse.elim
      | node children =>
          have horder := order_eq_of_childrenBag_eq_local hbag
          simpa [hd₁, hd₂] using horder

private theorem order_threeBagWitness_order_eq {t : BTree} (hw3 : OrderThreeBagWitness t) :
    t.order = 3 :=
  order_threeRecoveryWitness_order_eq (order_three_bag_witness_recover hw3)

/-- Legacy list-payload witness for order-4 rooted trees. The payload records
the exact ordered child list together with canonical low-order representatives. -/
inductive OrderFourBagWitness : BTree → Type where
  | bushy4 (children : List BTree) (c₁ c₂ c₃ : BTree)
      (hc₁ : c₁.order = 1) (hc₂ : c₂.order = 1) (hc₃ : c₃.order = 1)
      (hbag : (BTree.node children).childrenBag = (BTree.node [c₁, c₂, c₃]).childrenBag) :
      OrderFourBagWitness (.node children)
  | mixed4 (children : List BTree) (c₁ c₂ : BTree)
      (hcanon : c₁.order = 1 ∧ c₂.order = 2)
      (hbag : (BTree.node children).childrenBag = (BTree.node [c₁, c₂]).childrenBag) :
      OrderFourBagWitness (.node children)
  | single3 (children : List BTree) (c : BTree)
      (hw3 : OrderThreeRecoveryWitness c)
      (hbag : (BTree.node children).childrenBag = (BTree.node [c]).childrenBag) :
      OrderFourBagWitness (.node children)

/-- Bag-first recovery witness for the order-4 classifier. This keeps only the
canonical child bags and low-order facts needed by theorem-side consumers. -/
inductive OrderFourRecoveryWitness (t : BTree) : Type where
  | bushy4 (d₁ d₂ d₃ : BTree)
      (hbag : t.childrenBag = (BTree.node [d₁, d₂, d₃]).childrenBag)
      (hd₁ : d₁.order = 1) (hd₂ : d₂.order = 1) (hd₃ : d₃.order = 1) :
      OrderFourRecoveryWitness t
  | mixed4 (d₁ d₂ : BTree)
      (hbag : t.childrenBag = (BTree.node [d₁, d₂]).childrenBag)
      (hcanon : d₁.order = 1 ∧ d₂.order = 2) :
      OrderFourRecoveryWitness t
  | singleChain3 (d e : BTree)
      (htBag : t.childrenBag = (BTree.node [d]).childrenBag)
      (hdBag : d.childrenBag = (BTree.node [e]).childrenBag)
      (he : e.order = 2) :
      OrderFourRecoveryWitness t
  | singleBushy3 (d e₁ e₂ : BTree)
      (htBag : t.childrenBag = (BTree.node [d]).childrenBag)
      (hdBag : d.childrenBag = (BTree.node [e₁, e₂]).childrenBag)
      (he₁ : e₁.order = 1) (he₂ : e₂.order = 1) :
      OrderFourRecoveryWitness t

/-- Package the order-4 rooted-tree classification in recovery-first form. -/
theorem order_four_recovery_witness_nonempty (t : BTree) (ht : t.order = 4) :
    Nonempty (OrderFourRecoveryWitness t) := by
  cases t with
  | leaf => simp at ht
  | node children =>
    simp only [order_node] at ht
    have hfoldr : children.foldr (fun c n => c.order + n) 0 = 3 := by omega
    cases children with
    | nil => simp at hfoldr
    | cons hd tl =>
      simp only [List.foldr] at hfoldr
      have hhd_pos : 0 < hd.order := by
        cases hd <;> simp [order_node]
      cases tl with
      | nil =>
        have hw3 : OrderThreeRecoveryWitness hd := order_three_recovery_witness hd (by
          simp only [List.foldr] at hfoldr
          omega)
        cases hw3 with
        | chain3 e hdBag he =>
            exact ⟨.singleChain3 hd e rfl hdBag he⟩
        | bushy3 e₁ e₂ hdBag he₁ he₂ =>
            exact ⟨.singleBushy3 hd e₁ e₂ rfl hdBag he₁ he₂⟩
      | cons hd2 tl2 =>
        have hhd2_pos : 0 < hd2.order := by
          cases hd2 <;> simp [order_node]
        simp only [List.foldr] at hfoldr
        cases tl2 with
        | nil =>
          have hsum : hd.order + hd2.order = 3 := by simpa using hfoldr
          have hpair : (hd.order = 1 ∧ hd2.order = 2) ∨ (hd.order = 2 ∧ hd2.order = 1) := by
            by_cases h1 : hd.order = 1
            · exact Or.inl ⟨h1, by omega⟩
            · exact Or.inr ⟨by omega, by omega⟩
          rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨.mixed4 hd hd2 rfl ⟨h1, h2⟩⟩
          · exact ⟨.mixed4 hd2 hd (Quot.sound (List.Perm.swap _ _ _)) ⟨h2, h1⟩⟩
        | cons hd3 tl3 =>
          have hhd3_pos : 0 < hd3.order := by
            cases hd3 <;> simp [order_node]
          simp only [List.foldr] at hfoldr
          cases tl3 with
          | nil =>
            exact ⟨.bushy4 hd hd2 hd3 rfl (by omega) (by omega) (by omega)⟩
          | cons hd4 tl4 =>
            have hhd4_pos : 0 < hd4.order := by
              cases hd4 <;> simp [order_node]
            simp only [List.foldr] at hfoldr
            have : tl4.foldr (fun c n => c.order + n) 0 ≥ 0 := Nat.zero_le _
            omega

/-- Noncomputably choose the recovery-first order-4 witness. -/
noncomputable def order_four_recovery_witness (t : BTree) (ht : t.order = 4) :
    OrderFourRecoveryWitness t :=
  Classical.choice (order_four_recovery_witness_nonempty t ht)

def order_four_bag_witness_recover {t : BTree} (hw4 : OrderFourBagWitness t) :
    OrderFourRecoveryWitness t := by
  cases hw4 with
  | bushy4 children d₁ d₂ d₃ hd₁ hd₂ hd₃ hbag =>
      exact .bushy4 d₁ d₂ d₃ hbag hd₁ hd₂ hd₃
  | mixed4 children d₁ d₂ hcanon hbag =>
      exact .mixed4 d₁ d₂ hbag hcanon
  | single3 children d hw3 hbag =>
      cases hw3 with
      | chain3 e hdBag he =>
          exact .singleChain3 d e hbag hdBag he
      | bushy3 e₁ e₂ hdBag he₁ he₂ =>
          exact .singleBushy3 d e₁ e₂ hbag hdBag he₁ he₂

/-- Recover the legacy list-payload order-4 witness from the recovery-first
classifier. -/
theorem order_four_bag_witness_nonempty (t : BTree) (ht : t.order = 4) :
    Nonempty (OrderFourBagWitness t) := by
  cases t with
  | leaf => simp at ht
  | node children =>
      rcases order_four_recovery_witness_nonempty (.node children) ht with ⟨hw4⟩
      cases hw4 with
      | bushy4 d₁ d₂ d₃ hbag hd₁ hd₂ hd₃ =>
          exact ⟨.bushy4 children d₁ d₂ d₃ hd₁ hd₂ hd₃ hbag⟩
      | mixed4 d₁ d₂ hbag hcanon =>
          exact ⟨.mixed4 children d₁ d₂ hcanon hbag⟩
      | singleChain3 d e htBag hdBag he =>
          exact ⟨.single3 children d (.chain3 e hdBag he) htBag⟩
      | singleBushy3 d e₁ e₂ htBag hdBag he₁ he₂ =>
          exact ⟨.single3 children d (.bushy3 e₁ e₂ hdBag he₁ he₂) htBag⟩

/-- Noncomputably choose the legacy list-payload order-4 witness. -/
noncomputable def order_four_bag_witness (t : BTree) (ht : t.order = 4) :
    OrderFourBagWitness t :=
  Classical.choice (order_four_bag_witness_nonempty t ht)

theorem order_fourRecoveryWitness_order_eq {t : BTree} (hw4 : OrderFourRecoveryWitness t) :
    t.order = 4 := by
  cases hw4 with
  | bushy4 d₁ d₂ d₃ hbag hd₁ hd₂ hd₃ =>
      cases t with
      | leaf =>
          have hfalse : False := by
            have hcard := congrArg Multiset.card hbag
            simp at hcard
          exact hfalse.elim
      | node children =>
          have horder := order_eq_of_childrenBag_eq_local hbag
          simpa [hd₁, hd₂, hd₃, Nat.add_assoc] using horder
  | mixed4 d₁ d₂ hbag hcanon =>
      cases t with
      | leaf =>
          have hfalse : False := by
            have hcard := congrArg Multiset.card hbag
            simp at hcard
          exact hfalse.elim
      | node children =>
          have horder := order_eq_of_childrenBag_eq_local hbag
          simpa [hcanon.1, hcanon.2] using horder
  | singleChain3 d e htBag hdBag he =>
      cases t with
      | leaf =>
          have hfalse : False := by
            have hcard := congrArg Multiset.card htBag
            simp at hcard
          exact hfalse.elim
      | node children =>
          have horder := order_eq_of_childrenBag_eq_local htBag
          simpa [order_threeRecoveryWitness_order_eq (.chain3 e hdBag he)] using horder
  | singleBushy3 d e₁ e₂ htBag hdBag he₁ he₂ =>
      cases t with
      | leaf =>
          have hfalse : False := by
            have hcard := congrArg Multiset.card htBag
            simp at hcard
          exact hfalse.elim
      | node children =>
          have horder := order_eq_of_childrenBag_eq_local htBag
          simpa [order_threeRecoveryWitness_order_eq (.bushy3 e₁ e₂ hdBag he₁ he₂)] using horder

theorem order_fourBagWitness_order_eq {t : BTree} (hw4 : OrderFourBagWitness t) :
    t.order = 4 :=
  order_fourRecoveryWitness_order_eq (order_four_bag_witness_recover hw4)

/-- Bag-first witness for order-5 rooted trees. The payload records the child
bag together with canonical low-order representatives. -/
inductive OrderFiveBagWitness : BTree → Type where
  | bushy5 (children : List BTree) (c₁ c₂ c₃ c₄ : BTree)
      (hc₁ : c₁.order = 1) (hc₂ : c₂.order = 1) (hc₃ : c₃.order = 1) (hc₄ : c₄.order = 1)
      (hbag : (BTree.node children).childrenBag = (BTree.node [c₁, c₂, c₃, c₄]).childrenBag) :
      OrderFiveBagWitness (.node children)
  | caseB (children : List BTree) (c₁ c₂ c₃ : BTree)
      (hsum : c₁.order + c₂.order + c₃.order = 4)
      (hbag : (BTree.node children).childrenBag = (BTree.node [c₁, c₂, c₃]).childrenBag) :
      OrderFiveBagWitness (.node children)
  | caseC (children : List BTree) (c₁ c₂ : BTree)
      (hsum : c₁.order + c₂.order = 4)
      (hbag : (BTree.node children).childrenBag = (BTree.node [c₁, c₂]).childrenBag) :
      OrderFiveBagWitness (.node children)
  | caseD (children : List BTree) (c : BTree)
      (hw4 : OrderFourRecoveryWitness c)
      (hbag : (BTree.node children).childrenBag = (BTree.node [c]).childrenBag) :
      OrderFiveBagWitness (.node children)

/-- Package the order-5 rooted-tree classification in bag-first form. -/
theorem order_five_bag_witness_nonempty (t : BTree) (ht : t.order = 5) :
    Nonempty (OrderFiveBagWitness t) := by
  cases t with
  | leaf => simp at ht
  | node children =>
    simp only [order_node] at ht
    have hfoldr : children.foldr (fun c n => c.order + n) 0 = 4 := by omega
    cases children with
    | nil => simp at hfoldr
    | cons hd tl =>
      simp only [List.foldr] at hfoldr
      have hhd_pos : 0 < hd.order := by
        cases hd <;> simp [order_node]
      cases tl with
      | nil =>
        have hw4 : OrderFourRecoveryWitness hd := order_four_recovery_witness hd (by
          simp only [List.foldr] at hfoldr
          omega)
        exact ⟨.caseD [hd] hd hw4 rfl⟩
      | cons hd2 tl2 =>
        have hhd2_pos : 0 < hd2.order := by
          cases hd2 <;> simp [order_node]
        simp only [List.foldr] at hfoldr
        cases tl2 with
        | nil =>
          exact ⟨.caseC [hd, hd2] hd hd2 (by simpa using hfoldr) rfl⟩
        | cons hd3 tl3 =>
          have hhd3_pos : 0 < hd3.order := by
            cases hd3 <;> simp [order_node]
          simp only [List.foldr] at hfoldr
          cases tl3 with
          | nil =>
            exact ⟨.caseB [hd, hd2, hd3] hd hd2 hd3 (by simpa [Nat.add_assoc] using hfoldr) rfl⟩
          | cons hd4 tl4 =>
            have hhd4_pos : 0 < hd4.order := by
              cases hd4 <;> simp [order_node]
            simp only [List.foldr] at hfoldr
            cases tl4 with
            | nil =>
              have h1 : hd.order = 1 := by omega
              have h2 : hd2.order = 1 := by omega
              have h3 : hd3.order = 1 := by omega
              have h4 : hd4.order = 1 := by omega
              exact ⟨.bushy5 [hd, hd2, hd3, hd4] hd hd2 hd3 hd4 h1 h2 h3 h4 rfl⟩
            | cons hd5 tl5 =>
              exfalso
              have hhd5_pos : 0 < hd5.order := by
                cases hd5 <;> simp [order_node]
              simp only [List.foldr] at hfoldr
              have : tl5.foldr (fun c n => c.order + n) 0 ≥ 0 := Nat.zero_le _
              omega

/-- Noncomputably choose the bag-first order-5 witness. -/
noncomputable def order_five_bag_witness (t : BTree) (ht : t.order = 5) :
    OrderFiveBagWitness t :=
  Classical.choice (order_five_bag_witness_nonempty t ht)

/-- Child bags agree for any permutation of the ordered fallback representation. -/
theorem node_childrenBag_eq_of_perm {children₁ children₂ : List BTree}
    (hperm : children₁.Perm children₂) :
    (BTree.node children₁).childrenBag = (BTree.node children₂).childrenBag :=
  Quot.sound hperm

/-- Two-child nodes expose the same bag after swapping the ordered witnesses. -/
theorem node_childrenBag_eq_swap (c₁ c₂ : BTree) :
    (BTree.node [c₁, c₂]).childrenBag = (BTree.node [c₂, c₁]).childrenBag :=
  node_childrenBag_eq_of_perm (List.Perm.swap _ _ _)

/-- Three-child nodes expose the same bag after swapping the final two witnesses. -/
theorem node_childrenBag_eq_swap_right (c₁ c₂ c₃ : BTree) :
    (BTree.node [c₁, c₂, c₃]).childrenBag = (BTree.node [c₁, c₃, c₂]).childrenBag :=
  node_childrenBag_eq_of_perm (List.Perm.cons _ (List.Perm.swap _ _ _))

/-- Three-child nodes expose the same bag after rotating the witnesses left. -/
theorem node_childrenBag_eq_rotate_left (c₁ c₂ c₃ : BTree) :
    (BTree.node [c₁, c₂, c₃]).childrenBag = (BTree.node [c₂, c₃, c₁]).childrenBag :=
  node_childrenBag_eq_of_perm <|
    (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ _))

/-- Three-child nodes expose the same bag after rotating the witnesses right. -/
theorem node_childrenBag_eq_rotate_right (c₁ c₂ c₃ : BTree) :
    (BTree.node [c₁, c₂, c₃]).childrenBag = (BTree.node [c₃, c₁, c₂]).childrenBag :=
  node_childrenBag_eq_of_perm <|
    (List.Perm.cons _ (List.Perm.swap _ _ _)).trans (List.Perm.swap _ _ _)

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

private theorem symmetryScan_eq_foldr_dedup (allChildren remaining : List BTree) :
    symmetryScan allChildren remaining =
      remaining.dedup.foldr
        (fun t n =>
          (allChildren.count t).factorial * t.symmetry ^ (allChildren.count t) * n)
        1 := by
  classical
  induction remaining with
  | nil =>
      simp [symmetryScan]
  | cons hd tl ih =>
      by_cases hcontains : tl.contains hd = true
      · have hmem : hd ∈ tl := List.contains_iff_mem.mp hcontains
        calc
          symmetryScan allChildren (hd :: tl)
              = symmetryScan allChildren tl := by
                  rw [symmetryScan, if_pos hcontains]
          _ = tl.dedup.foldr
                (fun t n =>
                  (allChildren.count t).factorial * t.symmetry ^ (allChildren.count t) * n)
                1 := ih
          _ = (hd :: tl).dedup.foldr
                (fun t n =>
                  (allChildren.count t).factorial * t.symmetry ^ (allChildren.count t) * n)
                1 := by rw [List.dedup_cons_of_mem hmem]
      · have hfalse : tl.contains hd = false := by
          exact Bool.eq_false_iff.mpr hcontains
        have hnotmem : hd ∉ tl := by
          intro hmem
          exact hcontains (List.contains_iff_mem.mpr hmem)
        calc
          symmetryScan allChildren (hd :: tl)
              = (allChildren.count hd).factorial * hd.symmetry ^ (allChildren.count hd) *
                  symmetryScan allChildren tl := by
                    rw [symmetryScan, if_neg hcontains]
          _ = (allChildren.count hd).factorial * hd.symmetry ^ (allChildren.count hd) *
                tl.dedup.foldr
                  (fun t n =>
                    (allChildren.count t).factorial * t.symmetry ^ (allChildren.count t) * n)
                  1 := by rw [ih]
          _ = (hd :: tl).dedup.foldr
                (fun t n =>
                  (allChildren.count t).factorial * t.symmetry ^ (allChildren.count t) * n)
                1 := by simp [List.dedup_cons_of_notMem hnotmem]

/-- The symmetry of a node depends only on the multiset of its children. -/
theorem symmetry_node_perm {children₁ children₂ : List BTree}
    (hperm : children₁.Perm children₂) :
    (BTree.node children₁).symmetry = (BTree.node children₂).symmetry := by
  classical
  rw [symmetry_node, symmetry_node,
    symmetryScan_eq_foldr_dedup, symmetryScan_eq_foldr_dedup]
  have hcount : ∀ t : BTree, children₂.count t = children₁.count t := by
    intro t
    exact (hperm.count_eq t).symm
  simpa [hcount] using
    (hperm.dedup.foldr_eq
      (lcomm := ⟨fun a b c => by
        ac_rfl
      ⟩) 1)

/-- Bag-first order invariant for node children. -/
def orderBag (children : Multiset BTree) : ℕ :=
  Quotient.liftOn children (fun listed : List BTree => (BTree.node listed).order)
    (fun _ _ hperm => order_node_perm hperm)

/-- Bag-first density invariant for node children. -/
def densityBag (children : Multiset BTree) : ℕ :=
  Quotient.liftOn children (fun listed : List BTree => (BTree.node listed).density)
    (fun _ _ hperm => density_node_perm hperm)

/-- Bag-first symmetry invariant for node children. -/
def symmetryBag (children : Multiset BTree) : ℕ :=
  Quotient.liftOn children (fun listed : List BTree => (BTree.node listed).symmetry)
    (fun _ _ hperm => symmetry_node_perm hperm)

/-- Bag-first `β` invariant for node children. -/
def betaBag (children : Multiset BTree) : ℕ :=
  (orderBag children).factorial / symmetryBag children

/-- Bag-first `α` invariant for node children. -/
def alphaBag (children : Multiset BTree) : ℕ :=
  (orderBag children).factorial / (symmetryBag children * densityBag children)

@[simp] theorem orderBag_childrenBag (children : List BTree) :
    orderBag (BTree.node children).childrenBag = (BTree.node children).order := rfl

@[simp] theorem densityBag_childrenBag (children : List BTree) :
    densityBag (BTree.node children).childrenBag = (BTree.node children).density := rfl

@[simp] theorem symmetryBag_childrenBag (children : List BTree) :
    symmetryBag (BTree.node children).childrenBag = (BTree.node children).symmetry := rfl

@[simp] theorem betaBag_childrenBag (children : List BTree) :
    betaBag (BTree.node children).childrenBag = (BTree.node children).beta := rfl

@[simp] theorem alphaBag_childrenBag (children : List BTree) :
    alphaBag (BTree.node children).childrenBag = (BTree.node children).alpha := rfl

theorem order_eq_of_childrenBag_eq {children₁ children₂ : List BTree}
    (hbag : (BTree.node children₁).childrenBag = (BTree.node children₂).childrenBag) :
    (BTree.node children₁).order = (BTree.node children₂).order := by
  simpa only [childrenBag_node, orderBag_childrenBag] using congrArg orderBag hbag

theorem density_eq_of_childrenBag_eq {children₁ children₂ : List BTree}
    (hbag : (BTree.node children₁).childrenBag = (BTree.node children₂).childrenBag) :
    (BTree.node children₁).density = (BTree.node children₂).density := by
  simpa only [childrenBag_node, densityBag_childrenBag] using congrArg densityBag hbag

theorem symmetry_eq_of_childrenBag_eq {children₁ children₂ : List BTree}
    (hbag : (BTree.node children₁).childrenBag = (BTree.node children₂).childrenBag) :
    (BTree.node children₁).symmetry = (BTree.node children₂).symmetry := by
  simpa only [childrenBag_node, symmetryBag_childrenBag] using congrArg symmetryBag hbag

theorem beta_eq_of_childrenBag_eq {children₁ children₂ : List BTree}
    (hbag : (BTree.node children₁).childrenBag = (BTree.node children₂).childrenBag) :
    (BTree.node children₁).beta = (BTree.node children₂).beta := by
  simpa only [childrenBag_node, betaBag_childrenBag] using congrArg betaBag hbag

/-- Normalize the order-5 two-child family with child-order sum `4` into the
`{2,2}` / `{1, chain3}` / `{1, bushy3}` trichotomy. -/
inductive OrderFiveCaseCWitness (c₁ c₂ : BTree) : Type where
  | ord22 (hc₁ : c₁.order = 2) (hc₂ : c₂.order = 2) : OrderFiveCaseCWitness c₁ c₂
  | chain3 (d : BTree)
      (hpair : (c₁.order = 1 ∧ c₂.childrenBag = (BTree.node [d]).childrenBag ∧ d.order = 2) ∨
        (c₁.childrenBag = (BTree.node [d]).childrenBag ∧ d.order = 2 ∧ c₂.order = 1)) :
      OrderFiveCaseCWitness c₁ c₂
  | bushy3 (d₁ d₂ : BTree)
      (hpair : (c₁.order = 1 ∧ c₂.childrenBag = (BTree.node [d₁, d₂]).childrenBag ∧
          d₁.order = 1 ∧ d₂.order = 1) ∨
        (c₁.childrenBag = (BTree.node [d₁, d₂]).childrenBag ∧ d₁.order = 1 ∧
          d₂.order = 1 ∧ c₂.order = 1)) :
      OrderFiveCaseCWitness c₁ c₂

/-- Package the order-5 two-child `sum = 4` classification in rooted-tree form. -/
theorem order_five_caseC_witness_nonempty (c₁ c₂ : BTree)
    (hsum : c₁.order + c₂.order = 4) :
    Nonempty (OrderFiveCaseCWitness c₁ c₂) := by
  have hc₁_pos := order_pos c₁
  have hc₂_pos := order_pos c₂
  by_cases h22 : c₁.order = 2 ∧ c₂.order = 2
  · exact ⟨.ord22 h22.1 h22.2⟩
  · have h13 :
        (c₁.order = 1 ∧ c₂.order = 3) ∨ (c₁.order = 3 ∧ c₂.order = 1) := by
      by_cases h1 : c₁.order = 1
      · exact Or.inl ⟨h1, by omega⟩
      · by_cases h2 : c₂.order = 1
        · exact Or.inr ⟨by omega, h2⟩
        · exfalso
          omega
    rcases h13 with ⟨h1, hc₂⟩ | ⟨hc₁, h2⟩
    · have hw3 : OrderThreeRecoveryWitness c₂ := order_three_recovery_witness c₂ hc₂
      cases hw3 with
      | chain3 d hbag hdorder =>
          exact ⟨.chain3 d <| Or.inl ⟨h1, by simpa using hbag, hdorder⟩⟩
      | bushy3 d₁ d₂ hbag hd₁ hd₂ =>
          exact ⟨.bushy3 d₁ d₂ <| Or.inl ⟨h1, by simpa using hbag, hd₁, hd₂⟩⟩
    · have hw3 : OrderThreeRecoveryWitness c₁ := order_three_recovery_witness c₁ hc₁
      cases hw3 with
      | chain3 d hbag hdorder =>
          exact ⟨.chain3 d <| Or.inr ⟨by simpa using hbag, hdorder, h2⟩⟩
      | bushy3 d₁ d₂ hbag hd₁ hd₂ =>
          exact ⟨.bushy3 d₁ d₂ <| Or.inr ⟨by simpa using hbag, hd₁, hd₂, h2⟩⟩

/-- Noncomputably choose the normalized order-5 two-child Case C witness. -/
noncomputable def order_five_caseC_witness (c₁ c₂ : BTree)
    (hsum : c₁.order + c₂.order = 4) :
    OrderFiveCaseCWitness c₁ c₂ :=
  Classical.choice (order_five_caseC_witness_nonempty c₁ c₂ hsum)

/-- Normalize the order-5 three-child family with child-order sum `4` into a
bag-first `{1,1,2}` witness. -/
inductive OrderFiveCaseBWitness (c₁ c₂ c₃ : BTree) : Type where
  | bag112 (d₁ d₂ d₃ : BTree)
      (hbag : (BTree.node [c₁, c₂, c₃]).childrenBag = (BTree.node [d₁, d₂, d₃]).childrenBag)
      (hd₁ : d₁.order = 1) (hd₂ : d₂.order = 1) (hd₃ : d₃.order = 2) :
      OrderFiveCaseBWitness c₁ c₂ c₃

/-- Package the order-5 three-child `sum = 4` classification in rooted-tree form. -/
theorem order_five_caseB_witness_nonempty (c₁ c₂ c₃ : BTree)
    (hsum : c₁.order + c₂.order + c₃.order = 4) :
    Nonempty (OrderFiveCaseBWitness c₁ c₂ c₃) := by
  have hc₁_pos := order_pos c₁
  have hc₂_pos := order_pos c₂
  have hc₃_pos := order_pos c₃
  by_cases h1 : c₁.order = 1
  · by_cases h2 : c₂.order = 1
    · exact ⟨.bag112 c₁ c₂ c₃ rfl h1 h2 (by omega)⟩
    · exact ⟨.bag112 c₁ c₃ c₂ (BTree.node_childrenBag_eq_swap_right c₁ c₂ c₃)
        h1 (by omega) (by omega)⟩
  · exact ⟨.bag112 c₂ c₃ c₁ (BTree.node_childrenBag_eq_rotate_left c₁ c₂ c₃)
      (by omega) (by omega) (by omega)⟩

/-- Noncomputably choose the normalized order-5 three-child Case B witness. -/
noncomputable def order_five_caseB_witness (c₁ c₂ c₃ : BTree)
    (hsum : c₁.order + c₂.order + c₃.order = 4) :
    OrderFiveCaseBWitness c₁ c₂ c₃ :=
  Classical.choice (order_five_caseB_witness_nonempty c₁ c₂ c₃ hsum)

/-- Normalize the order-5 singleton-child family whose child has order `4`
into the `bushy4` / `mixed4` / `viaChain3` / `viaBushy3` quartic trichotomy. -/
inductive OrderFiveCaseDWitness (c : BTree) : Type where
  | bushy4 (d₁ d₂ d₃ : BTree)
      (hbag : c.childrenBag = (BTree.node [d₁, d₂, d₃]).childrenBag)
      (hd₁ : d₁.order = 1) (hd₂ : d₂.order = 1) (hd₃ : d₃.order = 1) :
      OrderFiveCaseDWitness c
  | mixed4 (d₁ d₂ : BTree)
      (hbag : c.childrenBag = (BTree.node [d₁, d₂]).childrenBag)
      (hpair : (d₁.order = 1 ∧ d₂.order = 2) ∨ (d₁.order = 2 ∧ d₂.order = 1)) :
      OrderFiveCaseDWitness c
  | viaChain3 (d e : BTree)
      (hcBag : c.childrenBag = (BTree.node [d]).childrenBag)
      (hdBag : d.childrenBag = (BTree.node [e]).childrenBag)
      (he : e.order = 2) :
      OrderFiveCaseDWitness c
  | viaBushy3 (d e₁ e₂ : BTree)
      (hcBag : c.childrenBag = (BTree.node [d]).childrenBag)
      (hdBag : d.childrenBag = (BTree.node [e₁, e₂]).childrenBag)
      (he₁ : e₁.order = 1) (he₂ : e₂.order = 1) :
      OrderFiveCaseDWitness c

/-- Package the order-5 singleton-child / Case D classification in rooted-tree
form from the recovery-first order-4 classifier. -/
theorem order_five_caseD_witness_nonempty (c : BTree) (hc : c.order = 4) :
    Nonempty (OrderFiveCaseDWitness c) := by
  have hw4 : OrderFourRecoveryWitness c := order_four_recovery_witness c hc
  cases hw4 with
  | bushy4 d₁ d₂ d₃ hbag hd₁ hd₂ hd₃ =>
      exact ⟨.bushy4 d₁ d₂ d₃ hbag hd₁ hd₂ hd₃⟩
  | mixed4 d₁ d₂ hbag hcanon =>
      exact ⟨.mixed4 d₁ d₂ hbag (Or.inl hcanon)⟩
  | singleChain3 d e hcBag hdBag he =>
      exact ⟨.viaChain3 d e hcBag hdBag he⟩
  | singleBushy3 d e₁ e₂ hcBag hdBag he₁ he₂ =>
      exact ⟨.viaBushy3 d e₁ e₂ hcBag hdBag he₁ he₂⟩

/-- Noncomputably choose the normalized order-5 singleton-child / Case D witness. -/
noncomputable def order_five_caseD_witness (c : BTree) (hc : c.order = 4) :
    OrderFiveCaseDWitness c :=
  Classical.choice (order_five_caseD_witness_nonempty c hc)

/-- Recover an exact singleton-node presentation from a bag-equality against a
canonical singleton node. -/
theorem singleton_node_recover_of_childrenBag_eq {t d : BTree}
    (hbag : t.childrenBag = (BTree.node [d]).childrenBag) :
    ∃ e, t.childrenBag = (BTree.node [e]).childrenBag ∧ t = .node [e] := by
  cases t with
  | leaf =>
      have hfalse : False := by
        have hcard := congrArg Multiset.card hbag
        simp at hcard
      exact hfalse.elim
  | node children =>
      have hchildren : children = [d] := singleton_children_eq_of_childrenBag_eq hbag
      exact ⟨d, by simp [hchildren] at hbag ⊢, by simp [hchildren]⟩

/-- Recover an exact pair-node presentation from a bag-equality against a
canonical two-child node. -/
theorem pair_node_recover_of_childrenBag_eq {t d₁ d₂ : BTree}
    (hbag : t.childrenBag = (BTree.node [d₁, d₂]).childrenBag) :
    ∃ e₁ e₂, t.childrenBag = (BTree.node [e₁, e₂]).childrenBag ∧ t = .node [e₁, e₂] := by
  cases t with
  | leaf =>
      have hfalse : False := by
        have hcard := congrArg Multiset.card hbag
        simp at hcard
      exact hfalse.elim
  | node children =>
      rcases pair_children_exists_of_childrenBag_eq hbag with ⟨e₁, e₂, hchildren⟩
      exact ⟨e₁, e₂, by simp [hchildren] at hbag ⊢, by simp [hchildren]⟩

/-- Recover an exact triple-node presentation from a bag-equality against a
canonical three-child node. -/
theorem triple_node_recover_of_childrenBag_eq {t d₁ d₂ d₃ : BTree}
    (hbag : t.childrenBag = (BTree.node [d₁, d₂, d₃]).childrenBag) :
    ∃ e₁ e₂ e₃,
      t.childrenBag = (BTree.node [e₁, e₂, e₃]).childrenBag ∧
      t = .node [e₁, e₂, e₃] := by
  cases t with
  | leaf =>
      have hfalse : False := by
        have hcard := congrArg Multiset.card hbag
        simp at hcard
      exact hfalse.elim
  | node children =>
      rcases triple_children_exists_of_childrenBag_eq hbag with ⟨e₁, e₂, e₃, hchildren⟩
      exact ⟨e₁, e₂, e₃, by simp [hchildren] at hbag ⊢, by simp [hchildren]⟩

/-- Recover an exact four-child node presentation from a bag-equality against a
canonical four-child node. -/
theorem four_node_recover_of_childrenBag_eq {t d₁ d₂ d₃ d₄ : BTree}
    (hbag : t.childrenBag = (BTree.node [d₁, d₂, d₃, d₄]).childrenBag) :
    ∃ e₁ e₂ e₃ e₄,
      t.childrenBag = (BTree.node [e₁, e₂, e₃, e₄]).childrenBag ∧
      t = .node [e₁, e₂, e₃, e₄] := by
  cases t with
  | leaf =>
      have hfalse : False := by
        have hcard := congrArg Multiset.card hbag
        simp at hcard
      exact hfalse.elim
  | node children =>
      rcases four_children_exists_of_childrenBag_eq hbag with ⟨e₁, e₂, e₃, e₄, hchildren⟩
      exact ⟨e₁, e₂, e₃, e₄, by simp [hchildren] at hbag ⊢, by simp [hchildren]⟩

theorem alpha_eq_of_childrenBag_eq {children₁ children₂ : List BTree}
    (hbag : (BTree.node children₁).childrenBag = (BTree.node children₂).childrenBag) :
    (BTree.node children₁).alpha = (BTree.node children₂).alpha := by
  simpa only [childrenBag_node, alphaBag_childrenBag] using congrArg alphaBag hbag

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
