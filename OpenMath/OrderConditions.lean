import OpenMath.RootedTree
import OpenMath.RungeKutta

/-!
# B-Series Order Conditions via Rooted Trees

Theorem 301A (Iserles): A Runge–Kutta method has order p if and only if
the elementary weight condition ∑ bᵢ Φᵢ(t) = 1/γ(t) holds for every rooted
tree t with |t| ≤ p, where Φᵢ is the elementary weight and γ is the density.

This file defines:
- `elementaryWeight`: the elementary weight Φᵢ(t) for a RK method
- `satisfiesTreeCondition`: the order condition for a single tree
- Connection lemmas showing equivalence with explicit order conditions
- `Theorem_301A`: the master theorem (sorry, pending full proof)

Reference: Iserles, Section 3.1; Butcher, Section 300.
-/

open Finset Real BTree

namespace ButcherTableau

variable {s : ℕ}

/-! ## Elementary Weights -/

/-- The **elementary weight** Φᵢ(t) for stage i of a Runge–Kutta method on tree t.

The recurrence is:
- Φᵢ(τ) = 1 (leaf: every stage gets weight 1)
- Φᵢ([t₁, ..., tₘ]) = ∏ⱼ (∑ₖ aᵢₖ Φₖ(tⱼ))

This is the fundamental quantity connecting rooted trees to RK methods.
Reference: Butcher, Theorem 301A; Iserles, Section 3.1. -/
noncomputable def elementaryWeight (tab : ButcherTableau s) : BTree → Fin s → ℝ
  | .leaf, _ => 1
  | .node children, i =>
      children.foldr
        (fun t acc => acc * (∑ k : Fin s, tab.A i k * tab.elementaryWeight t k)) 1
termination_by t => sizeOf t
decreasing_by
  have hmem : sizeOf t < sizeOf children :=
    List.sizeOf_lt_of_mem (by assumption)
  have hnode : sizeOf children < sizeOf (BTree.node children) := by simp
  exact Nat.lt_trans hmem hnode

/-- The **tree order condition** for a single rooted tree t:
∑ᵢ bᵢ Φᵢ(t) = 1/γ(t). -/
noncomputable def satisfiesTreeCondition (tab : ButcherTableau s) (t : BTree) : Prop :=
  ∑ i : Fin s, tab.b i * tab.elementaryWeight t i = 1 / (t.density : ℝ)

/-! ## Connection with Explicit Order Conditions -/

/-- Elementary weight of a leaf is 1. -/
@[simp]
theorem elementaryWeight_leaf (tab : ButcherTableau s) (i : Fin s) :
    tab.elementaryWeight .leaf i = 1 := by
  simp [elementaryWeight]

/-- Elementary weight of a single-child node [t] is ∑ₖ aᵢₖ Φₖ(t). -/
theorem elementaryWeight_singleton (tab : ButcherTableau s) (t : BTree) (i : Fin s) :
    tab.elementaryWeight (.node [t]) i = ∑ k : Fin s, tab.A i k * tab.elementaryWeight t k := by
  simp [elementaryWeight, List.foldr]

/-- The tree condition for τ (leaf) is equivalent to ∑ bᵢ = 1. -/
theorem satisfiesTreeCondition_leaf (tab : ButcherTableau s) :
    tab.satisfiesTreeCondition .leaf ↔ tab.order1 := by
  simp [satisfiesTreeCondition, order1, density_leaf]

/-- The tree condition for [τ] (t2) is equivalent to ∑ bᵢ (∑ⱼ aᵢⱼ) = 1/2.
Under row-sum consistency (cᵢ = ∑ⱼ aᵢⱼ), this becomes ∑ bᵢ cᵢ = 1/2. -/
theorem satisfiesTreeCondition_t2 (tab : ButcherTableau s) :
    tab.satisfiesTreeCondition t2 ↔
    ∑ i : Fin s, tab.b i * (∑ k : Fin s, tab.A i k) = 1 / 2 := by
  simp [satisfiesTreeCondition, t2, elementaryWeight_singleton, elementaryWeight_leaf]

/-- Under row-sum consistency, the t2 tree condition matches order2. -/
theorem satisfiesTreeCondition_t2_of_consistent (tab : ButcherTableau s)
    (hrc : tab.IsRowSumConsistent) :
    tab.satisfiesTreeCondition t2 ↔ tab.order2 := by
  rw [satisfiesTreeCondition_t2]
  constructor
  · intro h
    simp only [order2]
    convert h using 1
    congr 1; ext i
    congr 1
    exact hrc i
  · intro h
    simp only [order2] at h
    convert h using 1
    congr 1; ext i
    congr 1
    exact (hrc i).symm

/-! ## Order via Trees -/

/-- A method satisfies the tree-based order conditions up to order p if
for every tree t with |t| ≤ p, the elementary weight condition holds. -/
noncomputable def hasTreeOrder (tab : ButcherTableau s) (p : ℕ) : Prop :=
  ∀ t : BTree, t.order ≤ p → tab.satisfiesTreeCondition t

/-- **Theorem 301A** (Iserles / Butcher): A consistent Runge–Kutta method has
classical order at least p if and only if all tree conditions up to order p hold.

The forward direction shows that each `orderNx` condition corresponds to
the tree condition for the appropriate tree. The reverse direction uses that
the set of trees of order ≤ p is finite (up to isomorphism) and exhaustive. -/
theorem thm_301A_order1 (tab : ButcherTableau s) :
    tab.hasTreeOrder 1 ↔ tab.HasOrderGe1 := by
  constructor
  · intro h
    exact (satisfiesTreeCondition_leaf tab).mp (h .leaf (by simp))
  · intro h t ht
    have heq : t.order = 1 := by have := BTree.order_pos t; omega
    cases t with
    | leaf => exact (satisfiesTreeCondition_leaf tab).mpr h
    | node children =>
      simp only [order_node] at heq
      have hfoldr : children.foldr (fun t n => t.order + n) 0 = 0 := by omega
      cases children with
      | nil =>
        simp [satisfiesTreeCondition, elementaryWeight, List.foldr,
              density, order, HasOrderGe1, order1]
        exact h
      | cons hd tl =>
        exfalso; simp only [List.foldr] at hfoldr
        have := BTree.order_pos hd; omega

/-! ### Helper lemmas for tree enumeration -/

/-- Any tree of order 1 has elementary weight 1. -/
private theorem ew_of_order_one (tab : ButcherTableau s) (t : BTree) (ht : t.order = 1)
    (i : Fin s) : tab.elementaryWeight t i = 1 := by
  cases t with
  | leaf => simp [elementaryWeight]
  | node children =>
    simp only [order_node] at ht
    have hfoldr : children.foldr (fun t n => t.order + n) 0 = 0 := by omega
    cases children with
    | nil => simp [elementaryWeight, List.foldr]
    | cons hd tl =>
      exfalso; simp only [List.foldr] at hfoldr
      have := BTree.order_pos hd; omega

/-- Any tree of order 1 has density 1. -/
private theorem density_of_order_one (t : BTree) (ht : t.order = 1) :
    t.density = 1 := by
  cases t with
  | leaf => simp
  | node children =>
    simp only [order_node] at ht
    have hfoldr : children.foldr (fun t n => t.order + n) 0 = 0 := by omega
    cases children with
    | nil => simp [density, order, List.foldr]
    | cons hd tl =>
      exfalso; simp only [List.foldr] at hfoldr
      have := BTree.order_pos hd; omega

/-- Any tree of order 2 has elementary weight ∑ k, A i k. -/
private theorem ew_of_order_two (tab : ButcherTableau s) (t : BTree) (ht : t.order = 2)
    (i : Fin s) :
    tab.elementaryWeight t i = ∑ k : Fin s, tab.A i k := by
  cases t with
  | leaf => simp at ht
  | node children =>
    simp only [order_node] at ht
    have hfoldr : children.foldr (fun c n => c.order + n) 0 = 1 := by omega
    cases children with
    | nil => simp [List.foldr] at hfoldr
    | cons hd tl =>
      simp only [List.foldr] at hfoldr
      have hpos := BTree.order_pos hd
      have htl : tl.foldr (fun c n => c.order + n) 0 = 0 := by omega
      have hhd : hd.order = 1 := by omega
      cases tl with
      | nil =>
        simp [elementaryWeight, List.foldr]
        congr 1; ext k
        rw [ew_of_order_one tab hd hhd k, mul_one]
      | cons hd2 tl2 =>
        exfalso; simp only [List.foldr] at htl
        have := BTree.order_pos hd2; omega

/-- Any tree of order 2 has density 2. -/
private theorem density_of_order_two (t : BTree) (ht : t.order = 2) :
    t.density = 2 := by
  cases t with
  | leaf => simp at ht
  | node children =>
    simp only [order_node] at ht
    have hfoldr : children.foldr (fun c n => c.order + n) 0 = 1 := by omega
    cases children with
    | nil => simp [List.foldr] at hfoldr
    | cons hd tl =>
      simp only [List.foldr] at hfoldr
      have hpos := BTree.order_pos hd
      have htl : tl.foldr (fun c n => c.order + n) 0 = 0 := by omega
      have hhd : hd.order = 1 := by omega
      cases tl with
      | nil =>
        simp only [density_node, order_node, List.foldr]
        rw [density_of_order_one hd hhd, hhd]
      | cons hd2 tl2 =>
        exfalso; simp only [List.foldr] at htl
        have := BTree.order_pos hd2; omega

/-- Any tree of order 1 satisfies the tree condition iff order1 holds. -/
private theorem satisfiesTreeCondition_order_one (tab : ButcherTableau s) (t : BTree)
    (ht : t.order = 1) :
    tab.satisfiesTreeCondition t ↔ tab.order1 := by
  simp only [satisfiesTreeCondition, order1, density_of_order_one t ht, Nat.cast_one, div_one]
  constructor
  · intro h; convert h using 1; simp [ew_of_order_one tab t ht]
  · intro h; convert h using 1; simp [ew_of_order_one tab t ht]

/-- Any tree of order 2 satisfies the tree condition iff ∑ bᵢ (∑ aᵢⱼ) = 1/2. -/
private theorem satisfiesTreeCondition_order_two (tab : ButcherTableau s) (t : BTree)
    (ht : t.order = 2) :
    tab.satisfiesTreeCondition t ↔
    ∑ i : Fin s, tab.b i * (∑ k : Fin s, tab.A i k) = 1 / 2 := by
  simp only [satisfiesTreeCondition, density_of_order_two t ht]
  constructor
  · intro h; convert h using 1; congr 1; ext i; congr 1; exact (ew_of_order_two tab t ht i).symm
  · intro h; convert h using 1; congr 1; ext i; congr 1; exact ew_of_order_two tab t ht i

/-- Theorem 301A at order 2 (assuming row-sum consistency). -/
theorem thm_301A_order2 (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    tab.hasTreeOrder 2 ↔ tab.HasOrderGe2 := by
  constructor
  · intro h
    exact ⟨(satisfiesTreeCondition_leaf tab).mp (h .leaf (by simp)),
           (satisfiesTreeCondition_t2_of_consistent tab hrc).mp (h t2 (by native_decide))⟩
  · intro ⟨h1, h2⟩ t ht
    have hpos := BTree.order_pos t
    by_cases hle : t.order ≤ 1
    · exact (satisfiesTreeCondition_order_one tab t (by omega)).mpr h1
    · have heq : t.order = 2 := by omega
      rw [satisfiesTreeCondition_order_two tab t heq]
      rw [order2] at h2
      convert h2 using 1
      congr 1; ext i; congr 1; exact (hrc i).symm

/-- Theorem 301A at order 3 (assuming row-sum consistency). -/
theorem thm_301A_order3 (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    tab.hasTreeOrder 3 ↔ tab.HasOrderGe3 := by
  sorry

/-- Theorem 301A at order 4 (assuming row-sum consistency). -/
theorem thm_301A_order4 (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    tab.hasTreeOrder 4 ↔ tab.HasOrderGe4 := by
  sorry

/-- Theorem 301A at order 5 (assuming row-sum consistency). -/
theorem thm_301A_order5 (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    tab.hasTreeOrder 5 ↔ tab.HasOrderGe5 := by
  sorry

end ButcherTableau
