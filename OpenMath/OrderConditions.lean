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
- `Theorem_301A`: the master theorem through order 5

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

/-- Elementary weights for a node depend only on the multiset of its children. -/
theorem elementaryWeight_node_perm (tab : ButcherTableau s) {children₁ children₂ : List BTree}
    (hperm : children₁.Perm children₂) (i : Fin s) :
    tab.elementaryWeight (.node children₁) i = tab.elementaryWeight (.node children₂) i := by
  unfold elementaryWeight
  simpa using hperm.foldr_eq
    (f := fun t acc => acc * (∑ k : Fin s, tab.A i k * tab.elementaryWeight t k))
    (lcomm := ⟨fun a b c => by ring⟩) 1

/-- Bag-facing corollary of `elementaryWeight_node_perm`. -/
theorem elementaryWeight_eq_of_childrenBag_eq (tab : ButcherTableau s)
    {children₁ children₂ : List BTree}
    (hbag : (BTree.node children₁).childrenBag = (BTree.node children₂).childrenBag)
    (i : Fin s) :
    tab.elementaryWeight (.node children₁) i = tab.elementaryWeight (.node children₂) i := by
  have hperm : children₁.Perm children₂ := Quotient.exact hbag
  exact elementaryWeight_node_perm tab hperm i

/-- The tree condition for a node depends only on the unordered child multiplicities. -/
theorem satisfiesTreeCondition_eq_of_childrenBag_eq (tab : ButcherTableau s)
    {children₁ children₂ : List BTree}
    (hbag : (BTree.node children₁).childrenBag = (BTree.node children₂).childrenBag) :
    tab.satisfiesTreeCondition (.node children₁) ↔ tab.satisfiesTreeCondition (.node children₂) := by
  unfold satisfiesTreeCondition
  have hden :
      (BTree.node children₁).density = (BTree.node children₂).density :=
    BTree.density_eq_of_childrenBag_eq hbag
  have hew :
      ∀ i : Fin s,
        tab.elementaryWeight (.node children₁) i = tab.elementaryWeight (.node children₂) i := by
    intro i
    exact elementaryWeight_eq_of_childrenBag_eq tab hbag i
  constructor
  · intro h
    convert h using 1
    · congr 1
      ext i
      rw [hew i]
    · simp [hden]
  · intro h
    convert h using 1
    · congr 1
      ext i
      rw [← hew i]
    · simp [hden]

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

/-- Bushy order-3 trees have elementary weight `(∑ₖ aᵢₖ)^2`. -/
private theorem ew_of_order_three_bushy (tab : ButcherTableau s) (t : BTree)
    (hbushy : ∃ c₁ c₂ : BTree, t = .node [c₁, c₂] ∧ c₁.order = 1 ∧ c₂.order = 1)
    (i : Fin s) :
    tab.elementaryWeight t i = (∑ k : Fin s, tab.A i k) ^ 2 := by
  rcases hbushy with ⟨c₁, c₂, rfl, hc₁, hc₂⟩
  simp [elementaryWeight, List.foldr, ew_of_order_one, hc₁, hc₂, pow_two]

/-- Chain order-3 trees have elementary weight `∑ⱼ aᵢⱼ (∑ₖ aⱼₖ)`. -/
private theorem ew_of_order_three_chain (tab : ButcherTableau s) (t : BTree)
    (hchain : ∃ c : BTree, t = .node [c] ∧ c.order = 2)
    (i : Fin s) :
    tab.elementaryWeight t i = ∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) := by
  rcases hchain with ⟨c, rfl, hc⟩
  simp [elementaryWeight_singleton, ew_of_order_two, hc]

/-- Bushy order-3 trees have density `3`. -/
private theorem density_of_order_three_bushy (t : BTree)
    (hbushy : ∃ c₁ c₂ : BTree, t = .node [c₁, c₂] ∧ c₁.order = 1 ∧ c₂.order = 1) :
    t.density = 3 := by
  rcases hbushy with ⟨c₁, c₂, rfl, hc₁, hc₂⟩
  simp only [density_node, order_node, List.foldr]
  rw [density_of_order_one c₁ hc₁, density_of_order_one c₂ hc₂, hc₁, hc₂]

/-- Chain order-3 trees have density `6`. -/
private theorem density_of_order_three_chain (t : BTree)
    (hchain : ∃ c : BTree, t = .node [c] ∧ c.order = 2) :
    t.density = 6 := by
  rcases hchain with ⟨c, rfl, hc⟩
  simp only [density_node, order_node, List.foldr]
  rw [density_of_order_two c hc, hc]

/-- Bushy order-3 trees satisfy the tree condition iff the bushy order-3 condition holds. -/
private theorem satisfiesTreeCondition_order_three_bushy (tab : ButcherTableau s) (t : BTree)
    (hbushy : ∃ c₁ c₂ : BTree, t = .node [c₁, c₂] ∧ c₁.order = 1 ∧ c₂.order = 1) :
    tab.satisfiesTreeCondition t ↔
    ∑ i : Fin s, tab.b i * (∑ k : Fin s, tab.A i k) ^ 2 = 1 / 3 := by
  simp only [satisfiesTreeCondition, density_of_order_three_bushy t hbushy]
  constructor
  · intro h
    convert h using 1
    congr 1
    ext i
    congr 1
    exact (ew_of_order_three_bushy tab t hbushy i).symm
  · intro h
    convert h using 1
    congr 1
    ext i
    congr 1
    exact ew_of_order_three_bushy tab t hbushy i

/-- Chain order-3 trees satisfy the tree condition iff the chain order-3 condition holds. -/
private theorem satisfiesTreeCondition_order_three_chain (tab : ButcherTableau s) (t : BTree)
    (hchain : ∃ c : BTree, t = .node [c] ∧ c.order = 2) :
    tab.satisfiesTreeCondition t ↔
    ∑ i : Fin s, tab.b i * (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) = 1 / 6 := by
  simp only [satisfiesTreeCondition, density_of_order_three_chain t hchain]
  constructor
  · intro h
    convert h using 1
    congr 1
    ext i
    congr 1
    exact (ew_of_order_three_chain tab t hchain i).symm
  · intro h
    convert h using 1
    congr 1
    ext i
    congr 1
    exact ew_of_order_three_chain tab t hchain i

/-- A unary parent preserves tree conditions across a bag-equivalent child swap. -/
private theorem satisfiesTreeCondition_singleton_eq_of_childrenBag_eq (tab : ButcherTableau s)
    {children₁ children₂ : List BTree}
    (hbag : (BTree.node children₁).childrenBag = (BTree.node children₂).childrenBag) :
    tab.satisfiesTreeCondition (.node [BTree.node children₁]) ↔
      tab.satisfiesTreeCondition (.node [BTree.node children₂]) := by
  unfold satisfiesTreeCondition
  have horder :
      (BTree.node children₁).order = (BTree.node children₂).order :=
    BTree.order_eq_of_childrenBag_eq hbag
  have hchild_density :
      (BTree.node children₁).density = (BTree.node children₂).density :=
    BTree.density_eq_of_childrenBag_eq hbag
  have hparent_density :
      (BTree.node [BTree.node children₁]).density = (BTree.node [BTree.node children₂]).density := by
    simp [BTree.density_node, BTree.order_node, horder, hchild_density]
  have hew :
      ∀ i : Fin s,
        tab.elementaryWeight (.node [BTree.node children₁]) i =
          tab.elementaryWeight (.node [BTree.node children₂]) i := by
    intro i
    rw [elementaryWeight_singleton, elementaryWeight_singleton]
    congr 1
    ext k
    rw [elementaryWeight_eq_of_childrenBag_eq tab hbag k]
  constructor
  · intro h
    convert h using 1
    · congr 1
      ext i
      rw [hew i]
    · simp [hparent_density]
  · intro h
    convert h using 1
    · congr 1
      ext i
      rw [← hew i]
    · simp [hparent_density]

private theorem order3a_sum_eq (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    (∑ i : Fin s, tab.b i * (∑ k : Fin s, tab.A i k) ^ 2) =
      ∑ i : Fin s, tab.b i * tab.c i ^ 2 := by
  congr 1
  ext i
  congr 1
  rw [hrc i]

private theorem order3b_sum_eq (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    (∑ i : Fin s, tab.b i * (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k))) =
      ∑ i : Fin s, ∑ j : Fin s, tab.b i * tab.A i j * tab.c j := by
  calc
    ∑ i : Fin s, tab.b i * (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k))
        = ∑ i : Fin s, ∑ j : Fin s, tab.b i * (tab.A i j * (∑ k : Fin s, tab.A j k)) := by
            simp_rw [Finset.mul_sum]
    _ = ∑ i : Fin s, ∑ j : Fin s, tab.b i * (tab.A i j * tab.c j) := by
          congr 1
          ext i
          congr 1
          ext j
          rw [hrc j]
    _ = ∑ i : Fin s, ∑ j : Fin s, tab.b i * tab.A i j * tab.c j := by
          congr 1
          ext i
          congr 1
          ext j
          ring

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
  constructor
  · intro h
    refine ⟨(satisfiesTreeCondition_leaf tab).mp (h .leaf (by simp)),
      (satisfiesTreeCondition_t2_of_consistent tab hrc).mp (h t2 (by native_decide)),
      ?_, ?_⟩
    · have ht3a : tab.satisfiesTreeCondition t3a := h t3a (by native_decide)
      rw [satisfiesTreeCondition_order_three_bushy tab t3a
        ⟨.leaf, .leaf, rfl, by simp, by simp⟩] at ht3a
      rw [order3a]
      simpa [order3a_sum_eq tab hrc] using ht3a
    · have ht3b : tab.satisfiesTreeCondition t3b := h t3b (by native_decide)
      rw [satisfiesTreeCondition_order_three_chain tab t3b
        ⟨t2, rfl, by native_decide⟩] at ht3b
      rw [order3b]
      simpa [order3b_sum_eq tab hrc] using ht3b
  · rintro ⟨h1, h2, h3a, h3b⟩ t ht
    have hpos := BTree.order_pos t
    by_cases hle1 : t.order ≤ 1
    · exact (satisfiesTreeCondition_order_one tab t (by omega)).mpr h1
    · by_cases hle2 : t.order ≤ 2
      · have heq : t.order = 2 := by omega
        rw [satisfiesTreeCondition_order_two tab t heq]
        rw [order2] at h2
        convert h2 using 1
        congr 1
        ext i
        congr 1
        exact (hrc i).symm
      · have heq : t.order = 3 := by omega
        cases t with
        | leaf => simp at heq
        | node children =>
          have hw : BTree.OrderThreeBagWitness (.node children) :=
            BTree.order_three_bag_witness (.node children) heq
          cases BTree.order_three_bag_witness_recover hw with
          | chain3 c hbag hc =>
            rw [satisfiesTreeCondition_eq_of_childrenBag_eq tab hbag]
            rw [satisfiesTreeCondition_order_three_chain tab _ ⟨c, rfl, hc⟩]
            rw [order3b] at h3b
            simpa [order3b_sum_eq tab hrc] using h3b
          | bushy3 c₁ c₂ hbag hc₁ hc₂ =>
            rw [satisfiesTreeCondition_eq_of_childrenBag_eq tab hbag]
            rw [satisfiesTreeCondition_order_three_bushy tab _ ⟨c₁, c₂, rfl, hc₁, hc₂⟩]
            rw [order3a] at h3a
            simpa [order3a_sum_eq tab hrc] using h3a

/-! ### Order 4 helpers -/

/-- Bushy order-4 tree (3 leaves): ew = (∑ₖ aᵢₖ)³. -/
private theorem ew_of_order_four_bushy4 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c₁ c₂ c₃ : BTree, t = .node [c₁, c₂, c₃] ∧ c₁.order = 1 ∧ c₂.order = 1 ∧ c₃.order = 1)
    (i : Fin s) :
    tab.elementaryWeight t i = (∑ k : Fin s, tab.A i k) ^ 3 := by
  rcases h with ⟨c₁, c₂, c₃, rfl, hc₁, hc₂, hc₃⟩
  simp [elementaryWeight, List.foldr, ew_of_order_one tab c₁ hc₁, ew_of_order_one tab c₂ hc₂,
        ew_of_order_one tab c₃ hc₃]
  ring

/-- Bushy order-4 tree has density 4. -/
private theorem density_of_order_four_bushy4 (t : BTree)
    (h : ∃ c₁ c₂ c₃ : BTree, t = .node [c₁, c₂, c₃] ∧ c₁.order = 1 ∧ c₂.order = 1 ∧ c₃.order = 1) :
    t.density = 4 := by
  rcases h with ⟨c₁, c₂, c₃, rfl, hc₁, hc₂, hc₃⟩
  simp only [density_node, order_node, List.foldr]
  rw [density_of_order_one c₁ hc₁, density_of_order_one c₂ hc₂, density_of_order_one c₃ hc₃,
      hc₁, hc₂, hc₃]

/-- Mixed order-4 tree [order-1, order-2]: ew = (∑ₖ aᵢₖ)(∑ⱼ aᵢⱼ(∑ₖ aⱼₖ)). -/
private theorem ew_of_order_four_mixed12 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c₁ c₂ : BTree, t = .node [c₁, c₂] ∧ c₁.order = 1 ∧ c₂.order = 2)
    (i : Fin s) :
    tab.elementaryWeight t i =
      (∑ k : Fin s, tab.A i k) * (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) := by
  rcases h with ⟨c₁, c₂, rfl, hc₁, hc₂⟩
  simp [elementaryWeight, List.foldr, ew_of_order_one tab c₁ hc₁, ew_of_order_two tab c₂ hc₂]
  exact mul_comm _ _

/-- Mixed order-4 tree [order-1, order-2] has density 8. -/
private theorem density_of_order_four_mixed (t : BTree)
    (h : ∃ c₁ c₂ : BTree, t = .node [c₁, c₂] ∧ c₁.order = 1 ∧ c₂.order = 2) :
    t.density = 8 := by
  rcases h with ⟨c₁, c₂, rfl, hc₁, hc₂⟩
  simp only [density_node, order_node, List.foldr]
  rw [density_of_order_one c₁ hc₁, density_of_order_two c₂ hc₂, hc₁, hc₂]

/-- Transport the canonical mixed `{1,2}` elementary weight across bag-equal
two-child representations. -/
private theorem ew_of_order_four_mixed_eq_of_childrenBag_eq (tab : ButcherTableau s)
    (c₁ c₂ d₁ d₂ : BTree)
    (hcanon : c₁.order = 1 ∧ c₂.order = 2)
    (hbag : (BTree.node [d₁, d₂]).childrenBag = (BTree.node [c₁, c₂]).childrenBag)
    (i : Fin s) :
    tab.elementaryWeight (.node [d₁, d₂]) i =
      (∑ k : Fin s, tab.A i k) * (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) := by
  calc
    tab.elementaryWeight (.node [d₁, d₂]) i =
        tab.elementaryWeight (.node [c₁, c₂]) i :=
      elementaryWeight_eq_of_childrenBag_eq tab hbag i
    _ =
        (∑ k : Fin s, tab.A i k) * (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) :=
      ew_of_order_four_mixed12 tab (.node [c₁, c₂]) ⟨c₁, c₂, rfl, hcanon.1, hcanon.2⟩ i

/-- Mixed order-4 density depends only on the unordered two-child witness. -/
private theorem density_of_order_four_mixed_eq_of_childrenBag_eq
    (c₁ c₂ d₁ d₂ : BTree)
    (hcanon : c₁.order = 1 ∧ c₂.order = 2)
    (hbag : (BTree.node [d₁, d₂]).childrenBag = (BTree.node [c₁, c₂]).childrenBag) :
    (BTree.node [d₁, d₂]).density = 8 := by
  calc
    (BTree.node [d₁, d₂]).density = (BTree.node [c₁, c₂]).density :=
      BTree.density_eq_of_childrenBag_eq hbag
    _ = 8 :=
      density_of_order_four_mixed (.node [c₁, c₂]) ⟨c₁, c₂, rfl, hcanon.1, hcanon.2⟩

/-- Order-4 via bushy-3 child: ew = ∑ⱼ aᵢⱼ(∑ₖ aⱼₖ)². -/
private theorem ew_of_order_four_via_bushy3 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧ ∃ c₁ c₂ : BTree,
      c = .node [c₁, c₂] ∧ c₁.order = 1 ∧ c₂.order = 1)
    (i : Fin s) :
    tab.elementaryWeight t i = ∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2 := by
  rcases h with ⟨c, rfl, c₁, c₂, hc, hc₁, hc₂⟩
  simp [elementaryWeight_singleton, hc, elementaryWeight, List.foldr,
        ew_of_order_one tab c₁ hc₁, ew_of_order_one tab c₂ hc₂, pow_two]

/-- Order-4 via chain-3 child: ew = ∑ⱼ aᵢⱼ(∑ₖ aⱼₖ(∑ₗ aₖₗ)). -/
private theorem ew_of_order_four_via_chain3 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧ ∃ c' : BTree, c = .node [c'] ∧ c'.order = 2)
    (i : Fin s) :
    tab.elementaryWeight t i =
      ∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l)) := by
  rcases h with ⟨c, rfl, c', hc, hc'⟩
  simp [elementaryWeight_singleton, hc, elementaryWeight_singleton, ew_of_order_two tab c' hc']

/-- Order-4 via bushy-3 child has density 12. -/
private theorem density_of_order_four_via_bushy3 (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧ ∃ c₁ c₂ : BTree,
      c = .node [c₁, c₂] ∧ c₁.order = 1 ∧ c₂.order = 1) :
    t.density = 12 := by
  rcases h with ⟨c, rfl, c₁, c₂, hc, hc₁, hc₂⟩
  subst hc
  simp only [density_node, order_node, List.foldr]
  rw [density_of_order_one c₁ hc₁, density_of_order_one c₂ hc₂, hc₁, hc₂]

/-- Order-4 via chain-3 child has density 24. -/
private theorem density_of_order_four_via_chain3 (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧ ∃ c' : BTree, c = .node [c'] ∧ c'.order = 2) :
    t.density = 24 := by
  rcases h with ⟨c, rfl, c', hc, hc'⟩
  subst hc
  simp only [density_node, order_node, List.foldr]
  rw [density_of_order_two c' hc', hc']

/-- Convert bushy-4 ew sum from A-sums to c-notation. -/
private theorem order4a_sum_eq (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    (∑ i : Fin s, tab.b i * (∑ k : Fin s, tab.A i k) ^ 3) =
      ∑ i : Fin s, tab.b i * tab.c i ^ 3 := by
  congr 1; ext i; congr 1; rw [hrc i]

/-- Convert mixed ew sum from A-sums to c-notation. -/
private theorem order4b_sum_eq (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    (∑ i : Fin s, tab.b i *
      ((∑ k : Fin s, tab.A i k) * (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)))) =
      ∑ i : Fin s, tab.b i * tab.c i * (∑ j : Fin s, tab.A i j * tab.c j) := by
  have hrc' : ∀ i : Fin s, (∑ k : Fin s, tab.A i k) = tab.c i := fun i => (hrc i).symm
  congr 1; ext i; simp_rw [hrc']; ring

/-- Convert via-bushy3 ew sum from A-sums to c-notation. -/
private theorem order4c_sum_eq (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    (∑ i : Fin s, tab.b i * (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2)) =
      ∑ i : Fin s, ∑ j : Fin s, tab.b i * tab.A i j * tab.c j ^ 2 := by
  simp_rw [Finset.mul_sum]
  congr 1; ext i; congr 1; ext j
  rw [hrc j]; ring

/-- Convert via-chain3 ew sum from A-sums to c-notation. -/
private theorem order4d_sum_eq (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    (∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l)))) =
      ∑ i : Fin s, ∑ j : Fin s, ∑ k : Fin s,
        tab.b i * tab.A i j * tab.A j k * tab.c k := by
  have hrc' : ∀ i : Fin s, (∑ k : Fin s, tab.A i k) = tab.c i := fun i => (hrc i).symm
  simp_rw [hrc', Finset.mul_sum]
  congr 1; ext i; congr 1; ext j; congr 1; ext k; ring

/-- Bushy-4 satisfies tree condition iff ∑ bᵢ (∑ₖ aᵢₖ)³ = 1/4. -/
private theorem satisfiesTreeCondition_order_four_bushy4 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c₁ c₂ c₃ : BTree, t = .node [c₁, c₂, c₃] ∧ c₁.order = 1 ∧ c₂.order = 1 ∧ c₃.order = 1) :
    tab.satisfiesTreeCondition t ↔
    ∑ i : Fin s, tab.b i * (∑ k : Fin s, tab.A i k) ^ 3 = 1 / 4 := by
  simp only [satisfiesTreeCondition, density_of_order_four_bushy4 t h]
  constructor
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact (ew_of_order_four_bushy4 tab t h i).symm
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact ew_of_order_four_bushy4 tab t h i

/-- Mixed-4 (order-1, order-2) satisfies tree condition iff sum = 1/8. -/
private theorem satisfiesTreeCondition_order_four_mixed12 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c₁ c₂ : BTree, t = .node [c₁, c₂] ∧ c₁.order = 1 ∧ c₂.order = 2) :
    tab.satisfiesTreeCondition t ↔
    ∑ i : Fin s, tab.b i *
      ((∑ k : Fin s, tab.A i k) * (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k))) = 1 / 8 := by
  simp only [satisfiesTreeCondition, density_of_order_four_mixed t h]
  constructor
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact (ew_of_order_four_mixed12 tab t h i).symm
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact ew_of_order_four_mixed12 tab t h i

/-- Transport the canonical mixed `{1,2}` tree condition across bag-equal
two-child representations. -/
private theorem satisfiesTreeCondition_order_four_mixed_eq_of_childrenBag_eq
    (tab : ButcherTableau s)
    (c₁ c₂ d₁ d₂ : BTree)
    (hcanon : c₁.order = 1 ∧ c₂.order = 2)
    (hbag : (BTree.node [d₁, d₂]).childrenBag = (BTree.node [c₁, c₂]).childrenBag) :
    tab.satisfiesTreeCondition (BTree.node [d₁, d₂]) ↔
    ∑ i : Fin s, tab.b i *
      ((∑ k : Fin s, tab.A i k) * (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k))) = 1 / 8 := by
  simp only [satisfiesTreeCondition,
    density_of_order_four_mixed_eq_of_childrenBag_eq c₁ c₂ d₁ d₂ hcanon hbag]
  constructor
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact (ew_of_order_four_mixed_eq_of_childrenBag_eq tab c₁ c₂ d₁ d₂ hcanon hbag i).symm
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact ew_of_order_four_mixed_eq_of_childrenBag_eq tab c₁ c₂ d₁ d₂ hcanon hbag i

/-- Mixed order-4 nodes are canonical up to swapping the ordered child witnesses. -/
private theorem satisfiesTreeCondition_order_four_mixed_canonical (tab : ButcherTableau s)
    (c₁ c₂ : BTree)
    (hpair : (c₁.order = 1 ∧ c₂.order = 2) ∨ (c₁.order = 2 ∧ c₂.order = 1)) :
    tab.satisfiesTreeCondition (.node [c₁, c₂]) ↔
    ∑ i : Fin s, tab.b i *
      ((∑ k : Fin s, tab.A i k) * (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k))) = 1 / 8 := by
  rcases hpair with ⟨hc₁, hc₂⟩ | ⟨hc₁, hc₂⟩
  · simpa using
      (satisfiesTreeCondition_order_four_mixed12 tab (.node [c₁, c₂])
        ⟨c₁, c₂, rfl, hc₁, hc₂⟩)
  · simpa using
      satisfiesTreeCondition_order_four_mixed_eq_of_childrenBag_eq tab
        c₂ c₁ c₁ c₂ ⟨hc₂, hc₁⟩
        (BTree.node_childrenBag_eq_swap c₁ c₂)

/-- Via-bushy3 satisfies tree condition iff ∑ bᵢ (∑ⱼ aᵢⱼ (∑ₖ aⱼₖ)²) = 1/12. -/
private theorem satisfiesTreeCondition_order_four_via_bushy3 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧ ∃ c₁ c₂ : BTree,
      c = .node [c₁, c₂] ∧ c₁.order = 1 ∧ c₂.order = 1) :
    tab.satisfiesTreeCondition t ↔
    ∑ i : Fin s, tab.b i * (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2) = 1 / 12 := by
  simp only [satisfiesTreeCondition, density_of_order_four_via_bushy3 t h]
  constructor
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact (ew_of_order_four_via_bushy3 tab t h i).symm
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact ew_of_order_four_via_bushy3 tab t h i

/-- Via-chain3 satisfies tree condition iff ∑ bᵢ (∑ⱼ aᵢⱼ (∑ₖ aⱼₖ (∑ₗ aₖₗ))) = 1/24. -/
private theorem satisfiesTreeCondition_order_four_via_chain3 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧ ∃ c' : BTree, c = .node [c'] ∧ c'.order = 2) :
    tab.satisfiesTreeCondition t ↔
    ∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l))) = 1 / 24 := by
  simp only [satisfiesTreeCondition, density_of_order_four_via_chain3 t h]
  constructor
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact (ew_of_order_four_via_chain3 tab t h i).symm
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact ew_of_order_four_via_chain3 tab t h i

/-- Theorem 301A at order 4 (assuming row-sum consistency). -/
theorem thm_301A_order4 (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    tab.hasTreeOrder 4 ↔ tab.HasOrderGe4 := by
  constructor
  · intro h
    have h3 : tab.HasOrderGe3 := (thm_301A_order3 tab hrc).mp (fun t ht => h t (by omega))
    refine ⟨h3.1, h3.2.1, h3.2.2.1, h3.2.2.2, ?_, ?_, ?_, ?_⟩
    · -- order4a: from t4a = [leaf, leaf, leaf]
      have ht4a : tab.satisfiesTreeCondition t4a := h t4a (by native_decide)
      rw [satisfiesTreeCondition_order_four_bushy4 tab t4a
        ⟨.leaf, .leaf, .leaf, rfl, by simp, by simp, by simp⟩] at ht4a
      rw [order4a]
      simpa [order4a_sum_eq tab hrc] using ht4a
    · -- order4b: from t4b = [leaf, t2]
      have ht4b : tab.satisfiesTreeCondition t4b := h t4b (by native_decide)
      change tab.satisfiesTreeCondition (.node [.leaf, t2]) at ht4b
      rw [satisfiesTreeCondition_order_four_mixed_canonical tab .leaf t2
        (Or.inl ⟨by simp, by native_decide⟩)] at ht4b
      rw [order4b]
      simpa [order4b_sum_eq tab hrc] using ht4b
    · -- order4c: from t4c = [t3a] where t3a = [leaf, leaf]
      have ht4c : tab.satisfiesTreeCondition t4c := h t4c (by native_decide)
      rw [satisfiesTreeCondition_order_four_via_bushy3 tab t4c
        ⟨t3a, rfl, .leaf, .leaf, rfl, by simp, by simp⟩] at ht4c
      rw [order4c]
      simpa [order4c_sum_eq tab hrc] using ht4c
    · -- order4d: from t4d = [t3b] where t3b = [t2]
      have ht4d : tab.satisfiesTreeCondition t4d := h t4d (by native_decide)
      rw [satisfiesTreeCondition_order_four_via_chain3 tab t4d
        ⟨t3b, rfl, t2, rfl, by native_decide⟩] at ht4d
      rw [order4d]
      simpa [order4d_sum_eq tab hrc] using ht4d
  · rintro ⟨h1, h2, h3a, h3b, h4a, h4b, h4c, h4d⟩ t ht
    have hpos := BTree.order_pos t
    by_cases hle3 : t.order ≤ 3
    · exact ((thm_301A_order3 tab hrc).mpr ⟨h1, h2, h3a, h3b⟩) t hle3
    · have heq : t.order = 4 := by omega
      cases t with
      | leaf => simp at heq
      | node children =>
        have hw4 : BTree.OrderFourBagWitness (.node children) :=
          BTree.order_four_bag_witness (.node children) heq
        cases BTree.order_four_bag_witness_recover hw4 with
        | bushy4 c₁ c₂ c₃ hbag hc₁ hc₂ hc₃ =>
          rw [satisfiesTreeCondition_eq_of_childrenBag_eq tab hbag]
          rw [satisfiesTreeCondition_order_four_bushy4 tab _ ⟨c₁, c₂, c₃, rfl, hc₁, hc₂, hc₃⟩]
          rw [order4a] at h4a
          simpa [order4a_sum_eq tab hrc] using h4a
        | mixed4 c₁ c₂ hbag hcanon =>
          rw [satisfiesTreeCondition_eq_of_childrenBag_eq tab hbag]
          rw [satisfiesTreeCondition_order_four_mixed12 tab _ ⟨c₁, c₂, rfl, hcanon.1, hcanon.2⟩]
          rw [order4b] at h4b
          simpa [order4b_sum_eq tab hrc] using h4b
        | singleChain3 child3 c' hbag hchildBag hc' =>
            rw [satisfiesTreeCondition_eq_of_childrenBag_eq tab hbag]
            cases child3 with
            | leaf =>
                have hcard := congrArg Multiset.card hchildBag
                simp at hcard
            | node childChildren =>
                rw [satisfiesTreeCondition_singleton_eq_of_childrenBag_eq tab hchildBag]
                rw [satisfiesTreeCondition_order_four_via_chain3 tab _
                  ⟨.node [c'], rfl, c', rfl, hc'⟩]
                rw [order4d] at h4d
                simpa [order4d_sum_eq tab hrc] using h4d
        | singleBushy3 child3 c₁ c₂ hbag hchildBag hc₁ hc₂ =>
            rw [satisfiesTreeCondition_eq_of_childrenBag_eq tab hbag]
            cases child3 with
            | leaf =>
                have hcard := congrArg Multiset.card hchildBag
                simp at hcard
            | node childChildren =>
                rw [satisfiesTreeCondition_singleton_eq_of_childrenBag_eq tab hchildBag]
                rw [satisfiesTreeCondition_order_four_via_bushy3 tab _
                  ⟨.node [c₁, c₂], rfl, c₁, c₂, rfl, hc₁, hc₂⟩]
                rw [order4c] at h4c
                simpa [order4c_sum_eq tab hrc] using h4c

/-! ### Order 5 helpers -/

/-- Bushy order-5 tree (4 leaves): ew = (∑ₖ aᵢₖ)⁴. -/
private theorem ew_of_order_five_bushy5 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c₁ c₂ c₃ c₄ : BTree, t = .node [c₁, c₂, c₃, c₄] ∧
      c₁.order = 1 ∧ c₂.order = 1 ∧ c₃.order = 1 ∧ c₄.order = 1)
    (i : Fin s) :
    tab.elementaryWeight t i = (∑ k : Fin s, tab.A i k) ^ 4 := by
  rcases h with ⟨c₁, c₂, c₃, c₄, rfl, hc₁, hc₂, hc₃, hc₄⟩
  simp [elementaryWeight, List.foldr, ew_of_order_one tab c₁ hc₁, ew_of_order_one tab c₂ hc₂,
        ew_of_order_one tab c₃ hc₃, ew_of_order_one tab c₄ hc₄]
  ring

/-- 3-child [order-1, order-1, order-2]: ew = (∑ₖ aᵢₖ)² · (∑ⱼ aᵢⱼ(∑ₖ aⱼₖ)). -/
private theorem ew_of_order_five_112 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c₁ c₂ c₃ : BTree, t = .node [c₁, c₂, c₃] ∧
      c₁.order = 1 ∧ c₂.order = 1 ∧ c₃.order = 2)
    (i : Fin s) :
    tab.elementaryWeight t i =
      (∑ k : Fin s, tab.A i k) ^ 2 *
      (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) := by
  rcases h with ⟨c₁, c₂, c₃, rfl, hc₁, hc₂, hc₃⟩
  simp [elementaryWeight, List.foldr, ew_of_order_one tab c₁ hc₁,
        ew_of_order_one tab c₂ hc₂, ew_of_order_two tab c₃ hc₃]
  ring

/-- Transport the canonical `{1,1,2}` elementary-weight formula across
bag-equal three-child representations. -/
private theorem ew_of_order_five_3child_eq_of_childrenBag_eq (tab : ButcherTableau s)
    (c₁ c₂ c₃ d₁ d₂ d₃ : BTree)
    (hcanon : c₁.order = 1 ∧ c₂.order = 1 ∧ c₃.order = 2)
    (hbag : (BTree.node [d₁, d₂, d₃]).childrenBag = (BTree.node [c₁, c₂, c₃]).childrenBag)
    (i : Fin s) :
    tab.elementaryWeight (.node [d₁, d₂, d₃]) i =
      (∑ k : Fin s, tab.A i k) ^ 2 *
      (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) := by
  exact
    (elementaryWeight_eq_of_childrenBag_eq tab hbag i).trans <|
      ew_of_order_five_112 tab (.node [c₁, c₂, c₃])
        ⟨c₁, c₂, c₃, rfl, hcanon.1, hcanon.2.1, hcanon.2.2⟩ i

/-- 3-child [order-1, order-2, order-1]: same ew by commutativity. -/
private theorem ew_of_order_five_121 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c₁ c₂ c₃ : BTree, t = .node [c₁, c₂, c₃] ∧
      c₁.order = 1 ∧ c₂.order = 2 ∧ c₃.order = 1)
    (i : Fin s) :
    tab.elementaryWeight t i =
      (∑ k : Fin s, tab.A i k) ^ 2 *
      (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) := by
  rcases h with ⟨c₁, c₂, c₃, rfl, hc₁, hc₂, hc₃⟩
  simpa using
    ew_of_order_five_3child_eq_of_childrenBag_eq tab
      c₃ c₁ c₂ c₁ c₂ c₃ ⟨hc₃, hc₁, hc₂⟩
      (BTree.node_childrenBag_eq_rotate_right c₁ c₂ c₃) i

/-- 3-child [order-2, order-1, order-1]: same ew by commutativity. -/
private theorem ew_of_order_five_211 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c₁ c₂ c₃ : BTree, t = .node [c₁, c₂, c₃] ∧
      c₁.order = 2 ∧ c₂.order = 1 ∧ c₃.order = 1)
    (i : Fin s) :
    tab.elementaryWeight t i =
      (∑ k : Fin s, tab.A i k) ^ 2 *
      (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) := by
  rcases h with ⟨c₁, c₂, c₃, rfl, hc₁, hc₂, hc₃⟩
  simpa using
    ew_of_order_five_3child_eq_of_childrenBag_eq tab
      c₂ c₃ c₁ c₁ c₂ c₃ ⟨hc₂, hc₃, hc₁⟩
      (BTree.node_childrenBag_eq_rotate_left c₁ c₂ c₃) i

/-- 2-child [order-1, bushy-3]: ew = (∑ₖ aᵢₖ) · (∑ⱼ aᵢⱼ(∑ₖ aⱼₖ)²). -/
private theorem ew_of_order_five_1_bushy3 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c₁ c₂ : BTree, t = .node [c₁, c₂] ∧ c₁.order = 1 ∧
      ∃ d₁ d₂ : BTree, c₂ = .node [d₁, d₂] ∧ d₁.order = 1 ∧ d₂.order = 1)
    (i : Fin s) :
    tab.elementaryWeight t i =
      (∑ k : Fin s, tab.A i k) *
      (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2) := by
  rcases h with ⟨c₁, c₂, rfl, hc₁, d₁, d₂, hc₂, hd₁, hd₂⟩
  simp [elementaryWeight, List.foldr, ew_of_order_one tab c₁ hc₁, hc₂,
        ew_of_order_one tab d₁ hd₁, ew_of_order_one tab d₂ hd₂, pow_two]
  ring

/-- Transport the canonical `{1, bushy-3}` elementary weight formula across
bag-equal two-child representations. -/
private theorem ew_of_order_five_bushy3_eq_of_childrenBag_eq (tab : ButcherTableau s)
    (c₁ c₂ d₁ d₂ e₁ e₂ : BTree)
    (hcanon : c₁.order = 1 ∧ c₂ = BTree.node [e₁, e₂] ∧ e₁.order = 1 ∧ e₂.order = 1)
    (hbag : (BTree.node [d₁, d₂]).childrenBag = (BTree.node [c₁, c₂]).childrenBag)
    (i : Fin s) :
    tab.elementaryWeight (BTree.node [d₁, d₂]) i =
      (∑ k : Fin s, tab.A i k) *
      (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2) := by
  exact
    (elementaryWeight_eq_of_childrenBag_eq tab hbag i).trans <|
      ew_of_order_five_1_bushy3 tab (BTree.node [c₁, c₂])
        ⟨c₁, c₂, rfl, hcanon.1, e₁, e₂, hcanon.2.1, hcanon.2.2.1, hcanon.2.2.2⟩ i

/-- 2-child [order-1, chain-3]: ew = (∑ₖ aᵢₖ) · (∑ⱼ aᵢⱼ(∑ₖ aⱼₖ(∑ₗ aₖₗ))). -/
private theorem ew_of_order_five_1_chain3 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c₁ c₂ : BTree, t = .node [c₁, c₂] ∧ c₁.order = 1 ∧
      ∃ d : BTree, c₂ = .node [d] ∧ d.order = 2)
    (i : Fin s) :
    tab.elementaryWeight t i =
      (∑ k : Fin s, tab.A i k) *
      (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l))) := by
  rcases h with ⟨c₁, c₂, rfl, hc₁, d, hc₂, hd⟩
  simp [elementaryWeight, List.foldr, ew_of_order_one tab c₁ hc₁, hc₂,
        elementaryWeight_singleton, ew_of_order_two tab d hd]
  ring

/-- Transport the canonical `{1, chain-3}` elementary weight formula across
bag-equal two-child representations. -/
private theorem ew_of_order_five_chain3_eq_of_childrenBag_eq (tab : ButcherTableau s)
    (c₁ c₂ d₁ d₂ d : BTree)
    (hcanon : c₁.order = 1 ∧ c₂ = BTree.node [d] ∧ d.order = 2)
    (hbag : (BTree.node [d₁, d₂]).childrenBag = (BTree.node [c₁, c₂]).childrenBag)
    (i : Fin s) :
    tab.elementaryWeight (BTree.node [d₁, d₂]) i =
      (∑ k : Fin s, tab.A i k) *
      (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l))) := by
  exact
    (elementaryWeight_eq_of_childrenBag_eq tab hbag i).trans <|
      ew_of_order_five_1_chain3 tab (BTree.node [c₁, c₂])
        ⟨c₁, c₂, rfl, hcanon.1, d, hcanon.2.1, hcanon.2.2⟩ i

/-- 2-child [order-2, order-2]: ew = (∑ⱼ aᵢⱼ(∑ₖ aⱼₖ))². -/
private theorem ew_of_order_five_22 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c₁ c₂ : BTree, t = .node [c₁, c₂] ∧ c₁.order = 2 ∧ c₂.order = 2)
    (i : Fin s) :
    tab.elementaryWeight t i =
      (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) ^ 2 := by
  rcases h with ⟨c₁, c₂, rfl, hc₁, hc₂⟩
  simp [elementaryWeight, List.foldr, ew_of_order_two tab c₁ hc₁, ew_of_order_two tab c₂ hc₂,
        pow_two]

/-- Single child bushy-4: ew = ∑ⱼ aᵢⱼ(∑ₖ aⱼₖ)³. -/
private theorem ew_of_order_five_via_bushy4 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧
      ∃ d₁ d₂ d₃ : BTree, c = .node [d₁, d₂, d₃] ∧
        d₁.order = 1 ∧ d₂.order = 1 ∧ d₃.order = 1)
    (i : Fin s) :
    tab.elementaryWeight t i =
      ∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) ^ 3 := by
  rcases h with ⟨c, rfl, d₁, d₂, d₃, hc, hd₁, hd₂, hd₃⟩
  simp [elementaryWeight_singleton, hc, elementaryWeight, List.foldr,
        ew_of_order_one tab d₁ hd₁, ew_of_order_one tab d₂ hd₂, ew_of_order_one tab d₃ hd₃]
  congr 1; ext j; ring

/-- Single child mixed [1,2]: ew = ∑ⱼ aᵢⱼ(∑ₖ aⱼₖ)(∑ₗ aⱼₗ(∑ₘ aₗₘ)). -/
private theorem ew_of_order_five_via_mixed12 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧
      ∃ d₁ d₂ : BTree, c = .node [d₁, d₂] ∧ d₁.order = 1 ∧ d₂.order = 2)
    (i : Fin s) :
    tab.elementaryWeight t i =
      ∑ j : Fin s, tab.A i j *
        ((∑ k : Fin s, tab.A j k) * (∑ l : Fin s, tab.A j l * (∑ m : Fin s, tab.A l m))) := by
  rcases h with ⟨c, rfl, d₁, d₂, hc, hd₁, hd₂⟩
  simp [elementaryWeight_singleton, hc, elementaryWeight, List.foldr,
        ew_of_order_one tab d₁ hd₁, ew_of_order_two tab d₂ hd₂]
  congr 1; ext j; ring

/-- Transport the canonical unary mixed `{1,2}` elementary weight formula across
bag-equal presentations of the inner two-child witness. -/
private theorem ew_of_order_five_via_mixed_eq_of_childrenBag_eq (tab : ButcherTableau s)
    (c₁ c₂ d₁ d₂ : BTree)
    (hcanon : c₁.order = 1 ∧ c₂.order = 2)
    (hbag : (BTree.node [d₁, d₂]).childrenBag = (BTree.node [c₁, c₂]).childrenBag)
    (i : Fin s) :
    tab.elementaryWeight (.node [.node [d₁, d₂]]) i =
      ∑ j : Fin s, tab.A i j *
        ((∑ k : Fin s, tab.A j k) * (∑ l : Fin s, tab.A j l * (∑ m : Fin s, tab.A l m))) := by
  have heq :
      tab.elementaryWeight (.node [.node [d₁, d₂]]) i =
        tab.elementaryWeight (.node [.node [c₁, c₂]]) i := by
    rw [elementaryWeight_singleton, elementaryWeight_singleton]
    congr 1
    ext k
    rw [elementaryWeight_eq_of_childrenBag_eq tab hbag k]
  exact heq.trans <|
    ew_of_order_five_via_mixed12 tab (.node [.node [c₁, c₂]])
      ⟨.node [c₁, c₂], rfl, c₁, c₂, rfl, hcanon.1, hcanon.2⟩ i

/-- Single child via-bushy3: ew = ∑ⱼ aᵢⱼ(∑ₖ aⱼₖ(∑ₗ aₖₗ)²). -/
private theorem ew_of_order_five_via_via_bushy3 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧
      ∃ d : BTree, c = .node [d] ∧
        ∃ e₁ e₂ : BTree, d = .node [e₁, e₂] ∧ e₁.order = 1 ∧ e₂.order = 1)
    (i : Fin s) :
    tab.elementaryWeight t i =
      ∑ j : Fin s, tab.A i j *
        (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l) ^ 2) := by
  rcases h with ⟨c, rfl, d, hc, e₁, e₂, hd, he₁, he₂⟩
  simp [elementaryWeight_singleton, hc, elementaryWeight_singleton, hd,
        elementaryWeight, List.foldr,
        ew_of_order_one tab e₁ he₁, ew_of_order_one tab e₂ he₂, pow_two]

/-- Transport the canonical unary `via_via_bushy3` elementary-weight formula
across bag-equal presentations of the inner bushy child. -/
private theorem ew_of_order_five_via_via_bushy3_eq_of_childrenBag_eq (tab : ButcherTableau s)
    (c₁ c₂ d₁ d₂ : BTree)
    (hcanon : c₁.order = 1 ∧ c₂.order = 1)
    (hbag : (BTree.node [d₁, d₂]).childrenBag = (BTree.node [c₁, c₂]).childrenBag)
    (i : Fin s) :
    tab.elementaryWeight (.node [.node [.node [d₁, d₂]]]) i =
      ∑ j : Fin s, tab.A i j *
        (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l) ^ 2) := by
  have hew :
      ∀ j : Fin s,
        tab.elementaryWeight (.node [.node [d₁, d₂]]) j =
          tab.elementaryWeight (.node [.node [c₁, c₂]]) j := by
    intro j
    rw [elementaryWeight_singleton, elementaryWeight_singleton]
    congr 1
    ext k
    rw [elementaryWeight_eq_of_childrenBag_eq tab hbag k]
  calc
    tab.elementaryWeight (.node [.node [.node [d₁, d₂]]]) i =
      tab.elementaryWeight (.node [.node [.node [c₁, c₂]]]) i := by
        rw [elementaryWeight_singleton, elementaryWeight_singleton]
        congr 1
        ext j
        rw [hew j]
    _ =
      ∑ j : Fin s, tab.A i j *
        (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l) ^ 2) := by
        exact
          ew_of_order_five_via_via_bushy3 tab (.node [.node [.node [c₁, c₂]]])
            ⟨.node [.node [c₁, c₂]], rfl, .node [c₁, c₂], rfl,
              c₁, c₂, rfl, hcanon.1, hcanon.2⟩ i

/-- Single child via-chain3: ew = ∑ⱼ aᵢⱼ(∑ₖ aⱼₖ(∑ₗ aₖₗ(∑ₘ aₗₘ))). -/
private theorem ew_of_order_five_via_via_chain3 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧
      ∃ d : BTree, c = .node [d] ∧ ∃ e : BTree, d = .node [e] ∧ e.order = 2)
    (i : Fin s) :
    tab.elementaryWeight t i =
      ∑ j : Fin s, tab.A i j *
        (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l * (∑ m : Fin s, tab.A l m))) := by
  rcases h with ⟨c, rfl, d, hc, e, hd, he⟩
  simp [elementaryWeight_singleton, hc, elementaryWeight_singleton, hd,
        elementaryWeight_singleton, ew_of_order_two tab e he]

/-- Transport the canonical unary `via_via_chain3` elementary-weight formula
across bag-equal presentations of the inner chain child. -/
private theorem ew_of_order_five_via_via_chain3_eq_of_childrenBag_eq (tab : ButcherTableau s)
    (c d : BTree)
    (hcanon : c.order = 2)
    (hbag : (BTree.node [d]).childrenBag = (BTree.node [c]).childrenBag)
    (i : Fin s) :
    tab.elementaryWeight (.node [.node [.node [d]]]) i =
      ∑ j : Fin s, tab.A i j *
        (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l * (∑ m : Fin s, tab.A l m))) := by
  have hew :
      ∀ j : Fin s,
        tab.elementaryWeight (.node [.node [d]]) j =
          tab.elementaryWeight (.node [.node [c]]) j := by
    intro j
    rw [elementaryWeight_singleton, elementaryWeight_singleton]
    congr 1
    ext k
    rw [elementaryWeight_eq_of_childrenBag_eq tab hbag k]
  calc
    tab.elementaryWeight (.node [.node [.node [d]]]) i =
      tab.elementaryWeight (.node [.node [.node [c]]]) i := by
        rw [elementaryWeight_singleton, elementaryWeight_singleton]
        congr 1
        ext j
        rw [hew j]
    _ =
      ∑ j : Fin s, tab.A i j *
        (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l * (∑ m : Fin s, tab.A l m))) := by
        exact
          ew_of_order_five_via_via_chain3 tab (.node [.node [.node [c]]])
            ⟨.node [.node [c]], rfl, .node [c], rfl, c, rfl, hcanon⟩ i

/-- Bushy-5 has density 5. -/
private theorem density_of_order_five_bushy5 (t : BTree)
    (h : ∃ c₁ c₂ c₃ c₄ : BTree, t = .node [c₁, c₂, c₃, c₄] ∧
      c₁.order = 1 ∧ c₂.order = 1 ∧ c₃.order = 1 ∧ c₄.order = 1) :
    t.density = 5 := by
  rcases h with ⟨c₁, c₂, c₃, c₄, rfl, hc₁, hc₂, hc₃, hc₄⟩
  simp only [density_node, order_node, List.foldr]
  rw [density_of_order_one c₁ hc₁, density_of_order_one c₂ hc₂,
      density_of_order_one c₃ hc₃, density_of_order_one c₄ hc₄, hc₁, hc₂, hc₃, hc₄]

/-- 3-child with orders summing to 4 has density 10. -/
private theorem density_of_order_five_3child (t : BTree)
    (h : ∃ c₁ c₂ c₃ : BTree, t = .node [c₁, c₂, c₃] ∧
      c₁.order + c₂.order + c₃.order = 4) :
    t.density = 10 := by
  rcases h with ⟨c₁, c₂, c₃, rfl, hsum⟩
  simp only [density_node, order_node, List.foldr]
  have hc₁_pos := BTree.order_pos c₁
  have hc₂_pos := BTree.order_pos c₂
  have hc₃_pos := BTree.order_pos c₃
  -- All orders ≥ 1 and sum = 4 with 3 children → exactly one is 2, others are 1
  by_cases h1 : c₁.order = 1
  · by_cases h2 : c₂.order = 1
    · have h3 : c₃.order = 2 := by omega
      rw [density_of_order_one c₁ h1, density_of_order_one c₂ h2,
          density_of_order_two c₃ h3, h1, h2, h3]
    · have h2' : c₂.order = 2 := by omega
      have h3 : c₃.order = 1 := by omega
      rw [density_of_order_one c₁ h1, density_of_order_two c₂ h2',
          density_of_order_one c₃ h3, h1, h2', h3]
  · have h1' : c₁.order = 2 := by omega
    have h2 : c₂.order = 1 := by omega
    have h3 : c₃.order = 1 := by omega
    rw [density_of_order_two c₁ h1', density_of_order_one c₂ h2,
        density_of_order_one c₃ h3, h1', h2, h3]

/-- 2-child [order-1, order-3] has density determined by the order-3 shape. -/
private theorem density_of_order_five_1_bushy3 (t : BTree)
    (h : ∃ c₁ c₂ : BTree, t = .node [c₁, c₂] ∧ c₁.order = 1 ∧
      ∃ d₁ d₂ : BTree, c₂ = .node [d₁, d₂] ∧ d₁.order = 1 ∧ d₂.order = 1) :
    t.density = 15 := by
  rcases h with ⟨c₁, c₂, rfl, hc₁, d₁, d₂, hc₂, hd₁, hd₂⟩
  subst hc₂
  simp only [density_node, order_node, List.foldr]
  rw [density_of_order_one c₁ hc₁, density_of_order_one d₁ hd₁,
      density_of_order_one d₂ hd₂, hc₁, hd₁, hd₂]

/-- Transport the canonical `{1, bushy-3}` density formula across bag-equal
two-child representations. -/
private theorem density_of_order_five_bushy3_eq_of_childrenBag_eq
    (c₁ c₂ d₁ d₂ e₁ e₂ : BTree)
    (hcanon : c₁.order = 1 ∧ c₂ = BTree.node [e₁, e₂] ∧ e₁.order = 1 ∧ e₂.order = 1)
    (hbag : (BTree.node [d₁, d₂]).childrenBag = (BTree.node [c₁, c₂]).childrenBag) :
    (BTree.node [d₁, d₂]).density = 15 := by
  exact
    (BTree.density_eq_of_childrenBag_eq hbag).trans <|
      density_of_order_five_1_bushy3 (BTree.node [c₁, c₂])
        ⟨c₁, c₂, rfl, hcanon.1, e₁, e₂, hcanon.2.1, hcanon.2.2.1, hcanon.2.2.2⟩

/-- 2-child [order-1, chain-3] has density 30. -/
private theorem density_of_order_five_1_chain3 (t : BTree)
    (h : ∃ c₁ c₂ : BTree, t = .node [c₁, c₂] ∧ c₁.order = 1 ∧
      ∃ d : BTree, c₂ = .node [d] ∧ d.order = 2) :
    t.density = 30 := by
  rcases h with ⟨c₁, c₂, rfl, hc₁, d, hc₂, hd⟩
  subst hc₂
  simp only [density_node, order_node, List.foldr]
  rw [density_of_order_one c₁ hc₁, density_of_order_two d hd, hc₁, hd]

/-- Transport the canonical `{1, chain-3}` density formula across bag-equal
two-child representations. -/
private theorem density_of_order_five_chain3_eq_of_childrenBag_eq
    (c₁ c₂ d₁ d₂ d : BTree)
    (hcanon : c₁.order = 1 ∧ c₂ = BTree.node [d] ∧ d.order = 2)
    (hbag : (BTree.node [d₁, d₂]).childrenBag = (BTree.node [c₁, c₂]).childrenBag) :
    (BTree.node [d₁, d₂]).density = 30 := by
  exact
    (BTree.density_eq_of_childrenBag_eq hbag).trans <|
      density_of_order_five_1_chain3 (BTree.node [c₁, c₂])
        ⟨c₁, c₂, rfl, hcanon.1, d, hcanon.2.1, hcanon.2.2⟩

/-- 2-child [order-2, order-2] has density 20. -/
private theorem density_of_order_five_22 (t : BTree)
    (h : ∃ c₁ c₂ : BTree, t = .node [c₁, c₂] ∧ c₁.order = 2 ∧ c₂.order = 2) :
    t.density = 20 := by
  rcases h with ⟨c₁, c₂, rfl, hc₁, hc₂⟩
  simp only [density_node, order_node, List.foldr]
  rw [density_of_order_two c₁ hc₁, density_of_order_two c₂ hc₂, hc₁, hc₂]

/-- Single bushy-4 child has density 20. -/
private theorem density_of_order_five_via_bushy4 (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧
      ∃ d₁ d₂ d₃ : BTree, c = .node [d₁, d₂, d₃] ∧
        d₁.order = 1 ∧ d₂.order = 1 ∧ d₃.order = 1) :
    t.density = 20 := by
  rcases h with ⟨c, rfl, d₁, d₂, d₃, hc, hd₁, hd₂, hd₃⟩
  subst hc
  simp only [density_node, order_node, List.foldr]
  rw [density_of_order_one d₁ hd₁, density_of_order_one d₂ hd₂,
      density_of_order_one d₃ hd₃, hd₁, hd₂, hd₃]

/-- Single mixed child [1,2] has density 40. -/
private theorem density_of_order_five_via_mixed (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧
      ∃ d₁ d₂ : BTree, c = .node [d₁, d₂] ∧ d₁.order + d₂.order = 3 ∧
        ((d₁.order = 1 ∧ d₂.order = 2) ∨ (d₁.order = 2 ∧ d₂.order = 1))) :
    t.density = 40 := by
  rcases h with ⟨c, rfl, d₁, d₂, hc, _, hord⟩
  subst hc
  rcases hord with ⟨hd₁, hd₂⟩ | ⟨hd₁, hd₂⟩
  · simp only [density_node, order_node, List.foldr]
    rw [density_of_order_one d₁ hd₁, density_of_order_two d₂ hd₂, hd₁, hd₂]
  · simp only [density_node, order_node, List.foldr]
    rw [density_of_order_two d₁ hd₁, density_of_order_one d₂ hd₂, hd₁, hd₂]

/-- Single via-bushy3 child has density 60. -/
private theorem density_of_order_five_via_via_bushy3 (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧
      ∃ d : BTree, c = .node [d] ∧
        ∃ e₁ e₂ : BTree, d = .node [e₁, e₂] ∧ e₁.order = 1 ∧ e₂.order = 1) :
    t.density = 60 := by
  rcases h with ⟨c, rfl, d, hc, e₁, e₂, hd, he₁, he₂⟩
  subst hc; subst hd
  simp only [density_node, order_node, List.foldr]
  rw [density_of_order_one e₁ he₁, density_of_order_one e₂ he₂, he₁, he₂]

/-- Transport the canonical unary `via_via_bushy3` density across bag-equal
presentations of the inner bushy child. -/
private theorem density_of_order_five_via_via_bushy3_eq_of_childrenBag_eq
    (c₁ c₂ d₁ d₂ : BTree)
    (hcanon : c₁.order = 1 ∧ c₂.order = 1)
    (hbag : (BTree.node [d₁, d₂]).childrenBag = (BTree.node [c₁, c₂]).childrenBag) :
    (BTree.node [BTree.node [BTree.node [d₁, d₂]]]).density = 60 := by
  have horder :
      (BTree.node [d₁, d₂]).order = (BTree.node [c₁, c₂]).order :=
    BTree.order_eq_of_childrenBag_eq hbag
  have hden :
      (BTree.node [d₁, d₂]).density = (BTree.node [c₁, c₂]).density :=
    BTree.density_eq_of_childrenBag_eq hbag
  calc
    (BTree.node [BTree.node [BTree.node [d₁, d₂]]]).density =
      (BTree.node [BTree.node [BTree.node [c₁, c₂]]]).density := by
        simp [BTree.density_node, BTree.order_node, horder, hden]
    _ = 60 := by
        exact
          density_of_order_five_via_via_bushy3 (.node [.node [.node [c₁, c₂]]])
            ⟨.node [.node [c₁, c₂]], rfl, .node [c₁, c₂], rfl,
              c₁, c₂, rfl, hcanon.1, hcanon.2⟩

/-- Single via-chain3 child has density 120. -/
private theorem density_of_order_five_via_via_chain3 (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧
      ∃ d : BTree, c = .node [d] ∧ ∃ e : BTree, d = .node [e] ∧ e.order = 2) :
    t.density = 120 := by
  rcases h with ⟨c, rfl, d, hc, e, hd, he⟩
  subst hc; subst hd
  simp only [density_node, order_node, List.foldr]
  rw [density_of_order_two e he, he]

/-- Transport the canonical unary `via_via_chain3` density across bag-equal
presentations of the inner chain child. -/
private theorem density_of_order_five_via_via_chain3_eq_of_childrenBag_eq
    (c d : BTree)
    (hcanon : c.order = 2)
    (hbag : (BTree.node [d]).childrenBag = (BTree.node [c]).childrenBag) :
    (BTree.node [BTree.node [BTree.node [d]]]).density = 120 := by
  have horder : (BTree.node [d]).order = (BTree.node [c]).order :=
    BTree.order_eq_of_childrenBag_eq hbag
  have hden : (BTree.node [d]).density = (BTree.node [c]).density :=
    BTree.density_eq_of_childrenBag_eq hbag
  calc
    (BTree.node [BTree.node [BTree.node [d]]]).density =
      (BTree.node [BTree.node [BTree.node [c]]]).density := by
        simp [BTree.density_node, BTree.order_node, horder, hden]
    _ = 120 := by
        exact
          density_of_order_five_via_via_chain3 (.node [.node [.node [c]]])
            ⟨.node [.node [c]], rfl, .node [c], rfl, c, rfl, hcanon⟩

/-! #### Tree condition equivalences for order 5 -/

/-- Bushy-5 tree condition: ∑ bᵢ (∑ₖ aᵢₖ)⁴ = 1/5. -/
private theorem satisfiesTreeCondition_order_five_bushy5 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c₁ c₂ c₃ c₄ : BTree, t = .node [c₁, c₂, c₃, c₄] ∧
      c₁.order = 1 ∧ c₂.order = 1 ∧ c₃.order = 1 ∧ c₄.order = 1) :
    tab.satisfiesTreeCondition t ↔
    ∑ i : Fin s, tab.b i * (∑ k : Fin s, tab.A i k) ^ 4 = 1 / 5 := by
  simp only [satisfiesTreeCondition, density_of_order_five_bushy5 t h]
  constructor
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact (ew_of_order_five_bushy5 tab t h i).symm
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact ew_of_order_five_bushy5 tab t h i

/-- 3-child tree condition: ∑ bᵢ (∑ₖ aᵢₖ)² (∑ⱼ aᵢⱼ(∑ₖ aⱼₖ)) = 1/10. -/
private theorem satisfiesTreeCondition_order_five_3child_112 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c₁ c₂ c₃ : BTree, t = .node [c₁, c₂, c₃] ∧
      c₁.order = 1 ∧ c₂.order = 1 ∧ c₃.order = 2) :
    tab.satisfiesTreeCondition t ↔
    ∑ i : Fin s, tab.b i *
      ((∑ k : Fin s, tab.A i k) ^ 2 *
       (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k))) = 1 / 10 := by
  have h3 : ∃ c₁ c₂ c₃ : BTree, t = .node [c₁, c₂, c₃] ∧
      c₁.order + c₂.order + c₃.order = 4 := by
    rcases h with ⟨c₁, c₂, c₃, rfl, hc₁, hc₂, hc₃⟩
    exact ⟨c₁, c₂, c₃, rfl, by omega⟩
  simp only [satisfiesTreeCondition, density_of_order_five_3child t h3]
  constructor
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact (ew_of_order_five_112 tab t h i).symm
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact ew_of_order_five_112 tab t h i

/-- Transport the canonical `{1,1,2}` order-5 three-child condition across
bag-equal child representations. -/
private theorem satisfiesTreeCondition_order_five_3child_eq_of_childrenBag_eq
    (tab : ButcherTableau s)
    (c₁ c₂ c₃ d₁ d₂ d₃ : BTree)
    (hcanon : c₁.order = 1 ∧ c₂.order = 1 ∧ c₃.order = 2)
    (hbag : (BTree.node [d₁, d₂, d₃]).childrenBag = (BTree.node [c₁, c₂, c₃]).childrenBag) :
    tab.satisfiesTreeCondition (.node [d₁, d₂, d₃]) ↔
    ∑ i : Fin s, tab.b i *
      ((∑ k : Fin s, tab.A i k) ^ 2 *
       (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k))) = 1 / 10 := by
  exact
    (satisfiesTreeCondition_eq_of_childrenBag_eq tab hbag).trans <|
      satisfiesTreeCondition_order_five_3child_112 tab (.node [c₁, c₂, c₃])
        ⟨c₁, c₂, c₃, rfl, hcanon.1, hcanon.2.1, hcanon.2.2⟩

/-- The `{1,1,2}` three-child family is canonical up to bag equality. -/
private theorem satisfiesTreeCondition_order_five_3child_canonical (tab : ButcherTableau s)
    (c₁ c₂ c₃ : BTree)
    (hord : (c₁.order = 1 ∧ c₂.order = 1 ∧ c₃.order = 2) ∨
      (c₁.order = 1 ∧ c₂.order = 2 ∧ c₃.order = 1) ∨
      (c₁.order = 2 ∧ c₂.order = 1 ∧ c₃.order = 1)) :
    tab.satisfiesTreeCondition (.node [c₁, c₂, c₃]) ↔
    ∑ i : Fin s, tab.b i *
      ((∑ k : Fin s, tab.A i k) ^ 2 *
       (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k))) = 1 / 10 := by
  rcases hord with ⟨hc₁, hc₂, hc₃⟩ | ⟨hc₁, hc₂, hc₃⟩ | ⟨hc₁, hc₂, hc₃⟩
  · simpa using
      (satisfiesTreeCondition_order_five_3child_112 tab (.node [c₁, c₂, c₃])
        ⟨c₁, c₂, c₃, rfl, hc₁, hc₂, hc₃⟩)
  · simpa using
      (satisfiesTreeCondition_order_five_3child_eq_of_childrenBag_eq tab
        c₁ c₃ c₂ c₁ c₂ c₃ ⟨hc₁, hc₃, hc₂⟩
        (BTree.node_childrenBag_eq_swap_right c₁ c₂ c₃))
  · simpa using
      (satisfiesTreeCondition_order_five_3child_eq_of_childrenBag_eq tab
        c₂ c₃ c₁ c₁ c₂ c₃ ⟨hc₂, hc₃, hc₁⟩
        (BTree.node_childrenBag_eq_rotate_left c₁ c₂ c₃))

/-- [1, bushy-3] tree condition: sum = 1/15. -/
private theorem satisfiesTreeCondition_order_five_1_bushy3 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c₁ c₂ : BTree, t = .node [c₁, c₂] ∧ c₁.order = 1 ∧
      ∃ d₁ d₂ : BTree, c₂ = .node [d₁, d₂] ∧ d₁.order = 1 ∧ d₂.order = 1) :
    tab.satisfiesTreeCondition t ↔
    ∑ i : Fin s, tab.b i *
      ((∑ k : Fin s, tab.A i k) *
       (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2)) = 1 / 15 := by
  simp only [satisfiesTreeCondition, density_of_order_five_1_bushy3 t h]
  constructor
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact (ew_of_order_five_1_bushy3 tab t h i).symm
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact ew_of_order_five_1_bushy3 tab t h i

/-- Transport the canonical `{1, bushy-3}` tree condition across bag-equal
two-child representations. -/
private theorem satisfiesTreeCondition_order_five_bushy3_eq_of_childrenBag_eq
    (tab : ButcherTableau s)
    (c₁ c₂ d₁ d₂ e₁ e₂ : BTree)
    (hcanon : c₁.order = 1 ∧ c₂ = BTree.node [e₁, e₂] ∧ e₁.order = 1 ∧ e₂.order = 1)
    (hbag : (BTree.node [d₁, d₂]).childrenBag = (BTree.node [c₁, c₂]).childrenBag) :
    tab.satisfiesTreeCondition (BTree.node [d₁, d₂]) ↔
    ∑ i : Fin s, tab.b i *
      ((∑ k : Fin s, tab.A i k) *
       (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2)) = 1 / 15 := by
  simp only [satisfiesTreeCondition,
    density_of_order_five_bushy3_eq_of_childrenBag_eq c₁ c₂ d₁ d₂ e₁ e₂ hcanon hbag]
  constructor
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact (ew_of_order_five_bushy3_eq_of_childrenBag_eq tab c₁ c₂ d₁ d₂ e₁ e₂ hcanon hbag i).symm
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact ew_of_order_five_bushy3_eq_of_childrenBag_eq tab c₁ c₂ d₁ d₂ e₁ e₂ hcanon hbag i

/-- [1, chain-3] tree condition: sum = 1/30. -/
private theorem satisfiesTreeCondition_order_five_1_chain3 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c₁ c₂ : BTree, t = .node [c₁, c₂] ∧ c₁.order = 1 ∧
      ∃ d : BTree, c₂ = .node [d] ∧ d.order = 2) :
    tab.satisfiesTreeCondition t ↔
    ∑ i : Fin s, tab.b i *
      ((∑ k : Fin s, tab.A i k) *
       (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l)))) = 1 / 30 := by
  simp only [satisfiesTreeCondition, density_of_order_five_1_chain3 t h]
  constructor
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact (ew_of_order_five_1_chain3 tab t h i).symm
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact ew_of_order_five_1_chain3 tab t h i

/-- Transport the canonical `{1, chain-3}` tree condition across bag-equal
two-child representations. -/
private theorem satisfiesTreeCondition_order_five_chain3_eq_of_childrenBag_eq
    (tab : ButcherTableau s)
    (c₁ c₂ d₁ d₂ d : BTree)
    (hcanon : c₁.order = 1 ∧ c₂ = BTree.node [d] ∧ d.order = 2)
    (hbag : (BTree.node [d₁, d₂]).childrenBag = (BTree.node [c₁, c₂]).childrenBag) :
    tab.satisfiesTreeCondition (BTree.node [d₁, d₂]) ↔
    ∑ i : Fin s, tab.b i *
      ((∑ k : Fin s, tab.A i k) *
       (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l)))) = 1 / 30 := by
  simp only [satisfiesTreeCondition,
    density_of_order_five_chain3_eq_of_childrenBag_eq c₁ c₂ d₁ d₂ d hcanon hbag]
  constructor
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact (ew_of_order_five_chain3_eq_of_childrenBag_eq tab c₁ c₂ d₁ d₂ d hcanon hbag i).symm
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact ew_of_order_five_chain3_eq_of_childrenBag_eq tab c₁ c₂ d₁ d₂ d hcanon hbag i

/-- The `{1, chain-3}` family is canonical up to swapping the two top-level children. -/
private theorem satisfiesTreeCondition_order_five_chain3_canonical (tab : ButcherTableau s)
    (c₁ c₂ d : BTree)
    (hpair : (c₁.order = 1 ∧ c₂.childrenBag = (BTree.node [d]).childrenBag ∧ d.order = 2) ∨
      (c₁.childrenBag = (BTree.node [d]).childrenBag ∧ d.order = 2 ∧ c₂.order = 1)) :
    tab.satisfiesTreeCondition (.node [c₁, c₂]) ↔
    ∑ i : Fin s, tab.b i *
      ((∑ k : Fin s, tab.A i k) *
       (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l)))) = 1 / 30 := by
  rcases hpair with ⟨hc₁, hc₂bag, hd⟩ | ⟨hc₁bag, hd, hc₂⟩
  · cases hc₂node : c₂ with
    | leaf =>
        exfalso
        have hcard : 0 = 1 := by
          simpa [hc₂node] using congrArg Multiset.card hc₂bag
        omega
    | node children =>
        have hchildren : children = [d] := by
          simpa [hc₂node] using BTree.singleton_children_eq_of_childrenBag_eq hc₂bag
        subst children
        simpa using
          (satisfiesTreeCondition_order_five_1_chain3 tab (.node [c₁, BTree.node [d]])
            ⟨c₁, BTree.node [d], rfl, hc₁, d, rfl, hd⟩)
  · cases hc₁node : c₁ with
    | leaf =>
        exfalso
        have hcard : 0 = 1 := by
          simpa [hc₁node] using congrArg Multiset.card hc₁bag
        omega
    | node children =>
        have hchildren : children = [d] := by
          simpa [hc₁node] using BTree.singleton_children_eq_of_childrenBag_eq hc₁bag
        subst children
        simpa using
          satisfiesTreeCondition_order_five_chain3_eq_of_childrenBag_eq tab
            c₂ (BTree.node [d]) (BTree.node [d]) c₂ d ⟨hc₂, rfl, hd⟩
            (BTree.node_childrenBag_eq_swap (BTree.node [d]) c₂)

/-- The `{1, bushy-3}` family is canonical up to swapping the two top-level children. -/
private theorem satisfiesTreeCondition_order_five_bushy3_canonical (tab : ButcherTableau s)
    (c₁ c₂ d₁ d₂ : BTree)
    (hpair : (c₁.order = 1 ∧ c₂.childrenBag = (BTree.node [d₁, d₂]).childrenBag ∧
        d₁.order = 1 ∧ d₂.order = 1) ∨
      (c₁.childrenBag = (BTree.node [d₁, d₂]).childrenBag ∧ d₁.order = 1 ∧
        d₂.order = 1 ∧ c₂.order = 1)) :
    tab.satisfiesTreeCondition (.node [c₁, c₂]) ↔
    ∑ i : Fin s, tab.b i *
      ((∑ k : Fin s, tab.A i k) *
       (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2)) = 1 / 15 := by
  rcases hpair with ⟨hc₁, hc₂bag, hd₁, hd₂⟩ | ⟨hc₁bag, hd₁, hd₂, hc₂⟩
  · cases hc₂node : c₂ with
    | leaf =>
        exfalso
        have hcard : 0 = 2 := by
          simpa [hc₂node] using congrArg Multiset.card hc₂bag
        omega
    | node children =>
        rcases BTree.pair_children_exists_of_childrenBag_eq hc₂bag with ⟨e₁, e₂, hchildren⟩
        have hc₂ : c₂ = .node [e₁, e₂] := by simpa [hc₂node] using congrArg BTree.node hchildren
        have horder : (BTree.node [e₁, e₂]).order = (BTree.node [d₁, d₂]).order := by
          simpa [hc₂] using BTree.order_eq_of_childrenBag_eq hc₂bag
        have hsum : e₁.order + e₂.order = 2 := by
          have horder' : 1 + (e₁.order + e₂.order) = 3 := by
            simpa [BTree.order_node, Nat.add_assoc] using
              horder.trans (by simp [hd₁, hd₂, BTree.order_node])
          omega
        have he₁ : e₁.order = 1 := by
          have he₁_pos := BTree.order_pos e₁
          have he₂_pos := BTree.order_pos e₂
          omega
        have he₂ : e₂.order = 1 := by
          have he₁_pos := BTree.order_pos e₁
          have he₂_pos := BTree.order_pos e₂
          omega
        have hcanon :=
          satisfiesTreeCondition_order_five_1_bushy3 tab (.node [c₁, BTree.node [e₁, e₂]])
            ⟨c₁, BTree.node [e₁, e₂], rfl, hc₁, e₁, e₂, rfl, he₁, he₂⟩
        have hchildren' : children = [e₁, e₂] := by
          simpa [hc₂node] using hchildren
        have hchildnode : BTree.node children = BTree.node [e₁, e₂] := by
          simpa using congrArg BTree.node hchildren'
        simpa [hchildnode] using hcanon
  · cases hc₁node : c₁ with
    | leaf =>
        exfalso
        have hcard : 0 = 2 := by
          simpa [hc₁node] using congrArg Multiset.card hc₁bag
        omega
    | node children =>
        rcases BTree.pair_children_exists_of_childrenBag_eq hc₁bag with ⟨e₁, e₂, hchildren⟩
        have hc₁ : c₁ = .node [e₁, e₂] := by simpa [hc₁node] using congrArg BTree.node hchildren
        have horder : (BTree.node [e₁, e₂]).order = (BTree.node [d₁, d₂]).order := by
          simpa [hc₁] using BTree.order_eq_of_childrenBag_eq hc₁bag
        have hsum : e₁.order + e₂.order = 2 := by
          have horder' : 1 + (e₁.order + e₂.order) = 3 := by
            simpa [BTree.order_node, Nat.add_assoc] using
              horder.trans (by simp [hd₁, hd₂, BTree.order_node])
          omega
        have he₁ : e₁.order = 1 := by
          have he₁_pos := BTree.order_pos e₁
          have he₂_pos := BTree.order_pos e₂
          omega
        have he₂ : e₂.order = 1 := by
          have he₁_pos := BTree.order_pos e₁
          have he₂_pos := BTree.order_pos e₂
          omega
        have hcanon :=
          satisfiesTreeCondition_order_five_bushy3_eq_of_childrenBag_eq tab
            c₂ (BTree.node [e₁, e₂]) (BTree.node [e₁, e₂]) c₂ e₁ e₂ ⟨hc₂, rfl, he₁, he₂⟩
            (BTree.node_childrenBag_eq_swap (BTree.node [e₁, e₂]) c₂)
        have hchildren' : children = [e₁, e₂] := by
          simpa [hc₁node] using hchildren
        have hchildnode : BTree.node children = BTree.node [e₁, e₂] := by
          simpa using congrArg BTree.node hchildren'
        simpa [hchildnode] using hcanon

/-- [order-2, order-2] tree condition: sum = 1/20. -/
private theorem satisfiesTreeCondition_order_five_22 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c₁ c₂ : BTree, t = .node [c₁, c₂] ∧ c₁.order = 2 ∧ c₂.order = 2) :
    tab.satisfiesTreeCondition t ↔
    ∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) ^ 2 = 1 / 20 := by
  simp only [satisfiesTreeCondition, density_of_order_five_22 t h]
  constructor
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact (ew_of_order_five_22 tab t h i).symm
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact ew_of_order_five_22 tab t h i

/-- Via-bushy4 tree condition: sum = 1/20. -/
private theorem satisfiesTreeCondition_order_five_via_bushy4 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧
      ∃ d₁ d₂ d₃ : BTree, c = .node [d₁, d₂, d₃] ∧
        d₁.order = 1 ∧ d₂.order = 1 ∧ d₃.order = 1) :
    tab.satisfiesTreeCondition t ↔
    ∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) ^ 3) = 1 / 20 := by
  simp only [satisfiesTreeCondition, density_of_order_five_via_bushy4 t h]
  constructor
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact (ew_of_order_five_via_bushy4 tab t h i).symm
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact ew_of_order_five_via_bushy4 tab t h i

/-- Via-mixed12 tree condition: sum = 1/40. -/
private theorem satisfiesTreeCondition_order_five_via_mixed12 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧
      ∃ d₁ d₂ : BTree, c = .node [d₁, d₂] ∧ d₁.order = 1 ∧ d₂.order = 2) :
    tab.satisfiesTreeCondition t ↔
    ∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j *
        ((∑ k : Fin s, tab.A j k) * (∑ l : Fin s, tab.A j l * (∑ m : Fin s, tab.A l m)))) = 1 / 40 := by
  have hmixed : ∃ c : BTree, t = .node [c] ∧
      ∃ d₁ d₂ : BTree, c = .node [d₁, d₂] ∧ d₁.order + d₂.order = 3 ∧
        ((d₁.order = 1 ∧ d₂.order = 2) ∨ (d₁.order = 2 ∧ d₂.order = 1)) := by
    rcases h with ⟨c, rfl, d₁, d₂, hc, hd₁, hd₂⟩
    exact ⟨c, rfl, d₁, d₂, hc, by omega, Or.inl ⟨hd₁, hd₂⟩⟩
  simp only [satisfiesTreeCondition, density_of_order_five_via_mixed t hmixed]
  constructor
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact (ew_of_order_five_via_mixed12 tab t h i).symm
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact ew_of_order_five_via_mixed12 tab t h i

/-- Transport the canonical unary mixed `{1,2}` tree condition across bag-equal
presentations of the inner two-child witness. -/
private theorem satisfiesTreeCondition_order_five_via_mixed_eq_of_childrenBag_eq
    (tab : ButcherTableau s)
    (c₁ c₂ d₁ d₂ : BTree)
    (hcanon : c₁.order = 1 ∧ c₂.order = 2)
    (hbag : (BTree.node [d₁, d₂]).childrenBag = (BTree.node [c₁, c₂]).childrenBag) :
    tab.satisfiesTreeCondition (.node [.node [d₁, d₂]]) ↔
    ∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j *
        ((∑ k : Fin s, tab.A j k) * (∑ l : Fin s, tab.A j l * (∑ m : Fin s, tab.A l m)))) = 1 / 40 := by
  exact
    (satisfiesTreeCondition_singleton_eq_of_childrenBag_eq tab
      (children₁ := [d₁, d₂]) (children₂ := [c₁, c₂]) hbag).trans <|
      satisfiesTreeCondition_order_five_via_mixed12 tab (.node [.node [c₁, c₂]])
        ⟨.node [c₁, c₂], rfl, c₁, c₂, rfl, hcanon.1, hcanon.2⟩

/-- Mixed order-5 singleton nodes are canonical up to swapping the ordered child witnesses. -/
private theorem satisfiesTreeCondition_order_five_via_mixed_canonical (tab : ButcherTableau s)
    (c d₁ d₂ : BTree) (hcBag : c.childrenBag = (BTree.node [d₁, d₂]).childrenBag)
    (hpair : (d₁.order = 1 ∧ d₂.order = 2) ∨ (d₁.order = 2 ∧ d₂.order = 1)) :
    tab.satisfiesTreeCondition (.node [c]) ↔
    ∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j *
        ((∑ k : Fin s, tab.A j k) * (∑ l : Fin s, tab.A j l * (∑ m : Fin s, tab.A l m)))) = 1 / 40 := by
  cases c with
  | leaf =>
      have hfalse : False := by
        have hcard := congrArg Multiset.card hcBag
        simpa using hcard
      exact hfalse.elim
  | node children =>
      rcases BTree.pair_children_exists_of_childrenBag_eq hcBag with ⟨e₁, e₂, hchildren⟩
      have hbase :
          (BTree.node [e₁, e₂]).childrenBag = (BTree.node [d₁, d₂]).childrenBag := by
        simpa [hchildren] using hcBag
      rcases hpair with ⟨hd₁, hd₂⟩ | ⟨hd₁, hd₂⟩
      · simpa [hchildren] using
          satisfiesTreeCondition_order_five_via_mixed_eq_of_childrenBag_eq tab
            d₁ d₂ e₁ e₂ ⟨hd₁, hd₂⟩ hbase
      · simpa [hchildren] using
          satisfiesTreeCondition_order_five_via_mixed_eq_of_childrenBag_eq tab
            d₂ d₁ e₁ e₂ ⟨hd₂, hd₁⟩
            (hbase.trans (BTree.node_childrenBag_eq_swap d₁ d₂))

/-- Via-via-bushy3 tree condition: sum = 1/60. -/
private theorem satisfiesTreeCondition_order_five_via_via_bushy3_eq_of_childrenBag_eq
    (tab : ButcherTableau s)
    (c₁ c₂ d₁ d₂ : BTree)
    (hcanon : c₁.order = 1 ∧ c₂.order = 1)
    (hbag : (BTree.node [d₁, d₂]).childrenBag = (BTree.node [c₁, c₂]).childrenBag) :
    tab.satisfiesTreeCondition (.node [.node [.node [d₁, d₂]]]) ↔
    ∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j *
        (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l) ^ 2)) = 1 / 60 := by
  simp only [satisfiesTreeCondition,
    density_of_order_five_via_via_bushy3_eq_of_childrenBag_eq c₁ c₂ d₁ d₂ hcanon hbag]
  constructor
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact (ew_of_order_five_via_via_bushy3_eq_of_childrenBag_eq tab c₁ c₂ d₁ d₂ hcanon hbag i).symm
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact ew_of_order_five_via_via_bushy3_eq_of_childrenBag_eq tab c₁ c₂ d₁ d₂ hcanon hbag i

/-- Via-via-bushy3 tree condition: sum = 1/60. -/
private theorem satisfiesTreeCondition_order_five_via_via_bushy3 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧
      ∃ d : BTree, c = .node [d] ∧
        ∃ e₁ e₂ : BTree, d = .node [e₁, e₂] ∧ e₁.order = 1 ∧ e₂.order = 1) :
    tab.satisfiesTreeCondition t ↔
    ∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j *
        (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l) ^ 2)) = 1 / 60 := by
  rcases h with ⟨c, rfl, d, hc, e₁, e₂, hd, he₁, he₂⟩
  subst hc
  subst hd
  simpa using
    satisfiesTreeCondition_order_five_via_via_bushy3_eq_of_childrenBag_eq tab
      e₁ e₂ e₁ e₂ ⟨he₁, he₂⟩ rfl

/-- Nested unary bushy-3 singleton nodes are canonical up to swapping the
ordered inner child witnesses. -/
private theorem satisfiesTreeCondition_order_five_via_via_bushy3_canonical
    (tab : ButcherTableau s) (c d e₁ e₂ : BTree)
    (hcBag : c.childrenBag = (BTree.node [d]).childrenBag)
    (hdBag : d.childrenBag = (BTree.node [e₁, e₂]).childrenBag)
    (he₁ : e₁.order = 1) (he₂ : e₂.order = 1) :
    tab.satisfiesTreeCondition (.node [c]) ↔
    ∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j *
        (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l) ^ 2)) = 1 / 60 := by
  cases c with
  | leaf =>
      simp at hcBag
  | node children =>
      have hchildren : children = [d] := BTree.singleton_children_eq_of_childrenBag_eq hcBag
      rcases BTree.pair_node_recover_of_childrenBag_eq hdBag with ⟨f₁, f₂, hfBag, hd⟩
      have hcanonBag : (BTree.node [f₁, f₂]).childrenBag = (BTree.node [e₁, e₂]).childrenBag := by
        simpa [hd] using hdBag
      simpa [hchildren, hd] using
        satisfiesTreeCondition_order_five_via_via_bushy3_eq_of_childrenBag_eq tab
          e₁ e₂ f₁ f₂ ⟨he₁, he₂⟩ hcanonBag

/-- Via-via-chain3 tree condition: sum = 1/120. -/
private theorem satisfiesTreeCondition_order_five_via_via_chain3_eq_of_childrenBag_eq
    (tab : ButcherTableau s)
    (c d : BTree)
    (hcanon : c.order = 2)
    (hbag : (BTree.node [d]).childrenBag = (BTree.node [c]).childrenBag) :
    tab.satisfiesTreeCondition (.node [.node [.node [d]]]) ↔
    ∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j *
        (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l * (∑ m : Fin s, tab.A l m)))) = 1 / 120 := by
  simp only [satisfiesTreeCondition,
    density_of_order_five_via_via_chain3_eq_of_childrenBag_eq c d hcanon hbag]
  constructor
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact (ew_of_order_five_via_via_chain3_eq_of_childrenBag_eq tab c d hcanon hbag i).symm
  · intro hh; convert hh using 1; congr 1; ext i; congr 1
    exact ew_of_order_five_via_via_chain3_eq_of_childrenBag_eq tab c d hcanon hbag i

/-- Via-via-chain3 tree condition: sum = 1/120. -/
private theorem satisfiesTreeCondition_order_five_via_via_chain3 (tab : ButcherTableau s) (t : BTree)
    (h : ∃ c : BTree, t = .node [c] ∧
      ∃ d : BTree, c = .node [d] ∧ ∃ e : BTree, d = .node [e] ∧ e.order = 2) :
    tab.satisfiesTreeCondition t ↔
    ∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j *
        (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l * (∑ m : Fin s, tab.A l m)))) = 1 / 120 := by
  rcases h with ⟨c, rfl, d, hc, e, hd, he⟩
  subst hc
  subst hd
  simpa using
    satisfiesTreeCondition_order_five_via_via_chain3_eq_of_childrenBag_eq tab
      e e he rfl

/-- Nested unary chain-3 singleton nodes are canonical at the unique
order-2 inner child. -/
private theorem satisfiesTreeCondition_order_five_via_via_chain3_canonical
    (tab : ButcherTableau s) (c d e : BTree)
    (hcBag : c.childrenBag = (BTree.node [d]).childrenBag)
    (hdBag : d.childrenBag = (BTree.node [e]).childrenBag)
    (he : e.order = 2) :
    tab.satisfiesTreeCondition (.node [c]) ↔
    ∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j *
        (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l * (∑ m : Fin s, tab.A l m)))) = 1 / 120 := by
  cases c with
  | leaf =>
      simp at hcBag
  | node children =>
      have hchildren : children = [d] := BTree.singleton_children_eq_of_childrenBag_eq hcBag
      rcases BTree.singleton_node_recover_of_childrenBag_eq hdBag with ⟨f, hfBag, hd⟩
      have hcanonBag : (BTree.node [f]).childrenBag = (BTree.node [e]).childrenBag := by
        simpa [hd] using hdBag
      have hfeq : f = e := by
        have hsingle : [f] = [e] := BTree.singleton_children_eq_of_childrenBag_eq hcanonBag
        simpa using hsingle
      have hf : f.order = 2 := by simpa [hfeq] using he
      simpa [hchildren, hd] using
        satisfiesTreeCondition_order_five_via_via_chain3_eq_of_childrenBag_eq tab
          e f he hcanonBag

/-! #### Sum conversion helpers for order 5 -/

/-- Convert bushy-5 sum: (∑ aᵢₖ)⁴ → cᵢ⁴. -/
private theorem order5a_sum_eq (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    (∑ i : Fin s, tab.b i * (∑ k : Fin s, tab.A i k) ^ 4) =
      ∑ i : Fin s, tab.b i * tab.c i ^ 4 := by
  congr 1; ext i; congr 1; rw [hrc i]

/-- Convert 3-child sum: (∑ aᵢₖ)²·(∑ⱼ aᵢⱼ(∑ₖ aⱼₖ)) → cᵢ²·(∑ aᵢⱼ cⱼ). -/
private theorem order5b_sum_eq (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    (∑ i : Fin s, tab.b i *
      ((∑ k : Fin s, tab.A i k) ^ 2 *
       (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)))) =
      ∑ i : Fin s, tab.b i * tab.c i ^ 2 * (∑ j : Fin s, tab.A i j * tab.c j) := by
  have hrc' : ∀ i : Fin s, (∑ k : Fin s, tab.A i k) = tab.c i := fun i => (hrc i).symm
  congr 1; ext i; simp_rw [hrc']; ring

/-- Branch-specific order condition selected by an order-5 three-child Case B
witness. -/
private def order_five_caseB_target (tab : ButcherTableau s)
    {c₁ c₂ c₃ : BTree} (_ : BTree.OrderFiveCaseBWitness c₁ c₂ c₃) : Prop :=
  tab.order5b

/-- Shared forward/reverse dispatcher for the order-5 three-child / Case B
witness family. -/
private theorem order_five_caseB_dispatch_shared (tab : ButcherTableau s)
    (hrc : tab.IsRowSumConsistent) {c₁ c₂ c₃ : BTree}
    (hwit : BTree.OrderFiveCaseBWitness c₁ c₂ c₃) :
    (tab.satisfiesTreeCondition (.node [c₁, c₂, c₃]) → order_five_caseB_target tab hwit) ∧
    (order_five_caseB_target tab hwit → tab.satisfiesTreeCondition (.node [c₁, c₂, c₃])) := by
  cases hwit with
  | ord112 hc₁ hc₂ hc₃ =>
      rw [satisfiesTreeCondition_order_five_3child_canonical tab c₁ c₂ c₃
        (Or.inl ⟨hc₁, hc₂, hc₃⟩)]
      constructor <;> intro h <;>
        simpa [order_five_caseB_target, order5b, order5b_sum_eq tab hrc] using h
  | ord121 hc₁ hc₂ hc₃ =>
      rw [satisfiesTreeCondition_order_five_3child_canonical tab c₁ c₂ c₃
        (Or.inr <| Or.inl ⟨hc₁, hc₂, hc₃⟩)]
      constructor <;> intro h <;>
        simpa [order_five_caseB_target, order5b, order5b_sum_eq tab hrc] using h
  | ord211 hc₁ hc₂ hc₃ =>
      rw [satisfiesTreeCondition_order_five_3child_canonical tab c₁ c₂ c₃
        (Or.inr <| Or.inr ⟨hc₁, hc₂, hc₃⟩)]
      constructor <;> intro h <;>
        simpa [order_five_caseB_target, order5b, order5b_sum_eq tab hrc] using h

/-- Convert [2,2] sum: (∑ⱼ aᵢⱼ(∑ₖ aⱼₖ))² → (∑ aᵢⱼ cⱼ)². -/
private theorem order5c_sum_eq (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    (∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) ^ 2) =
      ∑ i : Fin s, tab.b i * (∑ j : Fin s, tab.A i j * tab.c j) ^ 2 := by
  have hrc' : ∀ i : Fin s, (∑ k : Fin s, tab.A i k) = tab.c i := fun i => (hrc i).symm
  congr 1; ext i; simp_rw [hrc']

/-- Convert [1, bushy-3] sum: cᵢ·(∑ aᵢⱼ(∑ aⱼₖ)²) → cᵢ·(∑ aᵢⱼ cⱼ²). -/
private theorem order5d_sum_eq (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    (∑ i : Fin s, tab.b i *
      ((∑ k : Fin s, tab.A i k) *
       (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2))) =
      ∑ i : Fin s, tab.b i * tab.c i * (∑ j : Fin s, tab.A i j * tab.c j ^ 2) := by
  have hrc' : ∀ i : Fin s, (∑ k : Fin s, tab.A i k) = tab.c i := fun i => (hrc i).symm
  congr 1; ext i; simp_rw [hrc']; ring

/-- Convert via-bushy4 sum: ∑ bᵢ(∑ aᵢⱼ(∑ aⱼₖ)³) → ∑∑ bᵢ aᵢⱼ cⱼ³. -/
private theorem order5e_sum_eq (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    (∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) ^ 3)) =
      ∑ i : Fin s, ∑ j : Fin s, tab.b i * tab.A i j * tab.c j ^ 3 := by
  have hrc' : ∀ i : Fin s, (∑ k : Fin s, tab.A i k) = tab.c i := fun i => (hrc i).symm
  simp_rw [Finset.mul_sum]
  congr 1; ext i; congr 1; ext j; rw [hrc']; ring

/-- Convert [1, chain-3] sum: cᵢ·(∑ aᵢⱼ(∑ aⱼₖ(∑ aₖₗ))) → cᵢ·(∑ aᵢⱼ(∑ aⱼₖ cₖ)). -/
private theorem order5f_sum_eq (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    (∑ i : Fin s, tab.b i *
      ((∑ k : Fin s, tab.A i k) *
       (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l))))) =
      ∑ i : Fin s, tab.b i * tab.c i *
        (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k * tab.c k)) := by
  have hrc' : ∀ i : Fin s, (∑ k : Fin s, tab.A i k) = tab.c i := fun i => (hrc i).symm
  congr 1; ext i; simp_rw [hrc']; ring

/-- Convert via-mixed sum: ∑ bᵢ(∑ aᵢⱼ(cⱼ·(∑ aⱼₗ(∑ aₗₘ)))) → ∑∑ bᵢ aᵢⱼ cⱼ (∑ aⱼₖ cₖ). -/
private theorem order5g_sum_eq (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    (∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j *
        ((∑ k : Fin s, tab.A j k) * (∑ l : Fin s, tab.A j l * (∑ m : Fin s, tab.A l m))))) =
      ∑ i : Fin s, ∑ j : Fin s,
        tab.b i * tab.A i j * tab.c j * (∑ k : Fin s, tab.A j k * tab.c k) := by
  have hrc' : ∀ i : Fin s, (∑ k : Fin s, tab.A i k) = tab.c i := fun i => (hrc i).symm
  congr 1; ext i; simp_rw [hrc', Finset.mul_sum]; congr 1; ext j; ring

/-- Convert via-via-bushy3 sum: ∑ bᵢ(∑ aᵢⱼ(∑ aⱼₖ(∑ aₖₗ)²)) → ∑∑ bᵢ aᵢⱼ (∑ aⱼₖ cₖ²). -/
private theorem order5h_sum_eq (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    (∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j *
        (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l) ^ 2))) =
      ∑ i : Fin s, ∑ j : Fin s,
        tab.b i * tab.A i j * (∑ k : Fin s, tab.A j k * tab.c k ^ 2) := by
  have hrc' : ∀ i : Fin s, (∑ k : Fin s, tab.A i k) = tab.c i := fun i => (hrc i).symm
  simp_rw [Finset.mul_sum]
  congr 1; ext i; congr 1; ext j; simp_rw [hrc']; ring

/-- Convert via-via-chain3 sum: ∑ bᵢ(∑ aᵢⱼ(∑ aⱼₖ(∑ aₖₗ(∑ aₗₘ)))) → ∑∑∑ bᵢ aᵢⱼ aⱼₖ (∑ aₖₗ cₗ). -/
private theorem order5i_sum_eq (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    (∑ i : Fin s, tab.b i *
      (∑ j : Fin s, tab.A i j *
        (∑ k : Fin s, tab.A j k * (∑ l : Fin s, tab.A k l * (∑ m : Fin s, tab.A l m))))) =
      ∑ i : Fin s, ∑ j : Fin s, ∑ k : Fin s,
        tab.b i * tab.A i j * tab.A j k * (∑ l : Fin s, tab.A k l * tab.c l) := by
  have hrc' : ∀ i : Fin s, (∑ k : Fin s, tab.A i k) = tab.c i := fun i => (hrc i).symm
  congr 1; ext i; simp_rw [hrc', Finset.mul_sum]; congr 1; ext j; congr 1; ext k; ring

/-- Branch-specific order condition selected by an order-5 two-child Case C witness. -/
private def order_five_caseC_target (tab : ButcherTableau s) :
    {c₁ c₂ : BTree} → BTree.OrderFiveCaseCWitness c₁ c₂ → Prop
  | _, _, .ord22 _ _ => tab.order5c
  | _, _, .chain3 _ _ => tab.order5f
  | _, _, .bushy3 _ _ _ => tab.order5d

/-- Shared forward/reverse dispatcher for the order-5 two-child / Case C witness families. -/
private theorem order_five_caseC_dispatch_shared (tab : ButcherTableau s)
    (hrc : tab.IsRowSumConsistent) {c₁ c₂ : BTree}
    (hwit : BTree.OrderFiveCaseCWitness c₁ c₂) :
    (tab.satisfiesTreeCondition (.node [c₁, c₂]) → order_five_caseC_target tab hwit) ∧
    (order_five_caseC_target tab hwit → tab.satisfiesTreeCondition (.node [c₁, c₂])) := by
  cases hwit with
  | ord22 hc₁ hc₂ =>
      rw [satisfiesTreeCondition_order_five_22 tab (.node [c₁, c₂]) ⟨c₁, c₂, rfl, hc₁, hc₂⟩]
      constructor <;> intro h <;>
        simpa [order_five_caseC_target, order5c, order5c_sum_eq tab hrc] using h
  | chain3 d hpair =>
      rw [satisfiesTreeCondition_order_five_chain3_canonical tab c₁ c₂ d hpair]
      constructor <;> intro h <;>
        simpa [order_five_caseC_target, order5f, order5f_sum_eq tab hrc] using h
  | bushy3 d₁ d₂ hpair =>
      rw [satisfiesTreeCondition_order_five_bushy3_canonical tab c₁ c₂ d₁ d₂ hpair]
      constructor <;> intro h <;>
        simpa [order_five_caseC_target, order5d, order5d_sum_eq tab hrc] using h

/-- Canonical dispatcher for the order-5 two-child family with child-order sum `4`. -/
private theorem satisfiesTreeCondition_order_five_caseC (tab : ButcherTableau s)
    (hrc : tab.IsRowSumConsistent) (c₁ c₂ : BTree)
    (hwit : BTree.OrderFiveCaseCWitness c₁ c₂)
    (h5c :
      ∑ i : Fin s, tab.b i * (∑ j : Fin s, tab.A i j * tab.c j) ^ 2 = 1 / 20)
    (h5d :
      ∑ i : Fin s, tab.b i * tab.c i * (∑ j : Fin s, tab.A i j * tab.c j ^ 2) = 1 / 15)
    (h5f :
      ∑ i : Fin s, tab.b i * tab.c i *
        (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k * tab.c k)) = 1 / 30) :
    tab.satisfiesTreeCondition (.node [c₁, c₂]) := by
  have htarget : order_five_caseC_target tab hwit := by
    cases hwit with
    | ord22 =>
        simpa [order_five_caseC_target, order5c] using h5c
    | chain3 =>
        simpa [order_five_caseC_target, order5f] using h5f
    | bushy3 =>
        simpa [order_five_caseC_target, order5d] using h5d
  exact (order_five_caseC_dispatch_shared tab hrc hwit).2 htarget

/-- Canonical wrapper for the nested-unary via-chain3 singleton-child Case D
branch, packaged directly as `order5i`. -/
private theorem satisfiesTreeCondition_order_five_caseD_viaChain3_canonical
    (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) (c d e : BTree)
    (hcBag : c.childrenBag = (BTree.node [d]).childrenBag)
    (hdBag : d.childrenBag = (BTree.node [e]).childrenBag)
    (he : e.order = 2) :
    tab.satisfiesTreeCondition (.node [c]) ↔ tab.order5i := by
  rw [satisfiesTreeCondition_order_five_via_via_chain3_canonical tab c d e hcBag hdBag he]
  constructor <;> intro h <;> simpa [order5i, order5i_sum_eq tab hrc] using h

/-- Canonical wrapper for the nested-unary via-bushy3 singleton-child Case D
branch, packaged directly as `order5h`. -/
private theorem satisfiesTreeCondition_order_five_caseD_viaBushy3_canonical
    (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) (c d e₁ e₂ : BTree)
    (hcBag : c.childrenBag = (BTree.node [d]).childrenBag)
    (hdBag : d.childrenBag = (BTree.node [e₁, e₂]).childrenBag)
    (he₁ : e₁.order = 1) (he₂ : e₂.order = 1) :
    tab.satisfiesTreeCondition (.node [c]) ↔ tab.order5h := by
  rw [satisfiesTreeCondition_order_five_via_via_bushy3_canonical tab c d e₁ e₂ hcBag hdBag he₁ he₂]
  constructor <;> intro h <;> simpa [order5h, order5h_sum_eq tab hrc] using h

/-- Branch-specific order condition selected by an order-4 singleton-child witness. -/
private def order_five_caseD_target (tab : ButcherTableau s) {c : BTree}
    (hwit : BTree.OrderFiveCaseDWitness c) : Prop :=
  match hwit with
  | .bushy4 .. => tab.order5e
  | .mixed4 .. => tab.order5g
  | .viaChain3 .. => tab.order5i
  | .viaBushy3 .. => tab.order5h

/-- Shared forward/reverse dispatcher for the order-5 singleton-child / Case D witness families. -/
private theorem order_five_caseD_dispatch_shared (tab : ButcherTableau s)
    (hrc : tab.IsRowSumConsistent) {c : BTree} (hwit : BTree.OrderFiveCaseDWitness c) :
    (tab.satisfiesTreeCondition (.node [c]) → order_five_caseD_target tab hwit) ∧
    (order_five_caseD_target tab hwit → tab.satisfiesTreeCondition (.node [c])) := by
  cases c with
  | leaf =>
      cases hwit with
      | bushy4 _ _ _ hcBag _ _ _ =>
          have hcard := congrArg Multiset.card hcBag
          simp at hcard
      | mixed4 _ _ hcBag _ =>
          have hcard := congrArg Multiset.card hcBag
          simp at hcard
      | viaChain3 _ _ hcBag _ _ =>
          have hcard := congrArg Multiset.card hcBag
          simp at hcard
      | viaBushy3 _ _ _ hcBag _ _ _ =>
          have hcard := congrArg Multiset.card hcBag
          simp at hcard
  | node children =>
      cases hwit with
      | bushy4 d₁ d₂ d₃ hcBag hd₁ hd₂ hd₃ =>
          rcases BTree.triple_children_exists_of_childrenBag_eq hcBag with ⟨e₁, e₂, e₃, hchildren⟩
          have horder : (BTree.node children).order = 4 := by
            refine (BTree.order_eq_of_childrenBag_eq hcBag).trans ?_
            simp [hd₁, hd₂, hd₃, BTree.order_node]
          have hsume : 1 + (e₁.order + (e₂.order + e₃.order)) = 4 := by
            simpa [hchildren, BTree.order_node, Nat.add_assoc] using horder
          have he₁_pos := BTree.order_pos e₁
          have he₂_pos := BTree.order_pos e₂
          have he₃_pos := BTree.order_pos e₃
          have he₁ : e₁.order = 1 := by omega
          have he₂ : e₂.order = 1 := by omega
          have he₃ : e₃.order = 1 := by omega
          rw [satisfiesTreeCondition_order_five_via_bushy4 tab (.node [BTree.node children])
            ⟨BTree.node children, rfl, e₁, e₂, e₃, by simp [hchildren], he₁, he₂, he₃⟩]
          constructor <;> intro h <;>
            simpa [order_five_caseD_target, order5e, order5e_sum_eq tab hrc] using h
      | mixed4 d₁ d₂ hcBag hpair =>
          have hcBag' : (BTree.node children).childrenBag = (BTree.node [d₁, d₂]).childrenBag := by
            simp [hcBag]
          rw [satisfiesTreeCondition_order_five_via_mixed_canonical tab (.node children) d₁ d₂
            hcBag' hpair]
          constructor <;> intro h <;>
            simpa [order_five_caseD_target, order5g, order5g_sum_eq tab hrc] using h
      | viaChain3 d e hcBag hdBag he =>
          have hcBag' : (BTree.node children).childrenBag = (BTree.node [d]).childrenBag := by
            simp [hcBag]
          have hdBag' : d.childrenBag = (BTree.node [e]).childrenBag := by
            simp [hdBag]
          have h := satisfiesTreeCondition_order_five_caseD_viaChain3_canonical tab hrc
            (.node children) d e hcBag' hdBag' he
          exact ⟨fun ht => by simpa [order_five_caseD_target] using h.mp ht,
            fun htarget => h.mpr (by simpa [order_five_caseD_target] using htarget)⟩
      | viaBushy3 d e₁ e₂ hcBag hdBag he₁ he₂ =>
          have hcBag' : (BTree.node children).childrenBag = (BTree.node [d]).childrenBag := by
            simp [hcBag]
          have hdBag' : d.childrenBag = (BTree.node [e₁, e₂]).childrenBag := by
            simp [hdBag]
          have h := satisfiesTreeCondition_order_five_caseD_viaBushy3_canonical tab hrc
            (.node children) d e₁ e₂ hcBag' hdBag' he₁ he₂
          exact ⟨fun ht => by simpa [order_five_caseD_target] using h.mp ht,
            fun htarget => h.mpr (by simpa [order_five_caseD_target] using htarget)⟩

/-- Theorem 301A at order 5 (assuming row-sum consistency). -/
theorem thm_301A_order5 (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    tab.hasTreeOrder 5 ↔ tab.HasOrderGe5 := by
  constructor
  · -- Forward: hasTreeOrder 5 → HasOrderGe5
    intro h
    have h4 : tab.HasOrderGe4 := (thm_301A_order4 tab hrc).mp (fun t ht => h t (by omega))
    refine ⟨h4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- order5a from t5a = [leaf⁴]
      have ht := h t5a (by native_decide)
      rw [satisfiesTreeCondition_order_five_bushy5 tab t5a
        ⟨.leaf, .leaf, .leaf, .leaf, rfl, by simp, by simp, by simp, by simp⟩] at ht
      rw [order5a]; simpa [order5a_sum_eq tab hrc] using ht
    · -- order5b from t5b = [leaf, leaf, t2]
      have ht := h t5b (by native_decide)
      have hCaseB : BTree.OrderFiveCaseBWitness .leaf .leaf t2 :=
        .ord112 (by simp) (by simp) (by native_decide)
      have htarget :=
        (order_five_caseB_dispatch_shared tab hrc
          (c₁ := .leaf) (c₂ := .leaf) (c₃ := t2) hCaseB).1
          (by simpa [t5b] using ht)
      simpa [order_five_caseB_target] using htarget
    · -- order5c from t5e = [t2, t2]
      have ht := h t5e (by native_decide)
      have htarget :=
        (order_five_caseC_dispatch_shared tab hrc
          (c₁ := t2) (c₂ := t2) (.ord22 (by native_decide) (by native_decide))).1
          (by simpa [t5e] using ht)
      simpa [order_five_caseC_target] using htarget
    · -- order5d from t5c = [leaf, t3a]
      have ht := h t5c (by native_decide)
      have htarget :=
        (order_five_caseC_dispatch_shared tab hrc
          (c₁ := .leaf) (c₂ := t3a)
          (.bushy3 .leaf .leaf (Or.inl ⟨by simp, rfl, by simp, by simp⟩))).1
          (by simpa [t5c] using ht)
      simpa [order_five_caseC_target] using htarget
    · -- order5e from t5f = [t4a] where t4a = [leaf, leaf, leaf]
      have ht := h t5f (by native_decide)
      have htarget :=
        (order_five_caseD_dispatch_shared tab hrc (c := t4a)
          (.bushy4 .leaf .leaf .leaf rfl (by simp) (by simp) (by simp))).1 (by simpa using ht)
      simpa [order_five_caseD_target] using htarget
    · -- order5f from t5d = [leaf, t3b]
      have ht := h t5d (by native_decide)
      have htarget :=
        (order_five_caseC_dispatch_shared tab hrc
          (c₁ := .leaf) (c₂ := t3b)
          (.chain3 t2 (Or.inl ⟨by simp, rfl, by native_decide⟩))).1
          (by simpa [t5d] using ht)
      simpa [order_five_caseC_target] using htarget
    · -- order5g from t5g = [t4b] where t4b = [leaf, t2]
      have ht := h t5g (by native_decide)
      have htarget :=
        (order_five_caseD_dispatch_shared tab hrc (c := t4b)
          (.mixed4 .leaf t2 rfl (Or.inl ⟨by simp, by native_decide⟩))).1 (by simpa using ht)
      simpa [order_five_caseD_target] using htarget
    · -- order5h from t5h = [t4c] where t4c = [t3a] = [[leaf, leaf]]
      have ht := h t5h (by native_decide)
      have htarget :=
        (order_five_caseD_dispatch_shared tab hrc (c := t4c)
          (.viaBushy3 t3a .leaf .leaf rfl rfl (by simp) (by simp))).1 (by simpa using ht)
      simpa [order_five_caseD_target] using htarget
    · -- order5i from t5i = [t4d] where t4d = [t3b] = [[t2]]
      have ht := h t5i (by native_decide)
      have htarget :=
        (order_five_caseD_dispatch_shared tab hrc (c := t4d)
          (.viaChain3 t3b t2 rfl rfl (by native_decide))).1 (by simpa using ht)
      simpa [order_five_caseD_target] using htarget
  · -- Reverse: HasOrderGe5 → hasTreeOrder 5
    rintro ⟨h4, h5a, h5b, h5c, h5d, h5e, h5f, h5g, h5h, h5i⟩ t ht
    have hpos := BTree.order_pos t
    by_cases hle4 : t.order ≤ 4
    · exact ((thm_301A_order4 tab hrc).mpr h4) t hle4
    · have heq : t.order = 5 := by omega
      have hw5 : BTree.OrderFiveBagWitness t := BTree.order_five_bag_witness t heq
      cases hw5 with
      | bushy5 children c₁ c₂ c₃ c₄ hc₁ hc₂ hc₃ hc₄ hbag =>
        -- Case A: 4 leaves → order5a
        have hcanonical : tab.satisfiesTreeCondition (BTree.node [c₁, c₂, c₃, c₄]) := by
          rw [satisfiesTreeCondition_order_five_bushy5 tab (BTree.node [c₁, c₂, c₃, c₄])
            ⟨c₁, c₂, c₃, c₄, rfl, hc₁, hc₂, hc₃, hc₄⟩]
          rw [order5a] at h5a
          simpa [order5a_sum_eq tab hrc] using h5a
        exact (satisfiesTreeCondition_eq_of_childrenBag_eq tab hbag).2 hcanonical
      | caseB children c₁ c₂ c₃ hsum hbag =>
        -- Case B: 3 children summing to 4
        have hCaseB : BTree.OrderFiveCaseBWitness c₁ c₂ c₃ :=
          BTree.order_five_caseB_witness c₁ c₂ c₃ hsum
        have htarget : order_five_caseB_target tab hCaseB := by
          simpa [order_five_caseB_target] using h5b
        have hcanonical : tab.satisfiesTreeCondition (.node [c₁, c₂, c₃]) :=
          (order_five_caseB_dispatch_shared tab hrc hCaseB).2 htarget
        exact (satisfiesTreeCondition_eq_of_childrenBag_eq tab hbag).2 hcanonical
      | caseC children c₁ c₂ hsum hbag =>
        -- Case C: 2 children summing to 4
        have hCaseC : BTree.OrderFiveCaseCWitness c₁ c₂ :=
          BTree.order_five_caseC_witness c₁ c₂ hsum
        have htarget : order_five_caseC_target tab hCaseC := by
          cases hCaseC with
          | ord22 =>
              simpa [order_five_caseC_target] using h5c
          | bushy3 =>
              simpa [order_five_caseC_target] using h5d
          | chain3 =>
              simpa [order_five_caseC_target] using h5f
        have hcanonical : tab.satisfiesTreeCondition (.node [c₁, c₂]) :=
          (order_five_caseC_dispatch_shared tab hrc hCaseC).2 htarget
        exact (satisfiesTreeCondition_eq_of_childrenBag_eq tab hbag).2 hcanonical
      | caseD children c hw4 hbag =>
        -- Case D: single order-4 child
        have hCaseD : BTree.OrderFiveCaseDWitness c :=
          BTree.order_five_caseD_witness c (BTree.order_fourBagWitness_order_eq hw4)
        have htarget : order_five_caseD_target tab hCaseD := by
          cases hCaseD with
          | bushy4 =>
              simpa [order_five_caseD_target] using h5e
          | mixed4 =>
              simpa [order_five_caseD_target] using h5g
          | viaBushy3 =>
              simpa [order_five_caseD_target] using h5h
          | viaChain3 =>
              simpa [order_five_caseD_target] using h5i
        have hcanonical : tab.satisfiesTreeCondition (.node [c]) :=
          (order_five_caseD_dispatch_shared tab hrc hCaseD).2 htarget
        exact (satisfiesTreeCondition_eq_of_childrenBag_eq tab hbag).2 hcanonical

end ButcherTableau
