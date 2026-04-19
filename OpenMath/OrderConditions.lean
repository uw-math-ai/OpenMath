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

/-- Any order-3 tree is either a chain `[[τ]]` or a bushy tree `[τ²]`. -/
private theorem order_three_cases (t : BTree) (ht : t.order = 3) :
    (∃ c : BTree, t = .node [c] ∧ c.order = 2) ∨
    (∃ c₁ c₂ : BTree, t = .node [c₁, c₂] ∧ c₁.order = 1 ∧ c₂.order = 1) := by
  cases t with
  | leaf => simp at ht
  | node children =>
    simp only [order_node] at ht
    have hfoldr : children.foldr (fun c n => c.order + n) 0 = 2 := by omega
    cases children with
    | nil => simp at hfoldr
    | cons hd tl =>
      simp only [List.foldr] at hfoldr
      have hhd_pos := BTree.order_pos hd
      cases tl with
      | nil =>
        left
        refine ⟨hd, rfl, by simpa using hfoldr⟩
      | cons hd2 tl2 =>
        have hhd2_pos := BTree.order_pos hd2
        have hhd : hd.order = 1 := by
          simp only [List.foldr] at hfoldr
          omega
        have hrest : hd2.order + tl2.foldr (fun c n => c.order + n) 0 = 1 := by
          simp only [List.foldr] at hfoldr
          omega
        cases tl2 with
        | nil =>
          right
          refine ⟨hd, hd2, rfl, hhd, by simpa using hrest⟩
        | cons hd3 tl3 =>
          simp only [List.foldr] at hrest
          have hhd3_pos := BTree.order_pos hd3
          omega

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
        rcases order_three_cases t heq with hchain | hbushy
        · rw [satisfiesTreeCondition_order_three_chain tab t hchain]
          rw [order3b] at h3b
          simpa [order3b_sum_eq tab hrc] using h3b
        · rw [satisfiesTreeCondition_order_three_bushy tab t hbushy]
          rw [order3a] at h3a
          simpa [order3a_sum_eq tab hrc] using h3a

/-- Theorem 301A at order 4 (assuming row-sum consistency). -/
theorem thm_301A_order4 (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    tab.hasTreeOrder 4 ↔ tab.HasOrderGe4 := by
  sorry

/-- Theorem 301A at order 5 (assuming row-sum consistency). -/
theorem thm_301A_order5 (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent) :
    tab.hasTreeOrder 5 ↔ tab.HasOrderGe5 := by
  sorry

end ButcherTableau
