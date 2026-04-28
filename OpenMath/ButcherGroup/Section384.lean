import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core

/-!
# Butcher §384 right-block convolution

Extracted from `OpenMath/ButcherGroup.lean` in cycle 535 because the
parent file crossed the 3000-line cap. This module collects the §384
right-block convolution chain: `bSeries`, the upper-left block reduction
`elementaryWeight_castAdd`, the powerset combinator
`foldr_mul_add_eq_powerset_sum`, the recursive auxiliaries `rightAuxAt`
and `rightAuxAtCoef`, the kept/cut trunk pass-through ladder, and the
closed-form `convAt` collapse landed in cycle 534.

This module depends only on the §381 / §382 / §384-prep material from
`OpenMath.ButcherGroup.Core`. It is imported by
`OpenMath.ButcherGroup` to expose the §384 surface to downstream
modules.

Reference: Butcher, *Numerical Methods for Ordinary Differential
Equations*, §38.4. See also
`.prover-state/issues/butcher_section384_convolution.md`.
-/

open Finset

namespace ButcherTableau

variable {s : ℕ}

/-- Raw Butcher-series coefficient of a tableau at a rooted tree:
`∑ i, bᵢ Φᵢ(τ)`. The quotient-level version is `QuotEquiv.bSeries`;
this representative-level wrapper is convenient for the §384 convolution
identities before quotienting. -/
noncomputable def bSeries (tab : ButcherTableau s) (τ : BTree) : ℝ :=
  ∑ i, tab.b i * tab.elementaryWeight τ i

/-- The elementary weight of `ButcherProduct t₁ t₂` at an upper-left block
stage is exactly the elementary weight of `t₁`. This is the cut-side
reduction needed for the §384 convolution: once a child has crossed through
the lower-left `t₁.b` block, all further descendants remain inside the
first tableau. -/
theorem ButcherProduct.elementaryWeight_castAdd
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (τ : BTree) (i : Fin s) :
    (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.castAdd t i)
      = t₁.elementaryWeight τ i := by
  revert i
  refine BTree.rec
    (motive_1 := fun τ => ∀ i : Fin s,
      (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.castAdd t i)
        = t₁.elementaryWeight τ i)
    (motive_2 := fun children => ∀ i : Fin s,
      children.foldr
        (fun r acc => acc * (∑ k : Fin (s + t),
          (ButcherProduct t₁ t₂).A (Fin.castAdd t i) k *
            (ButcherProduct t₁ t₂).elementaryWeight r k)) 1 =
      children.foldr
        (fun r acc => acc * (∑ k : Fin s,
          t₁.A i k * t₁.elementaryWeight r k)) 1)
    ?leaf ?node ?nil ?cons τ
  · intro i
    simp
  · intro children hchildren i
    simpa [ButcherTableau.elementaryWeight] using hchildren i
  · intro i
    simp
  · intro head tail ih_head ih_tail i
    simp only [List.foldr]
    have hsum :
        (∑ k : Fin (s + t),
          (ButcherProduct t₁ t₂).A (Fin.castAdd t i) k *
            (ButcherProduct t₁ t₂).elementaryWeight head k) =
          ∑ k : Fin s, t₁.A i k * t₁.elementaryWeight head k := by
      rw [Fin.sum_univ_add]
      have hzero :
          (∑ k : Fin t,
            (ButcherProduct t₁ t₂).A (Fin.castAdd t i) (Fin.natAdd s k) *
              (ButcherProduct t₁ t₂).elementaryWeight head (Fin.natAdd s k)) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        simp [ButcherProduct]
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [ih_head k]
      simp [ButcherProduct]
    rw [ih_tail i, hsum]

/-- The cut-side weighted sum through the upper-left block is the raw
Butcher-series coefficient of the first tableau. -/
theorem ButcherProduct.bSeries_castAdd
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (τ : BTree) :
    (∑ i : Fin s, t₁.b i *
      (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.castAdd t i))
      = t₁.bSeries τ := by
  simp [bSeries, ButcherProduct.elementaryWeight_castAdd]

/-- List-level combinator: a `foldr`-style product of binomial sums
expands as a Finset.powerset-indexed sum over which factor is taken
from each list position. This is the list-version mirror of
`Finset.prod_add`. -/
private theorem foldr_mul_add_eq_powerset_sum {α : Type*}
    (children : List α) (x y : α → ℝ) :
    children.foldr (fun c acc => acc * (x c + y c)) 1
      = ∑ T ∈ (Finset.univ : Finset (Fin children.length)).powerset,
          (∏ k ∈ T, x children[k]) * ∏ k ∈ Finset.univ \ T, y children[k] := by
  have hprod : children.foldr (fun c acc => acc * (x c + y c)) 1
      = ∏ k : Fin children.length, (x children[k] + y children[k]) := by
    induction children with
    | nil => simp
    | cons c cs ih =>
      show cs.foldr (fun c acc => acc * (x c + y c)) 1 * (x c + y c)
           = ∏ k : Fin (cs.length + 1), (x (c :: cs)[k] + y (c :: cs)[k])
      rw [ih, Fin.prod_univ_succ]
      have h0 : (c :: cs)[(0 : Fin (cs.length + 1))] = c := rfl
      have hsucc : ∀ k : Fin cs.length,
          (c :: cs)[(k.succ : Fin (cs.length + 1))] = cs[k] := fun _ => rfl
      rw [h0]
      simp_rw [hsucc]
      ring
  rw [hprod, Finset.prod_add]

/-- Raw "sum over cuts" identity for the elementary weight of
`ButcherProduct t₁ t₂` at a `node children` tree, in a row
`Fin.natAdd s i` of the second-method block. The inner sum
`∑ k : Fin (s+t), (ButcherProduct t₁ t₂).A (natAdd s i) k * Φ_k` splits
into the lower-left block (`t₁.b j₁` broadcast across rows, paired
with `Φ` at upper-left columns `Fin.castAdd t j₁`) and the lower-right
block (`t₂.A i j₂`, paired with `Φ` at lower-right columns
`Fin.natAdd s j₂`). Applying `foldr_mul_add_eq_powerset_sum` to this
binomial split gives the powerset-indexed sum below.

This is the §384 "for each child, choose first-method `b`-cut versus
second-method `A`-keep" identity at a single node, with the inner
elementary weights kept in their raw `ButcherProduct`-indexed form.
The next layer (deferred) will recurse on the attached children to
reduce each factor to a `t₁.bSeries`/`t₂.elementaryWeight` shape. -/
theorem ButcherProduct.elementaryWeight_natAdd_node_eq_powerset_sum
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (i : Fin t) :
    (ButcherProduct t₁ t₂).elementaryWeight (BTree.node children) (Fin.natAdd s i)
      = ∑ T ∈ (Finset.univ : Finset (Fin children.length)).powerset,
          (∏ k ∈ T,
             ∑ j₁ : Fin s, t₁.b j₁ *
               (ButcherProduct t₁ t₂).elementaryWeight children[k] (Fin.castAdd t j₁))
            * ∏ k ∈ Finset.univ \ T,
                 ∑ j₂ : Fin t, t₂.A i j₂ *
                   (ButcherProduct t₁ t₂).elementaryWeight children[k] (Fin.natAdd s j₂) := by
  have hsplit : ∀ c : BTree,
      (∑ k : Fin (s + t),
        (ButcherProduct t₁ t₂).A (Fin.natAdd s i) k *
          (ButcherProduct t₁ t₂).elementaryWeight c k) =
      (∑ j₁ : Fin s, t₁.b j₁ *
        (ButcherProduct t₁ t₂).elementaryWeight c (Fin.castAdd t j₁))
      + (∑ j₂ : Fin t, t₂.A i j₂ *
        (ButcherProduct t₁ t₂).elementaryWeight c (Fin.natAdd s j₂)) := by
    intro c
    rw [Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl ?_
      intro j₁ _
      simp [ButcherProduct]
    · refine Finset.sum_congr rfl ?_
      intro j₂ _
      simp [ButcherProduct]
  rw [show (ButcherProduct t₁ t₂).elementaryWeight (BTree.node children) (Fin.natAdd s i)
        = children.foldr
          (fun c acc => acc * (∑ k : Fin (s + t),
            (ButcherProduct t₁ t₂).A (Fin.natAdd s i) k *
              (ButcherProduct t₁ t₂).elementaryWeight c k)) 1 from by
        simp [elementaryWeight]]
  have heq : (fun c (acc : ℝ) => acc * (∑ k : Fin (s + t),
        (ButcherProduct t₁ t₂).A (Fin.natAdd s i) k *
          (ButcherProduct t₁ t₂).elementaryWeight c k))
      = (fun c acc => acc *
        ((∑ j₁ : Fin s, t₁.b j₁ *
          (ButcherProduct t₁ t₂).elementaryWeight c (Fin.castAdd t j₁))
        + (∑ j₂ : Fin t, t₂.A i j₂ *
          (ButcherProduct t₁ t₂).elementaryWeight c (Fin.natAdd s j₂)))) := by
    funext c acc
    rw [hsplit]
  rw [heq]
  exact foldr_mul_add_eq_powerset_sum children
    (fun c => ∑ j₁ : Fin s, t₁.b j₁ *
      (ButcherProduct t₁ t₂).elementaryWeight c (Fin.castAdd t j₁))
    (fun c => ∑ j₂ : Fin t, t₂.A i j₂ *
      (ButcherProduct t₁ t₂).elementaryWeight c (Fin.natAdd s j₂))

/-- The same node-level §384 powerset identity as
`ButcherProduct.elementaryWeight_natAdd_node_eq_powerset_sum`, with the
cut-side factor reduced to the raw Butcher-series coefficient of `t₁`.
The summation index `S` records the children kept attached to the second
method; the complement `Sᶜ` records the children cut through `t₁.bSeries`. -/
theorem ButcherProduct.elementaryWeight_natAdd_node_eq_powerset_sum_bSeries
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (i : Fin t) :
    (ButcherProduct t₁ t₂).elementaryWeight (BTree.node children) (Fin.natAdd s i)
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∏ p ∈ S, ∑ j₂ : Fin t, t₂.A i j₂ *
            (ButcherProduct t₁ t₂).elementaryWeight (children.get p) (Fin.natAdd s j₂)) := by
  classical
  let cut : Fin children.length → ℝ := fun p => t₁.bSeries (children.get p)
  let keep : Fin children.length → ℝ := fun p =>
    ∑ j₂ : Fin t, t₂.A i j₂ *
      (ButcherProduct t₁ t₂).elementaryWeight (children.get p) (Fin.natAdd s j₂)
  have hraw :
      (ButcherProduct t₁ t₂).elementaryWeight (BTree.node children) (Fin.natAdd s i)
        = ∑ T ∈ (Finset.univ : Finset (Fin children.length)).powerset,
            (∏ p ∈ T, cut p) *
            (∏ p ∈ Finset.univ \ T, keep p) := by
    rw [ButcherProduct.elementaryWeight_natAdd_node_eq_powerset_sum]
    simp [cut, keep, ButcherProduct.bSeries_castAdd]
  have hraw_univ :
      (∑ T ∈ (Finset.univ : Finset (Fin children.length)).powerset,
          (∏ p ∈ T, cut p) *
          (∏ p ∈ Finset.univ \ T, keep p))
        = ∑ T : Finset (Fin children.length),
            (∏ p ∈ T, cut p) * (∏ p ∈ Tᶜ, keep p) := by
    simp [Finset.compl_eq_univ_sdiff]
  have hcompl :
      (∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, cut p) * (∏ p ∈ S, keep p))
        = ∑ T : Finset (Fin children.length),
            (∏ p ∈ T, cut p) * (∏ p ∈ Tᶜ, keep p) := by
    let complPerm : Equiv.Perm (Finset (Fin children.length)) :=
      { toFun := fun S => Sᶜ
        invFun := fun S => Sᶜ
        left_inv := by
          intro S
          ext p
          simp
        right_inv := by
          intro S
          ext p
          simp }
    simpa [complPerm] using
      (Equiv.sum_comp complPerm (fun T : Finset (Fin children.length) =>
        (∏ p ∈ T, cut p) * (∏ p ∈ Tᶜ, keep p)))
  rw [hraw, hraw_univ]
  exact hcompl.symm

/-- §384 right-block auxiliary `ψ`: the recursive contribution attached
to a second-method stage `i : Fin t` after the upper-left block has been
collapsed via `t₁.bSeries`. The `t₁` data only enters through `bSeries`
values on subtrees, which is the structural witness that the next layer
of the §384 convolution recursion can consume to expose a closed-form
`(trunk, cuts)` decomposition. -/
noncomputable def ButcherProduct.rightAuxAt
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    BTree → Fin t → ℝ
  | .leaf, _ => 1
  | .node children, i =>
      children.foldr
        (fun c acc => acc * (t₁.bSeries c +
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.rightAuxAt t₁ t₂ c j)) 1
termination_by t => sizeOf t
decreasing_by
  have hmem : sizeOf c < sizeOf children :=
    List.sizeOf_lt_of_mem (by assumption)
  have hnode : sizeOf children < sizeOf (BTree.node children) := by simp
  exact Nat.lt_trans hmem hnode

@[simp] theorem ButcherProduct.rightAuxAt_leaf
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ BTree.leaf i = 1 := by
  simp [ButcherProduct.rightAuxAt]

theorem ButcherProduct.rightAuxAt_node
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i
      = children.foldr
          (fun c acc => acc * (t₁.bSeries c +
            ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAt t₁ t₂ c j)) 1 := by
  rw [ButcherProduct.rightAuxAt]

/-- §384 right-block recursive reduction: the elementary weight of
`ButcherProduct t₁ t₂` at a second-method stage `Fin.natAdd s i` is the
recursive auxiliary `rightAuxAt t₁ t₂ τ i`. The `t₁` data only enters
through `bSeries`, which makes the closed-form `(trunk, cuts)`
decomposition viable on the next layer. -/
theorem ButcherProduct.elementaryWeight_natAdd
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (τ : BTree) (i : Fin t) :
    (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.natAdd s i)
      = ButcherProduct.rightAuxAt t₁ t₂ τ i := by
  revert i
  refine BTree.rec
    (motive_1 := fun τ => ∀ i : Fin t,
      (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.natAdd s i)
        = ButcherProduct.rightAuxAt t₁ t₂ τ i)
    (motive_2 := fun children => ∀ i : Fin t,
      children.foldr
        (fun r acc => acc * (∑ k : Fin (s + t),
          (ButcherProduct t₁ t₂).A (Fin.natAdd s i) k *
            (ButcherProduct t₁ t₂).elementaryWeight r k)) 1 =
      children.foldr
        (fun r acc => acc * (t₁.bSeries r +
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.rightAuxAt t₁ t₂ r j)) 1)
    ?leaf ?node ?nil ?cons τ
  · intro i
    simp
  · intro children hchildren i
    simpa [ButcherTableau.elementaryWeight,
           ButcherProduct.rightAuxAt_node] using hchildren i
  · intro i
    simp
  · intro head tail ih_head ih_tail i
    simp only [List.foldr]
    have hsum :
        (∑ k : Fin (s + t),
          (ButcherProduct t₁ t₂).A (Fin.natAdd s i) k *
            (ButcherProduct t₁ t₂).elementaryWeight head k) =
          t₁.bSeries head +
            ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAt t₁ t₂ head j := by
      rw [Fin.sum_univ_add]
      have hL :
          (∑ k : Fin s,
            (ButcherProduct t₁ t₂).A (Fin.natAdd s i) (Fin.castAdd t k) *
              (ButcherProduct t₁ t₂).elementaryWeight head (Fin.castAdd t k)) =
            t₁.bSeries head := by
        rw [ButcherTableau.bSeries]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [ButcherProduct.elementaryWeight_castAdd]
        simp [ButcherProduct]
      have hR :
          (∑ k : Fin t,
            (ButcherProduct t₁ t₂).A (Fin.natAdd s i) (Fin.natAdd s k) *
              (ButcherProduct t₁ t₂).elementaryWeight head (Fin.natAdd s k)) =
            ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAt t₁ t₂ head j := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [ih_head k]
        simp [ButcherProduct]
      rw [hL, hR]
    rw [ih_tail i, hsum]

/-- Node-level powerset expansion of the §384 right-block auxiliary. The
summation index `S` records children kept in the recursive second-method
stage sum; the complement records children already cut to `t₁.bSeries`. -/
theorem ButcherProduct.rightAuxAt_node_eq_powerset_sum
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
            ButcherProduct.rightAuxAt t₁ t₂ (children.get p) j) := by
  classical
  let cut : Fin children.length → ℝ := fun p => t₁.bSeries (children.get p)
  let keep : Fin children.length → ℝ := fun p =>
    ∑ j : Fin t, t₂.A i j *
      ButcherProduct.rightAuxAt t₁ t₂ (children.get p) j
  have hraw :
      ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i
        = ∑ T ∈ (Finset.univ : Finset (Fin children.length)).powerset,
            (∏ p ∈ T, cut p) *
            (∏ p ∈ Finset.univ \ T, keep p) := by
    rw [ButcherProduct.rightAuxAt_node]
    simpa [cut, keep] using
      (foldr_mul_add_eq_powerset_sum children
        (fun c => t₁.bSeries c)
        (fun c => ∑ j : Fin t, t₂.A i j *
          ButcherProduct.rightAuxAt t₁ t₂ c j))
  have hraw_univ :
      (∑ T ∈ (Finset.univ : Finset (Fin children.length)).powerset,
          (∏ p ∈ T, cut p) *
          (∏ p ∈ Finset.univ \ T, keep p))
        = ∑ T : Finset (Fin children.length),
            (∏ p ∈ T, cut p) * (∏ p ∈ Tᶜ, keep p) := by
    simp [Finset.compl_eq_univ_sdiff]
  have hcompl :
      (∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, cut p) * (∏ p ∈ S, keep p))
        = ∑ T : Finset (Fin children.length),
            (∏ p ∈ T, cut p) * (∏ p ∈ Tᶜ, keep p) := by
    let complPerm : Equiv.Perm (Finset (Fin children.length)) :=
      { toFun := fun S => Sᶜ
        invFun := fun S => Sᶜ
        left_inv := by
          intro S
          ext p
          simp
        right_inv := by
          intro S
          ext p
          simp }
    simpa [complPerm] using
      (Equiv.sum_comp complPerm (fun T : Finset (Fin children.length) =>
        (∏ p ∈ T, cut p) * (∏ p ∈ Tᶜ, keep p)))
  rw [hraw, hraw_univ]
  exact hcompl.symm

/-- The stage-`b` weighted form of
`ButcherProduct.rightAuxAt_node_eq_powerset_sum`, ready for the §384
closed-form convolution: after choosing kept children `S`, the cut-side
`t₁.bSeries` product is independent of the second-method stage sum. -/
theorem ButcherProduct.bSeries_natAdd_node_eq_powerset_sum
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i)
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAt t₁ t₂ (children.get p) j)) := by
  classical
  let cut : Finset (Fin children.length) → ℝ := fun S =>
    ∏ p ∈ Sᶜ, t₁.bSeries (children.get p)
  let keep : Fin t → Finset (Fin children.length) → ℝ := fun i S =>
    ∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
      ButcherProduct.rightAuxAt t₁ t₂ (children.get p) j
  have hstage : ∀ i : Fin t,
      ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i
        = ∑ S : Finset (Fin children.length), cut S * keep i S := by
    intro i
    simpa [cut, keep] using
      (ButcherProduct.rightAuxAt_node_eq_powerset_sum t₁ t₂ children i)
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i)
        = ∑ i : Fin t, t₂.b i *
            (∑ S : Finset (Fin children.length), cut S * keep i S) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hstage i]
    _ = ∑ i : Fin t, ∑ S : Finset (Fin children.length),
          t₂.b i * (cut S * keep i S) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ S : Finset (Fin children.length), ∑ i : Fin t,
          t₂.b i * (cut S * keep i S) := by
        rw [Finset.sum_comm]
    _ = ∑ S : Finset (Fin children.length),
          cut S * (∑ i : Fin t, t₂.b i * keep i S) := by
        refine Finset.sum_congr rfl ?_
        intro S _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
    _ = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAt t₁ t₂ (children.get p) j)) := by
        simp [cut, keep]

/-- Two-level powerset expansion of the §384 right-block auxiliary: each
kept child's contribution is itself decomposed by case analysis on the
child's tree shape, exposing the second-method side one full structural
layer deeper. Leaf children contribute a bare `t₂.A i j` row sum (since
`rightAuxAt t₁ t₂ leaf j = 1`); node children unfold into the inner
`(cut, kept)` powerset sum at the new parent index `j`. -/
theorem ButcherProduct.rightAuxAt_node_two_level_eq_powerset_sum
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∏ p ∈ S,
            (match children.get p with
             | BTree.leaf => ∑ j : Fin t, t₂.A i j
             | BTree.node gc =>
                 ∑ j : Fin t, t₂.A i j *
                   (∑ S' : Finset (Fin gc.length),
                     (∏ q ∈ S'ᶜ, t₁.bSeries (gc.get q)) *
                     (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                       ButcherProduct.rightAuxAt t₁ t₂ (gc.get q) k)))) := by
  rw [ButcherProduct.rightAuxAt_node_eq_powerset_sum]
  refine Finset.sum_congr rfl ?_
  intro S _
  congr 1
  refine Finset.prod_congr rfl ?_
  intro p _
  generalize children.get p = c
  cases c with
  | leaf =>
    simp [ButcherProduct.rightAuxAt_leaf]
  | node gc =>
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ButcherProduct.rightAuxAt_node_eq_powerset_sum]

/-- The stage-`b` weighted form of
`ButcherProduct.rightAuxAt_node_two_level_eq_powerset_sum`: the cut-side
`t₁.bSeries` product factors out of the second-method `b`-weighted stage
sum, and each kept child's contribution is the explicit leaf-or-node
case split that exposes `t₁` only through `bSeries` calls on
grand-subtrees. -/
theorem ButcherProduct.bSeries_natAdd_node_two_level_eq_powerset_sum
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i)
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S,
              (match children.get p with
               | BTree.leaf => ∑ j : Fin t, t₂.A i j
               | BTree.node gc =>
                   ∑ j : Fin t, t₂.A i j *
                     (∑ S' : Finset (Fin gc.length),
                       (∏ q ∈ S'ᶜ, t₁.bSeries (gc.get q)) *
                       (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                         ButcherProduct.rightAuxAt t₁ t₂ (gc.get q) k))))) := by
  classical
  let cut : Finset (Fin children.length) → ℝ := fun S =>
    ∏ p ∈ Sᶜ, t₁.bSeries (children.get p)
  let kept : Fin t → Finset (Fin children.length) → ℝ := fun i S =>
    ∏ p ∈ S,
      (match children.get p with
       | BTree.leaf => ∑ j : Fin t, t₂.A i j
       | BTree.node gc =>
           ∑ j : Fin t, t₂.A i j *
             (∑ S' : Finset (Fin gc.length),
               (∏ q ∈ S'ᶜ, t₁.bSeries (gc.get q)) *
               (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                 ButcherProduct.rightAuxAt t₁ t₂ (gc.get q) k)))
  have hstage : ∀ i : Fin t,
      ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i
        = ∑ S : Finset (Fin children.length), cut S * kept i S := by
    intro i
    simpa [cut, kept] using
      (ButcherProduct.rightAuxAt_node_two_level_eq_powerset_sum t₁ t₂ children i)
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i)
        = ∑ i : Fin t, t₂.b i *
            (∑ S : Finset (Fin children.length), cut S * kept i S) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hstage i]
    _ = ∑ i : Fin t, ∑ S : Finset (Fin children.length),
          t₂.b i * (cut S * kept i S) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ S : Finset (Fin children.length), ∑ i : Fin t,
          t₂.b i * (cut S * kept i S) := by
        rw [Finset.sum_comm]
    _ = ∑ S : Finset (Fin children.length),
          cut S * (∑ i : Fin t, t₂.b i * kept i S) := by
        refine Finset.sum_congr rfl ?_
        intro S _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
    _ = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S,
              (match children.get p with
               | BTree.leaf => ∑ j : Fin t, t₂.A i j
               | BTree.node gc =>
                   ∑ j : Fin t, t₂.A i j *
                     (∑ S' : Finset (Fin gc.length),
                       (∏ q ∈ S'ᶜ, t₁.bSeries (gc.get q)) *
                       (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                         ButcherProduct.rightAuxAt t₁ t₂ (gc.get q) k))))) := by
        simp [cut, kept]

/-- Closed-form right-block auxiliary: at each node, sum over subsets
`S` of children. Children outside `S` are cut via `coef` (later specialised
to `t₁.bSeries`); children inside `S` are kept and feed back into the
recursion through `t₂.A i j`. -/
noncomputable def ButcherProduct.rightAuxAtCoef
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) :
    BTree → Fin t → ℝ
  | .leaf, _ => 1
  | .node children, i =>
      ∑ S ∈ (Finset.univ : Finset (Fin children.length)).powerset,
        (∏ p ∈ Sᶜ, coef (children.get p)) *
        (∏ p ∈ S,
          ∑ j : Fin t,
            t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef (children.get p) j)
termination_by τ => sizeOf τ
decreasing_by
  have hmem : sizeOf (children.get p) < sizeOf children :=
    List.sizeOf_lt_of_mem (List.get_mem children p)
  have hnode : sizeOf children < sizeOf (BTree.node children) := by simp
  exact Nat.lt_trans hmem hnode

@[simp] theorem ButcherProduct.rightAuxAtCoef_leaf
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (i : Fin t) :
    ButcherProduct.rightAuxAtCoef t₂ coef BTree.leaf i = 1 := by
  simp [ButcherProduct.rightAuxAtCoef]

theorem ButcherProduct.rightAuxAtCoef_node
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i =
      ∑ S ∈ (Finset.univ : Finset (Fin children.length)).powerset,
        (∏ p ∈ Sᶜ, coef (children.get p)) *
        (∏ p ∈ S,
          ∑ j : Fin t,
            t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef (children.get p) j) := by
  rw [ButcherProduct.rightAuxAtCoef]

/-- Leaf-level `b`-weighted reduction for the coefficient-parametric
right-block auxiliary: leaves do not see the cut coefficient function. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_leaf
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef BTree.leaf i)
      = t₂.weightsSum := by
  simp [ButcherTableau.weightsSum]

/-- One-child node specialization of the coefficient-parametric right-block
auxiliary. It exposes the single `cut OR keep` branch. -/
theorem ButcherProduct.rightAuxAtCoef_node_singleton
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (child : BTree) (i : Fin t) :
    ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node [child]) i
      = coef child +
        ∑ j : Fin t,
          t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef child j := by
  simp [ButcherProduct.rightAuxAtCoef_node]
  have hpowerset :
      ({0} : Finset (Fin 1)).powerset =
        ({∅, {0}} : Finset (Finset (Fin 1))) := by
    ext S
    simp [Finset.subset_singleton_iff]
  have hcompl : ({0} : Finset (Fin 1))ᶜ = ∅ := by
    ext x
    fin_cases x
    simp
  rw [hpowerset]
  simp [hcompl]

/-- One-child `b`-weighted closed form for the coefficient-parametric
right-block auxiliary. The cut term factors through `weightsSum`, while
the kept term retains the `A`-twisted recursion. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node_singleton
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (child : BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node [child]) i)
      = coef child * t₂.weightsSum +
        ∑ i : Fin t, t₂.b i *
          ∑ j : Fin t,
            t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef child j := by
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node [child]) i)
        = ∑ i : Fin t, t₂.b i *
            (coef child +
              ∑ j : Fin t,
                t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef child j) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [ButcherProduct.rightAuxAtCoef_node_singleton]
    _ = ∑ i : Fin t,
          (t₂.b i * coef child +
            t₂.b i *
              ∑ j : Fin t,
                t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef child j) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
    _ = (∑ i : Fin t, t₂.b i * coef child) +
          ∑ i : Fin t, t₂.b i *
            ∑ j : Fin t,
              t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef child j := by
        rw [Finset.sum_add_distrib]
    _ = coef child * t₂.weightsSum +
          ∑ i : Fin t, t₂.b i *
            ∑ j : Fin t,
              t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef child j := by
        congr 1
        calc
          (∑ i : Fin t, t₂.b i * coef child)
              = ∑ i : Fin t, coef child * t₂.b i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
          _ = coef child * t₂.weightsSum := by
            simp [ButcherTableau.weightsSum, Finset.mul_sum]

/-- Powerset-form unfolding of the coefficient-parametric right-block
auxiliary at a node, with the indexing set restated as the universal
`Finset (Fin children.length)`. The summation index `S` records the
children kept attached to the second method via `t₂.A`-twisted recursion;
the complement `Sᶜ` records the children cut through `coef`. This is the
§384 mirror of `ButcherProduct.rightAuxAt_node_eq_powerset_sum` with
`coef` replacing `t₁.bSeries`. -/
theorem ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, coef (children.get p)) *
          (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
            ButcherProduct.rightAuxAtCoef t₂ coef (children.get p) j) := by
  rw [ButcherProduct.rightAuxAtCoef_node, Finset.powerset_univ]

/-- The stage-`b` weighted form of
`ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum`, ready for the §384
closed-form convolution: after choosing kept children `S`, the cut-side
`coef` product is independent of the second-method stage sum. This is the
`coef`-parametric mirror of
`ButcherProduct.bSeries_natAdd_node_eq_powerset_sum`. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, coef (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAtCoef t₂ coef (children.get p) j)) := by
  classical
  let cut : Finset (Fin children.length) → ℝ := fun S =>
    ∏ p ∈ Sᶜ, coef (children.get p)
  let keep : Fin t → Finset (Fin children.length) → ℝ := fun i S =>
    ∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
      ButcherProduct.rightAuxAtCoef t₂ coef (children.get p) j
  have hstage : ∀ i : Fin t,
      ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i
        = ∑ S : Finset (Fin children.length), cut S * keep i S := by
    intro i
    simpa [cut, keep] using
      (ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum t₂ coef children i)
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
        = ∑ i : Fin t, t₂.b i *
            (∑ S : Finset (Fin children.length), cut S * keep i S) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hstage i]
    _ = ∑ i : Fin t, ∑ S : Finset (Fin children.length),
          t₂.b i * (cut S * keep i S) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ S : Finset (Fin children.length), ∑ i : Fin t,
          t₂.b i * (cut S * keep i S) := by
        rw [Finset.sum_comm]
    _ = ∑ S : Finset (Fin children.length),
          cut S * (∑ i : Fin t, t₂.b i * keep i S) := by
        refine Finset.sum_congr rfl ?_
        intro S _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
    _ = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, coef (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAtCoef t₂ coef (children.get p) j)) := by
        simp [cut, keep]

/-- Two-level powerset expansion of the coefficient-parametric right-block
auxiliary. Each kept child is case-split: leaves collapse to a row sum of
`t₂.A`, while node children unfold into the inner powerset decomposition at
the new parent stage. -/
theorem ButcherProduct.rightAuxAtCoef_node_two_level_eq_powerset_sum
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, coef (children.get p)) *
          (∏ p ∈ S,
            (match children.get p with
             | BTree.leaf => ∑ j : Fin t, t₂.A i j
             | BTree.node gc =>
                 ∑ j : Fin t, t₂.A i j *
                   (∑ S' : Finset (Fin gc.length),
                     (∏ q ∈ S'ᶜ, coef (gc.get q)) *
                     (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                       ButcherProduct.rightAuxAtCoef t₂ coef (gc.get q) k)))) := by
  rw [ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum]
  refine Finset.sum_congr rfl ?_
  intro S _
  congr 1
  refine Finset.prod_congr rfl ?_
  intro p _
  generalize children.get p = c
  cases c with
  | leaf =>
    simp [ButcherProduct.rightAuxAtCoef_leaf]
  | node gc =>
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum]

/-- The stage-`b` weighted form of
`ButcherProduct.rightAuxAtCoef_node_two_level_eq_powerset_sum`. The
cut-side `coef` product factors through the second-method weighted stage
sum, while each kept child is expanded one structural layer deeper. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node_two_level
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, coef (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S,
              (match children.get p with
               | BTree.leaf => ∑ j : Fin t, t₂.A i j
               | BTree.node gc =>
                   ∑ j : Fin t, t₂.A i j *
                     (∑ S' : Finset (Fin gc.length),
                       (∏ q ∈ S'ᶜ, coef (gc.get q)) *
                       (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                         ButcherProduct.rightAuxAtCoef t₂ coef (gc.get q) k))))) := by
  classical
  let cut : Finset (Fin children.length) → ℝ := fun S =>
    ∏ p ∈ Sᶜ, coef (children.get p)
  let kept : Fin t → Finset (Fin children.length) → ℝ := fun i S =>
    ∏ p ∈ S,
      (match children.get p with
       | BTree.leaf => ∑ j : Fin t, t₂.A i j
       | BTree.node gc =>
           ∑ j : Fin t, t₂.A i j *
             (∑ S' : Finset (Fin gc.length),
               (∏ q ∈ S'ᶜ, coef (gc.get q)) *
               (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                 ButcherProduct.rightAuxAtCoef t₂ coef (gc.get q) k)))
  have hstage : ∀ i : Fin t,
      ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i
        = ∑ S : Finset (Fin children.length), cut S * kept i S := by
    intro i
    simpa [cut, kept] using
      (ButcherProduct.rightAuxAtCoef_node_two_level_eq_powerset_sum t₂ coef children i)
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
        = ∑ i : Fin t, t₂.b i *
            (∑ S : Finset (Fin children.length), cut S * kept i S) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hstage i]
    _ = ∑ i : Fin t, ∑ S : Finset (Fin children.length),
          t₂.b i * (cut S * kept i S) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ S : Finset (Fin children.length), ∑ i : Fin t,
          t₂.b i * (cut S * kept i S) := by
        rw [Finset.sum_comm]
    _ = ∑ S : Finset (Fin children.length),
          cut S * (∑ i : Fin t, t₂.b i * kept i S) := by
        refine Finset.sum_congr rfl ?_
        intro S _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
    _ = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, coef (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S,
              (match children.get p with
               | BTree.leaf => ∑ j : Fin t, t₂.A i j
               | BTree.node gc =>
                   ∑ j : Fin t, t₂.A i j *
                     (∑ S' : Finset (Fin gc.length),
                       (∏ q ∈ S'ᶜ, coef (gc.get q)) *
                       (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                         ButcherProduct.rightAuxAtCoef t₂ coef (gc.get q) k))))) := by
        simp [cut, kept]

theorem ButcherProduct.rightAuxAt_leaf_eq_coef
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ BTree.leaf i =
      ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) BTree.leaf i := by
  simp [ButcherProduct.rightAuxAt_leaf, ButcherProduct.rightAuxAtCoef_leaf]

theorem ButcherProduct.rightAuxAt_node_eq_coef_one_level
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i =
      ∑ S ∈ (Finset.univ : Finset (Fin children.length)).powerset,
        (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
        (∏ p ∈ S,
          ∑ j : Fin t,
            t₂.A i j * ButcherProduct.rightAuxAt t₁ t₂ (children.get p) j) := by
  simpa using
    (ButcherProduct.rightAuxAt_node_eq_powerset_sum t₁ t₂ children i)

/-- §384 right-block structural equivalence: the recursive auxiliary
`rightAuxAt t₁ t₂` equals the closed-form `rightAuxAtCoef t₂ (t₁.bSeries)`,
i.e., `t₁` enters the right-block recursion only through its
`bSeries` values on subtrees. This is the structural witness Butcher's
§384 homomorphism statement consumes. -/
theorem ButcherProduct.rightAuxAt_eq_rightAuxAtCoef_bSeries
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (τ : BTree) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ τ i
      = ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) τ i := by
  classical
  revert i
  refine BTree.rec
    (motive_1 := fun τ => ∀ i : Fin t,
      ButcherProduct.rightAuxAt t₁ t₂ τ i
        = ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) τ i)
    (motive_2 := fun children => ∀ c ∈ children, ∀ j : Fin t,
      ButcherProduct.rightAuxAt t₁ t₂ c j
        = ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) c j)
    ?leaf ?node ?nil ?cons τ
  · intro i
    exact ButcherProduct.rightAuxAt_leaf_eq_coef t₁ t₂ i
  · intro children hchildren i
    rw [ButcherProduct.rightAuxAt_node_eq_coef_one_level,
        ButcherProduct.rightAuxAtCoef_node]
    refine Finset.sum_congr rfl ?_
    intro S _
    congr 1
    refine Finset.prod_congr rfl ?_
    intro p _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hchildren (children.get p) (List.get_mem children p) j]
  · intro c hc
    simp at hc
  · intro head tail ih_head ih_tail c hc j
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ih_head j
    · exact ih_tail c hc' j

/-- §384 elementary-weight corollary: the elementary weight of
`ButcherProduct t₁ t₂` at a second-method stage `Fin.natAdd s i` equals
the closed-form `rightAuxAtCoef t₂ (t₁.bSeries)`. This composes
`elementaryWeight_natAdd` with the structural equivalence. -/
theorem ButcherProduct.elementaryWeight_natAdd_eq_rightAuxAtCoef
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (τ : BTree) (i : Fin t) :
    (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.natAdd s i)
      = ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) τ i := by
  rw [ButcherProduct.elementaryWeight_natAdd,
      ButcherProduct.rightAuxAt_eq_rightAuxAtCoef_bSeries]

/-- §384 bSeries-level corollary: the second-method `b`-weighted stage
sum of `ButcherProduct t₁ t₂` evaluated at any tree `τ` collapses to a
sum of `rightAuxAtCoef`-values, mentioning `t₁` only through its
`bSeries`. -/
theorem ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (τ : BTree) :
    (∑ i : Fin t, t₂.b i *
        (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.natAdd s i))
      = ∑ i : Fin t, t₂.b i *
          ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) τ i := by
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [ButcherProduct.elementaryWeight_natAdd_eq_rightAuxAtCoef]

/-- `bSeries`-level two-level right-block expansion, specialized from the
coefficient-parametric auxiliary with `coef = t₁.bSeries`. This is the
node-level bridge from the product tableau's second block to the closed
coefficient-parametric §384 recursion one structural layer below the root. -/
theorem ButcherProduct.bSeries_natAdd_node_two_level_eq_rightAuxAtCoef
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        (ButcherProduct t₁ t₂).elementaryWeight
          (BTree.node children) (Fin.natAdd s i))
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S,
              (match children.get p with
               | BTree.leaf => ∑ j : Fin t, t₂.A i j
               | BTree.node gc =>
                   ∑ j : Fin t, t₂.A i j *
                     (∑ S' : Finset (Fin gc.length),
                       (∏ q ∈ S'ᶜ, t₁.bSeries (gc.get q)) *
                       (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                         ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) (gc.get q) k))))) := by
  rw [ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef,
      ButcherProduct.bWeighted_rightAuxAtCoef_node_two_level]

/-- Leaf-level `b`-weighted closed form, restated as `weightsSum`. This is
the cycle 528 `_eq` companion to `bWeighted_rightAuxAtCoef_leaf`, with the
same statement, exposed under the rotation-naming convention used by the
node-side closures. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_leaf_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef BTree.leaf i)
      = t₂.weightsSum :=
  ButcherProduct.bWeighted_rightAuxAtCoef_leaf t₂ coef

/-- Leaf specialization of the right-block coefficient at `coef := t₁.bSeries`:
the second-method `b`-weighted stage sum of the product tableau evaluated at
`BTree.leaf` collapses to `t₂.weightsSum`. -/
theorem ButcherProduct.bSeries_natAdd_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    (∑ i : Fin t, t₂.b i *
        (ButcherProduct t₁ t₂).elementaryWeight BTree.leaf
            (Fin.natAdd s i))
      = t₂.weightsSum := by
  rw [ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef,
      ButcherProduct.bWeighted_rightAuxAtCoef_leaf]

/-- Trunk-recursion form of the `b`-weighted root sum at a node tree: the
powerset sum is reindexed so that the chosen subset `S` records the children
*cut* via `coef`, while the complement `Sᶜ` records the children kept
attached through the second-method `t₂.A`-twisted recursion. This is the
`S`/`Sᶜ` swap of `bWeighted_rightAuxAtCoef_node`, ready for the §384
trunk-side closed form. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Fin children.length)).powerset,
          (∏ p ∈ S, coef (children.get p)) *
            (∑ i : Fin t, t₂.b i *
              (∏ p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j *
                  ButcherProduct.rightAuxAtCoef t₂ coef (children.get p) j)) := by
  classical
  rw [ButcherProduct.bWeighted_rightAuxAtCoef_node, Finset.powerset_univ]
  refine Finset.sum_nbij' (fun S => Sᶜ) (fun S => Sᶜ) ?_ ?_ ?_ ?_ ?_
  · intros S _; exact Finset.mem_univ _
  · intros S _; exact Finset.mem_univ _
  · intros S _; exact compl_compl S
  · intros S _; exact compl_compl S
  · intros S _; rw [compl_compl]

/-- Trunk-recursion kept-leaf simplification: if every child of the root is
`BTree.leaf`, the kept-side auxiliary factor in the trunk recursion collapses
to the plain row sum `∑ j, t₂.A i j`. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (coef : BTree → ℝ)
    (children : List BTree)
    (hAllLeaf : ∀ c ∈ children, c = BTree.leaf) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ _p ∈ S, coef BTree.leaf) *
            (∑ i : Fin t, t₂.b i *
                ∏ _p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j) := by
  classical
  have _ht₁ : t₁ = t₁ := rfl
  have hchild : ∀ p : Fin children.length, children.get p = BTree.leaf := by
    intro p
    exact hAllLeaf (children.get p) (List.get_mem children p)
  rw [ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion,
      Finset.powerset_univ]
  refine Finset.sum_congr rfl ?_
  intro S _
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro p _
    rw [hchild p]
  · refine Finset.sum_congr rfl ?_
    intro i _
    congr 1
    refine Finset.prod_congr rfl ?_
    intro p _
    rw [hchild p]
    simp [ButcherProduct.rightAuxAtCoef_leaf]

/-- Trunk-recursion kept singleton-node simplification: if every child of the
root is a one-child node `BTree.node [gc p]`, the kept-side recursive auxiliary
factor in the trunk recursion expands one structural level using the
single-child unfolding `ButcherProduct.rightAuxAtCoef_node_singleton`,
exposing only coefficient values on the grandchild trees `gc p`. This is the
kept-node companion to `bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq`,
demonstrating that the trunk recursion factors through `coef`-only values one
level beyond the leaf base case from cycle 529. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_singleton_node_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) (gc : Fin children.length → BTree)
    (hChild : ∀ p : Fin children.length, children.get p = BTree.node [gc p]) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ p ∈ S, coef (BTree.node [gc p])) *
            (∑ i : Fin t, t₂.b i *
              ∏ p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j *
                (coef (gc p) +
                  ∑ k : Fin t, t₂.A j k *
                    ButcherProduct.rightAuxAtCoef t₂ coef (gc p) k)) := by
  classical
  rw [ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion,
      Finset.powerset_univ]
  refine Finset.sum_congr rfl ?_
  intro S _
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro p _
    rw [hChild p]
  · refine Finset.sum_congr rfl ?_
    intro i _
    congr 1
    refine Finset.prod_congr rfl ?_
    intro p _
    rw [hChild p]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ButcherProduct.rightAuxAtCoef_node_singleton]

/-- Trunk-recursion kept node simplification: if every child of the root is
a node `BTree.node (gc p)`, the kept-side recursive auxiliary factor in the
trunk recursion expands by the full powerset decomposition over the
grandchildren of each kept child. This generalizes
`bWeighted_rightAuxAtCoef_node_trunk_kept_singleton_node_eq` from singleton
grandchild lists to arbitrary grandchild lists. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_node_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) (gc : Fin children.length → List BTree)
    (hChild : ∀ p : Fin children.length, children.get p = BTree.node (gc p)) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ p ∈ S, coef (BTree.node (gc p))) *
            (∑ i : Fin t, t₂.b i *
              ∏ p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j *
                (∑ T : Finset (Fin (gc p).length),
                  (∏ q ∈ Tᶜ, coef ((gc p).get q)) *
                    (∏ q ∈ T, ∑ k : Fin t, t₂.A j k *
                      ButcherProduct.rightAuxAtCoef t₂ coef ((gc p).get q) k))) := by
  classical
  rw [ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion,
      Finset.powerset_univ]
  refine Finset.sum_congr rfl ?_
  intro S _
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro p _
    rw [hChild p]
  · refine Finset.sum_congr rfl ?_
    intro i _
    congr 1
    refine Finset.prod_congr rfl ?_
    intro p _
    rw [hChild p]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum]

/-- bSeries-form corollary of
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq`: when every
child of the root is `BTree.leaf`, the second-method `b`-weighted stage sum
of `ButcherProduct t₁ t₂` evaluated at `BTree.node children` collapses to
the trunk-recursion RHS with `coef := t₁.bSeries`, so each cut factor
becomes `t₁.bSeries BTree.leaf` and the kept factor is the plain row sum
`∑ j, t₂.A i j`. -/
theorem ButcherProduct.bSeries_natAdd_node_trunk_kept_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree)
    (hAllLeaf : ∀ c ∈ children, c = BTree.leaf) :
    (∑ i : Fin t, t₂.b i *
        (ButcherProduct t₁ t₂).elementaryWeight
          (BTree.node children) (Fin.natAdd s i))
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ _p ∈ S, t₁.bSeries BTree.leaf) *
            (∑ i : Fin t, t₂.b i *
                ∏ _p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j) := by
  rw [ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef,
      ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq
        t₁ t₂ (t₁.bSeries) children hAllLeaf]

/-- bSeries-form corollary of
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_singleton_node_eq`:
when every child of the root is a one-child node `BTree.node [gc p]`, the
second-method `b`-weighted stage sum of `ButcherProduct t₁ t₂` is the
coefficient-parametric trunk-recursion RHS specialized at
`coef := t₁.bSeries`. -/
theorem ButcherProduct.bSeries_natAdd_node_trunk_kept_singleton_node_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (gc : Fin children.length → BTree)
    (hChild : ∀ p : Fin children.length, children.get p = BTree.node [gc p]) :
    (∑ i : Fin t, t₂.b i *
        (ButcherProduct t₁ t₂).elementaryWeight
          (BTree.node children) (Fin.natAdd s i))
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ p ∈ S, t₁.bSeries (BTree.node [gc p])) *
            (∑ i : Fin t, t₂.b i *
              ∏ p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j *
                (t₁.bSeries (gc p) +
                  ∑ k : Fin t, t₂.A j k *
                    ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) (gc p) k)) := by
  rw [ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef,
      ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_singleton_node_eq
        t₂ (t₁.bSeries) children gc hChild]

/-- Trunk-recursion unified kept-children simplification: each kept-side
recursive auxiliary factor in the trunk recursion is simplified by
case-splitting on whether the corresponding root child is a leaf or a node.
A leaf kept-child contributes the plain row sum `∑ j, t₂.A i j`; a node
kept-child contributes `∑ j, t₂.A i j *` times the inner powerset sum from
`rightAuxAtCoef_node_eq_powerset_sum`. This generalizes
`bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq` and
`bWeighted_rightAuxAtCoef_node_trunk_kept_node_eq` to arbitrary mixes of
leaves and nodes among the root's children. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (coef : BTree → ℝ) (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ p ∈ S, coef (children.get p)) *
            (∑ i : Fin t, t₂.b i *
              ∏ p ∈ Sᶜ,
                (match children.get p with
                 | BTree.leaf => ∑ j : Fin t, t₂.A i j
                 | BTree.node gc =>
                     ∑ j : Fin t, t₂.A i j *
                       (∑ T : Finset (Fin gc.length),
                         (∏ q ∈ Tᶜ, coef (gc.get q)) *
                         (∏ q ∈ T, ∑ k : Fin t, t₂.A j k *
                           ButcherProduct.rightAuxAtCoef t₂ coef (gc.get q) k)))) := by
  classical
  have _ht₁ : t₁ = t₁ := rfl
  rw [ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion,
      Finset.powerset_univ]
  refine Finset.sum_congr rfl ?_
  intro S _
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  congr 1
  refine Finset.prod_congr rfl ?_
  intro p _
  generalize children.get p = c
  cases c with
  | leaf =>
    simp [ButcherProduct.rightAuxAtCoef_leaf]
  | node gc =>
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum]

/-- bSeries-form corollary of
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_eq`: the
second-method `b`-weighted stage sum of `ButcherProduct t₁ t₂` evaluated at
`BTree.node children` is the trunk-recursion RHS specialized at
`coef := t₁.bSeries`, with each kept-child factor simplified by
case-splitting on whether the root child is a leaf or a node. -/
theorem ButcherProduct.bSeries_natAdd_node_trunk_kept_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        (ButcherProduct t₁ t₂).elementaryWeight
          (BTree.node children) (Fin.natAdd s i))
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ p ∈ S, t₁.bSeries (children.get p)) *
            (∑ i : Fin t, t₂.b i *
              ∏ p ∈ Sᶜ,
                (match children.get p with
                 | BTree.leaf => ∑ j : Fin t, t₂.A i j
                 | BTree.node gc =>
                     ∑ j : Fin t, t₂.A i j *
                       (∑ T : Finset (Fin gc.length),
                         (∏ q ∈ Tᶜ, t₁.bSeries (gc.get q)) *
                         (∏ q ∈ T, ∑ k : Fin t, t₂.A j k *
                           ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries)
                             (gc.get q) k)))) := by
  rw [ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef,
      ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_eq
        t₁ t₂ (t₁.bSeries) children]

/-- Trunk-recursion depth-2 kept-children simplification: after the cycle 532
kept-child pass-through, each kept grandchild that remains attached under a
kept node child is simplified one structural layer further by case-splitting
on whether that grandchild is a leaf or a node. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_two_level_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (coef : BTree → ℝ) (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ p ∈ S, coef (children.get p)) *
            (∑ i : Fin t, t₂.b i *
              ∏ p ∈ Sᶜ,
                (match children.get p with
                 | BTree.leaf => ∑ j : Fin t, t₂.A i j
                 | BTree.node gc =>
                     ∑ j : Fin t, t₂.A i j *
                       (∑ T : Finset (Fin gc.length),
                         (∏ q ∈ Tᶜ, coef (gc.get q)) *
                         (∏ q ∈ T,
                           (match gc.get q with
                            | BTree.leaf => ∑ k : Fin t, t₂.A j k
                            | BTree.node ggc =>
                                ∑ k : Fin t, t₂.A j k *
                                  (∑ U : Finset (Fin ggc.length),
                                    (∏ r ∈ Uᶜ, coef (ggc.get r)) *
                                    (∏ r ∈ U, ∑ l : Fin t, t₂.A k l *
                                      ButcherProduct.rightAuxAtCoef t₂ coef
                                        (ggc.get r) l))))))) := by
  classical
  have _ht₁ : t₁ = t₁ := rfl
  rw [ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_eq
    t₁ t₂ coef children]
  refine Finset.sum_congr rfl ?_
  intro S _
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  congr 1
  refine Finset.prod_congr rfl ?_
  intro p _
  generalize children.get p = c
  cases c with
  | leaf =>
    rfl
  | node gc =>
    refine Finset.sum_congr rfl ?_
    intro j _
    congr 1
    refine Finset.sum_congr rfl ?_
    intro T _
    congr 1
    refine Finset.prod_congr rfl ?_
    intro q _
    generalize gc.get q = c
    cases c with
    | leaf =>
      simp [ButcherProduct.rightAuxAtCoef_leaf]
    | node ggc =>
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum]

/-- bSeries-form corollary of
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_two_level_eq`:
specialize the depth-2 trunk kept-children simplification at
`coef := t₁.bSeries`. -/
theorem ButcherProduct.bSeries_natAdd_node_trunk_kept_two_level_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        (ButcherProduct t₁ t₂).elementaryWeight
          (BTree.node children) (Fin.natAdd s i))
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ p ∈ S, t₁.bSeries (children.get p)) *
            (∑ i : Fin t, t₂.b i *
              ∏ p ∈ Sᶜ,
                (match children.get p with
                 | BTree.leaf => ∑ j : Fin t, t₂.A i j
                 | BTree.node gc =>
                     ∑ j : Fin t, t₂.A i j *
                       (∑ T : Finset (Fin gc.length),
                         (∏ q ∈ Tᶜ, t₁.bSeries (gc.get q)) *
                         (∏ q ∈ T,
                           (match gc.get q with
                            | BTree.leaf => ∑ k : Fin t, t₂.A j k
                            | BTree.node ggc =>
                                ∑ k : Fin t, t₂.A j k *
                                  (∑ U : Finset (Fin ggc.length),
                                    (∏ r ∈ Uᶜ, t₁.bSeries (ggc.get r)) *
                                    (∏ r ∈ U, ∑ l : Fin t, t₂.A k l *
                                      ButcherProduct.rightAuxAtCoef t₂
                                        (t₁.bSeries) (ggc.get r) l))))))) := by
  rw [ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef,
      ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_two_level_eq
        t₁ t₂ (t₁.bSeries) children]

/-! ### §384 BTree-recursive closed form (`convAt`)

This block collapses the depth ladder of cycles 528-533 into a single
`BTree.rec` closure. `convAt` mirrors `rightAuxAtCoef` but with the
kept/cut roles of `S`/`Sᶜ` swapped at every node so that the recursion
unfolds along the kept side at every depth in one step. The headline
`rightAuxAtCoef_eq_convAt` shows that the two recursive auxiliaries are
equal, which makes any depth-N pass-through immediate. -/

/-- Closed-form recursive auxiliary mirroring `rightAuxAtCoef` but with
the kept-side powerset decomposition exposed at every level. -/
noncomputable def ButcherProduct.convAt
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) :
    BTree → Fin t → ℝ
  | .leaf, _ => 1
  | .node children, i =>
      ∑ S : Finset (Fin children.length),
        (∏ p ∈ S, coef (children.get p)) *
          (∏ p ∈ Sᶜ,
            ∑ j : Fin t, t₂.A i j *
              ButcherProduct.convAt t₂ coef (children.get p) j)
termination_by τ => sizeOf τ
decreasing_by
  have hmem : sizeOf (children.get p) < sizeOf children :=
    List.sizeOf_lt_of_mem (List.get_mem children p)
  have hnode : sizeOf children < sizeOf (BTree.node children) := by simp
  exact Nat.lt_trans hmem hnode

@[simp] theorem ButcherProduct.convAt_leaf
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (i : Fin t) :
    ButcherProduct.convAt t₂ coef BTree.leaf i = 1 := by
  simp [ButcherProduct.convAt]

theorem ButcherProduct.convAt_node
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.convAt t₂ coef (BTree.node children) i
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ S, coef (children.get p)) *
            (∏ p ∈ Sᶜ,
              ∑ j : Fin t, t₂.A i j *
                ButcherProduct.convAt t₂ coef (children.get p) j) := by
  rw [ButcherProduct.convAt]

/-- §384 single-step depth-ladder collapse: the §384 right-block
auxiliary `rightAuxAtCoef` agrees with the closed-form recursive
auxiliary `convAt` at every tree and stage. This makes every cycle
528-533 depth-ladder result immediate. -/
theorem ButcherProduct.rightAuxAtCoef_eq_convAt
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (τ : BTree) (i : Fin t) :
    ButcherProduct.rightAuxAtCoef t₂ coef τ i
      = ButcherProduct.convAt t₂ coef τ i := by
  classical
  revert i
  refine BTree.rec
    (motive_1 := fun τ => ∀ i : Fin t,
      ButcherProduct.rightAuxAtCoef t₂ coef τ i
        = ButcherProduct.convAt t₂ coef τ i)
    (motive_2 := fun children => ∀ c ∈ children, ∀ j : Fin t,
      ButcherProduct.rightAuxAtCoef t₂ coef c j
        = ButcherProduct.convAt t₂ coef c j)
    ?leaf ?node ?nil ?cons τ
  · intro i
    simp
  · intro children hchildren i
    rw [ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum,
        ButcherProduct.convAt_node]
    -- LHS: ∑ S, (∏ p ∈ Sᶜ, coef ...) * (∏ p ∈ S, ∑ j, A * rightAuxAtCoef)
    -- RHS: ∑ S, (∏ p ∈ S, coef ...) * (∏ p ∈ Sᶜ, ∑ j, A * convAt)
    -- Bridge: complement bijection on subsets + per-child IH.
    have hIH :
        ∀ S : Finset (Fin children.length), ∀ i : Fin t,
          (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAtCoef t₂ coef (children.get p) j) =
          (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
              ButcherProduct.convAt t₂ coef (children.get p) j) := by
      intro S i
      refine Finset.prod_congr rfl ?_
      intro p _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [hchildren (children.get p) (List.get_mem children p) j]
    let complPerm : Equiv.Perm (Finset (Fin children.length)) :=
      { toFun := fun S => Sᶜ
        invFun := fun S => Sᶜ
        left_inv := by intro S; ext p; simp
        right_inv := by intro S; ext p; simp }
    have hperm :
        (∑ S : Finset (Fin children.length),
            (∏ p ∈ Sᶜ, coef (children.get p)) *
            (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
              ButcherProduct.convAt t₂ coef (children.get p) j))
        = ∑ S : Finset (Fin children.length),
            (∏ p ∈ S, coef (children.get p)) *
            (∏ p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j *
              ButcherProduct.convAt t₂ coef (children.get p) j) := by
      simpa [complPerm] using
        (Equiv.sum_comp complPerm
          (fun S : Finset (Fin children.length) =>
            (∏ p ∈ S, coef (children.get p)) *
            (∏ p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j *
              ButcherProduct.convAt t₂ coef (children.get p) j)))
    calc
      (∑ S : Finset (Fin children.length),
            (∏ p ∈ Sᶜ, coef (children.get p)) *
            (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAtCoef t₂ coef (children.get p) j))
          = ∑ S : Finset (Fin children.length),
              (∏ p ∈ Sᶜ, coef (children.get p)) *
              (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
                ButcherProduct.convAt t₂ coef (children.get p) j) := by
            refine Finset.sum_congr rfl ?_
            intro S _
            rw [hIH S i]
      _ = ∑ S : Finset (Fin children.length),
              (∏ p ∈ S, coef (children.get p)) *
              (∏ p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j *
                ButcherProduct.convAt t₂ coef (children.get p) j) := hperm
  · intro c hc
    simp at hc
  · intro head tail ih_head ih_tail c hc j
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ih_head j
    · exact ih_tail c hc' j

/-- Stage-`b` weighted closed form for the §384 right block: the
`b`-weighted stage sum of `rightAuxAtCoef` collapses to the same
weighted sum of `convAt`. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_eq_convAt_sum
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (τ : BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef τ i)
      = ∑ i : Fin t, t₂.b i * ButcherProduct.convAt t₂ coef τ i := by
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [ButcherProduct.rightAuxAtCoef_eq_convAt]

/-- §384 bSeries-form corollary: the second-method `b`-weighted stage
sum of `ButcherProduct t₁ t₂` evaluated at any tree `τ` collapses to a
`convAt` sum, mentioning `t₁` only through its `bSeries`. -/
theorem ButcherProduct.bSeries_natAdd_eq_convAt
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (τ : BTree) :
    (∑ i : Fin t, t₂.b i *
        (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.natAdd s i))
      = ∑ i : Fin t, t₂.b i *
          ButcherProduct.convAt t₂ (t₁.bSeries) τ i := by
  rw [ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef,
      ButcherProduct.bWeighted_rightAuxAtCoef_eq_convAt_sum]

/-- §384 closed-form for the product bSeries: split the `Fin (s+t)` stage
sum into the upper-left `Fin s` block (which collapses to `t₁.bSeries τ`
via the cycle 519 corollary `bSeries_castAdd`) and the lower-right `Fin t`
block (which collapses to a `convAt` sum via the cycle 534 corollary
`bSeries_natAdd_eq_convAt`). The right-hand side mentions `t₁` only
through `t₁.bSeries` and `t₂` only through `t₂.A` / `t₂.b`. -/
theorem ButcherProduct.bSeries_eq_split
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (τ : BTree) :
    (ButcherProduct t₁ t₂).bSeries τ
      = t₁.bSeries τ
        + ∑ i : Fin t, t₂.b i *
            ButcherProduct.convAt t₂ (t₁.bSeries) τ i := by
  unfold bSeries
  rw [Fin.sum_univ_add]
  congr 1
  · -- Upper-left block: `b (castAdd t i) = t₁.b i`, then `bSeries_castAdd`.
    have h : ∀ i : Fin s,
        (ButcherProduct t₁ t₂).b (Fin.castAdd t i) *
            (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.castAdd t i)
          = t₁.b i *
            (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.castAdd t i) := by
      intro i
      rw [butcherProduct_b_castAdd]
    simp only [h]
    exact ButcherProduct.bSeries_castAdd t₁ t₂ τ
  · -- Lower-right block: `b (natAdd s i) = t₂.b i`, then `bSeries_natAdd_eq_convAt`.
    have h : ∀ i : Fin t,
        (ButcherProduct t₁ t₂).b (Fin.natAdd s i) *
            (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.natAdd s i)
          = t₂.b i *
            (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.natAdd s i) := by
      intro i
      rw [butcherProduct_b_natAdd]
    simp only [h]
    exact ButcherProduct.bSeries_natAdd_eq_convAt t₁ t₂ τ

/-- §384 honest bSeries-side convolution: the product of a coefficient
function `φ : BTree → ℝ` with the second tableau `t₂`. This is **not**
tautological — `bConv φ t₂` reads `t₂.A` at every internal node through
`convAt`, not just `t₂.bSeries`. By cycle 536's `bSeries_eq_bConv`,
`(t₁.product t₂).bSeries = bConv t₁.bSeries t₂` on every tree. -/
noncomputable def ButcherProduct.bConv
    {t : ℕ} (φ : BTree → ℝ) (t₂ : ButcherTableau t) (τ : BTree) : ℝ :=
  φ τ + ∑ i : Fin t, t₂.b i * ButcherProduct.convAt t₂ φ τ i

/-- The `bConv` closed form computes the product bSeries: every product
tableau's bSeries factors through the bSeries of its first factor and the
honest tree-level convolution `bConv`. -/
theorem ButcherProduct.bSeries_eq_bConv
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (τ : BTree) :
    (ButcherProduct t₁ t₂).bSeries τ
      = ButcherProduct.bConv t₁.bSeries t₂ τ := by
  rw [ButcherProduct.bSeries_eq_split, ButcherProduct.bConv]

/-- A child of `BTree.node children` has strictly smaller order than its
parent. Local copy of the unnamed helper used elsewhere; needed by the
`coef`-slot congruence below. -/
private theorem child_order_lt_of_mem_node
    {children : List BTree} {ch : BTree} (hmem : ch ∈ children) :
    ch.order < (BTree.node children).order := by
  simp only [BTree.order_node]
  have hsum : ch.order ≤ children.foldr (fun t n => t.order + n) 0 := by
    induction children with
    | nil => simp at hmem
    | cons hd tl ih =>
      simp only [List.foldr]
      rcases List.mem_cons.mp hmem with rfl | htl
      · omega
      · have := ih htl
        omega
  omega

/-- `coef`-slot congruence for `convAt`: if two coefficient functions
`coef`, `coef'` agree on every subtree of order at most `τ.order`, then
`convAt t₂ coef τ i = convAt t₂ coef' τ i`. This is the per-tree-fixed
agreement lemma needed for the next-cycle attempt at
`IsG1Equiv.product_congr` on the `t₁` slot. -/
theorem ButcherProduct.convAt_congr_coef
    {t : ℕ} {coef coef' : BTree → ℝ}
    (t₂ : ButcherTableau t) (τ : BTree)
    (hcoef : ∀ σ : BTree, σ.order ≤ τ.order → coef σ = coef' σ)
    (i : Fin t) :
    ButcherProduct.convAt t₂ coef τ i
      = ButcherProduct.convAt t₂ coef' τ i := by
  classical
  revert hcoef i
  refine BTree.rec
    (motive_1 := fun τ =>
      (∀ σ : BTree, σ.order ≤ τ.order → coef σ = coef' σ) →
      ∀ i : Fin t,
      ButcherProduct.convAt t₂ coef τ i
        = ButcherProduct.convAt t₂ coef' τ i)
    (motive_2 := fun children => ∀ c ∈ children,
      (∀ σ : BTree, σ.order ≤ c.order → coef σ = coef' σ) →
      ∀ j : Fin t,
      ButcherProduct.convAt t₂ coef c j
        = ButcherProduct.convAt t₂ coef' c j)
    ?leaf ?node ?nil ?cons τ
  · intro _ i
    simp
  · intro children hchildren hcoef i
    rw [ButcherProduct.convAt_node, ButcherProduct.convAt_node]
    refine Finset.sum_congr rfl ?_
    intro S _
    -- For each `S`, the kept-side product agrees pointwise via `hcoef`,
    -- and the cut-side product agrees via the per-child IH at strictly
    -- smaller order.
    have hcoef_child : ∀ p : Fin children.length,
        coef (children.get p) = coef' (children.get p) := by
      intro p
      have hmem : children.get p ∈ children := List.get_mem children p
      have hlt : (children.get p).order < (BTree.node children).order :=
        child_order_lt_of_mem_node hmem
      exact hcoef (children.get p) (Nat.le_of_lt hlt)
    have hkept :
        (∏ p ∈ S, coef (children.get p))
          = ∏ p ∈ S, coef' (children.get p) := by
      refine Finset.prod_congr rfl ?_
      intro p _
      exact hcoef_child p
    have hcut :
        (∏ p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j *
              ButcherProduct.convAt t₂ coef (children.get p) j)
          = ∏ p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j *
              ButcherProduct.convAt t₂ coef' (children.get p) j := by
      refine Finset.prod_congr rfl ?_
      intro p _
      refine Finset.sum_congr rfl ?_
      intro j _
      have hmem : children.get p ∈ children := List.get_mem children p
      have hlt : (children.get p).order < (BTree.node children).order :=
        child_order_lt_of_mem_node hmem
      have hcoef' : ∀ σ : BTree, σ.order ≤ (children.get p).order →
          coef σ = coef' σ := by
        intro σ hσ
        exact hcoef σ (Nat.le_of_lt (Nat.lt_of_le_of_lt hσ hlt))
      rw [hchildren (children.get p) hmem hcoef' j]
    rw [hkept, hcut]
  · intro c hc
    simp at hc
  · intro head tail ih_head ih_tail c hc hcoef j
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ih_head hcoef j
    · exact ih_tail c hc' hcoef j

/-- Internal stage-permutation transport for `convAt`. This follows the
same orientation as `IsRKEquivalent`: the permutation maps stages of the
second tableau back to stages of the first. -/
private theorem convAt_perm_t2_aux
    {t : ℕ} {t₂ t₂' : ButcherTableau t} {σ : Equiv.Perm (Fin t)}
    (hA : ∀ i j, t₂'.A i j = t₂.A (σ i) (σ j))
    (coef : BTree → ℝ) (τ : BTree) (i : Fin t) :
    ButcherProduct.convAt t₂' coef τ i
      = ButcherProduct.convAt t₂ coef τ (σ i) := by
  classical
  revert i
  refine BTree.rec
    (motive_1 := fun τ => ∀ i : Fin t,
      ButcherProduct.convAt t₂' coef τ i
        = ButcherProduct.convAt t₂ coef τ (σ i))
    (motive_2 := fun children => ∀ c ∈ children, ∀ i : Fin t,
      ButcherProduct.convAt t₂' coef c i
        = ButcherProduct.convAt t₂ coef c (σ i))
    ?leaf ?node ?nil ?cons τ
  · intro i
    simp
  · intro children hchildren i
    rw [ButcherProduct.convAt_node, ButcherProduct.convAt_node]
    refine Finset.sum_congr rfl ?_
    intro S _
    have hcut :
        (∏ p ∈ Sᶜ, ∑ j : Fin t, t₂'.A i j *
              ButcherProduct.convAt t₂' coef (children.get p) j)
          = ∏ p ∈ Sᶜ, ∑ j : Fin t, t₂.A (σ i) j *
              ButcherProduct.convAt t₂ coef (children.get p) j := by
      refine Finset.prod_congr rfl ?_
      intro p _
      calc
        (∑ j : Fin t, t₂'.A i j *
              ButcherProduct.convAt t₂' coef (children.get p) j)
            = ∑ j : Fin t, t₂.A (σ i) (σ j) *
                ButcherProduct.convAt t₂ coef (children.get p) (σ j) := by
                refine Finset.sum_congr rfl ?_
                intro j _
                rw [hA i j,
                  hchildren (children.get p) (List.get_mem children p) j]
        _ = ∑ j : Fin t, t₂.A (σ i) j *
              ButcherProduct.convAt t₂ coef (children.get p) j := by
                exact Equiv.sum_comp σ
                  (fun j : Fin t => t₂.A (σ i) j *
                    ButcherProduct.convAt t₂ coef (children.get p) j)
    rw [hcut]
  · intro c hc
    simp at hc
  · intro head tail ih_head ih_tail c hc i
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ih_head i
    · exact ih_tail c hc' i

/-- Permutation transport for `convAt` along an `IsRKEquivalent`
witness on `t₂`. For a fixed coefficient slot `coef`, the recursive
auxiliary `convAt t₂ coef τ` transports through a relabelling permutation
between equivalent tableaux. -/
theorem ButcherProduct.convAt_isRKEquivalent_t2
    {t : ℕ} {t₂ t₂' : ButcherTableau t}
    (h : IsRKEquivalent t₂ t₂')
    (coef : BTree → ℝ) (τ : BTree) (i : Fin t) :
    ∃ i', ButcherProduct.convAt t₂' coef τ i'
      = ButcherProduct.convAt t₂ coef τ i := by
  obtain ⟨σ, hA, _, _⟩ := h
  refine ⟨σ.symm i, ?_⟩
  simpa using
    (convAt_perm_t2_aux (t₂ := t₂) (t₂' := t₂') (σ := σ) hA
      coef τ (σ.symm i))

/-- `b`-weighted form: the `b`-weighted sum
`∑ i, t₂.b i * convAt t₂ coef τ i` is invariant under
`IsRKEquivalent` on `t₂`. -/
theorem ButcherProduct.bWeighted_convAt_isRKEquivalent_t2
    {t : ℕ} {t₂ t₂' : ButcherTableau t}
    (h : IsRKEquivalent t₂ t₂')
    (coef : BTree → ℝ) (τ : BTree) :
    (∑ i : Fin t, t₂.b i * ButcherProduct.convAt t₂ coef τ i)
      = ∑ i : Fin t, t₂'.b i * ButcherProduct.convAt t₂' coef τ i := by
  obtain ⟨σ, hA, hb, _⟩ := h
  have hsum :
      (∑ i : Fin t, t₂'.b i * ButcherProduct.convAt t₂' coef τ i)
        = ∑ i : Fin t, t₂.b i * ButcherProduct.convAt t₂ coef τ i := by
    calc
      (∑ i : Fin t, t₂'.b i * ButcherProduct.convAt t₂' coef τ i)
          = ∑ i : Fin t, t₂.b (σ i) *
              ButcherProduct.convAt t₂ coef τ (σ i) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [hb i,
                convAt_perm_t2_aux (t₂ := t₂) (t₂' := t₂') (σ := σ)
                  hA coef τ i]
      _ = ∑ i : Fin t, t₂.b i * ButcherProduct.convAt t₂ coef τ i := by
              exact Equiv.sum_comp σ
                (fun i : Fin t => t₂.b i * ButcherProduct.convAt t₂ coef τ i)
  exact hsum.symm

/-- `bConv` is invariant in the `t₂` slot under `IsRKEquivalent`. -/
theorem ButcherProduct.bConv_isRKEquivalent_t2
    {t : ℕ} {t₂ t₂' : ButcherTableau t}
    (h : IsRKEquivalent t₂ t₂')
    (φ : BTree → ℝ) (τ : BTree) :
    ButcherProduct.bConv φ t₂ τ = ButcherProduct.bConv φ t₂' τ := by
  rw [ButcherProduct.bConv, ButcherProduct.bConv,
      ButcherProduct.bWeighted_convAt_isRKEquivalent_t2 h φ τ]

/-- Honest convolution-form invariance on the `bSeries` of the product
under `IsRKEquivalent` on `t₂`. -/
theorem ButcherProduct.bSeries_product_isRKEquivalent_t2
    {s t : ℕ} (t₁ : ButcherTableau s)
    {t₂ t₂' : ButcherTableau t}
    (h : IsRKEquivalent t₂ t₂') (τ : BTree) :
    (ButcherProduct t₁ t₂).bSeries τ = (ButcherProduct t₁ t₂').bSeries τ := by
  rw [ButcherProduct.bSeries_eq_bConv, ButcherProduct.bSeries_eq_bConv]
  exact ButcherProduct.bConv_isRKEquivalent_t2 h t₁.bSeries τ

/-! ### §384 honest bSeries-only convolution: closed forms on the
b-weighted right block.

Cycle 538: the first concrete lemmas in the closed form
`∑ i, t₂.b i * convAt t₂ coef τ i` that mention `t₂` only through
`t₂.bSeries` values on subtrees of `τ`. -/

/-- Singleton-node closed form: the b-weighted right block at
`BTree.node [c]` splits into a `weightsSum`-scaled cut term on `coef c`
and a kept term that recurses one level into `convAt` at `c`. -/
theorem ButcherProduct.bWeighted_convAt_singleton_node_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (c : BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef (BTree.node [c]) i)
      = t₂.weightsSum * coef c
        + ∑ i : Fin t, t₂.b i *
            (∑ j : Fin t, t₂.A i j *
              ButcherProduct.convAt t₂ coef c j) := by
  have hLHS :
      (∑ i : Fin t, t₂.b i *
          ButcherProduct.convAt t₂ coef (BTree.node [c]) i)
        = ∑ i : Fin t, t₂.b i *
            ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node [c]) i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ButcherProduct.rightAuxAtCoef_eq_convAt]
  have hSing :
      (∑ i : Fin t, t₂.b i *
          ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node [c]) i)
        = coef c * t₂.weightsSum +
          ∑ i : Fin t, t₂.b i *
            ∑ j : Fin t,
              t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef c j :=
    ButcherProduct.bWeighted_rightAuxAtCoef_node_singleton t₂ coef c
  have hKept :
      (∑ i : Fin t, t₂.b i *
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.rightAuxAtCoef t₂ coef c j)
        = ∑ i : Fin t, t₂.b i *
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.convAt t₂ coef c j := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine congrArg _ ?_
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ButcherProduct.rightAuxAtCoef_eq_convAt]
  rw [hLHS, hSing, hKept, mul_comm (coef c) t₂.weightsSum]

/-- Kept-leaf closed form: the inner kept term `∑ i, b i * (∑ j, A i j *
convAt t₂ coef leaf j)` collapses to `t₂.bSeries (node [leaf])`.
This is the smallest instance where the RHS mentions `t₂` only through
`t₂.bSeries` applied to a subtree built from leaves. -/
theorem ButcherProduct.bWeighted_convAt_kept_leaf_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) :
    (∑ i : Fin t, t₂.b i *
        (∑ j : Fin t, t₂.A i j *
          ButcherProduct.convAt t₂ coef BTree.leaf j))
      = t₂.bSeries (BTree.node [BTree.leaf]) := by
  simp [ButcherTableau.bSeries, ButcherTableau.elementaryWeight_singleton,
        ButcherProduct.convAt_leaf]

/-- Helper: the elementary weight of a node whose children are `n` leaves
collapses to the `n`-th power of the row sum `∑ k, A i k`. -/
private theorem elementaryWeight_node_replicate_leaf
    {s : ℕ} (tab : ButcherTableau s) (n : ℕ) (i : Fin s) :
    tab.elementaryWeight (BTree.node (List.replicate n BTree.leaf)) i
      = (∑ k : Fin s, tab.A i k) ^ n := by
  induction n with
  | zero =>
    show tab.elementaryWeight (BTree.node []) i = _
    simp [ButcherTableau.elementaryWeight]
  | succ m ih =>
    rw [List.replicate_succ]
    have hfold :
        tab.elementaryWeight
            (BTree.node (BTree.leaf :: List.replicate m BTree.leaf)) i
          = tab.elementaryWeight (BTree.node (List.replicate m BTree.leaf)) i *
              (∑ k : Fin s, tab.A i k) := by
      simp [ButcherTableau.elementaryWeight, List.foldr]
    rw [hfold, ih, pow_succ]

/-- All-leaves trunk/cut closed form: when every child of the root is a
leaf, the b-weighted right block at `BTree.node children` decomposes
into a sum over cut subsets `S`, where each summand multiplies the cut
term `(∏ p ∈ S, coef BTree.leaf)` by the `bSeries` of a node of the
remaining leaves. The RHS mentions `t₂` only through `t₂.bSeries`
applied to leaf-only subtrees. -/
theorem ButcherProduct.bWeighted_convAt_node_all_leaves_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree)
    (hAll : ∀ c ∈ children, c = BTree.leaf) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Fin children.length)).powerset,
          (∏ _p ∈ S, coef BTree.leaf) *
          t₂.bSeries
            (BTree.node
              (List.replicate (children.length - S.card) BTree.leaf)) := by
  classical
  have hLHS :
      (∑ i : Fin t, t₂.b i *
          ButcherProduct.convAt t₂ coef (BTree.node children) i)
        = ∑ i : Fin t, t₂.b i *
            ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ButcherProduct.rightAuxAtCoef_eq_convAt]
  rw [hLHS,
      ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq
        t₂ t₂ coef children hAll]
  refine Finset.sum_congr rfl ?_
  intro S _
  congr 1
  -- Goal: ∑ i, t₂.b i * ∏ _p ∈ Sᶜ, ∑ j, t₂.A i j
  --     = t₂.bSeries (node (replicate (children.length - S.card) leaf))
  have hcard : (Sᶜ : Finset (Fin children.length)).card
      = children.length - S.card := by
    rw [Finset.card_compl]
    simp [Fintype.card_fin]
  have hbSeries :
      t₂.bSeries
          (BTree.node
            (List.replicate (children.length - S.card) BTree.leaf))
        = ∑ i : Fin t, t₂.b i *
            (∑ j : Fin t, t₂.A i j) ^ (children.length - S.card) := by
    unfold ButcherTableau.bSeries
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [elementaryWeight_node_replicate_leaf]
  rw [hbSeries]
  refine Finset.sum_congr rfl ?_
  intro i _
  congr 1
  rw [Finset.prod_const, hcard]

/-- Mixed kept-children closed form at the `convAt` level: in the
trunk-recursion expansion, cut children contribute `coef`, kept leaf
children contribute the row sum of `A`, and kept node children stay in the
recursive `convAt` form. This is the `convAt` analogue of
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_eq` with the
node case left in the closed recursive auxiliary instead of re-expanding the
inner powerset. -/
theorem ButcherProduct.bWeighted_convAt_node_kept_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ p ∈ S, coef (children.get p)) *
            (∑ i : Fin t, t₂.b i *
              ∏ p ∈ Sᶜ,
                (match children.get p with
                 | BTree.leaf => ∑ j : Fin t, t₂.A i j
                 | BTree.node gc =>
                     ∑ j : Fin t, t₂.A i j *
                       ButcherProduct.convAt t₂ coef (BTree.node gc) j)) := by
  classical
  have hLHS :
      (∑ i : Fin t, t₂.b i *
          ButcherProduct.convAt t₂ coef (BTree.node children) i)
        = ∑ i : Fin t, t₂.b i *
            ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ButcherProduct.rightAuxAtCoef_eq_convAt]
  rw [hLHS, ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion,
      Finset.powerset_univ]
  refine Finset.sum_congr rfl ?_
  intro S _
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  congr 1
  refine Finset.prod_congr rfl ?_
  intro p _
  generalize children.get p = c
  cases c with
  | leaf =>
    simp [ButcherProduct.rightAuxAtCoef_leaf]
  | node gc =>
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ButcherProduct.rightAuxAtCoef_eq_convAt]

/-- bSeries-form specialization of
`ButcherProduct.bWeighted_convAt_node_kept_eq`: the second-method
`b`-weighted stage sum of `ButcherProduct t₁ t₂` at a node is the mixed
kept-children trunk recursion with `coef := t₁.bSeries`. -/
theorem ButcherProduct.bSeries_natAdd_node_kept_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        (ButcherProduct t₁ t₂).elementaryWeight
          (BTree.node children) (Fin.natAdd s i))
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ p ∈ S, t₁.bSeries (children.get p)) *
            (∑ i : Fin t, t₂.b i *
              ∏ p ∈ Sᶜ,
                (match children.get p with
                 | BTree.leaf => ∑ j : Fin t, t₂.A i j
                 | BTree.node gc =>
                     ∑ j : Fin t, t₂.A i j *
                       ButcherProduct.convAt t₂ (t₁.bSeries)
                         (BTree.node gc) j)) := by
  rw [ButcherProduct.bSeries_natAdd_eq_convAt,
      ButcherProduct.bWeighted_convAt_node_kept_eq]

/-- All-leaves-grandchildren kept-node summand collapse: after choosing a
cut subset among the grandchildren of a kept node, the remaining product of
row sums is exactly the elementary-weight contribution to the `bSeries` of a
singleton parent over a leaf-only node. This is the depth-2 analogue of the
cycle 538 all-leaves collapse, restricted to one summand so it can be reused
inside future mixed-child convolution formulas. -/
theorem ButcherProduct.bWeighted_kept_node_all_leaves_summand_eq
    {t n : ℕ} (t₂ : ButcherTableau t) (S : Finset (Fin n)) :
    (∑ i : Fin t, t₂.b i *
        (∑ j : Fin t, t₂.A i j *
          ∏ _p ∈ Sᶜ, ∑ k : Fin t, t₂.A j k))
      = t₂.bSeries
          (BTree.node
            [BTree.node (List.replicate (n - S.card) BTree.leaf)]) := by
  classical
  have hcard : (Sᶜ : Finset (Fin n)).card = n - S.card := by
    rw [Finset.card_compl]
    simp [Fintype.card_fin]
  have hbSeries :
      t₂.bSeries
          (BTree.node
            [BTree.node (List.replicate (n - S.card) BTree.leaf)])
        = ∑ i : Fin t, t₂.b i *
            (∑ j : Fin t, t₂.A i j *
              (∑ k : Fin t, t₂.A j k) ^ (n - S.card)) := by
    unfold ButcherTableau.bSeries
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ButcherTableau.elementaryWeight_singleton]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [elementaryWeight_node_replicate_leaf]
  rw [hbSeries]
  refine Finset.sum_congr rfl ?_
  intro i _
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j _
  congr 1
  rw [Finset.prod_const, hcard]

/-! ### §384 first fully bSeries-only product closed form

Cycle 540: assemble the kept-leaf and singleton-node closed forms into the
first bSeries-only closed form for the product `bSeries` on a non-leaf
tree, namely the second-order rooted tree `BTree.node [BTree.leaf]`.
The right-hand side mentions `t₁` only through `t₁.bSeries` values and
mentions `t₂` only through `t₂.bSeries` values and `t₂.weightsSum`. -/

/-- §384 honest convolution closed form on the second-order rooted tree
`BTree.node [BTree.leaf]`: the bSeries-side convolution `bConv` evaluated
at this tree decomposes into three bSeries-only summands. The cut-side
contribution is `t₂.weightsSum * t₁.bSeries BTree.leaf`, and the kept-side
inner term collapses (via `bWeighted_convAt_kept_leaf_eq`) to
`t₂.bSeries (BTree.node [BTree.leaf])`. -/
theorem ButcherProduct.bConv_singleton_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    ButcherProduct.bConv (t₁.bSeries) t₂ (BTree.node [BTree.leaf])
      = t₁.bSeries (BTree.node [BTree.leaf])
        + t₂.bSeries (BTree.node [BTree.leaf])
        + t₂.weightsSum * t₁.bSeries BTree.leaf := by
  unfold ButcherProduct.bConv
  rw [ButcherProduct.bWeighted_convAt_singleton_node_eq t₂ t₁.bSeries BTree.leaf,
      ButcherProduct.bWeighted_convAt_kept_leaf_eq t₂ t₁.bSeries]
  ring

/-- Headline §384 corollary: the product `bSeries` on the second-order
rooted tree `BTree.node [BTree.leaf]` decomposes into a sum of three
bSeries-only summands. This is the first §384 closed-form result that
mentions both `t₁` and `t₂` only through `bSeries` and `weightsSum`. -/
theorem ButcherProduct.bSeries_singleton_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    (ButcherProduct t₁ t₂).bSeries (BTree.node [BTree.leaf])
      = t₁.bSeries (BTree.node [BTree.leaf])
        + t₂.bSeries (BTree.node [BTree.leaf])
        + t₂.weightsSum * t₁.bSeries BTree.leaf := by
  rw [ButcherProduct.bSeries_eq_bConv,
      ButcherProduct.bConv_singleton_leaf_eq]

end ButcherTableau
