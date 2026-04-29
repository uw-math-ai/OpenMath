import OpenMath.Chapter3.Section310
import OpenMath.Chapter3.Section312

/-!
# Butcher §380 — Φ-equivalence and P-reducibility of Runge–Kutta methods

This file formalises two definitions from Butcher's §380 ("Motivation"
of Section 38, *Numerical Methods for Ordinary Differential Equations*,
3rd ed.):

* **Definition 381B** (page 302) — *Φ-equivalent* Runge–Kutta methods.
* **Definition 381D** (page 303) — *P-reducible* Runge–Kutta methods
  and the *P-reduced method*.

## Definition 381B textbook statement (quoted verbatim from `def_381B.json`)

> Two Runge–Kutta methods are 'Φ-equivalent' if, for any `t ∈ T`, the
> elementary weight `Φ(t)` corresponding to the first method is equal
> to `Φ(t)` corresponding to the second method.

The surrounding text (page 302) introduces this notion alongside the
concept of *reducibility*, where one Runge–Kutta method is replaced by
another with **fewer stages**. The Lean signature must therefore allow
the two methods to have *different* stage counts; we parametrise
separately by `s` and `s'`.

## Definition 381D textbook statement (quoted verbatim from `def_381D.json`)

> A Runge–Kutta method `(A, b, c)` is `P`-reducible' if the stage
> index set can be partitioned into `{1, 2, …, s} = P₁ ∪ P₂ ∪ ⋯ ∪ P_ŝ`
> and if, for all `I, J = 1, 2, …, ŝ`, `Σ_{j ∈ P_J} a_{ij}` is
> constant for all `i ∈ P_I`. The method `(Â, b̂, ĉ)`, with `ŝ`
> stages, where `â_{IJ} = Σ_{j ∈ P_J} a_{ij}` for `i ∈ P_I`,
> `b̂_I = Σ_{i ∈ P_I} b_i` and `ĉ_I = c_i` for `i ∈ P_I`, is known as
> the *P-reduced method*.

## Faithfulness notes

* Definition 381B's "for any `t ∈ T`, `Φ(t)` agrees" is captured
  verbatim by `∀ t : RootedTree, M.elementaryWeight t = M'.elementaryWeight t`.
* Definition 381D's partition `{1, …, s} = P₁ ∪ ⋯ ∪ P_ŝ` is encoded
  as a block-index function `block : Fin s → Fin ŝ` together with
  surjectivity (every block is non-empty). This is an *equivalent*
  reformulation: a partition of a finite set into ŝ non-empty blocks
  is exactly a surjection onto `Fin ŝ`. No mathematical content is
  smuggled.
* The "non-trivial" partition condition (Butcher writes `ŝ` blocks
  without elaboration, but a partition into `s` singleton blocks is
  trivially row-sum-constant for any tableau) is captured by the
  side condition `ŝ < s` in `IsPReducible`.
* Butcher's "ĉ_I = c_i for i ∈ P_I" requires that `c` be constant on
  each block. This is **not** implied by the row-sum-constancy
  condition `Σ_{j ∈ P_J} a_{ij}` alone; under the consistency
  assumption `c_i = Σ_j a_{ij}` (which is *not* part of def:381D)
  block-constancy of `c` would follow. We therefore define `ĉ_I` by
  picking a representative `i ∈ P_I` (via `Classical.choose`); the
  full Butcher claim is recovered when the original tableau is
  consistent. This divergence is documented on `pReduced` and is a
  weakening, not a strengthening, of the textbook hypotheses.
-/

namespace OpenMath.Chapter3.Section381

open OpenMath.Chapter3.Section310 OpenMath.Chapter3.Section312

/-- Butcher §380 Definition 381B — two Runge–Kutta methods are
**Φ-equivalent** if their elementary weights agree on every rooted tree.

The methods are allowed to have different stage counts (`s` and `s'`),
matching Butcher's surrounding discussion of reducibility (where one
method is replaced by another with fewer stages). -/
def PhiEquivalent {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') :
    Prop :=
  ∀ t : RootedTree, M.elementaryWeight t = M'.elementaryWeight t

/-- Φ-equivalence is reflexive. -/
theorem PhiEquivalent.refl {s : ℕ} (M : RKTableau s) :
    PhiEquivalent M M := fun _ => rfl

/-- Φ-equivalence is symmetric (in the cross-stage-count sense). -/
theorem PhiEquivalent.symm {s s' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'}
    (h : PhiEquivalent M M') : PhiEquivalent M' M :=
  fun t => (h t).symm

/-- Φ-equivalence is transitive (in the cross-stage-count sense). -/
theorem PhiEquivalent.trans {s s' s'' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'} {M'' : RKTableau s''}
    (h₁ : PhiEquivalent M M') (h₂ : PhiEquivalent M' M'') :
    PhiEquivalent M M'' :=
  fun t => (h₁ t).trans (h₂ t)

/- ### Sanity witness — non-reflexive Φ-equivalence

The 2-stage tableau `paddedEuler` performs the same computation as
`explicitEuler` (its second stage carries `b 1 = 0` and `A 1 j = 0`).
We verify the elementary weights agree on the single-vertex tree;
this confirms the definition is non-vacuous on a concrete pair of
distinct tableaux. -/

/-- Two-stage padded version of explicit Euler: stage 2 contributes
nothing (`b 1 = 0`, row `A 1` is zero), so it computes the same result
as `RKTableau.explicitEuler`. -/
def paddedEuler : RKTableau 2 where
  A := 0
  b := ![1, 0]
  c := 0

example :
    RKTableau.explicitEuler.elementaryWeight RootedTree.vertex
      = paddedEuler.elementaryWeight RootedTree.vertex := by
  show (∑ i : Fin 1, RKTableau.explicitEuler.b i *
          RKTableau.explicitEuler.derivativeWeight i RootedTree.vertex)
      = ∑ i : Fin 2, paddedEuler.b i *
          paddedEuler.derivativeWeight i RootedTree.vertex
  simp [RKTableau.explicitEuler, paddedEuler,
        RKTableau.derivativeWeight_vertex, Fin.sum_univ_two]

/- ### Definition 381D — P-reducible Runge–Kutta methods -/

/-- A *P-partition* of an `s`-stage Runge–Kutta method into `ŝ` blocks.

The block-index function `block` records, for each stage `i : Fin s`,
the block `block i : Fin sBar` containing it. Surjectivity ensures
every block is non-empty (so the partition is genuine in Butcher's
sense — every `P_I` is inhabited). -/
structure PPartition (s sBar : ℕ) where
  /-- The block-index function: `block i` is the block containing
  stage `i`. -/
  block : Fin s → Fin sBar
  /-- Every block is non-empty. -/
  surj  : Function.Surjective block

end OpenMath.Chapter3.Section381

namespace OpenMath.Chapter3.Section312.RKTableau

open OpenMath.Chapter3.Section381

/-- The row-sum-constancy condition (Definition 381D, first sentence):
for all blocks `I, J : Fin ŝ`, the sum `Σ_{j ∈ P_J} a_{ij}` is constant
as `i` ranges over `P_I`. -/
def IsPReducibleVia {s sBar : ℕ}
    (M : RKTableau s) (P : PPartition s sBar) : Prop :=
  ∀ (I J : Fin sBar) (i i' : Fin s),
    P.block i = I → P.block i' = I →
      (∑ j ∈ Finset.univ.filter (fun j => P.block j = J), M.A i j) =
      (∑ j ∈ Finset.univ.filter (fun j => P.block j = J), M.A i' j)

/-- Butcher §380 Definition 381D — a Runge–Kutta method is
*P-reducible* if there exists a *non-trivial* P-partition (`ŝ < s`)
witnessing the row-sum-constancy condition. The non-triviality
condition `ŝ < s` rules out the discrete partition (each stage in its
own block), which is vacuously row-sum-constant for any tableau. -/
def IsPReducible {s : ℕ} (M : RKTableau s) : Prop :=
  ∃ (sBar : ℕ) (_ : sBar < s) (P : PPartition s sBar),
    M.IsPReducibleVia P

/-- The *P-reduced method* obtained from a P-partition `P`.

The new coefficient `â_{IJ}` is defined by picking *some*
representative `i ∈ P_I` (via `Classical.choose (P.surj I)`) and
summing `a_{ij}` over `j ∈ P_J`. Under the hypothesis
`IsPReducibleVia M P`, this value is independent of the choice of
representative — see `pReduced_A_apply`.

The new weight `b̂_I = Σ_{i ∈ P_I} b_i` follows Butcher's formula
verbatim.

The new abscissa `ĉ_I` is defined here as `c i` for the chosen
representative `i := Classical.choose (P.surj I)`. Butcher's textbook
formulation "`ĉ_I = c_i` for `i ∈ P_I`" requires `c` to be constant
on each block, which is **not** implied by `IsPReducibleVia` alone
(it follows from the consistency condition `c_i = Σ_j a_{ij}`, but
that is not part of def:381D). The representative-based definition
is faithful to Butcher's intent under the consistency assumption and
is unambiguous in general; we do not silently strengthen
`IsPReducibleVia` to include `c`-constancy. -/
noncomputable def pReduced {s sBar : ℕ}
    (M : RKTableau s) (P : PPartition s sBar) : RKTableau sBar where
  A I J := ∑ j ∈ Finset.univ.filter (fun j => P.block j = J),
            M.A (Classical.choose (P.surj I)) j
  b I := ∑ i ∈ Finset.univ.filter (fun i => P.block i = I), M.b i
  c I := M.c (Classical.choose (P.surj I))

/-- The new coefficient `â_{IJ}` is independent of the choice of
representative `i ∈ P_I` under `IsPReducibleVia`. This is the
well-definedness lemma for `pReduced`'s `A` field. -/
theorem pReduced_A_apply {s sBar : ℕ}
    (M : RKTableau s) {P : PPartition s sBar}
    (h : M.IsPReducibleVia P) (I J : Fin sBar) (i : Fin s)
    (hi : P.block i = I) :
    (M.pReduced P).A I J =
      ∑ j ∈ Finset.univ.filter (fun j => P.block j = J), M.A i j := by
  have hRep : P.block (Classical.choose (P.surj I)) = I :=
    Classical.choose_spec (P.surj I)
  exact h I J (Classical.choose (P.surj I)) i hRep hi

/-- Unfolding lemma for the `b` field of the P-reduced method. -/
theorem pReduced_b_apply {s sBar : ℕ}
    (M : RKTableau s) (P : PPartition s sBar) (I : Fin sBar) :
    (M.pReduced P).b I =
      ∑ i ∈ Finset.univ.filter (fun i => P.block i = I), M.b i :=
  rfl

/-- Unfolding lemma for the `c` field of the P-reduced method. The
representative is `Classical.choose (P.surj I)`; see the `pReduced`
docstring for why this is a faithful encoding of Butcher's formula. -/
theorem pReduced_c_apply {s sBar : ℕ}
    (M : RKTableau s) (P : PPartition s sBar) (I : Fin sBar) :
    (M.pReduced P).c I = M.c (Classical.choose (P.surj I)) :=
  rfl

end OpenMath.Chapter3.Section312.RKTableau

namespace OpenMath.Chapter3.Section381

open OpenMath.Chapter3.Section310 OpenMath.Chapter3.Section312

/- ### Non-vacuous witness for P-reducibility

The 2-stage `paddedEuler` tableau has `A = 0`, so the row-sum
condition `Σ_{j ∈ P_J} a_{ij}` is identically `0` for any partition.
We exhibit the trivial 2-into-1 partition merging both stages into
block `0` and verify it is a P-partition witnessing P-reducibility. -/

/-- The trivial 2-stage-into-1-block partition. -/
def pairPartition : PPartition 2 1 where
  block := fun _ => 0
  surj  := fun _ => ⟨0, Subsingleton.elim _ _⟩

/-- `paddedEuler` is P-reducible-via the trivial partition: the
row-sum-constancy condition holds because every entry of
`paddedEuler.A` is zero. -/
example : paddedEuler.IsPReducibleVia pairPartition := by
  intro _ _ _ _ _ _
  simp [paddedEuler]

/-- Hence `paddedEuler` is P-reducible. -/
example : paddedEuler.IsPReducible :=
  ⟨1, by decide, pairPartition, by
    intro _ _ _ _ _ _
    simp [paddedEuler]⟩

end OpenMath.Chapter3.Section381
