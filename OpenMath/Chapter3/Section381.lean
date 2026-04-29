import OpenMath.Chapter3.Section310
import OpenMath.Chapter3.Section312

/-!
# Butcher §380 — Φ-equivalence and reducibility of Runge–Kutta methods

This file formalises three definitions from Butcher's §380 ("Motivation"
of Section 38, *Numerical Methods for Ordinary Differential Equations*,
3rd ed.):

* **Definition 381B** (page 302) — *Φ-equivalent* Runge–Kutta methods.
* **Definition 381C** (page 303) — *0-reducible* Runge–Kutta methods
  and the *0-reduced method*.
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

## Definition 381C textbook statement (quoted verbatim from `def_381C.json`)

> A Runge–Kutta method `(A, b, c)` is `0-reducible' if the stage index
> set can be partitioned into two subsets `{1, 2, …, s} = P₀ ∪ P₁`
> such that `bᵢ = 0` for all `i ∈ P₀` and such that `aᵢⱼ = 0` if
> `i ∈ P₁` and `j ∈ P₀`. The method formed by deleting all stages
> indexed by members of `P₀` is known as the `0-reduced method'.

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
* Definition 381C's two-block partition `{1, …, s} = P₀ ∪ P₁` is
  encoded as a Boolean predicate `inP1 : Fin s → Bool`. We set
  `P₀ = {i | inP1 i = false}` and `P₁ = {i | inP1 i = true}`. A
  Boolean predicate is equivalent to a partition of `Fin s` into two
  sets, with `decide` available as a bonus for the witness. The
  non-emptiness side condition `(∃ i, inP1 i = false)` in
  `IsZeroReducible` rules out the trivially-no-reduction case
  `P₀ = ∅`; without it, every tableau is vacuously 0-reducible via
  the all-`P₁` partition. This mirrors the `ŝ < s` strengthening on
  `IsPReducible`. Requiring also `P₁ ≠ ∅` would over-strengthen and
  exclude the legitimate "delete all stages" reduction (which yields
  the unique 0-stage tableau).
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

/- ### Definition 381C — 0-reducible Runge–Kutta methods -/

/-- Predicate form of Butcher §380 Definition 381C: the 2-block
partition `P₀ := {i | ¬ inP1 i}`, `P₁ := {i | inP1 i}` witnesses
0-reducibility of `M` when

* `b i = 0` for every `i ∈ P₀`, and
* `A i j = 0` whenever `i ∈ P₁` and `j ∈ P₀`. -/
def IsZeroReducibleVia {s : ℕ}
    (M : RKTableau s) (inP1 : Fin s → Bool) : Prop :=
  (∀ i : Fin s, inP1 i = false → M.b i = 0) ∧
  (∀ i j : Fin s, inP1 i = true → inP1 j = false → M.A i j = 0)

/-- Butcher §380 Definition 381C — a Runge–Kutta method is
*0-reducible* if there is a 2-block partition (encoded as a Boolean
predicate `inP1`) with **non-empty** `P₀` satisfying the two zero
conditions. The non-emptiness of `P₀` rules out the trivial
"all-stages-in-`P₁`" partition under which every tableau would
vacuously satisfy the zero conditions; this strengthening parallels
the `ŝ < s` side condition on `IsPReducible`. See the file docstring
for further discussion. -/
def IsZeroReducible {s : ℕ} (M : RKTableau s) : Prop :=
  ∃ inP1 : Fin s → Bool,
    (∃ i, inP1 i = false) ∧ M.IsZeroReducibleVia inP1

/-- Order embedding from `Fin (#P₁)` into `Fin s` whose image is
exactly `P₁ = {i | inP1 i = true}`. Used to re-index the surviving
stages after deleting `P₀`. -/
noncomputable def zeroReducedEmb {s : ℕ} (inP1 : Fin s → Bool) :
    Fin (Finset.univ.filter (fun i : Fin s => inP1 i = true)).card ↪o
      Fin s :=
  (Finset.univ.filter (fun i : Fin s => inP1 i = true)).orderEmbOfFin
    rfl

/-- The *0-reduced method* obtained by deleting all `P₀`-indexed
stages (Butcher §380 Definition 381C, second sentence).

The new stage index set is `Fin (#P₁)`, and the canonical order
embedding `zeroReducedEmb inP1` identifies each new stage with a
specific old stage in `P₁`. The new `A`, `b`, `c` are the obvious
restrictions; no `Classical.choose` is needed because the embedding
makes each new index correspond to a unique old index (contrast with
`pReduced`'s representative-based `A` and `c`). -/
noncomputable def zeroReduced {s : ℕ}
    (M : RKTableau s) (inP1 : Fin s → Bool) :
    RKTableau (Finset.univ.filter (fun i : Fin s => inP1 i = true)).card
    where
  A I J := M.A (zeroReducedEmb inP1 I) (zeroReducedEmb inP1 J)
  b I := M.b (zeroReducedEmb inP1 I)
  c I := M.c (zeroReducedEmb inP1 I)

/-- Unfolding lemma for the `A` field of the 0-reduced method. -/
theorem zeroReduced_A_apply {s : ℕ} (M : RKTableau s)
    (inP1 : Fin s → Bool)
    (I J : Fin (Finset.univ.filter
        (fun i : Fin s => inP1 i = true)).card) :
    (M.zeroReduced inP1).A I J =
      M.A (zeroReducedEmb inP1 I) (zeroReducedEmb inP1 J) :=
  rfl

/-- Unfolding lemma for the `b` field of the 0-reduced method. -/
theorem zeroReduced_b_apply {s : ℕ} (M : RKTableau s)
    (inP1 : Fin s → Bool)
    (I : Fin (Finset.univ.filter
        (fun i : Fin s => inP1 i = true)).card) :
    (M.zeroReduced inP1).b I = M.b (zeroReducedEmb inP1 I) :=
  rfl

/-- Unfolding lemma for the `c` field of the 0-reduced method. -/
theorem zeroReduced_c_apply {s : ℕ} (M : RKTableau s)
    (inP1 : Fin s → Bool)
    (I : Fin (Finset.univ.filter
        (fun i : Fin s => inP1 i = true)).card) :
    (M.zeroReduced inP1).c I = M.c (zeroReducedEmb inP1 I) :=
  rfl

/- ### Definition 381D — P-reducible Runge–Kutta methods -/

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

/- ### Definition 381E — irreducible Runge–Kutta methods -/

/-- Butcher §380 Definition 381E (first sentence) — a Runge–Kutta method
is *irreducible* if it is neither 0-reducible (`def:381C`) nor
P-reducible (`def:381D`).

This is the literal Boolean composite of the two negations, faithful to
Butcher §380 page 303. The second sentence of def:381E (the construction
of the "reduced method") is deferred — see
`.prover-state/issues/reduced_method_deferred.md`. -/
def IsIrreducible {s : ℕ} (M : RKTableau s) : Prop :=
  ¬ M.IsZeroReducible ∧ ¬ M.IsPReducible

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

/- ### Non-vacuous witness for 0-reducibility

The 2-stage `paddedEuler` tableau has `b = ![1, 0]` and `A = 0`. The
partition `inP1 := ![true, false]` (so `P₁ = {0}` and `P₀ = {1}`)
witnesses 0-reducibility:

* `b 1 = 0` ✔ (the only `P₀`-indexed stage is `1`).
* `A i j = 0` for `i ∈ P₁, j ∈ P₀` ✔ (vacuously, since `A = 0`).
* `P₀ ≠ ∅` ✔ (stage `1` lies in `P₀`). -/

/-- `paddedEuler` is 0-reducible-via the partition `![true, false]`
(i.e. `P₁ = {0}`, `P₀ = {1}`). -/
example : paddedEuler.IsZeroReducibleVia ![true, false] := by
  refine ⟨?_, ?_⟩
  · intro i hi
    fin_cases i <;> simp_all [paddedEuler]
  · intro i j hi hj
    simp [paddedEuler]

/-- Hence `paddedEuler` is 0-reducible. -/
example : paddedEuler.IsZeroReducible :=
  ⟨![true, false], ⟨1, by decide⟩, by
    refine ⟨?_, ?_⟩
    · intro i hi
      fin_cases i <;> simp_all [paddedEuler]
    · intro i j hi hj
      simp [paddedEuler]⟩

/- ### Non-vacuous witness for irreducibility

The 1-stage `RKTableau.explicitEuler` tableau is irreducible:

* It is not 0-reducible: any 2-block partition `inP1 : Fin 1 → Bool`
  with `(∃ i, inP1 i = false)` forces `inP1 0 = false`, giving
  `b 0 = 0`. But `explicitEuler.b 0 = 1`.
* It is not P-reducible: a non-trivial P-partition would require
  `sBar < 1`, hence `sBar = 0`, but then `P.block 0 : Fin 0` is
  uninhabited. -/

/-- `RKTableau.explicitEuler` is irreducible (def:381E). -/
theorem explicitEuler_isIrreducible :
    RKTableau.explicitEuler.IsIrreducible := by
  refine ⟨?_, ?_⟩
  · rintro ⟨inP1, ⟨i, hi⟩, hbZero, _⟩
    fin_cases i
    exact one_ne_zero (hbZero 0 hi)
  · rintro ⟨sBar, hLt, P, _⟩
    obtain rfl : sBar = 0 := Nat.lt_one_iff.mp hLt
    exact (P.block 0).elim0

end OpenMath.Chapter3.Section381
