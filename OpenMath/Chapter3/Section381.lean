import OpenMath.Chapter3.Section310
import OpenMath.Chapter3.Section312
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Butcher §380 — equivalence and reducibility of Runge–Kutta methods

This file formalises four definitions from Butcher's §380 ("Motivation"
of Section 38, *Numerical Methods for Ordinary Differential Equations*,
3rd ed.):

* **Definition 381A** (page 302) — *equivalent* Runge–Kutta methods
  (semantic same-output equivalence on Lipschitz autonomous problems).
* **Definition 381B** (page 302) — *Φ-equivalent* Runge–Kutta methods.
* **Definition 381C** (page 303) — *0-reducible* Runge–Kutta methods
  and the *0-reduced method*.
* **Definition 381D** (page 303) — *P-reducible* Runge–Kutta methods
  and the *P-reduced method*.

## Definition 381A textbook statement (quoted verbatim from `def_381A.json`)

> Two Runge–Kutta methods are 'equivalent' if, for any initial value
> problem defined by an autonomous function `f` satisfying a Lipschitz
> condition, and an initial value `y₀`, there exists `h₀ > 0` such that
> the result computed by the first method is identical with the result
> computed by the second method, if `h ≤ h₀`.

The encoding splits this into two definitions:
* `IsRKOneStep M f y₀ h y₁` — *predicate* form of "method `M` produces
  output `y₁` after one step of size `h`". Encoded as a `Prop` so that
  implicit methods (whose stage equations may have zero, one, or
  multiple solutions depending on `h`) are handled honestly: any tuple
  `(Y, y₁)` satisfying the implicit stage system is a valid output.
* `Equivalent M M'` — Butcher's def:381A — for every Lipschitz
  autonomous problem and initial value, there exists `h₀ > 0` below
  which *every* output of `M` agrees with *every* output of `M'`.

The semantic equivalence of def:381A is **strictly weaker** than
Φ-equivalence (def:381B): it allows the methods to differ on
non-Lipschitz or implicitly ill-defined problems. Butcher's
`thm:381H` later proves the two notions agree modulo passing to the
reduced method; that is a *theorem*, not a definition. We therefore
must NOT define `Equivalent` as `PhiEquivalent`.

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
open scoped NNReal

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

/- ### Definition 381F — P-equivalent Runge–Kutta methods

Butcher §380 Definition 381F (page 303), quoted verbatim from
`def_381F.json`:

> Two Runge–Kutta methods are 'P-equivalent' if each of them reduces
> to the same reduced method.

The textbook's *reduced method* (def:381E, page 303) is "P-reduce
then 0-reduce", iterated until irreducible. The full iterated
"reduced method" infrastructure depends on a fixed-point construction
that is currently deferred (see
`.prover-state/issues/reduced_method_deferred.md`). The encoding
below captures the **P-only flavour** of the textbook definition:
two methods are P-equivalent if they share a common P-reduced form
reachable in zero or more P-reduction steps. The 0-reduction
strengthening will fold in cleanly once the reduced-method
construction lands — extending `PReducesTo` by a 0-reduction
constructor and re-using the same `∃ Mbar, ... ∧ ...` shape for
`PEquivalent`.

The P-only encoding is faithful to the P-side of the textbook
definition; methods that already differ only by 0-reduction (a
strictly weaker reduction) will require the 0-step extension. The
non-vacuity witness via `paddedEuler` exercises a non-trivial
P-reduction and confirms the predicate is satisfiable beyond
reflexivity. -/

/-- Reflexive-transitive closure of single-step P-reduction.

`PReducesTo M M'` holds when `M'` can be obtained from `M` by zero or
more P-reduction steps. Each step picks a P-partition `P` together
with a proof that `M.IsPReducibleVia P`, then replaces the current
method with the resulting P-reduced form `M.pReduced P`. The relation
is heterogeneous in the stage-count parameter: each non-trivial
P-reduction strictly decreases the stage count (`sBar < s`), but the
reflexivity case keeps it constant. -/
inductive PReducesTo : {s s' : ℕ} → RKTableau s → RKTableau s' → Prop where
  /-- Zero-step (reflexive) case: every method reduces to itself. -/
  | refl {s : ℕ} (M : RKTableau s) : PReducesTo M M
  /-- One P-reduction step: `M` is P-reducible via a non-trivial partition
  `P` (`sBar < s`), and the result `M.pReduced P` reduces further (in
  zero or more steps) to `M''`. The non-triviality `hLt` keeps this
  relation faithful to Butcher §380's textbook P-reduction, which
  strictly decreases the stage count; without it, the discrete
  partition (`sBar = s`, each stage in its own block) would
  vacuously satisfy `IsPReducibleVia` for every tableau and admit
  trivial "reductions" that do not reflect the textbook intent. -/
  | step {s sBar s'' : ℕ}
      {M : RKTableau s} {M'' : RKTableau s''}
      (P : PPartition s sBar) (_hLt : sBar < s)
      (_h : M.IsPReducibleVia P) :
      PReducesTo (M.pReduced P) M'' → PReducesTo M M''
  /-- One 0-reduction step: `M` is 0-reducible via `inP1` (with `P₀`
  non-empty), and the result `M.zeroReduced inP1` reduces further (in
  zero or more steps) to `M''`. The non-emptiness `hP0` keeps this
  faithful to Butcher §380 def:381C, which requires P₀ to contain at
  least one stage; without it, the trivial all-stages-in-P₁ partition
  would admit vacuous "0-reductions" that do not decrease the stage
  count. The two clauses of `IsZeroReducibleVia` (b vanishes on P₀ and
  A vanishes on P₁ × P₀) together with non-empty P₀ are exactly the
  textbook's def:381C hypotheses. -/
  | zeroStep {s s'' : ℕ}
      {M : RKTableau s} {M'' : RKTableau s''}
      (inP1 : Fin s → Bool) (_hP0 : ∃ i, inP1 i = false)
      (_h : M.IsZeroReducibleVia inP1) :
      PReducesTo (M.zeroReduced inP1) M'' → PReducesTo M M''

/-- Butcher §380 Definition 381F — two Runge–Kutta methods are
*P-equivalent* if each of them P-reduces (in zero or more steps) to a
common reduced form. See the comment block above for the relationship
to the full textbook "reduced method" of def:381E. -/
def PEquivalent {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') : Prop :=
  ∃ (sBar : ℕ) (Mbar : RKTableau sBar),
    PReducesTo M Mbar ∧ PReducesTo M' Mbar

/-- P-equivalence is reflexive. -/
theorem PEquivalent.refl {s : ℕ} (M : RKTableau s) : PEquivalent M M :=
  ⟨s, M, PReducesTo.refl M, PReducesTo.refl M⟩

/-- P-equivalence is symmetric (swap the two reduction witnesses). -/
theorem PEquivalent.symm {s s' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'} :
    PEquivalent M M' → PEquivalent M' M
  | ⟨sBar, Mbar, hM, hM'⟩ => ⟨sBar, Mbar, hM', hM⟩

/-- A method is P-equivalent to anything it P-reduces to. -/
theorem PEquivalent.of_pReducesTo {s s' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'} (h : PReducesTo M M') :
    PEquivalent M M' :=
  ⟨s', M', h, PReducesTo.refl M'⟩

/-- A method P-reduces (in one step) to its 0-reduction. Direct
corollary of the `zeroStep` constructor. The `refl` continuation
witnesses that no further reduction is required.

This is the `PReducesTo`-level analog of cycle 189's
`PEquivalent.of_isZeroReducibleVia` (below, which wraps this lemma
with `PEquivalent.of_pReducesTo`). Cycle 191 deliverable; reordered
in cycle 192 to precede its `PEquivalent`-level consumer. -/
theorem PReducesTo.of_isZeroReducibleVia {s : ℕ}
    (M : RKTableau s) {inP1 : Fin s → Bool}
    (hP0 : ∃ i, inP1 i = false)
    (h : M.IsZeroReducibleVia inP1) :
    PReducesTo M (M.zeroReduced inP1) :=
  PReducesTo.zeroStep inP1 hP0 h (PReducesTo.refl _)

/-- A method is P-equivalent to its 0-reduction. Direct corollary of
`PReducesTo.of_isZeroReducibleVia` combined with
`PEquivalent.of_pReducesTo`. -/
theorem PEquivalent.of_isZeroReducibleVia {s : ℕ}
    (M : RKTableau s) {inP1 : Fin s → Bool}
    (hP0 : ∃ i, inP1 i = false)
    (h : M.IsZeroReducibleVia inP1) :
    PEquivalent M (M.zeroReduced inP1) :=
  PEquivalent.of_pReducesTo (PReducesTo.of_isZeroReducibleVia M hP0 h)

/-- *Transitivity of `PReducesTo`.* Concatenation of two reduction
sequences. The constructors `step` / `zeroStep` each consume a tail
reduction, so this proof walks `h₁` and re-applies the same
constructor at every node, plugging `h₂` in at the previously-`refl`
endpoint.

Used together with `PReducesTo.of_isZeroReducibleVia` and
`PEquivalent.of_pReducesTo` to chain witnesses across mixed (P-step,
0-step) reduction sequences. Cycle 192 deliverable. -/
theorem PReducesTo.trans
    {s s' s'' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'} {M'' : RKTableau s''}
    (h₁ : PReducesTo M M') (h₂ : PReducesTo M' M'') :
    PReducesTo M M'' := by
  induction h₁ with
  | refl => exact h₂
  | step P hLt hVia _ ih => exact PReducesTo.step P hLt hVia (ih h₂)
  | zeroStep inP1 hP0 hVia _ ih =>
      exact PReducesTo.zeroStep inP1 hP0 hVia (ih h₂)

/-- If `M` is irreducible (def:381E — neither P-reducible nor 0-reducible),
then any reduction sequence starting from `M` is the reflexive (zero-step)
one. The `step` constructor would furnish `IsPReducible M`; the `zeroStep`
constructor would furnish `IsZeroReducible M`; both contradict
`IsIrreducible`.

This strengthens cycles 185–187's `eq_of_not_isPReducible_of_pReducesTo`
(which only needed `¬ IsPReducible`) to handle the `zeroStep` constructor
added in cycle 188. -/
theorem eq_of_isIrreducible_of_pReducesTo {s s' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'}
    (hIrr : M.IsIrreducible) (h : PReducesTo M M') :
    s' = s ∧ HEq M' M := by
  cases h with
  | refl => exact ⟨rfl, HEq.rfl⟩
  | step P hLt hVia _ => exact absurd ⟨_, hLt, P, hVia⟩ hIrr.2
  | zeroStep inP1 hP0 hVia _ => exact absurd ⟨inP1, hP0, hVia⟩ hIrr.1

/-- *Transitivity of P-equivalence over an irreducible middle method.*
If `M₂` is irreducible (def:381E), then `PEquivalent M₁ M₂` and
`PEquivalent M₂ M₃` together yield `PEquivalent M₁ M₃`.

The general `PEquivalent.trans` over arbitrary middle methods would
require confluence of P-reduction (any two reduction sequences from
a common source can be completed to a common target). When `M₂` is
irreducible, both reductions out of `M₂` are forced to be reflexive
(`eq_of_isIrreducible_of_pReducesTo`), so the witnesses
`PReducesTo M₁ M₂` and `PReducesTo M₃ M₂` extracted from the
hypotheses combine directly via the existing common reduct `M₂`.

Strengthens cycle 185's `trans_of_middle_not_pReducible` (which only
required `¬ IsPReducible`) to require full irreducibility — necessary
because cycle 188's `zeroStep` constructor admits 0-reductions out of
a non-P-reducible middle, so the original lemma's reflexive-only
conclusion no longer holds with only the weaker hypothesis. -/
theorem PEquivalent.trans_of_middle_isIrreducible {s₁ s₂ s₃ : ℕ}
    {M₁ : RKTableau s₁} {M₂ : RKTableau s₂} {M₃ : RKTableau s₃}
    (h₁₂ : PEquivalent M₁ M₂) (h₂₃ : PEquivalent M₂ M₃)
    (hIrr : M₂.IsIrreducible) :
    PEquivalent M₁ M₃ := by
  refine ⟨s₂, M₂, ?_, ?_⟩
  · obtain ⟨sA, MA, h1A, h2A⟩ := h₁₂
    obtain ⟨hsA, hMA⟩ := eq_of_isIrreducible_of_pReducesTo hIrr h2A
    subst hsA
    obtain rfl : MA = M₂ := eq_of_heq hMA
    exact h1A
  · obtain ⟨sB, MB, h2B, h3B⟩ := h₂₃
    obtain ⟨hsB, hMB⟩ := eq_of_isIrreducible_of_pReducesTo hIrr h2B
    subst hsB
    obtain rfl : MB = M₂ := eq_of_heq hMB
    exact h3B

/-- *Canonical-form constructor for P-equivalence through a common
irreducible middle.* If two methods `M`, `M'` both P-reduce to a common
intermediate `N`, they are P-equivalent (def:381F).

The `_hN : N.IsIrreducible` hypothesis is documentation-only: the
existential constructor of `PEquivalent` does not consume it. It is
included so that downstream callers signal the intended use case
(reducing to a normal form) at the source-code level by supplying an
`IsIrreducible` proof at the `_hN` slot. The proof would still go
through with a weaker (or no) hypothesis; the strength is a contract,
not a logical requirement. Cycle 190 deliverable A. -/
theorem PEquivalent.eq_of_isIrreducible_of_middle
    {s s' sBar : ℕ}
    {M : RKTableau s} {M' : RKTableau s'} {N : RKTableau sBar}
    (_hN : N.IsIrreducible)
    (h₁ : PReducesTo M N) (h₂ : PReducesTo M' N) :
    PEquivalent M M' :=
  ⟨sBar, N, h₁, h₂⟩

/-- *Canonical-form half of def:381E.* If two P-equivalent methods are
both `IsIrreducible`, they coincide up to heterogeneous-stage `HEq`.

Dual to `PEquivalent.eq_of_isIrreducible_of_middle` (cycle 190), which
handles the case where the existential common reduct is irreducible.
Here both endpoints are irreducible; the common reduct collapses to
each endpoint via `eq_of_isIrreducible_of_pReducesTo` (cycle 188),
forcing the two endpoints to share stage count and tableau data. -/
theorem PEquivalent.eq_of_both_isIrreducible
    {s s' : ℕ} {M : RKTableau s} {M' : RKTableau s'}
    (hM : M.IsIrreducible) (hM' : M'.IsIrreducible)
    (h : PEquivalent M M') :
    ∃ heq : s' = s, HEq M' M := by
  obtain ⟨_, _, h₁, h₂⟩ := h
  obtain ⟨h₁eq, h₁heq⟩ := eq_of_isIrreducible_of_pReducesTo hM h₁
  obtain ⟨h₂eq, h₂heq⟩ := eq_of_isIrreducible_of_pReducesTo hM' h₂
  subst h₁eq
  subst h₂eq
  exact ⟨rfl, h₂heq.symm.trans h₁heq⟩

/-- *Irreducible-endpoint extraction (left).* If `M.IsIrreducible` and
`PEquivalent M M'`, then `M'` reduces to `M`. The common reduct in the
`PEquivalent` existential is forced to coincide with `M` by
`eq_of_isIrreducible_of_pReducesTo` (cycle 188), so the second leg
`PReducesTo M' (commonReduct)` becomes `PReducesTo M' M` directly.

Load-bearing for downstream `def:381E reducedMethod` uniqueness work:
when an irreducible reduct exists, every P-equivalent method reduces
to it. -/
theorem PEquivalent.pReducesTo_of_left_isIrreducible
    {s s' : ℕ} {M : RKTableau s} {M' : RKTableau s'}
    (hIrr : M.IsIrreducible)
    (h : PEquivalent M M') :
    PReducesTo M' M := by
  obtain ⟨_, MMid, h₁, h₂⟩ := h
  obtain ⟨h_eq, h_heq⟩ := eq_of_isIrreducible_of_pReducesTo hIrr h₁
  subst h_eq
  obtain rfl : MMid = M := eq_of_heq h_heq
  exact h₂

/-- *Irreducible-endpoint extraction (right).* Symmetric companion of
`pReducesTo_of_left_isIrreducible`: if `M'.IsIrreducible` and
`PEquivalent M M'`, then `M` reduces to `M'`. One-line corollary via
`PEquivalent.symm`. -/
theorem PEquivalent.pReducesTo_of_right_isIrreducible
    {s s' : ℕ} {M : RKTableau s} {M' : RKTableau s'}
    (hIrr : M'.IsIrreducible)
    (h : PEquivalent M M') :
    PReducesTo M M' :=
  h.symm.pReducesTo_of_left_isIrreducible hIrr

/-- Homogeneous-stage corollary of `eq_of_both_isIrreducible`: when the
two irreducible P-equivalent methods have the same stage count, they
are literally equal. Drops the heterogeneous `HEq` packaging for caller
convenience when the stage type is known statically. -/
theorem PEquivalent.eq_of_both_isIrreducible_homogeneous
    {s : ℕ} {M M' : RKTableau s}
    (hM : M.IsIrreducible) (hM' : M'.IsIrreducible)
    (h : PEquivalent M M') :
    M = M' := by
  obtain ⟨_, h_heq⟩ := h.eq_of_both_isIrreducible hM hM'
  exact (eq_of_heq h_heq).symm

/-- *Cardinality helper for 0-reduction.* When the partition predicate
`inP1` admits at least one `false` element, the surviving stage set
`P₁ = {i | inP1 i = true}` is a proper subset of the universe and so
its cardinality is strictly less than `s`. Shared between
`PReducesTo.size_le`'s `zeroStep` case and
`PReducesTo.size_lt_of_zeroStep`. -/
private theorem card_filter_true_lt_of_exists_false {s : ℕ}
    {inP1 : Fin s → Bool} (hP0 : ∃ i, inP1 i = false) :
    (Finset.univ.filter (fun i : Fin s => inP1 i = true)).card < s := by
  have hSubset :
      (Finset.univ.filter (fun i : Fin s => inP1 i = true)) ⊂
        (Finset.univ : Finset (Fin s)) := by
    rw [Finset.filter_ssubset]
    obtain ⟨i, hi⟩ := hP0
    exact ⟨i, Finset.mem_univ i, by simp [hi]⟩
  have hCard := Finset.card_lt_card hSubset
  simpa [Finset.card_univ, Fintype.card_fin] using hCard

/-- *Stage-count monotonicity for `PReducesTo`.* Every P-reduction
sequence is non-increasing on the underlying stage-count parameter.
The `refl` case preserves it; the `step` and `zeroStep` cases strictly
decrease it (see `PReducesTo.size_lt_of_step` and
`PReducesTo.size_lt_of_zeroStep`).

Prerequisite for the def:381E `reducedMethod` construction (issue
`reduced_method_deferred.md`): together with the strict-descent
siblings, this is the structural infrastructure required to establish
well-foundedness of `PReducesTo` on a Σ-typed wrapper. -/
theorem PReducesTo.size_le {s s' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'}
    (h : PReducesTo M M') : s' ≤ s := by
  induction h with
  | refl _ => exact le_refl _
  | step _ hLt _ _ ih => exact ih.trans hLt.le
  | zeroStep inP1 hP0 _ _ ih =>
      exact ih.trans (card_filter_true_lt_of_exists_false hP0).le

/-- *Strict stage-count descent via a P-reduction step.* A single
non-trivial P-reduction step (`step` constructor of `PReducesTo`,
parameterised by a partition `P` with `sBar < s`) strictly decreases
the stage count. Direct consequence of the constructor's `sBar < s`
hypothesis composed with `size_le` on the continuation. -/
theorem PReducesTo.size_lt_of_step {s sBar s'' : ℕ}
    {M : RKTableau s} {M'' : RKTableau s''}
    (P : PPartition s sBar) (hLt : sBar < s)
    (_hRed : M.IsPReducibleVia P)
    (hRest : PReducesTo (M.pReduced P) M'') :
    s'' < s :=
  lt_of_le_of_lt hRest.size_le hLt

/-- *Strict stage-count descent via a 0-reduction step.* A single
0-reduction step (`zeroStep` constructor of `PReducesTo`, requiring
`hP0 : ∃ i, inP1 i = false`) strictly decreases the stage count,
because the existence of an `inP1 i = false` witness forces
`|P₁| < s`. -/
theorem PReducesTo.size_lt_of_zeroStep {s s'' : ℕ}
    {M : RKTableau s} {M'' : RKTableau s''}
    (inP1 : Fin s → Bool) (hP0 : ∃ i, inP1 i = false)
    (_h : M.IsZeroReducibleVia inP1)
    (hRest : PReducesTo (M.zeroReduced inP1) M'') :
    s'' < s :=
  lt_of_le_of_lt hRest.size_le (card_filter_true_lt_of_exists_false hP0)

/-- *P-reduction witness extractor — reduced stage count.* When `M` is
P-reducible, extracts the reduced stage count `ŝ` from the existential
witness. Companion `IsPReducible.sBar_lt` exposes `ŝ < s`. -/
noncomputable def IsPReducible.sBar {s : ℕ} {M : RKTableau s}
    (h : M.IsPReducible) : ℕ :=
  h.choose

/-- *P-reduction witness extractor — strict descent.* The extracted
reduced stage count is strictly less than `s`. This is the
non-triviality side condition (`ŝ < s`) of `IsPReducible` exposed at
the destructor level. -/
theorem IsPReducible.sBar_lt {s : ℕ} {M : RKTableau s}
    (h : M.IsPReducible) : h.sBar < s :=
  h.choose_spec.choose

/-- *P-reduction witness extractor — partition.* The partition
witnessing P-reducibility, with the extracted stage count as its
codomain. -/
noncomputable def IsPReducible.partition {s : ℕ} {M : RKTableau s}
    (h : M.IsPReducible) : PPartition s h.sBar :=
  h.choose_spec.choose_spec.choose

/-- *P-reduction witness extractor — row-sum-constancy proof.* The
extracted partition satisfies the row-sum-constancy condition
`IsPReducibleVia`. Together with `IsPReducible.partition`, this is the
full P-reduction certificate. -/
theorem IsPReducible.partition_isPReducibleVia {s : ℕ} {M : RKTableau s}
    (h : M.IsPReducible) : M.IsPReducibleVia h.partition :=
  h.choose_spec.choose_spec.choose_spec

/-- *0-reduction witness extractor — partition predicate.* When `M`
is 0-reducible, extracts the Boolean partition predicate `inP1`
witnessing `{1,…,s} = P₀ ∪ P₁` with `P₀ = {i | inP1 i = false}`. -/
noncomputable def IsZeroReducible.inP1 {s : ℕ} {M : RKTableau s}
    (h : M.IsZeroReducible) : Fin s → Bool :=
  h.choose

/-- *0-reduction witness extractor — non-empty P₀.* The extracted
partition has at least one `false`-indexed element (i.e. `P₀ ≠ ∅`).
This is the non-triviality hypothesis from `IsZeroReducible`; it is
exactly the hypothesis that `PReducesTo.size_lt_of_zeroStep`
(cycle 195) and `card_filter_true_lt_of_exists_false` (cycle 195
private helper) consume. -/
theorem IsZeroReducible.exists_inP1_false {s : ℕ} {M : RKTableau s}
    (h : M.IsZeroReducible) : ∃ i, h.inP1 i = false :=
  h.choose_spec.1

/-- *0-reduction witness extractor — zero-reducibility proof.* The
extracted partition satisfies the two zero conditions
(`IsZeroReducibleVia`: `b` vanishes on `P₀`, and `A` vanishes on
`P₁ × P₀`). -/
theorem IsZeroReducible.inP1_isZeroReducibleVia
    {s : ℕ} {M : RKTableau s}
    (h : M.IsZeroReducible) : M.IsZeroReducibleVia h.inP1 :=
  h.choose_spec.2

/-- *Strict stage-count descent via the extracted P-reduction.* The
`pReduced` of the extracted partition has stage count `h.sBar`, which
is strictly less than `s`. Direct restatement of `IsPReducible.sBar_lt`
under the renaming "the pReduced-codomain stage count is strictly less
than the original stage count", which is the form the future
`reducedMethod` recursion will consume. -/
theorem IsPReducible.pReduced_size_lt {s : ℕ} {M : RKTableau s}
    (h : M.IsPReducible) : h.sBar < s :=
  h.sBar_lt

/-- *Strict stage-count descent via the extracted 0-reduction.* The
`zeroReduced` of the extracted partition has stage count
`(Finset.univ.filter (fun i => h.inP1 i = true)).card`, strictly less
than `s` because `h.exists_inP1_false` provides a witness of a
`false`-indexed element (so the `true`-filter is a proper subset of
`Finset.univ`). Direct application of cycle 195's
`card_filter_true_lt_of_exists_false` private helper. -/
theorem IsZeroReducible.zeroReduced_size_lt
    {s : ℕ} {M : RKTableau s} (h : M.IsZeroReducible) :
    (Finset.univ.filter
        (fun i : Fin s => h.inP1 i = true)).card < s :=
  card_filter_true_lt_of_exists_false h.exists_inP1_false

/-- *Existential witness for def:381E `reducedMethod`.* Every
Runge–Kutta method P-reduces (in zero or more steps via `PReducesTo`)
to an irreducible one. This is the *existential* half of the textbook
def:381E "reduced method" construction: it asserts the *existence* of
an irreducible reduct, without (yet) constructing it as a definable
recursive function.

The full constructive `noncomputable def reducedMethod` is deferred
(see `.prover-state/issues/reduced_method_deferred.md`): it would
require either a Σ-typed `WellFoundedRelation` instance on
`(s, M)`-pairs or decidability of `IsPReducible`/`IsZeroReducible`,
both of which are multi-cycle engineering tasks. The existential
witness packaged here suffices for *uniqueness* statements about the
reduced method (e.g. def:381F can be phrased existentially: two
P-equivalent methods produce reducts that coincide up to `HEq` via
`PEquivalent.eq_of_both_isIrreducible`).

The proof is strong induction on the stage count `s`, using the
cycle-195 strict-descent infrastructure (`PReducesTo.size_lt_of_step`
and `size_lt_of_zeroStep` via the destructor-level restatements
`IsPReducible.sBar_lt` and `IsZeroReducible.zeroReduced_size_lt`)
and the cycle-196 witness destructors (`IsPReducible.partition`,
`IsPReducible.partition_isPReducibleVia`, `IsZeroReducible.inP1`,
`IsZeroReducible.exists_inP1_false`,
`IsZeroReducible.inP1_isZeroReducibleVia`). The inductive step
case-splits on `¬ M.IsIrreducible = M.IsZeroReducible ∨ M.IsPReducible`
(both branches transitively chain the single-step reduction with the
IH-supplied tail via `PReducesTo.trans`, cycle 192). The
non-constructive `Classical.choose`-flavoured destructors and the
classical `not_and_or`/`not_not` rewrites make this theorem
`Classical.choice`-axiomatic, which is expected for an existential
witness over a non-decidable predicate. -/
theorem reducedMethod_exists {s : ℕ} (M : RKTableau s) :
    ∃ (s' : ℕ) (M' : RKTableau s'),
      M.PReducesTo M' ∧ M'.IsIrreducible := by
  suffices h : ∀ s : ℕ, ∀ M : RKTableau s,
      ∃ (s' : ℕ) (M' : RKTableau s'),
        M.PReducesTo M' ∧ M'.IsIrreducible from h s M
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro M
    by_cases hIrr : M.IsIrreducible
    · exact ⟨s, M, .refl M, hIrr⟩
    · -- Reducible: 0-reducible or P-reducible (def:381E negated)
      rw [IsIrreducible, not_and_or, not_not, not_not] at hIrr
      rcases hIrr with hZ | hP
      · -- 0-reducible branch — chain `.zeroStep` with the IH-supplied tail
        have hStep : M.PReducesTo (M.zeroReduced hZ.inP1) :=
          .zeroStep hZ.inP1 hZ.exists_inP1_false
            hZ.inP1_isZeroReducibleVia (.refl _)
        obtain ⟨s', M', hRed, hIrr'⟩ :=
          ih _ hZ.zeroReduced_size_lt (M.zeroReduced hZ.inP1)
        exact ⟨s', M', hStep.trans hRed, hIrr'⟩
      · -- P-reducible branch — chain `.step` with the IH-supplied tail
        have hStep : M.PReducesTo (M.pReduced hP.partition) :=
          .step hP.partition hP.sBar_lt
            hP.partition_isPReducibleVia (.refl _)
        obtain ⟨s', M', hRed, hIrr'⟩ :=
          ih hP.sBar hP.sBar_lt (M.pReduced hP.partition)
        exact ⟨s', M', hStep.trans hRed, hIrr'⟩

/-- *Existential characterization of def:381F (P-equivalence).*

Butcher §380 def:381F asserts that two Runge–Kutta methods are
P-equivalent iff each of them reduces to the same reduced method.
The constructive `noncomputable def reducedMethod` recursion that
would produce the canonical reduct as a function of the input is
deferred (see `.prover-state/issues/reduced_method_deferred.md`),
but the *existential* reading — that a common irreducible reduct
exists — is provable directly from cycle 197's
`reducedMethod_exists` and cycle 192's `PReducesTo.trans`, and
captures the def:381F content as a `Prop`.

The forward direction destructures `PEquivalent` to a common (not
necessarily irreducible) reduct `N`, applies `reducedMethod_exists`
to `N` to obtain an irreducible reduct `M''` of `N`, and chains the
two reduction sequences via `PReducesTo.trans`.

The reverse direction discards the irreducibility witness (which is
not required at the `PEquivalent`-level: P-equivalence only demands
a common reduct, not an irreducible one) and unpacks the
existential directly.

Cycle 198 deliverable. -/
theorem pEquivalent_iff_exists_common_irreducible_reduct
    {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') :
    PEquivalent M M' ↔
      ∃ (s'' : ℕ) (M'' : RKTableau s''),
        PReducesTo M M'' ∧ PReducesTo M' M'' ∧ M''.IsIrreducible := by
  refine ⟨?_, ?_⟩
  · rintro ⟨t, N, hMN, hM'N⟩
    obtain ⟨s'', M'', hNM'', hIrr⟩ := reducedMethod_exists N
    exact ⟨s'', M'', hMN.trans hNM'', hM'N.trans hNM'', hIrr⟩
  · rintro ⟨s'', M'', hMM'', hM'M'', _hIrr⟩
    exact ⟨s'', M'', hMM'', hM'M''⟩

/-- *Heterogeneous-stage uniqueness of irreducible reducts — special case
where both sources are already irreducible.*

If two irreducible methods `M` and `M'` are `PEquivalent`, then any
`PReducesTo` chains `h₁ : M → M₁` and `h₂ : M' → M₂` produce reducts
`M₁`, `M₂` that coincide up to heterogeneous-stage `HEq`. Cycle 188's
`eq_of_isIrreducible_of_pReducesTo` forces both chains to be reflexive
(`M₁ ≃ M`, `M₂ ≃ M'` up to `HEq`), so this lemma is a corollary of
cycle 193's `PEquivalent.eq_of_both_isIrreducible` composed with two
applications of cycle 188 and an `HEq` chain.

The general statement — uniqueness of the irreducible reduct when the
sources `M`, `M'` are *not* a priori irreducible — is the natural
continuation of cycle 198's `pEquivalent_iff_exists_common_irreducible_reduct`
but requires confluence of `PReducesTo` (Newman's lemma applied to the
abstract rewriting system defined by `step` / `zeroStep`), which is not
currently in `Section381.lean`. The multi-cycle plan toward the general
statement is documented at
`.prover-state/issues/p_reduction_confluence_gap.md` (cycle 199 issue).
This lemma is the strictly-weaker single-cycle deliverable that an
ergonomic call-site API for the special case, without depending on the
unfinished confluence infrastructure.

Note that the target irreducibility hypotheses `M₁.IsIrreducible`,
`M₂.IsIrreducible` are *not* required: cycle 188 forces `M₁ ≃ M` and
`M₂ ≃ M'`, so the targets inherit irreducibility from the sources
automatically. Cycle 199 deliverable. -/
theorem pEquivalent_irreducible_reduct_unique_of_sources_irreducible
    {s s' s₁ s₂ : ℕ}
    {M : RKTableau s} {M' : RKTableau s'}
    {M₁ : RKTableau s₁} {M₂ : RKTableau s₂}
    (hMirr : M.IsIrreducible) (hM'irr : M'.IsIrreducible)
    (h₁ : PReducesTo M M₁) (h₂ : PReducesTo M' M₂)
    (hEquiv : PEquivalent M M') :
    s₁ = s₂ ∧ HEq M₁ M₂ := by
  obtain ⟨h₁eq, h₁heq⟩ := eq_of_isIrreducible_of_pReducesTo hMirr h₁
  obtain ⟨h₂eq, h₂heq⟩ := eq_of_isIrreducible_of_pReducesTo hM'irr h₂
  obtain ⟨h₃eq, h₃heq⟩ :=
    PEquivalent.eq_of_both_isIrreducible hMirr hM'irr hEquiv
  subst h₁eq
  subst h₂eq
  subst h₃eq
  exact ⟨rfl, (h₁heq.trans h₃heq.symm).trans h₂heq.symm⟩

/- ### Definition 381A — equivalent Runge–Kutta methods -/

/-- Predicate form of "method `M` produces output `y₁` after one step
of size `h` from initial value `y₀` on the autonomous ODE `y' = f(y)`".

Captures the implicit stage system
`Yᵢ = y₀ + h • Σⱼ aᵢⱼ • f(Yⱼ)` together with the update
`y₁ = y₀ + h • Σᵢ bᵢ • f(Yᵢ)`. Encoded as a `Prop`, not a function:
implicit methods may admit zero, one, or many solutions of the stage
system depending on `M`, `f`, and `h`, so a function-style "the
output" would silently drop the ambiguity. The predicate is *true*
for any `(Y, y₁)` tuple satisfying both equations. -/
def IsRKOneStep {s : ℕ} (M : RKTableau s) {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : N → N) (y₀ : N) (h : ℝ) (y₁ : N) : Prop :=
  ∃ Y : Fin s → N,
    (∀ i, Y i = y₀ + h • ∑ j, M.A i j • f (Y j)) ∧
    y₁ = y₀ + h • ∑ i, M.b i • f (Y i)

/-- Non-autonomous predicate form of "method `M` produces output `y₁`
after one step of size `h` from initial value `y₀` at time `x₀` on the
non-autonomous ODE `y' = f(x, y)`".

Captures the implicit stage system
`Yᵢ = y₀ + h • Σⱼ aᵢⱼ • f(x₀ + cⱼ h, Yⱼ)` together with the update
`y₁ = y₀ + h • Σᵢ bᵢ • f(x₀ + cᵢ h, Yᵢ)`. As with `IsRKOneStep`, this
is a `Prop`: any `(Y, y₁)` tuple satisfying both equations witnesses
the relation, honestly handling the zero/one/many implicit-stage
solutions case.

Used by `Section357.IsBNStable` (def:357A) and downstream non-linear
stability results which require the non-autonomous form. -/
def IsRKOneStepNonAut {s : ℕ} (M : RKTableau s) {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : ℝ → N → N) (x₀ : ℝ) (y₀ : N) (h : ℝ) (y₁ : N) : Prop :=
  ∃ Y : Fin s → N,
    (∀ i, Y i = y₀ + h • ∑ j, M.A i j • f (x₀ + M.c j * h) (Y j)) ∧
    y₁ = y₀ + h • ∑ i, M.b i • f (x₀ + M.c i * h) (Y i)

/-- Butcher §380 Definition 381A — two Runge–Kutta methods are
*equivalent* if, for every autonomous Lipschitz right-hand side `f` and
every initial value `y₀`, there exists a step-size threshold `h₀ > 0`
below which any one-step output of the first method coincides with any
one-step output of the second method.

This is **semantic** equivalence (same numerical output on every
Lipschitz autonomous problem at sufficiently small step), strictly
weaker than Φ-equivalence (`PhiEquivalent`, def:381B): the methods
are allowed to diverge on non-Lipschitz problems or at large step
sizes where the implicit stage system has no/multiple solutions.

The `∀ y₁ y₁'` quantifier handles the (rare, implicit-method) case
where the stage equations have multiple solutions: we require
*every* output of `M` to agree with *every* output of `M'`. The
hypothesis `LipschitzWith L f` (`L : ℝ≥0`) is the standard
Mathlib global-Lipschitz predicate and matches Butcher's "satisfying
a Lipschitz condition" verbatim. -/
def Equivalent {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') : Prop :=
  ∀ {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : N → N) (L : ℝ≥0) (_hL : LipschitzWith L f) (y₀ : N),
    ∃ h₀ > (0 : ℝ), ∀ h, 0 < h → h ≤ h₀ →
      ∀ y₁ y₁', M.IsRKOneStep f y₀ h y₁ → M'.IsRKOneStep f y₀ h y₁' →
        y₁ = y₁'

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
theorem paddedEuler_isPReducibleVia_pairPartition :
    paddedEuler.IsPReducibleVia pairPartition := by
  intro _ _ _ _ _ _
  simp [paddedEuler]

/-- Hence `paddedEuler` is P-reducible. -/
theorem paddedEuler_isPReducible : paddedEuler.IsPReducible :=
  ⟨1, by decide, pairPartition, paddedEuler_isPReducibleVia_pairPartition⟩

/-- Non-trivial single-step P-reduction: `paddedEuler` (2 stages) reduces
to its 1-stage P-reduced form via `pairPartition`. Exercises the `step`
constructor of `PReducesTo` (cycle 185 made `step` require the strict
stage-decrease side condition `sBar < s`); composed with `refl` for
the tail of the chain. -/
theorem paddedEuler_pReducesTo_pReduced :
    RKTableau.PReducesTo paddedEuler (paddedEuler.pReduced pairPartition) :=
  RKTableau.PReducesTo.step pairPartition (by decide)
    paddedEuler_isPReducibleVia_pairPartition
    (RKTableau.PReducesTo.refl _)

/-- Non-vacuity witness for `def:381F` (P-equivalent): `paddedEuler` is
P-equivalent to its 1-stage P-reduction via `pairPartition`. The
reduction step is the textbook's row-sum-constancy P-reduction
(def:381D); the witness exercises the `step` constructor of
`PReducesTo`, beyond reflexivity, on heterogeneous stage counts
(2 ↦ 1). Cycle 185 used this fact internally inside the
`paddedEuler.PEquivalent paddedEuler` proof; cycle 186 promotes it to
a public theorem so downstream P-equivalence work has a named
non-reflexive witness to consume. -/
theorem paddedEuler_pEquivalent_pReduced :
    paddedEuler.PEquivalent (paddedEuler.pReduced pairPartition) :=
  RKTableau.PEquivalent.of_pReducesTo paddedEuler_pReducesTo_pReduced

/- ### Non-vacuous witness for 0-reducibility

The 2-stage `paddedEuler` tableau has `b = ![1, 0]` and `A = 0`. The
partition `inP1 := ![true, false]` (so `P₁ = {0}` and `P₀ = {1}`)
witnesses 0-reducibility:

* `b 1 = 0` ✔ (the only `P₀`-indexed stage is `1`).
* `A i j = 0` for `i ∈ P₁, j ∈ P₀` ✔ (vacuously, since `A = 0`).
* `P₀ ≠ ∅` ✔ (stage `1` lies in `P₀`). -/

/-- `paddedEuler` is 0-reducible-via the partition `![true, false]`
(i.e. `P₁ = {0}`, `P₀ = {1}`). Promoted to a named theorem in cycle 188
so that `zeroStep`-based reduction witnesses can consume it directly. -/
theorem paddedEuler_isZeroReducibleVia_split :
    paddedEuler.IsZeroReducibleVia ![true, false] := by
  refine ⟨?_, ?_⟩
  · intro i hi
    fin_cases i <;> simp_all [paddedEuler]
  · intro i j hi hj
    simp [paddedEuler]

/-- Hence `paddedEuler` is 0-reducible. -/
theorem paddedEuler_isZeroReducible : paddedEuler.IsZeroReducible :=
  ⟨![true, false], ⟨1, by decide⟩, paddedEuler_isZeroReducibleVia_split⟩

/-- Non-trivial single-step 0-reduction: `paddedEuler` (2 stages)
reduces to its 1-stage 0-reduced form via the `![true, false]` partition.
Exercises the `zeroStep` constructor of `PReducesTo` (introduced in
cycle 188), composed with `refl` for the tail of the chain. The
`(by decide)` discharges `∃ i, inP1 i = false` (witness `i = 1`). -/
theorem paddedEuler_pReducesTo_zeroReduced :
    RKTableau.PReducesTo paddedEuler
      (paddedEuler.zeroReduced ![true, false]) :=
  RKTableau.PReducesTo.zeroStep ![true, false] (by decide)
    paddedEuler_isZeroReducibleVia_split
    (RKTableau.PReducesTo.refl _)

/-- Non-vacuity witness for `def:381F` exercising the `zeroStep`
constructor: `paddedEuler` is P-equivalent to its 1-stage 0-reduced
form via a single 0-reduction step. Consumes
`paddedEuler_pReducesTo_zeroReduced` through
`PEquivalent.of_pReducesTo`. The Φ-equivalence companion
`paddedEuler_phiEquivalent_zeroReduced` is below the definition of
`PhiEquivalent.of_pReducesTo`. -/
theorem paddedEuler_pEquivalent_zeroReduced :
    paddedEuler.PEquivalent (paddedEuler.zeroReduced ![true, false]) :=
  RKTableau.PEquivalent.of_pReducesTo paddedEuler_pReducesTo_zeroReduced

/-- Non-vacuity witness for cycle 198's
`pEquivalent_iff_exists_common_irreducible_reduct`: applying the
forward (`.mp`) direction of the iff to
`paddedEuler_pEquivalent_pReduced` extracts an irreducible common
reduct of `paddedEuler` and `paddedEuler.pReduced pairPartition`.
Confirms the def:381F existential characterization fires
non-vacuously on the heterogeneous-stages (2 → 1) reduction
exercised by the canonical example. -/
example :
    ∃ (s'' : ℕ) (M'' : RKTableau s''),
      paddedEuler.PReducesTo M''
      ∧ (paddedEuler.pReduced pairPartition).PReducesTo M''
      ∧ M''.IsIrreducible :=
  (RKTableau.pEquivalent_iff_exists_common_irreducible_reduct _ _).mp
    paddedEuler_pEquivalent_pReduced

/-- Non-vacuity witness for `PReducesTo.trans` (cycle 192): chaining a
non-trivial P-reduction step with a reflexive tail re-yields the
single-step witness. The `step` constructor case of `trans`'s
induction fires on the left factor; the `refl` continuation is the
right factor. -/
example :
    RKTableau.PReducesTo paddedEuler (paddedEuler.pReduced pairPartition) :=
  paddedEuler_pReducesTo_pReduced.trans
    (RKTableau.PReducesTo.refl _)

/-- Non-vacuity witness for `PReducesTo.trans` (cycle 192) exercising
the `zeroStep` constructor case of the induction: chaining the
non-trivial 0-reduction `paddedEuler →ᴾ paddedEuler.zeroReduced
![true, false]` with a reflexive tail re-yields the single-step
witness. -/
example :
    RKTableau.PReducesTo paddedEuler
      (paddedEuler.zeroReduced ![true, false]) :=
  paddedEuler_pReducesTo_zeroReduced.trans
    (RKTableau.PReducesTo.refl _)

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

/- ### Non-vacuity witness for `def:381A` (Equivalent)

`RKTableau.explicitEuler` (the 1-stage explicit Euler tableau, with
`A = 0` and `b ≡ 1`) is `Equivalent` to itself: the stage system has
the unique solution `Y 0 = y₀` and the update reads
`y₁ = y₀ + h • f y₀`. The threshold `h₀ = 1` works (any positive `h₀`
would do, since explicit Euler is well-defined for every `h`).

The general `Equivalent M M` for arbitrary `M` requires implicit-stage
uniqueness via Banach contraction at small `h`; that infrastructure is
deferred — see `.prover-state/issues/equivalent_self_general_deferred.md`. -/

open scoped NNReal in
/-- Non-vacuity witness for `def:381A`: explicit Euler is equivalent to
itself. -/
theorem equivalent_explicitEuler_self :
    RKTableau.explicitEuler.Equivalent RKTableau.explicitEuler := by
  intro N _ _ f L _hL y₀
  refine ⟨1, one_pos, ?_⟩
  intro h _hh_pos _hh_le y₁ y₁' h₁ h₁'
  obtain ⟨Y, hY_stage, hy₁⟩ := h₁
  obtain ⟨Y', hY'_stage, hy₁'⟩ := h₁'
  have hY0 : Y 0 = y₀ := by
    have hs := hY_stage 0
    simp [RKTableau.explicitEuler] at hs
    exact hs
  have hY'0 : Y' 0 = y₀ := by
    have hs := hY'_stage 0
    simp [RKTableau.explicitEuler] at hs
    exact hs
  rw [hy₁, hy₁']
  simp [RKTableau.explicitEuler, hY0, hY'0]

/- ### Non-vacuity witness for `PEquivalent.trans_of_middle_isIrreducible`

The 1-stage tableau `paddedEuler.pReduced pairPartition` is irreducible:

* Not 0-reducible: the only partition `inP1 : Fin 1 → Bool` with
  `(∃ i, inP1 i = false)` has `inP1 0 = false`, which forces `b 0 = 0`.
  But `(paddedEuler.pReduced pairPartition).b 0 = 1` (sum of
  `paddedEuler.b 0 = 1` and `paddedEuler.b 1 = 0` over the trivial
  block `pairPartition⁻¹{0} = {0, 1}`).
* Not P-reducible: `sBar < 1` ⇒ `sBar = 0` ⇒ `Fin 0` empty.

Combined with the non-trivial reduction
`paddedEuler →ᴾ paddedEuler.pReduced pairPartition`, trans-through-an-
irreducible-middle yields `paddedEuler.PEquivalent paddedEuler`
exercising the non-trivial `step` constructor in both directions —
strictly beyond the reflexivity witness `PEquivalent.refl`. -/

/-- Non-vacuity witness for `def:381F` exercising
`PEquivalent.trans_of_middle_isIrreducible`: `paddedEuler` is
P-equivalent to itself via the trans-through-the-1-stage-reduction,
not just via the reflexive witness. -/
example : paddedEuler.PEquivalent paddedEuler := by
  have hMidPReducedB :
      (paddedEuler.pReduced pairPartition).b 0 = 1 := by
    show (∑ i ∈ Finset.univ.filter
              (fun i : Fin 2 => pairPartition.block i = 0),
            paddedEuler.b i) = 1
    have hFilter :
        (Finset.univ.filter
            (fun i : Fin 2 => pairPartition.block i = 0))
          = Finset.univ := by
      ext i
      simp [pairPartition]
    rw [hFilter]
    simp [paddedEuler, Fin.sum_univ_two]
  have hMid_irr : (paddedEuler.pReduced pairPartition).IsIrreducible := by
    refine ⟨?_, ?_⟩
    · -- ¬ IsZeroReducible
      rintro ⟨inP1, ⟨i, hiF⟩, hbZero, _⟩
      fin_cases i
      have hb0 : (paddedEuler.pReduced pairPartition).b 0 = 0 :=
        hbZero 0 hiF
      linarith [hMidPReducedB]
    · -- ¬ IsPReducible
      rintro ⟨sBar, hLt, P, _⟩
      obtain rfl : sBar = 0 := Nat.lt_one_iff.mp hLt
      exact (P.block 0).elim0
  exact paddedEuler_pEquivalent_pReduced.trans_of_middle_isIrreducible
    paddedEuler_pEquivalent_pReduced.symm hMid_irr

/- ### Φ-equivalence is implied by P-reduction (Butcher §380)

The two `derivativeWeight_pReduced` / `derivativeWeightProd_pReduced`
helpers below are proved by mutual induction on the rooted-tree
structure, paralleling `derivativeWeight`'s mutual recursion through
`RootedTree` and `List RootedTree` (Section 312). The key fact: the
row-sum-constancy condition `IsPReducibleVia` ensures the recursive
sum over `Fin s` regroups into the `Fin sBar` sum that defines the
reduced method's coefficient `â_{IJ}`. -/

mutual
  /-- *P-reduction preserves derivative weights stage-by-stage.*
  Helper for `pReduced_phiEquivalent`; companion to
  `derivativeWeightProd_pReduced` for the list-helper level. -/
  private theorem derivativeWeight_pReduced {s sBar : ℕ}
      (M : RKTableau s) {P : PPartition s sBar}
      (h : M.IsPReducibleVia P) :
      ∀ (t : RootedTree) (i : Fin s),
      M.derivativeWeight i t
        = (M.pReduced P).derivativeWeight (P.block i) t
    | RootedTree.mk children, i => by
        show M.derivativeWeightProd i children
            = (M.pReduced P).derivativeWeightProd (P.block i) children
        exact derivativeWeightProd_pReduced M h children i

  /-- List-helper companion to `derivativeWeight_pReduced`. -/
  private theorem derivativeWeightProd_pReduced {s sBar : ℕ}
      (M : RKTableau s) {P : PPartition s sBar}
      (h : M.IsPReducibleVia P) :
      ∀ (children : List RootedTree) (i : Fin s),
      M.derivativeWeightProd i children
        = (M.pReduced P).derivativeWeightProd (P.block i) children
    | [], _ => rfl
    | t :: ts, i => by
        show (∑ j : Fin s, M.A i j * M.derivativeWeight j t)
                * M.derivativeWeightProd i ts
            = (∑ J : Fin sBar, (M.pReduced P).A (P.block i) J
                                * (M.pReduced P).derivativeWeight J t)
              * (M.pReduced P).derivativeWeightProd (P.block i) ts
        rw [derivativeWeightProd_pReduced M h ts i]
        congr 1
        have hSumRewrite :
            (∑ j : Fin s, M.A i j * M.derivativeWeight j t)
              = ∑ j : Fin s,
                  M.A i j * (M.pReduced P).derivativeWeight (P.block j) t :=
          Finset.sum_congr rfl (fun j _ => by
            rw [derivativeWeight_pReduced M h t j])
        rw [hSumRewrite,
            show
              (∑ j : Fin s,
                  M.A i j * (M.pReduced P).derivativeWeight (P.block j) t)
                = ∑ J : Fin sBar,
                    ∑ j ∈ Finset.univ.filter
                            (fun j : Fin s => P.block j = J),
                      M.A i j
                        * (M.pReduced P).derivativeWeight (P.block j) t
            from
              (Finset.sum_fiberwise
                  (Finset.univ : Finset (Fin s)) P.block
                  (fun j => M.A i j
                              * (M.pReduced P).derivativeWeight
                                  (P.block j) t)).symm]
        refine Finset.sum_congr rfl (fun J _ => ?_)
        have hSubst :
            (∑ j ∈ Finset.univ.filter (fun j : Fin s => P.block j = J),
                M.A i j * (M.pReduced P).derivativeWeight (P.block j) t)
              = ∑ j ∈ Finset.univ.filter
                        (fun j : Fin s => P.block j = J),
                  M.A i j * (M.pReduced P).derivativeWeight J t :=
          Finset.sum_congr rfl (fun j hj => by
            rw [(Finset.mem_filter.mp hj).2])
        rw [hSubst, ← Finset.sum_mul,
            RKTableau.pReduced_A_apply M h (P.block i) J i rfl]
end

/-- *P-reduction preserves elementary weights.*

Each P-reduction step regroups the elementary-weight sum
`Σ_i b_i Φᵢ(t)` into the reduced sum `Σ_I b̂_I Φ̂_I(t)`:
row-sum-constancy makes the per-stage derivative weights agree on each
block (`derivativeWeight_pReduced`), and the textbook partition
`b̂_I = Σ_{i ∈ P_I} b_i` collapses the regrouped `b`-sum via
`pReduced_b_apply`. -/
theorem pReduced_phiEquivalent {s sBar : ℕ}
    (M : RKTableau s) {P : PPartition s sBar}
    (h : M.IsPReducibleVia P) :
    PhiEquivalent M (M.pReduced P) := by
  intro t
  show ∑ i : Fin s, M.b i * M.derivativeWeight i t
      = ∑ I : Fin sBar,
          (M.pReduced P).b I * (M.pReduced P).derivativeWeight I t
  have hSumRewrite :
      (∑ i : Fin s, M.b i * M.derivativeWeight i t)
        = ∑ i : Fin s,
            M.b i * (M.pReduced P).derivativeWeight (P.block i) t :=
    Finset.sum_congr rfl (fun i _ => by
      rw [derivativeWeight_pReduced M h t i])
  rw [hSumRewrite,
      show
        (∑ i : Fin s,
            M.b i * (M.pReduced P).derivativeWeight (P.block i) t)
          = ∑ I : Fin sBar,
              ∑ i ∈ Finset.univ.filter (fun i : Fin s => P.block i = I),
                M.b i * (M.pReduced P).derivativeWeight (P.block i) t
      from
        (Finset.sum_fiberwise
            (Finset.univ : Finset (Fin s)) P.block
            (fun i => M.b i
                        * (M.pReduced P).derivativeWeight
                            (P.block i) t)).symm]
  refine Finset.sum_congr rfl (fun I _ => ?_)
  have hSubst :
      (∑ i ∈ Finset.univ.filter (fun i : Fin s => P.block i = I),
          M.b i * (M.pReduced P).derivativeWeight (P.block i) t)
        = ∑ i ∈ Finset.univ.filter (fun i : Fin s => P.block i = I),
            M.b i * (M.pReduced P).derivativeWeight I t :=
    Finset.sum_congr rfl (fun i hi => by
      rw [(Finset.mem_filter.mp hi).2])
  rw [hSubst, ← Finset.sum_mul,
      show (∑ i ∈ Finset.univ.filter (fun i : Fin s => P.block i = I),
              M.b i)
            = (M.pReduced P).b I
        from (RKTableau.pReduced_b_apply M P I).symm]

/- ### Φ-equivalence is implied by 0-reduction (Butcher §380)

The 0-reduction analogue of `pReduced_phiEquivalent`. Butcher's narrative
around 0-reduction (§380, p. 302) treats Φ-preservation as obvious because
deleted stages have weight zero; we formalise this via the two clauses of
`IsZeroReducibleVia`. Proof structure parallels the P-reduction case:
two private mutual helpers establish stage-by-stage agreement, and the
main theorem reindexes the outer `Σ_i b_i Φᵢ(t)` decomposition.

The reindexing is simpler than in the P-reduction case — `zeroReducedEmb`
is a literal injection from `Fin sBar'` into `Fin s` (no `Classical.choose`
representative plumbing), so each new stage corresponds to a unique old
stage in `P₁`. The `inP1 i = false` summands are killed via the two
clauses of `IsZeroReducibleVia` (`b i = 0` for the outer sum, `A i j = 0`
for the inner sum). -/

/-- The 0-reduction order embedding lands inside `P₁`: every reindexed
stage `(zeroReducedEmb inP1) I` satisfies `inP1 _ = true`. Used by the
mutual derivative-weight helpers to identify which old-stage indices the
embedding produces. -/
private theorem zeroReducedEmb_inP1_eq_true {s : ℕ}
    (inP1 : Fin s → Bool)
    (I : Fin (Finset.univ.filter (fun i : Fin s => inP1 i = true)).card) :
    inP1 (RKTableau.zeroReducedEmb inP1 I) = true := by
  have h := Finset.orderEmbOfFin_mem
    (Finset.univ.filter (fun i : Fin s => inP1 i = true)) rfl I
  exact (Finset.mem_filter.mp h).2

mutual
  /-- *0-reduction preserves derivative weights stage-by-stage.*
  Helper for `zeroReduced_phiEquivalent`; companion to
  `derivativeWeightProd_zeroReduced` for the list-helper level. -/
  private theorem derivativeWeight_zeroReduced {s : ℕ}
      (M : RKTableau s) {inP1 : Fin s → Bool}
      (h : M.IsZeroReducibleVia inP1) :
      ∀ (t : RootedTree)
        (I : Fin (Finset.univ.filter
                    (fun i : Fin s => inP1 i = true)).card),
      M.derivativeWeight (RKTableau.zeroReducedEmb inP1 I) t
        = (M.zeroReduced inP1).derivativeWeight I t
    | RootedTree.mk children, I => by
        show M.derivativeWeightProd (RKTableau.zeroReducedEmb inP1 I) children
            = (M.zeroReduced inP1).derivativeWeightProd I children
        exact derivativeWeightProd_zeroReduced M h children I

  /-- List-helper companion to `derivativeWeight_zeroReduced`. -/
  private theorem derivativeWeightProd_zeroReduced {s : ℕ}
      (M : RKTableau s) {inP1 : Fin s → Bool}
      (h : M.IsZeroReducibleVia inP1) :
      ∀ (children : List RootedTree)
        (I : Fin (Finset.univ.filter
                    (fun i : Fin s => inP1 i = true)).card),
      M.derivativeWeightProd (RKTableau.zeroReducedEmb inP1 I) children
        = (M.zeroReduced inP1).derivativeWeightProd I children
    | [], _ => rfl
    | t :: ts, I => by
        show (∑ j : Fin s,
                M.A (RKTableau.zeroReducedEmb inP1 I) j
                  * M.derivativeWeight j t)
              * M.derivativeWeightProd (RKTableau.zeroReducedEmb inP1 I) ts
            = (∑ J :
                Fin (Finset.univ.filter
                        (fun i : Fin s => inP1 i = true)).card,
                  (M.zeroReduced inP1).A I J
                    * (M.zeroReduced inP1).derivativeWeight J t)
              * (M.zeroReduced inP1).derivativeWeightProd I ts
        rw [derivativeWeightProd_zeroReduced M h ts I]
        congr 1
        have hEmbTrue :
            inP1 (RKTableau.zeroReducedEmb inP1 I) = true :=
          zeroReducedEmb_inP1_eq_true inP1 I
        -- Step 1: discard `inP1 j = false` summands (their `M.A` factor is 0).
        have hStep1 :
            (∑ j : Fin s,
                M.A (RKTableau.zeroReducedEmb inP1 I) j
                  * M.derivativeWeight j t)
              = ∑ j ∈ Finset.univ.filter (fun j : Fin s => inP1 j = true),
                  M.A (RKTableau.zeroReducedEmb inP1 I) j
                    * M.derivativeWeight j t := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro j _ hj_notin
          have hjFalse : inP1 j = false := by
            have hjNotTrue : inP1 j ≠ true := fun hjT =>
              hj_notin (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjT⟩)
            cases hh : inP1 j with
            | false => rfl
            | true => exact absurd hh hjNotTrue
          rw [h.2 (RKTableau.zeroReducedEmb inP1 I) j hEmbTrue hjFalse,
              zero_mul]
        rw [hStep1]
        -- Step 2: reindex the surviving `Fin s` sum back to `Fin sBar'` via
        -- `zeroReducedEmb`. We use `Finset.sum_bij` to avoid the dependent-
        -- type issue that breaks `rw [image_orderEmbOfFin_univ.symm]` (the
        -- RHS sum's index type is `Fin filter.card`).
        symm
        refine Finset.sum_bij
          (fun J _ => RKTableau.zeroReducedEmb inP1 J)
          (fun J _ => Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, zeroReducedEmb_inP1_eq_true inP1 J⟩)
          (fun J₁ _ J₂ _ heq =>
            (RKTableau.zeroReducedEmb inP1).injective heq)
          ?_ ?_
        · intro b hb
          have hImg : Finset.image (RKTableau.zeroReducedEmb inP1)
                        Finset.univ
                = Finset.univ.filter (fun j : Fin s => inP1 j = true) := by
            show Finset.image
              ⇑((Finset.univ.filter
                    (fun i : Fin s => inP1 i = true)).orderEmbOfFin rfl)
              Finset.univ = _
            exact Finset.image_orderEmbOfFin_univ _ rfl
          have hbImg : b ∈ Finset.image
              (RKTableau.zeroReducedEmb inP1) Finset.univ := hImg.symm ▸ hb
          rcases Finset.mem_image.mp hbImg with ⟨J, hJ_mem, hJ_eq⟩
          exact ⟨J, hJ_mem, hJ_eq⟩
        · intro J _
          rw [derivativeWeight_zeroReduced M h t J]
          rfl
end

/-- *0-reduction preserves elementary weights.*

Each 0-reduction step regroups `Σ_i b_i Φᵢ(t)` over `Fin s` into the
reduced sum `Σ_I b̂_I Φ̂_I(t)` over `Fin (#P₁)`: the `inP1 i = false`
summands vanish because `b i = 0` (clause 1 of `IsZeroReducibleVia`),
and the surviving `inP1 i = true` summands reindex through the order
embedding `zeroReducedEmb`. The per-stage derivative-weight agreement
is `derivativeWeight_zeroReduced`; the textbook restriction
`b̂_I = b_{emb I}` holds definitionally on `M.zeroReduced inP1`. -/
theorem zeroReduced_phiEquivalent {s : ℕ}
    (M : RKTableau s) {inP1 : Fin s → Bool}
    (h : M.IsZeroReducibleVia inP1) :
    PhiEquivalent M (M.zeroReduced inP1) := by
  intro t
  show ∑ i : Fin s, M.b i * M.derivativeWeight i t
      = ∑ I : Fin (Finset.univ.filter
                    (fun i : Fin s => inP1 i = true)).card,
          (M.zeroReduced inP1).b I
            * (M.zeroReduced inP1).derivativeWeight I t
  -- Step 1: discard `inP1 i = false` summands (their `M.b` factor is 0).
  have hStep1 :
      (∑ i : Fin s, M.b i * M.derivativeWeight i t)
        = ∑ i ∈ Finset.univ.filter (fun i : Fin s => inP1 i = true),
            M.b i * M.derivativeWeight i t := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi_notin
    have hiFalse : inP1 i = false := by
      have hiNotTrue : inP1 i ≠ true := fun hiT =>
        hi_notin (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiT⟩)
      cases hh : inP1 i with
      | false => rfl
      | true => exact absurd hh hiNotTrue
    rw [h.1 i hiFalse, zero_mul]
  rw [hStep1]
  -- Step 2: reindex the surviving `Fin s` sum back to `Fin sBar'` via
  -- `zeroReducedEmb`. Use `Finset.sum_bij` to avoid dependent-type issues
  -- with the RHS index type `Fin filter.card`.
  symm
  refine Finset.sum_bij
    (fun I _ => RKTableau.zeroReducedEmb inP1 I)
    (fun I _ => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, zeroReducedEmb_inP1_eq_true inP1 I⟩)
    (fun I₁ _ I₂ _ heq =>
      (RKTableau.zeroReducedEmb inP1).injective heq)
    ?_ ?_
  · intro b hb
    have hImg : Finset.image (RKTableau.zeroReducedEmb inP1) Finset.univ
          = Finset.univ.filter (fun i : Fin s => inP1 i = true) := by
      show Finset.image
        ⇑((Finset.univ.filter
              (fun i : Fin s => inP1 i = true)).orderEmbOfFin rfl)
        Finset.univ = _
      exact Finset.image_orderEmbOfFin_univ _ rfl
    have hbImg : b ∈ Finset.image
        (RKTableau.zeroReducedEmb inP1) Finset.univ := hImg.symm ▸ hb
    rcases Finset.mem_image.mp hbImg with ⟨I, hI_mem, hI_eq⟩
    exact ⟨I, hI_mem, hI_eq⟩
  · intro I _
    rw [derivativeWeight_zeroReduced M h t I]
    rfl

/-- *Φ-equivalence is implied by P-reduction.*

If `M` P-reduces (in zero or more steps) to `M'` — through any mix of
P-reduction (`step`) and 0-reduction (`zeroStep`) — then `M` and `M'`
agree on every elementary weight (def:381B). This formalises Butcher's
§380 narrative ("reducible methods agree on elementary weights"); the
implication is implicit in the textbook's treatment of
equivalence/reducibility but is not stated as a numbered result. -/
theorem PhiEquivalent.of_pReducesTo {s s' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'}
    (h : RKTableau.PReducesTo M M') : PhiEquivalent M M' := by
  induction h with
  | refl M => exact PhiEquivalent.refl M
  | step P _hLt hVia _hRest IH =>
      exact PhiEquivalent.trans (pReduced_phiEquivalent _ hVia) IH
  | zeroStep inP1 _hP0 hVia _hRest IH =>
      exact PhiEquivalent.trans (zeroReduced_phiEquivalent _ hVia) IH

end OpenMath.Chapter3.Section381

namespace OpenMath.Chapter3.Section312.RKTableau

open OpenMath.Chapter3.Section381

/-- Butcher §380 — `def:381F` ⇒ `def:381B`: P-equivalent methods are
Φ-equivalent. The easy direction of `thm:381H`. The reverse direction
(`PhiEquivalent → PEquivalent`) requires `thm:314A` (independence of
elementary differentials) and is genuinely harder; deferred. -/
theorem PEquivalent.toPhiEquivalent {s s' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'} :
    PEquivalent M M' → PhiEquivalent M M'
  | ⟨_, _, hM, hM'⟩ =>
      (PhiEquivalent.of_pReducesTo hM).trans
        (PhiEquivalent.of_pReducesTo hM').symm

/-- One-step bridge: any P-reduction induces Φ-equivalence between its
endpoints. Direct alias of `PhiEquivalent.of_pReducesTo` provided for
caller ergonomics, so downstream code can write `h.toPhiEquivalent` on
a `PReducesTo` hypothesis without first wrapping it in `PEquivalent`. -/
theorem PReducesTo.toPhiEquivalent {s s' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'} (h : PReducesTo M M') :
    PhiEquivalent M M' :=
  PhiEquivalent.of_pReducesTo h

end OpenMath.Chapter3.Section312.RKTableau

namespace OpenMath.Chapter3.Section381

open OpenMath.Chapter3.Section310 OpenMath.Chapter3.Section312

/-- Non-vacuity witness for Φ-equivalence under 0-reduction:
`paddedEuler` is Φ-equivalent to its 1-stage 0-reduced form. Consumes
`paddedEuler_pReducesTo_zeroReduced` through `PhiEquivalent.of_pReducesTo`,
exercising the `zeroStep` case of the latter's induction. Companion to
`paddedEuler_pEquivalent_zeroReduced` above. -/
theorem paddedEuler_phiEquivalent_zeroReduced :
    PhiEquivalent paddedEuler (paddedEuler.zeroReduced ![true, false]) :=
  PhiEquivalent.of_pReducesTo paddedEuler_pReducesTo_zeroReduced

/-- `paddedEuler` is Φ-equivalent to itself via the `def:381F → def:381B`
bridge applied to the reflexive P-equivalence witness. Trivial but exercises
`PEquivalent.toPhiEquivalent` on the canonical reflexive case. -/
theorem paddedEuler_phiEquivalent_self_via_PEquivalent :
    PhiEquivalent paddedEuler paddedEuler :=
  (RKTableau.PEquivalent.refl paddedEuler).toPhiEquivalent

/-- `paddedEuler` is Φ-equivalent to its 0-reduction via the
`def:381F → def:381B` bridge. Composes `paddedEuler_pEquivalent_zeroReduced`
with `PEquivalent.toPhiEquivalent`, giving an alternative derivation of
`paddedEuler_phiEquivalent_zeroReduced` that goes through the
P-equivalence intermediary. -/
theorem paddedEuler_phiEquivalent_zeroReduced_via_PEquivalent :
    PhiEquivalent paddedEuler
      (paddedEuler.zeroReduced ![true, false]) :=
  paddedEuler_pEquivalent_zeroReduced.toPhiEquivalent

/-- The 1-stage tableau `paddedEuler.pReduced pairPartition` is irreducible
(neither 0-reducible nor P-reducible). Lifted from the inline witness in
the `paddedEuler.PEquivalent paddedEuler` example earlier in this file
(cycle 188 era) so that downstream witnesses can cite it as a named
helper. Cycle 190 deliverable B prerequisite. -/
private theorem paddedEuler_pReduced_pairPartition_isIrreducible :
    (paddedEuler.pReduced pairPartition).IsIrreducible := by
  have hMidPReducedB :
      (paddedEuler.pReduced pairPartition).b 0 = 1 := by
    show (∑ i ∈ Finset.univ.filter
              (fun i : Fin 2 => pairPartition.block i = 0),
            paddedEuler.b i) = 1
    have hFilter :
        (Finset.univ.filter
            (fun i : Fin 2 => pairPartition.block i = 0))
          = Finset.univ := by
      ext i
      simp [pairPartition]
    rw [hFilter]
    simp [paddedEuler, Fin.sum_univ_two]
  refine ⟨?_, ?_⟩
  · rintro ⟨inP1, ⟨i, hiF⟩, hbZero, _⟩
    fin_cases i
    have hb0 : (paddedEuler.pReduced pairPartition).b 0 = 0 :=
      hbZero 0 hiF
    linarith [hMidPReducedB]
  · rintro ⟨sBar, hLt, P, _⟩
    obtain rfl : sBar = 0 := Nat.lt_one_iff.mp hLt
    exact (P.block 0).elim0

/-- Non-vacuity witness for `PEquivalent.eq_of_isIrreducible_of_middle`:
`paddedEuler` is P-equivalent to itself, witnessed via the common
irreducible middle `paddedEuler.pReduced pairPartition`. Exercises the
canonical-form constructor on a non-trivial heterogeneous-stage
(2 ↦ 1) reduction chain, going through both the new constructor and
the existing irreducibility witness. Cycle 190 deliverable B. -/
theorem paddedEuler_pEquivalent_self_via_pReduced :
    paddedEuler.PEquivalent paddedEuler :=
  RKTableau.PEquivalent.eq_of_isIrreducible_of_middle
    paddedEuler_pReduced_pairPartition_isIrreducible
    paddedEuler_pReducesTo_pReduced
    paddedEuler_pReducesTo_pReduced

/-- Non-vacuity witness for `PEquivalent.eq_of_both_isIrreducible`:
the 1-stage `paddedEuler.pReduced pairPartition` is irreducible and
P-equivalent (reflexively) to itself, so the canonical-form theorem
recovers the trivial `HEq` along the identity-stage axis. Exercises
the type-level heterogeneous-stage plumbing on a non-trivial
irreducible witness. Cycle 193 deliverable. -/
theorem paddedEuler_pReduced_pairPartition_eq_of_both_isIrreducible :
    ∃ heq : 1 = 1,
      HEq (paddedEuler.pReduced pairPartition)
          (paddedEuler.pReduced pairPartition) :=
  RKTableau.PEquivalent.eq_of_both_isIrreducible
    paddedEuler_pReduced_pairPartition_isIrreducible
    paddedEuler_pReduced_pairPartition_isIrreducible
    (RKTableau.PEquivalent.refl (paddedEuler.pReduced pairPartition))

/-- Non-vacuity witness for `PEquivalent.pReducesTo_of_right_isIrreducible`:
`paddedEuler.pReduced pairPartition` is irreducible (cycle 190 helper)
and `paddedEuler` is P-equivalent to it (cycle 188 via
`paddedEuler_pEquivalent_pReduced`), so the irreducible-endpoint
extraction theorem recovers the underlying P-reduction. The output
matches `paddedEuler_pReducesTo_pReduced` from cycle 186, confirming
the extraction lemma produces the expected reduct on the canonical
heterogeneous-stage example. Cycle 194 deliverable. -/
theorem paddedEuler_pReducesTo_pReduced_via_pEquivalent_extraction :
    paddedEuler.PReducesTo (paddedEuler.pReduced pairPartition) :=
  paddedEuler_pEquivalent_pReduced.pReducesTo_of_right_isIrreducible
    paddedEuler_pReduced_pairPartition_isIrreducible

/-- Non-vacuity witness for the homogeneous-stage corollary
`PEquivalent.eq_of_both_isIrreducible_homogeneous`: a single irreducible
1-stage method is equal to itself when extracted from its reflexive
P-equivalence witness via the new corollary. Trivial but exercises the
homogeneous-stage path through the `HEq → Eq` collapse. Cycle 194
deliverable. -/
example :
    paddedEuler.pReduced pairPartition = paddedEuler.pReduced pairPartition :=
  RKTableau.PEquivalent.eq_of_both_isIrreducible_homogeneous
    paddedEuler_pReduced_pairPartition_isIrreducible
    paddedEuler_pReduced_pairPartition_isIrreducible
    (RKTableau.PEquivalent.refl (paddedEuler.pReduced pairPartition))

/-- Non-vacuity witness for
`pEquivalent_irreducible_reduct_unique_of_sources_irreducible`: the
1-stage `paddedEuler.pReduced pairPartition` is irreducible (cycle 190
witness), so the cycle 199 sources-irreducible uniqueness theorem fires
on the trivial reflexive case where both `PReducesTo` chains and the
`PEquivalent` hypothesis are all reflexive. Exercises the cycle 188 ×
cycle 193 × `HEq.trans` composition path on a concrete irreducible
example. Cycle 199 deliverable. -/
example :
    (1 : ℕ) = 1 ∧
    HEq (paddedEuler.pReduced pairPartition)
        (paddedEuler.pReduced pairPartition) :=
  RKTableau.pEquivalent_irreducible_reduct_unique_of_sources_irreducible
    paddedEuler_pReduced_pairPartition_isIrreducible
    paddedEuler_pReduced_pairPartition_isIrreducible
    (RKTableau.PReducesTo.refl _)
    (RKTableau.PReducesTo.refl _)
    (RKTableau.PEquivalent.refl _)

/-- *Non-vacuity for `IsPReducible` destructors.* `paddedEuler` is
P-reducible (cycle 186 witness `paddedEuler_isPReducible`); the
destructors produce a partition whose codomain stage count is
strictly less than 2 (the stage count of `paddedEuler`). -/
example : paddedEuler_isPReducible.sBar < 2 :=
  paddedEuler_isPReducible.sBar_lt

/-- *Non-vacuity for `IsZeroReducible` destructors.* `paddedEuler` is
0-reducible (cycle 188 witness `paddedEuler_isZeroReducible`); the
destructors expose the strict-descent property
`(true-filter cardinality) < 2`. -/
example :
    (Finset.univ.filter
        (fun i : Fin 2 => paddedEuler_isZeroReducible.inP1 i = true)).card < 2 :=
  paddedEuler_isZeroReducible.zeroReduced_size_lt

end OpenMath.Chapter3.Section381
