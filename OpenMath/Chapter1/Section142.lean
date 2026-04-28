import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Topology.Order

/-!
# Butcher §142 — Powers of matrices

This file collects the entities of subsection 142 of Butcher's
*Numerical Methods for Ordinary Differential Equations* (3rd ed.).

So far this file contains Definitions 142A (power-boundedness) and 142B
(convergent matrix). Subsequent cycles will add `thm:142C/D/E/F`
(characterizations of power-boundedness and convergence via spectral
radius / minimal polynomial / Jordan form).
-/

namespace OpenMath.Chapter1.Section142

open Filter Topology

/-- Butcher §142, Definition 142A — *power-boundedness* (a.k.a. *stable* matrix).

The textbook statement (Butcher 2008, p. 67):

> A square matrix `A` is *stable* if there exists a constant `C` such that for
> all `n = 0, 1, 2, …`, `‖A^n‖ ≤ C`.
>
> This property is often referred to as *power-boundedness*.

We follow the convention from `def:110A` and expose Butcher's "there exists a
constant `C`" as a *parameter* `M : ℝ`; the existential variant
`∃ M, PowerBounded M a` is recoverable downstream when needed.

The carrier is generalised from "square matrix" to an arbitrary
`SeminormedRing`. The Butcher instance is recovered by choosing
`A := Matrix n n ℝ` (or `Matrix n n ℂ`) with any submultiplicative matrix
norm — e.g. `Matrix.linftyOpNormedRing` from `Mathlib.Analysis.Matrix.Normed`,
or the Frobenius / spectral-radius-induced norm. The textbook is silent on
which matrix norm to use, and the predicate is norm-equivalence-invariant up
to changing the bound `M` (matrix norms on a finite-dimensional space are
all equivalent), so generalising the carrier rather than committing to a
specific matrix-norm definition is faithful to the textbook.

We deliberately do **not** define power-boundedness via spectral radius,
minimal polynomial, or Jordan normal form — those are characterization
*theorems* (`thm:142C`, `thm:142D`, `thm:142E`), not the definition. -/
def PowerBounded {A : Type*} [SeminormedRing A] (M : ℝ) (a : A) : Prop :=
  ∀ k : ℕ, ‖a ^ k‖ ≤ M

/-- Butcher §142, Definition 142B — *convergent* matrix.

The textbook statement (Butcher 2008, p. 67):

> A square matrix `A` is *convergent* if `lim_{n → ∞} A^n = 0`.

We use `Filter.Tendsto … atTop (𝓝 0)` — Mathlib's canonical spelling of
"the sequence has limit zero". The carrier is generalised from "square
matrix" to a `SeminormedRing`, matching `def:142A`'s carrier so that the
two definitions interoperate with the same matrix-norm instances. The
Butcher textbook instance is recovered exactly as for `PowerBounded`.

We deliberately do **not** define `Convergent` via spectral radius < 1,
the minimal polynomial having all roots in the open unit disc, the
Jordan form having diagonal entries in the open unit disc, or the
existence of a similarity making the operator norm strictly less than 1.
Each of those is one of the *equivalent characterizations* of
convergence (Butcher's Theorem 142D); encoding any of them as the
definition would make 142D a tautology. The definition must remain
`lim_{n → ∞} a^n = 0` verbatim. -/
def Convergent {A : Type*} [SeminormedRing A] (a : A) : Prop :=
  Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0)

end OpenMath.Chapter1.Section142
