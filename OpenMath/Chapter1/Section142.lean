import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Butcher §142 — Powers of matrices

This file collects the entities of subsection 142 of Butcher's
*Numerical Methods for Ordinary Differential Equations* (3rd ed.).

This cycle introduces only Definition 142A. Subsequent cycles will add
`def:142B` (`convergent` matrix), `thm:142C/D/E/F` (characterizations of
power-boundedness via spectral radius / minimal polynomial / Jordan form)
to this file.
-/

namespace OpenMath.Chapter1.Section142

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

end OpenMath.Chapter1.Section142
