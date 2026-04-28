import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Butcher §112 — Stiff differential equations

This file collects the entities of subsection 112 of Butcher's
*Numerical Methods for Ordinary Differential Equations* (3rd ed.).

This cycle introduces only Definition 112A. Subsequent cycles will add
`thm:112B` to this file.
-/

namespace OpenMath.Chapter1.Section112

/-- Butcher §112, Definition 112A — *one-sided Lipschitz condition*.

The textbook statement (Butcher 2008, p. 47):

> The function `f` satisfies a *one-sided Lipschitz condition*, with
> *one-sided Lipschitz constant* `ℓ` if for all `x ∈ [a, b]` and all
> `u, v ∈ ℝ^N`, `⟨f(x, u) - f(x, v), u - v⟩ ≤ ℓ ‖u - v‖²`.

We follow the same generalization pattern as `def:110A`:
* the closed interval `[a, b]` is replaced by an arbitrary `s : Set ℝ`;
* the concrete `ℝ^N` is replaced by an arbitrary real inner-product space `E`
  (the Butcher instance is recovered by `E = EuclideanSpace ℝ (Fin N)`,
  `s = Set.Icc a b`).

The constant `ℓ : ℝ` (not `ℝ≥0`) is intentional: one-sided Lipschitz
constants can be **negative**, and that is exactly when the condition is
strictly stronger than the two-sided Lipschitz condition (it gives
contractivity rather than mere boundedness of growth). This is a genuine
difference from `def:110A`, where `L : ℝ≥0` matched Mathlib's `LipschitzWith`
convention.

The constant `ℓ` is exposed as a parameter (matching the textbook's "with
one-sided Lipschitz constant `ℓ`"), not baked into an existential. The
existential variant `∃ ℓ, OneSidedLipschitzInSecond s ℓ f` is recoverable
downstream when needed. -/
def OneSidedLipschitzInSecond {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Set ℝ) (ℓ : ℝ) (f : ℝ → E → E) : Prop :=
  ∀ x ∈ s, ∀ Y Z : E, inner ℝ (f x Y - f x Z) (Y - Z) ≤ ℓ * ‖Y - Z‖ ^ 2

end OpenMath.Chapter1.Section112
