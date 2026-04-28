import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Butcher §110 — Existence and uniqueness of solutions

This file collects the entities of subsection 110 of Butcher's
*Numerical Methods for Ordinary Differential Equations* (3rd ed.).

This cycle introduces only Definition 110A. Subsequent cycles will add
`lem:110B` (contraction mapping principle) and `thm:110C` (Picard
existence/uniqueness) to this file.
-/

namespace OpenMath.Chapter1.Section110

open scoped NNReal

/-- Butcher §110, Definition 110A — *Lipschitz condition in its second variable*.

The textbook statement (Butcher 2008, p. 43):

> The function `f : [a, b] × ℝ^N → ℝ^N` is said to satisfy a *Lipschitz
> condition in its second variable* if there exists a constant `L`, known as a
> *Lipschitz constant*, such that for any `x ∈ [a, b]` and `Y, Z ∈ ℝ^N`,
> `‖f(x, Y) - f(x, Z)‖ ≤ L ‖Y - Z‖`.

We follow the planner's recommended Lean form: keep the second-variable domain
`E` and codomain `F` polymorphic over `PseudoEMetricSpace`, take `s : Set ℝ`
in place of the closed interval `[a, b]`, and parameterise by `L : ℝ≥0`. The
Butcher textbook instance is recovered by choosing
`s = Set.Icc a b` and `E = F = EuclideanSpace ℝ (Fin N)`.

The Lipschitz constant `L` is exposed as a parameter (matching Butcher's
"there exists a constant `L`") rather than baked into an existential, so that
downstream constructive proofs (e.g. Picard) can extract it directly. The
existential variant is `∃ L, LipschitzInSecond s L f`. -/
def LipschitzInSecond {E F : Type*}
    [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    (s : Set ℝ) (L : ℝ≥0) (f : ℝ → E → F) : Prop :=
  ∀ x ∈ s, LipschitzWith L (f x)

end OpenMath.Chapter1.Section110
