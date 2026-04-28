import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Butcher §110 — Existence and uniqueness of solutions

This file collects the entities of subsection 110 of Butcher's
*Numerical Methods for Ordinary Differential Equations* (3rd ed.).

So far this file contains Definition 110A (Lipschitz-in-second) and
Lemma 110B (Banach contraction-mapping fixed-point theorem). The Picard
existence/uniqueness theorem `thm:110C` will be added in a later cycle.
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

/-- Butcher §110, Lemma 110B — *Banach contraction-mapping fixed-point theorem*.

The textbook statement (Butcher 2008, p. 43):

> Let `M` denote a complete metric space with metric `ρ` and let
> `φ : M → M` denote a mapping which is a contraction, in the sense that
> there exists a number `k`, satisfying `0 ≤ k < 1`, such that for any
> `η, ζ ∈ M`, `ρ(φ(η), φ(ζ)) ≤ k ρ(η, ζ)`. Then there exists a unique
> `ξ ∈ M` such that `φ(ξ) = ξ`.

This is a thin wrapper around Mathlib's `ContractingWith.fixedPoint` and
`ContractingWith.fixedPoint_unique'`; it merely repackages the API in
Butcher's `∃!` form for downstream use in the Picard existence/uniqueness
theorem `thm:110C`.

Hypothesis notes:
* `k : ℝ≥0` rather than `k : ℝ` matches Mathlib's `LipschitzWith` convention.
  Butcher's `0 ≤ k` half is built into the type; the `k < 1` half is the
  `hk` argument.
* `[Nonempty M]` is required by Mathlib (and is implicit in the textbook —
  on an empty space the existential conclusion is vacuously false). -/
lemma contraction_fixedPoint
    {M : Type*} [MetricSpace M] [CompleteSpace M] [Nonempty M]
    {k : ℝ≥0} (hk : k < 1) {φ : M → M} (hφ : LipschitzWith k φ) :
    ∃! ξ : M, φ ξ = ξ := by
  have hcw : ContractingWith k φ := ⟨hk, hφ⟩
  refine ⟨hcw.fixedPoint φ, ?_, ?_⟩
  · exact hcw.fixedPoint_isFixedPt
  · intro ξ hξ
    exact hcw.fixedPoint_unique' hξ hcw.fixedPoint_isFixedPt

end OpenMath.Chapter1.Section110
