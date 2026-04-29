import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Topology.Connected.Basic

/-!
# Butcher §355 — Order arrows and the Ehle barrier (def:355A)

This file formalises Definition 355A from Butcher's *Numerical Methods for
Ordinary Differential Equations* (3rd ed., page 264).

## Textbook statement (Definition 355A, quoted verbatim from `def_355A.json`)

> The locus of points in the complex plane for which `φ(z) = R(z) exp(−z)`
> is real and positive is said to be the 'order web' for the rational
> function `R`. The part of the order web connected to `0` is the
> 'principal order web'. The rays emanating from `0` with increasing
> value of `φ` are 'up arrows' and those emanating from `0` with
> decreasing `φ` are 'down arrows'.

## Faithfulness notes

* `phi R z := R z * Complex.exp (-z)` is Butcher's auxiliary `φ`.
* `orderWeb R := { z | (phi R z).im = 0 ∧ 0 < (phi R z).re }` encodes
  "real and positive" as the intersection of "imaginary part is 0" with
  "real part is strictly positive". This is exactly Butcher's "real and
  positive" since a complex number is a positive real iff its imaginary
  part is `0` and its real part is `> 0`.
* `principalOrderWeb R` is the connected component of `0` in
  `orderWeb R`, using Mathlib's `connectedComponentIn`.
* `IsUpArrow R γ` / `IsDownArrow R γ` encode "ray emanating from `0`
  with increasing/decreasing `φ`" as a function `γ : ℝ → ℂ` with
  `γ 0 = 0`, with `γ t ∈ orderWeb R` for all `t > 0`, and along which
  the (real) value of `φ ∘ γ` is strictly monotone (resp. anti-monotone)
  on `[0, ∞)`. The `t = 0` endpoint is excluded from the order-web
  membership clause because Butcher's "ray emanating from `0`" includes
  the origin as an endpoint, but `0` is in the order web only when
  `R(0) > 0` (in particular, `R(0)` real positive). For `R(z) = z + 1`
  the down arrow `γ(t) = t` has `γ 0 = 0`, `γ t > 0` for `t > 0`, and
  `φ(t) = (t+1)·exp(-t)` is real positive for all `t > -1`.
* We keep `R : ℂ → ℂ` an explicit parameter rather than tying these
  predicates to a `RKTableau`. Linking them via Butcher's formula
  `R(z) = 1 + z bᵀ (I − zA)⁻¹ 𝟏` is deferred to a later cycle that
  builds the `(I − zA)⁻¹` machinery.

The witness `phi_exp` shows that for the exact-flow stability function
`R(z) := exp(z)`, `φ(z) = 1` constantly, so `orderWeb` is all of `ℂ`
and `principalOrderWeb` contains `0`.
-/

namespace OpenMath.Chapter3.Section355

open Complex

/-- Butcher's auxiliary function `φ(z) = R(z) · exp(-z)` from the
preamble of Definition 355A. -/
noncomputable def phi (R : ℂ → ℂ) (z : ℂ) : ℂ := R z * Complex.exp (-z)

/-- Butcher Definition 355A — the *order web* of a stability function
`R`: the set of points `z ∈ ℂ` at which `φ(z) = R(z) · exp(-z)` is real
and strictly positive. -/
def orderWeb (R : ℂ → ℂ) : Set ℂ :=
  { z : ℂ | (phi R z).im = 0 ∧ 0 < (phi R z).re }

/-- Butcher Definition 355A — the *principal order web* of `R`: the
connected component of `0` inside the order web. -/
def principalOrderWeb (R : ℂ → ℂ) : Set ℂ :=
  connectedComponentIn (orderWeb R) 0

/-- Butcher Definition 355A — `γ : ℝ → ℂ` is an *up arrow* of the
stability function `R` if `γ` emanates from the origin (`γ 0 = 0`),
takes values in the order web of `R` for every positive parameter, and
the (real) value of `φ ∘ γ` is strictly monotone on `[0, ∞)`. -/
def IsUpArrow (R : ℂ → ℂ) (γ : ℝ → ℂ) : Prop :=
  γ 0 = 0 ∧
  (∀ t : ℝ, 0 < t → γ t ∈ orderWeb R) ∧
  StrictMonoOn (fun t : ℝ => (phi R (γ t)).re) (Set.Ici 0)

/-- Butcher Definition 355A — `γ : ℝ → ℂ` is a *down arrow* of the
stability function `R` if `γ` emanates from the origin (`γ 0 = 0`),
takes values in the order web of `R` for every positive parameter, and
the (real) value of `φ ∘ γ` is strictly anti-monotone on `[0, ∞)`. -/
def IsDownArrow (R : ℂ → ℂ) (γ : ℝ → ℂ) : Prop :=
  γ 0 = 0 ∧
  (∀ t : ℝ, 0 < t → γ t ∈ orderWeb R) ∧
  StrictAntiOn (fun t : ℝ => (phi R (γ t)).re) (Set.Ici 0)

/-! ## Concrete witnesses

For the exact-flow stability function `R(z) := exp(z)` we have
`φ(z) = exp(z) · exp(-z) = exp(0) = 1`, so the order web is all of `ℂ`
and contains `0`. -/

/-- `φ` of the exact-flow stability function `R(z) := exp(z)` equals
the constant `1`. -/
lemma phi_exp (z : ℂ) : phi Complex.exp z = 1 := by
  unfold phi
  rw [← Complex.exp_add]
  simp

/-- The order web of `R(z) := exp(z)` is all of `ℂ`. -/
lemma orderWeb_exp : orderWeb Complex.exp = Set.univ := by
  ext z
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  refine ⟨?_, ?_⟩ <;> rw [phi_exp]
  · exact Complex.one_im
  · simp [Complex.one_re]

/-- The origin lies in the order web of `R(z) := exp(z)`. -/
lemma zero_mem_orderWeb_exp : (0 : ℂ) ∈ orderWeb Complex.exp := by
  rw [orderWeb_exp]; trivial

/-- The origin lies in the principal order web of `R(z) := exp(z)`. -/
lemma zero_mem_principalOrderWeb_exp :
    (0 : ℂ) ∈ principalOrderWeb Complex.exp :=
  mem_connectedComponentIn zero_mem_orderWeb_exp

end OpenMath.Chapter3.Section355
