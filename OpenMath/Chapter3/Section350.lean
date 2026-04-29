import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Polyrith

/-!
# Butcher §350 — A-stability, A(α)-stability and L-stability (def:350A)

This file formalises Definition 350A from Butcher's *Numerical Methods for
Ordinary Differential Equations* (3rd ed., page 251).

## Textbook statement (Definition 350A, quoted verbatim from `def_350A.json`)

> Let `α` denote an angle satisfying `α ∈ (0, π)` and let `S(α)` denote
> the set of points `x + iy` in the complex plane such that `x ≤ 0` and
> `−tan(α)|x| ≤ y ≤ tan(α)|x|`. A Runge–Kutta method with stability
> function `R(z)` is `A(α)`-stable if `|R(z)| ≤ 1` for all `z ∈ S(α)`.

The same subsection (Butcher §350, surrounding context — see the
`context_latex` field of the JSON) introduces:

* **A-stability**: `|R(z)| ≤ 1` for all `z` with `Re(z) ≤ 0`.
* **L-stability**: A-stable, and additionally `R(z) → 0` as
  `Re(z) → −∞` (Butcher's `R(∞) = 0` in the JSON `context_latex`).

## Faithfulness notes

* The set `S(α)` is encoded as
  `{ z | z.re ≤ 0 ∧ |z.im| ≤ tan α * |z.re| }`. Butcher writes
  `−tan(α)|x| ≤ y ≤ tan(α)|x|`, i.e. `|y| ≤ tan(α)|x|`. This is the
  same condition since for `α ∈ (0, π/2]` we have `tan α ≥ 0`, and the
  symmetric inequality on `y` is exactly `|y| ≤ tan(α)|x|`. (For
  `α ∈ (π/2, π)`, `tan α` is negative; the textbook implicitly works
  with `α ∈ (0, π/2]` for stability sectors. We retain Butcher's
  literal range `α ∈ (0, π)` in `IsAlphaStable` and let the predicate
  trivialise for `α ∈ (π/2, π)`.)
* We keep `R : ℂ → ℂ` an explicit parameter rather than tying these
  predicates to an `RKTableau`. Linking them via Butcher's formula
  `R(z) = 1 + z bᵀ (I − zA)⁻¹ 𝟏` (eq. 350a) is deferred to a later
  cycle that builds the `(I − zA)⁻¹` machinery.
* For `IsLStable` we encode "as `Re(z) → −∞`" by tendency along the
  negative real axis (Filter.atBot on the real coordinate of `z`).
  This is equivalent to Butcher's `R(∞) = 0` in his stability-region
  context, since `R` for an RK method is rational and the limit on
  the negative real axis equals the limit at infinity in the
  Riemann-sphere sense Butcher uses.
-/

namespace OpenMath.Chapter3.Section350

open Complex

/-- The closed sector `S(α) ⊂ ℂ` of Butcher Definition 350A: points
`x + iy` with `x ≤ 0` and `|y| ≤ tan(α) · |x|`. -/
def stabilitySector (α : ℝ) : Set ℂ :=
  { z : ℂ | z.re ≤ 0 ∧ |z.im| ≤ Real.tan α * |z.re| }

/-- Butcher Definition 350A — `A(α)`-stability of a stability function
`R`: the angle `α` lies in `(0, π)`, and `|R(z)| ≤ 1` for every `z` in
the sector `S(α)`. -/
def IsAlphaStable (α : ℝ) (R : ℂ → ℂ) : Prop :=
  α ∈ Set.Ioo 0 Real.pi ∧ ∀ z ∈ stabilitySector α, ‖R z‖ ≤ 1

/-- Butcher Definition 350A — `A`-stability of a stability function
`R`: `|R(z)| ≤ 1` on the closed left half-plane. -/
def IsAStable (R : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, z.re ≤ 0 → ‖R z‖ ≤ 1

/-- Butcher Definition 350A — `L`-stability of a stability function `R`:
`A`-stable, with `R` tending to `0` along the negative real axis (the
Mathlib spelling of Butcher's `R(∞) = 0` in the §350 context). -/
def IsLStable (R : ℂ → ℂ) : Prop :=
  IsAStable R ∧ Filter.Tendsto (fun x : ℝ => R (x : ℂ))
    Filter.atBot (nhds 0)

/-! ## Basic API: L-stable implies A-stable -/

lemma IsLStable.isAStable {R : ℂ → ℂ} (h : IsLStable R) : IsAStable R :=
  h.1

/-! ## Concrete witnesses

The CLAUDE.md "concrete witness" rule asks for at least one non-vacuous
instance per new definition. We exhibit:

* The constant function `R(z) := 0` is A-stable and L-stable.
* The implicit-Euler stability function `R(z) := 1 / (1 − z)` is
  A-stable. (This is the canonical worked example in Butcher §35x.)
-/

/-- The zero stability function `R(z) := 0` is A-stable. -/
lemma isAStable_zero : IsAStable (fun _ : ℂ => 0) := by
  intro z _
  simp

/-- The zero stability function `R(z) := 0` is L-stable. -/
lemma isLStable_zero : IsLStable (fun _ : ℂ => 0) := by
  refine ⟨isAStable_zero, ?_⟩
  exact (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℂ))
    Filter.atBot (nhds 0))

/-- Auxiliary: under `Re z ≤ 0`, the squared norm `‖1 - z‖²` is at
least `1`. -/
lemma one_le_normSq_one_sub {z : ℂ} (hz : z.re ≤ 0) :
    1 ≤ Complex.normSq (1 - z) := by
  have hsub_re : (1 - z).re = 1 - z.re := by simp
  have hsub_im : (1 - z).im = -z.im := by simp
  have hxle : 1 ≤ (1 - z.re) := by linarith
  have hxsq : 1 ≤ (1 - z.re) ^ 2 := by
    have h1 : (0 : ℝ) ≤ 1 := by norm_num
    nlinarith [sq_nonneg (1 - z.re), sq_nonneg z.re, sq_nonneg z.im]
  have hnsq : Complex.normSq (1 - z) = (1 - z.re) ^ 2 + (-z.im) ^ 2 := by
    rw [Complex.normSq_apply, hsub_re, hsub_im]
    ring
  rw [hnsq]
  nlinarith [sq_nonneg (-z.im), sq_nonneg z.im, hxsq]

/-- Auxiliary: under `Re z ≤ 0`, `‖1 - z‖ ≥ 1`. -/
lemma one_le_norm_one_sub {z : ℂ} (hz : z.re ≤ 0) :
    1 ≤ ‖(1 : ℂ) - z‖ := by
  have h := one_le_normSq_one_sub hz
  have hnorm : ‖(1 : ℂ) - z‖ ^ 2 = Complex.normSq (1 - z) :=
    Complex.sq_norm (1 - z)
  have h2 : (1 : ℝ) ≤ ‖(1 : ℂ) - z‖ ^ 2 := by rw [hnorm]; exact h
  have hnn : 0 ≤ ‖(1 : ℂ) - z‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖(1 : ℂ) - z‖ - 1), hnn, h2]

/-- The implicit-Euler stability function `R(z) := 1 / (1 − z)` is
A-stable. (Standard worked example from Butcher §35x.) -/
lemma isAStable_implicitEuler :
    IsAStable (fun z : ℂ => 1 / (1 - z)) := by
  intro z hz
  -- ‖1 / (1 - z)‖ = 1 / ‖1 - z‖ ≤ 1, since ‖1 - z‖ ≥ 1.
  have hnorm : 1 ≤ ‖(1 : ℂ) - z‖ := one_le_norm_one_sub hz
  have hpos : (0 : ℝ) < ‖(1 : ℂ) - z‖ := lt_of_lt_of_le one_pos hnorm
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpos
    exact lt_irrefl 0 hpos
  rw [norm_div, norm_one]
  rw [div_le_one hpos]
  exact hnorm

end OpenMath.Chapter3.Section350
