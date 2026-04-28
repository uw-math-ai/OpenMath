import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Butcher §110 — Existence and uniqueness of solutions

This file collects the entities of subsection 110 of Butcher's
*Numerical Methods for Ordinary Differential Equations* (3rd ed.).

Contents:

* `def:110A` — `LipschitzInSecond` (Lipschitz-in-second-variable predicate).
* `lem:110B` — `contraction_fixedPoint` (Banach contraction-mapping fixed-point theorem).
* `thm:110C` — `ode_solution_unique`, `ode_solution_exists`, and a
  combined packaging.
-/

namespace OpenMath.Chapter1.Section110

open scoped NNReal Topology
open Set Metric Filter

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

/-! ## Picard–Lindelöf existence and uniqueness (`thm:110C`)

Butcher (2008, Thm 110C, p. 44) states:

> Consider an initial value problem `y'(x) = f(x, y(x)), y(a) = y₀`,
> where `f : [a, b] × ℝ^N → ℝ^N` is continuous in its first variable
> and satisfies a Lipschitz condition in its second variable. Then there
> exists a unique solution to this problem.

We split the textbook statement into two halves (`ode_solution_unique` and
`ode_solution_exists`) plus a combined `∃ y, ... ∧ ∀ z, ...` packaging.
The existence half adopts Mathlib's `IsPicardLindelof` / `Picard–Lindelöf`
theorem and therefore needs an additional uniform bound on `‖f‖`
on a closed ball — this is documented in `ode_solution_exists`'s docstring
as a strengthening relative to Butcher's textbook hypothesis. The uniqueness
half is immediate from Mathlib's `ODE_solution_unique_of_mem_Icc_right`.
-/

variable {N : ℕ}

/-- Butcher §110, Theorem 110C (uniqueness half).

Two solutions of the initial value problem `y'(x) = f(x, y(x))`, `y(a) = y₀`,
defined on `[a, b]`, that agree at `x = a`, agree on the entire interval
`[a, b]`, provided `f` is Lipschitz-in-second on `[a, b]`.

This matches Butcher's textbook statement of uniqueness exactly: continuity in
`x` is implied by differentiability (`HasDerivWithinAt`), and the Lipschitz
hypothesis is `LipschitzInSecond (Icc a b) L f`. The derivative is taken
within `Set.Ici x` (i.e. the right-derivative within `[x, ∞)`) at every
`x ∈ Ico a b`, which is the natural shape for Mathlib's
`ODE_solution_unique_of_mem_Icc_right`. -/
theorem ode_solution_unique
    {a b : ℝ}
    {L : ℝ≥0}
    {f : ℝ → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    (hf : LipschitzInSecond (Set.Icc a b) L f)
    {y z : ℝ → EuclideanSpace ℝ (Fin N)}
    (hy_cont : ContinuousOn y (Set.Icc a b))
    (hy : ∀ x ∈ Set.Ico a b,
        HasDerivWithinAt y (f x (y x)) (Set.Ici x) x)
    (hz_cont : ContinuousOn z (Set.Icc a b))
    (hz : ∀ x ∈ Set.Ico a b,
        HasDerivWithinAt z (f x (z x)) (Set.Ici x) x)
    (h₀ : y a = z a) :
    Set.EqOn y z (Set.Icc a b) := by
  -- Convert `LipschitzInSecond (Icc a b) L f` to the `LipschitzOnWith` shape
  -- on the universal set, then apply Mathlib's right-bracket uniqueness.
  refine ODE_solution_unique_of_mem_Icc_right
    (s := fun _ => Set.univ)
    (K := L)
    ?hv hy_cont hy ?hfs hz_cont hz ?hgs h₀
  · intro t ht
    exact (hf t (Set.Ico_subset_Icc_self ht)).lipschitzOnWith
  · intro _ _; exact Set.mem_univ _
  · intro _ _; exact Set.mem_univ _

/-- Butcher §110, Theorem 110C (existence half).

There exists a function `y : ℝ → ℝ^N` with `y(a) = y₀` solving
`y'(x) = f(x, y(x))` on `[a, b]`, where `f : [a, b] × ℝ^N → ℝ^N` is
continuous in `x` and Lipschitz in `y`.

**Faithfulness flag.** Butcher's textbook hypothesis ("Lipschitz in its second
variable") is *global* (for all `Y, Z ∈ ℝ^N`) but does **not** include an
explicit norm bound on `f`. Mathlib's `IsPicardLindelof` API requires a
uniform bound `‖f t y‖ ≤ M` on a closed ball around `y₀` together with the
constraint `M * (b - a) ≤ a` (where `a` is the radius of the closed ball).
In Butcher's setting (`f` defined on `[a, b] × ℝ^N` with global Lipschitz),
such a bound exists and the textbook proof recovers it implicitly via the
Bielecki-norm Picard contraction over the *full* interval. Mathlib does not
yet expose a global-Lipschitz wrapper, so we add the bound and the radius as
extra hypotheses. See
`.prover-state/issues/picard_lindelof_bound_strengthening.md` for the gap.

The strengthening is mechanical: any `M` and `a` satisfying
`‖f t y‖ ≤ M` for `y ∈ closedBall y₀ a` and `M * (b - a) ≤ a` work. -/
theorem ode_solution_exists
    {a b : ℝ} (hab : a ≤ b)
    {L : ℝ≥0}
    {f : ℝ → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    (hf_lip  : LipschitzInSecond (Set.Icc a b) L f)
    (y₀ : EuclideanSpace ℝ (Fin N))
    (a_rad M_norm : ℝ≥0)
    (hf_cont : ∀ y ∈ Metric.closedBall y₀ a_rad,
        ContinuousOn (fun x => f x y) (Set.Icc a b))
    (hf_bound : ∀ x ∈ Set.Icc a b, ∀ y ∈ Metric.closedBall y₀ a_rad,
        ‖f x y‖ ≤ M_norm)
    (h_radius : M_norm * (b - a) ≤ a_rad) :
    ∃ y : ℝ → EuclideanSpace ℝ (Fin N),
        y a = y₀
      ∧ ∀ x ∈ Set.Icc a b,
          HasDerivWithinAt y (f x (y x)) (Set.Icc a b) x := by
  -- Package the hypotheses into `IsPicardLindelof` and invoke
  -- `exists_eq_forall_mem_Icc_hasDerivWithinAt₀`.
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  set t₀ : Set.Icc a b := ⟨a, ha⟩ with ht₀_def
  have hpl : IsPicardLindelof f (tmin := a) (tmax := b) t₀ y₀ a_rad 0 M_norm L := by
    refine
      { lipschitzOnWith := ?_
        continuousOn := ?_
        norm_le := ?_
        mul_max_le := ?_ }
    · intro t ht
      exact (hf_lip t ht).lipschitzOnWith
    · intro x hx
      exact hf_cont x hx
    · intro t ht y hy
      exact hf_bound t ht y hy
    · -- t₀ = a, so max (b - a) (a - a) = b - a (since a ≤ b)
      have h1 : (b - a : ℝ) ≥ 0 := sub_nonneg.mpr hab
      have h2 : (a - a : ℝ) = 0 := sub_self a
      have hmax : max ((b : ℝ) - (t₀ : ℝ)) ((t₀ : ℝ) - a) = b - a := by
        simp [ht₀_def, h1]
      simp [hmax, NNReal.coe_zero, sub_zero]
      exact_mod_cast h_radius
  obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨α, ?_, hα⟩
  -- α t₀ = y₀, and t₀ = ⟨a, ...⟩ so α a = y₀
  simpa [ht₀_def] using hα0

/-- Butcher §110, Theorem 110C — *Existence and uniqueness of solutions*
(combined packaging).

Verbatim textbook statement (Butcher 2008, p. 44):

> Consider an initial value problem `y'(x) = f(x, y(x)), y(a) = y₀`,
> where `f : [a, b] × ℝ^N → ℝ^N` is continuous in its first variable
> and satisfies a Lipschitz condition in its second variable. Then there
> exists a unique solution to this problem.

We package existence (`ode_solution_exists`) and uniqueness
(`ode_solution_unique`) into a single statement: there exists a solution `y`
on `[a, b]`, and any other solution `z` agrees with `y` on `[a, b]`.

The literal `∃!` packaging (over functions `ℝ → ℝ^N`) is awkward because
Butcher's uniqueness is only on `[a, b]`, not on the entire real line; so we
return uniqueness as `Set.EqOn y z (Icc a b)` instead of function equality.

Same `hf_bound` strengthening as `ode_solution_exists` applies. -/
theorem ode_existence_uniqueness
    {a b : ℝ} (hab : a ≤ b)
    {L : ℝ≥0}
    {f : ℝ → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    (hf_lip  : LipschitzInSecond (Set.Icc a b) L f)
    (y₀ : EuclideanSpace ℝ (Fin N))
    (a_rad M_norm : ℝ≥0)
    (hf_cont : ∀ y ∈ Metric.closedBall y₀ a_rad,
        ContinuousOn (fun x => f x y) (Set.Icc a b))
    (hf_bound : ∀ x ∈ Set.Icc a b, ∀ y ∈ Metric.closedBall y₀ a_rad,
        ‖f x y‖ ≤ M_norm)
    (h_radius : M_norm * (b - a) ≤ a_rad) :
    ∃ y : ℝ → EuclideanSpace ℝ (Fin N),
        (y a = y₀
          ∧ ∀ x ∈ Set.Icc a b,
              HasDerivWithinAt y (f x (y x)) (Set.Icc a b) x)
      ∧ ∀ z : ℝ → EuclideanSpace ℝ (Fin N),
          z a = y₀ →
          ContinuousOn z (Set.Icc a b) →
          (∀ x ∈ Set.Ico a b,
              HasDerivWithinAt z (f x (z x)) (Set.Ici x) x) →
          Set.EqOn y z (Set.Icc a b) := by
  obtain ⟨y, hy0, hy_deriv⟩ :=
    ode_solution_exists hab hf_lip y₀ a_rad M_norm hf_cont hf_bound h_radius
  refine ⟨y, ⟨hy0, hy_deriv⟩, ?_⟩
  intro z hz0 hz_cont hz_deriv
  -- Convert y's `Icc`-form derivative to `Ici`-form on `Ico a b`.
  have hy_cont : ContinuousOn y (Set.Icc a b) := fun x hx =>
    (hy_deriv x hx).continuousWithinAt
  have hy_deriv_Ici : ∀ x ∈ Set.Ico a b,
      HasDerivWithinAt y (f x (y x)) (Set.Ici x) x := by
    intro x hx
    have hx_Icc : x ∈ Set.Icc a b := Set.Ico_subset_Icc_self hx
    have h_mem : Set.Icc a b ∈ 𝓝[Set.Ici x] x := by
      -- For x ∈ Ico a b, [a, b] is a right-neighborhood of x.
      have h_sub : Set.Ico x b ⊆ Set.Icc a b := fun y hy =>
        ⟨le_trans hx.1 hy.1, le_of_lt hy.2⟩
      have h_Ico_mem : Set.Ico x b ∈ 𝓝[Set.Ici x] x := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        refine ⟨Set.Iio b, Iio_mem_nhds hx.2, ?_⟩
        intro y hy
        exact ⟨hy.2, hy.1⟩
      exact Filter.mem_of_superset h_Ico_mem h_sub
    exact (hy_deriv x hx_Icc).mono_of_mem_nhdsWithin h_mem
  exact ode_solution_unique hf_lip hy_cont hy_deriv_Ici hz_cont hz_deriv (hy0.trans hz0.symm)

end OpenMath.Chapter1.Section110
