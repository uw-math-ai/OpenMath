import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Picard–Lindelöf Existence and Uniqueness Theorem

We formalize the Picard–Lindelöf theorem (Iserles, *A First Course in the Numerical
Analysis of Differential Equations*, Theorem 1.1 / thm:110C):

> If f : [a,b] × E → E is continuous and satisfies a Lipschitz condition in its
> second variable, then the IVP y'(x) = f(x, y(x)), y(a) = y₀ has a unique solution.

We also formalize:
- **def:110A**: Lipschitz condition in the second variable (`IsLipschitzInSecondVar`)
- **Continuous dependence on initial data** (Iserles eq. (110c)):
  `‖y(t) - z(t)‖ ≤ ‖y(a) - z(a)‖ * exp(L * (t - a))`

The proofs wrap Mathlib's `Mathlib.Analysis.ODE.PicardLindelof` (existence via
contraction mapping) and `Mathlib.Analysis.ODE.Gronwall` (uniqueness and Gronwall
bounds).

## References

* Iserles, §1.1, pp. 43–45
* Entity IDs: def:110A, thm:110C
-/

open Set Metric MeasureTheory Real Filter
open scoped NNReal

/-! ## Definition: Lipschitz condition in the second variable (def:110A) -/

section LipschitzDef

variable {E : Type*} [NormedAddCommGroup E]

/-- **Lipschitz condition in the second variable** (Iserles Definition 1.1, def:110A).
The function `f : ℝ → E → E` satisfies a Lipschitz condition in its second variable
on `[a, b]` with constant `L` if `‖f x y - f x z‖ ≤ L * ‖y - z‖` for all
`x ∈ [a, b]` and `y, z : E`. -/
def IsLipschitzInSecondVar (f : ℝ → E → E) (L : ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Icc a b, ∀ y z : E, ‖f x y - f x z‖ ≤ L * ‖y - z‖

/-- The Lipschitz condition implies `LipschitzWith` for each fixed time `x ∈ [a,b]`. -/
lemma IsLipschitzInSecondVar.lipschitzWith {f : ℝ → E → E} {L : ℝ} {a b : ℝ}
    (hf : IsLipschitzInSecondVar f L a b) (hL : 0 ≤ L) {x : ℝ} (hx : x ∈ Icc a b) :
    LipschitzWith ⟨L, hL⟩ (f x) :=
  LipschitzWith.of_dist_le_mul fun y z => by
    simp only [NNReal.coe_mk, dist_eq_norm]
    exact hf x hx y z

/-- The Lipschitz condition implies `LipschitzOnWith` on any set for each fixed `x`. -/
lemma IsLipschitzInSecondVar.lipschitzOnWith {f : ℝ → E → E} {L : ℝ} {a b : ℝ}
    (hf : IsLipschitzInSecondVar f L a b) (hL : 0 ≤ L) {x : ℝ} (hx : x ∈ Icc a b)
    (s : Set E) :
    LipschitzOnWith ⟨L, hL⟩ (f x) s :=
  (hf.lipschitzWith hL hx).lipschitzOnWith

end LipschitzDef

/-! ## Picard–Lindelöf: Uniqueness, Existence, and Continuous Dependence -/

namespace PicardLindelof

section Uniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Picard–Lindelöf uniqueness** (Iserles Theorem 1.1, uniqueness part).
If `f` satisfies a Lipschitz condition in its second variable on `[a, b]`, then
two solutions of `y' = f(x, y)` on `[a, b]` with the same initial value at `a`
agree on `[a, b]`.

The derivative condition uses `HasDerivWithinAt ... (Ici t) t` on `Ico a b`,
matching the convention in Mathlib's Gronwall-based uniqueness theorems. -/
theorem unique {f : ℝ → E → E} {L : ℝ} {a b : ℝ}
    (hf_lip : IsLipschitzInSecondVar f L a b) (hL : 0 ≤ L)
    {y z : ℝ → E}
    (hy_cont : ContinuousOn y (Icc a b))
    (hy_deriv : ∀ t ∈ Ico a b, HasDerivWithinAt y (f t (y t)) (Ici t) t)
    (hz_cont : ContinuousOn z (Icc a b))
    (hz_deriv : ∀ t ∈ Ico a b, HasDerivWithinAt z (f t (z t)) (Ici t) t)
    (h_init : y a = z a) :
    EqOn y z (Icc a b) :=
  ODE_solution_unique_of_mem_Icc_right
    (s := fun _ => univ)
    (fun _ ht => (hf_lip.lipschitzWith hL (Ico_subset_Icc_self ht)).lipschitzOnWith)
    hy_cont hy_deriv (fun _ _ => trivial)
    hz_cont hz_deriv (fun _ _ => trivial) h_init

end Uniqueness

section ContinuousDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Continuous dependence on initial data** (Iserles eq. (110c)).
If `y` and `z` solve the same ODE `y' = f(x, y)` with `f` Lipschitz in `y`, then
the distance between solutions is bounded by the initial distance times an exponential:
`‖y(t) - z(t)‖ ≤ ‖y(a) - z(a)‖ * exp(L * (t - a))` for all `t ∈ [a, b]`. -/
theorem continuous_dependence {f : ℝ → E → E} {L : ℝ} {a b : ℝ}
    (hf_lip : IsLipschitzInSecondVar f L a b) (hL : 0 ≤ L)
    {y z : ℝ → E}
    (hy_cont : ContinuousOn y (Icc a b))
    (hy_deriv : ∀ t ∈ Ico a b, HasDerivWithinAt y (f t (y t)) (Ici t) t)
    (hz_cont : ContinuousOn z (Icc a b))
    (hz_deriv : ∀ t ∈ Ico a b, HasDerivWithinAt z (f t (z t)) (Ici t) t)
    (t : ℝ) (ht : t ∈ Icc a b) :
    ‖y t - z t‖ ≤ ‖y a - z a‖ * exp (L * (t - a)) := by
  have := dist_le_of_trajectories_ODE_of_mem
    (K := ⟨L, hL⟩)
    (s := fun _ => univ)
    (fun t ht => (hf_lip.lipschitzWith hL (Ico_subset_Icc_self ht)).lipschitzOnWith)
    hy_cont hy_deriv (fun _ _ => trivial)
    hz_cont hz_deriv (fun _ _ => trivial)
    (le_refl _) t ht
  simp only [NNReal.coe_mk, dist_eq_norm] at this
  exact this

end ContinuousDependence

section Perturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Perturbation bound** for Lipschitz ODEs (connects to Iserles §1.1).
If `y` solves `y' = f(t, y)` exactly and `z` satisfies `z' ≈ f(t, z)` with
defect at most `ε`, then the distance between `y` and `z` is bounded by
`gronwallBound ‖y(a) - z(a)‖ L ε (t - a)`.

When `L > 0`, this equals `‖y(a)-z(a)‖ * exp(L*(t-a)) + (ε/L)*(exp(L*(t-a))-1)`.
This is the foundation for convergence analysis of numerical methods. -/
theorem perturbation_bound {f : ℝ → E → E} {L : ℝ} {a b : ℝ}
    (hf_lip : IsLipschitzInSecondVar f L a b) (hL : 0 ≤ L)
    {y z : ℝ → E} {z' : ℝ → E} {ε : ℝ}
    (hy_cont : ContinuousOn y (Icc a b))
    (hy_deriv : ∀ t ∈ Ico a b, HasDerivWithinAt y (f t (y t)) (Ici t) t)
    (hz_cont : ContinuousOn z (Icc a b))
    (hz_deriv : ∀ t ∈ Ico a b, HasDerivWithinAt z (z' t) (Ici t) t)
    (hz_approx : ∀ t ∈ Ico a b, ‖z' t - f t (z t)‖ ≤ ε) :
    ∀ t ∈ Icc a b,
      ‖y t - z t‖ ≤ gronwallBound ‖y a - z a‖ L ε (t - a) := by
  have key := dist_le_of_approx_trajectories_ODE_of_mem
    (K := ⟨L, hL⟩)
    (s := fun _ => univ)
    (f' := fun t => f t (y t))
    (εf := 0) (εg := ε)
    (fun _ ht => (hf_lip.lipschitzWith hL (Ico_subset_Icc_self ht)).lipschitzOnWith)
    hy_cont hy_deriv
    (fun _ _ => by simp [dist_self])
    (fun _ _ => trivial)
    hz_cont hz_deriv
    (fun t ht => by rw [dist_eq_norm]; exact hz_approx t ht)
    (fun _ _ => trivial)
    (le_refl _)
  intro t ht
  have h := key t ht
  rw [zero_add, dist_eq_norm, dist_eq_norm] at h
  simpa only [NNReal.coe_mk] using h

end Perturbation

/-- Convert `HasDerivWithinAt` on `Icc a b` to `HasDerivWithinAt` on `Ici t`
for `t ∈ Ico a b`. At interior points this follows from `HasDerivAt`;
at the left endpoint `a` the within-filters coincide when `a < b`. -/
lemma hasDerivWithinAt_Icc_to_Ici {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ℝ → E} {y' : E} {a b : ℝ} {t : ℝ}
    (hab : a < b) (ht : t ∈ Ico a b)
    (hd : HasDerivWithinAt y y' (Icc a b) t) :
    HasDerivWithinAt y y' (Ici t) t := by
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · exact hd.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hab)
  · exact (hd.hasDerivAt (Icc_mem_nhds hat ht.2)).hasDerivWithinAt

section Existence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private lemma exists_solution_small {f : ℝ → E → E} {L : ℝ} {a b : ℝ} {y₀ : E}
    (hab : a < b) (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))
    (hf_lip : IsLipschitzInSecondVar f L a b) (hL : 0 ≤ L) (hLδ : L * (b - a) < 1) :
    ∃ y : ℝ → E, y a = y₀ ∧ ContinuousOn y (Icc a b) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt y (f t (y t)) (Icc a b) t := by
  have hpair_cont : Continuous (fun t : ℝ => (t, y₀)) := by
    fun_prop
  have hy0_cont : ContinuousOn (fun t => f t y₀) (Icc a b) :=
    (hf_cont.comp hpair_cont).continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hy0_cont
  have hC0 : 0 ≤ C := by
    have hCa := hC a (left_mem_Icc.mpr (le_of_lt hab))
    exact le_trans (norm_nonneg _) hCa
  let δ : ℝ := b - a
  have hδnonneg : 0 ≤ δ := sub_nonneg.mpr (le_of_lt hab)
  have hden : 0 < 1 - L * δ := sub_pos.mpr (by simpa [δ] using hLδ)
  let R : ℝ := C * δ / (1 - L * δ)
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    exact div_nonneg (mul_nonneg hC0 hδnonneg) (le_of_lt hden)
  let K : ℝ≥0 := ⟨L, hL⟩
  let Rn : ℝ≥0 := ⟨R, hRnonneg⟩
  let B : ℝ := C + L * R
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  let Bn : ℝ≥0 := ⟨B, hBnonneg⟩
  let t0 : Icc a b := ⟨a, left_mem_Icc.mpr (le_of_lt hab)⟩
  have hcont_ball : ∀ x ∈ closedBall y₀ R, ContinuousOn (fun t => f t x) (Icc a b) := by
    intro x hx
    have hpair_cont' : Continuous (fun t : ℝ => (t, x)) := by
      fun_prop
    exact (hf_cont.comp hpair_cont').continuousOn
  have hnorm : ∀ t ∈ Icc a b, ∀ x ∈ closedBall y₀ R, ‖f t x‖ ≤ B := by
    intro t ht x hx
    have h1 := hC t ht
    have h2 := hf_lip t ht x y₀
    have hx' : ‖x - y₀‖ ≤ R := by
      simpa [mem_closedBall, dist_eq_norm, sub_eq_add_neg] using hx
    calc
      ‖f t x‖ ≤ ‖f t x - f t y₀‖ + ‖f t y₀‖ := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          norm_add_le (f t x - f t y₀) (f t y₀)
      _ ≤ L * ‖x - y₀‖ + C := by
        gcongr
      _ ≤ L * R + C := by
        gcongr
      _ = B := by
        ring
  have hmul : B * max (b - (t0 : ℝ)) ((t0 : ℝ) - a) ≤ R - (0 : ℝ) := by
    dsimp [t0, R, B, δ]
    simp [max_eq_left (sub_nonneg.mpr (le_of_lt hab))]
    have hne : 1 - L * (b - a) ≠ 0 := ne_of_gt hden
    field_simp [hne]
    ring_nf
    exact le_rfl
  have hpl : IsPicardLindelof f t0 y₀ Rn (0 : ℝ≥0) Bn K := by
    refine IsPicardLindelof.mk ?_ hcont_ball ?_ ?_
    · intro t ht
      exact (hf_lip.lipschitzWith hL ht).lipschitzOnWith
    · simpa using hnorm
    · simpa [K, Rn, Bn] using hmul
  obtain ⟨α, hα, hαcont⟩ :=
    IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn hpl
  let y : ℝ → E := fun t => α (y₀, t)
  have hy0mem : y₀ ∈ closedBall y₀ (0 : ℝ) := by
    simpa using mem_closedBall_self (show (0 : ℝ) ≤ 0 by simp)
  have hy_init : y a = y₀ := by
    simpa [y, t0] using (hα y₀ hy0mem).1
  have hy_cont : ContinuousOn y (Icc a b) := by
    have hp : ContinuousOn (fun t : ℝ => (y₀, t)) (Icc a b) := by
      fun_prop
    refine hαcont.comp hp ?_
    intro t ht
    exact ⟨by simpa [mem_closedBall, dist_eq_norm] using hy0mem, ht⟩
  have hy_deriv : ∀ t ∈ Icc a b, HasDerivWithinAt y (f t (y t)) (Icc a b) t := by
    intro t ht
    simpa [y] using (hα y₀ hy0mem).2 t ht
  exact ⟨y, hy_init, hy_cont, hy_deriv⟩

/-- **Picard–Lindelöf existence** (Iserles Theorem 1.1, existence part).
If `f` is continuous and Lipschitz in its second variable on `[a, b]`, then
the IVP `y' = f(x, y(x)), y(a) = y₀` has a solution on `[a, b]`.

The proof constructs Mathlib's `IsPicardLindelof` data on subintervals where
`L * δ < 1`, then chains solutions via uniqueness. The details are deferred
to a future cycle; the well-typed sorry preserves the proof structure. -/
theorem exists_solution {f : ℝ → E → E} {L : ℝ} {a b : ℝ} {y₀ : E}
    (hab : a < b)
    (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))
    (hf_lip : IsLipschitzInSecondVar f L a b)
    (hL : 0 ≤ L) :
    ∃ y : ℝ → E, y a = y₀ ∧ ContinuousOn y (Icc a b) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt y (f t (y t)) (Icc a b) t := by
  by_cases hLδ : L * (b - a) < 1
  · exact exists_solution_small hab hf_cont hf_lip hL hLδ
  · /-
    General case: subdivide `[a,b]` into finitely many subintervals of length `δ`
    with `L * δ < 1`, solve on each piece using `exists_solution_small`, then glue
    the solutions using `unique`.
    -/
    sorry

/-- **Picard–Lindelöf theorem** (Iserles Theorem 1.1, thm:110C).
Combining existence and uniqueness: if `f` is continuous and Lipschitz in `y`,
then the IVP `y' = f(x, y), y(a) = y₀` has a solution, and any two solutions
with the same initial data agree on `[a, b]`. -/
theorem exists_unique {f : ℝ → E → E} {L : ℝ} {a b : ℝ} {y₀ : E}
    (hab : a < b)
    (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))
    (hf_lip : IsLipschitzInSecondVar f L a b)
    (hL : 0 ≤ L) :
    ∃ y : ℝ → E, y a = y₀ ∧ ContinuousOn y (Icc a b) ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt y (f t (y t)) (Icc a b) t) ∧
      (∀ z : ℝ → E, z a = y₀ → ContinuousOn z (Icc a b) →
        (∀ t ∈ Ico a b, HasDerivWithinAt z (f t (z t)) (Ici t) t) →
        EqOn y z (Icc a b)) := by
  obtain ⟨y, hy_init, hy_cont, hy_deriv⟩ := exists_solution hab hf_cont hf_lip hL
  exact ⟨y, hy_init, hy_cont, hy_deriv, fun z hz_init hz_cont hz_deriv =>
    unique hf_lip hL hy_cont
      (fun t ht => hasDerivWithinAt_Icc_to_Ici hab ht (hy_deriv t (Ico_subset_Icc_self ht)))
      hz_cont hz_deriv (hy_init.trans hz_init.symm)⟩

end Existence

end PicardLindelof
