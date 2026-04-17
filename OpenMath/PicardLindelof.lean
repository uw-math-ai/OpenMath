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

/-- Restriction of the Lipschitz condition to a sub-interval `[c, d] ⊆ [a, b]`. -/
lemma IsLipschitzInSecondVar.mono_Icc {f : ℝ → E → E} {L : ℝ} {a b c d : ℝ}
    (hf : IsLipschitzInSecondVar f L a b) (hca : a ≤ c) (hdb : d ≤ b) :
    IsLipschitzInSecondVar f L c d :=
  fun x hx y z => hf x ⟨le_trans hca hx.1, le_trans hx.2 hdb⟩ y z

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

private lemma exists_solution_short {f : ℝ → E → E} {L : ℝ} {a b : ℝ} {y₀ : E}
    (hab : a ≤ b)
    (hLab : L * (b - a) < 1)
    (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))
    (hf_lip : IsLipschitzInSecondVar f L a b)
    (hL : 0 ≤ L) :
    ∃ y : ℝ → E, y a = y₀ ∧ ContinuousOn y (Icc a b) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt y (f t (y t)) (Icc a b) t := by
  obtain ⟨M₀, M₀_mem, hM₀⟩ : ∃ M₀ ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ‖f t y₀‖ ≤ ‖f M₀ y₀‖ := by
    exact (IsCompact.exists_isMaxOn CompactIccSpace.isCompact_Icc
      ⟨a, Set.left_mem_Icc.mpr hab⟩
      (show ContinuousOn (fun t => ‖f t y₀‖) (Set.Icc a b) from
        hf_cont.norm.comp_continuousOn (continuousOn_id.prodMk continuousOn_const)))
  set R_real := ‖f M₀ y₀‖ * (b - a) / (1 - L * (b - a))
  set M_real := ‖f M₀ y₀‖ / (1 - L * (b - a))
  have h_data : ∃ (R_nn : NNReal) (M_nn K_nn : NNReal),
      IsPicardLindelof f ⟨a, left_mem_Icc.mpr hab⟩ y₀ R_nn 0 M_nn K_nn := by
    refine' ⟨⟨R_real, div_nonneg (mul_nonneg (norm_nonneg _) (sub_nonneg.mpr hab))
      (sub_nonneg.mpr hLab.le)⟩, ⟨M_real, div_nonneg (norm_nonneg _)
      (sub_nonneg.mpr hLab.le)⟩, ⟨L, hL⟩, _, _, _, _⟩ <;> norm_num
    · exact fun t ht₁ ht₂ => hf_lip.lipschitzOnWith hL ⟨ht₁, ht₂⟩ _
    · exact fun x hx => hf_cont.comp_continuousOn (continuousOn_id.prodMk continuousOn_const)
    · intro t ht₁ ht₂ x hx
      have h_dist : ‖f t x - f t y₀‖ ≤ L * ‖x - y₀‖ := by
        exact hf_lip t ⟨ht₁, ht₂⟩ x y₀
      rw [dist_eq_norm] at hx
      rw [le_div_iff₀] at * <;> nlinarith [norm_sub_norm_le (f t x) (f t y₀), hM₀ t ⟨ht₁, ht₂⟩]
    · rw [max_eq_left (by linarith), div_mul_eq_mul_div, div_le_div_iff_of_pos_right]; linarith
  obtain ⟨R_nn, M_nn, K_nn, h⟩ := h_data
  obtain ⟨α, hα₁, hα₂⟩ := h.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα₁, fun t ht => (hα₂ t ht |> HasDerivWithinAt.continuousWithinAt), hα₂⟩

private lemma exists_solution_concat {f : ℝ → E → E} {a b c : ℝ} {y₀ : E}
    (hac : a ≤ c) (hcb : c ≤ b)
    (h1 : ∃ y : ℝ → E, y a = y₀ ∧ ContinuousOn y (Icc a c) ∧
      ∀ t ∈ Icc a c, HasDerivWithinAt y (f t (y t)) (Icc a c) t)
    (h2 : ∀ w : E, ∃ z : ℝ → E, z c = w ∧ ContinuousOn z (Icc c b) ∧
      ∀ t ∈ Icc c b, HasDerivWithinAt z (f t (z t)) (Icc c b) t) :
    ∃ y : ℝ → E, y a = y₀ ∧ ContinuousOn y (Icc a b) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt y (f t (y t)) (Icc a b) t := by
  obtain ⟨y, hy₀, hy_cont, hy_deriv⟩ := h1
  obtain ⟨z, hz₀, hz_cont, hz_deriv⟩ := h2 (y c)
  refine' ⟨fun t => if t ≤ c then y t else z t, _, _, _⟩
  · grind +locals
  · refine' ContinuousOn.if _ _ _
    · erw [frontier_Iic]; aesop
    · refine' hy_cont.mono _
      simp +decide [Set.subset_def, Set.Iic_def]
      exact fun x hx₁ hx₂ hx₃ => ⟨hx₁, hx₃⟩
    · refine' hz_cont.mono _
      simp +decide [Set.subset_def, Set.Icc_def, Set.Ioi_def]
      exact fun x hx₁ hx₂ hx₃ => ⟨hx₃, hx₂⟩
  · intro t ht
    by_cases htc : t = c
    · have h_deriv_c : HasDerivWithinAt (fun t => if t ≤ c then y t else z t)
          (f c (y c)) (Icc a c) c ∧ HasDerivWithinAt (fun t => if t ≤ c then y t else z t)
          (f c (z c)) (Icc c b) c := by
        constructor
        · have := hy_deriv c ⟨by linarith, by linarith⟩
          exact this.congr (fun x hx => by aesop) (by aesop)
        · have h_deriv_c : HasDerivWithinAt z (f c (z c)) (Icc c b) c := by
            exact hz_deriv c ⟨le_rfl, hcb⟩
          refine' h_deriv_c.congr _ _
          · grind
          · simp +decide [hz₀]
      simp_all +decide [Set.Icc_union_Icc_eq_Icc hac hcb]
      convert h_deriv_c.1.union h_deriv_c.2 using 1; ext; aesop
    · by_cases htc : t < c
      · have h_deriv_y : HasDerivWithinAt y (f t (y t)) (Icc a b) t := by
          have := hy_deriv t ⟨ht.1, htc.le⟩
          apply this.mono_of_mem_nhdsWithin
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          exact ⟨Set.Iio c, Iio_mem_nhds htc,
            fun x hx => ⟨hx.2.1, hx.1.out.le⟩⟩
        simp +zetaDelta at *
        convert h_deriv_y.congr_of_eventuallyEq _ _ using 1
        · rw [if_pos htc.le]
        · filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htc)] with x hx₁ hx₂
            using if_pos hx₂.out.le
        · rw [if_pos htc.le]
      · have hz_deriv_t : HasDerivWithinAt z (f t (z t)) (Icc c b) t := by
          exact hz_deriv t ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have hz_deriv_t : HasDerivWithinAt (fun t => if t ≤ c then y t else z t)
            (f t (z t)) (Icc c b) t := by
          refine' hz_deriv_t.congr _ _
          · grind
          · rw [if_neg (by linarith [lt_of_le_of_ne (le_of_not_gt htc) (Ne.symm ‹_›)])]
        have hz_deriv_t : HasDerivWithinAt (fun t => if t ≤ c then y t else z t)
            (f t (z t)) (Icc a b) t := by
          refine' hz_deriv_t.mono_of_mem_nhdsWithin _
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          exact ⟨Set.Ioi c, Ioi_mem_nhds
            (lt_of_le_of_ne (le_of_not_gt htc) (Ne.symm ‹_›)),
            fun x hx => ⟨by linarith [hx.1.out], by linarith [hx.2.2]⟩⟩
        grind

private lemma exists_solution_induct {f : ℝ → E → E} {L : ℝ} (n : ℕ)
    (hL : 0 ≤ L) (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2)) :
    ∀ {a b : ℝ} {y₀ : E} (hab : a ≤ b) (hLab : L * (b - a) < ↑n + 1)
      (hf_lip : IsLipschitzInSecondVar f L a b),
      ∃ y : ℝ → E, y a = y₀ ∧ ContinuousOn y (Icc a b) ∧
        ∀ t ∈ Icc a b, HasDerivWithinAt y (f t (y t)) (Icc a b) t := by
  induction n with
  | zero =>
    intro a b y₀ hab hLab hf_lip
    exact exists_solution_short hab (by push_cast at hLab; linarith) hf_cont hf_lip hL
  | succ n ih =>
    intro a b y₀ hab hLab hf_lip
    by_cases h : L * (b - a) < 1
    · exact exists_solution_short hab h hf_cont hf_lip hL
    · set c := (a + b) / 2 with hc_def
      have hac : a ≤ c := by linarith
      have hcb : c ≤ b := by linarith
      have hba_half : c - a = (b - a) / 2 := by ring
      have hba_half' : b - c = (b - a) / 2 := by ring
      have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hL_half : L * (c - a) < ↑n + 1 := by
        rw [hba_half]; push_cast at hLab ⊢; nlinarith
      have hL_half' : L * (b - c) < ↑n + 1 := by
        rw [hba_half']; push_cast at hLab ⊢; nlinarith
      exact exists_solution_concat hac hcb
        (ih hac hL_half (hf_lip.mono_Icc le_rfl hcb))
        (fun w => ih hcb hL_half' (hf_lip.mono_Icc hac le_rfl))

/-- **Picard–Lindelöf existence** (Iserles Theorem 1.1, existence part).
If `f` is continuous and Lipschitz in its second variable on `[a, b]`, then
the IVP `y' = f(x, y(x)), y(a) = y₀` has a solution on `[a, b]`.

The proof uses bisection induction: subdivide `[a,b]` until each piece has
`L * δ < 1`, solve locally via `IsPicardLindelof`, then glue via
`exists_solution_concat`. -/
theorem exists_solution {f : ℝ → E → E} {L : ℝ} {a b : ℝ} {y₀ : E}
    (hab : a < b)
    (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))
    (hf_lip : IsLipschitzInSecondVar f L a b)
    (hL : 0 ≤ L) :
    ∃ y : ℝ → E, y a = y₀ ∧ ContinuousOn y (Icc a b) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt y (f t (y t)) (Icc a b) t := by
  obtain ⟨n, hn⟩ := exists_nat_gt (L * (b - a))
  exact exists_solution_induct n hL hf_cont (le_of_lt hab) (by linarith) hf_lip

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
