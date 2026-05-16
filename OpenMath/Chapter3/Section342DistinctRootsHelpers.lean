/-
Helper lemmas for the Butcher §342 (342g) distinct-roots argument.

Adapted from the Aristotle proof (cycle 301, project
`5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`) of
`butcherShiftedLegendre_n_distinct_real_zeros`: `P_n^*` has `n` distinct
real zeros in `(0, 1)`.

The helpers exposed in `OpenMath.Chapter3.Section342DistinctRootsHelpers`:
- `poly_nonneg_or_nonpos_near_even_mult_root` — at a root of even
  multiplicity, the polynomial has locally constant sign.
- `poly_constant_sign_of_even_mult_roots` — a polynomial whose roots
  in `(0,1)` all have even multiplicity, and which is nonzero at the
  endpoints, has constant sign on `[0,1]`.
- `prod_linear_factors_dvd_of_roots` — the product of distinct linear
  factors over a finite root set divides the polynomial.

These are generic polynomial / sign-analysis helpers; they do not
depend on `butcherShiftedLegendre` and are placed in their own
namespace for future reuse.
-/

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

open Polynomial

namespace OpenMath.Chapter3.Section342DistinctRootsHelpers

/-- At a root of even multiplicity, the polynomial has locally constant
sign: there is a neighbourhood radius `δ > 0` such that either the
polynomial is `≥ 0` on the whole ball or `≤ 0` on the whole ball. -/
lemma poly_nonneg_or_nonpos_near_even_mult_root
    (p : Polynomial ℝ) (hp : p ≠ 0) (r : ℝ)
    (heven : Even (p.rootMultiplicity r)) :
    ∃ δ > (0 : ℝ), (∀ x : ℝ, |x - r| < δ → 0 ≤ p.eval x) ∨
                     (∀ x : ℝ, |x - r| < δ → p.eval x ≤ 0) := by
  obtain ⟨q, hq⟩ :
      ∃ q : Polynomial ℝ,
        p = (Polynomial.X - Polynomial.C r) ^ (rootMultiplicity r p) * q ∧
        ¬(Polynomial.X - Polynomial.C r) ∣ q :=
    exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp r
  have hq_ne_zero : q.eval r ≠ 0 := by
    exact fun h => hq.2 <| Polynomial.dvd_iff_isRoot.mpr h
  obtain ⟨δ, hδ_pos, hδ⟩ :
      ∃ δ > 0, ∀ x, abs (x - r) < δ → (q.eval x) * (q.eval r) > 0 := by
    have := Metric.continuous_iff.mp q.continuous r
    exact Exists.elim (this (|q.eval r|) (abs_pos.mpr hq_ne_zero))
      fun δ hδ => ⟨δ, hδ.1, fun x hx => by
        cases abs_cases (q.eval r) <;>
          nlinarith [abs_lt.mp (hδ.2 x hx)]⟩
  have h_even_pow :
      ∀ x, abs (x - r) < δ →
        (x - r) ^ (rootMultiplicity r p) * q.eval x * q.eval r ≥ 0 := by
    intro x hx
    specialize hδ x hx
    rw [mul_assoc]
    exact mul_nonneg (by exact heven.pow_nonneg _) (by linarith)
  refine ⟨δ, hδ_pos, ?_⟩
  rw [hq.1]
  norm_num +zetaDelta at *
  cases lt_or_gt_of_ne hq_ne_zero <;>
    first
      | (left; intro x hx; nlinarith [h_even_pow x hx, hδ x hx])
      | (right; intro x hx; nlinarith [h_even_pow x hx, hδ x hx])

/-- A polynomial with even-multiplicity roots in `(0,1)` and nonzero at
the endpoints `0` and `1` has constant sign on `[0,1]`. -/
lemma poly_constant_sign_of_even_mult_roots (p : Polynomial ℝ) (hp : p ≠ 0)
    (hp0 : p.eval 0 ≠ 0) (hp1 : p.eval 1 ≠ 0)
    (heven : ∀ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 → Even (p.rootMultiplicity r)) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ p.eval x) ∨
    (∀ x ∈ Set.Icc (0 : ℝ) 1, p.eval x ≤ 0) := by
  by_contra h_contra
  obtain ⟨q, hq⟩ :
      ∃ q : Polynomial ℝ,
        p = q * (∏ r ∈ p.roots.toFinset.filter (fun r => r ∈ Set.Ioo (0 : ℝ) 1),
                  (Polynomial.X - Polynomial.C r) ^ (Polynomial.rootMultiplicity r p)) ∧
        (∀ r ∈ Set.Ioo (0 : ℝ) 1, q.eval r ≠ 0) := by
    have h_factor :
        p = (∏ r ∈ p.roots.toFinset.filter (fun r => r ∈ Set.Ioo (0 : ℝ) 1),
              (Polynomial.X - Polynomial.C r) ^ (Polynomial.rootMultiplicity r p)) *
            (p /ₘ (∏ r ∈ p.roots.toFinset.filter (fun r => r ∈ Set.Ioo (0 : ℝ) 1),
                    (Polynomial.X - Polynomial.C r) ^ (Polynomial.rootMultiplicity r p))) := by
      rw [Polynomial.divByMonic_eq_div _]
      · rw [EuclideanDomain.mul_div_cancel']
        · exact Finset.prod_ne_zero_iff.mpr
            fun x _ => pow_ne_zero _ <| Polynomial.X_sub_C_ne_zero x
        · refine Finset.prod_dvd_of_coprime ?_ ?_
          · intros r _ s _ hrs
            exact IsCoprime.pow
              (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
                (sub_ne_zero_of_ne hrs).isUnit)
          · exact fun x _ => Polynomial.pow_rootMultiplicity_dvd p x
      · exact Polynomial.monic_prod_of_monic _ _ fun x _ =>
          Polynomial.monic_X_sub_C _ |> Polynomial.Monic.pow <|
            Polynomial.rootMultiplicity x p
    refine ⟨p /ₘ (∏ r ∈ p.roots.toFinset with r ∈ Set.Ioo 0 1,
                (X - C r) ^ rootMultiplicity r p), h_factor.trans (mul_comm _ _), ?_⟩
    intro r hr hq_zero
    have h_root :
        Polynomial.rootMultiplicity r p =
          Polynomial.rootMultiplicity r
            (∏ r ∈ p.roots.toFinset.filter (fun r => r ∈ Set.Ioo (0 : ℝ) 1),
              (Polynomial.X - Polynomial.C r) ^ (Polynomial.rootMultiplicity r p)) +
          Polynomial.rootMultiplicity r
            (p /ₘ (∏ r ∈ p.roots.toFinset.filter (fun r => r ∈ Set.Ioo (0 : ℝ) 1),
                    (Polynomial.X - Polynomial.C r) ^ (Polynomial.rootMultiplicity r p))) := by
      rw [← Polynomial.rootMultiplicity_mul]
      · rw [← h_factor]
      · exact h_factor ▸ hp
    have h_root_mult :
        Polynomial.rootMultiplicity r
            (∏ r ∈ p.roots.toFinset.filter (fun r => r ∈ Set.Ioo (0 : ℝ) 1),
              (Polynomial.X - Polynomial.C r) ^ (Polynomial.rootMultiplicity r p)) =
          Polynomial.rootMultiplicity r p := by
      rw [Finset.prod_eq_prod_diff_singleton_mul <|
        show r ∈ p.roots.toFinset.filter (fun r => r ∈ Set.Ioo 0 1) from ?_]
      · rw [Polynomial.rootMultiplicity_mul]
        · rw [Polynomial.rootMultiplicity_X_sub_C_pow]
          simp +decide [Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]
        · exact mul_ne_zero
            (Finset.prod_ne_zero_iff.mpr fun x _ => pow_ne_zero _ <|
              Polynomial.X_sub_C_ne_zero _) <|
            pow_ne_zero _ <| Polynomial.X_sub_C_ne_zero _
      · replace h_factor := congr_arg (Polynomial.eval r) h_factor
        norm_num [hq_zero] at h_factor
        simp_all +singlePass [Polynomial.eval_prod]
    norm_num [hr.1, hr.2] at h_root_mult h_root
    norm_num [h_root_mult] at h_root
    grind +revert
  have hq_sign :
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < q.eval x) ∨
      (∀ x ∈ Set.Icc (0 : ℝ) 1, q.eval x < 0) := by
    have hq_sign : ∀ x ∈ Set.Icc (0 : ℝ) 1, q.eval x ≠ 0 := by
      intro x hx hqx
      have := hq.1
      replace := congr_arg (Polynomial.eval x) this
      norm_num [hqx, Finset.prod_eq_zero_iff, Polynomial.eval_prod] at this
      exact hq.2 x ⟨lt_of_le_of_ne hx.1 (by rintro rfl; exact hp0 this),
                    lt_of_le_of_ne hx.2 (by rintro rfl; exact hp1 this)⟩ hqx
    contrapose! hq_sign
    have h_ivt :
        IsConnected (Set.image (fun x => q.eval x) (Set.Icc (0 : ℝ) 1)) := by
      exact ⟨Set.Nonempty.image _ ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩,
              isPreconnected_Icc.image _ <| q.continuous.continuousOn⟩
    exact h_ivt.Icc_subset
      (Set.mem_image_of_mem _ hq_sign.1.choose_spec.1)
      (Set.mem_image_of_mem _ hq_sign.2.choose_spec.1)
      ⟨hq_sign.1.choose_spec.2, hq_sign.2.choose_spec.2⟩
  have hp_sign :
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ p.eval x) ∨
      (∀ x ∈ Set.Icc (0 : ℝ) 1, p.eval x ≤ 0) := by
    rcases hq_sign with hq_sign | hq_sign <;>
      [left; right] <;> intro x hx <;> rw [hq.1] <;>
        norm_num [Polynomial.eval_prod]
    · refine mul_nonneg (le_of_lt (hq_sign x hx)) (Finset.prod_nonneg fun r hr => ?_)
      rw [← Nat.mul_div_cancel'
        (even_iff_two_dvd.mp (heven r ⟨by linarith [Finset.mem_filter.mp hr],
                                       by linarith [Finset.mem_filter.mp hr]⟩))]
      rw [pow_mul]
      positivity
    · refine mul_nonpos_of_nonpos_of_nonneg (le_of_lt (hq_sign x hx)) ?_
      refine Finset.prod_nonneg fun r hr => ?_
      rw [← Nat.mul_div_cancel'
        (even_iff_two_dvd.mp (heven r ⟨by linarith [Finset.mem_filter.mp hr],
                                       by linarith [Finset.mem_filter.mp hr]⟩))]
      rw [pow_mul]
      positivity
  contradiction

/-- Product of distinct linear factors divides `p` if each root divides `p`. -/
lemma prod_linear_factors_dvd_of_roots (p : Polynomial ℝ) (S : Finset ℝ)
    (hroots : ∀ r ∈ S, p.IsRoot r) :
    S.prod (fun r => (X : ℝ[X]) - C r) ∣ p := by
  exact Finset.prod_dvd_of_coprime
    (fun x _ y _ hxy => Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero_of_ne hxy).isUnit)
    fun x hx => Polynomial.dvd_iff_isRoot.mpr (hroots x hx)

end OpenMath.Chapter3.Section342DistinctRootsHelpers
