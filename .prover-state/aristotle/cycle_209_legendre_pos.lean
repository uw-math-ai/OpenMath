import OpenMath.Legendre

open Polynomial
open scoped BigOperators

namespace OpenMath
namespace Cycle209Scratch

private lemma eval_eq_zero_on_Icc_imp_eq_zero
    (p : ℝ[X])
    (hzero : ∀ x ∈ Set.Icc (0 : ℝ) 1, p.eval x = 0) :
    p = 0 := by
  sorry

private lemma exists_eval_ne_zero_on_Icc
    (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧ p.eval x ≠ 0 := by
  sorry

private lemma sq_eval_continuousOn
    (p : ℝ[X]) :
    ContinuousOn (fun x : ℝ => (p.eval x) ^ 2) (Set.Icc (0 : ℝ) 1) := by
  sorry

private lemma intervalIntegral_sq_eval_pos_of_exists_ne_zero
    (p : ℝ[X])
    (hx : ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧ p.eval x ≠ 0) :
    0 < ∫ x in (0 : ℝ)..1, (p.eval x) ^ 2 := by
  sorry

lemma poly_eq_zero_of_intervalIntegral_sq_zero_candidate
    (p : ℝ[X])
    (h : ∫ x in (0 : ℝ)..1, (p.eval x) ^ 2 = 0) :
    p = 0 := by
  sorry

end Cycle209Scratch
end OpenMath
