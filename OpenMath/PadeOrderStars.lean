import OpenMath.Pade
import OpenMath.OrderStars

open Complex

theorem thm_355D_of_padeR
    (n d : ℕ) (data : OrderArrowTerminationData)
    (happrox : IsRationalApproxToExp data)
    (hreal : RealizesInfinityBranchGerms (padeR n d) data)
    (hconcrete : ConcreteRationalApproxToExp (padeR n d) data) :
    SatisfiesArrowCountInequality data.toOrderArrowCountData := by
  simpa using
    (thm_355D_of_concreteRationalApprox
      (R := padeR n d) data happrox hreal hconcrete)

theorem thm_355E'_of_padeR
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpade : IsPadeApproxToExp data)
    (hreal : RealizesInfinityBranchGerms (padeR n d) data)
    (hconcrete : ConcreteRationalApproxToExp (padeR n d) data) :
    data.downArrowsAtZeros = data.numeratorDegree ∧
    data.upArrowsAtPoles = data.denominatorDegree := by
  simpa using
    (thm_355E'_of_concreteRationalApprox
      (R := padeR n d) data hpade hreal hconcrete)

theorem padeR_no_nonzero_eq_exp_on_orderWeb
    (n d : ℕ) :
    ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) →
      padeR n d z = exp z → False := by
  sorry
