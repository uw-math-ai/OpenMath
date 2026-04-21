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

/-- For Padé order webs, the exact coincidence exclusion is an honest consequence
of the unit-level exclusion already exposed by `OrderStars`. The fully uniform
statement without this extra hypothesis is false already for `padeR 0 0 = 1`. -/
theorem padeR_no_nonzero_eq_exp_on_orderWeb
    (n d : ℕ)
    (hno_nonzero_unit_points_on_orderWeb :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) →
        ‖padeR n d z * exp (-z)‖ = 1 → False) :
    ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) →
      padeR n d z = exp z → False := by
  intro z hz_ne hz_web hz_eq
  apply hno_nonzero_unit_points_on_orderWeb z hz_ne hz_web
  calc
    ‖padeR n d z * exp (-z)‖ = ‖exp z * exp (-z)‖ := by simp [hz_eq]
    _ = ‖(1 : ℂ)‖ := by rw [← Complex.exp_add]; simp
    _ = 1 := by simp
