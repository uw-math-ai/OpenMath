import OpenMath.PadeOrderStars

open Complex

theorem cycle298_padeR_pole_side_correction_of_aStable
    {n d : ℕ} {data : OrderArrowTerminationData}
    (hnum : data.numeratorDegree = n)
    (hden : data.denominatorDegree = d)
    (hA : IsAStablePadeApprox data) :
    ∃ poleCorrection : ℕ,
      data.denominatorDegree ≤ data.numeratorDegree + 2 + poleCorrection ∧
      poleCorrection = 0 := by
  sorry
