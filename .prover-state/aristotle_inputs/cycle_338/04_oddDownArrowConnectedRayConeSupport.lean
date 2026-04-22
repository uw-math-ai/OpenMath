import OpenMath.PadeOrderStars

open Complex

theorem cycle338_oddDownArrowConnectedRayConeSupport
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    Nonempty
      (PadeRConnectedRayConeOrderWebSupport n d
        (Real.pi / ((↑(n + d) + 1) : ℝ))) := by
  sorry
