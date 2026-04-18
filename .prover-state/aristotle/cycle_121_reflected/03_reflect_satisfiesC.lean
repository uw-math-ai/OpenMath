import OpenMath.Adjoint

namespace ButcherTableau

def reflect (t : ButcherTableau s) : ButcherTableau s where
  c := fun i => 1 - t.c i
  A := fun i j => t.b j - t.A i j
  b := t.b

theorem reflect_satisfiesC_aristotle {t : ButcherTableau s} {η : ℕ}
    (hB : t.SatisfiesB η) (hC : t.SatisfiesC η) : t.reflect.SatisfiesC η := by
  sorry

end ButcherTableau
