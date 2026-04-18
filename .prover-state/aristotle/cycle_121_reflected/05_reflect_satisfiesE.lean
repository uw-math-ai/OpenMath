import OpenMath.Adjoint

namespace ButcherTableau

def reflect (t : ButcherTableau s) : ButcherTableau s where
  c := fun i => 1 - t.c i
  A := fun i j => t.b j - t.A i j
  b := t.b

theorem reflect_satisfiesE_aristotle {t : ButcherTableau s} {η ζ : ℕ}
    (hB : t.SatisfiesB (η + ζ)) (hE : t.SatisfiesE η ζ) :
    t.reflect.SatisfiesE η ζ := by
  sorry

end ButcherTableau
