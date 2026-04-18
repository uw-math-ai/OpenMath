import OpenMath.Adjoint

namespace ButcherTableau

def reflect (t : ButcherTableau s) : ButcherTableau s where
  c := fun i => 1 - t.c i
  A := fun i j => t.b j - t.A i j
  b := t.b

theorem reflect_reflect_aristotle (t : ButcherTableau s) :
    t.reflect.reflect = t := by
  sorry

end ButcherTableau
