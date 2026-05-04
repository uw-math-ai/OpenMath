import OpenMath.AdamsMethods
import OpenMath.MultistepMethods

/-! # Milne Device for Local Error Estimation (Butcher §463)

Pairs an explicit Adams–Bashforth predictor with an implicit
Adams–Moulton corrector of the same order. The local truncation error
of the corrector at step `n` is asymptotically proportional to the
predictor / corrector difference `y^C_n − y^P_n`, with the
proportionality constant determined by the ratio of error constants.

Reference: Butcher §463; Hairer–Nørsett–Wanner Vol. I §III.7.
-/

namespace OpenMath

open scoped Classical

/-- A **Milne device pair** packages a predictor LMM (explicit) and a
corrector LMM (implicit) of the same order `p`. Step counts may differ
(predictor typically `p` steps, corrector typically `p − 1` steps). -/
structure MilneDevicePair (sP sC p : ℕ) where
  predictor : LMM sP
  corrector : LMM sC
  predictor_order : predictor.HasOrder p
  corrector_order : corrector.HasOrder p
  predictor_explicit : predictor.IsExplicit
  corrector_implicit : corrector.IsImplicit

namespace MilneDevicePair

variable {sP sC p : ℕ}

/-- The **Milne factor** `κ := C^C / (C^P − C^C)` is the ratio that
turns the predictor / corrector difference into a leading-order
estimate of the corrector's local truncation error. Asymptotically:
`LTE^C ≈ κ · (y^C − y^P)`. -/
noncomputable def milneFactor (m : MilneDevicePair sP sC p) : ℝ :=
  let CC := m.corrector.errorConstant p
  let CP := m.predictor.errorConstant p
  CC / (CP - CC)

/-- The Milne local error estimate, as a function of the predictor and
corrector outputs at a single step. -/
noncomputable def localErrorEstimate
    (m : MilneDevicePair sP sC p) (yP yC : ℝ) : ℝ :=
  m.milneFactor * (yC - yP)

end MilneDevicePair

/-! ## Concrete instance: AB4 / AM3 order-4 Milne pair -/

/-- Classical Milne device: AB4 predictor + AM3 corrector, both order 4.
Predictor error constant `251/720`, corrector `-19/720`. -/
noncomputable def milneAB4AM3 : MilneDevicePair 4 3 4 where
  predictor := adamsBashforth4
  corrector := adamsMoulton3
  predictor_order := adamsBashforth4_order_four
  corrector_order := adamsMoulton3_order_four
  predictor_explicit := adamsBashforth4_explicit
  corrector_implicit := adamsMoulton3_implicit

/-- The AB4 / AM3 Milne factor evaluates to `−19/270`. -/
theorem milneAB4AM3_milneFactor :
    milneAB4AM3.milneFactor = -(19 / 270) := by
  unfold MilneDevicePair.milneFactor milneAB4AM3
  rw [adamsBashforth4_errorConstant, adamsMoulton3_errorConstant]
  norm_num

/-- The AB4 / AM3 local error estimate equals `−(19/270) · (yC − yP)`. -/
theorem milneAB4AM3_localErrorEstimate (yP yC : ℝ) :
    milneAB4AM3.localErrorEstimate yP yC = -(19 / 270) * (yC - yP) := by
  unfold MilneDevicePair.localErrorEstimate
  rw [milneAB4AM3_milneFactor]

/-- The Milne factor at AB4 / AM3 is strictly negative — the
corrector's leading error has the opposite sign from the AB-predictor's
error, which is what makes the device meaningful. -/
theorem milneAB4AM3_milneFactor_neg :
    milneAB4AM3.milneFactor < 0 := by
  rw [milneAB4AM3_milneFactor]; norm_num

end OpenMath
