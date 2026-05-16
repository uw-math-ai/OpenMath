import Mathlib
import OpenMath.Chapter3.Section381
import OpenMath.Chapter4.Section404

/-!
# Butcher §422 — The underlying one-step method (Phase 0 wire-up)

Phase 0 scaffold for `def:422B` (Butcher §422, p. 359, *"The
underlying one-step method"*). The full construction — building the
underlying one-step method `η ∈ G₁` of a preconsistent and stable
linear multistep method — is multi-cycle work (Phases A–E in
`.prover-state/issues/def_422B_path.md`).

This file ships only the wire-up sanity ship: the §383 `G₁` group
codomain (the `Quotient PhiEquivalent.setoidSigma` from cycle 236's
`instGroup_phi`) is non-empty. Together with cycle 35's
`LinearMultistepMethod` structure and cycles 232–236's §383 group
infrastructure, this confirms the prerequisite stack is healthy and
ready for the cycle 337+ Phase A `D`-operator ship.

## Cycle 336 deliverable

* `Nonempty (Quotient PhiEquivalent.setoidSigma)` — Phase 0
  non-vacuity, witnessed by the equivalence class of cycle 184's
  `paddedEuler` (a 2-stage tableau computing the same step as
  explicit Euler).

The full `def:422B` `noncomputable def
LinearMultistepMethod.underlyingOneStepMethod` is deferred to cycle
337+ per the phase decomposition in `def_422B_path.md`.
-/

namespace OpenMath.Chapter4.Section422

/-- `def:422B` Phase 0 sanity: the §383 quotient group `G₁ = Quotient
PhiEquivalent.setoidSigma` is non-empty.

The eventual `def:422B` will define `M.underlyingOneStepMethod :
Quotient PhiEquivalent.setoidSigma` for every preconsistent and
stable `M : LinearMultistepMethod k`. This Phase 0 theorem only
confirms the *target type* is non-empty — a necessary prerequisite
for that future definition. The witness is the equivalence class of
cycle 184's `paddedEuler : RKTableau 2`.

See `.prover-state/issues/def_422B_path.md` for the multi-cycle
phase decomposition (Phase A: `D`-operator; Phase B: `Group.zpow`
API; Phase C: (422a) predicate; Phase D: inductive solver; Phase E:
sealing). -/
theorem underlyingOneStepMethod_target_nonempty :
    Nonempty (Quotient
      OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma) :=
  ⟨Quotient.mk
    OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma
    ⟨2, OpenMath.Chapter3.Section381.paddedEuler⟩⟩

end OpenMath.Chapter4.Section422
