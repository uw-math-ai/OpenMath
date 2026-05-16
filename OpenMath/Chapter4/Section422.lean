import Mathlib
import OpenMath.Chapter3.Section381
import OpenMath.Chapter4.Section404

/-!
# Butcher §422 — The underlying one-step method (Phase A.0)

This file ships:

* **Phase 0 wire-up sanity (cycle 336)**:
  `underlyingOneStepMethod_target_nonempty` — the §383 quotient group
  `Q = Quotient PhiEquivalent.setoidSigma` is non-empty (the eventual
  codomain of `def:422B`).
* **Phase A.0 `D`-operator (cycle 337)**: `D_element : Q` and
  `D_phi : Q → Q` corresponding to Butcher §387's `D ∈ G`
  (`extraction/raw_text/ch03.txt:9392`), the differentiation
  operation scaled by the unit stepsize `h`. Two non-vacuity sanity
  theorems verify the choice acts correctly at the identity input and
  on the single-vertex tree `τ`.

See `.prover-state/issues/def_422B_path.md` §A.0 for the detailed
design discussion, including the b₀-invisibility argument that
justifies using `⟦⟨1, explicitEuler⟩⟧` as the quotient-level
representative of Butcher's `D ∈ G` (which has `b₀ = 0` and is not
directly representable in our b₀=1 `RKTableau` framework).

The full `def:422B` construction (Phase B–E: `Group.zpow` non-vacuity,
the (422a) predicate, the inductive solver, and the sealing) is
multi-cycle work; see the scoping doc §5 for the phase decomposition.
-/

namespace OpenMath.Chapter4.Section422

open OpenMath.Chapter3.Section310 OpenMath.Chapter3.Section312
open OpenMath.Chapter3.Section312.RKTableau

/-- `def:422B` Phase 0 sanity (cycle 336): the §383 quotient group
`Q = Quotient PhiEquivalent.setoidSigma` is non-empty.

The eventual `def:422B` will define `M.underlyingOneStepMethod : Q`
for every preconsistent and stable `M : LinearMultistepMethod k`.
This Phase 0 theorem only confirms the *target type* is non-empty —
a necessary prerequisite for that future definition. The witness is
the equivalence class of cycle 184's `paddedEuler : RKTableau 2`.

See `.prover-state/issues/def_422B_path.md` §5 for the multi-cycle
phase decomposition (Phase A: `D`-operator; Phase B: `Group.zpow`
API; Phase C: (422a) predicate; Phase D: inductive solver; Phase E:
sealing). -/
theorem underlyingOneStepMethod_target_nonempty :
    Nonempty (Quotient PhiEquivalent.setoidSigma) :=
  ⟨Quotient.mk PhiEquivalent.setoidSigma
    ⟨2, OpenMath.Chapter3.Section381.paddedEuler⟩⟩

/-! ### Phase A.0 — Butcher §387's `D ∈ G` (cycle 337)

Butcher §387 (`extraction/raw_text/ch03.txt:9392`) defines `D ∈ G` as
the differentiation operation scaled by the unit stepsize `h`. The
underlying realisation is the §385b generalized one-stage RK method

```
0 0
0 1
```

i.e. `s = 1, A = 0, b = [1], c = [0]` with `b₀ = 0`, computing
`y_n = 0·y_{n-1} + h·f(y_{n-1}) = h·f(y_{n-1})`.

Its elementary weights on the rooted-tree domain `T` are:

* `Φ_D(τ) = 1` (single-vertex tree),
* `Φ_D(t) = 0` for `t` of order ≥ 2.

**b₀-invisibility.** Our `RKTableau` (`Section312.lean:66`) has only
`(A, b, c)`; the implicit `b₀ = 1` is *not* part of `PhiEquivalent`'s
defining quantifier `∀ t : RootedTree, …`, since `RootedTree`
(`Section310.lean:83`) admits no empty-tree representative. Hence the
b₀-distinction between Butcher's `D ∈ G` (with `b₀ = 0`) and the
explicit Euler tableau (with `b₀ = 1` implicit) is *invisible* at the
§383 quotient level: their elementary weights agree on every
`t : RootedTree`. Consequently `⟦⟨1, explicitEuler⟩⟧` is the canonical
quotient-level representative of Butcher's `D`.
-/

/-- *Phase A.0 §A.0.5:* the §387 `D`-operator's quotient-level
representative. Butcher's `D ∈ G` (the §385b generalized one-stage RK
method with `b₀ = 0`) and `RKTableau.explicitEuler` (a 1-stage RK
method with `b₀ = 1` implicit, `A = 0`, `b = [1]`, `c = [0]`) share
the elementary-weight signature `Φ(τ) = 1`, `Φ(t≥2) = 0` on `T`. The
b₀-distinction is invisible to `PhiEquivalent`, so this class is the
canonical quotient representative of `D`.

See `.prover-state/issues/def_422B_path.md` §A.0 for the detailed
b₀-invisibility justification. -/
noncomputable def D_element : Quotient PhiEquivalent.setoidSigma :=
  Quotient.mk PhiEquivalent.setoidSigma
    ⟨1, RKTableau.explicitEuler⟩

/-- *Phase A.0 §A.0.5:* the `D_phi` operator. Right-multiplication by
`D_element` in the §383 group (cycle 236's `instGroup_phi`).

In Butcher's notation: for `η ∈ G₁`, `D_phi η = η · D ∈ G` (with the
b₀-collapse to `Q` understood). This is the operator that appears in
the right half of equation (422a), `Σ βᵢ η^{-i} D(u)`.

The definition is unconditionally well-defined (no `Quotient.lift`
respect obligation is needed): `D_phi` is given by the §383 group's
own multiplication, which already respects `PhiEquivalent`. -/
noncomputable def D_phi (η : Quotient PhiEquivalent.setoidSigma) :
    Quotient PhiEquivalent.setoidSigma :=
  η * D_element

/-- *Phase A.0 non-vacuity 1:* `D_phi` evaluated at the §383 group
identity `1` returns `D_element`. Follows from `one_mul` in cycle
236's `instGroup_phi`. -/
theorem D_phi_one : D_phi 1 = D_element := one_mul _

/-- *Phase A.0 non-vacuity 2:* at the single-vertex tree `τ`, the
elementary weight of `D_element` is `1`. Matches Butcher §387's
`Φ_D(τ) = 1` from the (385b) generalized tableau, confirming the
representative choice acts correctly on `τ`.

Reduces to `RKTableau.explicitEuler.elementaryWeight τ = 1`, which
expands to `∑ i : Fin 1, 1 · (Φᵢ D)(τ) = 1 · 1 = 1` via cycle 187's
`derivativeWeight_vertex`. -/
theorem D_element_elementaryWeight_vertex :
    RKTableau.elementaryWeightQ_phi D_element RootedTree.vertex = 1 := by
  show RKTableau.explicitEuler.elementaryWeight RootedTree.vertex = 1
  show ∑ i : Fin 1, RKTableau.explicitEuler.b i *
        RKTableau.explicitEuler.derivativeWeight i RootedTree.vertex = 1
  simp [RKTableau.explicitEuler, RKTableau.derivativeWeight_vertex]

end OpenMath.Chapter4.Section422
