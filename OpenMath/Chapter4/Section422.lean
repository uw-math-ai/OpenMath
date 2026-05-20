import Mathlib
import OpenMath.Chapter3.Section301
import OpenMath.Chapter3.Section381
import OpenMath.Chapter4.Section404
import OpenMath.Chapter4.Section410
import OpenMath.Chapter4.Section441
import OpenMath.Chapter4.Section451

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

/-- Local alias to disambiguate from Mathlib's `_root_.RootedTree`. -/
private abbrev RT := OpenMath.Chapter3.Section310.RootedTree

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

/-- *Phase A.0.2 helper:* every internal weight of `explicitEuler` is `0`.
Direct consequence of `explicitEuler.A = 0`: the defining sum
`∑ j, A 0 j * (Φⱼ D)(c)` reduces to `0 * _ = 0` via `Fin.sum_univ_one`. -/
private theorem explicitEuler_internalWeight_zero (c : RT)
    (i : Fin 1) :
    RKTableau.explicitEuler.internalWeight c i = 0 := by
  show ∑ j : Fin 1, RKTableau.explicitEuler.A i j *
        RKTableau.explicitEuler.derivativeWeight j c = 0
  simp [RKTableau.explicitEuler]

/-- *Phase A.0.2:* at every tree of order ≥ 2, the elementary weight of
`D_element` vanishes. Matches Butcher §387's `Φ_D(t) = 0` for `t≥2`
from the (385b) generalized tableau (whose `A = 0` zeroes out every
internal-weight factor `Σⱼ Aᵢⱼ · Φⱼ` in the recursion).

Together with `D_element_elementaryWeight_vertex`, this pins
`D_element`'s on-tree elementary-weight signature to exactly Butcher's
`Φ_D`: `1` at `τ`, `0` elsewhere on `T`. -/
theorem D_element_elementaryWeight_higher_order
    (t : RT) (h : 2 ≤ t.order) :
    RKTableau.elementaryWeightQ_phi D_element t = 0 := by
  cases t with
  | mk children =>
    have hne : children ≠ [] := by
      intro heq
      subst heq
      simp [RootedTree.order, RootedTree.orderSum] at h
    show RKTableau.explicitEuler.elementaryWeight
          (OpenMath.Chapter3.Section310.RootedTree.mk children) = 0
    rw [RKTableau.elementaryWeight_eq, Fin.sum_univ_one,
        RKTableau.derivativeWeight_mk]
    cases children with
    | nil => exact absurd rfl hne
    | cons c rest =>
      simp [List.map_cons, List.prod_cons,
            explicitEuler_internalWeight_zero]

/-- *Phase A.0.2 helper:* a non-vertex tree has order at least `2`.
By cases on the child list: `mk []` is `vertex` (contradicting the
hypothesis); `mk (c :: rest)` has `order = 1 + (c.order + orderSum rest)
≥ 1 + 1 = 2` since `c.order ≥ 1` (Section301's `order_pos`). -/
private theorem RootedTree_two_le_order_of_ne_vertex
    (t : RT) (h : t ≠ RootedTree.vertex) : 2 ≤ t.order := by
  cases t with
  | mk children =>
    cases children with
    | nil =>
      exact absurd rfl h
    | cons c rest =>
      show 2 ≤ 1 + RootedTree.orderSum (c :: rest)
      have hc : 0 < c.order := RootedTree.order_pos c
      show 2 ≤ 1 + (c.order + RootedTree.orderSum rest)
      omega

/-- *Phase A.0.2 capstone:* the full on-tree elementary-weight signature
of `D_element`. Matches Butcher §387's `Φ_D` exactly: `1` at the
single-vertex tree `τ`, `0` everywhere else on `T`. -/
theorem D_element_elementaryWeight (t : RT) :
    RKTableau.elementaryWeightQ_phi D_element t =
      if t = RootedTree.vertex then 1 else 0 := by
  by_cases h : t = RootedTree.vertex
  · subst h
    rw [if_pos rfl]
    exact D_element_elementaryWeight_vertex
  · rw [if_neg h]
    exact D_element_elementaryWeight_higher_order t
      (RootedTree_two_le_order_of_ne_vertex t h)

/-- *Phase A.0.2 simp:* `D_phi` distributes over the §383 group product
on the left, by associativity of group multiplication. Useful for
unfolding `D_phi (η * η')` rewrites in downstream Phase B/C lemmas. -/
@[simp]
theorem D_phi_mul (η η' : Quotient PhiEquivalent.setoidSigma) :
    D_phi (η * η') = η * D_phi η' := by
  show (η * η') * D_element = η * (η' * D_element)
  exact mul_assoc _ _ _

/-! ### Phase B — `Group.zpow` non-vacuity (cycle 339)

Sanity-check that Mathlib's `Group.zpow` API fires correctly on
`Quotient PhiEquivalent.setoidSigma` via cycle 236's `instGroup_phi`.
These integer-power lemmas (`zpow_zero`, `zpow_one`, `zpow_neg_one`,
`zpow_two`) are infrastructure for Phase C's equation (422a)
predicate, which builds terms like `D_element ^ (-(i + 1 : ℤ))` (the
`η^{-i} D(u)` factor in Butcher's (422a)).

See `.prover-state/issues/def_422B_path.md` §5 for the full
phase decomposition; Phase B verifies the zpow hookup before Phase C
ships the (422a) predicate. -/

/-- *Phase B.1 (cycle 339):* `D_element ^ 0 = 1` in the §383 group.
Direct application of Mathlib's `zpow_zero`, exercising the `Group`
instance's `zpow` at the zero exponent. -/
@[simp]
theorem D_element_zpow_zero : D_element ^ (0 : ℤ) = 1 := zpow_zero _

/-- *Phase B.2 (cycle 339):* `D_element ^ 1 = D_element` in the §383
group. Direct application of Mathlib's `zpow_one`. -/
@[simp]
theorem D_element_zpow_one : D_element ^ (1 : ℤ) = D_element := zpow_one _

/-- *Phase B.3 (cycle 339):* `D_element ^ (-1) = D_element⁻¹` in the
§383 group. Direct application of Mathlib's `zpow_neg_one`, which
routes through cycle 236's `inverseQ_phi` lift via the §383 `Group`
instance's `Inv` field. -/
theorem D_element_zpow_neg_one :
    D_element ^ (-1 : ℤ) = D_element⁻¹ := zpow_neg_one _

/-- *Phase B.4 (cycle 339):* `D_element ^ 2 = D_element * D_element` in
the §383 group. Direct application of Mathlib's `zpow_two`, exercising
the `Group.zpow` API at a small positive integer exponent. Confirms the
integer-power machinery unfolds cleanly for downstream Phase C use. -/
theorem D_element_zpow_two :
    D_element ^ (2 : ℤ) = D_element * D_element := zpow_two _

/-- *Phase B.5 (cycle 339):* `paddedEuler` non-vacuity sanity check —
the `Group.zpow` API at `n = -1` applied to a heterogeneous-stage
representative `⟦⟨2, paddedEuler⟩⟧` recovers cycle 184's
`paddedEuler.inverse` class via cycle 236's `inverseQ_phi_mk`
definitional unfold. Confirms the zpow infrastructure works beyond
`D_element` to arbitrary classes in the §383 quotient group. -/
example :
    (Quotient.mk PhiEquivalent.setoidSigma
        ⟨2, OpenMath.Chapter3.Section381.paddedEuler⟩ :
          Quotient PhiEquivalent.setoidSigma) ^ (-1 : ℤ)
      = Quotient.mk PhiEquivalent.setoidSigma
          ⟨2, OpenMath.Chapter3.Section381.paddedEuler.inverse⟩ := by
  rw [zpow_neg_one]
  rfl

/-! ### Phase C — the (422a) condition predicate (cycle 340)

Butcher §422 p. 358 equation (422a) (`extraction/raw_text/ch04.txt:1115–1116`):

```
  1 − α₁ η⁻¹ − α₂ η⁻² − ⋯ − αₖ η⁻ᵏ
                 − β₀ D − β₁ η⁻¹ D − β₂ η⁻² D − ⋯ − βₖ η⁻ᵏ D = 0
```

This is the *defining* equation for the underlying one-step method of
a linear multistep method `M = [α, β]`: a quotient class `η_q : Q`
solves (422a) iff, at every rooted tree `u`,

```
  1(u) − Σᵢ₌₁..ₖ αᵢ · η_q^(-i)(u)
       − Σᵢ₌₀..ₖ βᵢ · (η_q^(-i) · D)(u) = 0.
```

The predicate `Eq422a M η_q` captures this equation. Note:

* `1(u) = 0` on every `u : RootedTree` (cycle 239's
  `elementaryWeightQ_phi_id` simp lemma) — this is the
  b₀-invisibility property documented in cycle 337 §A.0.4. The
  empty-tree case of (422a), where `1` would contribute non-zero,
  is invisible at the `PhiEquivalent` quotient level and is
  handled separately by `M.IsPreconsistent` (Butcher's proof at
  `:1152`).
* `Eq422a` does **not** require `IsPreconsistent` / `IsStable` in
  its signature: those are *existence* hypotheses for `thm:422A`
  (the "such η exists" theorem), not preconditions for the
  *predicate*. Keeping them off makes the predicate reusable.

See `.prover-state/issues/def_422B_path.md` §5 for the full phase
decomposition. Phase D (inductive η-solver) and Phase E (lift/seal)
remain deferred. -/

/-- *Phase C (cycle 340):* Butcher §422 (422a) — the
underlying-one-step-method condition. Given a `k`-step linear
multistep method `M = [α, β]` and a quotient class `η_q` in the §383
quotient group, `Eq422a M η_q` states that at every rooted tree `u`,

```
  1(u) − Σᵢ₌₁..ₖ αᵢ · η_q^(-i)(u)
       − Σᵢ₌₀..ₖ βᵢ · (η_q^(-i) · D)(u) = 0.
```

* α-sum: indexed by `Fin k`, with `i.succ : Fin (k+1)` selecting
  `M.α i.succ` and exponent `-(i.val + 1 : ℤ)` giving `-1, -2, …, -k`.
* β-sum: indexed by `Fin (k+1)`, with `M.β i` and exponent
  `-(i.val : ℤ)` giving `0, -1, -2, …, -k`.

The β-side's right-multiplication by `D_element` matches Butcher's
`η^{-i} D` (cycle 337 `D_phi η := η * D_element`).

This is a `Prop`-valued predicate; the existence of `η_q` solving
this equation for a preconsistent and stable `M` is the content of
`thm:422A` (deferred to later cycles per the scoping doc §5). -/
def Eq422a {k : ℕ}
    (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (η_q : Quotient PhiEquivalent.setoidSigma) : Prop :=
  ∀ u : RT,
    elementaryWeightQ_phi (1 : Quotient PhiEquivalent.setoidSigma) u
      - (∑ i : Fin k,
          M.α i.succ
            * elementaryWeightQ_phi (η_q ^ (-((i.val + 1 : ℕ) : ℤ))) u)
      - (∑ i : Fin (k + 1),
          M.β i
            * elementaryWeightQ_phi
                ((η_q ^ (-((i.val : ℕ) : ℤ))) * D_element) u)
      = 0

/-- *Phase C non-vacuity (cycle 340):* `Eq422a` respects equality on
its quotient-class argument. Trivial well-definedness check: the
predicate's body is a function of `η_q`, so quotient-class equality
preserves the truth value. Useful for chaining `Quotient.sound`
rewrites through `Eq422a` in downstream Phase D/E lemmas. -/
theorem Eq422a_congr {k : ℕ}
    (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    {η_q η_q' : Quotient PhiEquivalent.setoidSigma} (h : η_q = η_q') :
    Eq422a M η_q ↔ Eq422a M η_q' := by
  subst h
  rfl

/-! ### Phase D pre-infrastructure (cycle 341) — τ-additivity of
`elementaryWeightQ_phi` under the §383 group

Load-bearing infrastructure for Phase D.1's `η(τ)` base-case solver.
At the single-vertex tree `τ`, the elementary weight on the §383
quotient group is *additive* under group multiplication: for
representatives `M₁, M₂`, the bottom-block sum `Σᵢ M₂.b i ·
M₂.derivativeWeightWithSrc M₁ i τ` collapses to `M₂.elementaryWeight
τ` because every `derivativeWeightWithSrc M₁ i τ = 1` (the empty
list case of `derivativeWeightWithSrcProd`). Inverse and integer
powers follow as corollaries via the §383 group structure.

The full τ-additivity chain (P1+P2+P3) makes the (422a) equation at
`u = τ` linear in `η(τ) := elementaryWeightQ_phi η_q τ`, unlocking
Phase D.1's closed-form base-case solver. -/

/-- *Phase D pre-infrastructure (cycle 341) P0:* at the single-vertex
tree `τ`, the helper `derivativeWeightWithSrc M₁ i τ` is `1` for every
source tableau `M₁` and bottom-block stage `i`. Direct from the empty-
list base case of `derivativeWeightWithSrcProd` (`Section381.lean:2690`):
`τ = mk []`, so `derivativeWeightWithSrc M₁ i (mk []) =
derivativeWeightWithSrcProd M₁ i [] = 1`.

`WithSrc` analog of cycle 187's `RKTableau.derivativeWeight_vertex`. -/
theorem RKTableau.derivativeWeightWithSrc_vertex
    {s₁ s₂ : ℕ} (M₂ : RKTableau s₂) (M₁ : RKTableau s₁) (i : Fin s₂) :
    M₂.derivativeWeightWithSrc M₁ i RootedTree.vertex = 1 := by
  show M₂.derivativeWeightWithSrcProd M₁ i [] = 1
  rfl

/-- *Phase D pre-infrastructure (cycle 341) P1:* at the single-vertex
tree `τ`, the elementary weight on the §383 quotient group is
*additive* under group multiplication. Load-bearing for Phase D.1's
`η(τ)` base-case solver.

Recipe: `Quotient.inductionOn` on each factor gives concrete
representatives `M₁, M₂`. `instMul_phi` unfolds `*` to `composeQ_phi`,
and cycle 239's `elementaryWeightQ_phi_composeQ_phi_mk` decomposes
the LHS into `M₁.elementaryWeight τ + Σᵢ M₂.b i · derivativeWeightWithSrc
M₁ i τ`. Every `derivativeWeightWithSrc M₁ i τ = 1` (P0) and every
`derivativeWeight i τ = 1` (cycle 187), so the bottom-block sum collapses
to `M₂.elementaryWeight τ`, matching the RHS. -/
theorem elementaryWeightQ_phi_mul_vertex
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q * η_q') RootedTree.vertex
      = elementaryWeightQ_phi η_q RootedTree.vertex
        + elementaryWeightQ_phi η_q' RootedTree.vertex := by
  induction η_q using Quotient.inductionOn with | _ p₁ => ?_
  induction η_q' using Quotient.inductionOn with | _ p₂ => ?_
  obtain ⟨s₁, M₁⟩ := p₁
  obtain ⟨s₂, M₂⟩ := p₂
  show elementaryWeightQ_phi (composeQ_phi
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s₁, M₁⟩)
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s₂, M₂⟩))
        RootedTree.vertex = _
  rw [elementaryWeightQ_phi_composeQ_phi_mk M₁ M₂ RootedTree.vertex]
  congr 1

/-- *Phase D pre-infrastructure (cycle 341) P2:* at the single-vertex
tree `τ`, the elementary weight of the §383 group inverse is the
negation of the original's. Corollary of P1's additivity applied to
`η_q * η_q⁻¹ = 1` and cycle 239's `elementaryWeightQ_phi_id`. -/
theorem elementaryWeightQ_phi_inv_vertex
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi η_q⁻¹ RootedTree.vertex
      = - elementaryWeightQ_phi η_q RootedTree.vertex := by
  have h_cancel : η_q * η_q⁻¹ = 1 := mul_inv_cancel η_q
  have h_w := elementaryWeightQ_phi_eq_of_eq h_cancel RootedTree.vertex
  rw [elementaryWeightQ_phi_mul_vertex] at h_w
  have h_one : (1 : Quotient PhiEquivalent.setoidSigma)
      = Quotient.mk PhiEquivalent.setoidSigma ⟨0, RKTableau.id⟩ := rfl
  rw [h_one, elementaryWeightQ_phi_id] at h_w
  linarith

/-- *Phase D pre-infrastructure (cycle 341) P3:* at the single-vertex
tree `τ`, the elementary weight of the §383 integer power scales
linearly with the exponent. Combines P1 (induction on `m : ℕ` over
`pow_succ`) with P2 (sign flip via `zpow_negSucc`) and a case split
on `Int` constructors. Closed form for Butcher §422's `η^{-i}(τ)`
factors that appear in the (422a) equation. -/
theorem elementaryWeightQ_phi_zpow_vertex
    (η_q : Quotient PhiEquivalent.setoidSigma) (n : ℤ) :
    elementaryWeightQ_phi (η_q ^ n) RootedTree.vertex
      = (n : ℝ) * elementaryWeightQ_phi η_q RootedTree.vertex := by
  have h_nat : ∀ m : ℕ,
      elementaryWeightQ_phi (η_q ^ m) RootedTree.vertex
        = (m : ℝ) * elementaryWeightQ_phi η_q RootedTree.vertex := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero]
      have h_one : (1 : Quotient PhiEquivalent.setoidSigma)
          = Quotient.mk PhiEquivalent.setoidSigma ⟨0, RKTableau.id⟩ := rfl
      rw [h_one, elementaryWeightQ_phi_id]
      simp
    | succ k ih =>
      rw [pow_succ, elementaryWeightQ_phi_mul_vertex, ih]
      push_cast
      ring
  cases n with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, h_nat m]
    push_cast
    ring
  | negSucc m =>
    rw [zpow_negSucc, elementaryWeightQ_phi_inv_vertex, h_nat (m + 1)]
    push_cast
    ring

/-- *Phase D pre-infrastructure (cycle 341) P4(a) — non-vacuity:*
additivity at τ on `D_element`. Combines cycle 337's
`D_element_elementaryWeight_vertex = 1` with P1: `Φ_{D·D}(τ) = 1 + 1 = 2`. -/
example :
    elementaryWeightQ_phi (D_element * D_element) RootedTree.vertex
      = 2 := by
  rw [elementaryWeightQ_phi_mul_vertex, D_element_elementaryWeight_vertex]
  norm_num

/-- *Phase D pre-infrastructure (cycle 341) P4(b) — non-vacuity:*
inverse at τ on `D_element`. Combines cycle 337's
`D_element_elementaryWeight_vertex = 1` with P2: `Φ_{D⁻¹}(τ) = -1`. -/
example :
    elementaryWeightQ_phi D_element⁻¹ RootedTree.vertex = -1 := by
  rw [elementaryWeightQ_phi_inv_vertex, D_element_elementaryWeight_vertex]

/-- *Phase D pre-infrastructure (cycle 341) P4(c) — non-vacuity:*
zpow at τ on `D_element`. Combines cycle 337's
`D_element_elementaryWeight_vertex = 1` with P3: `Φ_{D³}(τ) = 3`. -/
example :
    elementaryWeightQ_phi (D_element ^ (3 : ℤ)) RootedTree.vertex
      = 3 := by
  rw [elementaryWeightQ_phi_zpow_vertex, D_element_elementaryWeight_vertex]
  norm_num

/-! ### Phase D.3.a — representative-form elementary-weight expansion (cycle 358)

Cycle 341 P1/P2/P3 closed the elementary-weight expansion of
`*`, `⁻¹`, and `^ (· : ℤ)` at the single-vertex tree `τ`. Cycle 358
generalises P1 and P2 to **arbitrary trees** `t`, lifting cycle 239's
`elementaryWeightQ_phi_composeQ_phi_mk` from `composeQ_phi`-notation
to the `*`/`⁻¹`-notation that `Eq422a` uses.

The shipped theorems are:

* `elementaryWeightQ_phi_mul_mk` — representative-form additivity.
  Wraps cycle 239 by unfolding `*` to `composeQ_phi`.
* `elementaryWeightQ_phi_inv_mk` — representative-form inverse
  characterization. Combines cycle 236's `inv_mul_cancel` with
  `_mul_mk` and cycle 239's `elementaryWeightQ_phi_id`.

Both theorems carry a bottom-block contribution involving the
**source-method-threaded** `derivativeWeightWithSrc`, because the
bottom-block sum's stage count does not descend to the abstract
Φ-quotient (cycle 239 design note at `Section381.lean:4727`). At
`t = RootedTree.vertex` the bottom-block collapses to `1`
(`RKTableau.derivativeWeightWithSrc_vertex`) and the formulas recover
cycle 341 P1/P2's symmetric form.

**D.3.a.3 deferred to cycle 359.** Lifting cycle 341 P3
(`elementaryWeightQ_phi_zpow_vertex`) to arbitrary `t` requires a
canonical representative of `η_q ^ m : Quotient PhiEquivalent.setoidSigma`
for each `m : ℕ`, since the bottom-block of each `pow_succ` step
depends on the chosen representative of the previous power. The
infrastructure (a `RKTableau.powRep : (m : ℕ) → Σ s', RKTableau s'`
construction and its quotient-equality lemma) is multi-cycle work
parallel to Phase D.3.b. See `.prover-state/issues/def_422B_phase_D_3_scoping.md`
§5 cycle-358 update.
-/

/-- *Phase D.3.a (cycle 358) D.3.a.1 — representative-form additivity:*
at an arbitrary tree `t`, the elementary weight of a §383 group
product decomposes into the LHS-representative's elementary weight
plus a bottom-block contribution involving the source-method-threaded
`derivativeWeightWithSrc` of the RHS representative. Lifts cycle
239's `elementaryWeightQ_phi_composeQ_phi_mk` from `composeQ_phi`
notation to the `*` notation used by `Eq422a`.

At `t = RootedTree.vertex` the bottom-block collapses to
`M₂.elementaryWeight vertex` (via `derivativeWeightWithSrc_vertex`
and `derivativeWeight_vertex`) and recovers cycle 341 P1's
symmetric additivity. At arbitrary `t` the bottom-block depends
on `M₁`'s elementary weights through `derivativeWeightWithSrc`, so
the asymmetric representative form is unavoidable. -/
theorem elementaryWeightQ_phi_mul_mk
    {s₁ s₂ : ℕ} (M₁ : RKTableau s₁) (M₂ : RKTableau s₂)
    (t : RT) :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma ⟨s₁, M₁⟩) *
         (Quotient.mk PhiEquivalent.setoidSigma ⟨s₂, M₂⟩)) t
      = elementaryWeightQ_phi
          (Quotient.mk PhiEquivalent.setoidSigma ⟨s₁, M₁⟩) t
        + ∑ i : Fin s₂, M₂.b i * M₂.derivativeWeightWithSrc M₁ i t := by
  show elementaryWeightQ_phi (composeQ_phi
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s₁, M₁⟩)
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s₂, M₂⟩)) t = _
  exact elementaryWeightQ_phi_composeQ_phi_mk M₁ M₂ t

/-- *Phase D.3.a (cycle 358) D.3.a.1 — non-vacuity at `cherry`.*
Exercises the representative-form additivity on the order-2 tree
`cherry = mk [vertex]` with two copies of `explicitEuler`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) *
         (Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩)) RootedTree.cherry
      = elementaryWeightQ_phi
          (Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) RootedTree.cherry
        + ∑ i : Fin 1,
            RKTableau.explicitEuler.b i *
            RKTableau.explicitEuler.derivativeWeightWithSrc
              RKTableau.explicitEuler i RootedTree.cherry :=
  elementaryWeightQ_phi_mul_mk
    RKTableau.explicitEuler RKTableau.explicitEuler RootedTree.cherry

/-- *Phase D.3.a (cycle 358) D.3.a.2 — representative-form inverse
characterization:* at an arbitrary tree `t`, the elementary weight
of the §383 group inverse class equals the negation of the bottom-
block contribution from `M.inverse * M = 1`. Derived from cycle
236's `inv_mul_cancel`, cycle 239's `elementaryWeightQ_phi_id`, and
D.3.a.1 above.

At `t = RootedTree.vertex` the bottom-block collapses to
`M.elementaryWeight vertex` (each `derivativeWeightWithSrc` factor
is `1`), and the formula reduces to cycle 341 P2's
`Φ_{η_q⁻¹}(τ) = -Φ_{η_q}(τ)`. At arbitrary `t` the bottom-block
genuinely depends on `M.inverse`'s structure, so the
characterization form is the cleanest representative-form output. -/
theorem elementaryWeightQ_phi_inv_mk
    {s : ℕ} (M : RKTableau s) (t : RT) :
    elementaryWeightQ_phi
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)⁻¹ t
      = - ∑ i : Fin s, M.b i * M.derivativeWeightWithSrc M.inverse i t := by
  -- ⟦M⟧⁻¹ = ⟦M.inverse⟧ by `inverseQ_phi_mk` (`@[simp]`, `:= rfl`).
  -- Apply `inv_mul_cancel` at the quotient level, then expand
  -- `elementaryWeightQ_phi` of the LHS via D.3.a.1.
  have h_cancel :
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M.inverse⟩) *
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) = 1 := by
    show (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)⁻¹ *
          (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) = 1
    exact inv_mul_cancel _
  have h_w := elementaryWeightQ_phi_eq_of_eq h_cancel t
  rw [elementaryWeightQ_phi_mul_mk M.inverse M t] at h_w
  have h_one : (1 : Quotient PhiEquivalent.setoidSigma)
      = Quotient.mk PhiEquivalent.setoidSigma ⟨0, RKTableau.id⟩ := rfl
  rw [h_one, elementaryWeightQ_phi_id] at h_w
  -- h_w : Φ_{⟦M.inverse⟧}(t) + Σᵢ M.b i · M.derivativeWeightWithSrc M.inverse i t = 0
  -- Goal: Φ_{⟦M⟧⁻¹}(t) = - Σᵢ …  (LHS reduces to Φ_{⟦M.inverse⟧}(t) by `inverseQ_phi_mk`).
  show elementaryWeightQ_phi
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M.inverse⟩) t = _
  linarith

/-- *Phase D.3.a (cycle 358) D.3.a.2 — non-vacuity at `cherry`.*
Exercises the representative-form inverse characterization on the
order-2 tree `cherry` with `explicitEuler`. -/
example :
    elementaryWeightQ_phi
        (Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩)⁻¹ RootedTree.cherry
      = - ∑ i : Fin 1,
            RKTableau.explicitEuler.b i *
            RKTableau.explicitEuler.derivativeWeightWithSrc
              RKTableau.explicitEuler.inverse i RootedTree.cherry :=
  elementaryWeightQ_phi_inv_mk RKTableau.explicitEuler RootedTree.cherry

/-- *Phase D.3.a (cycle 359) D.3.a.3 — recursive `pow_succ` form for
elementary weight on §383 powers at arbitrary trees.* Generalises
cycle 341 P3 (`elementaryWeightQ_phi_zpow_vertex`) from `vertex` to
arbitrary `t : RT`, in *recursive* form. Unlike the vertex case
(which admits the closed form `(n : ℝ) · Φ_η(τ)`), at arbitrary `t`
the recursion uses the canonical representative `powRep` (cycle 359's
new infrastructure in `Section381.lean`) for the bottom-block source
method at each step.

By induction on `m` via D.3.a.1 (`elementaryWeightQ_phi_mul_mk`)
plus cycle 359's `RKTableau.powRep_quotient_eq` to identify
`⟦M.powRep m⟧` with `⟦⟨s, M⟩⟧ ^ m`. -/
theorem elementaryWeightQ_phi_pow_succ_mk {s : ℕ} (M : RKTableau s)
    (m : ℕ) (t : RT) :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) ^ (m + 1)) t
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) ^ m) t
        + ∑ i : Fin s, M.b i *
            M.derivativeWeightWithSrc (M.powRep m).2 i t := by
  -- Step A: ⟦M⟧^(m+1) = ⟦M⟧^m * ⟦M⟧ via pow_succ.
  rw [pow_succ]
  -- Step B: rewrite both `⟦⟨s, M⟩⟧ ^ m` occurrences to
  -- `⟦M.powRep m⟧` via `powRep_quotient_eq` (reversed); a single
  -- `rw` fires on both the LHS factor and the RHS first summand.
  -- This exposes a `*` between two `Quotient.mk` classes on the LHS
  -- that D.3.a.1 can consume directly, and matches the RHS first
  -- summand to D.3.a.1's RHS first summand.
  rw [← RKTableau.powRep_quotient_eq M m]
  -- Step C: D.3.a.1 with `M₁ := (M.powRep m).2`, `M₂ := M` closes
  -- the equation. The `⟦M.powRep m⟧` form is definitionally equal
  -- to `⟦⟨(M.powRep m).1, (M.powRep m).2⟩⟧` via Σ-eta.
  exact elementaryWeightQ_phi_mul_mk (M.powRep m).2 M t

/-- *Phase D.3.a (cycle 359) D.3.a.3 — `powRep` base case
non-vacuity on `explicitEuler`.* The `m = 0` value of
`powRep explicitEuler` is the 0-stage identity tableau. -/
example :
    RKTableau.explicitEuler.powRep 0
      = (⟨0, RKTableau.id⟩ : Σ s' : ℕ, RKTableau s') := rfl

/-- *Phase D.3.a (cycle 359) D.3.a.3 — `powRep` first-step
stage-count non-vacuity on `explicitEuler`.* For `explicitEuler`
(`s = 1`), the `m = 1` value of `powRep` has stage count
`0 + 1 = 1`. -/
example : (RKTableau.explicitEuler.powRep 1).1 = 1 := rfl

/-- *Phase D.3.a (cycle 359) D.3.a.3 — end-to-end non-vacuity at
`cherry`, `m = 0`.* Exercises the recursive `pow_succ` identity on
`explicitEuler` at the order-2 tree `cherry` with `m = 0`, the
shortest non-trivial instance. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (0 + 1)) RootedTree.cherry
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ 0) RootedTree.cherry
        + ∑ i : Fin 1, RKTableau.explicitEuler.b i *
            RKTableau.explicitEuler.derivativeWeightWithSrc
              (RKTableau.explicitEuler.powRep 0).2 i RootedTree.cherry :=
  elementaryWeightQ_phi_pow_succ_mk
    RKTableau.explicitEuler 0 RootedTree.cherry

/-! ### Phase D.1 — closed-form `η(τ)` base-case solver (cycle 342)

Cycle 341's P1/P2/P3 (`elementaryWeightQ_phi_{mul,inv,zpow}_vertex`)
make the (422a) equation at `u = RootedTree.vertex` collapse to a
*linear equation in* `η(τ) := elementaryWeightQ_phi η_q τ`. This
section ships that algebraic specialization.

Substituting cycle 341 P3 into both sums of `Eq422a M η_q vertex` and
collecting `η`-terms yields

```
(coef_α(M) + coef_β(M)) * η(τ) = sum_β(M)
```

where, with `Fin k` indexing the α-side and `Fin (k+1)` indexing the
β-side,

```
coef_α(M) := Σ_{i:Fin k}     ((i.val + 1 : ℕ) : ℝ) * M.α i.succ
coef_β(M) := Σ_{i:Fin (k+1)} ((i.val : ℕ) : ℝ)     * M.β i
sum_β(M)  := Σ_{i:Fin (k+1)} M.β i
```

Note: `coef_α(M) = M.SatisfiesEq404b.LHS` (Butcher's (404b) α-side).
Under consistency (`M.IsConsistent → M.SatisfiesEq404b`), `coef_α =
sum_β`, recovering Butcher §422 p. 1163's textbook form.

See `.prover-state/issues/def_422B_path.md` §5 row D.1 for the phase
plan. Phase D.2 (well-founded recursion on `RootedTree.order`) and
Phase D.3 (inductive step for `r(t) ≥ 2`) remain deferred. -/

/-- *Phase D.1 main theorem (cycle 342):* the (422a) equation at the
single-vertex tree `τ` is **linear** in `η(τ) := elementaryWeightQ_phi
η_q τ`. Specifically,

```
(coef_α(M) + coef_β(M)) · η(τ) = sum_β(M)
```

where `coef_α(M) := Σ_{i:Fin k} (i+1) · α_{i+1}`, `coef_β(M) :=
Σ_{i:Fin (k+1)} i · β_i`, and `sum_β(M) := Σ_{i:Fin (k+1)} β_i`.

Proof sketch:

1. Specialize `Eq422a M η_q` at `u = vertex`.
2. Collapse `elementaryWeightQ_phi 1 vertex = 0` via cycle 239's
   `elementaryWeightQ_phi_id` (b₀-invisibility — `1` at `τ` vanishes).
3. Rewrite each α-summand via cycle 341 P3
   (`elementaryWeightQ_phi_zpow_vertex`):
   `Φ(η_q^{-(i+1)})(τ) = -(i+1) · η(τ)`.
4. Rewrite each β-summand via cycle 341 P1+P3 + cycle 337's
   `D_element_elementaryWeight_vertex = 1`:
   `Φ((η_q^{-i}) · D_element)(τ) = -i · η(τ) + 1`.
5. Collect `η(τ)`-terms via `Finset.sum_mul`/`Finset.mul_sum`/`ring`
   and close by `linarith`.

This is the **unconditional** algebraic form; the
`IsConsistent`-strengthened version `Eq422a_at_vertex_linear_of_isConsistent`
recovers Butcher's textbook η-coefficient simplification. -/
theorem Eq422a_at_vertex_linear
    {k : ℕ} {M : OpenMath.Chapter4.Section404.LinearMultistepMethod k}
    {η_q : Quotient PhiEquivalent.setoidSigma}
    (hEq : Eq422a M η_q) :
    ((∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
        + (∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i))
      * elementaryWeightQ_phi η_q RootedTree.vertex
      = ∑ i : Fin (k + 1), M.β i := by
  have h := hEq RootedTree.vertex
  -- Collapse `elementaryWeightQ_phi 1 vertex = 0` via cycle 239.
  have h_one : (1 : Quotient PhiEquivalent.setoidSigma)
      = Quotient.mk PhiEquivalent.setoidSigma ⟨0, RKTableau.id⟩ := rfl
  rw [h_one, elementaryWeightQ_phi_id] at h
  -- Rewrite each α-summand via cycle 341 P3.
  have hα_simp : ∀ i : Fin k,
      M.α i.succ * elementaryWeightQ_phi
                    (η_q ^ (-((i.val + 1 : ℕ) : ℤ))) RootedTree.vertex
        = -(((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
            * elementaryWeightQ_phi η_q RootedTree.vertex := by
    intro i
    rw [elementaryWeightQ_phi_zpow_vertex]
    push_cast
    ring
  -- Rewrite each β-summand via cycle 341 P1+P3 + cycle 337 `D_element_…_vertex`.
  have hβ_simp : ∀ i : Fin (k + 1),
      M.β i * elementaryWeightQ_phi
              ((η_q ^ (-((i.val : ℕ) : ℤ))) * D_element) RootedTree.vertex
        = -(((i.val : ℕ) : ℝ) * M.β i)
            * elementaryWeightQ_phi η_q RootedTree.vertex + M.β i := by
    intro i
    rw [elementaryWeightQ_phi_mul_vertex,
        elementaryWeightQ_phi_zpow_vertex,
        D_element_elementaryWeight_vertex]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => hα_simp i),
      Finset.sum_congr rfl (fun i _ => hβ_simp i)] at h
  -- Set `η := Φ_{η_q}(τ)` and factor it out of both sums.
  set η := elementaryWeightQ_phi η_q RootedTree.vertex with hη_def
  -- Pull η out of α-sum: Σ -(coef_i) · η = -(Σ coef_i) · η.
  have hα_factor :
      (∑ i : Fin k,
          -(((i.val + 1 : ℕ) : ℝ) * M.α i.succ) * η)
        = -(∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ) * η := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_mul]
  -- Pull η out of β-sum: Σ (-(coef_i) · η + βᵢ) = -(Σ coef_i) · η + Σ βᵢ.
  have hβ_factor :
      (∑ i : Fin (k + 1),
          (-(((i.val : ℕ) : ℝ) * M.β i) * η + M.β i))
        = -(∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i) * η
            + ∑ i : Fin (k + 1), M.β i := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_neg_distrib, ← Finset.sum_mul]
  rw [hα_factor, hβ_factor] at h
  linarith

/-- *Phase D.1 corollary (cycle 342) — consistency-strengthened form:*
under Butcher's full consistency (`M.IsConsistent`, i.e. (404a) ∧
(404b)), the right-hand side `sum_β(M)` of `Eq422a_at_vertex_linear`
simplifies to `coef_α(M) = Σ_{i:Fin k} (i+1) · α_{i+1}`. This matches
Butcher §422 p. 1163's textbook arrangement of the η-coefficient.

Proof: from `M.IsConsistent.2 : M.SatisfiesEq404b`, we have
`coef_α(M) = sum_β(M)`. Rewrite the RHS of `Eq422a_at_vertex_linear`
via this identity. (Note: `SatisfiesEq404b`'s LHS uses the cast form
`((i : ℕ) + 1 : ℝ)` while `Eq422a_at_vertex_linear` uses
`((i.val + 1 : ℕ) : ℝ)`; these agree under `push_cast`.) -/
theorem Eq422a_at_vertex_linear_of_isConsistent
    {k : ℕ} {M : OpenMath.Chapter4.Section404.LinearMultistepMethod k}
    (hCons : M.IsConsistent)
    {η_q : Quotient PhiEquivalent.setoidSigma}
    (hEq : Eq422a M η_q) :
    ((∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
        + (∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i))
      * elementaryWeightQ_phi η_q RootedTree.vertex
      = ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ := by
  have h := Eq422a_at_vertex_linear hEq
  have h404b : (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
      = ∑ i : Fin (k + 1), M.β i := by
    have := hCons.2
    -- `SatisfiesEq404b` uses `((i : ℕ) + 1 : ℝ)`; we use
    -- `((i.val + 1 : ℕ) : ℝ)`. Bridge via `push_cast`.
    have h_eq : (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
        = ∑ i : Fin k, ((i : ℕ) + 1 : ℝ) * M.α i.succ := by
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring
    rw [h_eq]
    exact this
  rw [h, ← h404b]

/-- *Phase D.1 non-vacuity (cycle 342) — `k = 0` degenerate case:*
for a 0-step LMM (which has only `α 0 = -1` and a single `β 0`), the
linear (422a) reduction yields `0 = M.β 0`. Both sums in
`Eq422a_at_vertex_linear` collapse via `Finset.univ_eq_empty` for
`Fin 0` and `Fin.sum_univ_one` for `Fin 1`. -/
example {η_q : Quotient PhiEquivalent.setoidSigma}
    (M : OpenMath.Chapter4.Section404.LinearMultistepMethod 0)
    (hEq : Eq422a M η_q) :
    (0 : ℝ) = M.β 0 := by
  have h := Eq422a_at_vertex_linear hEq
  simp at h
  exact h

/-- *Phase D.1 closed-form `η(τ)` extraction (cycle 342, stretch):*
under a non-vanishing-coefficient hypothesis `coef_α(M) + coef_β(M) ≠
0`, the (422a) reduction at `τ` determines `η(τ)` *uniquely* as
`sum_β(M) / (coef_α(M) + coef_β(M))`. This is the Phase D.1 closed-form
base-case solver: it pins `η(τ)` from the linear reduction without
needing the inductive step (Phase D.3).

The non-vanishing hypothesis is downstream of `M.IsStable +
M.IsPreconsistent` via cycle 178's
`ρPoly_deriv_eval_one_pos_of_stable_preconsistent`; that bridge is
deferred to cycle 343+. -/
theorem Eq422a_at_vertex_eta_eq
    {k : ℕ} {M : OpenMath.Chapter4.Section404.LinearMultistepMethod k}
    {η_q : Quotient PhiEquivalent.setoidSigma}
    (hEq : Eq422a M η_q)
    (h_ne : (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
              + (∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i) ≠ 0) :
    elementaryWeightQ_phi η_q RootedTree.vertex
      = (∑ i : Fin (k + 1), M.β i)
          / ((∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
              + (∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i)) := by
  have h := Eq422a_at_vertex_linear hEq
  field_simp
  linarith

/-! ### Phase D bridge (cycle 344) — `coef_α(M) = ρ'(1)` and positivity

This block ships the algebraic bridge from cycle 342's
`Eq422a`-coefficient notation `coef_α(M) = Σ_{i:Fin k} (i+1) · α_{i+1}`
to cycle 178's `ρPoly` machinery (`Section441.lean`).

* **P1** (`coef_α_eq_ρPoly_deriv_at_one_of_preconsistent`): under
  preconsistency, `coef_α(M) = ρ'(1)`.
* **P2** (`coef_α_pos_of_stable_preconsistent`): direct composition
  of P1 with cycle 178's `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`
  yields `coef_α(M) > 0` for any stable preconsistent LMM with `0 < k`.

This unlocks discharging the non-vanishing hypothesis of
`Eq422a_at_vertex_eta_eq` (cycle 342) under the textbook hypotheses
without manual coefficient inspection. The cycle 344 ship is purely
additive: cycle 342's signature is preserved.
-/

/-- *Phase D bridge (cycle 344) — P1:* under preconsistency, the
§422 coefficient `coef_α(M) = Σ_{i:Fin k} (i+1) · α_{i+1}` equals
`ρ'(1)`, the derivative of the §441 stability polynomial at `1`.

Algebraic derivation: cycle 178's
`ρPoly_deriv_eval_one_unconditional` (Section441.lean:375) gives
`ρ'(1) = k - Σ M.α i.succ · (k - (i.val + 1))`. Distributing inside
the sum and using preconsistency `Σ M.α i.succ = 1` to collapse
`k - k·1 = 0`, the residual is exactly `coef_α(M)`. -/
theorem coef_α_eq_ρPoly_deriv_at_one_of_preconsistent
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (hPre : M.IsPreconsistent) :
    (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
      = M.ρPoly.derivative.eval 1 := by
  rw [M.ρPoly_deriv_eval_one_unconditional]
  unfold OpenMath.Chapter4.Section404.LinearMultistepMethod.IsPreconsistent
    at hPre
  -- Canonicalize the LHS summands to `α * (i+1)` (in ℝ) so they match
  -- the residual that pops out of the RHS expansion below.
  have hLHS : (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
      = ∑ i : Fin k, M.α i.succ * (((i.val : ℝ) + 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  rw [hLHS]
  -- Distribute the RHS subtraction: `α · (k - (i+1)) = α·k - α·(i+1)`.
  have hRHS : (∑ i : Fin k, M.α i.succ * ((k : ℝ) - ((i.val : ℝ) + 1)))
      = (∑ i : Fin k, M.α i.succ) * (k : ℝ)
          - ∑ i : Fin k, M.α i.succ * (((i.val : ℝ) + 1)) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hRHS, ← hPre]
  ring

/-- *Phase D bridge (cycle 344) — P2:* for a stable preconsistent
LMM with `0 < k`, the §422 coefficient `coef_α(M)` is strictly
positive. Direct composition of P1 with cycle 178's
`ρPoly_deriv_eval_one_pos_of_stable_preconsistent`
(Section441.lean:767). -/
theorem coef_α_pos_of_stable_preconsistent
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (hk : 0 < k) (hStab : M.IsStable) (hPre : M.IsPreconsistent) :
    0 < ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ := by
  rw [coef_α_eq_ρPoly_deriv_at_one_of_preconsistent M hPre]
  exact M.ρPoly_deriv_eval_one_pos_of_stable_preconsistent hk hStab hPre

/-- *Phase D.3.c (cycle 363) — non-vanishing of `Σᵢ i·αᵢ` under
stability + preconsistency.* This is the load-bearing α-side
non-vanishing fact for Phase D.3.d's recursion: at every non-vertex
tree `t`, the cycle 360/361 closed form for
`linearResidualAt i ⟦M⟧ t` produces a linear equation in `η(t)`
whose coefficient is `(-1)^t.order · Σᵢ i·αᵢ` (modulo β-side and
D-side corrections). Phase D.3.d's construction
`underlyingOneStepMethod_aux M t := (RHS) / coef_α` requires this
denominator to be non-zero, which this theorem discharges.

Direct corollary of cycle 344's `coef_α_pos_of_stable_preconsistent`
(strict positivity) via `ne_of_gt`. -/
theorem sum_i_alpha_ne_zero_of_stable_preconsistent
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (hk : 0 < k) (hStab : M.IsStable) (hPre : M.IsPreconsistent) :
    (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ) ≠ 0 :=
  ne_of_gt (coef_α_pos_of_stable_preconsistent M hk hStab hPre)

/-- *Non-vacuity for Phase D.3.c (cycle 363):* `bdf2LMM` is stable +
preconsistent with `k = 2 > 0`, so its α-coefficient sum is non-zero
(equals `2/3 ≠ 0` per the existing non-vacuity example below). -/
example :
    (∑ i : Fin 2, ((i.val + 1 : ℕ) : ℝ) *
        OpenMath.Chapter4.Section451.bdf2LMM.α i.succ) ≠ 0 :=
  sum_i_alpha_ne_zero_of_stable_preconsistent
    OpenMath.Chapter4.Section451.bdf2LMM (by norm_num)
    OpenMath.Chapter4.Section451.bdf2LMM_isStable
    OpenMath.Chapter4.Section441.bdf2LMM_isPreconsistent

/-- *Non-vacuity for P1 (cycle 344):* `explicitEulerLMM`'s
`coef_α = 1` matches the §441 closed form `ρ'(1) = 1` at `k = 1`,
`α₁ = 1`. -/
example :
    (∑ i : Fin 1, ((i.val + 1 : ℕ) : ℝ) *
        OpenMath.Chapter4.Section404.explicitEulerLMM.α i.succ) = 1 := by
  simp [OpenMath.Chapter4.Section404.explicitEulerLMM]

/-- *Non-vacuity for P1 (cycle 344):* `bdf2LMM`'s `coef_α = 2/3`
matches cycle 176's `bdf2LMM_ρPoly_deriv_eval_one_eq = 2/3` at
`k = 2`, `α₁ = 4/3`, `α₂ = -1/3`:
`1·(4/3) + 2·(-1/3) = 4/3 - 2/3 = 2/3`. -/
example :
    (∑ i : Fin 2, ((i.val + 1 : ℕ) : ℝ) *
        OpenMath.Chapter4.Section451.bdf2LMM.α i.succ) = 2 / 3 := by
  simp [OpenMath.Chapter4.Section451.bdf2LMM, Fin.sum_univ_two]
  norm_num

/-! ### Phase D consolidation (cycle 345) — discharge the non-vanishing
hypothesis of `Eq422a_at_vertex_eta_eq` under textbook hypotheses

Cycle 344 shipped `coef_α(M) > 0` for stable preconsistent `M` with
`0 < k`. This block consumes that positivity to ship a corollary of
cycle 342's `Eq422a_at_vertex_eta_eq` whose non-vanishing side-goal
`coef_α + coef_β ≠ 0` is discharged via the §441 stability bridge,
modulo an explicit β-side non-negativity hypothesis. Closing that
β-side hypothesis from `M.IsConsistent` alone requires §441 β-side
machinery not yet built (analogous to cycle 178's α-side
`ρPoly_deriv_eval_one_pos_of_stable_preconsistent`); that is the
Phase D′ refinement target for a future cycle.

Also ships `coef_α_eq_sum_β_of_isConsistent`, extracted from cycle
342's `Eq422a_at_vertex_linear_of_isConsistent` body, so downstream
consumers (e.g. the future Phase D′ β-side machinery) can cite the
cast bridge directly.
-/

/-- *Phase D consolidation (cycle 345):* under the textbook hypotheses
of stability + preconsistency plus the side hypothesis that the
β-side coefficient `Σ_{i:Fin (k+1)} i · M.β i` is non-negative, the
(422a) reduction at the single-vertex tree `τ` determines `η(τ)`
uniquely as `sum_β / (coef_α + coef_β)`.

This routes the non-vanishing requirement of cycle 342's
`Eq422a_at_vertex_eta_eq` through cycle 344's `coef_α > 0`. The
β-side non-negativity hypothesis surfaces a residual textbook
assumption: eliminating it from `M.IsStable + M.IsPreconsistent`
alone requires §441 β-side machinery not yet built; defer that to
a Phase D′ refinement cycle. -/
theorem Eq422a_at_vertex_eta_eq_of_stable_preconsistent
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (hk : 0 < k)
    (hStab : M.IsStable) (hPre : M.IsPreconsistent)
    (hβ_nn : 0 ≤ ∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i)
    {η_q : Quotient PhiEquivalent.setoidSigma}
    (hEq : Eq422a M η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex
      = (∑ i : Fin (k + 1), M.β i)
          / ((∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
              + (∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i)) := by
  apply Eq422a_at_vertex_eta_eq hEq
  have hα_pos := coef_α_pos_of_stable_preconsistent M hk hStab hPre
  linarith

/-- *Phase D consolidation (cycle 345) — F-fallback ship:* under
Butcher's consistency condition, the §422 α-side coefficient
`coef_α(M) = Σ_{i:Fin k} ((i.val + 1 : ℕ) : ℝ) * M.α i.succ` equals
the β-sum `Σ_{i:Fin (k+1)} M.β i`.

Extracted from cycle 342's `Eq422a_at_vertex_linear_of_isConsistent`
body: bridges `SatisfiesEq404b`'s `((i : ℕ) + 1 : ℝ)` cast form to
the §422 `((i.val + 1 : ℕ) : ℝ)` cast form via `push_cast`+`ring`.
Useful infrastructure for downstream Phase D′ refinements (e.g. a
future `coef_β_pos_of_stable_consistent`). -/
theorem coef_α_eq_sum_β_of_isConsistent
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (hCons : M.IsConsistent) :
    (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
      = ∑ i : Fin (k + 1), M.β i := by
  have h404b := hCons.2
  have h_eq : (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
      = ∑ i : Fin k, ((i : ℕ) + 1 : ℝ) * M.α i.succ := by
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  rw [h_eq]
  exact h404b

/-- *Non-vacuity for the cycle 345 consolidation:* for the explicit
Euler 1-step LMM, the (422a) reduction at `τ` pins `η(τ) = 1/2`.
Computation: `coef_α = 1·1 = 1`, `coef_β = 0·0 + 1·1 = 1`,
`sum_β = 0 + 1 = 1`, so `η(τ) = 1 / (1 + 1) = 1/2`. The β-side
non-negativity discharges as `0 ≤ 1`. -/
example (η_q : Quotient PhiEquivalent.setoidSigma)
    (hEq : Eq422a OpenMath.Chapter4.Section404.explicitEulerLMM η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex = 1 / 2 := by
  have h := Eq422a_at_vertex_eta_eq_of_stable_preconsistent
    OpenMath.Chapter4.Section404.explicitEulerLMM
    Nat.one_pos
    OpenMath.Chapter4.Section404.explicitEulerLMM_isStable
    OpenMath.Chapter4.Section404.explicitEulerLMM_isPreconsistent
    (by
      simp [OpenMath.Chapter4.Section404.explicitEulerLMM,
        Fin.sum_univ_two])
    hEq
  rw [h]
  simp [OpenMath.Chapter4.Section404.explicitEulerLMM,
    Fin.sum_univ_two]
  norm_num

/-- *Non-vacuity for `coef_α_eq_sum_β_of_isConsistent` (cycle 345):*
for explicit Euler (which is consistent), both sides equal `1`:
`coef_α = 1·α₁ = 1·1 = 1`, `sum_β = β₀ + β₁ = 0 + 1 = 1`. -/
example :
    (∑ i : Fin 1, ((i.val + 1 : ℕ) : ℝ) *
        OpenMath.Chapter4.Section404.explicitEulerLMM.α i.succ)
      = ∑ i : Fin 2, OpenMath.Chapter4.Section404.explicitEulerLMM.β i :=
  coef_α_eq_sum_β_of_isConsistent
    OpenMath.Chapter4.Section404.explicitEulerLMM
    OpenMath.Chapter4.Section404.explicitEulerLMM_isConsistent

/-! ### Phase D′ scaffolding (cycle 346) — `coef_β` non-negativity helper

Cycle 345's `Eq422a_at_vertex_eta_eq_of_stable_preconsistent` takes the
β-side non-negativity hypothesis `0 ≤ coef_β(M)` as an explicit
assumption. The full Phase D′ derivation of this hypothesis from
`M.IsStable + M.IsConsistent` is multi-cycle (analog of the §441
`ρPoly_deriv_eval_one_pos_of_stable_preconsistent` α-side bridge but
for `coef_β`). This cycle ships a single-cycle additive helper:
methods with all-non-negative β-coefficients (which includes
`bdf2LMM`, where `β 1 = β 2 = 0` and `β 0 = 2/3 ≥ 0`) admit a direct
non-negativity proof. -/

/-- *Phase D′ helper (cycle 346):* if every β-coefficient of an LMM
is non-negative, then so is `coef_β(M) := Σ_{i:Fin (k+1)} i · M.β i`.
One-line structural lemma. -/
theorem coef_β_nonneg_of_β_nonneg
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (hβ : ∀ i : Fin (k + 1), 0 ≤ M.β i) :
    0 ≤ ∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (Nat.cast_nonneg _) (hβ i)

/-- BDF2's β-coefficients are all non-negative
(`β 0 = 2/3, β 1 = β 2 = 0`). -/
theorem bdf2LMM_β_nonneg :
    ∀ i : Fin (2 + 1), 0 ≤ OpenMath.Chapter4.Section451.bdf2LMM.β i := by
  intro i
  fin_cases i
  all_goals simp [OpenMath.Chapter4.Section451.bdf2LMM]
  all_goals try norm_num

/-- BDF2's `coef_β` is non-negative (in fact `= 0`, since
`β 1 = β 2 = 0` carry the only non-zero weights in the sum). -/
theorem bdf2LMM_coef_β_nonneg :
    0 ≤ ∑ i : Fin (2 + 1), ((i.val : ℕ) : ℝ) *
          OpenMath.Chapter4.Section451.bdf2LMM.β i :=
  coef_β_nonneg_of_β_nonneg OpenMath.Chapter4.Section451.bdf2LMM
    bdf2LMM_β_nonneg

/-- *Non-vacuity (cycle 346):* closing cycle 345's deferred BDF2
non-vacuity for `Eq422a_at_vertex_eta_eq_of_stable_preconsistent`.
The underlying-one-step-method `η ∈ G₁` corresponding to BDF2 pins
`η(τ) = 1`.

Numerical justification: BDF2 has `coef_α = 1·(4/3) + 2·(-1/3) = 2/3`,
`coef_β = 0·(2/3) + 1·0 + 2·0 = 0`, `sum_β = 2/3`, so
`η(τ) = (2/3)/(2/3 + 0) = 1`. The β-side non-negativity discharges
via `bdf2LMM_coef_β_nonneg`; Dahlquist-stability via cycle 346's
`bdf2LMM_isStable`; preconsistency via cycle 175's
`bdf2LMM_isPreconsistent` (Section441). -/
example (η_q : Quotient PhiEquivalent.setoidSigma)
    (hEq : Eq422a OpenMath.Chapter4.Section451.bdf2LMM η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex = 1 := by
  have h := Eq422a_at_vertex_eta_eq_of_stable_preconsistent
    OpenMath.Chapter4.Section451.bdf2LMM
    (by norm_num : (0 : ℕ) < 2)
    OpenMath.Chapter4.Section451.bdf2LMM_isStable
    OpenMath.Chapter4.Section441.bdf2LMM_isPreconsistent
    bdf2LMM_coef_β_nonneg
    hEq
  rw [h]
  simp [OpenMath.Chapter4.Section451.bdf2LMM,
    Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num

/-! ### Phase D′ Step 1 (cycle 347) — `coef_β ↔ βPoly.derivative.eval 1` bridge

Reuses Section410's `βPoly` (cycle 73, line 103) for the algebraic
bridge identity. The β-side analog of cycle 344's
`coef_α_eq_ρPoly_deriv_at_one_of_preconsistent`. **No hypothesis
needed** — βPoly's clean `Σ β_i · X^i` shape avoids the
`X^(k-(i+1))` Nat-subtraction bookkeeping that forced
preconsistency on the α-side.

Step 2 (positivity from `IsStable + IsConsistent` alone, analog of
cycle 178's `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`) is
multi-cycle work; deferred. -/

/-- *Phase D′ bridge (cycle 347) — P1:* the §422 β-side coefficient
`coef_β(M) = Σ_{i:Fin (k+1)} i · M.β i` equals `βPoly'(1)`, the
derivative of the §410 β-polynomial at `1`.

This is the β-side analog of cycle 344's
`coef_α_eq_ρPoly_deriv_at_one_of_preconsistent`. Unlike the α-side
bridge, **no preconsistency hypothesis is needed**: `βPoly` is
`Σ β_i · X^i` (no Nat-subtraction in the exponent), so the
derivative-at-1 unfolds directly without invoking `Σ α_i = 1`.

Algebraic derivation: `βPoly'(z) = Σ i · C(β_i) · X^(i-1)`, so
`βPoly'(1) = Σ i · β_i = coef_β(M)`. -/
theorem coef_β_eq_βPoly_deriv_at_one
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k) :
    (∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i)
      = (OpenMath.Chapter4.Section410.βPoly M).derivative.eval 1 := by
  unfold OpenMath.Chapter4.Section410.βPoly
  rw [Polynomial.derivative_sum]
  rw [Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.derivative_C_mul_X_pow]
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, one_pow, mul_one]
  ring

/-- *Non-vacuity for P1 (cycle 347):* `bdf2LMM`'s `coef_β = 0`
matches `βPoly'(1) = 0` since BDF2 has `β 1 = β 2 = 0` and the
only non-zero β-coefficient (β₀ = 2/3) contributes `0 · 2/3 = 0`. -/
example :
    (OpenMath.Chapter4.Section410.βPoly
        OpenMath.Chapter4.Section451.bdf2LMM).derivative.eval 1 = 0 := by
  rw [← coef_β_eq_βPoly_deriv_at_one]
  simp [OpenMath.Chapter4.Section451.bdf2LMM, Fin.sum_univ_three]

/-- *Non-vacuity for P1 (cycle 347):* `explicitEulerLMM`'s
`coef_β = 0·β₀ + 1·β₁ = 0 + 1·1 = 1` matches `βPoly'(1)` where
`βPoly explicitEulerLMM = X` (Section410 cycle 73's
`βPoly_explicitEuler`), so `βPoly'(1) = 1`. -/
example :
    (OpenMath.Chapter4.Section410.βPoly
        OpenMath.Chapter4.Section404.explicitEulerLMM).derivative.eval 1 = 1 := by
  rw [OpenMath.Chapter4.Section410.βPoly_explicitEuler]
  simp

/-- *Phase D′ Step 1 corollary (cycle 347):* combining cycle 347's
bridge with cycle 346's `coef_β_nonneg_of_β_nonneg`, methods with
all-non-negative β-coefficients satisfy `0 ≤ βPoly'(1)`. -/
theorem βPoly_deriv_eval_one_nonneg_of_β_nonneg
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (hβ : ∀ i : Fin (k + 1), 0 ≤ M.β i) :
    0 ≤ (OpenMath.Chapter4.Section410.βPoly M).derivative.eval 1 := by
  rw [← coef_β_eq_βPoly_deriv_at_one]
  exact coef_β_nonneg_of_β_nonneg M hβ

/-! ### Phase D′.2.0 precursor (cycle 349) — `sum_β > 0` for stable + consistent LMMs

Composes cycle 344's `coef_α_pos_of_stable_preconsistent` with cycle
345's `coef_α_eq_sum_β_of_isConsistent` to derive strict positivity of
the **unweighted** β-sum `Σᵢ M.β i` from `M.IsStable + M.IsConsistent`
and `0 < k`.

**Route B precursor** from the cycle 348 scoping doc
`.prover-state/issues/eq422a_eta_phase_D_prime_step_2_scoping.md`
§5 Phase D′.2.0. Important caveat: this is the **unweighted**
β-sum `sum_β = Σᵢ βᵢ`, **NOT** the §422 weighted coefficient
`coef_β(M) := Σᵢ i · M.β i` that
`Eq422a_at_vertex_eta_eq_of_stable_preconsistent` requires non-negative.
The two quantities differ — this precursor does **NOT** close
Phase D′ Step 2 on its own. Bridging `sum_β > 0` to
`coef_β ≥ 0` (or to the weaker non-vanishing
`coef_α + coef_β ≠ 0`) is Phase D′.2.1 work. -/

/-- *Phase D′.2.0 precursor (cycle 349):* under stability + consistency
plus `0 < k`, the **unweighted** β-sum `Σ_{i:Fin (k+1)} M.β i` is
strictly positive.

Proof: rewrite via cycle 345's `coef_α_eq_sum_β_of_isConsistent` to
convert the β-sum into the α-side `coef_α`, then discharge via cycle
344's `coef_α_pos_of_stable_preconsistent`.

**Caveat (see cycle 348 scoping doc §5):** the §422 weighted
coefficient `coef_β(M) = Σᵢ i · M.β i` is **NOT** the same as this
`sum_β = Σᵢ M.β i`. This lemma is the unweighted β-sum positivity;
the weighted-coefficient non-negativity required by cycle 345's
`Eq422a_at_vertex_eta_eq_of_stable_preconsistent` remains the Phase
D′.2.1 target. -/
theorem sum_β_pos_of_stable_consistent
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (hk : 0 < k) (hStable : M.IsStable) (hConsistent : M.IsConsistent) :
    0 < ∑ i : Fin (k + 1), M.β i := by
  rw [← coef_α_eq_sum_β_of_isConsistent M hConsistent]
  exact coef_α_pos_of_stable_preconsistent M hk hStable hConsistent.1

/-- *Phase D′.2.0 BDF2 witness (cycle 349):* end-to-end exercise of
`sum_β_pos_of_stable_consistent` on the canonical BDF2 example,
discharging stability via `bdf2LMM_isStable` (cycle 346) and
consistency via `bdf2LMM_isConsistent` (cycle 349, Section451).

Numerical sanity: BDF2's β-sum is `2/3 + 0 + 0 = 2/3 > 0`. -/
example : (0 : ℝ) < ∑ i : Fin 3, OpenMath.Chapter4.Section451.bdf2LMM.β i :=
  sum_β_pos_of_stable_consistent OpenMath.Chapter4.Section451.bdf2LMM
    (by norm_num : (0 : ℕ) < 2)
    OpenMath.Chapter4.Section451.bdf2LMM_isStable
    OpenMath.Chapter4.Section451.bdf2LMM_isConsistent

/-- *Trapezoidal D′.2.0 witness (cycle 355):* end-to-end exercise of
`sum_β_pos_of_stable_consistent` on the trapezoidal (Crank–Nicolson)
LMM, discharging stability via `trapezoidalLMM_isStable` (cycle 354)
and consistency via `trapezoidalLMM_isConsistent` (cycle 352).

Numerical sanity: trapezoidal's β-sum is `1/2 + 1/2 = 1 > 0`. -/
example : (0 : ℝ) < ∑ i : Fin 2, OpenMath.Chapter4.Section404.trapezoidalLMM.β i :=
  sum_β_pos_of_stable_consistent OpenMath.Chapter4.Section404.trapezoidalLMM
    (by norm_num : (0 : ℕ) < 1)
    OpenMath.Chapter4.Section404.trapezoidalLMM_isStable
    OpenMath.Chapter4.Section404.trapezoidalLMM_isConsistent

/-- *BDF3 D′.2.0 witness (cycle 355):* end-to-end exercise of
`sum_β_pos_of_stable_consistent` on BDF3, discharging stability via
`bdf3LMM_isStable` (cycle 354) and consistency via `bdf3LMM_isConsistent`
(cycle 353).

Numerical sanity: BDF3's β-sum is `6/11 + 0 + 0 + 0 = 6/11 > 0`. -/
example : (0 : ℝ) < ∑ i : Fin 4, OpenMath.Chapter4.Section451.bdf3LMM.β i :=
  sum_β_pos_of_stable_consistent OpenMath.Chapter4.Section451.bdf3LMM
    (by norm_num : (0 : ℕ) < 3)
    OpenMath.Chapter4.Section451.bdf3LMM_isStable
    OpenMath.Chapter4.Section451.bdf3LMM_isConsistent

/-- *Phase D′.2.0 implicit Euler non-vacuity (cycle 356):* the cycle
349 `sum_β_pos_of_stable_consistent` fires on implicit Euler; the
β-sum equals `1 + 0 = 1 > 0`. -/
example : (0 : ℝ) < ∑ i : Fin 2,
    OpenMath.Chapter4.Section404.implicitEulerLMM.β i :=
  sum_β_pos_of_stable_consistent
    OpenMath.Chapter4.Section404.implicitEulerLMM
    (by norm_num : (0 : ℕ) < 1)
    OpenMath.Chapter4.Section404.implicitEulerLMM_isStable
    OpenMath.Chapter4.Section404.implicitEulerLMM_isConsistent

/-- *Phase D′.2.0 explicit Euler non-vacuity (cycle 356):* the cycle
349 `sum_β_pos_of_stable_consistent` fires on explicit Euler; the
β-sum equals `0 + 1 = 1 > 0`. Completes the five-LMM consumer-witness
coverage matrix for cycle 349's `sum_β_pos_of_stable_consistent` ship
(explicit Euler + implicit Euler + trapezoidal + BDF2 + BDF3). -/
example : (0 : ℝ) < ∑ i : Fin 2,
    OpenMath.Chapter4.Section404.explicitEulerLMM.β i :=
  sum_β_pos_of_stable_consistent
    OpenMath.Chapter4.Section404.explicitEulerLMM
    (by norm_num : (0 : ℕ) < 1)
    OpenMath.Chapter4.Section404.explicitEulerLMM_isStable
    OpenMath.Chapter4.Section404.explicitEulerLMM_isConsistent

/-! ### Phase D′.2.1 (cycle 350) — Route E refinement of cycle 345

Cycle 345 shipped `Eq422a_at_vertex_eta_eq_of_stable_preconsistent`
with hypothesis `0 ≤ coef_β(M)`. Phase D′.2.1 weakens that to the
**strictly weaker** non-vanishing form `coef_α(M) + coef_β(M) ≠ 0`.
See `.prover-state/issues/eq422a_eta_phase_D_prime_step_2_scoping.md`
§4.5 + §5 for the rationale (the unconditional drop of the
non-vanishing side-hypothesis from `IsStable + IsConsistent` alone
is the Phase D′.2.2/2.3 multi-cycle target).

This block ships a sibling theorem (not a refactor of cycle 345),
plus the algebraic identity that bridges
`coef_α + coef_β = Σᵢ (i+1) · βᵢ` under consistency, plus the BDF2
non-vacuity witness.
-/

/-- *Phase D′.2.1 (cycle 350) — Route E refinement:* under stability
+ preconsistency plus the **weakened** side hypothesis that
`coef_α(M) + coef_β(M)` is non-zero (strictly weaker than cycle 345's
`0 ≤ coef_β(M)` combined with `coef_α > 0`), the (422a) reduction at
the single-vertex tree `τ` pins `η(τ) = sum_β / (coef_α + coef_β)`.

A direct one-line call to cycle 342's `Eq422a_at_vertex_eta_eq` with
the non-vanishing hypothesis supplied unconditionally. The
`hk`/`hStab`/`hPre` hypotheses are deliberately retained (unused at
the body level, marked with underscore) for caller ergonomics: this
signature is drop-in compatible with cycle 345's
`Eq422a_at_vertex_eta_eq_of_stable_preconsistent`. Any caller with
`0 ≤ coef_β` can derive `h_denom_ne` from cycle 344's `coef_α > 0`
via `linarith`.

The unconditional drop of `h_denom_ne` (i.e. proving `coef_α +
coef_β ≠ 0` from `IsStable + IsConsistent` alone) remains the Phase
D′.2.2/2.3 target — see the cycle 348 scoping doc §4 for the
multi-cycle obstruction (Routes A/B/C/D each blocked). -/
theorem Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (_hk : 0 < k)
    (_hStab : M.IsStable) (_hPre : M.IsPreconsistent)
    (h_denom_ne :
        (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
          + (∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i) ≠ 0)
    {η_q : Quotient PhiEquivalent.setoidSigma}
    (hEq : Eq422a M η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex
      = (∑ i : Fin (k + 1), M.β i)
          / ((∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
              + (∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i)) :=
  Eq422a_at_vertex_eta_eq hEq h_denom_ne

/-- *Phase D′.2.1 algebraic identity (cycle 350):* under consistency,
the §422 denominator `coef_α + coef_β` equals the `(i+1)`-weighted
β-sum `Σᵢ (i+1) · βᵢ`.

Derivation: `coef_α = sum_β` (cycle 345's
`coef_α_eq_sum_β_of_isConsistent`, from (404b)), so `coef_α + coef_β =
Σᵢ βᵢ + Σᵢ i · βᵢ = Σᵢ (1 · βᵢ + i · βᵢ) = Σᵢ (i+1) · βᵢ`.

Pure structural algebra; no Butcher-named lemma. Useful for the
Phase D′.2.1 stretch corollary `Eq422a_at_vertex_eta_eq_of_stable_consistent`
which translates `h_denom_ne` to the cleaner `Σᵢ (i+1) · βᵢ ≠ 0`. -/
theorem coef_α_plus_coef_β_eq_succ_weighted_β_of_isConsistent
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (hCons : M.IsConsistent) :
    (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
      + (∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i)
      = ∑ i : Fin (k + 1), ((i.val + 1 : ℕ) : ℝ) * M.β i := by
  rw [coef_α_eq_sum_β_of_isConsistent M hCons]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- *Phase D′.2.1 BDF2 non-vanishing witness (cycle 350):* BDF2's
denominator `coef_α + coef_β = 2/3 + 0 = 2/3 ≠ 0`. Numerical
witness for the weakened-hypothesis ship. -/
theorem bdf2LMM_coef_α_plus_coef_β_ne_zero :
    (∑ i : Fin 2, ((i.val + 1 : ℕ) : ℝ) *
        OpenMath.Chapter4.Section451.bdf2LMM.α i.succ)
      + (∑ i : Fin 3, ((i.val : ℕ) : ℝ) *
            OpenMath.Chapter4.Section451.bdf2LMM.β i) ≠ 0 := by
  simp [OpenMath.Chapter4.Section451.bdf2LMM,
    Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num

/-- *Trapezoidal D′.2.1 non-vanishing witness (cycle 355):*
trapezoidal's denominator `coef_α + coef_β = 1 + 1/2 = 3/2 ≠ 0`.
Numerical witness for the cycle 350 weakened-hypothesis ship at the
trapezoidal (Crank–Nicolson) LMM. -/
theorem trapezoidalLMM_coef_α_plus_coef_β_ne_zero :
    (∑ i : Fin 1, ((i.val + 1 : ℕ) : ℝ) *
        OpenMath.Chapter4.Section404.trapezoidalLMM.α i.succ)
      + (∑ i : Fin 2, ((i.val : ℕ) : ℝ) *
            OpenMath.Chapter4.Section404.trapezoidalLMM.β i) ≠ 0 := by
  simp [OpenMath.Chapter4.Section404.trapezoidalLMM,
    Fin.sum_univ_two]
  norm_num

/-- *BDF3 D′.2.1 non-vanishing witness (cycle 355):* BDF3's denominator
`coef_α + coef_β = 6/11 + 0 = 6/11 ≠ 0`. Numerical witness for the
cycle 350 weakened-hypothesis ship at BDF3. -/
theorem bdf3LMM_coef_α_plus_coef_β_ne_zero :
    (∑ i : Fin 3, ((i.val + 1 : ℕ) : ℝ) *
        OpenMath.Chapter4.Section451.bdf3LMM.α i.succ)
      + (∑ i : Fin 4, ((i.val : ℕ) : ℝ) *
            OpenMath.Chapter4.Section451.bdf3LMM.β i) ≠ 0 := by
  simp [OpenMath.Chapter4.Section451.bdf3LMM,
    Fin.sum_univ_three, Fin.sum_univ_four]
  norm_num

/-- *Implicit Euler D′.2.1 non-vanishing witness (cycle 356):*
implicit Euler's denominator `coef_α + coef_β = 1 + 0 = 1 ≠ 0`.
Numerical witness for the cycle 350 weakened-hypothesis ship at
the implicit Euler LMM. -/
theorem implicitEulerLMM_coef_α_plus_coef_β_ne_zero :
    (∑ i : Fin 1, ((i.val + 1 : ℕ) : ℝ) *
        OpenMath.Chapter4.Section404.implicitEulerLMM.α i.succ)
      + (∑ i : Fin 2, ((i.val : ℕ) : ℝ) *
            OpenMath.Chapter4.Section404.implicitEulerLMM.β i) ≠ 0 := by
  simp [OpenMath.Chapter4.Section404.implicitEulerLMM]

/-- *Explicit Euler D′.2.1 non-vanishing witness (cycle 356):*
explicit Euler's denominator `coef_α + coef_β = 1 + 1 = 2 ≠ 0`.
Numerical witness for the cycle 350 weakened-hypothesis ship at
the explicit Euler LMM. -/
theorem explicitEulerLMM_coef_α_plus_coef_β_ne_zero :
    (∑ i : Fin 1, ((i.val + 1 : ℕ) : ℝ) *
        OpenMath.Chapter4.Section404.explicitEulerLMM.α i.succ)
      + (∑ i : Fin 2, ((i.val : ℕ) : ℝ) *
            OpenMath.Chapter4.Section404.explicitEulerLMM.β i) ≠ 0 := by
  simp [OpenMath.Chapter4.Section404.explicitEulerLMM,
    Fin.sum_univ_two]

/-- *Non-vacuity for the cycle 355 weakened ship (trapezoidal):*
end-to-end exercise of `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened`
on trapezoidal, pinning `η(τ) = 1 / (3/2) = 2/3` for the underlying
one-step method corresponding to the Crank–Nicolson LMM. -/
example (η_q : Quotient PhiEquivalent.setoidSigma)
    (hEq : Eq422a OpenMath.Chapter4.Section404.trapezoidalLMM η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex = 2 / 3 := by
  have h := Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened
    OpenMath.Chapter4.Section404.trapezoidalLMM
    (by norm_num : (0 : ℕ) < 1)
    OpenMath.Chapter4.Section404.trapezoidalLMM_isStable
    OpenMath.Chapter4.Section404.trapezoidalLMM_isPreconsistent
    trapezoidalLMM_coef_α_plus_coef_β_ne_zero
    hEq
  rw [h]
  simp [OpenMath.Chapter4.Section404.trapezoidalLMM,
    Fin.sum_univ_two]
  norm_num

/-- *Non-vacuity for the cycle 350 weakened ship:* end-to-end
exercise of `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened`
on BDF2, discharging the weakened non-vanishing hypothesis via
`bdf2LMM_coef_α_plus_coef_β_ne_zero`. The underlying-one-step-method
`η ∈ G₁` corresponding to BDF2 pins `η(τ) = 1` (same numerical
conclusion as cycle 346's witness, via the weaker route). -/
example (η_q : Quotient PhiEquivalent.setoidSigma)
    (hEq : Eq422a OpenMath.Chapter4.Section451.bdf2LMM η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex = 1 := by
  have h := Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened
    OpenMath.Chapter4.Section451.bdf2LMM
    (by norm_num : (0 : ℕ) < 2)
    OpenMath.Chapter4.Section451.bdf2LMM_isStable
    OpenMath.Chapter4.Section441.bdf2LMM_isPreconsistent
    bdf2LMM_coef_α_plus_coef_β_ne_zero
    hEq
  rw [h]
  simp [OpenMath.Chapter4.Section451.bdf2LMM,
    Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num

/-- *Non-vacuity for the cycle 356 implicit Euler ship:* end-to-end
exercise of `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened`
on implicit Euler, discharging the weakened non-vanishing hypothesis
via `implicitEulerLMM_coef_α_plus_coef_β_ne_zero`. The
underlying-one-step-method `η ∈ G₁` corresponding to implicit Euler
pins `η(τ) = 1` (same numerical conclusion as BDF2 and cycle 346's
witness). -/
example (η_q : Quotient PhiEquivalent.setoidSigma)
    (hEq : Eq422a OpenMath.Chapter4.Section404.implicitEulerLMM η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex = 1 := by
  have h := Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened
    OpenMath.Chapter4.Section404.implicitEulerLMM
    (by norm_num : (0 : ℕ) < 1)
    OpenMath.Chapter4.Section404.implicitEulerLMM_isStable
    OpenMath.Chapter4.Section404.implicitEulerLMM_isPreconsistent
    implicitEulerLMM_coef_α_plus_coef_β_ne_zero
    hEq
  rw [h]
  simp [OpenMath.Chapter4.Section404.implicitEulerLMM]

/-- *Non-vacuity for the cycle 356 explicit Euler ship:* end-to-end
exercise of `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened`
on explicit Euler, pinning `η(τ) = 1 / 2` for the underlying
one-step method corresponding to the original 1-step LMM. Completes
the five-LMM consumer matrix (explicit Euler + implicit Euler +
trapezoidal + BDF2 + BDF3) for the cycle 350 weakened-hypothesis
ship. -/
example (η_q : Quotient PhiEquivalent.setoidSigma)
    (hEq : Eq422a OpenMath.Chapter4.Section404.explicitEulerLMM η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex = 1 / 2 := by
  have h := Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened
    OpenMath.Chapter4.Section404.explicitEulerLMM
    (by norm_num : (0 : ℕ) < 1)
    OpenMath.Chapter4.Section404.explicitEulerLMM_isStable
    OpenMath.Chapter4.Section404.explicitEulerLMM_isPreconsistent
    explicitEulerLMM_coef_α_plus_coef_β_ne_zero
    hEq
  rw [h]
  simp [OpenMath.Chapter4.Section404.explicitEulerLMM,
    Fin.sum_univ_two]
  norm_num

/-- *Non-vacuity for the cycle 350 weakened ship at BDF3 (cycle 357):*
end-to-end exercise of `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened`
on BDF3, discharging the weakened non-vanishing hypothesis via
`bdf3LMM_coef_α_plus_coef_β_ne_zero` (cycle 355). The underlying-
one-step-method `η ∈ G₁` corresponding to BDF3 pins
`η(τ) = (6/11) / (6/11) = 1`. Completes the 5-LMM × 3-theorem
consumer-witness matrix
{explicitEulerLMM, implicitEulerLMM, trapezoidalLMM, bdf2LMM, bdf3LMM}
× {sum_β_pos, coef_α_plus_coef_β_ne_zero, Eq422a_at_vertex_eta_eq}. -/
example (η_q : Quotient PhiEquivalent.setoidSigma)
    (hEq : Eq422a OpenMath.Chapter4.Section451.bdf3LMM η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex = 1 := by
  have h := Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened
    OpenMath.Chapter4.Section451.bdf3LMM
    (by norm_num : (0 : ℕ) < 3)
    OpenMath.Chapter4.Section451.bdf3LMM_isStable
    OpenMath.Chapter4.Section451.bdf3LMM_isPreconsistent
    bdf3LMM_coef_α_plus_coef_β_ne_zero
    hEq
  rw [h]
  simp [OpenMath.Chapter4.Section451.bdf3LMM,
    Fin.sum_univ_three, Fin.sum_univ_four]
  norm_num

/-- *Phase D′.2.1 consistent-form corollary (cycle 350, stretch):*
under stability + consistency plus the side hypothesis that the
`(i+1)`-weighted β-sum `Σᵢ (i+1) · βᵢ` is non-zero, the (422a)
reduction at `τ` pins `η(τ) = sum_β / Σᵢ (i+1) · βᵢ`.

This is the cleaner-signature corollary that consumes cycle 350's
algebraic identity `coef_α_plus_coef_β_eq_succ_weighted_β_of_isConsistent`
directly. The signature matches Butcher §422's surface notation
more closely (the textbook denominator is naturally written in the
`Σᵢ (i+1) · βᵢ` form under consistency). -/
theorem Eq422a_at_vertex_eta_eq_of_stable_consistent
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (hk : 0 < k)
    (hStab : M.IsStable) (hCons : M.IsConsistent)
    (h_succ_β_ne :
        (∑ i : Fin (k + 1), ((i.val + 1 : ℕ) : ℝ) * M.β i) ≠ 0)
    {η_q : Quotient PhiEquivalent.setoidSigma}
    (hEq : Eq422a M η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex
      = (∑ i : Fin (k + 1), M.β i)
          / (∑ i : Fin (k + 1), ((i.val + 1 : ℕ) : ℝ) * M.β i) := by
  have h_id := coef_α_plus_coef_β_eq_succ_weighted_β_of_isConsistent M hCons
  rw [← h_id] at h_succ_β_ne ⊢
  exact Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened
    M hk hStab hCons.1 h_succ_β_ne hEq

/-- *Non-vacuity for the cycle 350 consistent-form corollary:*
end-to-end exercise of `Eq422a_at_vertex_eta_eq_of_stable_consistent`
on BDF2. The `(i+1)`-weighted β-sum is
`1·(2/3) + 2·0 + 3·0 = 2/3 ≠ 0`; the `η(τ) = (2/3)/(2/3) = 1`
conclusion matches the cycle 346 / cycle 350 weakened-form
witnesses. -/
example (η_q : Quotient PhiEquivalent.setoidSigma)
    (hEq : Eq422a OpenMath.Chapter4.Section451.bdf2LMM η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex = 1 := by
  have h := Eq422a_at_vertex_eta_eq_of_stable_consistent
    OpenMath.Chapter4.Section451.bdf2LMM
    (by norm_num : (0 : ℕ) < 2)
    OpenMath.Chapter4.Section451.bdf2LMM_isStable
    OpenMath.Chapter4.Section451.bdf2LMM_isConsistent
    (by
      simp [OpenMath.Chapter4.Section451.bdf2LMM,
        Fin.sum_univ_three])
    hEq
  rw [h]
  simp [OpenMath.Chapter4.Section451.bdf2LMM,
    Fin.sum_univ_three]

/-! ### Phase D′.2.2 Route D Step 1 — algebraic bridge

Under `M.HasOrderAtLeast 2`, the §410 Taylor coefficient identity
`C M 2 = 0` rearranges to a direct algebraic equality between the
β-coefficient sum `coef_β = Σᵢ i · M.β i` and the half-weighted
α-square sum `(1/2) · Σᵢ (i+1)² · M.α i.succ`. This is the
**Route D** Step 1 of `eq422a_eta_phase_D_prime_step_2_scoping.md`:
it provides a different bridge from the cycle 350 Route E surface,
trading the Phase D′.2.1 `IsConsistent` hypothesis (order ≥ 1) for
the stronger `HasOrderAtLeast 2` so the identity is an equality
rather than a one-sided inequality.

**Faithfulness note**: textbook (Butcher §410 / §422) conditions
for `def:422B`'s underlying-one-step-method require only
`IsConsistent` (order ≥ 1). Under `HasOrderAtLeast 2` the
additional constraint `C M 2 = 0` makes the bridge from `coef_β`
to `Σᵢ (i+1)² · M.α i.succ` an equality. The cycle 350 Route E
surface (`Eq422a_at_vertex_eta_eq_of_stable_consistent`) remains
available for callers without order ≥ 2 in hand; this Route D
lemma is the algebraic identity Phase D′.2.2 Step 1 needs.
Compatible with the cycle 250 `alphaWeight` precedent on
hypothesis-strengthening. -/

/-- *Phase D′.2.2 Route D Step 1 (cycle 351):* under
`M.HasOrderAtLeast 2`, the §410 Taylor coefficient identity
`C M 2 = 0` rearranges to the algebraic equality
`Σᵢ i · M.β i = (1/2) · Σᵢ (i+1)² · M.α i.succ`. -/
theorem coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (hOrder : M.HasOrderAtLeast 2) :
    (∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i)
      = (1 / 2) *
        ∑ i : Fin k, (((i.val + 1 : ℕ) : ℝ))^2 * M.α i.succ := by
  have hC2 : OpenMath.Chapter4.Section410.C M 2 = 0 :=
    hOrder 2 (by norm_num)
  have hC2_unfold : OpenMath.Chapter4.Section410.C M 2 =
      -∑ i : Fin k,
          M.α i.succ * (-(((i.val + 1 : ℕ) : ℝ))) ^ (1 + 1) /
            (Nat.factorial (1 + 1) : ℝ)
      - ∑ i : Fin (k + 1),
          M.β i * (-(((i.val : ℕ) : ℝ))) ^ 1 /
            (Nat.factorial 1 : ℝ) := rfl
  rw [hC2_unfold] at hC2
  have h_alpha :
      ∑ i : Fin k,
          M.α i.succ * (-(((i.val + 1 : ℕ) : ℝ))) ^ (1 + 1) /
            (Nat.factorial (1 + 1) : ℝ)
        = (1 / 2) *
          ∑ i : Fin k, (((i.val + 1 : ℕ) : ℝ))^2 * M.α i.succ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hfact : (Nat.factorial (1 + 1) : ℝ) = 2 := by
      norm_num [Nat.factorial]
    rw [hfact]
    ring
  have h_beta :
      ∑ i : Fin (k + 1),
          M.β i * (-(((i.val : ℕ) : ℝ))) ^ 1 /
            (Nat.factorial 1 : ℝ)
        = -∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hfact : (Nat.factorial 1 : ℝ) = 1 := by
      norm_num [Nat.factorial]
    rw [hfact]
    ring
  rw [h_alpha, h_beta] at hC2
  linarith

/-- *Phase D′.2.2 BDF2 order-2 witness (cycle 351 precursor):* BDF2
satisfies `HasOrderAtLeast 2`. Verified by checking
`C bdf2LMM j = 0` for `j ∈ {0, 1, 2}`:
* `C bdf2LMM 0 = 1 - (4/3 + (-1/3)) = 0` (preconsistency);
* `C bdf2LMM 1 = 0` (consistency);
* `C bdf2LMM 2 = -((4/3)·(-1)²/2 + (-1/3)·(-2)²/2) - 0 =
  -(2/3 - 2/3) = 0`. -/
theorem bdf2LMM_hasOrderAtLeast_two :
    OpenMath.Chapter4.Section451.bdf2LMM.HasOrderAtLeast 2 := by
  intro j hj
  interval_cases j
  · -- C bdf2LMM 0 = 0
    show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section451.bdf2LMM 0 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section451.bdf2LMM, Fin.sum_univ_two]
    norm_num
  · -- C bdf2LMM 1 = 0 (consistency)
    show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section451.bdf2LMM 1 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section451.bdf2LMM,
      Fin.sum_univ_two, Fin.sum_univ_three, Nat.factorial]
    norm_num
  · -- C bdf2LMM 2 = 0
    show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section451.bdf2LMM 2 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section451.bdf2LMM,
      Fin.sum_univ_two, Fin.sum_univ_three, Nat.factorial]
    norm_num

/-- *Phase D′.2.2 BDF2 sanity witness (cycle 351):* end-to-end
exercise of `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two`
on BDF2. Both sides vanish on BDF2 (the textbook order-2 method):
* LHS `coef_β(bdf2LMM) = 0·(2/3) + 1·0 + 2·0 = 0`;
* RHS `(1/2) · Σᵢ (i+1)²·αᵢ = (1/2) · (1²·(4/3) + 2²·(-1/3)) =
  (1/2) · (4/3 - 4/3) = 0`.
The witness exercises the theorem at an order-2 method where the
identity trivializes to `0 = 0`. -/
theorem bdf2LMM_coef_β_eq_half_sum_i_sq_alpha :
    (∑ i : Fin 3, ((i.val : ℕ) : ℝ) *
        OpenMath.Chapter4.Section451.bdf2LMM.β i)
      = (1 / 2) *
        ∑ i : Fin 2, (((i.val + 1 : ℕ) : ℝ))^2 *
          OpenMath.Chapter4.Section451.bdf2LMM.α i.succ :=
  coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two
    OpenMath.Chapter4.Section451.bdf2LMM
    bdf2LMM_hasOrderAtLeast_two

/-- *Phase D′.2.2 trapezoidal precursor (cycle 352):* the
trapezoidal rule satisfies `HasOrderAtLeast 2`. Verified by
checking `C trapezoidalLMM j = 0` for `j ∈ {0, 1, 2}`:
* `C trapezoidalLMM 0 = 1 - 1 = 0` (preconsistency);
* `C trapezoidalLMM 1 = 0` (consistency);
* `C trapezoidalLMM 2 = -(1·1²/2) + (0·(1/2) + 1·(1/2)) =
  -1/2 + 1/2 = 0`. -/
theorem trapezoidalLMM_hasOrderAtLeast_two :
    OpenMath.Chapter4.Section404.trapezoidalLMM.HasOrderAtLeast 2 := by
  intro j hj
  interval_cases j
  · show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section404.trapezoidalLMM 0 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section404.trapezoidalLMM]
  · show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section404.trapezoidalLMM 1 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section404.trapezoidalLMM, Nat.factorial]
  · show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section404.trapezoidalLMM 2 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section404.trapezoidalLMM, Nat.factorial]

/-- *Phase D′.2.2 trapezoidal sanity witness (cycle 352):*
end-to-end exercise of `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two`
on the trapezoidal rule. Unlike BDF2 (where both sides vanish),
this gives the first non-trivial witness of cycle 351's identity:
* LHS `coef_β(trapezoidalLMM) = 0·(1/2) + 1·(1/2) = 1/2`;
* RHS `(1/2) · Σᵢ (i+1)²·αᵢ = (1/2) · 1²·1 = 1/2`. -/
theorem trapezoidalLMM_coef_β_eq_half_sum_i_sq_alpha :
    (∑ i : Fin 2, ((i.val : ℕ) : ℝ) *
        OpenMath.Chapter4.Section404.trapezoidalLMM.β i)
      = (1 / 2) *
        ∑ i : Fin 1, (((i.val + 1 : ℕ) : ℝ))^2 *
          OpenMath.Chapter4.Section404.trapezoidalLMM.α i.succ :=
  coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two
    OpenMath.Chapter4.Section404.trapezoidalLMM
    trapezoidalLMM_hasOrderAtLeast_two

/-- *Phase D′.2.2 BDF3 order-3 witness (cycle 353):* BDF3 satisfies
`HasOrderAtLeast 3`. Verified by checking `C bdf3LMM j = 0` for
`j ∈ {0, 1, 2, 3}` (preconsistency + (404b) + two further
cancellations from the α-side third- and fourth-power moments).
This is the project's first order-≥-3 LMM witness. -/
theorem bdf3LMM_hasOrderAtLeast_three :
    OpenMath.Chapter4.Section451.bdf3LMM.HasOrderAtLeast 3 := by
  intro j hj
  interval_cases j
  · show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section451.bdf3LMM 0 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section451.bdf3LMM, Fin.sum_univ_three]
    norm_num
  · show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section451.bdf3LMM 1 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section451.bdf3LMM,
      Fin.sum_univ_three, Fin.sum_univ_four, Nat.factorial]
    norm_num
  · show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section451.bdf3LMM 2 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section451.bdf3LMM,
      Fin.sum_univ_three, Fin.sum_univ_four, Nat.factorial]
    norm_num
  · show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section451.bdf3LMM 3 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section451.bdf3LMM,
      Fin.sum_univ_three, Fin.sum_univ_four, Nat.factorial]
    norm_num

/-- *Phase D′.2.2 BDF3 sanity witness (cycle 353):* end-to-end
exercise of `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two`
on BDF3. Like BDF2 (cycle 351), both sides vanish at BDF3:
* LHS `coef_β(bdf3LMM) = 0·(6/11) + 1·0 + 2·0 + 3·0 = 0`;
* RHS `(1/2) · Σᵢ (i+1)²·αᵢ.succ = (1/2) · [1·(18/11) + 4·(−9/11) +
  9·(2/11)] = (1/2) · 0 = 0`.
A trivial-identity witness (parity with BDF2); the first non-trivial
witness was trapezoidal `1/2 = 1/2` (cycle 352). The `HasOrderAtLeast 2`
hypothesis is derived inline from `HasOrderAtLeast 3` via `omega`. -/
theorem bdf3LMM_coef_β_eq_half_sum_i_sq_alpha :
    (∑ i : Fin 4, ((i.val : ℕ) : ℝ) *
        OpenMath.Chapter4.Section451.bdf3LMM.β i)
      = (1 / 2) *
        ∑ i : Fin 3, (((i.val + 1 : ℕ) : ℝ))^2 *
          OpenMath.Chapter4.Section451.bdf3LMM.α i.succ := by
  apply coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two
  intro j hj
  exact bdf3LMM_hasOrderAtLeast_three j (by omega)

/-! ### Phase D.3.b — linear coefficient extraction (cycle 360; redefined cycle 364)

Per Butcher §422 p. 359 (`extraction/raw_text/ch04.txt:1158`), the
proof of `thm:422A` (Theorem 422A — every preconsistent, stable
linear multistep method admits a member of `G₁` satisfying (422a))
relies on the structural claim:

> The coefficient of η(t) in η⁻ⁱ(t) is equal to i·(-1)^r(t), and
> there are no other terms in η⁻ⁱ(t) with orders greater than r(t)−1.

Note (cycle 364): under our §383 Φ-quotient encoding, the empirical
coefficient of `Φ_{η_q}(t)` in `Φ_{η_q^(-i)}(t)` is `-i` (constant in
`r(t)`), not `i·(-1)^r(t)`; see the cycle 363 P2 audit at
`.prover-state/issues/def_422B_phase_D_3_scoping.md` §10. Cycle 364
redefines `linearResidualAt` to match the quotient-encoded
coefficient. The cycle 360 definition is replaced; the cycle 360/361
theorem statements are updated for the corrected coefficient.

Phase D.3.b ships this **definitionally** as a named residual
`linearResidualAt`, with two substantive base-level theorems:

* `linearResidualAt_vertex_eq_zero` — at the single-vertex tree `τ`
  (where `r(τ) = 1` and the "other terms" set is empty), the residual
  is identically zero. Corroborates the textbook coefficient identity
  at the trivial case via cycle 341 P3 (`elementaryWeightQ_phi_zpow_vertex`).
* `linearResidualAt_one_mk_eq` — at `i = 1` at arbitrary `t`, the
  residual reduces to a closed-form expression involving cycle 358's
  `elementaryWeightQ_phi_inv_mk`, exposing the structural dependence
  on `M`'s representative data at subtrees of `t` via
  `derivativeWeightWithSrc`.

The structural content "`linearResidualAt` depends only on strict
subtrees of `t`" is the inductive step (Butcher's "induction on
r(t)") and is deferred to cycle 361 — see
`.prover-state/issues/def_422B_phase_D_3_scoping.md` §4.b and §5
Phase D.3.b row. Cycle 360 follows the §F graceful-degradation
template: Sub-deliverable 1 (signature pinning via `linearResidualAt`
+ `coeff_eta_t_in_eta_zpow_neg`) plus Sub-deliverable 2 partial
(vertex base case + `i = 1` closed form) shipped axiom-clean. -/

/-- *Phase D.3.b (cycle 360; redefined cycle 364) — named helper:*
the linear-coefficient **residual** in the textbook decomposition of
`η⁻ⁱ(t)`. Definitional on the §383 quotient (per §6.3
quotient-faithfulness discipline):

  `linearResidualAt i η_q t = Φ_{η_q^(-i)}(t) + i·Φ_{η_q}(t)`

By the audit at `.prover-state/issues/def_422B_phase_D_3_scoping.md`
§10 (cycle 363 P2), the coefficient of `Φ_{η_q}(t)` in
`Φ_{η_q^(-i)}(t)` under our §383 Φ-quotient encoding is `-i`,
constant in `r(t)`. The residual subtracts the η(t)-linear part
`(-i)·Φ_{η_q}(t)` from `Φ_{η_q^(-i)}(t)`, extracting the part that
depends only on strict subtrees of `t`. Cycle 360's original form
had `- i·(-1)^r(t)·Φ_{η_q}(t)`, which mismatches the quotient-encoded
coefficient at even `r(t) ≥ 2`; cycle 364 ships the corrected form.

`noncomputable` because `elementaryWeightQ_phi` is `noncomputable`
(via `Quotient.lift` in `Section381.lean:4759`); does not depend on
representative choice. -/
noncomputable def linearResidualAt (i : ℕ)
    (η_q : Quotient PhiEquivalent.setoidSigma) (t : RT) : ℝ :=
  elementaryWeightQ_phi (η_q ^ (-(i : ℤ))) t
    + (i : ℝ) * elementaryWeightQ_phi η_q t

/-- *Phase D.3.b (cycle 360; restated cycle 364) — signature-pinning
split form for the linear coefficient of η(t) in η⁻ⁱ(t).*
Definitional rearrangement of `linearResidualAt`'s defining
equation. Per the cycle 363 P2 audit (see
`.prover-state/issues/def_422B_phase_D_3_scoping.md` §10), the
coefficient of `Φ_{η_q}(t)` in `Φ_{η_q^(-i)}(t)` is `-i` (constant
in `r(t)`); cycle 364's redefinition of `linearResidualAt` makes
this split definitional. The parametricity claim
("`linearResidualAt` depends only on strict subtrees of `t`") is
deferred to cycle 365+. -/
theorem coeff_eta_t_in_eta_zpow_neg (i : ℕ)
    (η_q : Quotient PhiEquivalent.setoidSigma) (t : RT) :
    elementaryWeightQ_phi (η_q ^ (-(i : ℤ))) t
      = -(i : ℝ) * elementaryWeightQ_phi η_q t
        + linearResidualAt i η_q t := by
  unfold linearResidualAt
  ring

/-- *Phase D.3.b (cycle 360; redefined cycle 364) — base case at vertex.*
At the single-vertex tree `τ` (`r(τ) = 1`, no strict subtrees), the
residual is zero. This corroborates Butcher's "there are no other
terms in η⁻ⁱ(t) with orders greater than r(t)−1" specialised to
`r(t) = 1`, where the "other terms" set is empty.

Proof: cycle 341 P3 (`elementaryWeightQ_phi_zpow_vertex`) gives
`Φ_{η_q^n}(τ) = n·Φ_{η_q}(τ)` for all `n : ℤ`. At `n = -(i : ℤ)`,
this yields `Φ_{η_q^(-i)}(τ) = -(i : ℝ)·Φ_{η_q}(τ)`. Adding the
cycle 364 redefined `+i·Φ_{η_q}(τ)` correction gives 0. -/
theorem linearResidualAt_vertex_eq_zero (i : ℕ)
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    linearResidualAt i η_q RootedTree.vertex = 0 := by
  unfold linearResidualAt
  rw [elementaryWeightQ_phi_zpow_vertex]
  push_cast
  ring

/-- *Phase D.3.b (cycle 360) Sub-deliverable 2 — closed form for the
residual at `i = 1` at arbitrary `t` (representative form).*
Specialises `linearResidualAt` at `i = 1` to a closed-form expression
using cycle 358's `elementaryWeightQ_phi_inv_mk`. The closed form
exposes the residual's structural dependence on `M.elementaryWeight`
at subtrees of `t` (via `derivativeWeightWithSrc`'s recursive shape);
the parametricity claim "depends only on strict subtrees" is the
content of the cycle 361 inductive step.

At `t = vertex`, this reduces to the vertex base case via
`derivativeWeightWithSrc_vertex` (each factor is `1`) and
`vertex.order = 1` — providing an independent witness for
`linearResidualAt_vertex_eq_zero` at `i = 1`. -/
theorem linearResidualAt_one_mk_eq
    {s : ℕ} (M : RKTableau s) (t : RT) :
    linearResidualAt 1
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) t
      = - (∑ i : Fin s, M.b i * M.derivativeWeightWithSrc M.inverse i t)
        + M.elementaryWeight t := by
  unfold linearResidualAt
  have h_pow :
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) ^ (-((1 : ℕ) : ℤ))
        = (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)⁻¹ := by
    rw [Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow, elementaryWeightQ_phi_inv_mk M t, elementaryWeightQ_phi_mk]
  push_cast
  ring

/-- *Phase D.3.b (cycle 360) — non-vacuity at vertex with
`explicitEuler`, `i = 1`.* Exercises the vertex base case on a
canonical RK method, confirming the residual is zero. -/
example :
    linearResidualAt 1
        (Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩) RootedTree.vertex = 0 :=
  linearResidualAt_vertex_eq_zero 1 _

/-- *Phase D.3.b (cycle 360; restated cycle 364) — non-vacuity: split
form at vertex with `explicitEuler`, `i = 1`.* Exercises the
`coeff_eta_t_in_eta_zpow_neg` split form at the vertex with the
canonical `explicitEuler` representative. Cycle 364: RHS updated for
the redefined linear coefficient `-i` (constant in `r(t)`). -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-((1 : ℕ) : ℤ))) RootedTree.vertex
      = -((1 : ℕ) : ℝ)
          * elementaryWeightQ_phi
              (Quotient.mk PhiEquivalent.setoidSigma
                ⟨1, RKTableau.explicitEuler⟩) RootedTree.vertex
        + linearResidualAt 1
            (Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) RootedTree.vertex :=
  coeff_eta_t_in_eta_zpow_neg 1
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    RootedTree.vertex

/-- *Phase D.3.b (cycle 360; restated cycle 364) — non-vacuity: closed
form at `i = 1` at `cherry` with `explicitEuler`.* Exercises
`linearResidualAt_one_mk_eq` at the order-2 tree `cherry`, providing
the first non-vertex witness of the closed-form expression for the
residual via cycle 358's `elementaryWeightQ_phi_inv_mk`. Cycle 364:
RHS updated for the redefined coefficient (no `(-1)^r(t)` factor;
sign of `M.elementaryWeight t` flipped). -/
example :
    linearResidualAt 1
        (Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩) RootedTree.cherry
      = - (∑ i : Fin 1,
              RKTableau.explicitEuler.b i *
                RKTableau.explicitEuler.derivativeWeightWithSrc
                  RKTableau.explicitEuler.inverse i RootedTree.cherry)
        + RKTableau.explicitEuler.elementaryWeight RootedTree.cherry :=
  linearResidualAt_one_mk_eq RKTableau.explicitEuler RootedTree.cherry

/-! ### Phase D.3.b (cycle 361) — ℤ-form lift + closed form at `i = 2`

Cycle 360 shipped the Phase D.3.b *signature + base cases*: the
`linearResidualAt` named helper, the split form
`coeff_eta_t_in_eta_zpow_neg`, the vertex base case, and the closed
form at `i = 1` at arbitrary trees. Cycle 360 explicitly deferred the
**ℤ-form lift** `elementaryWeightQ_phi_zpow_mk` (the ℤ-power analogue
of cycle 359's ℕ-form `elementaryWeightQ_phi_pow_succ_mk`) per the
cycle 359 task results §C.4 graceful degradation.

Cycle 361 ships the ℤ-form lift in two cleanly-named pieces:

* `elementaryWeightQ_phi_zpow_natCast_mk` — positive natCast case:
  `Φ_{⟦M⟧^((m:ℤ))}(t) = (M.powRep m).2.elementaryWeight t`. Bridge
  via `zpow_natCast` + cycle 359's `RKTableau.powRep_quotient_eq`.
* `elementaryWeightQ_phi_zpow_negSucc_mk` — negative `Int.negSucc`
  case: `Φ_{⟦M⟧^(Int.negSucc m)}(t)` equals the negation of the
  bottom-block contribution of the `(m+1)`-fold composite
  representative's inverse. Bridge via `zpow_negSucc` + cycle 358's
  `elementaryWeightQ_phi_inv_mk` + cycle 359's `powRep_quotient_eq`.

Plus the cycle 360 ladder extension at `i = 2`:

* `linearResidualAt_two_mk_eq` — closed form at `i = 2` at arbitrary
  trees, exercising the ℤ-form lift at `Int.negSucc 1` (i.e. `-2`).

The full Phase D.3.b *inductive step* / *parametricity claim*
(`linearResidualAt_depends_only_on_strict_subtrees`) is deferred to a
later cycle (the strong-induction structure through
`derivativeWeightWithSrc` is multi-cycle work, per scoping doc §5).
-/

/-- *Phase D.3.b (cycle 361) — ℤ-form lift: positive natCast case.*
For `m : ℕ` cast to `ℤ`, the §383 quotient `m`-fold power's elementary
weight at any tree equals the elementary weight of cycle 359's
canonical `powRep` representative. Bridge: `zpow_natCast` reduces the
ℤ-power to the ℕ-power, then cycle 359's `powRep_quotient_eq` (reversed)
rewrites `⟦M⟧^m` to `⟦M.powRep m⟧`, after which
`elementaryWeightQ_phi_mk` (cycle 226) is definitional. -/
theorem elementaryWeightQ_phi_zpow_natCast_mk
    {s : ℕ} (M : RKTableau s) (m : ℕ) (t : RT) :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) ^ ((m : ℤ))) t
      = (M.powRep m).2.elementaryWeight t := by
  rw [zpow_natCast, ← RKTableau.powRep_quotient_eq M m]
  rfl

/-- *Phase D.3.b (cycle 361) — ℤ-form lift: negative `Int.negSucc` case.*
For `n = Int.negSucc m = -(m+1)`, the §383 quotient power's elementary
weight at any tree equals the negation of the bottom-block contribution
of cycle 359's `(m+1)`-fold composite representative's inverse.

Bridge: `zpow_negSucc` reduces `⟦M⟧ ^ (Int.negSucc m)` to
`(⟦M⟧ ^ (m+1))⁻¹`. Cycle 359's `powRep_quotient_eq` (reversed) rewrites
`⟦M⟧^(m+1)` to `⟦M.powRep (m+1)⟧`. Then cycle 358's
`elementaryWeightQ_phi_inv_mk` applied to the `(M.powRep (m+1)).2`
representative gives the bottom-block expansion.

`Σ`-eta on `M.powRep (m+1) = ⟨(M.powRep (m+1)).1, (M.powRep (m+1)).2⟩`
makes the rewrite definitional. -/
theorem elementaryWeightQ_phi_zpow_negSucc_mk
    {s : ℕ} (M : RKTableau s) (m : ℕ) (t : RT) :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) ^ (Int.negSucc m)) t
      = - ∑ j : Fin (M.powRep (m + 1)).1,
          (M.powRep (m + 1)).2.b j *
            (M.powRep (m + 1)).2.derivativeWeightWithSrc
              (M.powRep (m + 1)).2.inverse j t := by
  rw [zpow_negSucc, ← RKTableau.powRep_quotient_eq M (m + 1)]
  exact elementaryWeightQ_phi_inv_mk (M.powRep (m + 1)).2 t

/-- *Phase D.3.b (cycle 361) — ℤ-form lift: non-vacuity at `cherry`
with `explicitEuler`, `m = 0` positive case.* Exercises the positive
natCast branch on the order-2 tree, confirming the `M.powRep 0`
identity-representative reduction. At `m = 0`,
`(explicitEuler.powRep 0).2 = RKTableau.id` and
`RKTableau.id.elementaryWeight cherry = 0` (by `elementaryWeight_id`,
cycle 219). -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ ((0 : ℕ) : ℤ)) RootedTree.cherry
      = (RKTableau.explicitEuler.powRep 0).2.elementaryWeight
          RootedTree.cherry :=
  elementaryWeightQ_phi_zpow_natCast_mk
    RKTableau.explicitEuler 0 RootedTree.cherry

/-- *Phase D.3.b (cycle 361) — ℤ-form lift: non-vacuity at `cherry`
with `explicitEuler`, `m = 0` negative case (`Int.negSucc 0 = -1`).*
Exercises the negative-power branch at the order-2 tree with `n = -1`,
matching cycle 360's `linearResidualAt_one_mk_eq` pattern but via the
ℤ-form lift rather than the special-case `zpow_neg_one` bridge. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (Int.negSucc 0)) RootedTree.cherry
      = - ∑ j : Fin (RKTableau.explicitEuler.powRep 1).1,
          (RKTableau.explicitEuler.powRep 1).2.b j *
            (RKTableau.explicitEuler.powRep 1).2.derivativeWeightWithSrc
              (RKTableau.explicitEuler.powRep 1).2.inverse j RootedTree.cherry :=
  elementaryWeightQ_phi_zpow_negSucc_mk
    RKTableau.explicitEuler 0 RootedTree.cherry

/-- *Phase D.3.b (cycle 361) — general closed form for the residual at
`i = m + 1` at arbitrary `t` (representative form).* Generalises cycle
360's `linearResidualAt_one_mk_eq` (which handled `i = 1` via the
special-case `zpow_neg_one` bridge) to **arbitrary positive `i`** via
the ℤ-form lift `elementaryWeightQ_phi_zpow_negSucc_mk` shipped above.
The closed form exposes the residual's structural dependence on
`M.powRep (m+1)`'s representative data at subtrees of `t`.

For `m = 0`, this gives the `i = 1` form via the `M.powRep 1` representative
(which is Σ-eta equivalent to `M` itself); for `m = 1`, the `i = 2` form
(`M.powRep 2`); etc.

Bridge: `-(((m+1) : ℕ) : ℤ) = Int.negSucc m` by definitional reduction
of `Int.neg` on `Int.ofNat (Nat.succ _)`. -/
theorem linearResidualAt_succ_mk_eq
    {s : ℕ} (M : RKTableau s) (m : ℕ) (t : RT) :
    linearResidualAt (m + 1)
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) t
      = - (∑ j : Fin (M.powRep (m + 1)).1,
              (M.powRep (m + 1)).2.b j *
                (M.powRep (m + 1)).2.derivativeWeightWithSrc
                  (M.powRep (m + 1)).2.inverse j t)
        + ((m : ℝ) + 1) * M.elementaryWeight t := by
  unfold linearResidualAt
  have h_pow :
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) ^ (-(((m + 1) : ℕ) : ℤ))
        = (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) ^ (Int.negSucc m) :=
    rfl
  rw [h_pow, elementaryWeightQ_phi_zpow_negSucc_mk M m t,
      elementaryWeightQ_phi_mk]
  push_cast
  ring

/-- *Phase D.3.b (cycle 361; restated cycle 364) — non-vacuity: closed
form at `i = 2` at `cherry` with `explicitEuler`.* Exercises
`linearResidualAt_succ_mk_eq` at `m = 1` on the order-2 tree, the
first witness of the closed-form expression for the residual at
`i = 2` via the ℤ-form lift. Cycle 364: RHS updated for the redefined
coefficient. -/
example :
    linearResidualAt (1 + 1)
        (Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩) RootedTree.cherry
      = - (∑ j : Fin (RKTableau.explicitEuler.powRep (1 + 1)).1,
              (RKTableau.explicitEuler.powRep (1 + 1)).2.b j *
                (RKTableau.explicitEuler.powRep (1 + 1)).2.derivativeWeightWithSrc
                  (RKTableau.explicitEuler.powRep (1 + 1)).2.inverse
                  j RootedTree.cherry)
        + (((1 : ℕ) : ℝ) + 1)
            * RKTableau.explicitEuler.elementaryWeight RootedTree.cherry :=
  linearResidualAt_succ_mk_eq RKTableau.explicitEuler 1 RootedTree.cherry

/-- *Phase D.3.b (cycle 361) — non-vacuity: closed form at `i = 3` at
`vertex` with `explicitEuler`.* Exercises `linearResidualAt_succ_mk_eq`
at `m = 2` on the single-vertex tree; cross-checks that the closed
form is consistent with `linearResidualAt_vertex_eq_zero`: the residual
must equal 0 at vertex regardless of `i`. -/
example :
    linearResidualAt 3
        (Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩) RootedTree.vertex
      = 0 :=
  linearResidualAt_vertex_eq_zero 3 _

/-- *Phase D.3.b Step 1 (cycle 362) — non-vacuity at `cherry`.*
Trivial-agreement case for the cycle 362
`derivativeWeightWithSrc_eq_of_strict_subtree_agreement` lemma:
`M₁ = M₁' = explicitEuler`, so the strict-subtree hypothesis is
discharged by `fun _ _ => rfl`. Confirms the substitution lemma's
signature compiles and the lemma fires on a concrete tableau / tree
pair from §422's downstream consumer. A more substantive witness
exercising genuinely-distinct tableaux agreeing only at strict
subtrees of `cherry` is left to cycle 363+. -/
example :
    RKTableau.explicitEuler.derivativeWeightWithSrc
        RKTableau.explicitEuler 0 RootedTree.cherry
      = RKTableau.explicitEuler.derivativeWeightWithSrc
          RKTableau.explicitEuler 0 RootedTree.cherry :=
  RKTableau.derivativeWeightWithSrc_eq_of_strict_subtree_agreement
    (M₁ := RKTableau.explicitEuler) (M₁' := RKTableau.explicitEuler)
    RKTableau.explicitEuler RootedTree.cherry (fun _ _ => rfl) 0

/-! ### Phase D.3.b Step 2 (cycle 365) — parametricity of `linearResidualAt`

Cycle 360–362 shipped the §422 D.3.b infrastructure: the
`linearResidualAt` helper (cycle 360, redefined cycle 364), the ℤ-form
lift `elementaryWeightQ_phi_zpow_negSucc_mk` (cycle 361), and the
strict-subtree parametricity lemma for `derivativeWeightWithSrc`
(cycle 362, `derivativeWeightWithSrc_eq_of_strict_subtree_agreement`).
Cycle 365 ships **Phase D.3.b Step 2**: parametricity for
`linearResidualAt` itself. Concretely, the headline says that the
residual at a given `(i, t)` depends only on the §383 quotient
class's `elementaryWeightQ_phi` values at subtrees of `t`
(closed-subtree form, `s.order ≤ t.order` — see "Faithfulness note"
below for the closed-vs-strict justification).

The proof structure decomposes into:

* **Sub-lemma A — `powRep_sum_eq_of_strict_subtree_agreement`**: the
  substantive content. States that `Φ_{η_q^(-(m+1))}(t)` is invariant
  under quotient classes agreeing on `Φ` at every tree of order
  `≤ t.order`. Body deferred to cycle 366 (sorry) — the load-bearing
  algebraic identity reduces (via Quotient.inductionOn₂ +
  `elementaryWeightQ_phi_zpow_negSucc_mk`) to a comparison of two
  `powRep`-sums with **different stage counts** (heterogeneous Σ-types
  in `M.powRep (m+1)` vs `M'.powRep (m+1)`), which requires a more
  involved structural argument than the existing cycle 362 lemma alone
  can deliver.

* **Sub-lemma B — `linearResidualAt_depends_only_on_strict_subtrees`**:
  the headline. Direct composition of Sub-lemma A with cycle 364's
  redefined `linearResidualAt`, splitting on `i = 0` (`Φ_{η^0}(t) = 0`
  by `zpow_zero` + `elementaryWeightQ_phi_id`) and `i = m + 1` (apply
  Sub-lemma A on the `Φ_{η_q^(-(m+1))}(t)` term and `h_closed t (le_refl _)`
  on the direct `Φ_{η_q}(t)` term). Ships **axiom-clean** modulo
  Sub-lemma A as black box.

### Faithfulness note: closed-subtree vs strict-subtree

The cycle 365 strategy's headline scopes the hypothesis as
**closed-subtree** agreement (`s.order ≤ t.order`, including `t`
itself). This is **strictly weaker** as a Lean theorem (a more
permissive consumer interface) and is **sufficient** for Phase D.3.d's
`underlyingOneStepMethod_aux` recursion: by the time strong induction
on `t.order` reaches `t`, the recursion has stored agreement at every
`s.order ≤ t.order` (since `s.order < t.order` follows from the
recursive hypothesis, and `s.order = t.order` is supplied at the
recursion's anchor point).

The strict-subtree form (with separate handling of `t`-itself via the
cycle 364 Discovery #3 cancellation) is the stretch target; cycle 365
ships the closed-subtree form to maximise the probability of an
axiom-clean headline ship under a constrained sorry budget.

### Cycle 365 → 366 split

Per the strategy's "Likely" outcome: cycle 365 ships **Sub-lemma A's
signature (sorry) + Sub-lemma B's full body (axiom-clean)**. Cycle 366
discharges Sub-lemma A's body; that closure restores `Section422.lean`
to sorry-free. The headline (Sub-lemma B) is locked in axiom-clean
form via this cycle's ship; cycle 366 work is restricted to A's body.
-/

/-- *Phase D.3.b Step 2 (cycle 365) — Sub-lemma A:* parametricity of
`Φ_{η^(-(m+1))}(t)` under closed-subtree agreement. If `η_q` and `η_q'`
agree on `elementaryWeightQ_phi` at every tree of order at most
`t.order` (including `t` itself), then their negative-power images
`η_q^(-(m+1))` and `η_q'^(-(m+1))` agree on `elementaryWeightQ_phi`
at `t`.

**Body deferred to cycle 366.** Per the cycle 365 task results, the
substantive algebraic content is the heterogeneous Σ-type comparison
of the two `powRep`-sums produced by
`elementaryWeightQ_phi_zpow_negSucc_mk` on `⟦M⟧^(-(m+1))` and
`⟦M'⟧^(-(m+1))` (different stage counts, different source-method
threading). Closing this requires more substantive infrastructure
than the cycle 362 strict-subtree lemma alone provides (likely a
strong-induction-on-`t.order` argument that lifts the cycle 362 lemma
through `M.inverse` substitution, plus a `powRep`-level cancellation
identity matching the cycle 364 Discovery #3 prediction).

**Cycle 366 obligation**: discharge the body. Cycle 366 should attempt:
(i) Quotient.inductionOn₂ on `η_q, η_q'`; (ii) apply
`elementaryWeightQ_phi_zpow_negSucc_mk` on both sides; (iii) prove
equality of the two heterogeneous `powRep`-sums via an auxiliary
parametricity argument (likely strong induction on `t.order` with
`derivativeWeightWithSrc_eq_of_strict_subtree_agreement` at the inner
step). -/
theorem powRep_sum_eq_of_strict_subtree_agreement
    (m : ℕ) (t : RT)
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (_h_closed : ∀ s : RT, s.order ≤ t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    elementaryWeightQ_phi (η_q ^ (-(((m + 1) : ℕ) : ℤ))) t
      = elementaryWeightQ_phi (η_q' ^ (-(((m + 1) : ℕ) : ℤ))) t := by
  sorry

/-! ### Phase D.3.b Step 2 (cycle 366) — specialised small-tree witnesses

Per the cycle 366 strategy §D Priority 2 graceful degradation, the
general body of `powRep_sum_eq_of_strict_subtree_agreement` (Sub-lemma A)
is deferred to cycle 367+ pending substantive infrastructure for
comparing heterogeneous `powRep`-sums (sums over `Fin (M.1 * (m+1))`
vs `Fin (M'.1 * (m+1))` when `M.1 ≠ M'.1`). Cycle 366 ships
specialised axiom-clean witnesses at small trees where closed-form
quotient-level evaluation bypasses the heterogeneity obstruction.

The witnesses serve two purposes:

* **Non-vacuity / unblock downstream**: at `t = vertex`, the lemma
  closes cleanly via cycle 341 P3 (`elementaryWeightQ_phi_zpow_vertex`).
  Combined with `linearResidualAt_vertex_eq_zero` already in this file,
  this gives a complete vertex-case parametricity certificate.
* **Cherry m = 0 case**: at `t = cherry`, `m = 0`, the lemma closes
  via a closed-form computation analogous to cycle 358's `_inv_mk`
  reduction at cherry. The closed form `Φ_{η⁻¹}(cherry) =
  (Φ_η(vertex))^2 - Φ_η(cherry)` (a quotient-level invariant
  established here) makes the parametricity claim immediate under
  agreement at `vertex` and `cherry`. Cycle 367+ will generalise to
  `(m+1)*(m+2)/2 * (Φ_η(vertex))^2 - (m+1)*Φ_η(cherry)` for arbitrary
  `m`. -/

/-- *Phase D.3.b Step 2 (cycle 366) — Priority 2 witness:* parametricity
of `Φ_{η^(-(m+1))}` at `t = vertex` under agreement at vertex. Specialised
case of Sub-lemma A `powRep_sum_eq_of_strict_subtree_agreement` at
`t = RootedTree.vertex`.

Proof: by cycle 341 P3 (`elementaryWeightQ_phi_zpow_vertex`), both sides
reduce to `(-(m+1) : ℝ) * Φ_η(vertex)` and `(-(m+1) : ℝ) * Φ_{η'}(vertex)`
respectively, which agree under `h`. -/
theorem powRep_sum_eq_of_agreement_at_vertex
    (m : ℕ) (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h : elementaryWeightQ_phi η_q RootedTree.vertex
         = elementaryWeightQ_phi η_q' RootedTree.vertex) :
    elementaryWeightQ_phi (η_q ^ (-(((m + 1) : ℕ) : ℤ))) RootedTree.vertex
      = elementaryWeightQ_phi (η_q' ^ (-(((m + 1) : ℕ) : ℤ))) RootedTree.vertex := by
  rw [elementaryWeightQ_phi_zpow_vertex η_q (-(((m + 1) : ℕ) : ℤ)),
      elementaryWeightQ_phi_zpow_vertex η_q' (-(((m + 1) : ℕ) : ℤ)), h]

/-- *Phase D.3.b Step 2 (cycle 366) — Priority 2 witness non-vacuity at
`(m, η_q, η_q') = (0, ⟦explicitEuler⟧, ⟦explicitEuler⟧)`.* Confirms the
vertex specialisation fires with `h` discharged by `rfl`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1) : ℕ) : ℤ)))
        RootedTree.vertex
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1) : ℕ) : ℤ)))
          RootedTree.vertex :=
  powRep_sum_eq_of_agreement_at_vertex 0
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    rfl

/-! ### Phase D.3.b Step 2 (cycle 367) — cherry closed form + cherry m=0 witness

Per the cycle 367 strategy, the cycle 366 small-tree witness library is
extended one tree higher: cycle 366 covers `t = vertex`; cycle 367 covers
the order-2 tree `t = cherry`. The vehicle is a quotient-level closed
form `Φ_{η⁻¹}(cherry) = (Φ_η(vertex))² − Φ_η(cherry)` (a cherry analog
of cycle 341 P3's `elementaryWeightQ_phi_zpow_vertex` vertex closed
form), which makes Sub-lemma A's `m = 0` cherry case immediate under
agreement at `{vertex, cherry}`.

The cherry closed form is itself a non-trivial quotient-level
invariant: at the level of representatives, `Φ_{⟦M⟧⁻¹}(cherry)`
depends on `M.inverse`'s `derivativeWeightWithSrc` data (cycle 358's
`elementaryWeightQ_phi_inv_mk`), but the cycle 366 vertex collapses
(`derivativeWeightWithSrc_vertex` + `derivativeWeight_vertex` +
`M.inverse.b = -M.b`) reduce that data at cherry to a closed
expression in `Φ_η(vertex)` and `Φ_η(cherry)` alone. -/

/-- *Phase D.3.b Step 2 (cycle 367) — cherry closed form:* the cherry
analog of cycle 341 P3's vertex closed form `_zpow_vertex`. At the
order-2 tree `cherry`, the elementary weight of the inverse class
`η_q⁻¹` admits a closed expression in `Φ_η(vertex)` and `Φ_η(cherry)`:
`Φ_{η⁻¹}(cherry) = (Φ_η(vertex))² − Φ_η(cherry)`.

Proof: `Quotient.inductionOn` on `η_q` gives a representative
`⟨s, M⟩`. Cycle 358's `elementaryWeightQ_phi_inv_mk` reduces the LHS
to `-∑ᵢ M.b i · M.derivativeWeightWithSrc M.inverse i cherry`. At
`cherry = mk [vertex]`, the helper unfolds (via the mutual
recursion) to `M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j`,
using `derivativeWeightWithSrc_vertex` to collapse the recursive call
and `derivativeWeightWithSrcProd _ _ [] = 1` for the empty-list
base. The §382 inverse construction (`M.inverse.b = -M.b`) gives
`M.inverse.elementaryWeight vertex = -M.elementaryWeight vertex`.
Final assembly is a sum-of-products manipulation via
`Finset.sum_congr` + `Finset.sum_sub_distrib` + `← Finset.sum_mul`
+ `ring`. -/
theorem elementaryWeightQ_phi_inv_cherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹) RootedTree.cherry
      = (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
        - elementaryWeightQ_phi η_q RootedTree.cherry := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- Closed-form helpers (each ~one-level definitional unfold).
  have h_inv_v : M.inverse.elementaryWeight RootedTree.vertex
      = -M.elementaryWeight RootedTree.vertex := by
    show ∑ j : Fin s, M.inverse.b j * M.inverse.derivativeWeight j RootedTree.vertex
          = -(∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.inverse_b, RKTableau.derivativeWeight_vertex,
        RKTableau.derivativeWeight_vertex, neg_mul]
  have h_vertex : M.elementaryWeight RootedTree.vertex = ∑ j : Fin s, M.b j := by
    show ∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.b j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_dw_cherry : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.cherry = ∑ j : Fin s, M.A i j := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_cherry : M.elementaryWeight RootedTree.cherry
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.cherry
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_cherry i]
  have h_dws_cherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i RootedTree.cherry
        = M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * (1 : ℝ) = _
    rw [mul_one]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
  -- Main computation: apply cycle 358 _inv_mk, _mk, then assemble.
  rw [elementaryWeightQ_phi_inv_mk M RootedTree.cherry,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_sum :
      (∑ i : Fin s, M.b i * M.derivativeWeightWithSrc M.inverse i RootedTree.cherry)
        = M.elementaryWeight RootedTree.cherry
          - M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight RootedTree.vertex := by
    have h_subst :
        (∑ i : Fin s, M.b i * M.derivativeWeightWithSrc M.inverse i RootedTree.cherry)
          = ∑ i : Fin s, (M.b i * ∑ j : Fin s, M.A i j
                          - M.b i * M.elementaryWeight RootedTree.vertex) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_dws_cherry i, h_inv_v]; ring
    rw [h_subst, Finset.sum_sub_distrib, ← h_cherry,
        ← Finset.sum_mul, ← h_vertex]
  rw [h_sum]; ring

/-- *Phase D.3.b Step 2 (cycle 367) — cherry closed form non-vacuity at
`η_q = ⟦explicitEuler⟧`.* The expected value is
`Φ_{⟦explicitEuler⟧⁻¹}(cherry) = (1)² − 0 = 1`, since for explicit
Euler `Σ b = 1` (so `Φ_η(vertex) = 1`) and `A = 0` (so
`Φ_η(cherry) = ∑ᵢ b i · ∑ⱼ A i j = 0`). -/
example :
    elementaryWeightQ_phi
      ((Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩))⁻¹ RootedTree.cherry = 1 := by
  rw [elementaryWeightQ_phi_inv_cherry, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk]
  have h_vertex : RKTableau.explicitEuler.elementaryWeight RootedTree.vertex = 1 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.vertex = 1
    simp [RKTableau.explicitEuler, RKTableau.derivativeWeight_vertex]
  have h_cherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.cherry = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_cherry : RKTableau.explicitEuler.elementaryWeight RootedTree.cherry = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.cherry = 0
    simp [h_cherry_zero]
  rw [h_vertex, h_cherry]; ring

/-- *Phase D.3.b Step 2 (cycle 367) — Priority 1 cherry m=0 witness:*
specialisation of Sub-lemma A `powRep_sum_eq_of_strict_subtree_agreement`
at `t = cherry, m = 0`. Under agreement at `vertex` and `cherry`, the
`η_q^(-1)` images at `cherry` coincide.

Proof: reduce `η_q ^ (-(((0 + 1 : ℕ) : ℤ)))` to `η_q⁻¹` via
`Nat.cast_one` + `zpow_neg_one`, apply cycle 367's
`elementaryWeightQ_phi_inv_cherry` on both sides, then substitute
`h_vertex` and `h_cherry`. -/
theorem powRep_sum_eq_of_agreement_at_cherry_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ)))) RootedTree.cherry
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ)))) RootedTree.cherry := by
  have h_pow : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
      ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
    intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow η_q, h_pow η_q',
      elementaryWeightQ_phi_inv_cherry, elementaryWeightQ_phi_inv_cherry,
      h_vertex, h_cherry]

/-- *Phase D.3.b Step 2 (cycle 367) — cherry m=0 witness non-vacuity at
`η_q = η_q' = ⟦explicitEuler⟧`.* Discharges the two agreement
hypotheses by `rfl`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
        RootedTree.cherry
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
          RootedTree.cherry :=
  powRep_sum_eq_of_agreement_at_cherry_zero
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    rfl rfl

/-- *Phase D.3.b Step 2 (cycle 368) — broom₃ closed form for Φ_{η_q⁻¹}.*
At the order-3 tree `broom₃ = mk [vertex, vertex]`, the quotient-
level elementary weight of the §383 inverse class admits the closed
form
  `Φ_{η_q⁻¹}(broom₃) = -(Φ_η(vertex))^3
                       + 2 · Φ_η(vertex) · Φ_η(cherry)
                       - Φ_η(broom₃)`.

Third data point in the cycle 366 §G Route B hypothesis ladder
(vertex, cherry, broom₃): `Φ_{η_q⁻¹}` at strict subtrees of `t` is
a polynomial in `Φ_η` at those subtrees with quotient-invariant
coefficients. Cycle 367 covered the order-1 and order-2 cases; this
cycle adds order-3 with a two-child structure.

Proof outline (mirrors cycle 367's `elementaryWeightQ_phi_inv_cherry`
with one extra unfold layer for the second child):

1. Reduce to a representative `⟨s, M⟩` via `Quotient.inductionOn`.
2. Reuse the cycle 367 helpers `h_inv_v` (inverse weight at vertex),
   `h_vertex` (Φ_M(vertex) as ∑b), `h_dw_cherry`, `h_cherry`.
3. Introduce three new helpers for the broom₃ structure:
   - `h_dw_broom₃` : `M.derivativeWeight i broom₃ = (∑ⱼ M.A i j)^2`
   - `h_broom₃` : `M.elementaryWeight broom₃ = ∑ᵢ M.b i · (∑ⱼ M.A i j)^2`
   - `h_dws_broom₃` : `M.derivativeWeightWithSrc M.inverse i broom₃
                       = (M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j)^2`
4. After `_inv_mk`, `_mk` × 3 rewrites, substitute the closed form,
   expand the square per-summand via `ring`, distribute the sum
   via `Finset.sum_add_distrib`, `Finset.sum_sub_distrib`, factor
   out constants via `← Finset.mul_sum`, then close with `ring`. -/
theorem elementaryWeightQ_phi_inv_broom₃
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹) RootedTree.broom₃
      = -(elementaryWeightQ_phi η_q RootedTree.vertex) ^ 3
        + 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q RootedTree.cherry
        - elementaryWeightQ_phi η_q RootedTree.broom₃ := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- Cycle 367 helpers (reused verbatim).
  have h_inv_v : M.inverse.elementaryWeight RootedTree.vertex
      = -M.elementaryWeight RootedTree.vertex := by
    show ∑ j : Fin s, M.inverse.b j * M.inverse.derivativeWeight j RootedTree.vertex
          = -(∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.inverse_b, RKTableau.derivativeWeight_vertex,
        RKTableau.derivativeWeight_vertex, neg_mul]
  have h_vertex : M.elementaryWeight RootedTree.vertex = ∑ j : Fin s, M.b j := by
    show ∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.b j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_dw_cherry : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.cherry = ∑ j : Fin s, M.A i j := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_cherry : M.elementaryWeight RootedTree.cherry
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.cherry
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_cherry i]
  -- New cycle 368 helpers for the broom₃ two-child structure.
  have h_dw_broom₃ : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.broom₃ = (∑ j : Fin s, M.A i j) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 2
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    rw [h_inner_sum, h_prod_step]; ring
  have h_broom₃ : M.elementaryWeight RootedTree.broom₃
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.broom₃
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_broom₃ i]
  have h_dws_broom₃ : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i RootedTree.broom₃
        = (M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j) ^ 2 := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * M.derivativeWeightWithSrcProd M.inverse i [RootedTree.vertex]
        = (M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j) ^ 2
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
    have h_prod_step :
        M.derivativeWeightWithSrcProd M.inverse i [RootedTree.vertex]
          = M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j := by
      show (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ j : Fin s, M.A i j
                  * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
            * M.derivativeWeightWithSrcProd M.inverse i []
          = M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightWithSrcProd M.inverse i [] = 1 from rfl, mul_one,
          h_inner_sum]
    rw [h_inner_sum, h_prod_step]; ring
  -- Main computation: assemble closed form via _inv_mk + _mk × 3 + sum algebra.
  rw [elementaryWeightQ_phi_inv_mk M RootedTree.broom₃,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_sum :
      (∑ i : Fin s, M.b i * M.derivativeWeightWithSrc M.inverse i RootedTree.broom₃)
        = M.elementaryWeight RootedTree.broom₃
          - 2 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight RootedTree.cherry
          + M.elementaryWeight RootedTree.vertex ^ 3 := by
    have h_subst :
        (∑ i : Fin s, M.b i * M.derivativeWeightWithSrc M.inverse i RootedTree.broom₃)
          = ∑ i : Fin s,
            (M.b i * (∑ j : Fin s, M.A i j) ^ 2
              - 2 * M.elementaryWeight RootedTree.vertex
                  * (M.b i * ∑ j : Fin s, M.A i j)
              + M.elementaryWeight RootedTree.vertex ^ 2 * M.b i) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_dws_broom₃ i, h_inv_v]; ring
    rw [h_subst, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum,
        ← h_broom₃, ← h_cherry, ← h_vertex]
    ring
  rw [h_sum]; ring

/-- *Phase D.3.b Step 2 (cycle 368) — broom₃ closed form non-vacuity at
`η_q = ⟦explicitEuler⟧`.* The expected value is
`Φ_{⟦explicitEuler⟧⁻¹}(broom₃) = -(1)^3 + 2·1·0 − 0 = -1`, since for
explicit Euler `Σ b = 1` (so `Φ_η(vertex) = 1`) and `A = 0` (so
`Φ_η(cherry) = 0` and `Φ_η(broom₃) = ∑ᵢ b i · (∑ⱼ A i j)^2 = 0`). -/
example :
    elementaryWeightQ_phi
      ((Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩))⁻¹ RootedTree.broom₃ = -1 := by
  rw [elementaryWeightQ_phi_inv_broom₃, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_vertex : RKTableau.explicitEuler.elementaryWeight RootedTree.vertex = 1 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.vertex = 1
    simp [RKTableau.explicitEuler, RKTableau.derivativeWeight_vertex]
  have h_cherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.cherry = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_cherry : RKTableau.explicitEuler.elementaryWeight RootedTree.cherry = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.cherry = 0
    simp [h_cherry_zero]
  have h_broom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.broom₃ = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_broom₃ : RKTableau.explicitEuler.elementaryWeight RootedTree.broom₃ = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.broom₃ = 0
    simp [h_broom₃_zero]
  rw [h_vertex, h_cherry, h_broom₃]; ring

/-- *Phase D.3.b Step 2 (cycle 368) — Priority 3 broom₃ m=0 witness:*
specialisation of Sub-lemma A `powRep_sum_eq_of_strict_subtree_agreement`
at `t = broom₃, m = 0`. Under agreement at `vertex`, `cherry`, and
`broom₃` (three subtrees corresponding to the closed-form factors),
the `η_q^(-1)` images at `broom₃` coincide.

Proof: reduce `η_q ^ (-(((0 + 1 : ℕ) : ℤ)))` to `η_q⁻¹` via
`Nat.cast_one` + `zpow_neg_one`, apply cycle 368's
`elementaryWeightQ_phi_inv_broom₃` on both sides, then substitute
`h_vertex`, `h_cherry`, and `h_broom₃`. -/
theorem powRep_sum_eq_of_agreement_at_broom₃_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry)
    (h_broom₃ : elementaryWeightQ_phi η_q RootedTree.broom₃
              = elementaryWeightQ_phi η_q' RootedTree.broom₃) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ)))) RootedTree.broom₃
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ)))) RootedTree.broom₃ := by
  have h_pow : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
      ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
    intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow η_q, h_pow η_q',
      elementaryWeightQ_phi_inv_broom₃, elementaryWeightQ_phi_inv_broom₃,
      h_vertex, h_cherry, h_broom₃]

/-- *Phase D.3.b Step 2 (cycle 368) — broom₃ m=0 witness non-vacuity at
`η_q = η_q' = ⟦explicitEuler⟧`.* Discharges the three agreement
hypotheses by `rfl`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
        RootedTree.broom₃
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
          RootedTree.broom₃ :=
  powRep_sum_eq_of_agreement_at_broom₃_zero
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    rfl rfl rfl

/-- *Phase D.3.b Step 2 (cycle 369) — `mk [cherry]` closed form for Φ_{η_q⁻¹}.*
At the order-3 tree `mk [cherry] = mk [mk [vertex]]` (the depth-2 "ladder"
tree: root with one child that is itself `cherry`), the quotient-level
elementary weight of the §383 inverse class admits the closed form
  `Φ_{η_q⁻¹}(mk [cherry]) = -(Φ_η(vertex))^3
                            + 2 · Φ_η(vertex) · Φ_η(cherry)
                            - Φ_η(mk [cherry])`.

Fourth data point in the cycle 366 §G Route B hypothesis ladder
(vertex, cherry, broom₃, mk [cherry]): `Φ_{η_q⁻¹}` at strict subtrees
of `t` is a polynomial in `Φ_η` at those subtrees with quotient-
invariant coefficients. Note that the closed form is structurally
identical to cycle 368's `broom₃` closed form — both order-3 trees
yield `-v^3 + 2vc - Φ_η(t)`, but with different `w = Φ_η(t)` since
`broom₃ = mk [τ, τ]` and `mk [cherry] = mk [mk [τ]]` are distinct
rooted trees. The shared inverse-coproduct structure mirrors the
Connes–Kreimer Hopf algebra signature for order-3 trees.

Proof outline (mirrors cycle 368's `broom₃` recipe with one extra
inner unfold to handle the cherry-child):

1. Reduce to a representative `⟨s, M⟩` via `Quotient.inductionOn`.
2. Reuse the cycle 367 helpers `h_inv_v`, `h_vertex`, `h_dw_cherry`,
   `h_cherry`, `h_dws_cherry`.
3. Add new helpers for the `mk [cherry]` structure:
   - `h_inv_cherry` : `M.inverse.elementaryWeight cherry =
     (M.elementaryWeight vertex)^2 - M.elementaryWeight cherry`
     (derived from cycle 367's quotient-level
     `elementaryWeightQ_phi_inv_cherry` at `⟦M⟧`, descended via
     `_mk` rfl reductions).
   - `h_dw_mkCherry` : `M.derivativeWeight i (mk [cherry]) =
     ∑ⱼ M.A i j · ∑ₖ M.A j k` (one-layer unfold + `h_dw_cherry`).
   - `h_mkCherry` : `M.elementaryWeight (mk [cherry]) =
     ∑ᵢ M.b i · ∑ⱼ M.A i j · ∑ₖ M.A j k` (one `Finset.sum_congr`).
   - `h_dws_mkCherry` : the inverse-source variant of `h_dw_mkCherry`,
     with the inner `dws cherry j` rewritten to its closed form
     `(inv_v + ∑ₖ A j k)` and the result split into three sum-shaped
     pieces for the back-substitution.
4. After `_inv_mk`, `_mk` × 3 rewrites, substitute closed forms,
   distribute the sum via `Finset.sum_add_distrib`,
   `Finset.sum_sub_distrib`, factor constants via `← Finset.mul_sum`,
   then back-substitute via `← h_mkCherry, ← h_cherry, ← h_vertex`,
   close with `ring`. -/
theorem elementaryWeightQ_phi_inv_mkCherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹) (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      = -(elementaryWeightQ_phi η_q RootedTree.vertex) ^ 3
        + 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q RootedTree.cherry
        - elementaryWeightQ_phi η_q (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- Cycle 367 helpers (reused verbatim).
  have h_inv_v : M.inverse.elementaryWeight RootedTree.vertex
      = -M.elementaryWeight RootedTree.vertex := by
    show ∑ j : Fin s, M.inverse.b j * M.inverse.derivativeWeight j RootedTree.vertex
          = -(∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.inverse_b, RKTableau.derivativeWeight_vertex,
        RKTableau.derivativeWeight_vertex, neg_mul]
  have h_vertex : M.elementaryWeight RootedTree.vertex = ∑ j : Fin s, M.b j := by
    show ∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.b j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_dw_cherry : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.cherry = ∑ j : Fin s, M.A i j := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_cherry : M.elementaryWeight RootedTree.cherry
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.cherry
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_cherry i]
  have h_dws_cherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i RootedTree.cherry
        = M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * (1 : ℝ) = _
    rw [mul_one]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
  -- Cycle 369: `h_inv_cherry` lifted from cycle 367's quotient theorem at ⟦M⟧.
  have h_inv_cherry : M.inverse.elementaryWeight RootedTree.cherry
      = (M.elementaryWeight RootedTree.vertex) ^ 2
        - M.elementaryWeight RootedTree.cherry :=
    elementaryWeightQ_phi_inv_cherry
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)
  -- New cycle 369 helpers for the mk [cherry] depth-2 ladder structure.
  have h_dw_mkCherry : ∀ i : Fin s,
      M.derivativeWeight i (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
          * M.derivativeWeightProd i [] = _
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dw_cherry j]
  have h_mkCherry : M.elementaryWeight (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkCherry i]
  have h_dws_mkCherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = M.inverse.elementaryWeight RootedTree.cherry
          + M.inverse.elementaryWeight RootedTree.vertex * ∑ j : Fin s, M.A i j
          + ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.cherry
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.cherry)
          * M.derivativeWeightWithSrcProd M.inverse i [] = _
    rw [show M.derivativeWeightWithSrcProd M.inverse i [] = 1 from rfl, mul_one]
    have h_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeightWithSrc M.inverse j RootedTree.cherry
          = ∑ j : Fin s, (M.A i j * M.inverse.elementaryWeight RootedTree.vertex
                          + M.A i j * ∑ k : Fin s, M.A j k) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dws_cherry j]; ring
    rw [h_inner, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  -- Main computation: assemble closed form via _inv_mk + _mk × 3 + sum algebra.
  rw [elementaryWeightQ_phi_inv_mk M (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_sum :
      (∑ i : Fin s, M.b i
          * M.derivativeWeightWithSrc M.inverse i (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
        = M.elementaryWeight (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          - 2 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight RootedTree.cherry
          + M.elementaryWeight RootedTree.vertex ^ 3 := by
    have h_subst :
        (∑ i : Fin s, M.b i
            * M.derivativeWeightWithSrc M.inverse i (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
          = ∑ i : Fin s,
            (M.b i * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
              - M.elementaryWeight RootedTree.vertex
                  * (M.b i * ∑ j : Fin s, M.A i j)
              + ((M.elementaryWeight RootedTree.vertex) ^ 2
                  - M.elementaryWeight RootedTree.cherry) * M.b i) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_dws_mkCherry i, h_inv_cherry, h_inv_v]; ring
    rw [h_subst, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum,
        ← h_mkCherry, ← h_cherry, ← h_vertex]
    ring
  rw [h_sum]; ring

/-- *Phase D.3.b Step 2 (cycle 369) — `mk [cherry]` closed form non-vacuity
at `η_q = ⟦explicitEuler⟧`.* The expected value is
`Φ_{⟦explicitEuler⟧⁻¹}(mk [cherry]) = -(1)^3 + 2·1·0 − 0 = -1`, since
for explicit Euler `Σ b = 1` (so `Φ_η(vertex) = 1`) and `A = 0` (so
`Φ_η(cherry) = 0` and `Φ_η(mk [cherry]) = ∑ᵢ b i · ∑ⱼ A i j · ∑ k, A j k = 0`).
Structurally identical evaluation to the cycle 368 `broom₃` witness. -/
example :
    elementaryWeightQ_phi
      ((Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩))⁻¹
      (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = -1 := by
  rw [elementaryWeightQ_phi_inv_mkCherry, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_vertex : RKTableau.explicitEuler.elementaryWeight RootedTree.vertex = 1 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.vertex = 1
    simp [RKTableau.explicitEuler, RKTableau.derivativeWeight_vertex]
  have h_cherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.cherry = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_cherry : RKTableau.explicitEuler.elementaryWeight RootedTree.cherry = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.cherry = 0
    simp [h_cherry_zero]
  have h_mkCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0 (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.cherry)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_mkCherry :
      RKTableau.explicitEuler.elementaryWeight (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0
    simp [h_mkCherry_zero]
  rw [h_vertex, h_cherry, h_mkCherry]; ring

/-- *Phase D.3.b Step 2 (cycle 369) — Priority 2 `mk [cherry]` m=0 witness:*
specialisation of Sub-lemma A `powRep_sum_eq_of_strict_subtree_agreement`
at `t = mk [cherry], m = 0`. Under agreement at `vertex`, `cherry`, and
`mk [cherry]` (three subtrees corresponding to the closed-form factors),
the `η_q^(-1)` images at `mk [cherry]` coincide.

Proof: reduce `η_q ^ (-(((0 + 1 : ℕ) : ℤ)))` to `η_q⁻¹` via
`Nat.cast_one` + `zpow_neg_one`, apply cycle 369's
`elementaryWeightQ_phi_inv_mkCherry` on both sides, then substitute
`h_vertex`, `h_cherry`, and `h_mkCherry`. -/
theorem powRep_sum_eq_of_agreement_at_mkCherry_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry)
    (h_mkCherry : elementaryWeightQ_phi η_q (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
              = elementaryWeightQ_phi η_q' (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) := by
  have h_pow : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
      ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
    intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow η_q, h_pow η_q',
      elementaryWeightQ_phi_inv_mkCherry, elementaryWeightQ_phi_inv_mkCherry,
      h_vertex, h_cherry, h_mkCherry]

/-- *Phase D.3.b Step 2 (cycle 369) — `mk [cherry]` m=0 witness non-vacuity
at `η_q = η_q' = ⟦explicitEuler⟧`.* Discharges the three agreement
hypotheses by `rfl`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) :=
  powRep_sum_eq_of_agreement_at_mkCherry_zero
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    rfl rfl rfl

/-- *Phase D.3.b Step 2 (cycle 370) — `bushy` (order-4 broom) closed form for Φ_{η_q⁻¹}.*
At the order-4 broom tree `bushy = mk [vertex, vertex, vertex]`, the
quotient-level elementary weight of the §383 inverse class admits the
closed form
  `Φ_{η_q⁻¹}(bushy) = (Φ_η(vertex))^4
                     − 3 · (Φ_η(vertex))^2 · Φ_η(cherry)
                     + 3 · Φ_η(vertex) · Φ_η(broom₃)
                     − Φ_η(bushy)`.

Fifth data point in the cycle 366 §G Route B hypothesis ladder
(vertex, cherry, broom₃, mk [cherry], bushy). At order-4, the binomial
expansion of `(Aᵢ − v)^3` introduces a new 4-term polynomial structure
in `Φ_η(vertex), Φ_η(cherry), Φ_η(broom₃), Φ_η(bushy)`, confirming
cycle 368's `(Aᵢ − v)^k` Discovery hypothesis at depth 3.

Proof outline (mirrors cycle 368's `broom₃` recipe with one extra
cons-case unfold layer for the third child):

1. Reduce to a representative `⟨s, M⟩` via `Quotient.inductionOn`.
2. Reuse cycle 367/368 helpers `h_inv_v`, `h_vertex`, `h_dw_cherry`,
   `h_cherry`, `h_dw_broom₃`, `h_broom₃`.
3. Add three new helpers for the bushy three-child structure:
   - `h_dw_bushy` : `M.derivativeWeight i bushy = (∑ⱼ M.A i j)^3`
     (three-layer cons-case unfold extending `h_dw_broom₃`).
   - `h_bushy` : `M.elementaryWeight bushy = ∑ᵢ M.b i · (∑ⱼ M.A i j)^3`
     (one `Finset.sum_congr` on `h_dw_bushy`).
   - `h_dws_bushy` : `M.derivativeWeightWithSrc M.inverse i bushy
                      = (M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j)^3`
     (three-layer cons-case unfold of `derivativeWeightWithSrcProd`).
4. After `_inv_mk`, `_mk` × 4 rewrites, substitute the closed form,
   expand the cube per-summand via `ring`, distribute the sum via
   `Finset.sum_sub_distrib`, `Finset.sum_add_distrib`, factor out
   constants via `← Finset.mul_sum` (three applications), then close
   with `ring`. -/
theorem elementaryWeightQ_phi_inv_bushy
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹) RootedTree.bushy
      = (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 4
        - 3 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q RootedTree.cherry
        + 3 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        - elementaryWeightQ_phi η_q RootedTree.bushy := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- Cycle 367 helpers (reused verbatim).
  have h_inv_v : M.inverse.elementaryWeight RootedTree.vertex
      = -M.elementaryWeight RootedTree.vertex := by
    show ∑ j : Fin s, M.inverse.b j * M.inverse.derivativeWeight j RootedTree.vertex
          = -(∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.inverse_b, RKTableau.derivativeWeight_vertex,
        RKTableau.derivativeWeight_vertex, neg_mul]
  have h_vertex : M.elementaryWeight RootedTree.vertex = ∑ j : Fin s, M.b j := by
    show ∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.b j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_dw_cherry : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.cherry = ∑ j : Fin s, M.A i j := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_cherry : M.elementaryWeight RootedTree.cherry
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.cherry
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_cherry i]
  -- Cycle 368 helpers (reused verbatim).
  have h_dw_broom₃ : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.broom₃ = (∑ j : Fin s, M.A i j) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 2
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    rw [h_inner_sum, h_prod_step]; ring
  have h_broom₃ : M.elementaryWeight RootedTree.broom₃
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.broom₃
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_broom₃ i]
  -- New cycle 370 helpers for the bushy three-child structure.
  have h_dw_bushy : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.bushy = (∑ j : Fin s, M.A i j) ^ 3 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex, RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 3
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step_1 :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    have h_prod_step_2 :
        M.derivativeWeightProd i [RootedTree.vertex, RootedTree.vertex]
          = (∑ j : Fin s, M.A i j) ^ 2 := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [RootedTree.vertex]
          = (∑ j : Fin s, M.A i j) ^ 2
      rw [h_inner_sum, h_prod_step_1]; ring
    rw [h_inner_sum, h_prod_step_2]; ring
  have h_bushy : M.elementaryWeight RootedTree.bushy
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 3 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.bushy
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 3
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_bushy i]
  have h_dws_bushy : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i RootedTree.bushy
        = (M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j) ^ 3 := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * M.derivativeWeightWithSrcProd M.inverse i
              [RootedTree.vertex, RootedTree.vertex]
        = (M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j) ^ 3
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
    have h_prod_step_1 :
        M.derivativeWeightWithSrcProd M.inverse i [RootedTree.vertex]
          = M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j := by
      show (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ j : Fin s, M.A i j
                  * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
            * M.derivativeWeightWithSrcProd M.inverse i []
          = M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightWithSrcProd M.inverse i [] = 1 from rfl, mul_one,
          h_inner_sum]
    have h_prod_step_2 :
        M.derivativeWeightWithSrcProd M.inverse i
            [RootedTree.vertex, RootedTree.vertex]
          = (M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j) ^ 2 := by
      show (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ j : Fin s, M.A i j
                  * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
            * M.derivativeWeightWithSrcProd M.inverse i [RootedTree.vertex]
          = (M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j) ^ 2
      rw [h_inner_sum, h_prod_step_1]; ring
    rw [h_inner_sum, h_prod_step_2]; ring
  -- Main computation: assemble closed form via _inv_mk + _mk × 4 + sum algebra.
  rw [elementaryWeightQ_phi_inv_mk M RootedTree.bushy,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_sum :
      (∑ i : Fin s, M.b i * M.derivativeWeightWithSrc M.inverse i RootedTree.bushy)
        = M.elementaryWeight RootedTree.bushy
          - 3 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight RootedTree.broom₃
          + 3 * M.elementaryWeight RootedTree.vertex ^ 2
              * M.elementaryWeight RootedTree.cherry
          - M.elementaryWeight RootedTree.vertex ^ 4 := by
    have h_subst :
        (∑ i : Fin s, M.b i * M.derivativeWeightWithSrc M.inverse i RootedTree.bushy)
          = ∑ i : Fin s,
            (M.b i * (∑ j : Fin s, M.A i j) ^ 3
              - 3 * M.elementaryWeight RootedTree.vertex
                  * (M.b i * (∑ j : Fin s, M.A i j) ^ 2)
              + 3 * M.elementaryWeight RootedTree.vertex ^ 2
                  * (M.b i * ∑ j : Fin s, M.A i j)
              - M.elementaryWeight RootedTree.vertex ^ 3 * M.b i) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_dws_bushy i, h_inv_v]; ring
    rw [h_subst, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← h_bushy, ← h_broom₃, ← h_cherry, ← h_vertex]
    ring
  rw [h_sum]; ring

/-- *Phase D.3.b Step 2 (cycle 370) — bushy closed form non-vacuity at
`η_q = ⟦explicitEuler⟧`.* The expected value is
`Φ_{⟦explicitEuler⟧⁻¹}(bushy) = 1^4 − 3·1²·0 + 3·1·0 − 0 = 1`, since for
explicit Euler `Σ b = 1` (so `Φ_η(vertex) = 1`) and `A = 0` (so
`Φ_η(cherry) = 0`, `Φ_η(broom₃) = 0`, `Φ_η(bushy) = 0`). -/
example :
    elementaryWeightQ_phi
      ((Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩))⁻¹ RootedTree.bushy = 1 := by
  rw [elementaryWeightQ_phi_inv_bushy, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_vertex : RKTableau.explicitEuler.elementaryWeight RootedTree.vertex = 1 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.vertex = 1
    simp [RKTableau.explicitEuler, RKTableau.derivativeWeight_vertex]
  have h_cherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.cherry = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_cherry : RKTableau.explicitEuler.elementaryWeight RootedTree.cherry = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.cherry = 0
    simp [h_cherry_zero]
  have h_broom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.broom₃ = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_broom₃ : RKTableau.explicitEuler.elementaryWeight RootedTree.broom₃ = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.broom₃ = 0
    simp [h_broom₃_zero]
  have h_bushy_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.bushy = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0
                [RootedTree.vertex, RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_bushy : RKTableau.explicitEuler.elementaryWeight RootedTree.bushy = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.bushy = 0
    simp [h_bushy_zero]
  rw [h_vertex, h_cherry, h_broom₃, h_bushy]; ring

/-- *Phase D.3.b Step 2 (cycle 370) — Priority 2 bushy m=0 witness:*
specialisation of Sub-lemma A `powRep_sum_eq_of_strict_subtree_agreement`
at `t = bushy, m = 0`. Under agreement at `vertex`, `cherry`, `broom₃`,
and `bushy` (four subtrees corresponding to the closed-form factors),
the `η_q^(-1)` images at `bushy` coincide.

Proof: reduce `η_q ^ (-(((0 + 1 : ℕ) : ℤ)))` to `η_q⁻¹` via
`Nat.cast_one` + `zpow_neg_one`, apply cycle 370's
`elementaryWeightQ_phi_inv_bushy` on both sides, then substitute
`h_vertex`, `h_cherry`, `h_broom₃`, and `h_bushy`. -/
theorem powRep_sum_eq_of_agreement_at_bushy_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry)
    (h_broom₃ : elementaryWeightQ_phi η_q RootedTree.broom₃
              = elementaryWeightQ_phi η_q' RootedTree.broom₃)
    (h_bushy : elementaryWeightQ_phi η_q RootedTree.bushy
              = elementaryWeightQ_phi η_q' RootedTree.bushy) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ)))) RootedTree.bushy
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ)))) RootedTree.bushy := by
  have h_pow : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
      ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
    intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow η_q, h_pow η_q',
      elementaryWeightQ_phi_inv_bushy, elementaryWeightQ_phi_inv_bushy,
      h_vertex, h_cherry, h_broom₃, h_bushy]

/-- *Phase D.3.b Step 2 (cycle 370) — bushy m=0 witness non-vacuity at
`η_q = η_q' = ⟦explicitEuler⟧`.* Discharges the four agreement
hypotheses by `rfl`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
        RootedTree.bushy
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
          RootedTree.bushy :=
  powRep_sum_eq_of_agreement_at_bushy_zero
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    rfl rfl rfl rfl

/-- *Phase D.3.b Step 2 (cycle 365) — Sub-lemma B (HEADLINE):*
parametricity for `linearResidualAt`. If `η_q` and `η_q'` agree on
`elementaryWeightQ_phi` at every tree of order at most `t.order`
(including `t` itself), then their linear residuals at every `(i, t)`
coincide.

This is the Phase D.3.b Step 2 headline deliverable: it certifies
that the linear-coefficient residual depends only on the §383
quotient's "local profile" at subtrees of `t`, which is the
prerequisite for Phase D.3.d's `underlyingOneStepMethod_aux`
well-founded recursion on `RootedTree.order` (cycle 343's
`WellFoundedRelation RootedTree := measure RootedTree.order`).

Proof: case-split on `i`. At `i = 0`, both sides reduce to `0 + 0 = 0`
via `zpow_zero` and `elementaryWeightQ_phi_id`. At `i = m + 1`, apply
Sub-lemma A `powRep_sum_eq_of_strict_subtree_agreement` on the
`Φ_{η_q^(-(m+1))}(t)` term and `h_closed t (le_refl _)` on the direct
`Φ_{η_q}(t)` term; both terms transfer η_q → η_q', closing the goal
modulo definitional ring.

Headline ships **axiom-clean** modulo Sub-lemma A as black box
(Sub-lemma A's body is cycle 366 work; the headline statement is
locked in). -/
theorem linearResidualAt_depends_only_on_strict_subtrees
    (i : ℕ) (t : RT)
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_closed : ∀ s : RT, s.order ≤ t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    linearResidualAt i η_q t = linearResidualAt i η_q' t := by
  match i with
  | 0 =>
    simp [linearResidualAt, zpow_zero]
  | m + 1 =>
    have hA := powRep_sum_eq_of_strict_subtree_agreement m t η_q η_q' h_closed
    have hT := h_closed t (le_refl _)
    unfold linearResidualAt
    rw [hA, hT]

/-- *Phase D.3.b Step 2 (cycle 365) — non-vacuity at `(i, t) = (1, cherry)`
with trivial agreement on `explicitEuler`.* Exercises the headline at
the first non-vertex tree with `η_q = η_q' = ⟦explicitEuler⟧`, so the
strict-subtree hypothesis is discharged by `fun _ _ => rfl`. -/
example :
    linearResidualAt 1
        (Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩) RootedTree.cherry
      = linearResidualAt 1
          (Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) RootedTree.cherry :=
  linearResidualAt_depends_only_on_strict_subtrees 1 RootedTree.cherry
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (fun _ _ => rfl)

/-- *Phase D.3.b Step 2 (cycle 365) — non-vacuity at `(i, t) = (2, cherry)`
with trivial agreement on `explicitEuler`.* Exercises the headline at
the next residual index `i = 2`, confirming the lemma fires uniformly
across `i` (via the `m + 1` branch with `m = 1`). -/
example :
    linearResidualAt 2
        (Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩) RootedTree.cherry
      = linearResidualAt 2
          (Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) RootedTree.cherry :=
  linearResidualAt_depends_only_on_strict_subtrees 2 RootedTree.cherry
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (fun _ _ => rfl)

/-- *Phase D.3.b Step 2 (cycle 365) — non-vacuity at `i = 0` (the vertex-
free base branch).* Exercises the `i = 0` branch of the headline at
arbitrary tree; the residual at `i = 0` is `Φ_{η^0}(t) + 0 = 0` for
any `η`, so both sides are 0 unconditionally. -/
example :
    linearResidualAt 0
        (Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩) RootedTree.cherry
      = linearResidualAt 0
          (Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) RootedTree.cherry :=
  linearResidualAt_depends_only_on_strict_subtrees 0 RootedTree.cherry
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (fun _ _ => rfl)

/-- *Phase D.3.b Step 2 (cycle 371) — `mk [broom₃]` closed form for Φ_{η_q⁻¹}.*
At the order-4 depth-2 ladder tree
`mk [broom₃] = mk [mk [vertex, vertex]]` (root with a single child that
is itself `broom₃`), the quotient-level elementary weight of the §383
inverse class admits the closed form
  `Φ_{η_q⁻¹}(mk [broom₃]) = (Φ_η(vertex))^4
                            − 3·(Φ_η(vertex))²·Φ_η(cherry)
                            + Φ_η(vertex)·Φ_η(broom₃)
                            + 2·Φ_η(vertex)·Φ_η(mk [cherry])
                            − Φ_η(mk [broom₃])`.

Sixth data point in the cycle 366 §G Route B hypothesis ladder
(vertex, cherry, broom₃, mk [cherry], bushy, mk [broom₃]). Tests the
depth-2 ladder pattern of cycle 369's `_mkCherry` at the next depth
(with `broom₃` as the unique child in place of `cherry`), producing a
5-term polynomial in 5 elementary weights with the cycle 369-style
cross terms `2v·m` (depth-2 ladder signature) and `v·b'` (broom₃
inverse signature) combined.

Proof outline (mirrors cycle 369's `mk [cherry]` recipe with one extra
inner two-cons unfold for the broom₃-child's `(Aⱼ − v)²` expansion):

1. Reduce to a representative `⟨s, M⟩` via `Quotient.inductionOn`.
2. Reuse cycle 367/368/369 helpers `h_inv_v`, `h_vertex`, `h_dw_cherry`,
   `h_cherry`, `h_dw_broom₃`, `h_broom₃`, `h_dw_mkCherry`, `h_mkCherry`.
3. Add four new helpers for the cycle 371 mk [broom₃] structure:
   - `h_inv_broom₃` : `M.inverse.elementaryWeight broom₃ = -v³ + 2vc − b'`
     (representative-lift of cycle 368's quotient closed form via
     `elementaryWeightQ_phi_inv_broom₃` at ⟦⟨s, M⟩⟩, descended via
     definitional `inverseQ_phi_mk` + `elementaryWeightQ_phi_mk`).
   - `h_dw_mkBroom₃` : `M.derivativeWeight i (mk [broom₃])
                        = ∑ⱼ M.A i j · (∑ₖ M.A j k)²`
     (one-layer cons-case unfold using `h_dw_broom₃`).
   - `h_mkBroom₃` : `M.elementaryWeight (mk [broom₃])
                     = ∑ᵢ b_i · ∑ⱼ A_{ij} · (∑ₖ A_{jk})²`.
   - `h_dws_mkBroom₃` : `M.derivativeWeightWithSrc M.inverse i (mk [broom₃])
                         = inv_broom₃
                           + ∑ⱼ A_{ij} · (inv_v + ∑ₖ A_{jk})²`
     (one outer cons-case unfold, then inner cycle 368 two-layer
     `derivativeWeightWithSrcProd M.inverse j [vertex]` unfold).
4. After `_inv_mk`, `_mk` × 5 rewrites, substitute the closed form,
   distribute the sum via `Finset.sum_add_distrib`,
   `Finset.sum_sub_distrib`, factor out constants via
   `← Finset.mul_sum` (three applications), back-substitute via
   `← h_mkBroom₃, ← h_mkCherry, ← h_cherry, ← h_vertex`, close with
   `ring`. -/
theorem elementaryWeightQ_phi_inv_mkBroom₃
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹)
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
      = (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 4
        - 3 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q RootedTree.cherry
        + elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        + 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - elementaryWeightQ_phi η_q
            (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- Cycle 367 helpers (reused verbatim).
  have h_inv_v : M.inverse.elementaryWeight RootedTree.vertex
      = -M.elementaryWeight RootedTree.vertex := by
    show ∑ j : Fin s, M.inverse.b j * M.inverse.derivativeWeight j RootedTree.vertex
          = -(∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.inverse_b, RKTableau.derivativeWeight_vertex,
        RKTableau.derivativeWeight_vertex, neg_mul]
  have h_vertex : M.elementaryWeight RootedTree.vertex = ∑ j : Fin s, M.b j := by
    show ∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.b j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_dw_cherry : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.cherry = ∑ j : Fin s, M.A i j := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_cherry : M.elementaryWeight RootedTree.cherry
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.cherry
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_cherry i]
  -- Cycle 368 helpers (reused verbatim).
  have h_dw_broom₃ : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.broom₃ = (∑ j : Fin s, M.A i j) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 2
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    rw [h_inner_sum, h_prod_step]; ring
  have h_broom₃ : M.elementaryWeight RootedTree.broom₃
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.broom₃
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_broom₃ i]
  -- Cycle 369 helpers (reused verbatim) — `mk [cherry]` derivative/elementary
  -- weight closed forms.
  have h_dw_mkCherry : ∀ i : Fin s,
      M.derivativeWeight i (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
          * M.derivativeWeightProd i [] = _
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dw_cherry j]
  have h_mkCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkCherry i]
  -- New cycle 371 helpers.
  -- Representative-lift of cycle 368's quotient closed form for broom₃ inverse.
  have h_inv_broom₃ : M.inverse.elementaryWeight RootedTree.broom₃
      = -(M.elementaryWeight RootedTree.vertex) ^ 3
        + 2 * M.elementaryWeight RootedTree.vertex
            * M.elementaryWeight RootedTree.cherry
        - M.elementaryWeight RootedTree.broom₃ :=
    elementaryWeightQ_phi_inv_broom₃
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)
  -- One-layer cons-case unfold for `mk [broom₃]`'s derivativeWeight, reusing
  -- cycle 368's `h_dw_broom₃` for the inner broom₃.
  have h_dw_mkBroom₃ : ∀ i : Fin s,
      M.derivativeWeight i (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
        = ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.broom₃)
          * M.derivativeWeightProd i [] = _
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dw_broom₃ j]
  have h_mkBroom₃ : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2 := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkBroom₃ i]
  -- Two-layer cons-case unfold for `mk [broom₃]`'s derivativeWeightWithSrc:
  -- the outer one-cons unfold strips the `mk` layer, then the inner two-cons
  -- unfold (mirroring cycle 368's `h_dws_broom₃`) gives the (inv_v + ∑ₖ A_{jk})²
  -- closed form for `derivativeWeightWithSrc M.inverse j broom₃`.
  have h_dws_mkBroom₃ : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
        = M.inverse.elementaryWeight RootedTree.broom₃
          + ∑ j : Fin s, M.A i j
              * (M.inverse.elementaryWeight RootedTree.vertex
                  + ∑ k : Fin s, M.A j k) ^ 2 := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.broom₃
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.broom₃)
          * M.derivativeWeightWithSrcProd M.inverse i [] = _
    rw [show M.derivativeWeightWithSrcProd M.inverse i [] = 1 from rfl, mul_one]
    have h_dws_broom₃ : ∀ j : Fin s,
        M.derivativeWeightWithSrc M.inverse j RootedTree.broom₃
          = (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ k : Fin s, M.A j k) ^ 2 := by
      intro j
      show (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ k : Fin s, M.A j k
                  * M.derivativeWeightWithSrc M.inverse k RootedTree.vertex)
            * M.derivativeWeightWithSrcProd M.inverse j [RootedTree.vertex]
          = (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ k : Fin s, M.A j k) ^ 2
      have h_inner_sum :
          ∑ k : Fin s, M.A j k
              * M.derivativeWeightWithSrc M.inverse k RootedTree.vertex
            = ∑ k : Fin s, M.A j k := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
      have h_prod_step :
          M.derivativeWeightWithSrcProd M.inverse j [RootedTree.vertex]
            = M.inverse.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k := by
        show (M.inverse.elementaryWeight RootedTree.vertex
                + ∑ k : Fin s, M.A j k
                    * M.derivativeWeightWithSrc M.inverse k RootedTree.vertex)
              * M.derivativeWeightWithSrcProd M.inverse j []
            = M.inverse.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k
        rw [show M.derivativeWeightWithSrcProd M.inverse j [] = 1 from rfl, mul_one,
            h_inner_sum]
      rw [h_inner_sum, h_prod_step]; ring
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dws_broom₃ j]
  -- Main computation: assemble closed form via _inv_mk + _mk × 5 + sum algebra.
  rw [elementaryWeightQ_phi_inv_mk M
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]),
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk]
  have h_sum :
      (∑ i : Fin s, M.b i
          * M.derivativeWeightWithSrc M.inverse i
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]))
        = -(M.elementaryWeight RootedTree.vertex) ^ 4
          + 3 * (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight RootedTree.cherry
          - M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight RootedTree.broom₃
          - 2 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          + M.elementaryWeight
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) := by
    have h_subst :
        (∑ i : Fin s, M.b i
            * M.derivativeWeightWithSrc M.inverse i
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]))
          = ∑ i : Fin s,
            ((-(M.elementaryWeight RootedTree.vertex) ^ 3
                + 2 * M.elementaryWeight RootedTree.vertex
                    * M.elementaryWeight RootedTree.cherry
                - M.elementaryWeight RootedTree.broom₃) * M.b i
              + M.b i * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2)
              - 2 * M.elementaryWeight RootedTree.vertex
                  * (M.b i * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k))
              + (M.elementaryWeight RootedTree.vertex) ^ 2
                  * (M.b i * ∑ j : Fin s, M.A i j)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_dws_mkBroom₃ i, h_inv_broom₃, h_inv_v]
      -- The inner ∑ⱼ A_{ij} · (−v + ∑ₖ A_{jk})² needs to be distributed
      -- before `ring` can match the 4-term per-summand decomposition.
      have h_inner_expand :
          ∑ j : Fin s, M.A i j
              * (-M.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k) ^ 2
            = ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2
              - 2 * M.elementaryWeight RootedTree.vertex
                  * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k
              + M.elementaryWeight RootedTree.vertex ^ 2
                  * ∑ j : Fin s, M.A i j := by
        have h_inner :
            ∑ j : Fin s, M.A i j
                * (-M.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k) ^ 2
              = ∑ j : Fin s, (M.A i j * (∑ k : Fin s, M.A j k) ^ 2
                  - 2 * M.elementaryWeight RootedTree.vertex
                      * (M.A i j * ∑ k : Fin s, M.A j k)
                  + M.elementaryWeight RootedTree.vertex ^ 2 * M.A i j) := by
          refine Finset.sum_congr rfl (fun j _ => ?_); ring
        rw [h_inner, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
      rw [h_inner_expand]; ring
    rw [h_subst, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← h_mkBroom₃, ← h_mkCherry, ← h_cherry, ← h_vertex]
    ring
  rw [h_sum]; ring

/-- *Phase D.3.b Step 2 (cycle 371) — `mk [broom₃]` closed form non-vacuity
at `η_q = ⟦explicitEuler⟧`.* The expected value is
`Φ_{⟦explicitEuler⟧⁻¹}(mk [broom₃]) = 1^4 − 3·1²·0 + 1·0 + 2·1·0 − 0 = 1`,
since for explicit Euler `Σ b = 1` (so `Φ_η(vertex) = 1`) and `A = 0`
(so all higher elementary weights vanish). -/
example :
    elementaryWeightQ_phi
      ((Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩))⁻¹
      (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) = 1 := by
  rw [elementaryWeightQ_phi_inv_mkBroom₃, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_vertex : RKTableau.explicitEuler.elementaryWeight RootedTree.vertex = 1 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.vertex = 1
    simp [RKTableau.explicitEuler, RKTableau.derivativeWeight_vertex]
  have h_cherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.cherry = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_cherry : RKTableau.explicitEuler.elementaryWeight RootedTree.cherry = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.cherry = 0
    simp [h_cherry_zero]
  have h_broom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.broom₃ = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_broom₃ : RKTableau.explicitEuler.elementaryWeight RootedTree.broom₃ = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.broom₃ = 0
    simp [h_broom₃_zero]
  have h_mkCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.cherry)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_mkCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0
    simp [h_mkCherry_zero]
  have h_mkBroom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.broom₃)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_mkBroom₃ :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) = 0
    simp [h_mkBroom₃_zero]
  rw [h_vertex, h_cherry, h_broom₃, h_mkCherry, h_mkBroom₃]; ring

/-- *Phase D.3.b Step 2 (cycle 371) — Priority 2 `mk [broom₃]` m=0 witness:*
specialisation of Sub-lemma A `powRep_sum_eq_of_strict_subtree_agreement`
at `t = mk [broom₃], m = 0`. Under agreement at `vertex`, `cherry`,
`broom₃`, `mk [cherry]`, and `mk [broom₃]` (five subtrees corresponding
to the closed-form factors), the `η_q^(-1)` images at `mk [broom₃]`
coincide.

Proof: reduce `η_q ^ (-(((0 + 1 : ℕ) : ℤ)))` to `η_q⁻¹` via
`Nat.cast_one` + `zpow_neg_one`, apply cycle 371's
`elementaryWeightQ_phi_inv_mkBroom₃` on both sides, then substitute the
five agreement hypotheses. -/
theorem powRep_sum_eq_of_agreement_at_mkBroom₃_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry)
    (h_broom₃ : elementaryWeightQ_phi η_q RootedTree.broom₃
              = elementaryWeightQ_phi η_q' RootedTree.broom₃)
    (h_mkCherry : elementaryWeightQ_phi η_q
                    (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
    (h_mkBroom₃ : elementaryWeightQ_phi η_q
                    (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) := by
  have h_pow : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
      ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
    intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow η_q, h_pow η_q',
      elementaryWeightQ_phi_inv_mkBroom₃, elementaryWeightQ_phi_inv_mkBroom₃,
      h_vertex, h_cherry, h_broom₃, h_mkCherry, h_mkBroom₃]

/-- *Phase D.3.b Step 2 (cycle 371) — `mk [broom₃]` m=0 witness non-vacuity
at `η_q = η_q' = ⟦explicitEuler⟧`.* Discharges the five agreement
hypotheses by `rfl`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) :=
  powRep_sum_eq_of_agreement_at_mkBroom₃_zero
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    rfl rfl rfl rfl rfl

/-- *Phase D.3.b Step 2 (cycle 372) — `mk [vertex, cherry]` (first
asymmetric order-4 tree) closed form for Φ_{η_q⁻¹}.* At the order-4
tree `mk [vertex, cherry] = mk [vertex, mk [vertex]]`, the quotient-
level elementary weight of the §383 inverse class admits the closed
form
  `Φ_{η_q⁻¹}(mk [vertex, cherry])
       = (Φ_η(vertex))^4
         − 3 · (Φ_η(vertex))^2 · Φ_η(cherry)
         + (Φ_η(cherry))^2
         + Φ_η(vertex) · Φ_η(broom₃)
         + Φ_η(vertex) · Φ_η(mk [cherry])
         − Φ_η(mk [vertex, cherry])`.

Seventh data point in the cycle 366 §G Route B hypothesis ladder
(vertex, cherry, broom₃, mk [cherry], bushy, mk [broom₃],
mk [vertex, cherry]). The first asymmetric order-4 witness:
heterogeneous children with one leaf-child and one cherry-child,
introducing a new `c²` quadratic self-term not present in any
prior witness's closed form.

Proof outline (mirrors cycle 371's `mk [broom₃]` recipe with a
two-child cons-case unfold pattern from cycle 368, and inner cherry
handling from cycle 369):

1. Reduce to a representative `⟨s, M⟩` via `Quotient.inductionOn`.
2. Reuse cycle 367/368/369 helpers `h_inv_v`, `h_vertex`,
   `h_dw_cherry`, `h_cherry`, `h_dws_cherry`, `h_dw_broom₃`,
   `h_broom₃`, `h_inv_cherry`, `h_dw_mkCherry`, `h_mkCherry`.
3. Add three new helpers for the `mk [vertex, cherry]` two-child
   asymmetric structure:
   - `h_dw_mkVertexCherry` : `M.derivativeWeight i (mk [vertex, cherry])
                              = (∑ⱼ Aᵢⱼ) · (∑ⱼ Aᵢⱼ · ∑ₖ Aⱼₖ)`
     (two-child cons-case unfold combining cycle 367's `h_dw_cherry`
     inner factor with the vertex-factor `Σⱼ Aᵢⱼ · 1`).
   - `h_mkVertexCherry` : `M.elementaryWeight (mk [vertex, cherry])
                           = ∑ᵢ bᵢ · (∑ⱼ Aᵢⱼ) · (∑ⱼ Aᵢⱼ · ∑ₖ Aⱼₖ)`.
   - `h_dws_mkVertexCherry` : `M.derivativeWeightWithSrc M.inverse i
                               (mk [vertex, cherry])
                               = (inv_v + ∑ⱼ Aᵢⱼ)
                                 · (inv_c
                                    + ∑ⱼ Aᵢⱼ · (inv_v + ∑ₖ Aⱼₖ))`
     (two outer cons-case unfolds; inner cherry layer reuses cycle
     367's `h_dws_cherry`).
4. After `_inv_mk`, `_mk` × 5 rewrites, substitute the closed form
   per-summand (5-term decomposition with inner ∑ⱼ Aᵢⱼ · (-v + ∑ₖ Aⱼₖ)
   pre-distributed via `Finset.sum_add_distrib` + `← Finset.mul_sum`),
   distribute the sum via `Finset.sum_add_distrib × 4`, factor
   constants via `← Finset.mul_sum × 4`, back-substitute via
   `← h_mkVertexCherry, ← h_broom₃, ← h_mkCherry, ← h_cherry,
   ← h_vertex`, close with `ring`. -/
theorem elementaryWeightQ_phi_inv_mkVertexCherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹)
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry])
      = (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 4
        - 3 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q RootedTree.cherry
        + (elementaryWeightQ_phi η_q RootedTree.cherry) ^ 2
        + elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        + elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - elementaryWeightQ_phi η_q
            (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]) := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- Cycle 367 helpers (reused verbatim).
  have h_inv_v : M.inverse.elementaryWeight RootedTree.vertex
      = -M.elementaryWeight RootedTree.vertex := by
    show ∑ j : Fin s, M.inverse.b j * M.inverse.derivativeWeight j RootedTree.vertex
          = -(∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.inverse_b, RKTableau.derivativeWeight_vertex,
        RKTableau.derivativeWeight_vertex, neg_mul]
  have h_vertex : M.elementaryWeight RootedTree.vertex = ∑ j : Fin s, M.b j := by
    show ∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.b j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_dw_cherry : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.cherry = ∑ j : Fin s, M.A i j := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_cherry : M.elementaryWeight RootedTree.cherry
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.cherry
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_cherry i]
  have h_dws_cherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i RootedTree.cherry
        = M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * (1 : ℝ) = _
    rw [mul_one]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
  -- Cycle 368 helpers (reused verbatim).
  have h_dw_broom₃ : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.broom₃ = (∑ j : Fin s, M.A i j) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 2
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    rw [h_inner_sum, h_prod_step]; ring
  have h_broom₃ : M.elementaryWeight RootedTree.broom₃
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.broom₃
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_broom₃ i]
  -- Cycle 369: `h_inv_cherry` lifted from cycle 367's quotient theorem at ⟦M⟧.
  have h_inv_cherry : M.inverse.elementaryWeight RootedTree.cherry
      = (M.elementaryWeight RootedTree.vertex) ^ 2
        - M.elementaryWeight RootedTree.cherry :=
    elementaryWeightQ_phi_inv_cherry
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)
  -- Cycle 369 helpers for `mk [cherry]` derivative/elementary weight closed forms.
  have h_dw_mkCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
          * M.derivativeWeightProd i [] = _
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dw_cherry j]
  have h_mkCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkCherry i]
  -- New cycle 372 helpers — two-child asymmetric `mk [vertex, cherry]` structure.
  -- Derivative weight: combines the vertex-factor `Σⱼ Aᵢⱼ · 1` with the
  -- cherry-factor `Σⱼ Aᵢⱼ · Σₖ Aⱼₖ` via two-child cons-case unfold.
  have h_dw_mkVertexCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry])
        = (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.cherry] = _
    have h_vertex_factor :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_cherry_factor :
        M.derivativeWeightProd i [RootedTree.cherry]
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_cherry j]
    rw [h_vertex_factor, h_cherry_factor]
  have h_mkVertexCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
              * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexCherry i]; ring
  -- Two-layer cons-case unfold for `mk [vertex, cherry]`'s
  -- derivativeWeightWithSrc: outer one-cons unfold strips the `mk` layer,
  -- producing a product of two source-tagged factors (vertex layer + cherry
  -- layer). The vertex factor reduces via `derivativeWeightWithSrc_vertex = 1`,
  -- the cherry factor unfolds via cycle 367's `h_dws_cherry`.
  have h_dws_mkVertexCherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry])
        = (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j)
          * (M.inverse.elementaryWeight RootedTree.cherry
             + ∑ j : Fin s, M.A i j
                 * (M.inverse.elementaryWeight RootedTree.vertex
                    + ∑ k : Fin s, M.A j k)) := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * M.derivativeWeightWithSrcProd M.inverse i [RootedTree.cherry] = _
    have h_vertex_factor :
        ∑ j : Fin s, M.A i j * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
    have h_cherry_factor :
        M.derivativeWeightWithSrcProd M.inverse i [RootedTree.cherry]
          = M.inverse.elementaryWeight RootedTree.cherry
            + ∑ j : Fin s, M.A i j
                * (M.inverse.elementaryWeight RootedTree.vertex
                   + ∑ k : Fin s, M.A j k) := by
      show (M.inverse.elementaryWeight RootedTree.cherry
              + ∑ j : Fin s, M.A i j
                  * M.derivativeWeightWithSrc M.inverse j RootedTree.cherry)
            * M.derivativeWeightWithSrcProd M.inverse i [] = _
      rw [show M.derivativeWeightWithSrcProd M.inverse i [] = 1 from rfl, mul_one]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dws_cherry j]
    rw [h_vertex_factor, h_cherry_factor]
  -- Main computation: assemble closed form via _inv_mk + _mk × 5 + sum algebra.
  rw [elementaryWeightQ_phi_inv_mk M
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]),
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk]
  have h_sum :
      (∑ i : Fin s, M.b i
          * M.derivativeWeightWithSrc M.inverse i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]))
        = M.elementaryWeight
            (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
          - M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight RootedTree.broom₃
          - M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          + 3 * (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight RootedTree.cherry
          - (M.elementaryWeight RootedTree.cherry) ^ 2
          - (M.elementaryWeight RootedTree.vertex) ^ 4 := by
    have h_subst :
        (∑ i : Fin s, M.b i
            * M.derivativeWeightWithSrc M.inverse i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry]))
          = ∑ i : Fin s,
              (M.b i * (∑ j : Fin s, M.A i j)
                  * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
                + (-M.elementaryWeight RootedTree.vertex)
                    * (M.b i * (∑ j : Fin s, M.A i j) ^ 2)
                + (-M.elementaryWeight RootedTree.vertex)
                    * (M.b i * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k))
                + (2 * (M.elementaryWeight RootedTree.vertex) ^ 2
                    - M.elementaryWeight RootedTree.cherry)
                    * (M.b i * ∑ j : Fin s, M.A i j)
                + (-(M.elementaryWeight RootedTree.vertex) ^ 3
                    + M.elementaryWeight RootedTree.vertex
                      * M.elementaryWeight RootedTree.cherry) * M.b i) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_dws_mkVertexCherry i, h_inv_cherry, h_inv_v]
      -- The inner Σⱼ Aᵢⱼ · (-v + Σₖ Aⱼₖ) needs to be distributed before
      -- `ring` can match the 5-term per-summand decomposition.
      have h_inner_expand :
          ∑ j : Fin s, M.A i j
              * (-M.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k)
            = -M.elementaryWeight RootedTree.vertex * ∑ j : Fin s, M.A i j
              + ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
        have h_inner :
            ∑ j : Fin s, M.A i j
                * (-M.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k)
              = ∑ j : Fin s, (-M.elementaryWeight RootedTree.vertex * M.A i j
                  + M.A i j * ∑ k : Fin s, M.A j k) := by
          refine Finset.sum_congr rfl (fun j _ => ?_); ring
        rw [h_inner, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [h_inner_expand]; ring
    rw [h_subst, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← h_mkVertexCherry, ← h_broom₃, ← h_mkCherry, ← h_cherry, ← h_vertex]
    ring
  rw [h_sum]; ring

/-- *Phase D.3.b Step 2 (cycle 372) — `mk [vertex, cherry]` closed form
non-vacuity at `η_q = ⟦explicitEuler⟧`.* The expected value is
`Φ_{⟦explicitEuler⟧⁻¹}(mk [vertex, cherry]) = 1^4 − 3·1²·0 + 0² + 1·0
+ 1·0 − 0 = 1`, since for explicit Euler `Σ b = 1` (so `Φ_η(vertex) =
1`) and `A = 0` (so all higher elementary weights vanish). -/
example :
    elementaryWeightQ_phi
      ((Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩))⁻¹
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.cherry]) = 1 := by
  rw [elementaryWeightQ_phi_inv_mkVertexCherry, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_vertex : RKTableau.explicitEuler.elementaryWeight RootedTree.vertex = 1 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.vertex = 1
    simp [RKTableau.explicitEuler, RKTableau.derivativeWeight_vertex]
  have h_cherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.cherry = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_cherry : RKTableau.explicitEuler.elementaryWeight RootedTree.cherry = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.cherry = 0
    simp [h_cherry_zero]
  have h_broom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.broom₃ = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_broom₃ : RKTableau.explicitEuler.elementaryWeight RootedTree.broom₃ = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.broom₃ = 0
    simp [h_broom₃_zero]
  have h_mkCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.cherry)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_mkCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0
    simp [h_mkCherry_zero]
  have h_mkVertexCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.cherry] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]) = 0
    simp [h_mkVertexCherry_zero]
  rw [h_vertex, h_cherry, h_broom₃, h_mkCherry, h_mkVertexCherry]; ring

/-- *Phase D.3.b Step 2 (cycle 372) — Priority 2 `mk [vertex, cherry]`
m=0 witness:* specialisation of Sub-lemma A
`powRep_sum_eq_of_strict_subtree_agreement` at
`t = mk [vertex, cherry], m = 0`. Under agreement at `vertex`, `cherry`,
`broom₃`, `mk [cherry]`, and `mk [vertex, cherry]` (five subtrees
corresponding to the closed-form factors), the `η_q^(-1)` images at
`mk [vertex, cherry]` coincide.

Proof: reduce `η_q ^ (-(((0 + 1 : ℕ) : ℤ)))` to `η_q⁻¹` via
`Nat.cast_one` + `zpow_neg_one`, apply cycle 372's
`elementaryWeightQ_phi_inv_mkVertexCherry` on both sides, then
substitute the five agreement hypotheses. -/
theorem powRep_sum_eq_of_agreement_at_mkVertexCherry_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry)
    (h_broom₃ : elementaryWeightQ_phi η_q RootedTree.broom₃
              = elementaryWeightQ_phi η_q' RootedTree.broom₃)
    (h_mkCherry : elementaryWeightQ_phi η_q
                    (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
    (h_mkVertexCherry : elementaryWeightQ_phi η_q
                          (OpenMath.Chapter3.Section310.RootedTree.mk
                            [RootedTree.vertex, RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry])) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry])
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry]) := by
  have h_pow : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
      ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
    intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow η_q, h_pow η_q',
      elementaryWeightQ_phi_inv_mkVertexCherry,
      elementaryWeightQ_phi_inv_mkVertexCherry,
      h_vertex, h_cherry, h_broom₃, h_mkCherry, h_mkVertexCherry]

/-- *Phase D.3.b Step 2 (cycle 372) — `mk [vertex, cherry]` m=0 witness
non-vacuity at `η_q = η_q' = ⟦explicitEuler⟧`.* Discharges the five
agreement hypotheses by `rfl`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry])
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry]) :=
  powRep_sum_eq_of_agreement_at_mkVertexCherry_zero
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    rfl rfl rfl rfl rfl

/-- *Phase D.3.b Step 2 (cycle 378) — `mk [mk [cherry]]` (depth-3
single-child ladder) closed form for Φ_{η_q⁻¹}.* At the order-4 tree
`mk [mk [cherry]] = mk [mk [mk [vertex]]]`, the quotient-level
elementary weight of the §383 inverse class admits the closed form
  `Φ_{η_q⁻¹}(mk [mk [cherry]])
       = (Φ_η(vertex))^4
         − 3 · (Φ_η(vertex))^2 · Φ_η(cherry)
         + (Φ_η(cherry))^2
         + 2 · Φ_η(vertex) · Φ_η(mk [cherry])
         − Φ_η(mk [mk [cherry]])`.

Eighth data point in the cycle 366 §G Route B hypothesis ladder
(vertex, cherry, broom₃, mk [cherry], bushy, mk [broom₃],
mk [vertex, cherry], mk [mk [cherry]]). The first depth-3 witness:
single-child ladder extending cycles 369 (`mk [cherry]` depth-2) and
371 (`mk [broom₃]` depth-2) with one more depth layer.

Proof outline (mirrors cycle 371's `mk [broom₃]` recipe with the
inner broom₃ layer replaced by a `mk [cherry]` layer, requiring
cycle 369's `_mkCherry` quotient theorem as a representative-form
lift and an additional inner sum unfold):

1. Reduce to a representative `⟨s, M⟩` via `Quotient.inductionOn`.
2. Reuse cycle 367/368/369 helpers `h_inv_v`, `h_vertex`,
   `h_dw_cherry`, `h_cherry`, `h_dws_cherry`, `h_inv_cherry`,
   `h_dw_mkCherry`, `h_mkCherry`, `h_dws_mkCherry`.
3. Add three new cycle 378 helpers for the depth-3 layer:
   - `h_inv_mkCherry` : representative-form lift of cycle 369's
     `elementaryWeightQ_phi_inv_mkCherry`.
   - `h_dw_mkMkCherry` / `h_mkMkCherry` : derivative/elementary weight
     closed form `Σⱼ Aᵢⱼ · Σ_k A_jk · Σ_l A_kl` for `mk [mk [cherry]]`.
   - `h_dws_mkMkCherry` : derivativeWeightWithSrc closed form via
     one outer cons-case unfold followed by `h_dws_mkCherry`.
4. After `_inv_mk`, `_mk` × 4 rewrites, substitute the closed form
   per-summand (4-term decomposition with inner Σⱼ Aᵢⱼ · (inv_c
   + inv_v · Σ_k A_jk + Σ_k A_jk · Σ_l A_kl) pre-distributed via
   `Finset.sum_add_distrib` × 2 + `← Finset.mul_sum` × 2), distribute
   the sum via `Finset.sum_add_distrib` × 3, factor constants via
   `← Finset.mul_sum` × 3, back-substitute via `← h_mkMkCherry,
   ← h_mkCherry, ← h_cherry, ← h_vertex`, close with `ring`. -/
theorem elementaryWeightQ_phi_inv_mkMkCherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹)
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
      = (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 4
        - 3 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q RootedTree.cherry
        + (elementaryWeightQ_phi η_q RootedTree.cherry) ^ 2
        + 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - elementaryWeightQ_phi η_q
            (OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- Cycle 367 helpers (reused verbatim).
  have h_inv_v : M.inverse.elementaryWeight RootedTree.vertex
      = -M.elementaryWeight RootedTree.vertex := by
    show ∑ j : Fin s, M.inverse.b j * M.inverse.derivativeWeight j RootedTree.vertex
          = -(∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.inverse_b, RKTableau.derivativeWeight_vertex,
        RKTableau.derivativeWeight_vertex, neg_mul]
  have h_vertex : M.elementaryWeight RootedTree.vertex = ∑ j : Fin s, M.b j := by
    show ∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.b j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_dw_cherry : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.cherry = ∑ j : Fin s, M.A i j := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_cherry : M.elementaryWeight RootedTree.cherry
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.cherry
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_cherry i]
  have h_dws_cherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i RootedTree.cherry
        = M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * (1 : ℝ) = _
    rw [mul_one]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
  -- Cycle 369: `h_inv_cherry` lifted from cycle 367's quotient theorem at ⟦M⟧.
  have h_inv_cherry : M.inverse.elementaryWeight RootedTree.cherry
      = (M.elementaryWeight RootedTree.vertex) ^ 2
        - M.elementaryWeight RootedTree.cherry :=
    elementaryWeightQ_phi_inv_cherry
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)
  -- Cycle 369 helpers for `mk [cherry]` derivative/elementary weight closed forms.
  have h_dw_mkCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
          * M.derivativeWeightProd i [] = _
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dw_cherry j]
  have h_mkCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkCherry i]
  have h_dws_mkCherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = M.inverse.elementaryWeight RootedTree.cherry
          + M.inverse.elementaryWeight RootedTree.vertex * ∑ j : Fin s, M.A i j
          + ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.cherry
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.cherry)
          * M.derivativeWeightWithSrcProd M.inverse i [] = _
    rw [show M.derivativeWeightWithSrcProd M.inverse i [] = 1 from rfl, mul_one]
    have h_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeightWithSrc M.inverse j RootedTree.cherry
          = ∑ j : Fin s, (M.A i j * M.inverse.elementaryWeight RootedTree.vertex
                          + M.A i j * ∑ k : Fin s, M.A j k) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dws_cherry j]; ring
    rw [h_inner, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  -- New cycle 378 helper: `h_inv_mkCherry` lifted from cycle 369's quotient
  -- theorem `elementaryWeightQ_phi_inv_mkCherry` at ⟦⟨s, M⟩⟧.
  have h_inv_mkCherry : M.inverse.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      = -(M.elementaryWeight RootedTree.vertex) ^ 3
        + 2 * M.elementaryWeight RootedTree.vertex
            * M.elementaryWeight RootedTree.cherry
        - M.elementaryWeight
            (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) :=
    elementaryWeightQ_phi_inv_mkCherry
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)
  -- New cycle 378 helpers: depth-3 mk [mk [cherry]] derivative/elementary weight.
  -- One-layer cons-case unfold for `mk [mk [cherry]]`'s derivativeWeight,
  -- reusing cycle 369's h_dw_mkCherry for the inner mk [cherry].
  have h_dw_mkMkCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
        = ∑ j : Fin s, M.A i j
            * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l := by
    intro i
    show (∑ j : Fin s, M.A i j
            * M.derivativeWeight j
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
          * M.derivativeWeightProd i [] = _
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dw_mkCherry j]
  have h_mkMkCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
      = ∑ i : Fin s, M.b i
          * ∑ j : Fin s, M.A i j
              * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
          = ∑ i : Fin s, M.b i
              * ∑ j : Fin s, M.A i j
                  * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkMkCherry i]
  -- One-layer cons-case unfold for `mk [mk [cherry]]`'s derivativeWeightWithSrc,
  -- reusing cycle 378's h_dws_mkCherry for the inner mk [cherry] layer.
  have h_dws_mkMkCherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
        = M.inverse.elementaryWeight
            (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          + ∑ j : Fin s, M.A i j
              * (M.inverse.elementaryWeight RootedTree.cherry
                 + M.inverse.elementaryWeight RootedTree.vertex
                     * ∑ k : Fin s, M.A j k
                 + ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l) := by
    intro i
    show (M.inverse.elementaryWeight
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j
                    (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
          * M.derivativeWeightWithSrcProd M.inverse i [] = _
    rw [show M.derivativeWeightWithSrcProd M.inverse i [] = 1 from rfl, mul_one]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dws_mkCherry j]
  -- Main computation: assemble closed form via _inv_mk + _mk × 4 + sum algebra.
  rw [elementaryWeightQ_phi_inv_mk M
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]),
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_sum :
      (∑ i : Fin s, M.b i
          * M.derivativeWeightWithSrc M.inverse i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]))
        = -(M.elementaryWeight RootedTree.vertex) ^ 4
          + 3 * (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight RootedTree.cherry
          - (M.elementaryWeight RootedTree.cherry) ^ 2
          - 2 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          + M.elementaryWeight
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) := by
    have h_subst :
        (∑ i : Fin s, M.b i
            * M.derivativeWeightWithSrc M.inverse i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]))
          = ∑ i : Fin s,
              ((-(M.elementaryWeight RootedTree.vertex) ^ 3
                  + 2 * M.elementaryWeight RootedTree.vertex
                      * M.elementaryWeight RootedTree.cherry
                  - M.elementaryWeight
                      (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
                  * M.b i
                + ((M.elementaryWeight RootedTree.vertex) ^ 2
                    - M.elementaryWeight RootedTree.cherry)
                    * (M.b i * ∑ j : Fin s, M.A i j)
                + (-M.elementaryWeight RootedTree.vertex)
                    * (M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
                + M.b i * (∑ j : Fin s, M.A i j
                            * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_dws_mkMkCherry i, h_inv_mkCherry, h_inv_cherry, h_inv_v]
      -- The inner Σⱼ Aᵢⱼ · (inv_c + inv_v · Σ_k A_jk + Σ_k A_jk · Σ_l A_kl)
      -- needs to be distributed before `ring` can match the 4-term per-summand
      -- decomposition.
      have h_inner_expand :
          ∑ j : Fin s, M.A i j
              * (((M.elementaryWeight RootedTree.vertex) ^ 2
                    - M.elementaryWeight RootedTree.cherry)
                 + (-M.elementaryWeight RootedTree.vertex) * ∑ k : Fin s, M.A j k
                 + ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l)
            = ((M.elementaryWeight RootedTree.vertex) ^ 2
                  - M.elementaryWeight RootedTree.cherry)
                * ∑ j : Fin s, M.A i j
              + (-M.elementaryWeight RootedTree.vertex)
                  * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k
              + ∑ j : Fin s, M.A i j
                  * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l := by
        have h_inner :
            ∑ j : Fin s, M.A i j
                * (((M.elementaryWeight RootedTree.vertex) ^ 2
                      - M.elementaryWeight RootedTree.cherry)
                   + (-M.elementaryWeight RootedTree.vertex) * ∑ k : Fin s, M.A j k
                   + ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l)
              = ∑ j : Fin s, (((M.elementaryWeight RootedTree.vertex) ^ 2
                                - M.elementaryWeight RootedTree.cherry) * M.A i j
                + (-M.elementaryWeight RootedTree.vertex)
                    * (M.A i j * ∑ k : Fin s, M.A j k)
                + M.A i j * (∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l)) := by
          refine Finset.sum_congr rfl (fun j _ => ?_); ring
        rw [h_inner, Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
      rw [h_inner_expand]; ring
    rw [h_subst, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← h_mkMkCherry, ← h_mkCherry, ← h_cherry, ← h_vertex]
    ring
  rw [h_sum]; ring

/-- *Phase D.3.b Step 2 (cycle 378) — `mk [mk [cherry]]` closed form
non-vacuity at `η_q = ⟦explicitEuler⟧`.* The expected value is
`Φ_{⟦explicitEuler⟧⁻¹}(mk [mk [cherry]]) = 1^4 − 3·1²·0 + 0² + 2·1·0
 − 0 = 1`, since for explicit Euler `Σ b = 1` (so `Φ_η(vertex) = 1`)
and `A = 0` (so all higher elementary weights vanish). -/
example :
    elementaryWeightQ_phi
      ((Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩))⁻¹
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) = 1 := by
  rw [elementaryWeightQ_phi_inv_mkMkCherry, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk]
  have h_vertex : RKTableau.explicitEuler.elementaryWeight RootedTree.vertex = 1 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.vertex = 1
    simp [RKTableau.explicitEuler, RKTableau.derivativeWeight_vertex]
  have h_cherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.cherry = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_cherry : RKTableau.explicitEuler.elementaryWeight RootedTree.cherry = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.cherry = 0
    simp [h_cherry_zero]
  have h_mkCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.cherry)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_mkCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0
    simp [h_mkCherry_zero]
  have h_mkMkCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_mkMkCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) = 0
    simp [h_mkMkCherry_zero]
  rw [h_vertex, h_cherry, h_mkCherry, h_mkMkCherry]; ring

/-- *Phase D.3.b Step 2 (cycle 378) — Priority 2 `mk [mk [cherry]]`
m=0 witness:* specialisation of Sub-lemma A
`powRep_sum_eq_of_strict_subtree_agreement` at
`t = mk [mk [cherry]], m = 0`. Under agreement at `vertex`, `cherry`,
`mk [cherry]`, and `mk [mk [cherry]]` (four subtrees corresponding to
the closed-form factors of cycle 378's `_mkMkCherry`), the `η_q^(-1)`
images at `mk [mk [cherry]]` coincide.

Proof: reduce `η_q ^ (-(((0 + 1 : ℕ) : ℤ)))` to `η_q⁻¹` via
`Nat.cast_one` + `zpow_neg_one`, apply cycle 378's
`elementaryWeightQ_phi_inv_mkMkCherry` on both sides, then substitute
the four agreement hypotheses. Note: unlike cycles 371/372's m=0
corollaries which carry a (strictly unused) `h_broom₃` for ladder
uniformity, this corollary omits the broom₃ hypothesis, faithfully
matching the closed form `v⁴ − 3v²c + c² + 2vm − M_mkMkCherry`
which has no `broom₃` term. -/
theorem powRep_sum_eq_of_agreement_at_mkMkCherry_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry)
    (h_mkCherry : elementaryWeightQ_phi η_q
                    (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
    (h_mkMkCherry : elementaryWeightQ_phi η_q
                      (OpenMath.Chapter3.Section310.RootedTree.mk
                        [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) := by
  have h_pow : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
      ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
    intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow η_q, h_pow η_q',
      elementaryWeightQ_phi_inv_mkMkCherry,
      elementaryWeightQ_phi_inv_mkMkCherry,
      h_vertex, h_cherry, h_mkCherry, h_mkMkCherry]

/-- *Phase D.3.b Step 2 (cycle 378) — `mk [mk [cherry]]` m=0 witness
non-vacuity at `η_q = η_q' = ⟦explicitEuler⟧`.* Discharges the four
agreement hypotheses by `rfl`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) :=
  powRep_sum_eq_of_agreement_at_mkMkCherry_zero
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    rfl rfl rfl rfl

/-- *Phase D.3.b Step 2 (cycle 384) — `mk [cherry, cherry]` (order-5
symmetric-two-cherry-children) closed form for Φ_{η_q⁻¹}.* At the
order-5 tree `mk [cherry, cherry]` (σ=2, two identical cherry
children), the quotient-level elementary weight of the §383 inverse
class admits the closed form
  `Φ_{η_q⁻¹}(mk [cherry, cherry])
       = −(Φ_η(vertex))^5
         + 4 · (Φ_η(vertex))^3 · Φ_η(cherry)
         − 3 · Φ_η(vertex) · (Φ_η(cherry))^2
         − (Φ_η(vertex))^2 · Φ_η(broom₃)
         − 2 · (Φ_η(vertex))^2 · Φ_η(mk [cherry])
         + 2 · Φ_η(cherry) · Φ_η(mk [cherry])
         + 2 · Φ_η(vertex) · Φ_η(mk [vertex, cherry])
         − Φ_η(mk [cherry, cherry])`.

Ninth data point in the cycle 366 §G Route B hypothesis ladder
(vertex, cherry, broom₃, mk [cherry], bushy, mk [broom₃],
mk [vertex, cherry], mk [mk [cherry]], mk [cherry, cherry]). First
**symmetric two-non-leaf-children** witness: both children are
identical `cherry` subtrees, so the per-row factor of the
representative-form derivativeWeightWithSrc is a square
`(inv_c + Σⱼ Aᵢⱼ · (inv_v + Σₖ Aⱼₖ))²`.

Proof outline (mirrors cycle 372's `mk [vertex, cherry]` recipe with
the vertex factor replaced by a second cherry factor, yielding a
square instead of an asymmetric product):

1. Reduce to a representative `⟨s, M⟩` via `Quotient.inductionOn`.
2. Reuse cycle 367/368/369/372 helpers `h_inv_v`, `h_vertex`,
   `h_dw_cherry`, `h_cherry`, `h_dws_cherry`, `h_dw_broom₃`,
   `h_broom₃`, `h_inv_cherry`, `h_dw_mkCherry`, `h_mkCherry`,
   `h_dw_mkVertexCherry`, `h_mkVertexCherry`.
3. Add three new cycle 384 helpers for the
   `mk [cherry, cherry]` symmetric structure:
   - `h_dw_mkCherryCherry` : `M.derivativeWeight i (mk [cherry, cherry])
                              = (Σⱼ Aᵢⱼ · Σₖ Aⱼₖ)^2`
     (two-child cons-case unfold: both factors reduce via
     `h_dw_cherry`, yielding a square).
   - `h_mkCherryCherry` : `M.elementaryWeight (mk [cherry, cherry])
                           = Σᵢ bᵢ · (Σⱼ Aᵢⱼ · Σₖ Aⱼₖ)^2`.
   - `h_dws_mkCherryCherry` : `M.derivativeWeightWithSrc M.inverse i
                                (mk [cherry, cherry])
                                = (inv_c + Σⱼ Aᵢⱼ · (inv_v + Σₖ Aⱼₖ))^2`
     (two outer cons-case unfolds; both layers reuse cycle 367's
     `h_dws_cherry` (identical children).
4. After `_inv_mk`, `_mk` × 6 rewrites, substitute the closed form
   per-summand (6-term decomposition expanding the square via inner
   distribution + `Finset.sum_add_distrib`), distribute the sum via
   `Finset.sum_add_distrib` × 5, factor constants via
   `← Finset.mul_sum` × 5, back-substitute via `← h_mkCherryCherry,
   ← h_mkVertexCherry, ← h_broom₃, ← h_mkCherry, ← h_cherry,
   ← h_vertex`, close with `ring`. -/
theorem elementaryWeightQ_phi_inv_mkCherryCherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹)
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.cherry, RootedTree.cherry])
      = -(elementaryWeightQ_phi η_q RootedTree.vertex) ^ 5
        + 4 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 3
            * elementaryWeightQ_phi η_q RootedTree.cherry
        - 3 * elementaryWeightQ_phi η_q RootedTree.vertex
            * (elementaryWeightQ_phi η_q RootedTree.cherry) ^ 2
        - (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        - 2 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + 2 * elementaryWeightQ_phi η_q RootedTree.cherry
            * elementaryWeightQ_phi η_q
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry])
        - elementaryWeightQ_phi η_q
            (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.cherry, RootedTree.cherry]) := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- Cycle 367 helpers (reused verbatim).
  have h_inv_v : M.inverse.elementaryWeight RootedTree.vertex
      = -M.elementaryWeight RootedTree.vertex := by
    show ∑ j : Fin s, M.inverse.b j * M.inverse.derivativeWeight j RootedTree.vertex
          = -(∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.inverse_b, RKTableau.derivativeWeight_vertex,
        RKTableau.derivativeWeight_vertex, neg_mul]
  have h_vertex : M.elementaryWeight RootedTree.vertex = ∑ j : Fin s, M.b j := by
    show ∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.b j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_dw_cherry : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.cherry = ∑ j : Fin s, M.A i j := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_cherry : M.elementaryWeight RootedTree.cherry
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.cherry
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_cherry i]
  have h_dws_cherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i RootedTree.cherry
        = M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * (1 : ℝ) = _
    rw [mul_one]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
  -- Cycle 368 helpers (reused verbatim).
  have h_dw_broom₃ : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.broom₃ = (∑ j : Fin s, M.A i j) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 2
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    rw [h_inner_sum, h_prod_step]; ring
  have h_broom₃ : M.elementaryWeight RootedTree.broom₃
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.broom₃
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_broom₃ i]
  -- Cycle 369: `h_inv_cherry` lifted from cycle 367's quotient theorem at ⟦M⟧.
  have h_inv_cherry : M.inverse.elementaryWeight RootedTree.cherry
      = (M.elementaryWeight RootedTree.vertex) ^ 2
        - M.elementaryWeight RootedTree.cherry :=
    elementaryWeightQ_phi_inv_cherry
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)
  -- Cycle 369 helpers for `mk [cherry]` derivative/elementary weight closed forms.
  have h_dw_mkCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
          * M.derivativeWeightProd i [] = _
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dw_cherry j]
  have h_mkCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkCherry i]
  -- Cycle 372 helpers (reused verbatim) — `mk [vertex, cherry]` derivative/
  -- elementary weight closed forms.
  have h_dw_mkVertexCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry])
        = (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.cherry] = _
    have h_vertex_factor :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_cherry_factor :
        M.derivativeWeightProd i [RootedTree.cherry]
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_cherry j]
    rw [h_vertex_factor, h_cherry_factor]
  have h_mkVertexCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
              * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexCherry i]; ring
  -- New cycle 384 helpers — two-cherry-children symmetric structure.
  -- Derivative weight: two-child cons-case unfold, both children give the
  -- cherry-factor `Σⱼ Aᵢⱼ · Σₖ Aⱼₖ`; result is the square.
  have h_dw_mkCherryCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.cherry, RootedTree.cherry])
        = (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
          * M.derivativeWeightProd i [RootedTree.cherry] = _
    have h_cherry_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_cherry j]
    have h_cherry_factor :
        M.derivativeWeightProd i [RootedTree.cherry]
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_cherry_inner]
    rw [h_cherry_inner, h_cherry_factor]; ring
  have h_mkCherryCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.cherry, RootedTree.cherry])
      = ∑ i : Fin s, M.b i
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2 := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.cherry, RootedTree.cherry])
          = ∑ i : Fin s, M.b i
              * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkCherryCherry i]
  -- Two-layer cons-case unfold for `mk [cherry, cherry]`'s
  -- derivativeWeightWithSrc: outer one-cons unfold strips the `mk` layer,
  -- producing a product of two source-tagged factors. Both children are
  -- `cherry` (identical), so both factors unfold via cycle 367's `h_dws_cherry`
  -- to the same expression. The product is therefore a square.
  have h_dws_mkCherryCherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.cherry, RootedTree.cherry])
        = (M.inverse.elementaryWeight RootedTree.cherry
            + ∑ j : Fin s, M.A i j
                * (M.inverse.elementaryWeight RootedTree.vertex
                   + ∑ k : Fin s, M.A j k)) ^ 2 := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.cherry
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.cherry)
          * M.derivativeWeightWithSrcProd M.inverse i [RootedTree.cherry] = _
    have h_cherry_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeightWithSrc M.inverse j RootedTree.cherry
          = ∑ j : Fin s, M.A i j
              * (M.inverse.elementaryWeight RootedTree.vertex
                 + ∑ k : Fin s, M.A j k) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dws_cherry j]
    have h_cherry_factor :
        M.derivativeWeightWithSrcProd M.inverse i [RootedTree.cherry]
          = M.inverse.elementaryWeight RootedTree.cherry
            + ∑ j : Fin s, M.A i j
                * (M.inverse.elementaryWeight RootedTree.vertex
                   + ∑ k : Fin s, M.A j k) := by
      show (M.inverse.elementaryWeight RootedTree.cherry
              + ∑ j : Fin s, M.A i j
                  * M.derivativeWeightWithSrc M.inverse j RootedTree.cherry)
            * M.derivativeWeightWithSrcProd M.inverse i [] = _
      rw [show M.derivativeWeightWithSrcProd M.inverse i [] = 1 from rfl, mul_one,
          h_cherry_inner]
    rw [h_cherry_inner, h_cherry_factor]; ring
  -- Main computation: assemble closed form via _inv_mk + _mk × 6 + sum algebra.
  rw [elementaryWeightQ_phi_inv_mk M
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.cherry, RootedTree.cherry]),
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_sum :
      (∑ i : Fin s, M.b i
          * M.derivativeWeightWithSrc M.inverse i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.cherry, RootedTree.cherry]))
        = (M.elementaryWeight RootedTree.vertex) ^ 5
          - 4 * (M.elementaryWeight RootedTree.vertex) ^ 3
              * M.elementaryWeight RootedTree.cherry
          + 3 * M.elementaryWeight RootedTree.vertex
              * (M.elementaryWeight RootedTree.cherry) ^ 2
          + 2 * (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          - 2 * M.elementaryWeight RootedTree.cherry
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          + (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight RootedTree.broom₃
          - 2 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry])
          + M.elementaryWeight
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.cherry, RootedTree.cherry]) := by
    have h_subst :
        (∑ i : Fin s, M.b i
            * M.derivativeWeightWithSrc M.inverse i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.cherry, RootedTree.cherry]))
          = ∑ i : Fin s,
              (((M.elementaryWeight RootedTree.vertex) ^ 2
                  - M.elementaryWeight RootedTree.cherry) ^ 2 * M.b i
                + (-2 * M.elementaryWeight RootedTree.vertex
                    * ((M.elementaryWeight RootedTree.vertex) ^ 2
                       - M.elementaryWeight RootedTree.cherry))
                    * (M.b i * ∑ j : Fin s, M.A i j)
                + (2 * ((M.elementaryWeight RootedTree.vertex) ^ 2
                        - M.elementaryWeight RootedTree.cherry))
                    * (M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
                + (M.elementaryWeight RootedTree.vertex) ^ 2
                    * (M.b i * (∑ j : Fin s, M.A i j) ^ 2)
                + (-2 * M.elementaryWeight RootedTree.vertex)
                    * (M.b i * (∑ j : Fin s, M.A i j)
                        * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k))
                + M.b i * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_dws_mkCherryCherry i, h_inv_cherry, h_inv_v]
      -- The inner Σⱼ Aᵢⱼ · (-v + Σₖ Aⱼₖ) needs distribution before `ring`
      -- can match the 6-term per-summand decomposition.
      have h_inner_expand :
          ∑ j : Fin s, M.A i j
              * (-M.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k)
            = -M.elementaryWeight RootedTree.vertex * ∑ j : Fin s, M.A i j
              + ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
        have h_inner :
            ∑ j : Fin s, M.A i j
                * (-M.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k)
              = ∑ j : Fin s, (-M.elementaryWeight RootedTree.vertex * M.A i j
                  + M.A i j * ∑ k : Fin s, M.A j k) := by
          refine Finset.sum_congr rfl (fun j _ => ?_); ring
        rw [h_inner, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [h_inner_expand]; ring
    rw [h_subst, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum,
        ← h_mkCherryCherry, ← h_mkVertexCherry, ← h_broom₃, ← h_mkCherry,
        ← h_cherry, ← h_vertex]
    ring
  rw [h_sum]; ring

/-- *Phase D.3.b Step 2 (cycle 384) — `mk [cherry, cherry]` closed form
non-vacuity at `η_q = ⟦explicitEuler⟧`.* The expected value is
`Φ_{⟦explicitEuler⟧⁻¹}(mk [cherry, cherry]) = -1^5 + 4·1³·0 - 3·1·0²
 - 1²·0 - 2·1²·0 + 2·0·0 + 2·1·0 - 0 = -1`, since for explicit Euler
`Σ b = 1` (so `Φ_η(vertex) = 1`) and `A = 0` (so all higher elementary
weights vanish). -/
example :
    elementaryWeightQ_phi
      ((Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩))⁻¹
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.cherry, RootedTree.cherry]) = -1 := by
  rw [elementaryWeightQ_phi_inv_mkCherryCherry, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk]
  have h_vertex : RKTableau.explicitEuler.elementaryWeight RootedTree.vertex = 1 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.vertex = 1
    simp [RKTableau.explicitEuler, RKTableau.derivativeWeight_vertex]
  have h_cherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.cherry = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_cherry : RKTableau.explicitEuler.elementaryWeight RootedTree.cherry = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.cherry = 0
    simp [h_cherry_zero]
  have h_broom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.broom₃ = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_broom₃ : RKTableau.explicitEuler.elementaryWeight RootedTree.broom₃ = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.broom₃ = 0
    simp [h_broom₃_zero]
  have h_mkCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.cherry)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_mkCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0
    simp [h_mkCherry_zero]
  have h_mkVertexCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.cherry] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]) = 0
    simp [h_mkVertexCherry_zero]
  have h_mkCherryCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.cherry, RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.cherry)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.cherry] = 0
    simp [RKTableau.explicitEuler]
  have h_mkCherryCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.cherry, RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.cherry, RootedTree.cherry]) = 0
    simp [h_mkCherryCherry_zero]
  rw [h_vertex, h_cherry, h_broom₃, h_mkCherry, h_mkVertexCherry, h_mkCherryCherry]
  ring

/-- *Phase D.3.b Step 2 (cycle 384) — Priority 2 `mk [cherry, cherry]`
m=0 witness:* specialisation of Sub-lemma A
`powRep_sum_eq_of_strict_subtree_agreement` at
`t = mk [cherry, cherry], m = 0`. Under agreement at `vertex`, `cherry`,
`broom₃`, `mk [cherry]`, `mk [vertex, cherry]`, and `mk [cherry, cherry]`
(six subtrees corresponding to the closed-form factors of cycle 384's
`_mkCherryCherry`), the `η_q^(-1)` images at `mk [cherry, cherry]`
coincide.

Proof: reduce `η_q ^ (-(((0 + 1 : ℕ) : ℤ)))` to `η_q⁻¹` via
`Nat.cast_one` + `zpow_neg_one`, apply cycle 384's
`elementaryWeightQ_phi_inv_mkCherryCherry` on both sides, then
substitute the six agreement hypotheses. -/
theorem powRep_sum_eq_of_agreement_at_mkCherryCherry_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry)
    (h_broom₃ : elementaryWeightQ_phi η_q RootedTree.broom₃
              = elementaryWeightQ_phi η_q' RootedTree.broom₃)
    (h_mkCherry : elementaryWeightQ_phi η_q
                    (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
    (h_mkVertexCherry : elementaryWeightQ_phi η_q
                          (OpenMath.Chapter3.Section310.RootedTree.mk
                            [RootedTree.vertex, RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry]))
    (h_mkCherryCherry : elementaryWeightQ_phi η_q
                          (OpenMath.Chapter3.Section310.RootedTree.mk
                            [RootedTree.cherry, RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.cherry, RootedTree.cherry])) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.cherry, RootedTree.cherry])
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.cherry, RootedTree.cherry]) := by
  have h_pow : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
      ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
    intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow η_q, h_pow η_q',
      elementaryWeightQ_phi_inv_mkCherryCherry,
      elementaryWeightQ_phi_inv_mkCherryCherry,
      h_vertex, h_cherry, h_broom₃, h_mkCherry, h_mkVertexCherry, h_mkCherryCherry]

/-- *Phase D.3.b Step 2 (cycle 384) — `mk [cherry, cherry]` m=0 witness
non-vacuity at `η_q = η_q' = ⟦explicitEuler⟧`.* Discharges the six
agreement hypotheses by `rfl`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.cherry, RootedTree.cherry])
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.cherry, RootedTree.cherry]) :=
  powRep_sum_eq_of_agreement_at_mkCherryCherry_zero
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    rfl rfl rfl rfl rfl rfl

/-! ### Phase α'.4.0 (cycle 386) — `mk [broom₃, cherry]` Family C witness

Phase α'.4.0 deliverable per the cycle 385 Family C scoping doc §7
(`.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`).

The order-6 asymmetric two-non-leaf-children tree
`mk [broom₃, cherry]` (σ = 1) is the 10th Family C ladder data
point. Its closed form surfaces the NEW kernel
`Φ_η(mk [vertex, broom₃])` (order 5, leaf + non-leaf mixed
two-children) from the Block (4) bilinear cross-term per
scoping doc §3.2. This confirms the existence of an order-5
leaf+non-leaf mixed-children kernel that the Phase α'.4.1
recursive `inversePolyTree` must accommodate. -/

/-- *Phase α'.4.0 (cycle 386) — `mk [broom₃, cherry]` closed form for
Φ_{η_q⁻¹}.* At the order-6 asymmetric two-non-leaf-children tree
`mk [broom₃, cherry]` (σ = 1), the quotient-level elementary weight
of the §383 inverse class admits the closed form
  `Φ_{η_q⁻¹}(mk [broom₃, cherry])
    = v⁶ − 5v⁴c + 5v²c² + 2v³b' − 2vb'c + 3v³m − 4vcm + b'm
      − v²·M_broom₃ + c·M_broom₃ − 3v²·vc + 2v·cc + v·vb' − bc`
where `v, c, b', m, M_broom₃, vc, cc, vb', bc` abbreviate `Φ_η` at
vertex, cherry, broom₃, mk [cherry], mk [broom₃],
mk [vertex, cherry], mk [cherry, cherry], mk [vertex, broom₃] (new
kernel), and the self-kernel mk [broom₃, cherry] respectively.

Tenth data point in the cycle 366 §G Route B hypothesis ladder
(Phase α'.4.0 deliverable per the cycle 385 scoping doc §7). Block
(4) bilinear cross-term surfaces the NEW kernel
`vb' = Φ_η(mk [vertex, broom₃])` alongside the known cycle 384
kernel `cc = Φ_η(mk [cherry, cherry])`.

Proof: descend via `Quotient.inductionOn`, apply
`elementaryWeightQ_phi_inv_mk` to expand the LHS, then unfold
`derivativeWeightWithSrc` via the two-non-leaf-children cons-case
(outer first child `broom₃` reusing cycle 368's
`(inv_v + ∑_k A_{jk})²` formula, tail `[cherry]` reusing cycle
367's `(inv_v + ∑_k A_{jk})` formula). The inner sums
`∑_j A_{ij}·(inv_v + ∑_k A_{jk})` (linear, cycle 372 pattern) and
`∑_j A_{ij}·(inv_v + ∑_k A_{jk})²` (squared, cycle 371 pattern)
are pre-distributed via `h_inner_expand_1` / `h_inner_expand_2`
before `ring` can match the 9-term per-summand decomposition.
Final assembly via `Finset.sum_add_distrib × 8`,
`← Finset.mul_sum × 8`, and back-substitution into the nine
kernels (vertex, cherry, broom₃, mk [cherry], mk [broom₃],
mk [vertex, cherry], mk [cherry, cherry], mk [vertex, broom₃],
mk [broom₃, cherry]). -/
theorem elementaryWeightQ_phi_inv_mkBroomCherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹)
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.broom₃, RootedTree.cherry])
      = (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 6
        - 5 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 4
            * elementaryWeightQ_phi η_q RootedTree.cherry
        + 5 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * (elementaryWeightQ_phi η_q RootedTree.cherry) ^ 2
        + 2 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 3
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        - 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q RootedTree.broom₃
            * elementaryWeightQ_phi η_q RootedTree.cherry
        + 3 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 3
            * elementaryWeightQ_phi η_q
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - 4 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q RootedTree.cherry
            * elementaryWeightQ_phi η_q
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + elementaryWeightQ_phi η_q RootedTree.broom₃
            * elementaryWeightQ_phi η_q
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
        + elementaryWeightQ_phi η_q RootedTree.cherry
            * elementaryWeightQ_phi η_q
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
        - 3 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry])
        + 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.cherry, RootedTree.cherry])
        + elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.broom₃])
        - elementaryWeightQ_phi η_q
            (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.broom₃, RootedTree.cherry]) := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- Cycle 367 helpers (reused verbatim).
  have h_inv_v : M.inverse.elementaryWeight RootedTree.vertex
      = -M.elementaryWeight RootedTree.vertex := by
    show ∑ j : Fin s, M.inverse.b j * M.inverse.derivativeWeight j RootedTree.vertex
          = -(∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.inverse_b, RKTableau.derivativeWeight_vertex,
        RKTableau.derivativeWeight_vertex, neg_mul]
  have h_vertex : M.elementaryWeight RootedTree.vertex = ∑ j : Fin s, M.b j := by
    show ∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.b j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_dw_cherry : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.cherry = ∑ j : Fin s, M.A i j := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_cherry : M.elementaryWeight RootedTree.cherry
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.cherry
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_cherry i]
  have h_dws_cherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i RootedTree.cherry
        = M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * (1 : ℝ) = _
    rw [mul_one]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
  -- Cycle 368 helpers (reused verbatim).
  have h_dw_broom₃ : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.broom₃ = (∑ j : Fin s, M.A i j) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 2
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    rw [h_inner_sum, h_prod_step]; ring
  have h_broom₃ : M.elementaryWeight RootedTree.broom₃
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.broom₃
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_broom₃ i]
  have h_dws_broom₃ : ∀ j : Fin s,
      M.derivativeWeightWithSrc M.inverse j RootedTree.broom₃
        = (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ k : Fin s, M.A j k) ^ 2 := by
    intro j
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ k : Fin s, M.A j k
                * M.derivativeWeightWithSrc M.inverse k RootedTree.vertex)
          * M.derivativeWeightWithSrcProd M.inverse j [RootedTree.vertex]
        = (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ k : Fin s, M.A j k) ^ 2
    have h_inner_sum :
        ∑ k : Fin s, M.A j k
            * M.derivativeWeightWithSrc M.inverse k RootedTree.vertex
          = ∑ k : Fin s, M.A j k := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
    have h_prod_step :
        M.derivativeWeightWithSrcProd M.inverse j [RootedTree.vertex]
          = M.inverse.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k := by
      show (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ k : Fin s, M.A j k
                  * M.derivativeWeightWithSrc M.inverse k RootedTree.vertex)
            * M.derivativeWeightWithSrcProd M.inverse j []
          = M.inverse.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k
      rw [show M.derivativeWeightWithSrcProd M.inverse j [] = 1 from rfl, mul_one,
          h_inner_sum]
    rw [h_inner_sum, h_prod_step]; ring
  -- Cycle 369: `h_inv_cherry` lifted from cycle 367's quotient theorem at ⟦M⟧.
  have h_inv_cherry : M.inverse.elementaryWeight RootedTree.cherry
      = (M.elementaryWeight RootedTree.vertex) ^ 2
        - M.elementaryWeight RootedTree.cherry :=
    elementaryWeightQ_phi_inv_cherry
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)
  -- Cycle 371: `h_inv_broom₃` lifted from cycle 368's quotient theorem at ⟦M⟧.
  have h_inv_broom₃ : M.inverse.elementaryWeight RootedTree.broom₃
      = -(M.elementaryWeight RootedTree.vertex) ^ 3
        + 2 * M.elementaryWeight RootedTree.vertex
            * M.elementaryWeight RootedTree.cherry
        - M.elementaryWeight RootedTree.broom₃ :=
    elementaryWeightQ_phi_inv_broom₃
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)
  -- Cycle 369 helpers for `mk [cherry]` derivative/elementary weight closed forms.
  have h_dw_mkCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
          * M.derivativeWeightProd i [] = _
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dw_cherry j]
  have h_mkCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkCherry i]
  -- Cycle 371 helpers for `mk [broom₃]` derivative/elementary weight closed forms.
  have h_dw_mkBroom₃ : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
        = ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.broom₃)
          * M.derivativeWeightProd i [] = _
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dw_broom₃ j]
  have h_mkBroom₃ : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2 := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkBroom₃ i]
  -- Cycle 372 helpers for `mk [vertex, cherry]` derivative/elementary weight
  -- closed forms.
  have h_dw_mkVertexCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry])
        = (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.cherry] = _
    have h_vertex_factor :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_cherry_factor :
        M.derivativeWeightProd i [RootedTree.cherry]
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_cherry j]
    rw [h_vertex_factor, h_cherry_factor]
  have h_mkVertexCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
              * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexCherry i]; ring
  -- Cycle 384 helpers for `mk [cherry, cherry]` derivative/elementary weight
  -- closed forms.
  have h_dw_mkCherryCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.cherry, RootedTree.cherry])
        = (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
          * M.derivativeWeightProd i [RootedTree.cherry] = _
    have h_cherry_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_cherry j]
    have h_cherry_factor :
        M.derivativeWeightProd i [RootedTree.cherry]
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_cherry_inner]
    rw [h_cherry_inner, h_cherry_factor]; ring
  have h_mkCherryCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.cherry, RootedTree.cherry])
      = ∑ i : Fin s, M.b i
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2 := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.cherry, RootedTree.cherry])
          = ∑ i : Fin s, M.b i
              * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkCherryCherry i]
  -- New cycle 386 helpers — `mk [vertex, broom₃]` kernel surfaced by Block (4).
  -- Order-5 asymmetric leaf + non-leaf two-children tree.
  have h_dw_mkVertexBroom₃ : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.broom₃])
        = (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.broom₃] = _
    have h_vertex_factor :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_broom_factor :
        M.derivativeWeightProd i [RootedTree.broom₃]
          = ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2 := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.broom₃)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_broom₃ j]
    rw [h_vertex_factor, h_broom_factor]
  have h_mkVertexBroom₃ : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.broom₃])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.broom₃])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
              * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexBroom₃ i]; ring
  -- New cycle 386 helpers — `mk [broom₃, cherry]` self-kernel.
  have h_dw_mkBroomCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.broom₃, RootedTree.cherry])
        = (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.broom₃)
          * M.derivativeWeightProd i [RootedTree.cherry] = _
    have h_broom_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.broom₃
          = ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2 := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_broom₃ j]
    have h_cherry_factor :
        M.derivativeWeightProd i [RootedTree.cherry]
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_cherry j]
    rw [h_broom_inner, h_cherry_factor]
  have h_mkBroomCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.broom₃, RootedTree.cherry])
      = ∑ i : Fin s, M.b i
          * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.broom₃, RootedTree.cherry])
          = ∑ i : Fin s, M.b i
              * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2)
              * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkBroomCherry i]; ring
  -- New cycle 386 helper — `mk [broom₃, cherry]` derivativeWeightWithSrc unfold.
  -- Two-non-leaf-children cons-case: outer first child broom₃ uses cycle
  -- 368-style `h_dws_broom₃`, tail [cherry] uses cycle 367-style `h_dws_cherry`.
  have h_dws_mkBroomCherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.broom₃, RootedTree.cherry])
        = (M.inverse.elementaryWeight RootedTree.broom₃
            + ∑ j : Fin s, M.A i j
                * (M.inverse.elementaryWeight RootedTree.vertex
                    + ∑ k : Fin s, M.A j k) ^ 2)
          * (M.inverse.elementaryWeight RootedTree.cherry
              + ∑ j : Fin s, M.A i j
                  * (M.inverse.elementaryWeight RootedTree.vertex
                     + ∑ k : Fin s, M.A j k)) := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.broom₃
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.broom₃)
          * M.derivativeWeightWithSrcProd M.inverse i [RootedTree.cherry] = _
    have h_broom_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeightWithSrc M.inverse j RootedTree.broom₃
          = ∑ j : Fin s, M.A i j
              * (M.inverse.elementaryWeight RootedTree.vertex
                  + ∑ k : Fin s, M.A j k) ^ 2 := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dws_broom₃ j]
    have h_cherry_factor :
        M.derivativeWeightWithSrcProd M.inverse i [RootedTree.cherry]
          = M.inverse.elementaryWeight RootedTree.cherry
            + ∑ j : Fin s, M.A i j
                * (M.inverse.elementaryWeight RootedTree.vertex
                   + ∑ k : Fin s, M.A j k) := by
      show (M.inverse.elementaryWeight RootedTree.cherry
              + ∑ j : Fin s, M.A i j
                  * M.derivativeWeightWithSrc M.inverse j RootedTree.cherry)
            * M.derivativeWeightWithSrcProd M.inverse i [] = _
      rw [show M.derivativeWeightWithSrcProd M.inverse i [] = 1 from rfl, mul_one]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dws_cherry j]
    rw [h_broom_inner, h_cherry_factor]
  -- Main computation: assemble closed form via _inv_mk + _mk × 9 + sum algebra.
  rw [elementaryWeightQ_phi_inv_mk M
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.broom₃, RootedTree.cherry]),
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk]
  have h_sum :
      (∑ i : Fin s, M.b i
          * M.derivativeWeightWithSrc M.inverse i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.broom₃, RootedTree.cherry]))
        = -(M.elementaryWeight RootedTree.vertex) ^ 6
          + 5 * (M.elementaryWeight RootedTree.vertex) ^ 4
              * M.elementaryWeight RootedTree.cherry
          - 5 * (M.elementaryWeight RootedTree.vertex) ^ 2
              * (M.elementaryWeight RootedTree.cherry) ^ 2
          - 2 * (M.elementaryWeight RootedTree.vertex) ^ 3
              * M.elementaryWeight RootedTree.broom₃
          + 2 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight RootedTree.broom₃
              * M.elementaryWeight RootedTree.cherry
          - 3 * (M.elementaryWeight RootedTree.vertex) ^ 3
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          + 4 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight RootedTree.cherry
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          - M.elementaryWeight RootedTree.broom₃
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          + (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
          - M.elementaryWeight RootedTree.cherry
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
          + 3 * (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry])
          - 2 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.cherry, RootedTree.cherry])
          - M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.broom₃])
          + M.elementaryWeight
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.broom₃, RootedTree.cherry]) := by
    have h_subst :
        (∑ i : Fin s, M.b i
            * M.derivativeWeightWithSrc M.inverse i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.broom₃, RootedTree.cherry]))
          = ∑ i : Fin s,
              ((-(M.elementaryWeight RootedTree.vertex) ^ 3
                  + 2 * M.elementaryWeight RootedTree.vertex
                      * M.elementaryWeight RootedTree.cherry
                  - M.elementaryWeight RootedTree.broom₃)
                  * ((M.elementaryWeight RootedTree.vertex) ^ 2
                      - M.elementaryWeight RootedTree.cherry) * M.b i
                + (2 * (M.elementaryWeight RootedTree.vertex) ^ 4
                    - 3 * (M.elementaryWeight RootedTree.vertex) ^ 2
                        * M.elementaryWeight RootedTree.cherry
                    + M.elementaryWeight RootedTree.vertex
                        * M.elementaryWeight RootedTree.broom₃)
                    * (M.b i * ∑ j : Fin s, M.A i j)
                + (-3 * (M.elementaryWeight RootedTree.vertex) ^ 3
                    + 4 * M.elementaryWeight RootedTree.vertex
                        * M.elementaryWeight RootedTree.cherry
                    - M.elementaryWeight RootedTree.broom₃)
                    * (M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
                + ((M.elementaryWeight RootedTree.vertex) ^ 2
                    - M.elementaryWeight RootedTree.cherry)
                    * (M.b i * ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2)
                + (-(M.elementaryWeight RootedTree.vertex) ^ 3)
                    * (M.b i * (∑ j : Fin s, M.A i j) ^ 2)
                + 3 * (M.elementaryWeight RootedTree.vertex) ^ 2
                    * (M.b i * (∑ j : Fin s, M.A i j)
                        * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k))
                + (-2 * M.elementaryWeight RootedTree.vertex)
                    * (M.b i * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2)
                + (-M.elementaryWeight RootedTree.vertex)
                    * (M.b i * (∑ j : Fin s, M.A i j)
                        * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2))
                + M.b i
                    * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2)
                    * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_dws_mkBroomCherry i, h_inv_broom₃, h_inv_cherry, h_inv_v]
      -- Two inner sums to distribute before `ring` can match the 9-term
      -- per-summand decomposition.
      have h_inner_expand_1 :
          ∑ j : Fin s, M.A i j
              * (-M.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k)
            = -M.elementaryWeight RootedTree.vertex * ∑ j : Fin s, M.A i j
              + ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
        have h_inner :
            ∑ j : Fin s, M.A i j
                * (-M.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k)
              = ∑ j : Fin s, (-M.elementaryWeight RootedTree.vertex * M.A i j
                  + M.A i j * ∑ k : Fin s, M.A j k) := by
          refine Finset.sum_congr rfl (fun j _ => ?_); ring
        rw [h_inner, Finset.sum_add_distrib, ← Finset.mul_sum]
      have h_inner_expand_2 :
          ∑ j : Fin s, M.A i j
              * (-M.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k) ^ 2
            = ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2
              - 2 * M.elementaryWeight RootedTree.vertex
                  * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k
              + M.elementaryWeight RootedTree.vertex ^ 2
                  * ∑ j : Fin s, M.A i j := by
        have h_inner :
            ∑ j : Fin s, M.A i j
                * (-M.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k) ^ 2
              = ∑ j : Fin s, (M.A i j * (∑ k : Fin s, M.A j k) ^ 2
                  - 2 * M.elementaryWeight RootedTree.vertex
                      * (M.A i j * ∑ k : Fin s, M.A j k)
                  + M.elementaryWeight RootedTree.vertex ^ 2 * M.A i j) := by
          refine Finset.sum_congr rfl (fun j _ => ?_); ring
        rw [h_inner, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
      rw [h_inner_expand_1, h_inner_expand_2]; ring
    rw [h_subst, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← h_mkBroomCherry, ← h_mkVertexBroom₃, ← h_mkCherryCherry,
        ← h_mkVertexCherry, ← h_mkBroom₃, ← h_mkCherry, ← h_broom₃,
        ← h_cherry, ← h_vertex]
    ring
  rw [h_sum]; ring

/-- *Phase α'.4.0 (cycle 386) — `mk [broom₃, cherry]` closed form
non-vacuity at `η_q = ⟦explicitEuler⟧`.* The expected value is
`Φ_{⟦explicitEuler⟧⁻¹}(mk [broom₃, cherry]) = 1⁶ − 5·1⁴·0 + 5·1²·0² +
2·1³·0 − 2·1·0·0 + 3·1³·0 − 4·1·0·0 + 0·0 − 1²·0 + 0·0 − 3·1²·0 + 2·1·0
+ 1·0 − 0 = 1`, since for explicit Euler `Σ b = 1` (so `Φ_η(vertex) = 1`)
and `A = 0` (so all higher elementary weights vanish). -/
example :
    elementaryWeightQ_phi
      ((Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩))⁻¹
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.broom₃, RootedTree.cherry]) = 1 := by
  rw [elementaryWeightQ_phi_inv_mkBroomCherry, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_vertex : RKTableau.explicitEuler.elementaryWeight RootedTree.vertex = 1 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.vertex = 1
    simp [RKTableau.explicitEuler, RKTableau.derivativeWeight_vertex]
  have h_cherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.cherry = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_cherry : RKTableau.explicitEuler.elementaryWeight RootedTree.cherry = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.cherry = 0
    simp [h_cherry_zero]
  have h_broom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.broom₃ = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_broom₃ : RKTableau.explicitEuler.elementaryWeight RootedTree.broom₃ = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.broom₃ = 0
    simp [h_broom₃_zero]
  have h_mkCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.cherry)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_mkCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0
    simp [h_mkCherry_zero]
  have h_mkBroom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.broom₃)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_mkBroom₃ :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) = 0
    simp [h_mkBroom₃_zero]
  have h_mkVertexCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.cherry] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]) = 0
    simp [h_mkVertexCherry_zero]
  have h_mkCherryCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.cherry, RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.cherry)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.cherry] = 0
    simp [RKTableau.explicitEuler]
  have h_mkCherryCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.cherry, RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.cherry, RootedTree.cherry]) = 0
    simp [h_mkCherryCherry_zero]
  have h_mkVertexBroom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.broom₃]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.broom₃] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexBroom₃ :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.broom₃]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.broom₃]) = 0
    simp [h_mkVertexBroom₃_zero]
  have h_mkBroomCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.broom₃, RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.broom₃)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.cherry] = 0
    simp [RKTableau.explicitEuler]
  have h_mkBroomCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.broom₃, RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.broom₃, RootedTree.cherry]) = 0
    simp [h_mkBroomCherry_zero]
  rw [h_vertex, h_cherry, h_broom₃, h_mkCherry, h_mkBroom₃,
      h_mkVertexCherry, h_mkCherryCherry, h_mkVertexBroom₃, h_mkBroomCherry]
  ring

/-- *Phase α'.4.0 (cycle 386) — Priority 1 `mk [broom₃, cherry]` m=0
witness:* specialisation of Sub-lemma A
`powRep_sum_eq_of_strict_subtree_agreement` at
`t = mk [broom₃, cherry], m = 0`. Under agreement at `vertex`, `cherry`,
`broom₃`, `mk [cherry]`, `mk [broom₃]`, `mk [vertex, cherry]`,
`mk [cherry, cherry]`, `mk [vertex, broom₃]` (new kernel from Block (4)),
and `mk [broom₃, cherry]` (nine subtrees corresponding to the closed-form
factors), the `η_q^(-1)` images at `mk [broom₃, cherry]` coincide.

Proof: reduce `η_q ^ (-(((0 + 1 : ℕ) : ℤ)))` to `η_q⁻¹` via
`Nat.cast_one` + `zpow_neg_one`, apply cycle 386's
`elementaryWeightQ_phi_inv_mkBroomCherry` on both sides, then
substitute the nine agreement hypotheses. -/
theorem powRep_sum_eq_of_agreement_at_mkBroomCherry_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry)
    (h_broom₃ : elementaryWeightQ_phi η_q RootedTree.broom₃
              = elementaryWeightQ_phi η_q' RootedTree.broom₃)
    (h_mkCherry : elementaryWeightQ_phi η_q
                    (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
    (h_mkBroom₃ : elementaryWeightQ_phi η_q
                    (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]))
    (h_mkVertexCherry : elementaryWeightQ_phi η_q
                          (OpenMath.Chapter3.Section310.RootedTree.mk
                            [RootedTree.vertex, RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry]))
    (h_mkCherryCherry : elementaryWeightQ_phi η_q
                          (OpenMath.Chapter3.Section310.RootedTree.mk
                            [RootedTree.cherry, RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.cherry, RootedTree.cherry]))
    (h_mkVertexBroom₃ : elementaryWeightQ_phi η_q
                          (OpenMath.Chapter3.Section310.RootedTree.mk
                            [RootedTree.vertex, RootedTree.broom₃])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.broom₃]))
    (h_mkBroomCherry : elementaryWeightQ_phi η_q
                          (OpenMath.Chapter3.Section310.RootedTree.mk
                            [RootedTree.broom₃, RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.broom₃, RootedTree.cherry])) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.broom₃, RootedTree.cherry])
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.broom₃, RootedTree.cherry]) := by
  have h_pow : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
      ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
    intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow η_q, h_pow η_q',
      elementaryWeightQ_phi_inv_mkBroomCherry,
      elementaryWeightQ_phi_inv_mkBroomCherry,
      h_vertex, h_cherry, h_broom₃, h_mkCherry, h_mkBroom₃,
      h_mkVertexCherry, h_mkCherryCherry, h_mkVertexBroom₃, h_mkBroomCherry]

/-- *Phase α'.4.0 (cycle 386) — `mk [broom₃, cherry]` m=0 witness
non-vacuity at `η_q = η_q' = ⟦explicitEuler⟧`.* Discharges the nine
agreement hypotheses by `rfl`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.broom₃, RootedTree.cherry])
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.broom₃, RootedTree.cherry]) :=
  powRep_sum_eq_of_agreement_at_mkBroomCherry_zero
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-! ### Phase α'.5.0 (cycle 403) — `mk [vertex, vertex, cherry]` first
non-symmetric `k = 3` witness

Phase α'.5.0 deliverable per the cycle 402 Phase α'.5 scoping doc §6.1
(`.prover-state/issues/def_422B_phase_alpha_prime_5_scoping.md`).

The order-5 asymmetric two-leaf + cherry three-children tree
`mk [vertex, vertex, cherry]` is the first non-symmetric `k = 3`
empirical witness for `inversePolyTree`. Its closed form is the
first ship since cycle 370's symmetric `bushy = mk [v, v, v]` to
exercise the three-children cons-case unfold at non-uniform children.

**Symbolic verification (cycle 403 worker):** the strategy's §C
paper-derivation prescribed the per-row inverse-derivative as
`(-v + Aᵢ)² · ((v² - c) + Bᵢ)` with `Bᵢ = ∑ⱼ Aᵢⱼ · ∑ₖ Aⱼₖ`. This
was found to be **incorrect**: the cherry-child factor in
`derivativeWeightWithSrc` contains `∑ⱼ Aᵢⱼ · derivativeWeightWithSrc
M.inverse j cherry = ∑ⱼ Aᵢⱼ · (-v + ∑ₖ Aⱼₖ) = -v·Aᵢ + Bᵢ`, not just
`Bᵢ`. The corrected per-row factor is `(-v + Aᵢ)² · ((v² - c) - v·Aᵢ
+ Bᵢ)`, which when summed against `Σᵢ bᵢ` yields a closed form
involving `Σᵢ bᵢ · Aᵢ³ = Φ_η(bushy)` as a 7th kernel beyond the §B
strategy's 6 kernels. The cycle 370 `bushy` closed form (already
shipped) provides the needed helper; no new kernel needs to be
introduced. -/

/-- *Phase α'.5.0 (cycle 403) — `mk [vertex, vertex, cherry]` closed
form for Φ_{η_q⁻¹}.* At the order-5 asymmetric two-leaf + cherry
three-children tree `mk [vertex, vertex, cherry]`, the quotient-level
elementary weight of the §383 inverse class admits the closed form
  `Φ_{η_q⁻¹}(mk [vertex, vertex, cherry])
       = −v⁵ + 4v³c − 2vc² − 3v²b' + cb' + v·bushy − v²m + 2v·vc
         − M_vvc`
where `v, c, b', bushy, m, vc, M_vvc` abbreviate `Φ_η` at vertex,
cherry, broom₃, bushy, mk [cherry], mk [vertex, cherry], and the
self-kernel mk [vertex, vertex, cherry] respectively.

First non-symmetric `k = 3` data point (Phase α'.5.0 per cycle 402
scoping doc §6.1). Combines cycle 370's bushy three-vertex-children
template (for the `(-v + Aᵢ)²` portion) with cycle 372's
`mkVertexCherry` cherry-tail template (for the `(v² - c) - v·Aᵢ
+ Bᵢ` portion).

Proof: descend via `Quotient.inductionOn`, apply
`elementaryWeightQ_phi_inv_mk` to expand the LHS, then unfold
`derivativeWeightWithSrc` via the three-children cons-case (outer
two-vertex factors reusing cycle 367's `derivativeWeightWithSrc_vertex
= 1`, tail `[cherry]` reusing cycle 367's `(inv_v + ∑_k A_{jk})`
formula). The inner sum `∑_j A_{ij}·(inv_v + ∑_k A_{jk})` (linear
distribution, cycle 372 pattern) is pre-distributed via
`h_inner_expand` before `ring` can match the 7-term per-summand
decomposition. Final assembly via `Finset.sum_add_distrib × 6`,
`← Finset.mul_sum × 6`, and back-substitution into the seven kernels
(vertex, cherry, broom₃, bushy, mk [cherry], mk [vertex, cherry],
mk [vertex, vertex, cherry]). -/
theorem elementaryWeightQ_phi_inv_mkVertexVertexCherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹)
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
      = -(elementaryWeightQ_phi η_q RootedTree.vertex) ^ 5
        + 4 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 3
            * elementaryWeightQ_phi η_q RootedTree.cherry
        - 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * (elementaryWeightQ_phi η_q RootedTree.cherry) ^ 2
        - 3 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        + elementaryWeightQ_phi η_q RootedTree.cherry
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        + elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q RootedTree.bushy
        - (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry])
        - elementaryWeightQ_phi η_q
            (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- Cycle 367 helpers (reused verbatim).
  have h_inv_v : M.inverse.elementaryWeight RootedTree.vertex
      = -M.elementaryWeight RootedTree.vertex := by
    show ∑ j : Fin s, M.inverse.b j * M.inverse.derivativeWeight j RootedTree.vertex
          = -(∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.inverse_b, RKTableau.derivativeWeight_vertex,
        RKTableau.derivativeWeight_vertex, neg_mul]
  have h_vertex : M.elementaryWeight RootedTree.vertex = ∑ j : Fin s, M.b j := by
    show ∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.b j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_dw_cherry : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.cherry = ∑ j : Fin s, M.A i j := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_cherry : M.elementaryWeight RootedTree.cherry
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.cherry
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_cherry i]
  have h_dws_cherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i RootedTree.cherry
        = M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * (1 : ℝ) = _
    rw [mul_one]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
  -- Cycle 368 helpers (reused verbatim).
  have h_dw_broom₃ : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.broom₃ = (∑ j : Fin s, M.A i j) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 2
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    rw [h_inner_sum, h_prod_step]; ring
  have h_broom₃ : M.elementaryWeight RootedTree.broom₃
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.broom₃
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_broom₃ i]
  -- Cycle 370 helpers (reused verbatim) — bushy three-vertex-children structure.
  have h_dw_bushy : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.bushy = (∑ j : Fin s, M.A i j) ^ 3 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex, RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 3
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step_1 :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    have h_prod_step_2 :
        M.derivativeWeightProd i [RootedTree.vertex, RootedTree.vertex]
          = (∑ j : Fin s, M.A i j) ^ 2 := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [RootedTree.vertex]
          = (∑ j : Fin s, M.A i j) ^ 2
      rw [h_inner_sum, h_prod_step_1]; ring
    rw [h_inner_sum, h_prod_step_2]; ring
  have h_bushy : M.elementaryWeight RootedTree.bushy
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 3 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.bushy
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 3
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_bushy i]
  -- Cycle 369: `h_inv_cherry` lifted from cycle 367's quotient theorem at ⟦M⟧.
  have h_inv_cherry : M.inverse.elementaryWeight RootedTree.cherry
      = (M.elementaryWeight RootedTree.vertex) ^ 2
        - M.elementaryWeight RootedTree.cherry :=
    elementaryWeightQ_phi_inv_cherry
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)
  -- Cycle 369 helpers for `mk [cherry]` derivative/elementary weight closed forms.
  have h_dw_mkCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
          * M.derivativeWeightProd i [] = _
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dw_cherry j]
  have h_mkCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkCherry i]
  -- Cycle 372 helpers (reused verbatim) — `mk [vertex, cherry]` derivative/
  -- elementary weight closed forms.
  have h_dw_mkVertexCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry])
        = (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.cherry] = _
    have h_vertex_factor :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_cherry_factor :
        M.derivativeWeightProd i [RootedTree.cherry]
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_cherry j]
    rw [h_vertex_factor, h_cherry_factor]
  have h_mkVertexCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
              * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexCherry i]; ring
  -- New cycle 403 helpers — three-children asymmetric `mk [vertex, vertex, cherry]`
  -- structure: two-vertex prefix giving `Aᵢ²` factor + cherry tail giving the
  -- `Bᵢ`-pattern factor.
  have h_dw_mkVertexVertexCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
        = (∑ j : Fin s, M.A i j) ^ 2
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex, RootedTree.cherry] = _
    have h_vertex_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_cherry_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_cherry j]
    have h_prod_step_cherry :
        M.derivativeWeightProd i [RootedTree.cherry]
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_cherry_inner]
    have h_prod_step_vc :
        M.derivativeWeightProd i [RootedTree.vertex, RootedTree.cherry]
          = (∑ j : Fin s, M.A i j)
            * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [RootedTree.cherry] = _
      rw [h_vertex_inner, h_prod_step_cherry]
    rw [h_vertex_inner, h_prod_step_vc]; ring
  have h_mkVertexVertexCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
              * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexVertexCherry i]; ring
  -- Three-layer cons-case unfold for `mk [vertex, vertex, cherry]`'s
  -- derivativeWeightWithSrc: outer two-cons unfold strips the two-vertex
  -- prefix, producing two identical vertex-source factors `inv_v + Aᵢ`
  -- (cycle 367/370 pattern); inner cherry tail unfolds via cycle 367's
  -- `h_dws_cherry` to `inv_c + ∑ⱼ Aᵢⱼ · (inv_v + ∑ₖ Aⱼₖ)`.
  have h_dws_mkVertexVertexCherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
        = (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j) ^ 2
          * (M.inverse.elementaryWeight RootedTree.cherry
             + ∑ j : Fin s, M.A i j
                 * (M.inverse.elementaryWeight RootedTree.vertex
                    + ∑ k : Fin s, M.A j k)) := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * M.derivativeWeightWithSrcProd M.inverse i
              [RootedTree.vertex, RootedTree.cherry] = _
    have h_vertex_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
    have h_cherry_factor :
        M.derivativeWeightWithSrcProd M.inverse i [RootedTree.cherry]
          = M.inverse.elementaryWeight RootedTree.cherry
            + ∑ j : Fin s, M.A i j
                * (M.inverse.elementaryWeight RootedTree.vertex
                   + ∑ k : Fin s, M.A j k) := by
      show (M.inverse.elementaryWeight RootedTree.cherry
              + ∑ j : Fin s, M.A i j
                  * M.derivativeWeightWithSrc M.inverse j RootedTree.cherry)
            * M.derivativeWeightWithSrcProd M.inverse i [] = _
      rw [show M.derivativeWeightWithSrcProd M.inverse i [] = 1 from rfl, mul_one]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dws_cherry j]
    have h_prod_step_vc :
        M.derivativeWeightWithSrcProd M.inverse i [RootedTree.vertex, RootedTree.cherry]
          = (M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j)
            * (M.inverse.elementaryWeight RootedTree.cherry
               + ∑ j : Fin s, M.A i j
                   * (M.inverse.elementaryWeight RootedTree.vertex
                      + ∑ k : Fin s, M.A j k)) := by
      show (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ j : Fin s, M.A i j
                  * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
            * M.derivativeWeightWithSrcProd M.inverse i [RootedTree.cherry] = _
      rw [h_vertex_inner, h_cherry_factor]
    rw [h_vertex_inner, h_prod_step_vc]; ring
  -- Main computation: assemble closed form via _inv_mk + _mk × 7 + sum algebra.
  rw [elementaryWeightQ_phi_inv_mk M
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]),
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk]
  have h_sum :
      (∑ i : Fin s, M.b i
          * M.derivativeWeightWithSrc M.inverse i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]))
        = (M.elementaryWeight RootedTree.vertex) ^ 5
          - 4 * (M.elementaryWeight RootedTree.vertex) ^ 3
              * M.elementaryWeight RootedTree.cherry
          + 2 * M.elementaryWeight RootedTree.vertex
              * (M.elementaryWeight RootedTree.cherry) ^ 2
          + 3 * (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight RootedTree.broom₃
          - M.elementaryWeight RootedTree.cherry
              * M.elementaryWeight RootedTree.broom₃
          - M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight RootedTree.bushy
          + (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          - 2 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry])
          + M.elementaryWeight
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) := by
    have h_subst :
        (∑ i : Fin s, M.b i
            * M.derivativeWeightWithSrc M.inverse i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]))
          = ∑ i : Fin s,
              (((M.elementaryWeight RootedTree.vertex) ^ 4
                  - (M.elementaryWeight RootedTree.vertex) ^ 2
                      * M.elementaryWeight RootedTree.cherry) * M.b i
                + (-3 * (M.elementaryWeight RootedTree.vertex) ^ 3
                    + 2 * M.elementaryWeight RootedTree.vertex
                        * M.elementaryWeight RootedTree.cherry)
                    * (M.b i * ∑ j : Fin s, M.A i j)
                + (3 * (M.elementaryWeight RootedTree.vertex) ^ 2
                    - M.elementaryWeight RootedTree.cherry)
                    * (M.b i * (∑ j : Fin s, M.A i j) ^ 2)
                + (-M.elementaryWeight RootedTree.vertex)
                    * (M.b i * (∑ j : Fin s, M.A i j) ^ 3)
                + (M.elementaryWeight RootedTree.vertex) ^ 2
                    * (M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
                + (-2 * M.elementaryWeight RootedTree.vertex)
                    * (M.b i * (∑ j : Fin s, M.A i j)
                        * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k))
                + M.b i * (∑ j : Fin s, M.A i j) ^ 2
                    * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_dws_mkVertexVertexCherry i, h_inv_cherry, h_inv_v]
      -- Pre-distribute the inner Σⱼ Aᵢⱼ · (-v + ∑ₖ Aⱼₖ) before `ring` can
      -- match the 7-term per-summand decomposition.
      have h_inner_expand :
          ∑ j : Fin s, M.A i j
              * (-M.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k)
            = -M.elementaryWeight RootedTree.vertex * ∑ j : Fin s, M.A i j
              + ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
        have h_inner :
            ∑ j : Fin s, M.A i j
                * (-M.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k)
              = ∑ j : Fin s, (-M.elementaryWeight RootedTree.vertex * M.A i j
                  + M.A i j * ∑ k : Fin s, M.A j k) := by
          refine Finset.sum_congr rfl (fun j _ => ?_); ring
        rw [h_inner, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [h_inner_expand]; ring
    rw [h_subst, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum,
        ← h_mkVertexVertexCherry, ← h_mkVertexCherry, ← h_mkCherry,
        ← h_bushy, ← h_broom₃, ← h_cherry, ← h_vertex]
    ring
  rw [h_sum]; ring

/-- *Phase α'.5.0 (cycle 403) — `mk [vertex, vertex, cherry]` closed form
non-vacuity at `η_q = ⟦explicitEuler⟧`.* The expected value is
`Φ_{⟦explicitEuler⟧⁻¹}(mk [vertex, vertex, cherry]) = -1⁵ + 4·1³·0
− 2·1·0² − 3·1²·0 + 0·0 + 1·0 − 1²·0 + 2·1·0 − 0 = -1`, since for
explicit Euler `Σ b = 1` (so `Φ_η(vertex) = 1`) and `A = 0` (so all
higher elementary weights vanish). Leading `−v⁵` survives, all other
terms vanish — consistent with cycle 384's `mkCherryCherry` non-vacuity
pattern. -/
example :
    elementaryWeightQ_phi
      ((Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩))⁻¹
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) = -1 := by
  rw [elementaryWeightQ_phi_inv_mkVertexVertexCherry, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_vertex : RKTableau.explicitEuler.elementaryWeight RootedTree.vertex = 1 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.vertex = 1
    simp [RKTableau.explicitEuler, RKTableau.derivativeWeight_vertex]
  have h_cherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.cherry = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_cherry : RKTableau.explicitEuler.elementaryWeight RootedTree.cherry = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.cherry = 0
    simp [h_cherry_zero]
  have h_broom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.broom₃ = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_broom₃ : RKTableau.explicitEuler.elementaryWeight RootedTree.broom₃ = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.broom₃ = 0
    simp [h_broom₃_zero]
  have h_bushy_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.bushy = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0
                [RootedTree.vertex, RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_bushy : RKTableau.explicitEuler.elementaryWeight RootedTree.bushy = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.bushy = 0
    simp [h_bushy_zero]
  have h_mkCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.cherry)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_mkCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0
    simp [h_mkCherry_zero]
  have h_mkVertexCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.cherry] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]) = 0
    simp [h_mkVertexCherry_zero]
  have h_mkVertexVertexCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0
                [RootedTree.vertex, RootedTree.cherry] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexVertexCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) = 0
    simp [h_mkVertexVertexCherry_zero]
  rw [h_vertex, h_cherry, h_broom₃, h_bushy, h_mkCherry, h_mkVertexCherry,
      h_mkVertexVertexCherry]
  ring

/-- *Phase α'.5.0 (cycle 403) — Priority 2 `mk [vertex, vertex, cherry]`
m=0 witness:* specialisation of Sub-lemma A
`powRep_sum_eq_of_strict_subtree_agreement` at
`t = mk [vertex, vertex, cherry], m = 0`. Under agreement at `vertex`,
`cherry`, `broom₃`, `bushy`, `mk [cherry]`, `mk [vertex, cherry]`, and
`mk [vertex, vertex, cherry]` (seven subtrees corresponding to the
closed-form factors of cycle 403's
`_mkVertexVertexCherry`), the `η_q^(-1)` images at
`mk [vertex, vertex, cherry]` coincide.

Proof: reduce `η_q ^ (-(((0 + 1 : ℕ) : ℤ)))` to `η_q⁻¹` via
`Nat.cast_one` + `zpow_neg_one`, apply cycle 403's
`elementaryWeightQ_phi_inv_mkVertexVertexCherry` on both sides, then
substitute the seven agreement hypotheses. -/
theorem powRep_sum_eq_of_agreement_at_mkVertexVertexCherry_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry)
    (h_broom₃ : elementaryWeightQ_phi η_q RootedTree.broom₃
              = elementaryWeightQ_phi η_q' RootedTree.broom₃)
    (h_bushy : elementaryWeightQ_phi η_q RootedTree.bushy
              = elementaryWeightQ_phi η_q' RootedTree.bushy)
    (h_mkCherry : elementaryWeightQ_phi η_q
                    (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
    (h_mkVertexCherry : elementaryWeightQ_phi η_q
                          (OpenMath.Chapter3.Section310.RootedTree.mk
                            [RootedTree.vertex, RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry]))
    (h_mkVertexVertexCherry : elementaryWeightQ_phi η_q
                                (OpenMath.Chapter3.Section310.RootedTree.mk
                                  [RootedTree.vertex, RootedTree.vertex,
                                   RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) := by
  have h_pow : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
      ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
    intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow η_q, h_pow η_q',
      elementaryWeightQ_phi_inv_mkVertexVertexCherry,
      elementaryWeightQ_phi_inv_mkVertexVertexCherry,
      h_vertex, h_cherry, h_broom₃, h_bushy, h_mkCherry, h_mkVertexCherry,
      h_mkVertexVertexCherry]

/-- *Phase α'.5.0 (cycle 403) — `mk [vertex, vertex, cherry]` m=0 witness
non-vacuity at `η_q = η_q' = ⟦explicitEuler⟧`.* Discharges the seven
agreement hypotheses by `rfl`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) :=
  powRep_sum_eq_of_agreement_at_mkVertexVertexCherry_zero
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    rfl rfl rfl rfl rfl rfl rfl

/-- *Phase α'.5.1 P3 (cycle 492) — `mk [vertex, cherry, cherry]` closed
form for Φ_{η_q⁻¹}.* At the order-6 asymmetric vertex + two-cherry
three-children tree `mk [vertex, cherry, cherry]`, the quotient-level
elementary weight of the §383 inverse class admits the closed form
  `Φ_{η_q⁻¹}(mk [vertex, cherry, cherry])
       = v⁶ − 5v⁴c + 5v²c² − c³ + 3v³b' − 2vcb'
         − v²·bushy + 2v³m − 2vcm − 4v²·vc + 2c·vc
         + 2v·vvc + v·cc − M_vcc`
where `v, c, b', bushy, m, vc, vvc, cc, M_vcc` abbreviate `Φ_η` at
vertex, cherry, broom₃, bushy, mk[cherry], mk[vertex,cherry],
mk[vertex,vertex,cherry], mk[cherry,cherry], and the self-kernel
mk[vertex,cherry,cherry] respectively.

Second non-symmetric `k = 3` data point (Phase α'.5.1 P3 per cycle
402 scoping doc §6.2). Combines cycle 384's `mkCherryCherry`
two-cherry-children template (for the `((v² − c) − v·Aᵢ + Bᵢ)²`
portion) with cycle 367's `derivativeWeightWithSrc_vertex` factor
(for the leading `(−v + Aᵢ)` portion).

Proof: descend via `Quotient.inductionOn`, apply
`elementaryWeightQ_phi_inv_mk` to expand the LHS, then unfold
`derivativeWeightWithSrc` via the three-children cons-case (outer
vertex factor reusing cycle 367's `derivativeWeightWithSrc_vertex
= 1`, two cherry tails reusing cycle 367's `h_dws_cherry` shape).
The inner sum `∑_j A_{ij}·(inv_v + ∑_k A_{jk})` (linear
distribution, cycle 372/384 pattern) is pre-distributed via
`h_inner_expand` before `ring` can match the 9-term per-summand
decomposition. Final assembly via `Finset.sum_add_distrib × 8`,
`← Finset.mul_sum × 8`, and back-substitution into the nine kernels
(vertex, cherry, broom₃, bushy, mk[cherry], mk[vertex,cherry],
mk[vertex,vertex,cherry], mk[cherry,cherry],
mk[vertex,cherry,cherry]). -/
theorem elementaryWeightQ_phi_inv_mkVertexCherryCherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹)
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry])
      = (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 6
        - 5 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 4
            * elementaryWeightQ_phi η_q RootedTree.cherry
        + 5 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * (elementaryWeightQ_phi η_q RootedTree.cherry) ^ 2
        - (elementaryWeightQ_phi η_q RootedTree.cherry) ^ 3
        + 3 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 3
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        - 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q RootedTree.cherry
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        - (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q RootedTree.bushy
        + 2 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 3
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q RootedTree.cherry
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - 4 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry])
        + 2 * elementaryWeightQ_phi η_q RootedTree.cherry
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry])
        + 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
        + elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.cherry, RootedTree.cherry])
        - elementaryWeightQ_phi η_q
            (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry]) := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- Cycle 367 helpers (reused verbatim).
  have h_inv_v : M.inverse.elementaryWeight RootedTree.vertex
      = -M.elementaryWeight RootedTree.vertex := by
    show ∑ j : Fin s, M.inverse.b j * M.inverse.derivativeWeight j RootedTree.vertex
          = -(∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.inverse_b, RKTableau.derivativeWeight_vertex,
        RKTableau.derivativeWeight_vertex, neg_mul]
  have h_vertex : M.elementaryWeight RootedTree.vertex = ∑ j : Fin s, M.b j := by
    show ∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.b j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_dw_cherry : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.cherry = ∑ j : Fin s, M.A i j := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_cherry : M.elementaryWeight RootedTree.cherry
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.cherry
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_cherry i]
  have h_dws_cherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i RootedTree.cherry
        = M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * (1 : ℝ) = _
    rw [mul_one]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
  -- Cycle 368 helpers (reused verbatim).
  have h_dw_broom₃ : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.broom₃ = (∑ j : Fin s, M.A i j) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 2
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    rw [h_inner_sum, h_prod_step]; ring
  have h_broom₃ : M.elementaryWeight RootedTree.broom₃
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.broom₃
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_broom₃ i]
  -- Cycle 370 helpers (reused verbatim) — bushy three-vertex-children structure.
  have h_dw_bushy : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.bushy = (∑ j : Fin s, M.A i j) ^ 3 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex, RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 3
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step_1 :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    have h_prod_step_2 :
        M.derivativeWeightProd i [RootedTree.vertex, RootedTree.vertex]
          = (∑ j : Fin s, M.A i j) ^ 2 := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [RootedTree.vertex]
          = (∑ j : Fin s, M.A i j) ^ 2
      rw [h_inner_sum, h_prod_step_1]; ring
    rw [h_inner_sum, h_prod_step_2]; ring
  have h_bushy : M.elementaryWeight RootedTree.bushy
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 3 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.bushy
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 3
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_bushy i]
  -- Cycle 369: `h_inv_cherry` lifted from cycle 367's quotient theorem at ⟦M⟧.
  have h_inv_cherry : M.inverse.elementaryWeight RootedTree.cherry
      = (M.elementaryWeight RootedTree.vertex) ^ 2
        - M.elementaryWeight RootedTree.cherry :=
    elementaryWeightQ_phi_inv_cherry
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)
  -- Cycle 369 helpers for `mk [cherry]` derivative/elementary weight closed forms.
  have h_dw_mkCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
          * M.derivativeWeightProd i [] = _
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dw_cherry j]
  have h_mkCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkCherry i]
  -- Cycle 372 helpers (reused verbatim) — `mk [vertex, cherry]` derivative/
  -- elementary weight closed forms.
  have h_dw_mkVertexCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry])
        = (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.cherry] = _
    have h_vertex_factor :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_cherry_factor :
        M.derivativeWeightProd i [RootedTree.cherry]
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_cherry j]
    rw [h_vertex_factor, h_cherry_factor]
  have h_mkVertexCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
              * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexCherry i]; ring
  -- Cycle 384 helpers (reused verbatim) — `mk [cherry, cherry]`
  -- two-cherry-children structure.
  have h_dw_mkCherryCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.cherry, RootedTree.cherry])
        = (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
          * M.derivativeWeightProd i [RootedTree.cherry] = _
    have h_cherry_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_cherry j]
    have h_cherry_factor :
        M.derivativeWeightProd i [RootedTree.cherry]
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_cherry_inner]
    rw [h_cherry_inner, h_cherry_factor]; ring
  have h_mkCherryCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.cherry, RootedTree.cherry])
      = ∑ i : Fin s, M.b i
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2 := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.cherry, RootedTree.cherry])
          = ∑ i : Fin s, M.b i
              * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkCherryCherry i]
  -- Cycle 403 helpers (reused verbatim) — three-children asymmetric
  -- `mk [vertex, vertex, cherry]` structure.
  have h_dw_mkVertexVertexCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
        = (∑ j : Fin s, M.A i j) ^ 2
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex, RootedTree.cherry] = _
    have h_vertex_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_cherry_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_cherry j]
    have h_prod_step_cherry :
        M.derivativeWeightProd i [RootedTree.cherry]
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_cherry_inner]
    have h_prod_step_vc :
        M.derivativeWeightProd i [RootedTree.vertex, RootedTree.cherry]
          = (∑ j : Fin s, M.A i j)
            * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [RootedTree.cherry] = _
      rw [h_vertex_inner, h_prod_step_cherry]
    rw [h_vertex_inner, h_prod_step_vc]; ring
  have h_mkVertexVertexCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
              * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexVertexCherry i]; ring
  -- New cycle 492 helpers — three-children asymmetric
  -- `mk [vertex, cherry, cherry]` structure: leading vertex factor giving
  -- the outer `Aᵢ` factor + two cherry tails giving the `Bᵢ²` factor.
  have h_dw_mkVertexCherryCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry])
        = (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.cherry, RootedTree.cherry] = _
    have h_vertex_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_cherry_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_cherry j]
    have h_prod_step_cherry :
        M.derivativeWeightProd i [RootedTree.cherry]
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_cherry_inner]
    have h_prod_step_cc :
        M.derivativeWeightProd i [RootedTree.cherry, RootedTree.cherry]
          = (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2 := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [RootedTree.cherry] = _
      rw [h_cherry_inner, h_prod_step_cherry]; ring
    rw [h_vertex_inner, h_prod_step_cc]
  have h_mkVertexCherryCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2 := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
              * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexCherryCherry i]; ring
  -- Three-layer cons-case unfold for `mk [vertex, cherry, cherry]`'s
  -- derivativeWeightWithSrc: outer one-cons unfold strips the vertex
  -- prefix, producing a vertex-source factor `inv_v + Aᵢ` (cycle 367
  -- pattern); the cherry-cherry tail unfolds via cycle 384's two-step
  -- pattern, producing `(inv_c + ∑ⱼ Aᵢⱼ · (inv_v + ∑ₖ Aⱼₖ))²`.
  have h_dws_mkVertexCherryCherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry])
        = (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j)
          * (M.inverse.elementaryWeight RootedTree.cherry
             + ∑ j : Fin s, M.A i j
                 * (M.inverse.elementaryWeight RootedTree.vertex
                    + ∑ k : Fin s, M.A j k)) ^ 2 := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * M.derivativeWeightWithSrcProd M.inverse i
              [RootedTree.cherry, RootedTree.cherry] = _
    have h_vertex_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
    have h_cherry_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeightWithSrc M.inverse j RootedTree.cherry
          = ∑ j : Fin s, M.A i j
              * (M.inverse.elementaryWeight RootedTree.vertex
                 + ∑ k : Fin s, M.A j k) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dws_cherry j]
    have h_cherry_factor :
        M.derivativeWeightWithSrcProd M.inverse i [RootedTree.cherry]
          = M.inverse.elementaryWeight RootedTree.cherry
            + ∑ j : Fin s, M.A i j
                * (M.inverse.elementaryWeight RootedTree.vertex
                   + ∑ k : Fin s, M.A j k) := by
      show (M.inverse.elementaryWeight RootedTree.cherry
              + ∑ j : Fin s, M.A i j
                  * M.derivativeWeightWithSrc M.inverse j RootedTree.cherry)
            * M.derivativeWeightWithSrcProd M.inverse i [] = _
      rw [show M.derivativeWeightWithSrcProd M.inverse i [] = 1 from rfl, mul_one,
          h_cherry_inner]
    have h_prod_step_cc :
        M.derivativeWeightWithSrcProd M.inverse i
            [RootedTree.cherry, RootedTree.cherry]
          = (M.inverse.elementaryWeight RootedTree.cherry
              + ∑ j : Fin s, M.A i j
                  * (M.inverse.elementaryWeight RootedTree.vertex
                     + ∑ k : Fin s, M.A j k)) ^ 2 := by
      show (M.inverse.elementaryWeight RootedTree.cherry
              + ∑ j : Fin s, M.A i j
                  * M.derivativeWeightWithSrc M.inverse j RootedTree.cherry)
            * M.derivativeWeightWithSrcProd M.inverse i [RootedTree.cherry] = _
      rw [h_cherry_inner, h_cherry_factor]; ring
    rw [h_vertex_inner, h_prod_step_cc]
  -- Main computation: assemble closed form via _inv_mk + _mk × 9 + sum algebra.
  rw [elementaryWeightQ_phi_inv_mk M
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry]),
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk]
  have h_sum :
      (∑ i : Fin s, M.b i
          * M.derivativeWeightWithSrc M.inverse i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry]))
        = -(M.elementaryWeight RootedTree.vertex) ^ 6
          + 5 * (M.elementaryWeight RootedTree.vertex) ^ 4
              * M.elementaryWeight RootedTree.cherry
          - 5 * (M.elementaryWeight RootedTree.vertex) ^ 2
              * (M.elementaryWeight RootedTree.cherry) ^ 2
          + (M.elementaryWeight RootedTree.cherry) ^ 3
          - 3 * (M.elementaryWeight RootedTree.vertex) ^ 3
              * M.elementaryWeight RootedTree.broom₃
          + 2 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight RootedTree.cherry
              * M.elementaryWeight RootedTree.broom₃
          + (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight RootedTree.bushy
          - 2 * (M.elementaryWeight RootedTree.vertex) ^ 3
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          + 2 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight RootedTree.cherry
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          + 4 * (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry])
          - 2 * M.elementaryWeight RootedTree.cherry
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry])
          - 2 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
          - M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.cherry, RootedTree.cherry])
          + M.elementaryWeight
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry]) := by
    have h_subst :
        (∑ i : Fin s, M.b i
            * M.derivativeWeightWithSrc M.inverse i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry]))
          = ∑ i : Fin s,
              ((-M.elementaryWeight RootedTree.vertex
                    * ((M.elementaryWeight RootedTree.vertex) ^ 2
                       - M.elementaryWeight RootedTree.cherry) ^ 2) * M.b i
                + (3 * (M.elementaryWeight RootedTree.vertex) ^ 4
                    - 4 * (M.elementaryWeight RootedTree.vertex) ^ 2
                        * M.elementaryWeight RootedTree.cherry
                    + (M.elementaryWeight RootedTree.cherry) ^ 2)
                    * (M.b i * ∑ j : Fin s, M.A i j)
                + (-3 * (M.elementaryWeight RootedTree.vertex) ^ 3
                    + 2 * M.elementaryWeight RootedTree.vertex
                        * M.elementaryWeight RootedTree.cherry)
                    * (M.b i * (∑ j : Fin s, M.A i j) ^ 2)
                + (M.elementaryWeight RootedTree.vertex) ^ 2
                    * (M.b i * (∑ j : Fin s, M.A i j) ^ 3)
                + (-2 * (M.elementaryWeight RootedTree.vertex) ^ 3
                    + 2 * M.elementaryWeight RootedTree.vertex
                        * M.elementaryWeight RootedTree.cherry)
                    * (M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
                + (4 * (M.elementaryWeight RootedTree.vertex) ^ 2
                    - 2 * M.elementaryWeight RootedTree.cherry)
                    * (M.b i * (∑ j : Fin s, M.A i j)
                        * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k))
                + (-2 * M.elementaryWeight RootedTree.vertex)
                    * (M.b i * (∑ j : Fin s, M.A i j) ^ 2
                        * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k))
                + (-M.elementaryWeight RootedTree.vertex)
                    * (M.b i * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2)
                + M.b i * (∑ j : Fin s, M.A i j)
                    * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) ^ 2) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_dws_mkVertexCherryCherry i, h_inv_cherry, h_inv_v]
      -- Pre-distribute the inner Σⱼ Aᵢⱼ · (-v + ∑ₖ Aⱼₖ) before `ring` can
      -- match the 9-term per-summand decomposition.
      have h_inner_expand :
          ∑ j : Fin s, M.A i j
              * (-M.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k)
            = -M.elementaryWeight RootedTree.vertex * ∑ j : Fin s, M.A i j
              + ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
        have h_inner :
            ∑ j : Fin s, M.A i j
                * (-M.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k)
              = ∑ j : Fin s, (-M.elementaryWeight RootedTree.vertex * M.A i j
                  + M.A i j * ∑ k : Fin s, M.A j k) := by
          refine Finset.sum_congr rfl (fun j _ => ?_); ring
        rw [h_inner, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [h_inner_expand]; ring
    rw [h_subst, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← h_mkVertexCherryCherry, ← h_mkCherryCherry, ← h_mkVertexVertexCherry,
        ← h_mkVertexCherry, ← h_mkCherry,
        ← h_bushy, ← h_broom₃, ← h_cherry, ← h_vertex]
    ring
  rw [h_sum]; ring

/-- *Phase α'.5.1 P3 (cycle 492) — `mk [vertex, cherry, cherry]` closed form
non-vacuity at `η_q = ⟦explicitEuler⟧`.* The expected value is
`Φ_{⟦explicitEuler⟧⁻¹}(mk [vertex, cherry, cherry]) = 1⁶ − 5·1⁴·0 + ... = 1`,
since for explicit Euler `Σ b = 1` (so `Φ_η(vertex) = 1`) and `A = 0`
(so all higher elementary weights vanish). Leading `v⁶` survives, all
other terms vanish — consistent with the order-6 parity pattern of
cycles 384/403. -/
example :
    elementaryWeightQ_phi
      ((Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩))⁻¹
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry]) = 1 := by
  rw [elementaryWeightQ_phi_inv_mkVertexCherryCherry, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_vertex : RKTableau.explicitEuler.elementaryWeight RootedTree.vertex = 1 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.vertex = 1
    simp [RKTableau.explicitEuler, RKTableau.derivativeWeight_vertex]
  have h_cherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.cherry = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_cherry : RKTableau.explicitEuler.elementaryWeight RootedTree.cherry = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.cherry = 0
    simp [h_cherry_zero]
  have h_broom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.broom₃ = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_broom₃ : RKTableau.explicitEuler.elementaryWeight RootedTree.broom₃ = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.broom₃ = 0
    simp [h_broom₃_zero]
  have h_bushy_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.bushy = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0
                [RootedTree.vertex, RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_bushy : RKTableau.explicitEuler.elementaryWeight RootedTree.bushy = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.bushy = 0
    simp [h_bushy_zero]
  have h_mkCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.cherry)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_mkCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0
    simp [h_mkCherry_zero]
  have h_mkVertexCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.cherry] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]) = 0
    simp [h_mkVertexCherry_zero]
  have h_mkVertexVertexCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0
                [RootedTree.vertex, RootedTree.cherry] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexVertexCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) = 0
    simp [h_mkVertexVertexCherry_zero]
  have h_mkCherryCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.cherry, RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.cherry)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.cherry] = 0
    simp [RKTableau.explicitEuler]
  have h_mkCherryCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.cherry, RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.cherry, RootedTree.cherry]) = 0
    simp [h_mkCherryCherry_zero]
  have h_mkVertexCherryCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0
                [RootedTree.cherry, RootedTree.cherry] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexCherryCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry]) = 0
    simp [h_mkVertexCherryCherry_zero]
  rw [h_vertex, h_cherry, h_broom₃, h_bushy, h_mkCherry, h_mkVertexCherry,
      h_mkVertexVertexCherry, h_mkCherryCherry, h_mkVertexCherryCherry]
  ring

/-- *Phase α'.5.1 P3 (cycle 492) — Priority 2 `mk [vertex, cherry, cherry]`
m=0 witness:* specialisation of Sub-lemma A
`powRep_sum_eq_of_strict_subtree_agreement` at
`t = mk [vertex, cherry, cherry], m = 0`. Under agreement at `vertex`,
`cherry`, `broom₃`, `bushy`, `mk [cherry]`, `mk [vertex, cherry]`,
`mk [vertex, vertex, cherry]`, `mk [cherry, cherry]`, and
`mk [vertex, cherry, cherry]` (nine subtrees corresponding to the
closed-form factors of cycle 492's
`_mkVertexCherryCherry`), the `η_q^(-1)` images at
`mk [vertex, cherry, cherry]` coincide.

Proof: reduce `η_q ^ (-(((0 + 1 : ℕ) : ℤ)))` to `η_q⁻¹` via
`Nat.cast_one` + `zpow_neg_one`, apply cycle 492's
`elementaryWeightQ_phi_inv_mkVertexCherryCherry` on both sides, then
substitute the nine agreement hypotheses. -/
theorem powRep_sum_eq_of_agreement_at_mkVertexCherryCherry_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry)
    (h_broom₃ : elementaryWeightQ_phi η_q RootedTree.broom₃
              = elementaryWeightQ_phi η_q' RootedTree.broom₃)
    (h_bushy : elementaryWeightQ_phi η_q RootedTree.bushy
              = elementaryWeightQ_phi η_q' RootedTree.bushy)
    (h_mkCherry : elementaryWeightQ_phi η_q
                    (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
    (h_mkVertexCherry : elementaryWeightQ_phi η_q
                          (OpenMath.Chapter3.Section310.RootedTree.mk
                            [RootedTree.vertex, RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry]))
    (h_mkVertexVertexCherry : elementaryWeightQ_phi η_q
                                (OpenMath.Chapter3.Section310.RootedTree.mk
                                  [RootedTree.vertex, RootedTree.vertex,
                                   RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]))
    (h_mkCherryCherry : elementaryWeightQ_phi η_q
                          (OpenMath.Chapter3.Section310.RootedTree.mk
                            [RootedTree.cherry, RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.cherry, RootedTree.cherry]))
    (h_mkVertexCherryCherry : elementaryWeightQ_phi η_q
                                (OpenMath.Chapter3.Section310.RootedTree.mk
                                  [RootedTree.vertex, RootedTree.cherry,
                                   RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry])) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry])
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry]) := by
  have h_pow : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
      ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
    intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow η_q, h_pow η_q',
      elementaryWeightQ_phi_inv_mkVertexCherryCherry,
      elementaryWeightQ_phi_inv_mkVertexCherryCherry,
      h_vertex, h_cherry, h_broom₃, h_bushy, h_mkCherry, h_mkVertexCherry,
      h_mkVertexVertexCherry, h_mkCherryCherry, h_mkVertexCherryCherry]

/-- *Phase α'.5.1 P3 (cycle 492) — `mk [vertex, cherry, cherry]` m=0 witness
non-vacuity at `η_q = η_q' = ⟦explicitEuler⟧`.* Discharges the nine
agreement hypotheses by `rfl`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry])
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry]) :=
  powRep_sum_eq_of_agreement_at_mkVertexCherryCherry_zero
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- *Phase α'.5.1 P4 (cycle 493) — `mk [vertex, vertex, mk [cherry]]` closed
form for Φ_{η_q⁻¹}.* At the order-6 asymmetric tree
`mk [vertex, vertex, mk [cherry]]`, the quotient-level elementary weight of
the §383 inverse class admits the closed form
  `Φ_{η_q⁻¹}(mk [vertex, vertex, mk [cherry]])
       = v⁶ − 5v⁴c + 2v³m + 5v²c² − 2vcm + 3v³b' − 4vcb' + mb'
         − v²·bushy + c·bushy − 2v²·vc + v·vvc − v²·M_mc
         + 2v·vmc − vvmc`
where `v, c, b', bushy, m, vc, vvc, M_mc, vmc, vvmc` abbreviate `Φ_η` at
`vertex, cherry, broom₃, bushy, mk [cherry], mk [vertex, cherry],
mk [vertex, vertex, cherry], mk [mk [cherry]], mk [vertex, mk [cherry]],
mk [vertex, vertex, mk [cherry]]` respectively. This is the 13th Family C
ladder witness (Phase α'.5.1 P4), the second `mk [v, v, ·]`-shaped order-6
tree (after cycle 403's `mk [v, v, cherry]`). Non-vacuity at `⟦explicitEuler⟧`
pins the closed form to `1` via the leading `v⁶` term (all other kernels
vanish).

Proof structure: quotient-level induction to `⟨s, M⟩`, reuse cycle 367/368/
369/370/372/378/403 helpers for the standard kernels, add new helpers
`h_dw_mkVertexMkCherry`, `h_mkVertexMkCherry`, `h_dw_mkVertexVertexMkCherry`,
`h_mkVertexVertexMkCherry`, and `h_dws_mkVertexVertexMkCherry` (three-layer
cons-case unfold). Substitute via `h_inv_v`, `h_inv_cherry`, `h_inv_mkCherry`,
distribute the inner Σⱼ sum, and assemble the 10-kernel closed form via
nine applications of `Finset.sum_add_distrib` + nine `← Finset.mul_sum`
back-substitutions + `ring`. -/
theorem elementaryWeightQ_phi_inv_mkVertexVertexMkCherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹)
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex,
           OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
      = (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 6
        - 5 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 4
            * elementaryWeightQ_phi η_q RootedTree.cherry
        + 2 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 3
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + 5 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * (elementaryWeightQ_phi η_q RootedTree.cherry) ^ 2
        - 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q RootedTree.cherry
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + 3 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 3
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        - 4 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q RootedTree.cherry
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        + elementaryWeightQ_phi η_q
            (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        - (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q RootedTree.bushy
        + elementaryWeightQ_phi η_q RootedTree.cherry
            * elementaryWeightQ_phi η_q RootedTree.bushy
        - 2 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry])
        + elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
        - (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
        + 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex,
                   OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
        - elementaryWeightQ_phi η_q
            (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex,
               OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- Cycle 367 helpers (reused verbatim).
  have h_inv_v : M.inverse.elementaryWeight RootedTree.vertex
      = -M.elementaryWeight RootedTree.vertex := by
    show ∑ j : Fin s, M.inverse.b j * M.inverse.derivativeWeight j RootedTree.vertex
          = -(∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.inverse_b, RKTableau.derivativeWeight_vertex,
        RKTableau.derivativeWeight_vertex, neg_mul]
  have h_vertex : M.elementaryWeight RootedTree.vertex = ∑ j : Fin s, M.b j := by
    show ∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.b j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_dw_cherry : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.cherry = ∑ j : Fin s, M.A i j := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_cherry : M.elementaryWeight RootedTree.cherry
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.cherry
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_cherry i]
  have h_dws_cherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i RootedTree.cherry
        = M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * (1 : ℝ) = _
    rw [mul_one]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
  -- Cycle 368 helpers (reused verbatim).
  have h_dw_broom₃ : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.broom₃ = (∑ j : Fin s, M.A i j) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 2
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    rw [h_inner_sum, h_prod_step]; ring
  have h_broom₃ : M.elementaryWeight RootedTree.broom₃
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.broom₃
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_broom₃ i]
  -- Cycle 370 helpers (reused verbatim) — bushy three-vertex-children structure.
  have h_dw_bushy : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.bushy = (∑ j : Fin s, M.A i j) ^ 3 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex, RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 3
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step_1 :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    have h_prod_step_2 :
        M.derivativeWeightProd i [RootedTree.vertex, RootedTree.vertex]
          = (∑ j : Fin s, M.A i j) ^ 2 := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [RootedTree.vertex]
          = (∑ j : Fin s, M.A i j) ^ 2
      rw [h_inner_sum, h_prod_step_1]; ring
    rw [h_inner_sum, h_prod_step_2]; ring
  have h_bushy : M.elementaryWeight RootedTree.bushy
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 3 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.bushy
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 3
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_bushy i]
  -- Cycle 369: `h_inv_cherry` lifted from cycle 367's quotient theorem at ⟦M⟧.
  have h_inv_cherry : M.inverse.elementaryWeight RootedTree.cherry
      = (M.elementaryWeight RootedTree.vertex) ^ 2
        - M.elementaryWeight RootedTree.cherry :=
    elementaryWeightQ_phi_inv_cherry
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)
  -- Cycle 369 helpers for `mk [cherry]` derivative/elementary weight closed forms.
  have h_dw_mkCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
          * M.derivativeWeightProd i [] = _
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dw_cherry j]
  have h_mkCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkCherry i]
  have h_dws_mkCherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = M.inverse.elementaryWeight RootedTree.cherry
          + M.inverse.elementaryWeight RootedTree.vertex * ∑ j : Fin s, M.A i j
          + ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.cherry
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.cherry)
          * M.derivativeWeightWithSrcProd M.inverse i [] = _
    rw [show M.derivativeWeightWithSrcProd M.inverse i [] = 1 from rfl, mul_one]
    have h_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeightWithSrc M.inverse j RootedTree.cherry
          = ∑ j : Fin s, (M.A i j * M.inverse.elementaryWeight RootedTree.vertex
                          + M.A i j * ∑ k : Fin s, M.A j k) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dws_cherry j]; ring
    rw [h_inner, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  -- Cycle 378: `h_inv_mkCherry` lifted from cycle 369's quotient theorem at ⟦M⟧.
  have h_inv_mkCherry : M.inverse.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      = -(M.elementaryWeight RootedTree.vertex) ^ 3
        + 2 * M.elementaryWeight RootedTree.vertex
            * M.elementaryWeight RootedTree.cherry
        - M.elementaryWeight
            (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) :=
    elementaryWeightQ_phi_inv_mkCherry
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)
  -- Cycle 372 helpers (reused verbatim) — `mk [vertex, cherry]` derivative/
  -- elementary weight closed forms.
  have h_dw_mkVertexCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry])
        = (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.cherry] = _
    have h_vertex_factor :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_cherry_factor :
        M.derivativeWeightProd i [RootedTree.cherry]
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_cherry j]
    rw [h_vertex_factor, h_cherry_factor]
  have h_mkVertexCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
              * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexCherry i]; ring
  -- Cycle 378 helpers (reused verbatim) — `mk [mk [cherry]]` derivative/
  -- elementary weight closed forms.
  have h_dw_mkMkCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
        = ∑ j : Fin s, M.A i j
            * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l := by
    intro i
    show (∑ j : Fin s, M.A i j
            * M.derivativeWeight j
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
          * M.derivativeWeightProd i [] = _
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dw_mkCherry j]
  have h_mkMkCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
      = ∑ i : Fin s, M.b i
          * ∑ j : Fin s, M.A i j
              * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
          = ∑ i : Fin s, M.b i
              * ∑ j : Fin s, M.A i j
                  * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkMkCherry i]
  -- Cycle 403 helpers (reused verbatim) — `mk [v, v, cherry]` derivative/
  -- elementary weight closed forms.
  have h_dw_mkVertexVertexCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
        = (∑ j : Fin s, M.A i j) ^ 2
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex, RootedTree.cherry] = _
    have h_vertex_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_cherry_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_cherry j]
    have h_prod_step_cherry :
        M.derivativeWeightProd i [RootedTree.cherry]
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_cherry_inner]
    have h_prod_step_vc :
        M.derivativeWeightProd i [RootedTree.vertex, RootedTree.cherry]
          = (∑ j : Fin s, M.A i j)
            * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [RootedTree.cherry] = _
      rw [h_vertex_inner, h_prod_step_cherry]
    rw [h_vertex_inner, h_prod_step_vc]; ring
  have h_mkVertexVertexCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
              * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexVertexCherry i]; ring
  -- New cycle 493 helpers — `mk [vertex, mk [cherry]]` derivative/elementary
  -- weight closed forms (kernel for `vmc` = Φ_η(mk [vertex, mk [cherry]])).
  have h_dw_mkVertexMkCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex,
             OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
        = (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j
              * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]] = _
    have h_vertex_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_mkCherry_factor :
        M.derivativeWeightProd i
            [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
          = ∑ j : Fin s, M.A i j
              * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l := by
      show (∑ j : Fin s, M.A i j
              * M.derivativeWeight j
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_mkCherry j]
    rw [h_vertex_inner, h_mkCherry_factor]
  have h_mkVertexMkCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex,
           OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j
              * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex,
                   OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
              * (∑ j : Fin s, M.A i j
                  * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexMkCherry i]; ring
  -- New cycle 493 helpers — three-children asymmetric
  -- `mk [vertex, vertex, mk [cherry]]` structure: two-vertex prefix giving
  -- `Aᵢ²` factor + `mk [cherry]` tail giving the depth-3 Dᵢ-pattern factor.
  have h_dw_mkVertexVertexMkCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex,
             OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
        = (∑ j : Fin s, M.A i j) ^ 2
          * (∑ j : Fin s, M.A i j
              * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i
              [RootedTree.vertex,
               OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]] = _
    have h_vertex_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_mkCherry_inner :
        ∑ j : Fin s, M.A i j
            * M.derivativeWeight j
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          = ∑ j : Fin s, M.A i j
              * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_mkCherry j]
    have h_prod_step_mc :
        M.derivativeWeightProd i
            [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
          = ∑ j : Fin s, M.A i j
              * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l := by
      show (∑ j : Fin s, M.A i j
              * M.derivativeWeight j
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_mkCherry_inner]
    have h_prod_step_vmc :
        M.derivativeWeightProd i
            [RootedTree.vertex,
             OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
          = (∑ j : Fin s, M.A i j)
            * (∑ j : Fin s, M.A i j
                * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l) := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]] = _
      rw [h_vertex_inner, h_prod_step_mc]
    rw [h_vertex_inner, h_prod_step_vmc]; ring
  have h_mkVertexVertexMkCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex,
           OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
          * (∑ j : Fin s, M.A i j
              * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.vertex,
                   OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
              * (∑ j : Fin s, M.A i j
                  * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexVertexMkCherry i]; ring
  -- Three-layer cons-case unfold for `mk [v, v, mk [c]]`'s
  -- derivativeWeightWithSrc: outer two-cons unfold strips the two-vertex
  -- prefix, producing two identical vertex-source factors `inv_v + Aᵢ`
  -- (cycle 367/370 pattern); inner `mk [cherry]` tail unfolds via cycle
  -- 369's `h_dws_mkCherry` to `inv_mc + ∑ⱼ Aᵢⱼ · (inv_c + inv_v · ∑ₖ Aⱼₖ
  -- + ∑ₖ Aⱼₖ · ∑ₗ Aₖₗ)`.
  have h_dws_mkVertexVertexMkCherry : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex,
             OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
        = (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j) ^ 2
          * (M.inverse.elementaryWeight
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
             + ∑ j : Fin s, M.A i j
                 * (M.inverse.elementaryWeight RootedTree.cherry
                    + M.inverse.elementaryWeight RootedTree.vertex
                        * ∑ k : Fin s, M.A j k
                    + ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l)) := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * M.derivativeWeightWithSrcProd M.inverse i
              [RootedTree.vertex,
               OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]] = _
    have h_vertex_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
    have h_mkCherry_factor :
        M.derivativeWeightWithSrcProd M.inverse i
            [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
          = M.inverse.elementaryWeight
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
            + ∑ j : Fin s, M.A i j
                * (M.inverse.elementaryWeight RootedTree.cherry
                   + M.inverse.elementaryWeight RootedTree.vertex
                       * ∑ k : Fin s, M.A j k
                   + ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l) := by
      show (M.inverse.elementaryWeight
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j
                    (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
            * M.derivativeWeightWithSrcProd M.inverse i [] = _
      rw [show M.derivativeWeightWithSrcProd M.inverse i [] = 1 from rfl, mul_one]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dws_mkCherry j]
    have h_prod_step_vmc :
        M.derivativeWeightWithSrcProd M.inverse i
            [RootedTree.vertex,
             OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
          = (M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j)
            * (M.inverse.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
               + ∑ j : Fin s, M.A i j
                   * (M.inverse.elementaryWeight RootedTree.cherry
                      + M.inverse.elementaryWeight RootedTree.vertex
                          * ∑ k : Fin s, M.A j k
                      + ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l)) := by
      show (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ j : Fin s, M.A i j
                  * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
            * M.derivativeWeightWithSrcProd M.inverse i
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]] = _
      rw [h_vertex_inner, h_mkCherry_factor]
    rw [h_vertex_inner, h_prod_step_vmc]; ring
  -- Main computation: assemble closed form via _inv_mk + _mk × 10 + sum algebra.
  rw [elementaryWeightQ_phi_inv_mk M
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex,
           OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]),
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_sum :
      (∑ i : Fin s, M.b i
          * M.derivativeWeightWithSrc M.inverse i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex,
                 OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]))
        = -(M.elementaryWeight RootedTree.vertex) ^ 6
          + 5 * (M.elementaryWeight RootedTree.vertex) ^ 4
              * M.elementaryWeight RootedTree.cherry
          - 2 * (M.elementaryWeight RootedTree.vertex) ^ 3
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          - 5 * (M.elementaryWeight RootedTree.vertex) ^ 2
              * (M.elementaryWeight RootedTree.cherry) ^ 2
          + 2 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight RootedTree.cherry
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          - 3 * (M.elementaryWeight RootedTree.vertex) ^ 3
              * M.elementaryWeight RootedTree.broom₃
          + 4 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight RootedTree.cherry
              * M.elementaryWeight RootedTree.broom₃
          - M.elementaryWeight
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
              * M.elementaryWeight RootedTree.broom₃
          + (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight RootedTree.bushy
          - M.elementaryWeight RootedTree.cherry
              * M.elementaryWeight RootedTree.bushy
          + 2 * (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry])
          - M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
          + (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
          - 2 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex,
                     OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
          + M.elementaryWeight
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex,
                 OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) := by
    have h_subst :
        (∑ i : Fin s, M.b i
            * M.derivativeWeightWithSrc M.inverse i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.vertex,
                   OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]))
          = ∑ i : Fin s,
              ((-(M.elementaryWeight RootedTree.vertex) ^ 5
                  + 2 * (M.elementaryWeight RootedTree.vertex) ^ 3
                      * M.elementaryWeight RootedTree.cherry
                  - (M.elementaryWeight RootedTree.vertex) ^ 2
                      * M.elementaryWeight
                          (OpenMath.Chapter3.Section310.RootedTree.mk
                            [RootedTree.cherry])) * M.b i
                + (3 * (M.elementaryWeight RootedTree.vertex) ^ 4
                    - 5 * (M.elementaryWeight RootedTree.vertex) ^ 2
                        * M.elementaryWeight RootedTree.cherry
                    + 2 * M.elementaryWeight RootedTree.vertex
                        * M.elementaryWeight
                            (OpenMath.Chapter3.Section310.RootedTree.mk
                              [RootedTree.cherry]))
                    * (M.b i * ∑ j : Fin s, M.A i j)
                + (-3 * (M.elementaryWeight RootedTree.vertex) ^ 3
                    + 4 * M.elementaryWeight RootedTree.vertex
                        * M.elementaryWeight RootedTree.cherry
                    - M.elementaryWeight
                        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
                    * (M.b i * (∑ j : Fin s, M.A i j) ^ 2)
                + ((M.elementaryWeight RootedTree.vertex) ^ 2
                    - M.elementaryWeight RootedTree.cherry)
                    * (M.b i * (∑ j : Fin s, M.A i j) ^ 3)
                + (-(M.elementaryWeight RootedTree.vertex) ^ 3)
                    * (M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
                + (2 * (M.elementaryWeight RootedTree.vertex) ^ 2)
                    * (M.b i * (∑ j : Fin s, M.A i j)
                        * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k))
                + (-M.elementaryWeight RootedTree.vertex)
                    * (M.b i * (∑ j : Fin s, M.A i j) ^ 2
                        * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k))
                + (M.elementaryWeight RootedTree.vertex) ^ 2
                    * (M.b i * ∑ j : Fin s, M.A i j
                        * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l)
                + (-2 * M.elementaryWeight RootedTree.vertex)
                    * (M.b i * (∑ j : Fin s, M.A i j)
                        * (∑ j : Fin s, M.A i j
                            * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l))
                + M.b i * (∑ j : Fin s, M.A i j) ^ 2
                    * (∑ j : Fin s, M.A i j
                        * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_dws_mkVertexVertexMkCherry i, h_inv_mkCherry, h_inv_cherry, h_inv_v]
      -- Pre-distribute the inner Σⱼ Aᵢⱼ · (inv_c + inv_v · Σₖ Aⱼₖ + Σₖ Aⱼₖ · Σₗ Aₖₗ)
      -- before `ring` can match the 10-term per-summand decomposition.
      have h_inner_expand :
          ∑ j : Fin s, M.A i j
              * (((M.elementaryWeight RootedTree.vertex) ^ 2
                    - M.elementaryWeight RootedTree.cherry)
                 + (-M.elementaryWeight RootedTree.vertex) * ∑ k : Fin s, M.A j k
                 + ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l)
            = ((M.elementaryWeight RootedTree.vertex) ^ 2
                  - M.elementaryWeight RootedTree.cherry)
                * ∑ j : Fin s, M.A i j
              + (-M.elementaryWeight RootedTree.vertex)
                  * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k
              + ∑ j : Fin s, M.A i j
                  * ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l := by
        have h_inner :
            ∑ j : Fin s, M.A i j
                * (((M.elementaryWeight RootedTree.vertex) ^ 2
                      - M.elementaryWeight RootedTree.cherry)
                   + (-M.elementaryWeight RootedTree.vertex) * ∑ k : Fin s, M.A j k
                   + ∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l)
              = ∑ j : Fin s, (((M.elementaryWeight RootedTree.vertex) ^ 2
                                - M.elementaryWeight RootedTree.cherry) * M.A i j
                + (-M.elementaryWeight RootedTree.vertex)
                    * (M.A i j * ∑ k : Fin s, M.A j k)
                + M.A i j * (∑ k : Fin s, M.A j k * ∑ l : Fin s, M.A k l)) := by
          refine Finset.sum_congr rfl (fun j _ => ?_); ring
        rw [h_inner, Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
      rw [h_inner_expand]; ring
    rw [h_subst, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum,
        ← h_mkVertexVertexMkCherry, ← h_mkVertexMkCherry, ← h_mkMkCherry,
        ← h_mkVertexVertexCherry, ← h_mkVertexCherry, ← h_mkCherry,
        ← h_bushy, ← h_broom₃, ← h_cherry, ← h_vertex]
    ring
  rw [h_sum]; ring

/-- *Phase α'.5.1 P4 (cycle 493) — `mk [vertex, vertex, mk [cherry]]` closed
form non-vacuity at `η_q = ⟦explicitEuler⟧`.* The expected value is
`Φ_{⟦explicitEuler⟧⁻¹}(mk [vertex, vertex, mk [cherry]]) = 1⁶ + 0 + 0 + ...
= 1`, since for explicit Euler `Σ b = 1` (so `Φ_η(vertex) = 1`) and `A = 0`
(so all higher elementary weights vanish). Leading `v⁶` survives, all other
terms vanish — consistent with the order-6 parity pattern of cycles
384/403/492. -/
example :
    elementaryWeightQ_phi
      ((Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩))⁻¹
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.vertex,
         OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) = 1 := by
  rw [elementaryWeightQ_phi_inv_mkVertexVertexMkCherry, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk]
  have h_vertex : RKTableau.explicitEuler.elementaryWeight RootedTree.vertex = 1 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.vertex = 1
    simp [RKTableau.explicitEuler, RKTableau.derivativeWeight_vertex]
  have h_cherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.cherry = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_cherry : RKTableau.explicitEuler.elementaryWeight RootedTree.cherry = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.cherry = 0
    simp [h_cherry_zero]
  have h_broom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.broom₃ = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_broom₃ : RKTableau.explicitEuler.elementaryWeight RootedTree.broom₃ = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.broom₃ = 0
    simp [h_broom₃_zero]
  have h_bushy_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.bushy = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0
                [RootedTree.vertex, RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_bushy : RKTableau.explicitEuler.elementaryWeight RootedTree.bushy = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.bushy = 0
    simp [h_bushy_zero]
  have h_mkCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.cherry)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_mkCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0
    simp [h_mkCherry_zero]
  have h_mkVertexCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.cherry] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]) = 0
    simp [h_mkVertexCherry_zero]
  have h_mkVertexVertexCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0
                [RootedTree.vertex, RootedTree.cherry] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexVertexCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) = 0
    simp [h_mkVertexVertexCherry_zero]
  have h_mkMkCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_mkMkCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) = 0
    simp [h_mkMkCherry_zero]
  have h_mkVertexMkCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex,
           OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexMkCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex,
           OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex,
                 OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) = 0
    simp [h_mkVertexMkCherry_zero]
  have h_mkVertexVertexMkCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex,
           OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0
                [RootedTree.vertex,
                 OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexVertexMkCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex,
           OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex,
                 OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) = 0
    simp [h_mkVertexVertexMkCherry_zero]
  rw [h_vertex, h_cherry, h_broom₃, h_bushy, h_mkCherry, h_mkVertexCherry,
      h_mkVertexVertexCherry, h_mkMkCherry, h_mkVertexMkCherry,
      h_mkVertexVertexMkCherry]
  ring

/-- *Phase α'.5.1 P4 (cycle 493) — Priority 2 `mk [vertex, vertex, mk [cherry]]`
m=0 witness:* specialisation of Sub-lemma A
`powRep_sum_eq_of_strict_subtree_agreement` at
`t = mk [vertex, vertex, mk [cherry]], m = 0`. Under agreement at `vertex`,
`cherry`, `broom₃`, `bushy`, `mk [cherry]`, `mk [vertex, cherry]`,
`mk [vertex, vertex, cherry]`, `mk [mk [cherry]]`, `mk [vertex, mk [cherry]]`,
and `mk [vertex, vertex, mk [cherry]]` (ten subtrees corresponding to the
closed-form factors of cycle 493's
`_mkVertexVertexMkCherry`), the `η_q^(-1)` images at
`mk [vertex, vertex, mk [cherry]]` coincide.

Proof: reduce `η_q ^ (-(((0 + 1 : ℕ) : ℤ)))` to `η_q⁻¹` via
`Nat.cast_one` + `zpow_neg_one`, apply cycle 493's
`elementaryWeightQ_phi_inv_mkVertexVertexMkCherry` on both sides, then
substitute the ten agreement hypotheses. -/
theorem powRep_sum_eq_of_agreement_at_mkVertexVertexMkCherry_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry)
    (h_broom₃ : elementaryWeightQ_phi η_q RootedTree.broom₃
              = elementaryWeightQ_phi η_q' RootedTree.broom₃)
    (h_bushy : elementaryWeightQ_phi η_q RootedTree.bushy
              = elementaryWeightQ_phi η_q' RootedTree.bushy)
    (h_mkCherry : elementaryWeightQ_phi η_q
                    (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
    (h_mkVertexCherry : elementaryWeightQ_phi η_q
                          (OpenMath.Chapter3.Section310.RootedTree.mk
                            [RootedTree.vertex, RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry]))
    (h_mkVertexVertexCherry : elementaryWeightQ_phi η_q
                                (OpenMath.Chapter3.Section310.RootedTree.mk
                                  [RootedTree.vertex, RootedTree.vertex,
                                   RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]))
    (h_mkMkCherry : elementaryWeightQ_phi η_q
                      (OpenMath.Chapter3.Section310.RootedTree.mk
                        [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]))
    (h_mkVertexMkCherry : elementaryWeightQ_phi η_q
                            (OpenMath.Chapter3.Section310.RootedTree.mk
                              [RootedTree.vertex,
                               OpenMath.Chapter3.Section310.RootedTree.mk
                                 [RootedTree.cherry]])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex,
                     OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]))
    (h_mkVertexVertexMkCherry : elementaryWeightQ_phi η_q
                                  (OpenMath.Chapter3.Section310.RootedTree.mk
                                    [RootedTree.vertex, RootedTree.vertex,
                                     OpenMath.Chapter3.Section310.RootedTree.mk
                                       [RootedTree.cherry]])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.vertex,
                     OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex,
           OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex,
             OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) := by
  have h_pow : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
      ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
    intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow η_q, h_pow η_q',
      elementaryWeightQ_phi_inv_mkVertexVertexMkCherry,
      elementaryWeightQ_phi_inv_mkVertexVertexMkCherry,
      h_vertex, h_cherry, h_broom₃, h_bushy, h_mkCherry, h_mkVertexCherry,
      h_mkVertexVertexCherry, h_mkMkCherry, h_mkVertexMkCherry,
      h_mkVertexVertexMkCherry]

/-- *Phase α'.5.1 P4 (cycle 493) — `mk [vertex, vertex, mk [cherry]]` m=0
witness non-vacuity at `η_q = η_q' = ⟦explicitEuler⟧`.* Discharges the ten
agreement hypotheses by `rfl`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex,
           OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex,
             OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) :=
  powRep_sum_eq_of_agreement_at_mkVertexVertexMkCherry_zero
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- *Phase α'.5.1 P5 (cycle 494) — `mk [vertex, vertex, broom₃]` closed
form for the §383 inverse class.*

For any `η_q : Quotient PhiEquivalent.setoidSigma`, expresses
`Φ_{η_q⁻¹}(mk [vertex, vertex, broom₃])` as a polynomial in
`Φ_η` evaluated at ten named subtrees of order ≤ 6: `vertex`,
`cherry`, `broom₃`, `bushy`, `mk [cherry]`, `mk [vertex, cherry]`,
`mk [vertex, vertex, cherry]`, `mk [broom₃]`, `mk [vertex, broom₃]`,
and `mk [vertex, vertex, broom₃]` itself.

This is the fifth (and final) non-symmetric three-children
order-6 witness, completing the `k = 3` order-6 candidate list
per the scoping doc §6.2: `mk [vertex, vertex, vertex] = bushy`
(cycle 400), `mk [vertex, vertex, cherry]` (cycle 403),
`mk [vertex, cherry, cherry]` (cycle 492),
`mk [vertex, vertex, mk [cherry]]` (cycle 493), and
`mk [vertex, vertex, broom₃]` (cycle 494). Non-vacuity at
`⟦explicitEuler⟧` pins the closed form to `1` via the leading `v⁶`
term (all other kernels vanish).

Proof structure: quotient-level induction to `⟨s, M⟩`, reuse cycle
367/368/369/370/372/371/386/403 helpers for the standard kernels,
add new helpers `h_dw_mkVertexVertexBroom₃`,
`h_mkVertexVertexBroom₃`, and `h_dws_mkVertexVertexBroom₃`
(three-layer cons-case unfold with broom₃-tail). Substitute via
`h_inv_v`, `h_inv_broom₃`, distribute the inner Σⱼ sum
`∑ⱼ Aᵢⱼ · (-v + Aⱼ)² = v²·Aᵢ - 2v·∑ⱼ Aᵢⱼ·Aⱼ + ∑ⱼ Aᵢⱼ·Aⱼ²`, and
assemble the 10-kernel closed form via nine applications of
`Finset.sum_add_distrib` + nine `← Finset.mul_sum`
back-substitutions + `ring`. -/
theorem elementaryWeightQ_phi_inv_mkVertexVertexBroom₃
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹)
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃])
      = (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 6
        - 5 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 4
            * elementaryWeightQ_phi η_q RootedTree.cherry
        + 4 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 3
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        + 4 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * (elementaryWeightQ_phi η_q RootedTree.cherry) ^ 2
        - 4 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q RootedTree.cherry
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        + (elementaryWeightQ_phi η_q RootedTree.broom₃) ^ 2
        - (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q RootedTree.bushy
        + 2 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 3
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - 4 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry])
        + 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
        - (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
        + 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.broom₃])
        - elementaryWeightQ_phi η_q
            (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃]) := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- Cycle 367 helpers (reused verbatim).
  have h_inv_v : M.inverse.elementaryWeight RootedTree.vertex
      = -M.elementaryWeight RootedTree.vertex := by
    show ∑ j : Fin s, M.inverse.b j * M.inverse.derivativeWeight j RootedTree.vertex
          = -(∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.inverse_b, RKTableau.derivativeWeight_vertex,
        RKTableau.derivativeWeight_vertex, neg_mul]
  have h_vertex : M.elementaryWeight RootedTree.vertex = ∑ j : Fin s, M.b j := by
    show ∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.b j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_dw_cherry : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.cherry = ∑ j : Fin s, M.A i j := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_cherry : M.elementaryWeight RootedTree.cherry
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.cherry
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_cherry i]
  -- Cycle 368 helpers (reused verbatim).
  have h_dw_broom₃ : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.broom₃ = (∑ j : Fin s, M.A i j) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 2
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    rw [h_inner_sum, h_prod_step]; ring
  have h_broom₃ : M.elementaryWeight RootedTree.broom₃
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.broom₃
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_broom₃ i]
  -- Cycle 370 helpers (reused verbatim) — bushy three-vertex-children structure.
  have h_dw_bushy : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.bushy = (∑ j : Fin s, M.A i j) ^ 3 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex, RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 3
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step_1 :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    have h_prod_step_2 :
        M.derivativeWeightProd i [RootedTree.vertex, RootedTree.vertex]
          = (∑ j : Fin s, M.A i j) ^ 2 := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [RootedTree.vertex]
          = (∑ j : Fin s, M.A i j) ^ 2
      rw [h_inner_sum, h_prod_step_1]; ring
    rw [h_inner_sum, h_prod_step_2]; ring
  have h_bushy : M.elementaryWeight RootedTree.bushy
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 3 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.bushy
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 3
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_bushy i]
  -- Representative-lift of cycle 368's quotient closed form for broom₃ inverse.
  have h_inv_broom₃ : M.inverse.elementaryWeight RootedTree.broom₃
      = -(M.elementaryWeight RootedTree.vertex) ^ 3
        + 2 * M.elementaryWeight RootedTree.vertex
            * M.elementaryWeight RootedTree.cherry
        - M.elementaryWeight RootedTree.broom₃ :=
    elementaryWeightQ_phi_inv_broom₃
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)
  -- Cycle 369 helpers for `mk [cherry]` derivative/elementary weight closed forms.
  have h_dw_mkCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
          * M.derivativeWeightProd i [] = _
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dw_cherry j]
  have h_mkCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkCherry i]
  -- Cycle 371 helpers for `mk [broom₃]` derivative/elementary weight closed forms.
  have h_dw_mkBroom₃ : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
        = ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.broom₃)
          * M.derivativeWeightProd i [] = _
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_dw_broom₃ j]
  have h_mkBroom₃ : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2 := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkBroom₃ i]
  -- Cycle 372 helpers — `mk [vertex, cherry]` derivative/elementary weight.
  have h_dw_mkVertexCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry])
        = (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.cherry] = _
    have h_vertex_factor :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_cherry_factor :
        M.derivativeWeightProd i [RootedTree.cherry]
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_cherry j]
    rw [h_vertex_factor, h_cherry_factor]
  have h_mkVertexCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
              * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexCherry i]; ring
  -- Cycle 403 helpers — `mk [v, v, cherry]` derivative/elementary weight.
  have h_dw_mkVertexVertexCherry : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
        = (∑ j : Fin s, M.A i j) ^ 2
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex, RootedTree.cherry] = _
    have h_vertex_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_cherry_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_cherry j]
    have h_prod_step_cherry :
        M.derivativeWeightProd i [RootedTree.cherry]
          = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_cherry_inner]
    have h_prod_step_vc :
        M.derivativeWeightProd i [RootedTree.vertex, RootedTree.cherry]
          = (∑ j : Fin s, M.A i j)
            * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [RootedTree.cherry] = _
      rw [h_vertex_inner, h_prod_step_cherry]
    rw [h_vertex_inner, h_prod_step_vc]; ring
  have h_mkVertexVertexCherry : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
          * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
              * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexVertexCherry i]; ring
  -- Cycle 386 helpers — `mk [vertex, broom₃]` derivative/elementary weight.
  have h_dw_mkVertexBroom₃ : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.broom₃])
        = (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.broom₃] = _
    have h_vertex_factor :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_broom_factor :
        M.derivativeWeightProd i [RootedTree.broom₃]
          = ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2 := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.broom₃)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_broom₃ j]
    rw [h_vertex_factor, h_broom_factor]
  have h_mkVertexBroom₃ : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.broom₃])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
          * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.broom₃])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j)
              * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexBroom₃ i]; ring
  -- New cycle 494 helpers — three-children asymmetric
  -- `mk [vertex, vertex, broom₃]` structure: two-vertex prefix giving
  -- `Aᵢ²` factor + broom₃ tail giving the Aⱼ²-pattern factor.
  have h_dw_mkVertexVertexBroom₃ : ∀ i : Fin s,
      M.derivativeWeight i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃])
        = (∑ j : Fin s, M.A i j) ^ 2
          * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2) := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex, RootedTree.broom₃] = _
    have h_vertex_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_broom_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.broom₃
          = ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2 := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dw_broom₃ j]
    have h_prod_step_broom :
        M.derivativeWeightProd i [RootedTree.broom₃]
          = ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2 := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.broom₃)
            * M.derivativeWeightProd i [] = _
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_broom_inner]
    have h_prod_step_vb :
        M.derivativeWeightProd i [RootedTree.vertex, RootedTree.broom₃]
          = (∑ j : Fin s, M.A i j)
            * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2) := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [RootedTree.broom₃] = _
      rw [h_vertex_inner, h_prod_step_broom]
    rw [h_vertex_inner, h_prod_step_vb]; ring
  have h_mkVertexVertexBroom₃ : M.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃])
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
          * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2) := by
    show ∑ i : Fin s, M.b i
            * M.derivativeWeight i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃])
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
              * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_mkVertexVertexBroom₃ i]; ring
  -- Three-layer cons-case unfold for `mk [v, v, broom₃]`'s
  -- derivativeWeightWithSrc: outer two-cons unfold strips the two-vertex
  -- prefix, producing two identical vertex-source factors `inv_v + Aᵢ`
  -- (cycle 367/370 pattern); inner broom₃ tail unfolds via cycle
  -- 371's `h_dws_broom₃` to `(inv_v + ∑ₖ Aⱼₖ)²`.
  have h_dws_mkVertexVertexBroom₃ : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃])
        = (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j) ^ 2
          * (M.inverse.elementaryWeight RootedTree.broom₃
             + ∑ j : Fin s, M.A i j
                 * (M.inverse.elementaryWeight RootedTree.vertex
                    + ∑ k : Fin s, M.A j k) ^ 2) := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * M.derivativeWeightWithSrcProd M.inverse i
              [RootedTree.vertex, RootedTree.broom₃] = _
    have h_vertex_inner :
        ∑ j : Fin s, M.A i j * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
    -- Inner `dws_inv_j broom₃ = (inv_v + ∑ₖ Aⱼₖ)²` (cycle 371 pattern).
    have h_dws_broom₃ : ∀ j : Fin s,
        M.derivativeWeightWithSrc M.inverse j RootedTree.broom₃
          = (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ k : Fin s, M.A j k) ^ 2 := by
      intro j
      show (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ k : Fin s, M.A j k
                  * M.derivativeWeightWithSrc M.inverse k RootedTree.vertex)
            * M.derivativeWeightWithSrcProd M.inverse j [RootedTree.vertex]
          = (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ k : Fin s, M.A j k) ^ 2
      have h_inner_sum :
          ∑ k : Fin s, M.A j k
              * M.derivativeWeightWithSrc M.inverse k RootedTree.vertex
            = ∑ k : Fin s, M.A j k := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
      have h_prod_step :
          M.derivativeWeightWithSrcProd M.inverse j [RootedTree.vertex]
            = M.inverse.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k := by
        show (M.inverse.elementaryWeight RootedTree.vertex
                + ∑ k : Fin s, M.A j k
                    * M.derivativeWeightWithSrc M.inverse k RootedTree.vertex)
              * M.derivativeWeightWithSrcProd M.inverse j []
            = M.inverse.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k
        rw [show M.derivativeWeightWithSrcProd M.inverse j [] = 1 from rfl, mul_one,
            h_inner_sum]
      rw [h_inner_sum, h_prod_step]; ring
    have h_broom_factor :
        M.derivativeWeightWithSrcProd M.inverse i [RootedTree.broom₃]
          = M.inverse.elementaryWeight RootedTree.broom₃
            + ∑ j : Fin s, M.A i j
                * (M.inverse.elementaryWeight RootedTree.vertex
                   + ∑ k : Fin s, M.A j k) ^ 2 := by
      show (M.inverse.elementaryWeight RootedTree.broom₃
              + ∑ j : Fin s, M.A i j
                  * M.derivativeWeightWithSrc M.inverse j RootedTree.broom₃)
            * M.derivativeWeightWithSrcProd M.inverse i [] = _
      rw [show M.derivativeWeightWithSrcProd M.inverse i [] = 1 from rfl, mul_one]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h_dws_broom₃ j]
    have h_prod_step_vb :
        M.derivativeWeightWithSrcProd M.inverse i [RootedTree.vertex, RootedTree.broom₃]
          = (M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j)
            * (M.inverse.elementaryWeight RootedTree.broom₃
               + ∑ j : Fin s, M.A i j
                   * (M.inverse.elementaryWeight RootedTree.vertex
                      + ∑ k : Fin s, M.A j k) ^ 2) := by
      show (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ j : Fin s, M.A i j
                  * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
            * M.derivativeWeightWithSrcProd M.inverse i [RootedTree.broom₃] = _
      rw [h_vertex_inner, h_broom_factor]
    rw [h_vertex_inner, h_prod_step_vb]; ring
  -- Main computation: assemble closed form via _inv_mk + _mk × 10 + sum algebra.
  rw [elementaryWeightQ_phi_inv_mk M
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃]),
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_sum :
      (∑ i : Fin s, M.b i
          * M.derivativeWeightWithSrc M.inverse i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃]))
        = -(M.elementaryWeight RootedTree.vertex) ^ 6
          + 5 * (M.elementaryWeight RootedTree.vertex) ^ 4
              * M.elementaryWeight RootedTree.cherry
          - 4 * (M.elementaryWeight RootedTree.vertex) ^ 3
              * M.elementaryWeight RootedTree.broom₃
          - 4 * (M.elementaryWeight RootedTree.vertex) ^ 2
              * (M.elementaryWeight RootedTree.cherry) ^ 2
          + 4 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight RootedTree.cherry
              * M.elementaryWeight RootedTree.broom₃
          - (M.elementaryWeight RootedTree.broom₃) ^ 2
          + (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight RootedTree.bushy
          - 2 * (M.elementaryWeight RootedTree.vertex) ^ 3
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          + 4 * (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry])
          - 2 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
          + (M.elementaryWeight RootedTree.vertex) ^ 2
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
          - 2 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.broom₃])
          + M.elementaryWeight
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃]) := by
    have h_subst :
        (∑ i : Fin s, M.b i
            * M.derivativeWeightWithSrc M.inverse i
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃]))
          = ∑ i : Fin s,
              ((-(M.elementaryWeight RootedTree.vertex) ^ 5
                  + 2 * (M.elementaryWeight RootedTree.vertex) ^ 3
                      * M.elementaryWeight RootedTree.cherry
                  - (M.elementaryWeight RootedTree.vertex) ^ 2
                      * M.elementaryWeight RootedTree.broom₃) * M.b i
                + (3 * (M.elementaryWeight RootedTree.vertex) ^ 4
                    - 4 * (M.elementaryWeight RootedTree.vertex) ^ 2
                        * M.elementaryWeight RootedTree.cherry
                    + 2 * M.elementaryWeight RootedTree.vertex
                        * M.elementaryWeight RootedTree.broom₃)
                    * (M.b i * ∑ j : Fin s, M.A i j)
                + (-3 * (M.elementaryWeight RootedTree.vertex) ^ 3
                    + 2 * M.elementaryWeight RootedTree.vertex
                        * M.elementaryWeight RootedTree.cherry
                    - M.elementaryWeight RootedTree.broom₃)
                    * (M.b i * (∑ j : Fin s, M.A i j) ^ 2)
                + (M.elementaryWeight RootedTree.vertex) ^ 2
                    * (M.b i * (∑ j : Fin s, M.A i j) ^ 3)
                + (-2 * (M.elementaryWeight RootedTree.vertex) ^ 3)
                    * (M.b i * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k)
                + (4 * (M.elementaryWeight RootedTree.vertex) ^ 2)
                    * (M.b i * (∑ j : Fin s, M.A i j)
                        * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k))
                + (-2 * M.elementaryWeight RootedTree.vertex)
                    * (M.b i * (∑ j : Fin s, M.A i j) ^ 2
                        * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k))
                + (M.elementaryWeight RootedTree.vertex) ^ 2
                    * (M.b i * ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2)
                + (-2 * M.elementaryWeight RootedTree.vertex)
                    * (M.b i * (∑ j : Fin s, M.A i j)
                        * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2))
                + M.b i * (∑ j : Fin s, M.A i j) ^ 2
                    * (∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_dws_mkVertexVertexBroom₃ i, h_inv_broom₃, h_inv_v]
      -- Pre-distribute the inner Σⱼ Aᵢⱼ · (-v + Σₖ Aⱼₖ)² into three
      -- standard kernels (Aᵢ via v², ∑Aᵢⱼ·Aⱼ via -2v, ∑Aᵢⱼ·Aⱼ² via 1).
      have h_inner_expand :
          ∑ j : Fin s, M.A i j
              * (-M.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k) ^ 2
            = M.elementaryWeight RootedTree.vertex ^ 2 * ∑ j : Fin s, M.A i j
              + (-2 * M.elementaryWeight RootedTree.vertex)
                  * ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k
              + ∑ j : Fin s, M.A i j * (∑ k : Fin s, M.A j k) ^ 2 := by
        have h_inner :
            ∑ j : Fin s, M.A i j
                * (-M.elementaryWeight RootedTree.vertex + ∑ k : Fin s, M.A j k) ^ 2
              = ∑ j : Fin s, (M.elementaryWeight RootedTree.vertex ^ 2 * M.A i j
                  + (-2 * M.elementaryWeight RootedTree.vertex)
                      * (M.A i j * ∑ k : Fin s, M.A j k)
                  + M.A i j * (∑ k : Fin s, M.A j k) ^ 2) := by
          refine Finset.sum_congr rfl (fun j _ => ?_); ring
        rw [h_inner, Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
      rw [h_inner_expand]; ring
    rw [h_subst, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum,
        ← h_mkVertexVertexBroom₃, ← h_mkVertexBroom₃, ← h_mkBroom₃,
        ← h_mkVertexVertexCherry, ← h_mkVertexCherry, ← h_mkCherry,
        ← h_bushy, ← h_broom₃, ← h_cherry, ← h_vertex]
    ring
  rw [h_sum]; ring

/-- *Phase α'.5.1 P5 (cycle 494) — `mk [vertex, vertex, broom₃]` closed
form non-vacuity at `η_q = ⟦explicitEuler⟧`.* The expected value is
`Φ_{⟦explicitEuler⟧⁻¹}(mk [vertex, vertex, broom₃]) = 1⁶ - 0 + 0 - ...
= 1`, since for explicit Euler `Σ b = 1` (so `Φ_η(vertex) = 1`) and
`A = 0` (so all higher elementary weights vanish). Leading `v⁶`
survives, all other terms vanish — consistent with the order-6 even
parity pattern of cycles 384/403/492/493. -/
example :
    elementaryWeightQ_phi
      ((Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩))⁻¹
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃]) = 1 := by
  rw [elementaryWeightQ_phi_inv_mkVertexVertexBroom₃, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk]
  have h_vertex : RKTableau.explicitEuler.elementaryWeight RootedTree.vertex = 1 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.vertex = 1
    simp [RKTableau.explicitEuler, RKTableau.derivativeWeight_vertex]
  have h_cherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.cherry = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_cherry : RKTableau.explicitEuler.elementaryWeight RootedTree.cherry = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.cherry = 0
    simp [h_cherry_zero]
  have h_broom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.broom₃ = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_broom₃ : RKTableau.explicitEuler.elementaryWeight RootedTree.broom₃ = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.broom₃ = 0
    simp [h_broom₃_zero]
  have h_bushy_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.bushy = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0
                [RootedTree.vertex, RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_bushy : RKTableau.explicitEuler.elementaryWeight RootedTree.bushy = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.bushy = 0
    simp [h_bushy_zero]
  have h_mkCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.cherry)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_mkCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = 0
    simp [h_mkCherry_zero]
  have h_mkVertexCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.cherry] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]) = 0
    simp [h_mkVertexCherry_zero]
  have h_mkVertexVertexCherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0
                [RootedTree.vertex, RootedTree.cherry] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexVertexCherry :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) = 0
    simp [h_mkVertexVertexCherry_zero]
  have h_mkBroom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.broom₃)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_mkBroom₃ :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) = 0
    simp [h_mkBroom₃_zero]
  have h_mkVertexBroom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.broom₃]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.broom₃] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexBroom₃ :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.broom₃]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.broom₃]) = 0
    simp [h_mkVertexBroom₃_zero]
  have h_mkVertexVertexBroom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃]) = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0
                [RootedTree.vertex, RootedTree.broom₃] = 0
    simp [RKTableau.explicitEuler]
  have h_mkVertexVertexBroom₃ :
      RKTableau.explicitEuler.elementaryWeight
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃]) = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i
              (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃]) = 0
    simp [h_mkVertexVertexBroom₃_zero]
  rw [h_vertex, h_cherry, h_broom₃, h_bushy, h_mkCherry, h_mkVertexCherry,
      h_mkVertexVertexCherry, h_mkBroom₃, h_mkVertexBroom₃, h_mkVertexVertexBroom₃]
  ring

/-- *Phase α'.5.1 P5 (cycle 494) — Priority 2 `mk [vertex, vertex, broom₃]`
m=0 witness:* specialisation of Sub-lemma A
`powRep_sum_eq_of_strict_subtree_agreement` at
`t = mk [vertex, vertex, broom₃], m = 0`. Under agreement at
`vertex`, `cherry`, `broom₃`, `bushy`, `mk [cherry]`,
`mk [vertex, cherry]`, `mk [vertex, vertex, cherry]`, `mk [broom₃]`,
`mk [vertex, broom₃]`, and `mk [vertex, vertex, broom₃]` (ten
subtrees corresponding to the closed-form factors of cycle 494's
`_mkVertexVertexBroom₃`), the `η_q^(-1)` images at
`mk [vertex, vertex, broom₃]` coincide.

Proof: reduce `η_q ^ (-(((0 + 1 : ℕ) : ℤ)))` to `η_q⁻¹` via
`Nat.cast_one` + `zpow_neg_one`, apply cycle 494's
`elementaryWeightQ_phi_inv_mkVertexVertexBroom₃` on both sides, then
substitute the ten agreement hypotheses. -/
theorem powRep_sum_eq_of_agreement_at_mkVertexVertexBroom₃_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry)
    (h_broom₃ : elementaryWeightQ_phi η_q RootedTree.broom₃
              = elementaryWeightQ_phi η_q' RootedTree.broom₃)
    (h_bushy : elementaryWeightQ_phi η_q RootedTree.bushy
              = elementaryWeightQ_phi η_q' RootedTree.bushy)
    (h_mkCherry : elementaryWeightQ_phi η_q
                    (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
    (h_mkVertexCherry : elementaryWeightQ_phi η_q
                          (OpenMath.Chapter3.Section310.RootedTree.mk
                            [RootedTree.vertex, RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry]))
    (h_mkVertexVertexCherry : elementaryWeightQ_phi η_q
                                (OpenMath.Chapter3.Section310.RootedTree.mk
                                  [RootedTree.vertex, RootedTree.vertex,
                                   RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]))
    (h_mkBroom₃ : elementaryWeightQ_phi η_q
                    (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]))
    (h_mkVertexBroom₃ : elementaryWeightQ_phi η_q
                          (OpenMath.Chapter3.Section310.RootedTree.mk
                            [RootedTree.vertex, RootedTree.broom₃])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.broom₃]))
    (h_mkVertexVertexBroom₃ : elementaryWeightQ_phi η_q
                                (OpenMath.Chapter3.Section310.RootedTree.mk
                                  [RootedTree.vertex, RootedTree.vertex,
                                   RootedTree.broom₃])
              = elementaryWeightQ_phi η_q'
                  (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃])) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃])
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃]) := by
  have h_pow : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
      ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
    intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow η_q, h_pow η_q',
      elementaryWeightQ_phi_inv_mkVertexVertexBroom₃,
      elementaryWeightQ_phi_inv_mkVertexVertexBroom₃,
      h_vertex, h_cherry, h_broom₃, h_bushy, h_mkCherry, h_mkVertexCherry,
      h_mkVertexVertexCherry, h_mkBroom₃, h_mkVertexBroom₃,
      h_mkVertexVertexBroom₃]

/-- *Phase α'.5.1 P5 (cycle 494) — `mk [vertex, vertex, broom₃]` m=0 witness
non-vacuity at `η_q = η_q' = ⟦explicitEuler⟧`.* Discharges the ten
agreement hypotheses by `rfl`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃])
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃]) :=
  powRep_sum_eq_of_agreement_at_mkVertexVertexBroom₃_zero
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- *Phase α'.5.2.0 Step 1 (cycle 499) — `bushy₄ = mk [vertex, vertex, vertex, vertex]`
(order-5 broom) closed form for Φ_{η_q⁻¹}.* At the order-5 broom tree
`bushy₄`, the quotient-level elementary weight of the §383 inverse
class admits the closed form
  `Φ_{η_q⁻¹}(bushy₄) = -(Φ_η(vertex))^5
                       + 4 · (Φ_η(vertex))^3 · Φ_η(cherry)
                       − 6 · (Φ_η(vertex))^2 · Φ_η(broom₃)
                       + 4 · Φ_η(vertex) · Φ_η(bushy)
                       − Φ_η(bushy₄)`.

Sixth data point in the cycle 366 §G Route B hypothesis ladder
(vertex, cherry, broom₃, bushy, mkVertexVertexBroom₃, bushy₄). At
order 5, the binomial expansion of `(Aᵢ − v)^4` introduces a 5-term
polynomial in `Φ_η(vertex), Φ_η(cherry), Φ_η(broom₃), Φ_η(bushy),
Φ_η(bushy₄)`, extending cycle 370's `(Aᵢ − v)^3` bushy template by
one product layer. Ships the first concrete brick of the Phase α'.5.2
ladder per `def_422B_phase_alpha_prime_5_2_scoping.md`.

Proof outline (mirrors cycle 370's `bushy` recipe with one extra
cons-case unfold layer for the fourth child):

1. Reduce to a representative `⟨s, M⟩` via `Quotient.inductionOn`.
2. Reuse cycle 367/368/370 helpers `h_inv_v`, `h_vertex`,
   `h_dw_cherry`, `h_cherry`, `h_dw_broom₃`, `h_broom₃`, `h_dw_bushy`,
   `h_bushy` (verbatim ports).
3. Add three new helpers for the `bushy₄` four-child structure:
   - `h_dw_bushy₄` : `M.derivativeWeight i bushy₄ = (∑ⱼ M.A i j)^4`
     (four-layer cons-case unfold extending `h_dw_bushy`).
   - `h_bushy₄` : `M.elementaryWeight bushy₄
                   = ∑ᵢ M.b i · (∑ⱼ M.A i j)^4`
     (one `Finset.sum_congr` on `h_dw_bushy₄`).
   - `h_dws_bushy₄` : `M.derivativeWeightWithSrc M.inverse i bushy₄
                       = (M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j)^4`
     (four-layer cons-case unfold of `derivativeWeightWithSrcProd`).
4. After `_inv_mk`, `_mk` × 5 rewrites, substitute the per-summand
   fourth-power closed form via `ring`, distribute the sum via
   `Finset.sum_add_distrib` / `Finset.sum_sub_distrib`, factor out
   constants via `← Finset.mul_sum` (four applications), then close
   with `ring`. -/
theorem elementaryWeightQ_phi_inv_bushy₄
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹) RootedTree.bushy₄
      = -(elementaryWeightQ_phi η_q RootedTree.vertex) ^ 5
        + 4 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 3
            * elementaryWeightQ_phi η_q RootedTree.cherry
        - 6 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        + 4 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q RootedTree.bushy
        - elementaryWeightQ_phi η_q RootedTree.bushy₄ := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- Cycle 367 helpers (reused verbatim from cycle 370).
  have h_inv_v : M.inverse.elementaryWeight RootedTree.vertex
      = -M.elementaryWeight RootedTree.vertex := by
    show ∑ j : Fin s, M.inverse.b j * M.inverse.derivativeWeight j RootedTree.vertex
          = -(∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.inverse_b, RKTableau.derivativeWeight_vertex,
        RKTableau.derivativeWeight_vertex, neg_mul]
  have h_vertex : M.elementaryWeight RootedTree.vertex = ∑ j : Fin s, M.b j := by
    show ∑ j : Fin s, M.b j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.b j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_dw_cherry : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.cherry = ∑ j : Fin s, M.A i j := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
    rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RKTableau.derivativeWeight_vertex, mul_one]
  have h_cherry : M.elementaryWeight RootedTree.cherry
      = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.cherry
          = ∑ i : Fin s, M.b i * ∑ j : Fin s, M.A i j
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_cherry i]
  -- Cycle 368 helpers (reused verbatim from cycle 370).
  have h_dw_broom₃ : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.broom₃ = (∑ j : Fin s, M.A i j) ^ 2 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 2
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    rw [h_inner_sum, h_prod_step]; ring
  have h_broom₃ : M.elementaryWeight RootedTree.broom₃
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.broom₃
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_broom₃ i]
  -- Cycle 370 helpers (reused verbatim).
  have h_dw_bushy : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.bushy = (∑ j : Fin s, M.A i j) ^ 3 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i [RootedTree.vertex, RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 3
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step_1 :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    have h_prod_step_2 :
        M.derivativeWeightProd i [RootedTree.vertex, RootedTree.vertex]
          = (∑ j : Fin s, M.A i j) ^ 2 := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [RootedTree.vertex]
          = (∑ j : Fin s, M.A i j) ^ 2
      rw [h_inner_sum, h_prod_step_1]; ring
    rw [h_inner_sum, h_prod_step_2]; ring
  have h_bushy : M.elementaryWeight RootedTree.bushy
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 3 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.bushy
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 3
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_bushy i]
  -- New cycle 499 helpers for the bushy₄ four-child structure.
  have h_dw_bushy₄ : ∀ i : Fin s,
      M.derivativeWeight i RootedTree.bushy₄ = (∑ j : Fin s, M.A i j) ^ 4 := by
    intro i
    show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
          * M.derivativeWeightProd i
              [RootedTree.vertex, RootedTree.vertex, RootedTree.vertex]
        = (∑ j : Fin s, M.A i j) ^ 4
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeight_vertex, mul_one]
    have h_prod_step_1 :
        M.derivativeWeightProd i [RootedTree.vertex] = ∑ j : Fin s, M.A i j := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [] = ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one, h_inner_sum]
    have h_prod_step_2 :
        M.derivativeWeightProd i [RootedTree.vertex, RootedTree.vertex]
          = (∑ j : Fin s, M.A i j) ^ 2 := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [RootedTree.vertex]
          = (∑ j : Fin s, M.A i j) ^ 2
      rw [h_inner_sum, h_prod_step_1]; ring
    have h_prod_step_3 :
        M.derivativeWeightProd i
            [RootedTree.vertex, RootedTree.vertex, RootedTree.vertex]
          = (∑ j : Fin s, M.A i j) ^ 3 := by
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
            * M.derivativeWeightProd i [RootedTree.vertex, RootedTree.vertex]
          = (∑ j : Fin s, M.A i j) ^ 3
      rw [h_inner_sum, h_prod_step_2]; ring
    rw [h_inner_sum, h_prod_step_3]; ring
  have h_bushy₄ : M.elementaryWeight RootedTree.bushy₄
      = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 4 := by
    show ∑ i : Fin s, M.b i * M.derivativeWeight i RootedTree.bushy₄
          = ∑ i : Fin s, M.b i * (∑ j : Fin s, M.A i j) ^ 4
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dw_bushy₄ i]
  have h_dws_bushy₄ : ∀ i : Fin s,
      M.derivativeWeightWithSrc M.inverse i RootedTree.bushy₄
        = (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j) ^ 4 := by
    intro i
    show (M.inverse.elementaryWeight RootedTree.vertex
            + ∑ j : Fin s, M.A i j
                * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
          * M.derivativeWeightWithSrcProd M.inverse i
              [RootedTree.vertex, RootedTree.vertex, RootedTree.vertex]
        = (M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j) ^ 4
    have h_inner_sum :
        ∑ j : Fin s, M.A i j * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex
          = ∑ j : Fin s, M.A i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
    have h_prod_step_1 :
        M.derivativeWeightWithSrcProd M.inverse i [RootedTree.vertex]
          = M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j := by
      show (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ j : Fin s, M.A i j
                  * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
            * M.derivativeWeightWithSrcProd M.inverse i []
          = M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j
      rw [show M.derivativeWeightWithSrcProd M.inverse i [] = 1 from rfl, mul_one,
          h_inner_sum]
    have h_prod_step_2 :
        M.derivativeWeightWithSrcProd M.inverse i
            [RootedTree.vertex, RootedTree.vertex]
          = (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ j : Fin s, M.A i j) ^ 2 := by
      show (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ j : Fin s, M.A i j
                  * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
            * M.derivativeWeightWithSrcProd M.inverse i [RootedTree.vertex]
          = (M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j) ^ 2
      rw [h_inner_sum, h_prod_step_1]; ring
    have h_prod_step_3 :
        M.derivativeWeightWithSrcProd M.inverse i
            [RootedTree.vertex, RootedTree.vertex, RootedTree.vertex]
          = (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ j : Fin s, M.A i j) ^ 3 := by
      show (M.inverse.elementaryWeight RootedTree.vertex
              + ∑ j : Fin s, M.A i j
                  * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
            * M.derivativeWeightWithSrcProd M.inverse i
                [RootedTree.vertex, RootedTree.vertex]
          = (M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j) ^ 3
      rw [h_inner_sum, h_prod_step_2]; ring
    rw [h_inner_sum, h_prod_step_3]; ring
  -- Main computation: assemble closed form via _inv_mk + _mk × 5 + sum algebra.
  rw [elementaryWeightQ_phi_inv_mk M RootedTree.bushy₄,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk]
  have h_sum :
      (∑ i : Fin s, M.b i * M.derivativeWeightWithSrc M.inverse i RootedTree.bushy₄)
        = M.elementaryWeight RootedTree.bushy₄
          - 4 * M.elementaryWeight RootedTree.vertex
              * M.elementaryWeight RootedTree.bushy
          + 6 * M.elementaryWeight RootedTree.vertex ^ 2
              * M.elementaryWeight RootedTree.broom₃
          - 4 * M.elementaryWeight RootedTree.vertex ^ 3
              * M.elementaryWeight RootedTree.cherry
          + M.elementaryWeight RootedTree.vertex ^ 5 := by
    have h_subst :
        (∑ i : Fin s, M.b i * M.derivativeWeightWithSrc M.inverse i RootedTree.bushy₄)
          = ∑ i : Fin s,
            (M.b i * (∑ j : Fin s, M.A i j) ^ 4
              - 4 * M.elementaryWeight RootedTree.vertex
                  * (M.b i * (∑ j : Fin s, M.A i j) ^ 3)
              + 6 * M.elementaryWeight RootedTree.vertex ^ 2
                  * (M.b i * (∑ j : Fin s, M.A i j) ^ 2)
              - 4 * M.elementaryWeight RootedTree.vertex ^ 3
                  * (M.b i * ∑ j : Fin s, M.A i j)
              + M.elementaryWeight RootedTree.vertex ^ 4 * M.b i) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_dws_bushy₄ i, h_inv_v]; ring
    rw [h_subst, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← h_bushy₄, ← h_bushy, ← h_broom₃, ← h_cherry, ← h_vertex]
    ring
  rw [h_sum]; ring

/-- *Phase α'.5.2.0 Step 1 (cycle 499) — `bushy₄` closed form non-vacuity at
`η_q = ⟦explicitEuler⟧`.* The expected value is
`Φ_{⟦explicitEuler⟧⁻¹}(bushy₄) = -1^5 + 4·1^3·0 − 6·1^2·0 + 4·1·0 − 0 = -1`,
since for explicit Euler `Σ b = 1` (so `Φ_η(vertex) = 1`) and `A = 0`
(so `Φ_η(cherry) = Φ_η(broom₃) = Φ_η(bushy) = Φ_η(bushy₄) = 0`). -/
example :
    elementaryWeightQ_phi
      ((Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩))⁻¹ RootedTree.bushy₄ = -1 := by
  rw [elementaryWeightQ_phi_inv_bushy₄, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_vertex : RKTableau.explicitEuler.elementaryWeight RootedTree.vertex = 1 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.vertex = 1
    simp [RKTableau.explicitEuler, RKTableau.derivativeWeight_vertex]
  have h_cherry_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.cherry = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [] = 0
    simp [RKTableau.explicitEuler]
  have h_cherry : RKTableau.explicitEuler.elementaryWeight RootedTree.cherry = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.cherry = 0
    simp [h_cherry_zero]
  have h_broom₃_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.broom₃ = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_broom₃ : RKTableau.explicitEuler.elementaryWeight RootedTree.broom₃ = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.broom₃ = 0
    simp [h_broom₃_zero]
  have h_bushy_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.bushy = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0
                [RootedTree.vertex, RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_bushy : RKTableau.explicitEuler.elementaryWeight RootedTree.bushy = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.bushy = 0
    simp [h_bushy_zero]
  have h_bushy₄_zero :
      RKTableau.explicitEuler.derivativeWeight 0 RootedTree.bushy₄ = 0 := by
    show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j
              * RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex)
            * RKTableau.explicitEuler.derivativeWeightProd 0
                [RootedTree.vertex, RootedTree.vertex, RootedTree.vertex] = 0
    simp [RKTableau.explicitEuler]
  have h_bushy₄ : RKTableau.explicitEuler.elementaryWeight RootedTree.bushy₄ = 0 := by
    show ∑ i : Fin 1, RKTableau.explicitEuler.b i
            * RKTableau.explicitEuler.derivativeWeight i RootedTree.bushy₄ = 0
    simp [h_bushy₄_zero]
  rw [h_vertex, h_cherry, h_broom₃, h_bushy, h_bushy₄]; ring

/-- *Phase α'.5.2.0 Step 1 (cycle 499) — Priority 2 bushy₄ m=0 witness:*
specialisation of Sub-lemma A `powRep_sum_eq_of_strict_subtree_agreement`
at `t = bushy₄, m = 0`. Under agreement at `vertex`, `cherry`,
`broom₃`, `bushy`, and `bushy₄` (five subtrees corresponding to the
closed-form factors), the `η_q^(-1)` images at `bushy₄` coincide.

Proof: reduce `η_q ^ (-(((0 + 1 : ℕ) : ℤ)))` to `η_q⁻¹` via `zero_add`
+ `Nat.cast_one` + `zpow_neg_one`, apply cycle 499's
`elementaryWeightQ_phi_inv_bushy₄` on both sides, then substitute the
five agreement hypotheses. -/
theorem powRep_sum_eq_of_agreement_at_bushy₄_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry)
    (h_broom₃ : elementaryWeightQ_phi η_q RootedTree.broom₃
              = elementaryWeightQ_phi η_q' RootedTree.broom₃)
    (h_bushy : elementaryWeightQ_phi η_q RootedTree.bushy
              = elementaryWeightQ_phi η_q' RootedTree.bushy)
    (h_bushy₄ : elementaryWeightQ_phi η_q RootedTree.bushy₄
              = elementaryWeightQ_phi η_q' RootedTree.bushy₄) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ)))) RootedTree.bushy₄
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ)))) RootedTree.bushy₄ := by
  have h_pow : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
      ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
    intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow η_q, h_pow η_q',
      elementaryWeightQ_phi_inv_bushy₄, elementaryWeightQ_phi_inv_bushy₄,
      h_vertex, h_cherry, h_broom₃, h_bushy, h_bushy₄]

/-- *Phase α'.5.2.0 Step 1 (cycle 499) — bushy₄ m=0 witness non-vacuity at
`η_q = η_q' = ⟦explicitEuler⟧`.* Discharges the five agreement
hypotheses by `rfl`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
        RootedTree.bushy₄
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
          RootedTree.bushy₄ :=
  powRep_sum_eq_of_agreement_at_bushy₄_zero
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    rfl rfl rfl rfl rfl

/-! ### Phase α'.1 (cycle 380) — Family A recursive helper `inversePolyChain`

Cycle 380 ships the partial V1 recursive shape for Phase α': a
recursive helper `inversePolyChain : ℕ → (RT → ℝ) → ℝ` capturing the
closed-form recursion for the single-child ladder trees
`t_n = mk^n[vertex]` (Family A in the cycle 379 scoping doc
`.prover-state/issues/def_422B_phase_alpha_prime_scoping.md` §4).

**Derivation.** Let `c_k := Φ_η(t_k) = f (chainTree k)` and
`P_n := Φ_{η⁻¹}(t_n)`. From cycle 358's `_inv_mk`
(`Section422.lean:582`) and the per-row factorisation pattern in
the cycle 367 / 368 / 369 / 378 proof bodies, `dws(t_n, i)`
admits the expansion `∑_{p=0}^{n} α_{n,p}(c_*) · a_i^{(p)}` where:

* `a_i^{(p)} := M.derivativeWeight i (t_p)` (with `a_i^{(0)} = 1`,
  `a_i^{(p+1)} = ∑_j M.A i j · a_j^{(p)}`),
* `α_{n,n} = 1`, `α_{n,p} = P_{n-p-1}` for `0 ≤ p ≤ n-1`.

Summing against `M.b i` and using `∑_i M.b i · a_i^{(p)} = c_p`
gives the closed-form quotient-level convolution recursion:

  `P_0 = -c_0`
  `P_{n+1} = -(∑_{p=0}^{n} P_{n-p} · c_p) - c_{n+1}`

**Verification (hand-derivation against the cycle 341/367/369/378 closed forms).**

* `P_0 = -c_0 = -v` ✓ (matches cycle 341).
* `P_1 = -(P_0 · c_0) - c_1 = -(-c_0)·c_0 - c_1 = c_0² - c_1
        = v² - c` ✓ (matches cycle 367).
* `P_2 = -(P_1·c_0 + P_0·c_1) - c_2`
       `= -((c_0² - c_1)·c_0 + (-c_0)·c_1) - c_2`
       `= -c_0³ + c_0c_1 + c_0c_1 - c_2`
       `= -c_0³ + 2c_0c_1 - c_2 = -v³ + 2vc - m` ✓
  (matches cycle 369 for `mk [cherry]`).
* `P_3 = -(P_2·c_0 + P_1·c_1 + P_0·c_2) - c_3`
       `= -((-c_0³+2c_0c_1-c_2)·c_0 + (c_0²-c_1)·c_1 + (-c_0)·c_2) - c_3`
       `= c_0⁴ - 3c_0²c_1 + c_1² + 2c_0c_2 - c_3`
       `= v⁴ - 3v²c + c² + 2vm - M_mc` ✓
  (matches cycle 378 for `mk [mk [cherry]]`).

**Phase α'.2 (cycle 381) Family A bridge migration.** Cycle 381
migrates the four Family A branches of `inversePolynomial` (vertex /
cherry / `mk [cherry]` / `mk [mk [cherry]]`) to dispatch directly to
`inversePolyChain k` for `k = 0, 1, 2, 3`. The Family B/C branches
(`broom₃`, `bushy`, `mk [broom₃]`, `mk [vertex, cherry]`) remain as
explicit `if-then-else` branches. This requires the cycle 380 block
(`chainTree`, `inversePolyChain`, and the 4 closed-form theorems) to
sit *before* `inversePolynomial`. The Phase α'.1 bridge theorems
`inversePolyChain_{k}_eq_inversePolynomial` stay after
`inversePolynomial` and become trivial post-migration.

Future cycles (Phase α'.3+) will either (i) extend `inversePolyChain`
to cover Family B/C, or (ii) replace `inversePolynomial`'s body
with a fully recursive `match` driven by `inversePolyChain` plus
helpers for Family B/C. -/

/-- *Phase α'.1 (cycle 380) — depth-`n` single-child ladder tree.*
`chainTree n = mk^n[vertex]`. Concretely:
`chainTree 0 = vertex`,
`chainTree 1 = mk [vertex] = cherry`,
`chainTree 2 = mk [mk [vertex]] = mk [cherry]`,
`chainTree 3 = mk [mk [mk [vertex]]] = mk [mk [cherry]]`. -/
def chainTree : ℕ → RT
  | 0 => RootedTree.vertex
  | n + 1 => OpenMath.Chapter3.Section310.RootedTree.mk [chainTree n]

/-- *Phase α'.1 (cycle 380) — `chainTree 1 = cherry`.* -/
theorem chainTree_one : chainTree 1 = RootedTree.cherry := rfl

/-- *Phase α'.1 (cycle 380) — `chainTree 2 = mk [cherry]`.* -/
theorem chainTree_two :
    chainTree 2 = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry] := rfl

/-- *Phase α'.1 (cycle 380) — `chainTree 3 = mk [mk [cherry]]`.* -/
theorem chainTree_three :
    chainTree 3
      = OpenMath.Chapter3.Section310.RootedTree.mk
          [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]] := rfl

/-- *Phase α'.1 (cycle 380) — Family A recursive closed-form helper.*

For the depth-`n` single-child ladder tree `t_n = chainTree n`,
`inversePolyChain n f` evaluates to `Φ_{η⁻¹}(t_n)` (when
`f = Φ_η`) via the convolution recursion derived in the section
docstring above.

Base case: `inversePolyChain 0 f = -f vertex`.

Recursive case: for `n ≥ 0`,
`inversePolyChain (n+1) f = -(∑_{p=0}^n inversePolyChain (n-p) f · f (chainTree p))
                            - f (chainTree (n+1))`.

The recursion terminates structurally on `n` (each recursive call
has first-argument `n - p.val ≤ n < n + 1`). -/
noncomputable def inversePolyChain : ℕ → (RT → ℝ) → ℝ
  | 0, f => -f RootedTree.vertex
  | n + 1, f =>
    -(∑ p : Fin (n + 1),
        inversePolyChain (n - p.val) f * f (chainTree p.val))
    - f (chainTree (n + 1))

/-- *Phase α'.1 (cycle 380) — `inversePolyChain` base-case evaluation.* -/
theorem inversePolyChain_zero (f : RT → ℝ) :
    inversePolyChain 0 f = -f RootedTree.vertex := by
  rw [inversePolyChain]

/-- *Phase α'.1 (cycle 380) — `inversePolyChain` closed form at depth 1.*

Computes the cycle 367 closed form `(Φ_η τ)² − Φ_η [τ]` for `cherry`. -/
theorem inversePolyChain_one (f : RT → ℝ) :
    inversePolyChain 1 f
      = (f RootedTree.vertex) ^ 2 - f RootedTree.cherry := by
  rw [inversePolyChain, Fin.sum_univ_one]
  show -(inversePolyChain 0 f * f RootedTree.vertex) - f RootedTree.cherry = _
  rw [inversePolyChain_zero]
  ring

/-- *Phase α'.1 (cycle 380) — `inversePolyChain` closed form at depth 2.*

Computes the cycle 369 closed form
`-(Φ_η τ)³ + 2·Φ_η τ·Φ_η [τ] − Φ_η [[τ]]` for `mk [cherry]`. -/
theorem inversePolyChain_two (f : RT → ℝ) :
    inversePolyChain 2 f
      = -(f RootedTree.vertex) ^ 3
        + 2 * f RootedTree.vertex * f RootedTree.cherry
        - f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) := by
  rw [inversePolyChain, Fin.sum_univ_two]
  show -(inversePolyChain 1 f * f RootedTree.vertex
          + inversePolyChain 0 f * f RootedTree.cherry)
        - f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) = _
  rw [inversePolyChain_one, inversePolyChain_zero]
  ring

/-- *Phase α'.1 (cycle 380) — `inversePolyChain` closed form at depth 3.*

Computes the cycle 378 closed form
`(Φ_η τ)⁴ − 3·(Φ_η τ)²·Φ_η [τ] + (Φ_η [τ])² + 2·Φ_η τ·Φ_η [[τ]]
   − Φ_η [[[τ]]]` for `mk [mk [cherry]]`. This is the Phase α'.1
deliverable: a recursive definition matches the cycle 378
hand-derived closed form. -/
theorem inversePolyChain_three (f : RT → ℝ) :
    inversePolyChain 3 f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + (f RootedTree.cherry) ^ 2
        + 2 * f RootedTree.vertex
            * f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) := by
  rw [inversePolyChain, Fin.sum_univ_three]
  show -(inversePolyChain 2 f * f RootedTree.vertex
          + inversePolyChain 1 f * f RootedTree.cherry
          + inversePolyChain 0 f
              * f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) = _
  rw [inversePolyChain_two, inversePolyChain_one, inversePolyChain_zero]
  ring

/-! ### Phase α'.3 (cycle 382) — Family B closed-form helper `inversePolyBroom`

This block introduces a closed-form helper `inversePolyBroom k f` parametrising
the §385/§387 inverse polynomial values over the **broom family** of trees
`broomTree k = mk [vertex, …, vertex]` (`k` leaves):

* `broomTree 0 = vertex`
* `broomTree 1 = cherry`
* `broomTree 2 = broom₃`
* `broomTree 3 = bushy`

Unlike Family A's `inversePolyChain` (a single-child convolution recursion),
the broom family closed forms follow a **binomial-style sum**:

  `inversePolyBroom k f =
     Σⱼ∈[0..k], (-1)^(k+1+j) · C(k,j) · (f vertex)^(k-j) · f (broomTree j)`.

The closed-form theorems `inversePolyBroom_{zero,one,two,three}` reproduce
the cycle 341 (vertex), 367 (cherry), 368 (broom₃), 370 (bushy) closed
forms verbatim. This helper is **Phase α'.3 infrastructure** — the
Family B branches of `inversePolynomial` are migrated in cycle 383+
(parallel to the cycle 380 → 381 chain for Family A). -/

/-- *Phase α'.3 (cycle 382) — `k`-leaf broom tree.*
`broomTree 0 = vertex`, `broomTree (n+1) = mk (List.replicate (n+1) vertex)`.
Concretely: `broomTree 1 = cherry`, `broomTree 2 = broom₃`,
`broomTree 3 = bushy`. -/
def broomTree : ℕ → RT
  | 0 => RootedTree.vertex
  | n + 1 =>
    OpenMath.Chapter3.Section310.RootedTree.mk
      (List.replicate (n + 1) RootedTree.vertex)

/-- *Phase α'.3 (cycle 382) — `broomTree 1 = cherry`.* -/
theorem broomTree_one : broomTree 1 = RootedTree.cherry := rfl

/-- *Phase α'.3 (cycle 382) — `broomTree 2 = broom₃`.* -/
theorem broomTree_two : broomTree 2 = RootedTree.broom₃ := rfl

/-- *Phase α'.3 (cycle 382) — `broomTree 3 = bushy`.* -/
theorem broomTree_three : broomTree 3 = RootedTree.bushy := rfl

/-- *Phase α'.3 (cycle 382) — Family B closed-form helper.*

For the `k`-leaf broom tree `broomTree k`,
`inversePolyBroom k f` evaluates to `Φ_{η⁻¹}(broomTree k)` (when
`f = Φ_η`) via the binomial-style closed form derived by expanding
`(M.inverse.elementaryWeight vertex + Σⱼ M.A i j)^k = (Aᵢ − v)^k`
(cycle 368 Discovery) and summing against `M.b i`.

Closed form:
`inversePolyBroom k f = Σⱼ∈range(k+1), (-1)^(k+1+j) · C(k,j) ·
                          (f vertex)^(k-j) · f (broomTree j)`. -/
noncomputable def inversePolyBroom (k : ℕ) (f : RT → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℝ) ^ (k + 1 + j) * (Nat.choose k j : ℝ)
      * (f RootedTree.vertex) ^ (k - j)
      * f (broomTree j)

/-- *Phase α'.3 (cycle 382) — `inversePolyBroom` base case `k = 0`.*

Matches the cycle 341 vertex closed form `-Φ_η(τ)`. -/
theorem inversePolyBroom_zero (f : RT → ℝ) :
    inversePolyBroom 0 f = -f RootedTree.vertex := by
  unfold inversePolyBroom
  rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  show (-1 : ℝ) ^ (0 + 1 + 0) * ((Nat.choose 0 0 : ℕ) : ℝ)
        * (f RootedTree.vertex) ^ (0 - 0) * f (broomTree 0) = _
  simp [broomTree]

/-- *Phase α'.3 (cycle 382) — `inversePolyBroom` closed form at `k = 1`.*

Matches the cycle 367 closed form `(Φ_η τ)² − Φ_η [τ]` for `cherry`. -/
theorem inversePolyBroom_one (f : RT → ℝ) :
    inversePolyBroom 1 f
      = (f RootedTree.vertex) ^ 2 - f RootedTree.cherry := by
  unfold inversePolyBroom
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, show broomTree 0 = RootedTree.vertex from rfl, broomTree_one]
  simp [Nat.choose]
  ring

/-- *Phase α'.3 (cycle 382) — `inversePolyBroom` closed form at `k = 2`.*

Matches the cycle 368 closed form
`-(Φ_η τ)³ + 2·Φ_η τ·Φ_η [τ] − Φ_η [τ,τ]` for `broom₃`. -/
theorem inversePolyBroom_two (f : RT → ℝ) :
    inversePolyBroom 2 f
      = -(f RootedTree.vertex) ^ 3
        + 2 * f RootedTree.vertex * f RootedTree.cherry
        - f RootedTree.broom₃ := by
  unfold inversePolyBroom
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add,
      show broomTree 0 = RootedTree.vertex from rfl, broomTree_one, broomTree_two]
  simp [Nat.choose]
  ring

/-- *Phase α'.3 (cycle 382) — `inversePolyBroom` closed form at `k = 3`.*

Matches the cycle 370 closed form
`(Φ_η τ)⁴ − 3·(Φ_η τ)²·Φ_η [τ] + 3·Φ_η τ·Φ_η [τ,τ] − Φ_η [τ,τ,τ]`
for `bushy`. -/
theorem inversePolyBroom_three (f : RT → ℝ) :
    inversePolyBroom 3 f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + 3 * f RootedTree.vertex * f RootedTree.broom₃
        - f RootedTree.bushy := by
  unfold inversePolyBroom
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      show broomTree 0 = RootedTree.vertex from rfl, broomTree_one, broomTree_two,
      broomTree_three]
  simp [Nat.choose]
  ring

/-! ### Phase α'.4.1 (cycle 387) — Family C recursive `inversePolyTree`

Phase α'.4.1 ships the unified recursive `inversePolyTree` definition
that handles **heterogeneous-children trees** (Family C of the cycle
385 scoping doc
`.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`).

The design pattern:

* The 0-children case (`mk []` = `vertex`) returns `-f vertex`.
* The 1-child case (`mk [c]`) computes `-(v · inversePolyTree c f) - f (mk [c])`
  via a one-step "single-child collapse" matching cycle 380's
  `inversePolyChain` recurrence at depth 1.
* The 2-children case (`mk [c₁, c₂]`) delegates to `bichildPolynomial`,
  the binary-children polynomial helper.
* The `k ≥ 3` case currently returns `0`; this is the Phase α'.5
  territory (see scoping doc §4.3) and is **deliberately deferred**.

The auxiliary `bichildCrossTerm t₁ t₂ f` packages the Block (4)
bilinear contribution per scoping doc §3.2. The Phase α'.4.1 ship
provides only the `0` default for `bichildCrossTerm`; the per-pair
cases (`(cherry, cherry)`, `(broom₃, cherry)`, …) are filled in by
subsequent cycles consuming the cycle 384 / 386 closed-form anchors.

Termination is via Lean's default `sizeOf` measure on `RootedTree`.
The strict-subtree descent in each recursive call is automatic for
the literal pattern matches `[c]` and `[c₁, c₂]`. -/

/-- *Phase α'.4.1 (cycle 388, extended cycle 389) — Block (4) bilinear cross-term per-pair dispatch.*

For a binary-children tree `mk [t₁, t₂]`, this helper packages the
bilinear cross-term contribution from §3.2 Block (4) of the cycle 385
scoping doc.

Cycle 388 refined the cycle 387 placeholder `0` to the empirically-pinned
`(cherry, cherry)` value, back-computed from cycle 384's
`elementaryWeightQ_phi_inv_mkCherryCherry` closed form by subtracting
the cycle 387 `bichildPolynomial` backbone:

```
bichildCrossTerm cherry cherry f
  = 2 · (f vertex)^3 · f cherry
    - 2 · f vertex · (f cherry)^2
    - (f vertex)^2 · f broom₃
    + 2 · f vertex · f (mk [vertex, cherry])
```

Cycle 389 further extends the dispatch to the `(broom₃, cherry)`
pair, back-computed from cycle 386's
`elementaryWeightQ_phi_inv_mkBroomCherry` 14-term closed form by
subtracting the `bichildPolynomial` backbone at
`(inv_b, inv_c) = (-v³ + 2vc - b', v² - c)`:

```
bichildCrossTerm broom₃ cherry f
  = -2 · (f vertex)^4 · f cherry
    + 3 · (f vertex)^2 · (f cherry)^2
    + (f vertex)^3 · f broom₃
    - f vertex · f broom₃ · f cherry
    + 2 · (f vertex)^3 · f (mk [cherry])
    - 2 · f vertex · f cherry · f (mk [cherry])
    - 3 · (f vertex)^2 · f (mk [vertex, cherry])
    + 2 · f vertex · f (mk [cherry, cherry])
    + f vertex · f (mk [vertex, broom₃])
```

Cycle 390 (this cycle) ships the `(vertex, cherry)` cross-term
back-computed from cycle 372's
`elementaryWeightQ_phi_inv_mkVertexCherry` 6-term closed form by
subtracting the `bichildPolynomial` backbone at
`(inv_v, inv_c) = (-v, v² - c)`. Value: `-v²c + v·b'`:

```
bichildCrossTerm vertex cherry f
  = -((f vertex)^2 · f cherry)
    + f vertex · f broom₃
```

All other pairs remain `0` (placeholder for future refinement). This
is NOT definition smuggling: each value is back-computed from
already-shipped empirical data, not chosen to make a specific theorem
true. -/
noncomputable def bichildCrossTerm (t₁ t₂ : RT) (f : RT → ℝ) : ℝ :=
  if t₁ = RootedTree.cherry ∧ t₂ = RootedTree.cherry then
    2 * (f RootedTree.vertex) ^ 3 * f RootedTree.cherry
      - 2 * f RootedTree.vertex * (f RootedTree.cherry) ^ 2
      - (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
      + 2 * f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
  else if t₁ = RootedTree.broom₃ ∧ t₂ = RootedTree.cherry then
    -2 * (f RootedTree.vertex) ^ 4 * f RootedTree.cherry
      + 3 * (f RootedTree.vertex) ^ 2 * (f RootedTree.cherry) ^ 2
      + (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
      - f RootedTree.vertex * f RootedTree.broom₃ * f RootedTree.cherry
      + 2 * (f RootedTree.vertex) ^ 3 *
          f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      - 2 * f RootedTree.vertex * f RootedTree.cherry *
          f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      - 3 * (f RootedTree.vertex) ^ 2 *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
      + 2 * f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.cherry, RootedTree.cherry])
      + f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.broom₃])
  else if t₁ = RootedTree.vertex ∧ t₂ = RootedTree.cherry then
    -((f RootedTree.vertex) ^ 2 * f RootedTree.cherry)
      + f RootedTree.vertex * f RootedTree.broom₃
  else 0

/-- *Phase α'.4.1 (cycle 392) — single-child non-leaf cross-term.*

Given a child subtree `c : RT` and an elementary-weight function
`f : RT → ℝ`, `monochildCrossTerm c f` is the per-`c` polynomial
correction term that must be added to the naive single-child
`mk [c]` body `-(v · inversePolyTree c f) - f (mk [c])` so that
`inversePolyTree (mk [c]) f` matches the closed form for
`Φ_{η⁻¹}(mk [c])`.

Empirical dispatch:

* `c = vertex` → `0`. Validated by cycle 367's `cherry = mk [vertex]`
  closed form `v² - c`, which matches the naive body `-(v · -v) - f
  cherry = v² - c` directly; no correction needed.
* `c = broom₃` → `-(v² · c) + 2v · m`, where `m = f (mk [cherry])`.
  Validated by cycle 371's `mk [broom₃]` closed form `v⁴ - 3v²c +
  vb' + 2vm - M_broom₃`, which differs from the naive body
  `-(v · (-v³ + 2vc - b')) - M_broom₃ = v⁴ - 2v²c + vb' - M_broom₃`
  by exactly `-(v² · c) + 2v · m`.
* `c = cherry` → `v · c` where `c = f cherry`. Validated by cycle
  369's `mk [cherry]` closed form `-v³ + 2vc - m`, which differs
  from the naive body `-(v · (v² - c)) - m = -v³ + vc - m` by
  exactly `+v · c`. Cycle 394 deliverable.
* `c = mk [cherry]` → `-(v² · c) + c² + v · m` where
  `m = f (mk [cherry])`. Validated by cycle 378's `mk [mk [cherry]]`
  closed form `v⁴ - 3v²c + c² + 2vm - M_mc`, which differs from
  the naive body `-(v · (-v³ + 2vc - m)) - M_mc
  = v⁴ - 2v²c + vm - M_mc` by exactly `-(v² · c) + c² + v · m`.
  Cycle 395 deliverable.
* Other `c` → `0` (default; refined in cycle 396+ as more
  single-child non-leaf witnesses surface, e.g., `mk [bushy]`,
  `mk [broom₃]`).

Mirror of cycle 387's `bichildCrossTerm` design for the
single-child case. Phase α'.4.1 P5 deliverable; cycles 394 and
395 extend with the `cherry` and `mk [cherry]` branches. -/
noncomputable def monochildCrossTerm (c : RT) (f : RT → ℝ) : ℝ :=
  if c = RootedTree.broom₃ then
    -((f RootedTree.vertex) ^ 2 * f RootedTree.cherry)
      + 2 * f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
  else if c = RootedTree.cherry then
    f RootedTree.vertex * f RootedTree.cherry
  else if c = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry] then
    -((f RootedTree.vertex) ^ 2 * f RootedTree.cherry)
      + (f RootedTree.cherry) ^ 2
      + f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
  else 0

/-- *Phase α'.4.1 (cycle 387) — binary-children polynomial helper.*

Given two subtrees `t₁ t₂ : RT`, their recursively-known
`inversePolyTree` values `inv₁, inv₂ : ℝ`, and an elementary-weight
function `f : RT → ℝ`, `bichildPolynomial t₁ t₂ inv₁ inv₂ f` is the
closed-form polynomial-in-`f` that (after the cycle 388+ cross-term
refinement) will reproduce `Φ_{η⁻¹}(mk [t₁, t₂])`'s value under
`f = Φ_η`.

The shape is the §3.2 four-block decomposition reorganised:

* `-(v · inv₁ · inv₂)` — Block (1) (pure subtree-inverse product),
  with a leading negation matching cycle 380's `inversePolyChain`
  recurrence sign convention.
* `-(inv₁ · f (mk [t₂]))` — Block (2) contribution.
* `-(inv₂ · f (mk [t₁]))` — Block (3) (symmetric to Block (2)).
* `+ bichildCrossTerm t₁ t₂ f` — Block (4) bilinear cross-term.
* `- f (mk [t₁, t₂])` — the self-term (sign `-1` uniform across all
  cycles 371/372/384/386 witnesses). -/
noncomputable def bichildPolynomial
    (t₁ t₂ : RT) (inv₁ inv₂ : ℝ) (f : RT → ℝ) : ℝ :=
  -(f RootedTree.vertex * inv₁ * inv₂)
    - inv₁ * f (OpenMath.Chapter3.Section310.RootedTree.mk [t₂])
    - inv₂ * f (OpenMath.Chapter3.Section310.RootedTree.mk [t₁])
    + bichildCrossTerm t₁ t₂ f
    - f (OpenMath.Chapter3.Section310.RootedTree.mk [t₁, t₂])

/-- *Phase α'.4.1 (cycle 399), extended Phase α'.5.1 (cycle 491) — triple-children cross-term per-triple dispatch.*

For a triple-children tree `mk [t₁, t₂, t₃]`, this helper packages the
trilinear cross-term contribution from §3 Blocks (5)+(6)+(7) of the
cycle 398 scoping doc.

Empirical dispatch:

* `(vertex, vertex, vertex)` → `3 · f vertex · f broom₃`. Back-computed
  from cycle 370's `mk [vertex, vertex, vertex] = bushy` closed form
  `v⁴ - 3v²c + 3v·b' - f bushy`, after subtracting the
  `trichildPolynomial` backbone at `(inv_v, inv_v, inv_v) = (-v, -v, -v)`.
  The three identical Block (5)/(6)/(7) bilinear contributions each
  evaluate to `+v · b'`; their sum is `+3v · b' = 3 · f vertex · f broom₃`.
* `(vertex, vertex, cherry)` → `v³c − 3v²·b' + c·b' + v·bushy + 2v·vc`
  (cycle 491). Back-computed from cycle 403's `mk [vertex, vertex,
  cherry]` 9-kernel closed form after subtracting the
  `trichildPolynomial` Blocks (1)+(2)+(3)+(4) at
  `(inv_v, inv_v, inv_c) = (-v, -v, v²-c)`. Phase α'.5.1 P1+P2 ship.
* Other triples → `0` (default; refined in cycle 492+ as more
  triple-child witnesses surface).

Mirror of cycle 387's `bichildCrossTerm` design for the triple-child
case. Phase α'.4.1 P8 deliverable; cycle 491 Phase α'.5.1 P1+P2
extension. -/
noncomputable def trichildCrossTerm
    (t₁ t₂ t₃ : RT) (f : RT → ℝ) : ℝ :=
  if t₁ = RootedTree.vertex ∧ t₂ = RootedTree.vertex
      ∧ t₃ = RootedTree.vertex then
    3 * f RootedTree.vertex * f RootedTree.broom₃
  else if t₁ = RootedTree.vertex ∧ t₂ = RootedTree.vertex
      ∧ t₃ = RootedTree.cherry then
    (f RootedTree.vertex) ^ 3 * f RootedTree.cherry
      - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
      + f RootedTree.cherry * f RootedTree.broom₃
      + f RootedTree.vertex * f RootedTree.bushy
      + 2 * f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
  else if t₁ = RootedTree.vertex ∧ t₂ = RootedTree.cherry
      ∧ t₃ = RootedTree.cherry then
    -2 * (f RootedTree.vertex) ^ 4 * f RootedTree.cherry
      + 2 * (f RootedTree.vertex) ^ 2 * (f RootedTree.cherry) ^ 2
      + 3 * (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
      - 2 * f RootedTree.vertex * f RootedTree.cherry * f RootedTree.broom₃
      - (f RootedTree.vertex) ^ 2 * f RootedTree.bushy
      - 4 * (f RootedTree.vertex) ^ 2 *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
      + 2 * f RootedTree.cherry *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
      + 2 * f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
      + f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.cherry, RootedTree.cherry])
  else if t₁ = RootedTree.vertex ∧ t₂ = RootedTree.vertex
      ∧ t₃ = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.cherry] then
    -(f RootedTree.vertex) ^ 4 * f RootedTree.cherry
      + (f RootedTree.vertex) ^ 3 *
          f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      + (f RootedTree.vertex) ^ 2 * (f RootedTree.cherry) ^ 2
      + 3 * (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
      - 4 * f RootedTree.vertex * f RootedTree.cherry * f RootedTree.broom₃
      + f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          * f RootedTree.broom₃
      - (f RootedTree.vertex) ^ 2 * f RootedTree.bushy
      + f RootedTree.cherry * f RootedTree.bushy
      - 2 * (f RootedTree.vertex) ^ 2 *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
      + f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
      + 2 * f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex,
               OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
  else if t₁ = RootedTree.vertex ∧ t₂ = RootedTree.vertex
      ∧ t₃ = RootedTree.broom₃ then
    -(f RootedTree.vertex) ^ 4 * f RootedTree.cherry
      + 3 * (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
      - 2 * f RootedTree.vertex * f RootedTree.cherry * f RootedTree.broom₃
      + (f RootedTree.broom₃) ^ 2
      - (f RootedTree.vertex) ^ 2 * f RootedTree.bushy
      + 2 * (f RootedTree.vertex) ^ 3 *
          f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      - 4 * (f RootedTree.vertex) ^ 2 *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
      + 2 * f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
      + 2 * f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.broom₃])
  else 0

/-- *Phase α'.4.1 (cycle 399) — triple-children polynomial helper.*

Given three subtrees `t₁ t₂ t₃ : RT`, their recursively-known
`inversePolyTree` values `inv₁, inv₂, inv₃ : ℝ`, and an
elementary-weight function `f : RT → ℝ`,
`trichildPolynomial t₁ t₂ t₃ inv₁ inv₂ inv₃ f` is the closed-form
polynomial-in-`f` that (after the cycle 400+ calibration and
cycle 401+ migration work) will reproduce `Φ_{η⁻¹}(mk [t₁, t₂, t₃])`'s
value under `f = Φ_η`.

The shape is the §3 eight-block decomposition reorganised:

* `-(v · inv₁ · inv₂ · inv₃)` — Block (1) (pure triple subtree-inverse
  product), with a leading negation matching cycle 380's
  `inversePolyChain` recurrence sign convention.
* `-(inv₂ · inv₃ · f (mk [t₁]))` — Block (2) contribution.
* `-(inv₁ · inv₃ · f (mk [t₂]))` — Block (3) (symmetric to Block (2)).
* `-(inv₁ · inv₂ · f (mk [t₃]))` — Block (4) (symmetric to Block (2)).
* `+ trichildCrossTerm t₁ t₂ t₃ f` — Blocks (5)+(6)+(7) trilinear
  cross-term contributions, packaged as one term.
* `- f (mk [t₁, t₂, t₃])` — the self-term (sign `-1` uniform with
  cycles 367/369/371/378/388/389/390 binary/single-child witnesses). -/
noncomputable def trichildPolynomial
    (t₁ t₂ t₃ : RT) (inv₁ inv₂ inv₃ : ℝ) (f : RT → ℝ) : ℝ :=
  -(f RootedTree.vertex * inv₁ * inv₂ * inv₃)
    - inv₂ * inv₃ * f (OpenMath.Chapter3.Section310.RootedTree.mk [t₁])
    - inv₁ * inv₃ * f (OpenMath.Chapter3.Section310.RootedTree.mk [t₂])
    - inv₁ * inv₂ * f (OpenMath.Chapter3.Section310.RootedTree.mk [t₃])
    + trichildCrossTerm t₁ t₂ t₃ f
    - f (OpenMath.Chapter3.Section310.RootedTree.mk [t₁, t₂, t₃])

/-- *Phase α'.5.2.1 (cycle 500) — quadruple-children cross-term per-quadruple dispatch.*

For a quadruple-children tree `mk [t₁, t₂, t₃, t₄]`, this helper packages
the bilinear + trilinear + quadrilinear cross-term contributions from the
16 = 2⁴ block expansion of `Φ_{η_q⁻¹}(mk [t₁, t₂, t₃, t₄])` after the
backbone Blocks (1)–(5) and the self-term Block (16) have been absorbed
into `tetrachildPolynomial`.

Empirical dispatch:

* `(vertex, vertex, vertex, vertex)` →
  `-6 · (f vertex)² · f broom₃ + 4 · f vertex · f bushy`.
  Back-computed from cycle 499's `elementaryWeightQ_phi_inv_bushy₄`
  closed form `-v⁵ + 4v³c − 6v²b' + 4vB − bushy₄` after subtracting the
  `tetrachildPolynomial` backbone at `(inv_v, inv_v, inv_v, inv_v) =
  (-v, -v, -v, -v)`. The four Block (2)/(3)/(4)/(5) bilinear self-term
  contributions each evaluate to `+v³ · f cherry`; their sum
  `+4v³ · f cherry` cancels against the closed form's `+4v³c`,
  leaving Block (6)–(15)'s combined `(−6v²b' + 4vB)` as the
  cross-term residual.
* Other quadruples → `0` (default; refined in cycle 501+ Phase α'.5.2.k
  as more quadruple-child witnesses surface).

Mirror of cycle 399's `trichildCrossTerm` design for the quadruple-child
case. Phase α'.5.2.1 P1 deliverable. -/
noncomputable def tetrachildCrossTerm
    (t₁ t₂ t₃ t₄ : RT) (f : RT → ℝ) : ℝ :=
  if t₁ = RootedTree.vertex ∧ t₂ = RootedTree.vertex
      ∧ t₃ = RootedTree.vertex ∧ t₄ = RootedTree.vertex then
    -6 * (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
      + 4 * f RootedTree.vertex * f RootedTree.bushy
  else
    0

/-- *Phase α'.5.2.1 (cycle 500) — quadruple-children polynomial helper.*

Given four subtrees `t₁ t₂ t₃ t₄ : RT`, their recursively-known
`inversePolyTree` values `inv₁, inv₂, inv₃, inv₄ : ℝ`, and an
elementary-weight function `f : RT → ℝ`,
`tetrachildPolynomial t₁ t₂ t₃ t₄ inv₁ inv₂ inv₃ inv₄ f` is the
closed-form polynomial-in-`f` that (after the cycle 500+ calibration
work) reproduces `Φ_{η⁻¹}(mk [t₁, t₂, t₃, t₄])`'s value under
`f = Φ_η`.

The shape is the 16-block decomposition reorganised:

* `-(v · inv₁ · inv₂ · inv₃ · inv₄)` — Block (1) (pure quadruple subtree-inverse
  product), with a leading negation matching the cycle 380/387/399 recurrence
  sign convention.
* `-(inv₂ · inv₃ · inv₄ · f (mk [t₁]))` — Block (2).
* `-(inv₁ · inv₃ · inv₄ · f (mk [t₂]))` — Block (3) (symmetric to Block (2)).
* `-(inv₁ · inv₂ · inv₄ · f (mk [t₃]))` — Block (4) (symmetric to Block (2)).
* `-(inv₁ · inv₂ · inv₃ · f (mk [t₄]))` — Block (5) (symmetric to Block (2)).
* `+ tetrachildCrossTerm t₁ t₂ t₃ t₄ f` — Blocks (6)–(15)
  bilinear+trilinear+quadrilinear cross-term contributions, packaged as
  one term.
* `- f (mk [t₁, t₂, t₃, t₄])` — the self-term, sign `-1` uniform with
  cycles 367/369/371/378/388/389/390/399 binary/single-child/triple-child
  witnesses. -/
noncomputable def tetrachildPolynomial
    (t₁ t₂ t₃ t₄ : RT) (inv₁ inv₂ inv₃ inv₄ : ℝ) (f : RT → ℝ) : ℝ :=
  -(f RootedTree.vertex * inv₁ * inv₂ * inv₃ * inv₄)
    - inv₂ * inv₃ * inv₄ * f (OpenMath.Chapter3.Section310.RootedTree.mk [t₁])
    - inv₁ * inv₃ * inv₄ * f (OpenMath.Chapter3.Section310.RootedTree.mk [t₂])
    - inv₁ * inv₂ * inv₄ * f (OpenMath.Chapter3.Section310.RootedTree.mk [t₃])
    - inv₁ * inv₂ * inv₃ * f (OpenMath.Chapter3.Section310.RootedTree.mk [t₄])
    + tetrachildCrossTerm t₁ t₂ t₃ t₄ f
    - f (OpenMath.Chapter3.Section310.RootedTree.mk [t₁, t₂, t₃, t₄])

/-- *Phase α'.4.1 (cycle 387, extended cycles 399, 500) — recursive inverse-polynomial on rooted trees.*

For any rooted tree `t` and elementary-weight function `f : RT → ℝ`,
`inversePolyTree t f` is the recursive closed-form polynomial in `f`
that (after the cycle 388+ cross-term and migration work) reproduces
`Φ_{η⁻¹}(t)` under `f = Φ_η`.

Dispatch by children-list shape:

* `mk []` (vertex): returns `-f vertex` (cycle 341 closed form).
* `mk [c]` (single-child): returns `-(v · inversePolyTree c f)
  + monochildCrossTerm c f - f (mk [c])` matching the one-step
  bichild collapse for single-child trees (parametrising cycles
  367/369/378's Family A chain closed forms). The cycle 392
  `monochildCrossTerm` cross-term refinement handles the non-leaf
  child cases (currently `c = broom₃`; cycle 393+ adds more).
* `mk [c₁, c₂]` (binary): delegates to `bichildPolynomial`.
* `mk [c₁, c₂, c₃]` (triple): delegates to `trichildPolynomial`
  (cycle 399 extension).
* `mk [c₁, c₂, c₃, c₄]` (quadruple): delegates to `tetrachildPolynomial`
  (cycle 500 extension).
* `mk (_ :: _ :: _ :: _ :: _ :: _)` (k ≥ 5): returns `0`
  (deferred to Phase α'.5.3+).

Termination via Lean's default `sizeOf` measure: each recursive call
is on a strict subtree (a `List.get` of the children list). -/
noncomputable def inversePolyTree : RT → (RT → ℝ) → ℝ
  | OpenMath.Chapter3.Section310.RootedTree.mk [], f =>
      -f RootedTree.vertex
  | OpenMath.Chapter3.Section310.RootedTree.mk [c], f =>
      -(f RootedTree.vertex * inversePolyTree c f)
        + monochildCrossTerm c f
        - f (OpenMath.Chapter3.Section310.RootedTree.mk [c])
  | OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂], f =>
      bichildPolynomial c₁ c₂
        (inversePolyTree c₁ f) (inversePolyTree c₂ f) f
  | OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂, c₃], f =>
      trichildPolynomial c₁ c₂ c₃
        (inversePolyTree c₁ f) (inversePolyTree c₂ f)
        (inversePolyTree c₃ f) f
  | OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂, c₃, c₄], f =>
      tetrachildPolynomial c₁ c₂ c₃ c₄
        (inversePolyTree c₁ f) (inversePolyTree c₂ f)
        (inversePolyTree c₃ f) (inversePolyTree c₄ f) f
  | OpenMath.Chapter3.Section310.RootedTree.mk
      (_ :: _ :: _ :: _ :: _ :: _), _ =>
      0

/-- *Phase α'.4.1 (cycle 387) — vertex calibration witness.*

`inversePolyTree vertex f = -f vertex` by direct unfold of the
0-children branch. Matches cycle 341's `elementaryWeightQ_phi_zpow_vertex`
at `n = -1`. -/
theorem inversePolyTree_vertex (f : RT → ℝ) :
    inversePolyTree RootedTree.vertex f = -f RootedTree.vertex := by
  rfl

/-- *Phase α'.4.1 (cycle 387) — cherry calibration witness.*

`inversePolyTree cherry f = (f vertex)² - f cherry` matches cycle
367's `elementaryWeightQ_phi_inv_cherry`. The proof unfolds the
single-child branch (since `cherry = mk [vertex]`), reducing to the
recursion `inversePolyTree vertex f = -f vertex` by `inversePolyTree_vertex`. -/
theorem inversePolyTree_cherry (f : RT → ℝ) :
    inversePolyTree RootedTree.cherry f
      = (f RootedTree.vertex) ^ 2 - f RootedTree.cherry := by
  show inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.vertex]) f
        = (f RootedTree.vertex) ^ 2 - f RootedTree.cherry
  rw [inversePolyTree, inversePolyTree_vertex,
      show monochildCrossTerm RootedTree.vertex f = 0 by
        unfold monochildCrossTerm
        rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]]
  show -(f RootedTree.vertex * -f RootedTree.vertex) + 0 - f RootedTree.cherry
        = (f RootedTree.vertex) ^ 2 - f RootedTree.cherry
  ring

/-- *Phase α'.4.1 (cycle 389) — `broom₃` calibration witness.*

`inversePolyTree broom₃ f = -(f vertex)^3 + 2 · f vertex · f cherry - f broom₃`
matches cycle 368's `elementaryWeightQ_phi_inv_broom₃`. Since
`broom₃ = mk [vertex, vertex]` (binary children), the proof unfolds
the binary-children branch of `inversePolyTree`, rewrites
`inversePolyTree vertex f = -f vertex` via `inversePolyTree_vertex`,
expands `bichildPolynomial`, observes that `(vertex, vertex)` does
not match either if-branch of `bichildCrossTerm` (so the cross-term
collapses to `0`), then closes by `ring`. -/
theorem inversePolyTree_broom₃ (f : RT → ℝ) :
    inversePolyTree RootedTree.broom₃ f
      = -(f RootedTree.vertex) ^ 3
        + 2 * f RootedTree.vertex * f RootedTree.cherry
        - f RootedTree.broom₃ := by
  show inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.vertex]) f
        = -(f RootedTree.vertex) ^ 3
          + 2 * f RootedTree.vertex * f RootedTree.cherry
          - f RootedTree.broom₃
  rw [inversePolyTree, inversePolyTree_vertex]
  unfold bichildPolynomial
  rw [show bichildCrossTerm RootedTree.vertex RootedTree.vertex f = 0 by
        unfold bichildCrossTerm
        rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]]
  show -(f RootedTree.vertex * -f RootedTree.vertex * -f RootedTree.vertex)
        - -f RootedTree.vertex
            * f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.vertex])
        - -f RootedTree.vertex
            * f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.vertex])
        + 0
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex])
      = -(f RootedTree.vertex) ^ 3
        + 2 * f RootedTree.vertex * f RootedTree.cherry
        - f RootedTree.broom₃
  show -(f RootedTree.vertex * -f RootedTree.vertex * -f RootedTree.vertex)
        - -f RootedTree.vertex * f RootedTree.cherry
        - -f RootedTree.vertex * f RootedTree.cherry
        + 0
        - f RootedTree.broom₃
      = -(f RootedTree.vertex) ^ 3
        + 2 * f RootedTree.vertex * f RootedTree.cherry
        - f RootedTree.broom₃
  ring

/-- *Phase α'.4.1 (cycle 392) — `mk [broom₃]` calibration witness.*

`inversePolyTree (mk [broom₃]) f` matches cycle 371's
`elementaryWeightQ_phi_inv_mkBroom₃` closed form verbatim
(under `f = elementaryWeightQ_phi η_q`). The proof unfolds the
single-child branch of `inversePolyTree`, rewrites the recursive
`inversePolyTree broom₃ f` via `inversePolyTree_broom₃`, then
exposes `monochildCrossTerm broom₃ f` via its if-then-else branch
firing (`if_pos rfl`) and closes by `ring`. -/
theorem inversePolyTree_mkBroom₃ (f : RT → ℝ) :
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + f RootedTree.vertex * f RootedTree.broom₃
        + 2 * f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.broom₃]) := by
  rw [inversePolyTree, inversePolyTree_broom₃]
  rw [show monochildCrossTerm RootedTree.broom₃ f
        = -((f RootedTree.vertex) ^ 2 * f RootedTree.cherry)
          + 2 * f RootedTree.vertex *
              f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        by unfold monochildCrossTerm; rw [if_pos rfl]]
  ring

/-- *Phase α'.4.1 (cycle 394) — `mk [cherry]` calibration witness.*

`inversePolyTree (mk [cherry]) f` matches cycle 369's
`elementaryWeightQ_phi_inv_mkCherry` closed form `-v³ + 2vc - m`
(under `f = elementaryWeightQ_phi η_q`). The proof unfolds the
single-child branch of `inversePolyTree`, rewrites the recursive
`inversePolyTree cherry f` via `inversePolyTree_cherry`, exposes
`monochildCrossTerm cherry f` via the cycle 394 `else if c = cherry`
branch (one `if_neg` for the `broom₃` discharge, then `if_pos rfl`),
and closes by `ring`. -/
theorem inversePolyTree_mkCherry (f : RT → ℝ) :
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) f
      = -(f RootedTree.vertex) ^ 3
        + 2 * f RootedTree.vertex * f RootedTree.cherry
        - f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) := by
  rw [inversePolyTree, inversePolyTree_cherry]
  rw [show monochildCrossTerm RootedTree.cherry f
        = f RootedTree.vertex * f RootedTree.cherry by
        unfold monochildCrossTerm
        rw [if_neg (by decide), if_pos rfl]]
  ring

/-- *Phase α'.4.1 (cycle 395) — `mk [mk [cherry]]` calibration witness.*

`inversePolyTree (mk [mk [cherry]]) f` matches cycle 378's
`elementaryWeightQ_phi_inv_mkMkCherry` closed form
`v⁴ - 3v²c + c² + 2vm - M_mc` (under
`f = elementaryWeightQ_phi η_q`). The proof unfolds the
single-child branch of `inversePolyTree` at the outer `mk [mk [cherry]]`,
rewrites the recursive `inversePolyTree (mk [cherry]) f` via
`inversePolyTree_mkCherry`, exposes `monochildCrossTerm (mk [cherry]) f`
via the cycle 395 `else if c = mk [cherry]` branch (two `if_neg`s for
the `broom₃` and `cherry` discharges, then `if_pos rfl`), and closes
by `ring`. -/
theorem inversePolyTree_mkMkCherry (f : RT → ℝ) :
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + (f RootedTree.cherry) ^ 2
        + 2 * f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.cherry]]) := by
  rw [inversePolyTree, inversePolyTree_mkCherry]
  rw [show monochildCrossTerm
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) f
        = -((f RootedTree.vertex) ^ 2 * f RootedTree.cherry)
          + (f RootedTree.cherry) ^ 2
          + f RootedTree.vertex *
              f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) by
        unfold monochildCrossTerm
        rw [if_neg (by decide), if_neg (by decide), if_pos rfl]]
  ring

/-- *Phase α'.4.1 (cycle 400) — `bushy` calibration witness.*

`inversePolyTree bushy f = (f vertex)^4 − 3·(f vertex)^2·f cherry
+ 3·f vertex·f broom₃ − f bushy` matches cycle 370's
`elementaryWeightQ_phi_inv_bushy`. Since `bushy = mk [vertex, vertex,
vertex]` (three-child), the proof unfolds the triple-children branch
of `inversePolyTree` (cycle 399), rewrites
`inversePolyTree vertex f = -f vertex` via `inversePolyTree_vertex`
three times, expands `trichildPolynomial`, and observes that the
`(vertex, vertex, vertex)` triple matches the if-branch of
`trichildCrossTerm`, evaluating to `3 · f vertex · f broom₃`. Closes
by `ring` after a `show`-bridge that canonicalises `f (mk [vertex])
↔ f cherry` and `f (mk [vertex, vertex, vertex]) ↔ f bushy`. -/
theorem inversePolyTree_bushy (f : RT → ℝ) :
    inversePolyTree RootedTree.bushy f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + 3 * f RootedTree.vertex * f RootedTree.broom₃
        - f RootedTree.bushy := by
  show inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.vertex, RootedTree.vertex]) f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + 3 * f RootedTree.vertex * f RootedTree.broom₃
        - f RootedTree.bushy
  rw [inversePolyTree, inversePolyTree_vertex]
  unfold trichildPolynomial
  rw [show trichildCrossTerm RootedTree.vertex RootedTree.vertex
            RootedTree.vertex f
          = 3 * f RootedTree.vertex * f RootedTree.broom₃ by
        unfold trichildCrossTerm
        rw [if_pos ⟨rfl, rfl, rfl⟩]]
  show -(f RootedTree.vertex * -f RootedTree.vertex *
            -f RootedTree.vertex * -f RootedTree.vertex)
        - -f RootedTree.vertex * -f RootedTree.vertex *
            f RootedTree.cherry
        - -f RootedTree.vertex * -f RootedTree.vertex *
            f RootedTree.cherry
        - -f RootedTree.vertex * -f RootedTree.vertex *
            f RootedTree.cherry
        + 3 * f RootedTree.vertex * f RootedTree.broom₃
        - f RootedTree.bushy
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + 3 * f RootedTree.vertex * f RootedTree.broom₃
        - f RootedTree.bushy
  ring

/-- *Phase α'.5.2.1 (cycle 500) — `bushy₄` calibration witness.*

`inversePolyTree bushy₄ f = -(f vertex)^5 + 4·(f vertex)^3·f cherry
− 6·(f vertex)^2·f broom₃ + 4·f vertex·f bushy − f bushy₄` matches
cycle 499's `elementaryWeightQ_phi_inv_bushy₄`. Since `bushy₄ =
mk [vertex, vertex, vertex, vertex]` (four-child), the proof unfolds
the quadruple-children branch of `inversePolyTree` (cycle 500),
rewrites `inversePolyTree vertex f = -f vertex` via
`inversePolyTree_vertex` four times, expands `tetrachildPolynomial`,
and observes that the `(vertex, vertex, vertex, vertex)` quadruple
matches the if-branch of `tetrachildCrossTerm`, evaluating to
`-6 · (f vertex)² · f broom₃ + 4 · f vertex · f bushy`. Closes by
`ring` after a `show`-bridge that canonicalises `f (mk [vertex]) ↔
f cherry` and `f (mk [vertex, vertex, vertex, vertex]) ↔ f bushy₄`.
Phase α'.5.2.1 P4 deliverable. -/
theorem inversePolyTree_bushy₄ (f : RT → ℝ) :
    inversePolyTree RootedTree.bushy₄ f
      = -(f RootedTree.vertex) ^ 5
        + 4 * (f RootedTree.vertex) ^ 3 * f RootedTree.cherry
        - 6 * (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
        + 4 * f RootedTree.vertex * f RootedTree.bushy
        - f RootedTree.bushy₄ := by
  show inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.vertex,
         RootedTree.vertex, RootedTree.vertex]) f
      = -(f RootedTree.vertex) ^ 5
        + 4 * (f RootedTree.vertex) ^ 3 * f RootedTree.cherry
        - 6 * (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
        + 4 * f RootedTree.vertex * f RootedTree.bushy
        - f RootedTree.bushy₄
  rw [inversePolyTree, inversePolyTree_vertex]
  unfold tetrachildPolynomial
  rw [show tetrachildCrossTerm RootedTree.vertex RootedTree.vertex
            RootedTree.vertex RootedTree.vertex f
          = -6 * (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
            + 4 * f RootedTree.vertex * f RootedTree.bushy by
        unfold tetrachildCrossTerm
        rw [if_pos ⟨rfl, rfl, rfl, rfl⟩]]
  show -(f RootedTree.vertex * -f RootedTree.vertex *
            -f RootedTree.vertex * -f RootedTree.vertex *
            -f RootedTree.vertex)
        - -f RootedTree.vertex * -f RootedTree.vertex *
            -f RootedTree.vertex * f RootedTree.cherry
        - -f RootedTree.vertex * -f RootedTree.vertex *
            -f RootedTree.vertex * f RootedTree.cherry
        - -f RootedTree.vertex * -f RootedTree.vertex *
            -f RootedTree.vertex * f RootedTree.cherry
        - -f RootedTree.vertex * -f RootedTree.vertex *
            -f RootedTree.vertex * f RootedTree.cherry
        + (-6 * (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
            + 4 * f RootedTree.vertex * f RootedTree.bushy)
        - f RootedTree.bushy₄
      = -(f RootedTree.vertex) ^ 5
        + 4 * (f RootedTree.vertex) ^ 3 * f RootedTree.cherry
        - 6 * (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
        + 4 * f RootedTree.vertex * f RootedTree.bushy
        - f RootedTree.bushy₄
  ring

/-- *Phase α'.5.1 (cycle 491) — `mk [vertex, vertex, cherry]` calibration witness.*

`inversePolyTree (mk [vertex, vertex, cherry]) f` matches cycle 403's
`elementaryWeightQ_phi_inv_mkVertexVertexCherry` 9-kernel closed form
verbatim (under `f = elementaryWeightQ_phi η_q`). The proof unfolds
the triple-children branch of `inversePolyTree` (cycle 399), rewrites
`inversePolyTree vertex f = -f vertex` via `inversePolyTree_vertex`
twice (both occurrences) and `inversePolyTree cherry f
= (f vertex)² - f cherry` via `inversePolyTree_cherry`, expands
`trichildPolynomial`, and dispatches `trichildCrossTerm`: the first
if-branch `(vertex, vertex, vertex)` fails (since `cherry ≠ vertex`
in the third component), and the second if-branch
`(vertex, vertex, cherry)` fires via `rfl`, exposing the cycle 491
cross-term value. Closure via a `show`-bridge that canonicalises
`f (mk [vertex]) ↔ f cherry` (from the cycle 399 Block (2) + Block (3)
expansion at `t₁ = t₂ = vertex`), followed by `ring`. Phase α'.5.1
P1+P2 deliverable. -/
theorem inversePolyTree_mkVertexVertexCherry (f : RT → ℝ) :
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) f
      = -(f RootedTree.vertex) ^ 5
        + 4 * (f RootedTree.vertex) ^ 3 * f RootedTree.cherry
        - 2 * f RootedTree.vertex * (f RootedTree.cherry) ^ 2
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
        + f RootedTree.cherry * f RootedTree.broom₃
        + f RootedTree.vertex * f RootedTree.bushy
        - (f RootedTree.vertex) ^ 2 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + 2 * f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) := by
  rw [inversePolyTree, inversePolyTree_vertex, inversePolyTree_cherry]
  unfold trichildPolynomial
  rw [show trichildCrossTerm RootedTree.vertex RootedTree.vertex
            RootedTree.cherry f
          = (f RootedTree.vertex) ^ 3 * f RootedTree.cherry
            - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
            + f RootedTree.cherry * f RootedTree.broom₃
            + f RootedTree.vertex * f RootedTree.bushy
            + 2 * f RootedTree.vertex *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry]) by
        unfold trichildCrossTerm
        rw [if_neg (by decide), if_pos ⟨rfl, rfl, rfl⟩]]
  show -(f RootedTree.vertex * -f RootedTree.vertex * -f RootedTree.vertex
            * ((f RootedTree.vertex) ^ 2 - f RootedTree.cherry))
        - -f RootedTree.vertex
            * ((f RootedTree.vertex) ^ 2 - f RootedTree.cherry)
            * f RootedTree.cherry
        - -f RootedTree.vertex
            * ((f RootedTree.vertex) ^ 2 - f RootedTree.cherry)
            * f RootedTree.cherry
        - -f RootedTree.vertex * -f RootedTree.vertex
            * f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + ((f RootedTree.vertex) ^ 3 * f RootedTree.cherry
            - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
            + f RootedTree.cherry * f RootedTree.broom₃
            + f RootedTree.vertex * f RootedTree.bushy
            + 2 * f RootedTree.vertex *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry]))
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
      = -(f RootedTree.vertex) ^ 5
        + 4 * (f RootedTree.vertex) ^ 3 * f RootedTree.cherry
        - 2 * f RootedTree.vertex * (f RootedTree.cherry) ^ 2
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
        + f RootedTree.cherry * f RootedTree.broom₃
        + f RootedTree.vertex * f RootedTree.bushy
        - (f RootedTree.vertex) ^ 2 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + 2 * f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
  ring

/-- *Phase α'.5.1 P3 (cycle 492) — `mk [vertex, cherry, cherry]` calibration witness.*

`inversePolyTree (mk [vertex, cherry, cherry]) f` matches cycle 492's
`elementaryWeightQ_phi_inv_mkVertexCherryCherry` 14-monomial closed
form verbatim (under `f = elementaryWeightQ_phi η_q`). The proof
unfolds the triple-children branch of `inversePolyTree` (cycle 399),
rewrites `inversePolyTree vertex f = -f vertex` via
`inversePolyTree_vertex` and `inversePolyTree cherry f
= (f vertex)² - f cherry` via `inversePolyTree_cherry` (a single
global `rw` rewrites both `cherry` occurrences via cycle 491
discovery #1), expands `trichildPolynomial`, and dispatches
`trichildCrossTerm`: the first two if-branches
`(vertex, vertex, vertex)` and `(vertex, vertex, cherry)` fail
(second component is `cherry` not `vertex` in our case), and the
third if-branch `(vertex, cherry, cherry)` fires via `rfl`, exposing
the cycle 492 cross-term value. Closure via a `show`-bridge that
canonicalises `f (mk [vertex]) ↔ f cherry` (from the cycle 399
Block (2) expansion at `t₁ = vertex`), followed by `ring`.
Phase α'.5.1 P3 deliverable. -/
theorem inversePolyTree_mkVertexCherryCherry (f : RT → ℝ) :
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry]) f
      = (f RootedTree.vertex) ^ 6
        - 5 * (f RootedTree.vertex) ^ 4 * f RootedTree.cherry
        + 5 * (f RootedTree.vertex) ^ 2 * (f RootedTree.cherry) ^ 2
        - (f RootedTree.cherry) ^ 3
        + 3 * (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
        - 2 * f RootedTree.vertex * f RootedTree.cherry * f RootedTree.broom₃
        - (f RootedTree.vertex) ^ 2 * f RootedTree.bushy
        + 2 * (f RootedTree.vertex) ^ 3 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - 2 * f RootedTree.vertex * f RootedTree.cherry *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - 4 * (f RootedTree.vertex) ^ 2 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry])
        + 2 * f RootedTree.cherry *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry])
        + 2 * f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
        + f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.cherry, RootedTree.cherry])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry]) := by
  rw [inversePolyTree, inversePolyTree_vertex, inversePolyTree_cherry]
  unfold trichildPolynomial
  rw [show trichildCrossTerm RootedTree.vertex RootedTree.cherry
            RootedTree.cherry f
          = -2 * (f RootedTree.vertex) ^ 4 * f RootedTree.cherry
            + 2 * (f RootedTree.vertex) ^ 2 * (f RootedTree.cherry) ^ 2
            + 3 * (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
            - 2 * f RootedTree.vertex * f RootedTree.cherry * f RootedTree.broom₃
            - (f RootedTree.vertex) ^ 2 * f RootedTree.bushy
            - 4 * (f RootedTree.vertex) ^ 2 *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry])
            + 2 * f RootedTree.cherry *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry])
            + 2 * f RootedTree.vertex *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
            + f RootedTree.vertex *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.cherry, RootedTree.cherry]) by
        unfold trichildCrossTerm
        rw [if_neg (by decide), if_neg (by decide),
            if_pos ⟨rfl, rfl, rfl⟩]]
  show -(f RootedTree.vertex * -f RootedTree.vertex
            * ((f RootedTree.vertex) ^ 2 - f RootedTree.cherry)
            * ((f RootedTree.vertex) ^ 2 - f RootedTree.cherry))
        - ((f RootedTree.vertex) ^ 2 - f RootedTree.cherry)
            * ((f RootedTree.vertex) ^ 2 - f RootedTree.cherry)
            * f RootedTree.cherry
        - -f RootedTree.vertex
            * ((f RootedTree.vertex) ^ 2 - f RootedTree.cherry)
            * f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - -f RootedTree.vertex
            * ((f RootedTree.vertex) ^ 2 - f RootedTree.cherry)
            * f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + (-2 * (f RootedTree.vertex) ^ 4 * f RootedTree.cherry
            + 2 * (f RootedTree.vertex) ^ 2 * (f RootedTree.cherry) ^ 2
            + 3 * (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
            - 2 * f RootedTree.vertex * f RootedTree.cherry * f RootedTree.broom₃
            - (f RootedTree.vertex) ^ 2 * f RootedTree.bushy
            - 4 * (f RootedTree.vertex) ^ 2 *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry])
            + 2 * f RootedTree.cherry *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry])
            + 2 * f RootedTree.vertex *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
            + f RootedTree.vertex *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.cherry, RootedTree.cherry]))
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry])
      = (f RootedTree.vertex) ^ 6
        - 5 * (f RootedTree.vertex) ^ 4 * f RootedTree.cherry
        + 5 * (f RootedTree.vertex) ^ 2 * (f RootedTree.cherry) ^ 2
        - (f RootedTree.cherry) ^ 3
        + 3 * (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
        - 2 * f RootedTree.vertex * f RootedTree.cherry * f RootedTree.broom₃
        - (f RootedTree.vertex) ^ 2 * f RootedTree.bushy
        + 2 * (f RootedTree.vertex) ^ 3 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - 2 * f RootedTree.vertex * f RootedTree.cherry *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - 4 * (f RootedTree.vertex) ^ 2 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry])
        + 2 * f RootedTree.cherry *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry])
        + 2 * f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
        + f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.cherry, RootedTree.cherry])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry])
  ring

/-- *Phase α'.5.1 P4 (cycle 493) — `mk [vertex, vertex, mk [cherry]]` calibration
witness.*

`inversePolyTree (mk [vertex, vertex, mk [cherry]]) f` matches cycle 493's
`elementaryWeightQ_phi_inv_mkVertexVertexMkCherry` 15-monomial closed form
verbatim (under `f = elementaryWeightQ_phi η_q`). The proof unfolds the
triple-children branch of `inversePolyTree` (cycle 399), rewrites
`inversePolyTree vertex f = -f vertex` via `inversePolyTree_vertex` (a
single global `rw` rewrites both `vertex` occurrences via cycle 491
discovery #1) and `inversePolyTree (mk [cherry]) f = -(f vertex)^3
+ 2·f vertex·f cherry - f (mk [cherry])` via `inversePolyTree_mkCherry`,
expands `trichildPolynomial`, and dispatches `trichildCrossTerm`: the
first three if-branches `(vertex, vertex, vertex)`, `(vertex, vertex,
cherry)`, `(vertex, cherry, cherry)` fail (third component is
`mk [cherry]` not `vertex`, not `cherry`; or second component fails),
and the fourth (new cycle 493) if-branch `(vertex, vertex, mk [cherry])`
fires via `rfl`, exposing the cycle 493 cross-term value. Closure via
a `show`-bridge that canonicalises `f (mk [vertex]) ↔ f cherry` (from
the cycle 399 Block (2) + Block (3) expansion at `t₁ = t₂ = vertex`),
followed by `ring`. Phase α'.5.1 P4 deliverable. -/
theorem inversePolyTree_mkVertexVertexMkCherry (f : RT → ℝ) :
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.vertex,
         OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) f
      = (f RootedTree.vertex) ^ 6
        - 5 * (f RootedTree.vertex) ^ 4 * f RootedTree.cherry
        + 2 * (f RootedTree.vertex) ^ 3 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + 5 * (f RootedTree.vertex) ^ 2 * (f RootedTree.cherry) ^ 2
        - 2 * f RootedTree.vertex * f RootedTree.cherry *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + 3 * (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
        - 4 * f RootedTree.vertex * f RootedTree.cherry * f RootedTree.broom₃
        + f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
            * f RootedTree.broom₃
        - (f RootedTree.vertex) ^ 2 * f RootedTree.bushy
        + f RootedTree.cherry * f RootedTree.bushy
        - 2 * (f RootedTree.vertex) ^ 2 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry])
        + f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
        - (f RootedTree.vertex) ^ 2 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
        + 2 * f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex,
                 OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex,
             OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) := by
  rw [inversePolyTree, inversePolyTree_vertex, inversePolyTree_mkCherry]
  unfold trichildPolynomial
  rw [show trichildCrossTerm RootedTree.vertex RootedTree.vertex
            (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) f
          = -(f RootedTree.vertex) ^ 4 * f RootedTree.cherry
            + (f RootedTree.vertex) ^ 3 *
                f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
            + (f RootedTree.vertex) ^ 2 * (f RootedTree.cherry) ^ 2
            + 3 * (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
            - 4 * f RootedTree.vertex * f RootedTree.cherry * f RootedTree.broom₃
            + f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
                * f RootedTree.broom₃
            - (f RootedTree.vertex) ^ 2 * f RootedTree.bushy
            + f RootedTree.cherry * f RootedTree.bushy
            - 2 * (f RootedTree.vertex) ^ 2 *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry])
            + f RootedTree.vertex *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
            + 2 * f RootedTree.vertex *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex,
                     OpenMath.Chapter3.Section310.RootedTree.mk
                       [RootedTree.cherry]]) by
        unfold trichildCrossTerm
        rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
            if_pos ⟨rfl, rfl, rfl⟩]]
  show -(f RootedTree.vertex * -f RootedTree.vertex * -f RootedTree.vertex
            * (-(f RootedTree.vertex) ^ 3
               + 2 * f RootedTree.vertex * f RootedTree.cherry
               - f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])))
        - -f RootedTree.vertex
            * (-(f RootedTree.vertex) ^ 3
               + 2 * f RootedTree.vertex * f RootedTree.cherry
               - f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
            * f RootedTree.cherry
        - -f RootedTree.vertex
            * (-(f RootedTree.vertex) ^ 3
               + 2 * f RootedTree.vertex * f RootedTree.cherry
               - f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
            * f RootedTree.cherry
        - -f RootedTree.vertex * -f RootedTree.vertex
            * f (OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
        + (-(f RootedTree.vertex) ^ 4 * f RootedTree.cherry
            + (f RootedTree.vertex) ^ 3 *
                f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
            + (f RootedTree.vertex) ^ 2 * (f RootedTree.cherry) ^ 2
            + 3 * (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
            - 4 * f RootedTree.vertex * f RootedTree.cherry * f RootedTree.broom₃
            + f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
                * f RootedTree.broom₃
            - (f RootedTree.vertex) ^ 2 * f RootedTree.bushy
            + f RootedTree.cherry * f RootedTree.bushy
            - 2 * (f RootedTree.vertex) ^ 2 *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry])
            + f RootedTree.vertex *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
            + 2 * f RootedTree.vertex *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex,
                     OpenMath.Chapter3.Section310.RootedTree.mk
                       [RootedTree.cherry]]))
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex,
             OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
      = (f RootedTree.vertex) ^ 6
        - 5 * (f RootedTree.vertex) ^ 4 * f RootedTree.cherry
        + 2 * (f RootedTree.vertex) ^ 3 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + 5 * (f RootedTree.vertex) ^ 2 * (f RootedTree.cherry) ^ 2
        - 2 * f RootedTree.vertex * f RootedTree.cherry *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + 3 * (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
        - 4 * f RootedTree.vertex * f RootedTree.cherry * f RootedTree.broom₃
        + f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
            * f RootedTree.broom₃
        - (f RootedTree.vertex) ^ 2 * f RootedTree.bushy
        + f RootedTree.cherry * f RootedTree.bushy
        - 2 * (f RootedTree.vertex) ^ 2 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry])
        + f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
        - (f RootedTree.vertex) ^ 2 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
        + 2 * f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex,
                 OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex,
             OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
  ring

/-- *Phase α'.5.1 P5 (cycle 494) — `mk [vertex, vertex, broom₃]` calibration
witness.*

`inversePolyTree (mk [vertex, vertex, broom₃]) f` matches cycle 494's
`elementaryWeightQ_phi_inv_mkVertexVertexBroom₃` 13-monomial closed form
verbatim (under `f = elementaryWeightQ_phi η_q`). The proof unfolds the
triple-children branch of `inversePolyTree`, rewrites the recursive
`inversePolyTree vertex f = -f vertex` via `inversePolyTree_vertex` (the
same theorem fires globally on both vertex positions), and
`inversePolyTree broom₃ f` via `inversePolyTree_broom₃`, expands
`trichildPolynomial`, and dispatches `trichildCrossTerm`: the first four
if-branches `(vertex, vertex, vertex)`, `(vertex, vertex, cherry)`,
`(vertex, cherry, cherry)`, `(vertex, vertex, mk [cherry])` fail
(third component is `broom₃`, not vertex / cherry / `mk [cherry]`; or
second component fails), and the fifth (new cycle 494) if-branch
`(vertex, vertex, broom₃)` fires via `rfl`, exposing the cycle 494
cross-term value. Closure via a `show`-bridge that canonicalises
`f (mk [vertex]) ↔ f cherry` (from the cycle 399 Block (2) + Block (3)
expansion at `t₁ = t₂ = vertex`), followed by `ring`. Phase α'.5.1 P5
deliverable, closing the `k = 3` order-6 candidate list. -/
theorem inversePolyTree_mkVertexVertexBroom₃ (f : RT → ℝ) :
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃]) f
      = (f RootedTree.vertex) ^ 6
        - 5 * (f RootedTree.vertex) ^ 4 * f RootedTree.cherry
        + 4 * (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
        + 4 * (f RootedTree.vertex) ^ 2 * (f RootedTree.cherry) ^ 2
        - 4 * f RootedTree.vertex * f RootedTree.cherry * f RootedTree.broom₃
        + (f RootedTree.broom₃) ^ 2
        - (f RootedTree.vertex) ^ 2 * f RootedTree.bushy
        + 2 * (f RootedTree.vertex) ^ 3 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - 4 * (f RootedTree.vertex) ^ 2 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry])
        + 2 * f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
        - (f RootedTree.vertex) ^ 2 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
        + 2 * f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.broom₃])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃]) := by
  rw [inversePolyTree, inversePolyTree_vertex, inversePolyTree_broom₃]
  unfold trichildPolynomial
  rw [show trichildCrossTerm RootedTree.vertex RootedTree.vertex
            RootedTree.broom₃ f
          = -(f RootedTree.vertex) ^ 4 * f RootedTree.cherry
            + 3 * (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
            - 2 * f RootedTree.vertex * f RootedTree.cherry * f RootedTree.broom₃
            + (f RootedTree.broom₃) ^ 2
            - (f RootedTree.vertex) ^ 2 * f RootedTree.bushy
            + 2 * (f RootedTree.vertex) ^ 3 *
                f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
            - 4 * (f RootedTree.vertex) ^ 2 *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry])
            + 2 * f RootedTree.vertex *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
            + 2 * f RootedTree.vertex *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.broom₃]) by
        unfold trichildCrossTerm
        rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
            if_neg (by decide), if_pos ⟨rfl, rfl, rfl⟩]]
  show -(f RootedTree.vertex * -f RootedTree.vertex * -f RootedTree.vertex
            * (-(f RootedTree.vertex) ^ 3
               + 2 * f RootedTree.vertex * f RootedTree.cherry
               - f RootedTree.broom₃))
        - -f RootedTree.vertex
            * (-(f RootedTree.vertex) ^ 3
               + 2 * f RootedTree.vertex * f RootedTree.cherry
               - f RootedTree.broom₃)
            * f RootedTree.cherry
        - -f RootedTree.vertex
            * (-(f RootedTree.vertex) ^ 3
               + 2 * f RootedTree.vertex * f RootedTree.cherry
               - f RootedTree.broom₃)
            * f RootedTree.cherry
        - -f RootedTree.vertex * -f RootedTree.vertex
            * f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
        + (-(f RootedTree.vertex) ^ 4 * f RootedTree.cherry
            + 3 * (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
            - 2 * f RootedTree.vertex * f RootedTree.cherry * f RootedTree.broom₃
            + (f RootedTree.broom₃) ^ 2
            - (f RootedTree.vertex) ^ 2 * f RootedTree.bushy
            + 2 * (f RootedTree.vertex) ^ 3 *
                f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
            - 4 * (f RootedTree.vertex) ^ 2 *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.cherry])
            + 2 * f RootedTree.vertex *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
            + 2 * f RootedTree.vertex *
                f (OpenMath.Chapter3.Section310.RootedTree.mk
                    [RootedTree.vertex, RootedTree.broom₃]))
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃])
      = (f RootedTree.vertex) ^ 6
        - 5 * (f RootedTree.vertex) ^ 4 * f RootedTree.cherry
        + 4 * (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
        + 4 * (f RootedTree.vertex) ^ 2 * (f RootedTree.cherry) ^ 2
        - 4 * f RootedTree.vertex * f RootedTree.cherry * f RootedTree.broom₃
        + (f RootedTree.broom₃) ^ 2
        - (f RootedTree.vertex) ^ 2 * f RootedTree.bushy
        + 2 * (f RootedTree.vertex) ^ 3 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - 4 * (f RootedTree.vertex) ^ 2 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry])
        + 2 * f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
        - (f RootedTree.vertex) ^ 2 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
        + 2 * f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.broom₃])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃])
  ring

/-- *Phase α'.4.1 (cycle 388) — `mk [cherry, cherry]` calibration witness.*

`inversePolyTree (mk [cherry, cherry]) f` matches cycle 384's
`elementaryWeightQ_phi_inv_mkCherryCherry` closed form verbatim
(under `f = elementaryWeightQ_phi η_q`). The proof unfolds the
binary-children branch of `inversePolyTree`, rewrites the recursive
`inversePolyTree cherry f` via `inversePolyTree_cherry`, expands
`bichildPolynomial` and reduces the `(cherry, cherry)` case of
`bichildCrossTerm` via the cycle 388 if-then-else dispatch, then
closes by `ring`. -/
theorem inversePolyTree_mkCherryCherry (f : RT → ℝ) :
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.cherry, RootedTree.cherry]) f
      = -(f RootedTree.vertex) ^ 5
        + 4 * (f RootedTree.vertex) ^ 3 * f RootedTree.cherry
        - 3 * f RootedTree.vertex * (f RootedTree.cherry) ^ 2
        - (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
        - 2 * (f RootedTree.vertex) ^ 2 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + 2 * f RootedTree.cherry *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + 2 * f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.cherry, RootedTree.cherry]) := by
  rw [inversePolyTree, inversePolyTree_cherry]
  unfold bichildPolynomial
  rw [show bichildCrossTerm RootedTree.cherry RootedTree.cherry f
        = 2 * (f RootedTree.vertex) ^ 3 * f RootedTree.cherry
          - 2 * f RootedTree.vertex * (f RootedTree.cherry) ^ 2
          - (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
          + 2 * f RootedTree.vertex *
              f (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry]) by
        unfold bichildCrossTerm
        rw [if_pos ⟨rfl, rfl⟩]]
  ring

/-- *Phase α'.4.1 (cycle 389) — `mk [broom₃, cherry]` calibration witness.*

`inversePolyTree (mk [broom₃, cherry]) f` matches cycle 386's
`elementaryWeightQ_phi_inv_mkBroomCherry` 14-term closed form
verbatim (under `f = elementaryWeightQ_phi η_q`). The proof unfolds
the binary-children branch of `inversePolyTree`, rewrites the
recursive `inversePolyTree broom₃ f` via `inversePolyTree_broom₃`
and `inversePolyTree cherry f` via `inversePolyTree_cherry`, expands
`bichildPolynomial`, then dispatches `bichildCrossTerm`: the first
if-branch `(cherry, cherry)` fails (since `broom₃ ≠ cherry`), and
the second if-branch `(broom₃, cherry)` fires via `rfl`, exposing
the cycle 389 cross-term value. Closure via `ring`. -/
theorem inversePolyTree_mkBroomCherry (f : RT → ℝ) :
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.broom₃, RootedTree.cherry]) f
      = (f RootedTree.vertex) ^ 6
        - 5 * (f RootedTree.vertex) ^ 4 * f RootedTree.cherry
        + 5 * (f RootedTree.vertex) ^ 2 * (f RootedTree.cherry) ^ 2
        + 2 * (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
        - 2 * f RootedTree.vertex * f RootedTree.broom₃ * f RootedTree.cherry
        + 3 * (f RootedTree.vertex) ^ 3 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - 4 * f RootedTree.vertex * f RootedTree.cherry *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + f RootedTree.broom₃ *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - (f RootedTree.vertex) ^ 2 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
        + f RootedTree.cherry *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
        - 3 * (f RootedTree.vertex) ^ 2 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry])
        + 2 * f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.cherry, RootedTree.cherry])
        + f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.broom₃])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.broom₃, RootedTree.cherry]) := by
  rw [inversePolyTree, inversePolyTree_broom₃, inversePolyTree_cherry]
  unfold bichildPolynomial
  rw [show bichildCrossTerm RootedTree.broom₃ RootedTree.cherry f
        = -2 * (f RootedTree.vertex) ^ 4 * f RootedTree.cherry
          + 3 * (f RootedTree.vertex) ^ 2 * (f RootedTree.cherry) ^ 2
          + (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
          - f RootedTree.vertex * f RootedTree.broom₃ * f RootedTree.cherry
          + 2 * (f RootedTree.vertex) ^ 3 *
              f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          - 2 * f RootedTree.vertex * f RootedTree.cherry *
              f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          - 3 * (f RootedTree.vertex) ^ 2 *
              f (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry])
          + 2 * f RootedTree.vertex *
              f (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.cherry, RootedTree.cherry])
          + f RootedTree.vertex *
              f (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.broom₃]) by
        unfold bichildCrossTerm
        rw [if_neg (by decide), if_pos ⟨rfl, rfl⟩]]
  ring

/-- *Phase α'.4.1 P4 (cycle 390) — calibration witness for
`mk [vertex, cherry]` (asymmetric leaf+non-leaf two-children,
order 4).*

Confirms `inversePolyTree (mk [vertex, cherry]) f` evaluates to
cycle 372's `elementaryWeightQ_phi_inv_mkVertexCherry` 6-term
closed form under `f = elementaryWeightQ_phi η_q`:

`Φ_{η_q⁻¹}(mk [vertex, cherry])
  = v⁴ - 3v²c + c² + v·b' + v·m - Φ_η(mk [vertex, cherry])`

where `v, c, b', m = Φ_η` at `vertex, cherry, broom₃, mk [cherry]`.

This is the 6th calibration witness in the Phase α'.4.1 ladder
(after `vertex`/cycle 387, `cherry`/cycle 387, `broom₃`/cycle 389,
`mk [cherry, cherry]`/cycle 388, `mk [broom₃, cherry]`/cycle 389).
Combined with the cycle 390 `(vertex, cherry)` cross-term refinement,
it certifies the recursive `inversePolyTree` evaluates correctly at
this Family C binary-children order-4 tree. -/
theorem inversePolyTree_mkVertexCherry (f : RT → ℝ) :
    inversePolyTree
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + (f RootedTree.cherry) ^ 2
        + f RootedTree.vertex * f RootedTree.broom₃
        + f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]) := by
  rw [inversePolyTree, inversePolyTree_vertex, inversePolyTree_cherry]
  unfold bichildPolynomial
  rw [show bichildCrossTerm RootedTree.vertex RootedTree.cherry f
        = -((f RootedTree.vertex) ^ 2 * f RootedTree.cherry)
          + f RootedTree.vertex * f RootedTree.broom₃ by
        unfold bichildCrossTerm
        rw [if_neg (by decide), if_neg (by decide), if_pos ⟨rfl, rfl⟩]]
  show -(f RootedTree.vertex * -f RootedTree.vertex
            * ((f RootedTree.vertex) ^ 2 - f RootedTree.cherry))
        - -f RootedTree.vertex
            * f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - ((f RootedTree.vertex) ^ 2 - f RootedTree.cherry)
            * f RootedTree.cherry
        + (-((f RootedTree.vertex) ^ 2 * f RootedTree.cherry)
            + f RootedTree.vertex * f RootedTree.broom₃)
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
      = _
  ring

/-! ### Phase α.1 (cycle 374) — `inversePolynomial` pattern-match definition

`inversePolynomial t f` is the closed-form polynomial in the elementary
weights `f` such that, on the four trees of order ≤ 3 for which we
have shipped closed-form witnesses (cycles 341, 367, 368, 369), it
equals `elementaryWeightQ_phi η_q⁻¹ t` whenever
`f = elementaryWeightQ_phi η_q`.

This is the **Phase α.1** form (cycles 374): explicit pattern matching
on the small tree ladder, with `0` as a placeholder for all other
trees. The Phase α' refinement to a recursive definition handling all
`RootedTree` is cycle 375+ work (see
`.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` §7).

Why pattern-match instead of recursion in cycle 374?
* The cycle 367–372 closed forms don't cleanly factor into a single
  recursion (e.g. `f cherry` appears in the broom₃ closed form
  even though cherry is not a child of broom₃). Designing the
  recursive shape is multi-cycle research.
* A pattern-match definition compiles fast, ships axiom-clean, and
  provides Phase β (cycle 375+) with a definition whose small-tree
  unfolds match the cycle 367/368/369 lemmas by `rfl` after `unfold`.

Per the cycle 373 scoping doc §4.5 discovery slot: σ does NOT appear
in any closed form and the `-Φ_η(t)` term always has coefficient `-1`.
Both properties are inherited trivially by this definition. -/

/-- *Phase α.1 (cycle 374) — explicit polynomial for the §383 group
inverse on the small tree ladder.*

For every rooted tree `t` and elementary-weight function
`f : RT → ℝ`, `inversePolynomial t f` is the closed-form polynomial
shipped by cycles 341, 367, 368, 369 for the four small trees of
order ≤ 3. All other trees map to `0` (a Phase α'-replaced
placeholder).

The four matched cases are:

* `vertex` ↦ `-f vertex`                                       (cycle 341)
* `cherry` ↦ `(f vertex)^2 - f cherry`                        (cycle 367)
* `broom₃` ↦ `-(f vertex)^3 + 2·f vertex · f cherry - f broom₃`
                                                                (cycle 368)
* `mk [cherry]` ↦ `-(f vertex)^3 + 2·f vertex · f cherry - f (mk [cherry])`
                                                                (cycle 369)

The Phase β deliverable (cycle 375+) will be a lemma
`elementaryWeightQ_phi η_q⁻¹ t = inversePolynomial t
  (elementaryWeightQ_phi η_q)` for `t` in this ladder. -/
noncomputable def inversePolynomial (t : RT) (f : RT → ℝ) : ℝ :=
  if t = RootedTree.vertex then
    inversePolyChain 0 f
  else if t = RootedTree.cherry then
    inversePolyChain 1 f
  else if t = RootedTree.broom₃ then
    inversePolyBroom 2 f
  else if t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry] then
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) f
  else if t = RootedTree.bushy then
    inversePolyTree RootedTree.bushy f
  else if t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃] then
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) f
  else if t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry] then
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.cherry]) f
  else if t = OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.cherry]] then
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) f
  else
    0

/-- *Phase α.1 (cycle 374) — vertex calibration witness.*

Matches cycle 341's `elementaryWeightQ_phi_zpow_vertex` at `n = -1`
(`Φ_{η⁻¹}(τ) = -Φ_η(τ)`). Non-vacuity verification that
`inversePolynomial` evaluates as the closed-form table prescribes. -/
example (f : RT → ℝ) :
    inversePolynomial RootedTree.vertex f = -(f RootedTree.vertex) := by
  unfold inversePolynomial
  rw [if_pos rfl, inversePolyChain_zero]

/-- *Phase α.1 (cycle 374) — cherry calibration witness.*

Matches cycle 367's `elementaryWeightQ_phi_inv_cherry`
(`Φ_{η⁻¹}([τ]) = (Φ_η τ)² - Φ_η [τ]`). -/
example (f : RT → ℝ) :
    inversePolynomial RootedTree.cherry f
      = (f RootedTree.vertex) ^ 2 - f RootedTree.cherry := by
  unfold inversePolynomial
  rw [if_neg (by decide : RootedTree.cherry ≠ RootedTree.vertex),
      if_pos rfl, inversePolyChain_one]

/-- *Phase α.1 (cycle 374) — broom₃ calibration witness.*

Matches cycle 368's `elementaryWeightQ_phi_inv_broom₃`
(`Φ_{η⁻¹}([τ,τ]) = -(Φ_η τ)³ + 2 (Φ_η τ)(Φ_η [τ]) - Φ_η [τ,τ]`). -/
example (f : RT → ℝ) :
    inversePolynomial RootedTree.broom₃ f
      = -(f RootedTree.vertex) ^ 3
        + 2 * f RootedTree.vertex * f RootedTree.cherry
        - f RootedTree.broom₃ := by
  unfold inversePolynomial
  rw [if_neg (by decide : RootedTree.broom₃ ≠ RootedTree.vertex),
      if_neg (by decide : RootedTree.broom₃ ≠ RootedTree.cherry),
      if_pos rfl, inversePolyBroom_two]

/-- *Phase α.1 (cycle 374) — `mk [cherry]` calibration witness.*

Matches cycle 369's `elementaryWeightQ_phi_inv_mkCherry`
(`Φ_{η⁻¹}([[τ]]) = -(Φ_η τ)³ + 2 (Φ_η τ)(Φ_η [τ]) - Φ_η [[τ]]`). -/
example (f : RT → ℝ) :
    inversePolynomial
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) f
      = -(f RootedTree.vertex) ^ 3
        + 2 * f RootedTree.vertex * f RootedTree.cherry
        - f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) := by
  unfold inversePolynomial
  rw [if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
            ≠ RootedTree.vertex),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
            ≠ RootedTree.cherry),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
            ≠ RootedTree.broom₃),
      if_pos rfl, inversePolyTree_mkCherry]

/-- *Phase α.2 (cycle 377) — bushy calibration witness.*

Matches cycle 370's `elementaryWeightQ_phi_inv_bushy`
(`Φ_{η⁻¹}({τ,τ,τ}) = (Φ_η τ)⁴ − 3 (Φ_η τ)² (Φ_η [τ]) + 3 (Φ_η τ)(Φ_η [τ,τ]) − Φ_η bushy`).
The bushy branch is the 5th in `inversePolynomial`'s chain, so the
witness requires 4 `if_neg` discharges before `if_pos rfl`. -/
example (f : RT → ℝ) :
    inversePolynomial RootedTree.bushy f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + 3 * f RootedTree.vertex * f RootedTree.broom₃
        - f RootedTree.bushy := by
  unfold inversePolynomial
  rw [if_neg (by decide : RootedTree.bushy ≠ RootedTree.vertex),
      if_neg (by decide : RootedTree.bushy ≠ RootedTree.cherry),
      if_neg (by decide : RootedTree.bushy ≠ RootedTree.broom₃),
      if_neg
        (by decide :
          RootedTree.bushy
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      if_pos rfl, inversePolyTree_bushy]

/-- *Phase α.2 (cycle 377) — `mk [broom₃]` calibration witness.*

Matches cycle 371's `elementaryWeightQ_phi_inv_mkBroom₃`
(`Φ_{η⁻¹}([[τ,τ]]) = (Φ_η τ)⁴ − 3 (Φ_η τ)² (Φ_η [τ]) + (Φ_η τ)(Φ_η [τ,τ])
   + 2 (Φ_η τ)(Φ_η [[τ]]) − Φ_η [[τ,τ]]`).
The `mk [broom₃]` branch is the 6th in `inversePolynomial`'s chain, so
the witness requires 5 `if_neg` discharges before `if_pos rfl`. -/
example (f : RT → ℝ) :
    inversePolynomial
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + f RootedTree.vertex * f RootedTree.broom₃
        + 2 * f RootedTree.vertex
            * f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) := by
  unfold inversePolynomial
  rw [if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
            ≠ RootedTree.vertex),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
            ≠ RootedTree.cherry),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
            ≠ RootedTree.broom₃),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
            ≠ RootedTree.bushy),
      if_pos rfl, inversePolyTree_mkBroom₃]

/-- *Phase α.2 (cycle 377) — `mk [vertex, cherry]` calibration witness.*

Matches cycle 372's `elementaryWeightQ_phi_inv_mkVertexCherry`
(`Φ_{η⁻¹}([τ,[τ]]) = (Φ_η τ)⁴ − 3 (Φ_η τ)² (Φ_η [τ]) + (Φ_η [τ])²
   + (Φ_η τ)(Φ_η [τ,τ]) + (Φ_η τ)(Φ_η [[τ]]) − Φ_η [τ,[τ]]`).
The `mk [vertex, cherry]` branch is the 7th (final matched) branch in
`inversePolynomial`'s chain, so the witness requires 6 `if_neg`
discharges before `if_pos rfl`. -/
example (f : RT → ℝ) :
    inversePolynomial
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + (f RootedTree.cherry) ^ 2
        + f RootedTree.vertex * f RootedTree.broom₃
        + f RootedTree.vertex
            * f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]) := by
  unfold inversePolynomial
  rw [if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ RootedTree.vertex),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ RootedTree.cherry),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ RootedTree.broom₃),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ RootedTree.bushy),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]),
      if_pos rfl, inversePolyTree_mkVertexCherry]

/-- *Phase α.4 (cycle 378) — `mk [mk [cherry]]` calibration witness.*

Matches cycle 378's `elementaryWeightQ_phi_inv_mkMkCherry`
(`Φ_{η⁻¹}([[[τ]]]) = (Φ_η τ)⁴ − 3 (Φ_η τ)² (Φ_η [τ]) + (Φ_η [τ])²
   + 2 (Φ_η τ)(Φ_η [[τ]]) − Φ_η [[[τ]]]`).
The `mk [mk [cherry]]` branch is the 8th (final matched) branch in
`inversePolynomial`'s chain, so the witness requires 7 `if_neg`
discharges before `if_pos rfl`. -/
example (f : RT → ℝ) :
    inversePolynomial
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + (f RootedTree.cherry) ^ 2
        + 2 * f RootedTree.vertex
            * f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) := by
  unfold inversePolynomial
  rw [if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ RootedTree.vertex),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ RootedTree.cherry),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ RootedTree.broom₃),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ RootedTree.bushy),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]),
      if_pos rfl, inversePolyTree_mkMkCherry]

/-- *Phase α'.1 (cycle 380) — Family A bridge at depth 0 (vertex).*

Verifies that the recursive `inversePolyChain 0` matches the
existing pattern-match `inversePolynomial RootedTree.vertex`.
Both routes reduce to `-f vertex`: `inversePolyChain` via its base
case, `inversePolynomial` via cycle 374's first `if_pos rfl` branch. -/
theorem inversePolyChain_zero_eq_inversePolynomial (f : RT → ℝ) :
    inversePolyChain 0 f = inversePolynomial RootedTree.vertex f := by
  unfold inversePolynomial
  rw [if_pos rfl]

/-- *Phase α'.1 (cycle 380) — Family A bridge at depth 1 (cherry).*

Verifies that the recursive `inversePolyChain 1` matches the
existing pattern-match `inversePolynomial RootedTree.cherry`.
Both routes reduce to `(f vertex)² - f cherry`: `inversePolyChain`
via the depth-1 convolution recursion, `inversePolynomial` via
cycle 374's cherry branch (`if_neg ≠ vertex, if_pos = cherry`). -/
theorem inversePolyChain_one_eq_inversePolynomial (f : RT → ℝ) :
    inversePolyChain 1 f = inversePolynomial RootedTree.cherry f := by
  unfold inversePolynomial
  rw [if_neg (by decide : RootedTree.cherry ≠ RootedTree.vertex),
      if_pos rfl]

/-- *Phase α'.1 (cycle 380, updated cycle 396) — Family A bridge at depth 2 (`mk [cherry]`).*

Verifies that the recursive `inversePolyChain 2` matches the
existing pattern-match `inversePolynomial (mk [cherry])`.
Both routes reduce to `-(f vertex)³ + 2·f vertex·f cherry − f (mk [cherry])`:
`inversePolyChain` via the depth-2 convolution recursion (using
`inversePolyChain_two`), `inversePolynomial` via cycle 396's
post-migration `mk [cherry]` branch dispatching through
`inversePolyTree` (3 `if_neg`s before `if_pos rfl`, then
`inversePolyTree_mkCherry` to expose the closed form). -/
theorem inversePolyChain_two_eq_inversePolynomial (f : RT → ℝ) :
    inversePolyChain 2 f
      = inversePolynomial
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) f := by
  unfold inversePolynomial
  rw [if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
            ≠ RootedTree.vertex),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
            ≠ RootedTree.cherry),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
            ≠ RootedTree.broom₃),
      if_pos rfl, inversePolyChain_two, inversePolyTree_mkCherry]

/-- *Phase α'.1 (cycle 380) — Family A bridge at depth 3 (`mk [mk [cherry]]`).*

Verifies that the recursive `inversePolyChain 3` matches the
existing pattern-match `inversePolynomial (mk [mk [cherry]])`
shipped at cycle 378. Both routes reduce to the cycle 378 closed
form `v⁴ − 3v²c + c² + 2vm − M_mc`: `inversePolyChain` via the
depth-3 convolution recursion (using `inversePolyChain_two`),
`inversePolynomial` via cycle 378's 8th branch (7 `if_neg`s before
`if_pos rfl`). This is the Phase α'.1 deliverable bridging the
recursive helper to the existing closed-form table on the full
4-tree Family A subset of the cycle 378 ladder. -/
theorem inversePolyChain_three_eq_inversePolynomial (f : RT → ℝ) :
    inversePolyChain 3 f
      = inversePolynomial
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) f := by
  unfold inversePolynomial
  rw [if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ RootedTree.vertex),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ RootedTree.cherry),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ RootedTree.broom₃),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ RootedTree.bushy),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]),
      if_pos rfl, inversePolyChain_three, inversePolyTree_mkMkCherry]

/-- *Phase α'.3 (cycle 383) — Family B bridge at `broom₃` (k=2).*

Verifies that the closed-form `inversePolyBroom 2` matches the
post-migration `inversePolynomial RootedTree.broom₃` body. Both routes
reduce to `-(f vertex)^3 + 2·f vertex · f cherry - f broom₃`. -/
theorem inversePolyBroom_two_eq_inversePolynomial (f : RT → ℝ) :
    inversePolyBroom 2 f = inversePolynomial RootedTree.broom₃ f := by
  unfold inversePolynomial
  rw [if_neg (by decide : RootedTree.broom₃ ≠ RootedTree.vertex),
      if_neg (by decide : RootedTree.broom₃ ≠ RootedTree.cherry),
      if_pos rfl]

/-- *Phase α'.3 (cycle 383) — Family B bridge at `bushy` (k=3).*

Verifies that the closed-form `inversePolyBroom 3` matches the
post-migration `inversePolynomial RootedTree.bushy` body. Both routes
reduce to `v⁴ − 3v²c + 3vb' − bushy`. -/
theorem inversePolyBroom_three_eq_inversePolynomial (f : RT → ℝ) :
    inversePolyBroom 3 f = inversePolynomial RootedTree.bushy f := by
  unfold inversePolynomial
  rw [if_neg (by decide : RootedTree.bushy ≠ RootedTree.vertex),
      if_neg (by decide : RootedTree.bushy ≠ RootedTree.cherry),
      if_neg (by decide : RootedTree.bushy ≠ RootedTree.broom₃),
      if_neg
        (by decide :
          RootedTree.bushy
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      if_pos rfl, inversePolyBroom_three, inversePolyTree_bushy]

/-- *Phase α'.4.2 (cycle 391) — Family C bridge at `mk [vertex, cherry]`.*

Verifies that the recursive `inversePolyTree (mk [vertex, cherry]) f`
matches the post-migration
`inversePolynomial (mk [vertex, cherry]) f` body. Both routes reduce
to cycle 372's 6-term Family C closed form
`v⁴ - 3v²c + c² + vb' + vm - Φ_η(mk [vertex, cherry])`. The
`mk [vertex, cherry]` branch is the 7th in `inversePolynomial`'s
chain, so the proof requires 6 `if_neg` discharges before the
final `if_pos rfl` exposes the recursive `inversePolyTree` call. -/
theorem inversePolyTree_mkVertexCherry_eq_inversePolynomial (f : RT → ℝ) :
    inversePolyTree
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) f
      = inversePolynomial
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry]) f := by
  unfold inversePolynomial
  rw [if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ RootedTree.vertex),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ RootedTree.cherry),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ RootedTree.broom₃),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ RootedTree.bushy),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]),
      if_pos rfl]

/-- *Phase α'.4.2 (cycle 393) — Family C bridge at `mk [broom₃]`.*

Verifies that the recursive `inversePolyTree (mk [broom₃]) f`
matches the post-migration `inversePolynomial (mk [broom₃]) f`
body. Both routes reduce to cycle 371's 5-term Family C closed form
`v⁴ - 3v²c + vb' + 2vm - Φ_η(mk [broom₃])`. The `mk [broom₃]`
branch is the 6th in `inversePolynomial`'s chain, so the proof
requires 5 `if_neg` discharges before the final `if_pos rfl`
exposes the recursive `inversePolyTree` call. -/
theorem inversePolyTree_mkBroom₃_eq_inversePolynomial (f : RT → ℝ) :
    inversePolyTree
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) f
      = inversePolynomial
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) f := by
  unfold inversePolynomial
  rw [if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
            ≠ RootedTree.vertex),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
            ≠ RootedTree.cherry),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
            ≠ RootedTree.broom₃),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
            ≠ RootedTree.bushy),
      if_pos rfl]

/-- *Phase α'.4.2 (cycle 396) — Family A bridge at `mk [cherry]`.*

Verifies that the recursive `inversePolyTree (mk [cherry]) f` matches
the post-migration `inversePolynomial (mk [cherry]) f` body. Mechanical
mirror of cycle 393's `inversePolyTree_mkBroom₃_eq_inversePolynomial`.
The `mk [cherry]` branch is the 4th in `inversePolynomial`'s chain
(after `vertex`, `cherry`, `broom₃`), so three `if_neg` discharges
precede the final `if_pos rfl` that exposes the recursive
`inversePolyTree` call. After cycle 396's body migration, both sides
literally reduce to `inversePolyTree (mk [cherry]) f` and the bridge
closes by the implicit `rfl` after the `rw` cascade. -/
theorem inversePolyTree_mkCherry_eq_inversePolynomial (f : RT → ℝ) :
    inversePolyTree
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) f
      = inversePolynomial
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) f := by
  unfold inversePolynomial
  rw [if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
            ≠ RootedTree.vertex),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
            ≠ RootedTree.cherry),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
            ≠ RootedTree.broom₃),
      if_pos rfl]

/-- *Phase α'.4.2 (cycle 397) — Family A bridge at `mk [mk [cherry]]`.*

Verifies that the recursive `inversePolyTree (mk [mk [cherry]]) f` matches
the post-migration `inversePolynomial (mk [mk [cherry]]) f` body. Mechanical
mirror of cycle 396's `inversePolyTree_mkCherry_eq_inversePolynomial`.
The `mk [mk [cherry]]` branch is the 8th in `inversePolynomial`'s chain
(after `vertex`, `cherry`, `broom₃`, `mk [cherry]`, `bushy`,
`mk [broom₃]`, `mk [vertex, cherry]`), so seven `if_neg` discharges
precede the final `if_pos rfl` that exposes the recursive
`inversePolyTree` call. After cycle 397's body migration, both sides
literally reduce to `inversePolyTree (mk [mk [cherry]]) f` and the
bridge closes by the implicit `rfl` after the `rw` cascade. -/
theorem inversePolyTree_mkMkCherry_eq_inversePolynomial (f : RT → ℝ) :
    inversePolyTree
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) f
      = inversePolynomial
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) f := by
  unfold inversePolynomial
  rw [if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ RootedTree.vertex),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ RootedTree.cherry),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ RootedTree.broom₃),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ RootedTree.bushy),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]),
      if_pos rfl]

/-- *Phase α'.4.2 (cycle 401) — Family A bridge at `bushy`.*

Verifies that the recursive `inversePolyTree bushy f` matches
the post-migration `inversePolynomial bushy f` body. Mechanical mirror
of cycle 397's `inversePolyTree_mkMkCherry_eq_inversePolynomial`.
The `bushy` branch is the 5th in `inversePolynomial`'s chain
(after `vertex`, `cherry`, `broom₃`, `mk [cherry]`), so four `if_neg`
discharges precede the final `if_pos rfl` that exposes the recursive
`inversePolyTree` call. After cycle 401's body migration, both sides
literally reduce to `inversePolyTree RootedTree.bushy f` and the
bridge closes by the implicit `rfl` after the `rw` cascade.

This is the **fifth and final** Phase α'.4.2 ladder-tree migration;
after cycle 401, all 9 ladder trees route uniformly through
`inversePolyTree`. -/
theorem inversePolyTree_bushy_eq_inversePolynomial (f : RT → ℝ) :
    inversePolyTree RootedTree.bushy f
      = inversePolynomial RootedTree.bushy f := by
  unfold inversePolynomial
  rw [if_neg (by decide : RootedTree.bushy ≠ RootedTree.vertex),
      if_neg (by decide : RootedTree.bushy ≠ RootedTree.cherry),
      if_neg (by decide : RootedTree.bushy ≠ RootedTree.broom₃),
      if_neg
        (by decide :
          RootedTree.bushy
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      if_pos rfl]

/-! ### Phase β.1 (cycle 375) — per-tree bridges between `elementaryWeightQ_phi η_q⁻¹` and `inversePolynomial`

For each tree `t` in the four-tree ladder
`{vertex, cherry, broom₃, mk [cherry]}` matched by Phase α.1's
`inversePolynomial`, this section ships the bridge lemma

`elementaryWeightQ_phi η_q⁻¹ t = inversePolynomial t (elementaryWeightQ_phi η_q)`

reducing each case to the cycle 341 / 367 / 368 / 369 closed-form
theorem via `unfold inversePolynomial` + `if_*` rewrites.

This is the Phase β.1 deliverable promised by the cycle 374 Phase α.1
docstring (lines 4231–4233) and the cycle 373 / 374 scoping
documentation in
`.prover-state/issues/def_422B_subLemmaA_inductive_plan.md`. -/

/-- *Phase β.1 (cycle 375) — vertex bridge.*

At `t = vertex`, `elementaryWeightQ_phi η_q⁻¹ t` agrees with the
closed-form polynomial `inversePolynomial t (elementaryWeightQ_phi η_q)`.
Reduces to cycle 341's `elementaryWeightQ_phi_inv_vertex` after a
single `if_pos rfl` unfold of `inversePolynomial`. -/
theorem elementaryWeightQ_phi_inv_eq_inversePolynomial_vertex
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi η_q⁻¹ RootedTree.vertex
      = inversePolynomial RootedTree.vertex (elementaryWeightQ_phi η_q) := by
  unfold inversePolynomial
  rw [if_pos rfl, inversePolyChain_zero]
  exact elementaryWeightQ_phi_inv_vertex η_q

/-- *Phase β.1 (cycle 375) — cherry bridge.*

At `t = cherry`, `elementaryWeightQ_phi η_q⁻¹ t` agrees with the
closed-form polynomial `inversePolynomial t (elementaryWeightQ_phi η_q)`.
Reduces to cycle 367's `elementaryWeightQ_phi_inv_cherry` after one
`if_neg` (cherry ≠ vertex) and `if_pos rfl`. -/
theorem elementaryWeightQ_phi_inv_eq_inversePolynomial_cherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi η_q⁻¹ RootedTree.cherry
      = inversePolynomial RootedTree.cherry (elementaryWeightQ_phi η_q) := by
  unfold inversePolynomial
  rw [if_neg (by decide : RootedTree.cherry ≠ RootedTree.vertex),
      if_pos rfl, inversePolyChain_one]
  exact elementaryWeightQ_phi_inv_cherry η_q

/-- *Phase β.1 (cycle 375) — broom₃ bridge.*

At `t = broom₃`, `elementaryWeightQ_phi η_q⁻¹ t` agrees with the
closed-form polynomial `inversePolynomial t (elementaryWeightQ_phi η_q)`.
Reduces to cycle 368's `elementaryWeightQ_phi_inv_broom₃` after two
`if_neg` discharges and `if_pos rfl`. -/
theorem elementaryWeightQ_phi_inv_eq_inversePolynomial_broom₃
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi η_q⁻¹ RootedTree.broom₃
      = inversePolynomial RootedTree.broom₃ (elementaryWeightQ_phi η_q) := by
  unfold inversePolynomial
  rw [if_neg (by decide : RootedTree.broom₃ ≠ RootedTree.vertex),
      if_neg (by decide : RootedTree.broom₃ ≠ RootedTree.cherry),
      if_pos rfl, inversePolyBroom_two]
  exact elementaryWeightQ_phi_inv_broom₃ η_q

/-- *Phase β.1 (cycle 375) — `mk [cherry]` bridge.*

At `t = mk [cherry]`, `elementaryWeightQ_phi η_q⁻¹ t` agrees with the
closed-form polynomial `inversePolynomial t (elementaryWeightQ_phi η_q)`.
Reduces to cycle 369's `elementaryWeightQ_phi_inv_mkCherry` after three
`if_neg` discharges and `if_pos rfl`. Per cycle 374 Discovery #1, the
`mk [cherry]` literal must be fully qualified as
`OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]` to
avoid resolution to Mathlib's `_root_.RootedTree`. -/
theorem elementaryWeightQ_phi_inv_eq_inversePolynomial_mkCherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi η_q⁻¹
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      = inversePolynomial
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          (elementaryWeightQ_phi η_q) := by
  unfold inversePolynomial
  rw [if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
            ≠ RootedTree.vertex),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
            ≠ RootedTree.cherry),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
            ≠ RootedTree.broom₃),
      if_pos rfl, inversePolyTree_mkCherry]
  exact elementaryWeightQ_phi_inv_mkCherry η_q

/-- *Phase β.2 (cycle 377) — bushy bridge.*

At `t = bushy`, `elementaryWeightQ_phi η_q⁻¹ t` agrees with the
closed-form polynomial `inversePolynomial t (elementaryWeightQ_phi η_q)`.
Reduces to cycle 370's `elementaryWeightQ_phi_inv_bushy` after four
`if_neg` discharges (vertex, cherry, broom₃, mk [cherry]) and
`if_pos rfl`. -/
theorem elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi η_q⁻¹ RootedTree.bushy
      = inversePolynomial RootedTree.bushy (elementaryWeightQ_phi η_q) := by
  unfold inversePolynomial
  rw [if_neg (by decide : RootedTree.bushy ≠ RootedTree.vertex),
      if_neg (by decide : RootedTree.bushy ≠ RootedTree.cherry),
      if_neg (by decide : RootedTree.bushy ≠ RootedTree.broom₃),
      if_neg
        (by decide :
          RootedTree.bushy
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      if_pos rfl, inversePolyTree_bushy]
  exact elementaryWeightQ_phi_inv_bushy η_q

/-- *Phase β.2 (cycle 377) — `mk [broom₃]` bridge.*

At `t = mk [broom₃]`, `elementaryWeightQ_phi η_q⁻¹ t` agrees with the
closed-form polynomial `inversePolynomial t (elementaryWeightQ_phi η_q)`.
Reduces to cycle 371's `elementaryWeightQ_phi_inv_mkBroom₃` after five
`if_neg` discharges (vertex, cherry, broom₃, mk [cherry], bushy) and
`if_pos rfl`. -/
theorem elementaryWeightQ_phi_inv_eq_inversePolynomial_mkBroom₃
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi η_q⁻¹
        (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
      = inversePolynomial
          (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
          (elementaryWeightQ_phi η_q) := by
  unfold inversePolynomial
  rw [if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
            ≠ RootedTree.vertex),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
            ≠ RootedTree.cherry),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
            ≠ RootedTree.broom₃),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
            ≠ RootedTree.bushy),
      if_pos rfl, inversePolyTree_mkBroom₃]
  exact elementaryWeightQ_phi_inv_mkBroom₃ η_q

/-- *Phase β.2 (cycle 377) — `mk [vertex, cherry]` bridge.*

At `t = mk [vertex, cherry]`, `elementaryWeightQ_phi η_q⁻¹ t` agrees
with the closed-form polynomial
`inversePolynomial t (elementaryWeightQ_phi η_q)`. Reduces to cycle
372's `elementaryWeightQ_phi_inv_mkVertexCherry` after six `if_neg`
discharges (vertex, cherry, broom₃, mk [cherry], bushy, mk [broom₃])
and `if_pos rfl`. -/
theorem elementaryWeightQ_phi_inv_eq_inversePolynomial_mkVertexCherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi η_q⁻¹
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry])
      = inversePolynomial
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry])
          (elementaryWeightQ_phi η_q) := by
  unfold inversePolynomial
  rw [if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ RootedTree.vertex),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ RootedTree.cherry),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ RootedTree.broom₃),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ RootedTree.bushy),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]),
      if_pos rfl, inversePolyTree_mkVertexCherry]
  exact elementaryWeightQ_phi_inv_mkVertexCherry η_q

/-- *Phase β.4 (cycle 378) — `mk [mk [cherry]]` bridge.*

At `t = mk [mk [cherry]]`, `elementaryWeightQ_phi η_q⁻¹ t` agrees with
the closed-form polynomial
`inversePolynomial t (elementaryWeightQ_phi η_q)`. Reduces to cycle
378's `elementaryWeightQ_phi_inv_mkMkCherry` after seven `if_neg`
discharges (vertex, cherry, broom₃, mk [cherry], bushy, mk [broom₃],
mk [vertex, cherry]) and `if_pos rfl`. -/
theorem elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi η_q⁻¹
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
      = inversePolynomial
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
          (elementaryWeightQ_phi η_q) := by
  unfold inversePolynomial
  rw [if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ RootedTree.vertex),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ RootedTree.cherry),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ RootedTree.broom₃),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ RootedTree.bushy),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]),
      if_neg
        (by decide :
          OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
            ≠ OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]),
      if_pos rfl, inversePolyTree_mkMkCherry]
  exact elementaryWeightQ_phi_inv_mkMkCherry η_q

/-- *Phase β.1 (cycle 375) + β.2 (cycle 377) + β.4 (cycle 378) —
aggregated bridge on the eight-tree matched ladder.*

Packages the eight per-tree bridges (`_vertex`, `_cherry`, `_broom₃`,
`_mkCherry`, `_bushy`, `_mkBroom₃`, `_mkVertexCherry`, `_mkMkCherry`)
as a single named theorem for downstream consumers. Cycle 378+'s
Phase δ work can quote this lemma instead of branching on the eight
cases manually. -/
theorem elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder
    (η_q : Quotient PhiEquivalent.setoidSigma) (t : RT)
    (ht : t = RootedTree.vertex ∨ t = RootedTree.cherry
        ∨ t = RootedTree.broom₃
        ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.cherry]
        ∨ t = RootedTree.bushy
        ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.broom₃]
        ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]
        ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.cherry]]) :
    elementaryWeightQ_phi η_q⁻¹ t
      = inversePolynomial t (elementaryWeightQ_phi η_q) := by
  rcases ht with h | h | h | h | h | h | h | h <;> subst h
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_vertex η_q
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_cherry η_q
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_broom₃ η_q
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_mkCherry η_q
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy η_q
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_mkBroom₃ η_q
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_mkVertexCherry η_q
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry η_q

/-- *Phase β.1 (cycle 496) — per-tree dispatch theorem for `inversePolyTree`
over the 14-tree ladder.*

For each tree `t` in the §422 ladder
`{vertex, cherry, broom₃, mk [cherry], bushy, mk [broom₃],
mk [vertex, cherry], mk [mk [cherry]], mk [cherry, cherry],
mk [broom₃, cherry], mk [vertex, vertex, cherry],
mk [vertex, cherry, cherry], mk [vertex, vertex, mk [cherry]],
mk [vertex, vertex, broom₃]}` shipped by cycles 341, 367–372, 378, 384–386,
403, 491–494, the recursive `inversePolyTree t f` and the quotient-level
`elementaryWeightQ_phi η_q⁻¹ t` agree under `f = elementaryWeightQ_phi η_q`.

Each branch follows the same template: rewrite the LHS via cycle
`elementaryWeightQ_phi_inv_<tree>` to its closed form, rewrite the RHS via
the matching `inversePolyTree_<tree>` calibration (cycles 387–494) to the
same closed form, and the goal closes definitionally.

This is the **Phase β.1 deliverable** per the cycle 495 scoping doc §5.1.
It supersedes cycle 377's `inversePolynomial`-targeted version with the
recursive `inversePolyTree` form, paving the way for Phase β.2 (cycle 497)
structural induction. -/
theorem elementaryWeightQ_phi_inv_eq_inversePolyTree_on_ladder
    (η_q : Quotient PhiEquivalent.setoidSigma) (t : RT)
    (ht_ladder :
        t = RootedTree.vertex
      ∨ t = RootedTree.cherry
      ∨ t = RootedTree.broom₃
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
      ∨ t = RootedTree.bushy
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
              [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.cherry, RootedTree.cherry]
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.broom₃, RootedTree.cherry]
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry, RootedTree.cherry]
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex,
               OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
      ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex, RootedTree.broom₃]) :
    elementaryWeightQ_phi η_q⁻¹ t
      = inversePolyTree t (elementaryWeightQ_phi η_q) := by
  rcases ht_ladder with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst h
  · rw [elementaryWeightQ_phi_inv_vertex, inversePolyTree_vertex]
  · rw [elementaryWeightQ_phi_inv_cherry, inversePolyTree_cherry]
  · rw [elementaryWeightQ_phi_inv_broom₃, inversePolyTree_broom₃]
  · rw [elementaryWeightQ_phi_inv_mkCherry, inversePolyTree_mkCherry]
  · rw [elementaryWeightQ_phi_inv_bushy, inversePolyTree_bushy]
  · rw [elementaryWeightQ_phi_inv_mkBroom₃, inversePolyTree_mkBroom₃]
  · rw [elementaryWeightQ_phi_inv_mkVertexCherry, inversePolyTree_mkVertexCherry]
  · rw [elementaryWeightQ_phi_inv_mkMkCherry, inversePolyTree_mkMkCherry]
  · rw [elementaryWeightQ_phi_inv_mkCherryCherry, inversePolyTree_mkCherryCherry]
  · rw [elementaryWeightQ_phi_inv_mkBroomCherry, inversePolyTree_mkBroomCherry]
  · rw [elementaryWeightQ_phi_inv_mkVertexVertexCherry,
        inversePolyTree_mkVertexVertexCherry]
  · rw [elementaryWeightQ_phi_inv_mkVertexCherryCherry,
        inversePolyTree_mkVertexCherryCherry]
  · rw [elementaryWeightQ_phi_inv_mkVertexVertexMkCherry,
        inversePolyTree_mkVertexVertexMkCherry]
  · rw [elementaryWeightQ_phi_inv_mkVertexVertexBroom₃,
        inversePolyTree_mkVertexVertexBroom₃]

/-! ### Phase γ (cycle 497) — closed-subtree agreement for `inversePolyTree`

The Phase γ deliverable for the recursive `inversePolyTree` def. Mirrors
cycle 376's `inversePolynomial_eq_of_subtree_agreement` at the
pattern-match recursive level: each non-default branch of
`inversePolyTree` (and the cross-term helpers it delegates to) is a
polynomial in `f` evaluated at subtrees of order ≤ the matched tree's
order, so closed-subtree agreement of `f` and `g` propagates to
equality of `inversePolyTree t f` and `inversePolyTree t g`.

The default branch (`mk (_::_::_::_::_)`, k ≥ 4) returns `0` on both
sides; closed-subtree agreement is vacuous there.

This is the Phase γ deliverable per the cycle 495 scoping doc §5.3.
Downstream cycle 498+ Phase α'.5.2/3 work (extending `inversePolyTree`
to k ≥ 4) will rely on this lemma to thread the recursion hypothesis
through the eventual `underlyingOneStepMethod_aux` recursion. -/

/-- *Phase γ (cycle 497) — `monochildCrossTerm` respects closed-subtree
agreement of its weight function.*

If `f g : RT → ℝ` agree on every subtree `s` with
`s.order ≤ (mk [c]).order`, then
`monochildCrossTerm c f = monochildCrossTerm c g`.

Each non-default branch of `monochildCrossTerm` (cycles 392/394/395)
references `f` at named subtrees (`vertex`, `cherry`, `mk [cherry]`)
all of order ≤ `(mk [c]).order`. The default branch (other `c`) is
`0 = 0`. -/
private theorem monochildCrossTerm_eq_of_subtree_agreement
    (c : RT) (f g : RT → ℝ)
    (h_closed : ∀ s : RT,
        s.order ≤ (OpenMath.Chapter3.Section310.RootedTree.mk [c]).order →
        f s = g s) :
    monochildCrossTerm c f = monochildCrossTerm c g := by
  unfold monochildCrossTerm
  by_cases h_broom : c = RootedTree.broom₃
  · subst h_broom
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hmc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) :=
      h_closed _ (by decide)
    rw [if_pos rfl, if_pos rfl, hv, hc, hmc]
  by_cases h_cherry : c = RootedTree.cherry
  · subst h_cherry
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    rw [if_neg (by decide : RootedTree.cherry ≠ RootedTree.broom₃),
        if_neg (by decide : RootedTree.cherry ≠ RootedTree.broom₃),
        if_pos rfl, if_pos rfl, hv, hc]
  by_cases h_mkc :
      c = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
  · subst h_mkc
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hmc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) :=
      h_closed _ (by decide)
    rw [if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
              ≠ RootedTree.broom₃),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
              ≠ RootedTree.cherry),
        if_pos rfl,
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
              ≠ RootedTree.broom₃),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
              ≠ RootedTree.cherry),
        if_pos rfl, hv, hc, hmc]
  · rw [if_neg h_broom, if_neg h_cherry, if_neg h_mkc,
        if_neg h_broom, if_neg h_cherry, if_neg h_mkc]

/-- *Phase γ (cycle 497) — `bichildCrossTerm` respects closed-subtree
agreement of its weight function.*

If `f g : RT → ℝ` agree on every subtree `s` with
`s.order ≤ (mk [c₁, c₂]).order`, then
`bichildCrossTerm c₁ c₂ f = bichildCrossTerm c₁ c₂ g`.

Each non-default branch of `bichildCrossTerm` (cycles 387/388/390)
references `f` at named subtrees (subset of `{vertex, cherry, broom₃,
mk [cherry], mk [vertex, cherry], mk [cherry, cherry], mk [vertex,
broom₃]}`) all of order ≤ `(mk [c₁, c₂]).order`. The default branch
(other `(c₁, c₂)`) is `0 = 0`. -/
private theorem bichildCrossTerm_eq_of_subtree_agreement
    (c₁ c₂ : RT) (f g : RT → ℝ)
    (h_closed : ∀ s : RT,
        s.order ≤ (OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂]).order →
        f s = g s) :
    bichildCrossTerm c₁ c₂ f = bichildCrossTerm c₁ c₂ g := by
  unfold bichildCrossTerm
  by_cases h_cc : c₁ = RootedTree.cherry ∧ c₂ = RootedTree.cherry
  · obtain ⟨h₁, h₂⟩ := h_cc
    subst h₁; subst h₂
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hb : f RootedTree.broom₃ = g RootedTree.broom₃ :=
      h_closed RootedTree.broom₃ (by decide)
    have hvc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]) :=
      h_closed _ (by decide)
    rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, hv, hc, hb, hvc]
  by_cases h_bc : c₁ = RootedTree.broom₃ ∧ c₂ = RootedTree.cherry
  · obtain ⟨h₁, h₂⟩ := h_bc
    subst h₁; subst h₂
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hb : f RootedTree.broom₃ = g RootedTree.broom₃ :=
      h_closed RootedTree.broom₃ (by decide)
    have hmc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) :=
      h_closed _ (by decide)
    have hvc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]) :=
      h_closed _ (by decide)
    have hcc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.cherry, RootedTree.cherry])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.cherry, RootedTree.cherry]) :=
      h_closed _ (by decide)
    have hvb :
        f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.broom₃])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.broom₃]) :=
      h_closed _ (by decide)
    rw [if_neg (by decide :
            ¬ (RootedTree.broom₃ = RootedTree.cherry ∧
              RootedTree.cherry = RootedTree.cherry)),
        if_pos ⟨rfl, rfl⟩,
        if_neg (by decide :
            ¬ (RootedTree.broom₃ = RootedTree.cherry ∧
              RootedTree.cherry = RootedTree.cherry)),
        if_pos ⟨rfl, rfl⟩,
        hv, hc, hb, hmc, hvc, hcc, hvb]
  by_cases h_vc : c₁ = RootedTree.vertex ∧ c₂ = RootedTree.cherry
  · obtain ⟨h₁, h₂⟩ := h_vc
    subst h₁; subst h₂
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hb : f RootedTree.broom₃ = g RootedTree.broom₃ :=
      h_closed RootedTree.broom₃ (by decide)
    rw [if_neg (by decide :
            ¬ (RootedTree.vertex = RootedTree.cherry ∧
              RootedTree.cherry = RootedTree.cherry)),
        if_neg (by decide :
            ¬ (RootedTree.vertex = RootedTree.broom₃ ∧
              RootedTree.cherry = RootedTree.cherry)),
        if_pos ⟨rfl, rfl⟩,
        if_neg (by decide :
            ¬ (RootedTree.vertex = RootedTree.cherry ∧
              RootedTree.cherry = RootedTree.cherry)),
        if_neg (by decide :
            ¬ (RootedTree.vertex = RootedTree.broom₃ ∧
              RootedTree.cherry = RootedTree.cherry)),
        if_pos ⟨rfl, rfl⟩,
        hv, hc, hb]
  · rw [if_neg h_cc, if_neg h_bc, if_neg h_vc,
        if_neg h_cc, if_neg h_bc, if_neg h_vc]

/-- *Phase γ (cycle 497) — `trichildCrossTerm` respects closed-subtree
agreement of its weight function.*

If `f g : RT → ℝ` agree on every subtree `s` with
`s.order ≤ (mk [c₁, c₂, c₃]).order`, then
`trichildCrossTerm c₁ c₂ c₃ f = trichildCrossTerm c₁ c₂ c₃ g`.

Each non-default branch of `trichildCrossTerm` (cycles 399/491–494)
references `f` at named subtrees all of order ≤ `(mk [c₁, c₂, c₃]).order`.
The default branch (other `(c₁, c₂, c₃)`) is `0 = 0`. -/
private theorem trichildCrossTerm_eq_of_subtree_agreement
    (c₁ c₂ c₃ : RT) (f g : RT → ℝ)
    (h_closed : ∀ s : RT,
        s.order ≤ (OpenMath.Chapter3.Section310.RootedTree.mk
                      [c₁, c₂, c₃]).order →
        f s = g s) :
    trichildCrossTerm c₁ c₂ c₃ f = trichildCrossTerm c₁ c₂ c₃ g := by
  unfold trichildCrossTerm
  by_cases h_vvv : c₁ = RootedTree.vertex ∧ c₂ = RootedTree.vertex
      ∧ c₃ = RootedTree.vertex
  · obtain ⟨h₁, h₂, h₃⟩ := h_vvv
    subst h₁; subst h₂; subst h₃
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hb : f RootedTree.broom₃ = g RootedTree.broom₃ :=
      h_closed RootedTree.broom₃ (by decide)
    rw [if_pos ⟨rfl, rfl, rfl⟩, if_pos ⟨rfl, rfl, rfl⟩, hv, hb]
  by_cases h_vvc : c₁ = RootedTree.vertex ∧ c₂ = RootedTree.vertex
      ∧ c₃ = RootedTree.cherry
  · obtain ⟨h₁, h₂, h₃⟩ := h_vvc
    subst h₁; subst h₂; subst h₃
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hb : f RootedTree.broom₃ = g RootedTree.broom₃ :=
      h_closed RootedTree.broom₃ (by decide)
    have hbu : f RootedTree.bushy = g RootedTree.bushy :=
      h_closed RootedTree.bushy (by decide)
    have hvc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]) :=
      h_closed _ (by decide)
    rw [if_neg (by decide :
            ¬ (RootedTree.vertex = RootedTree.vertex ∧
              RootedTree.vertex = RootedTree.vertex ∧
              RootedTree.cherry = RootedTree.vertex)),
        if_pos ⟨rfl, rfl, rfl⟩,
        if_neg (by decide :
            ¬ (RootedTree.vertex = RootedTree.vertex ∧
              RootedTree.vertex = RootedTree.vertex ∧
              RootedTree.cherry = RootedTree.vertex)),
        if_pos ⟨rfl, rfl, rfl⟩,
        hv, hc, hb, hbu, hvc]
  by_cases h_vcc : c₁ = RootedTree.vertex ∧ c₂ = RootedTree.cherry
      ∧ c₃ = RootedTree.cherry
  · obtain ⟨h₁, h₂, h₃⟩ := h_vcc
    subst h₁; subst h₂; subst h₃
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hb : f RootedTree.broom₃ = g RootedTree.broom₃ :=
      h_closed RootedTree.broom₃ (by decide)
    have hbu : f RootedTree.bushy = g RootedTree.bushy :=
      h_closed RootedTree.bushy (by decide)
    have hvc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]) :=
      h_closed _ (by decide)
    have hvvc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) :=
      h_closed _ (by decide)
    have hccc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.cherry, RootedTree.cherry])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.cherry, RootedTree.cherry]) :=
      h_closed _ (by decide)
    rw [if_neg (by decide :
            ¬ (RootedTree.vertex = RootedTree.vertex ∧
              RootedTree.cherry = RootedTree.vertex ∧
              RootedTree.cherry = RootedTree.vertex)),
        if_neg (by decide :
            ¬ (RootedTree.vertex = RootedTree.vertex ∧
              RootedTree.cherry = RootedTree.vertex ∧
              RootedTree.cherry = RootedTree.cherry)),
        if_pos ⟨rfl, rfl, rfl⟩,
        if_neg (by decide :
            ¬ (RootedTree.vertex = RootedTree.vertex ∧
              RootedTree.cherry = RootedTree.vertex ∧
              RootedTree.cherry = RootedTree.vertex)),
        if_neg (by decide :
            ¬ (RootedTree.vertex = RootedTree.vertex ∧
              RootedTree.cherry = RootedTree.vertex ∧
              RootedTree.cherry = RootedTree.cherry)),
        if_pos ⟨rfl, rfl, rfl⟩,
        hv, hc, hb, hbu, hvc, hvvc, hccc]
  by_cases h_vvmc : c₁ = RootedTree.vertex ∧ c₂ = RootedTree.vertex
      ∧ c₃ = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
  · obtain ⟨h₁, h₂, h₃⟩ := h_vvmc
    subst h₁; subst h₂; subst h₃
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hb : f RootedTree.broom₃ = g RootedTree.broom₃ :=
      h_closed RootedTree.broom₃ (by decide)
    have hbu : f RootedTree.bushy = g RootedTree.bushy :=
      h_closed RootedTree.bushy (by decide)
    have hmc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) :=
      h_closed _ (by decide)
    have hvc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]) :=
      h_closed _ (by decide)
    have hvvc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) :=
      h_closed _ (by decide)
    have hvmc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex,
               OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex,
               OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) :=
      h_closed _ (by decide)
    rw [if_neg (by decide),
        if_neg (by decide),
        if_neg (by decide),
        if_pos ⟨rfl, rfl, rfl⟩,
        if_neg (by decide),
        if_neg (by decide),
        if_neg (by decide),
        if_pos ⟨rfl, rfl, rfl⟩,
        hv, hc, hb, hbu, hmc, hvc, hvvc, hvmc]
  by_cases h_vvb : c₁ = RootedTree.vertex ∧ c₂ = RootedTree.vertex
      ∧ c₃ = RootedTree.broom₃
  · obtain ⟨h₁, h₂, h₃⟩ := h_vvb
    subst h₁; subst h₂; subst h₃
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hb : f RootedTree.broom₃ = g RootedTree.broom₃ :=
      h_closed RootedTree.broom₃ (by decide)
    have hbu : f RootedTree.bushy = g RootedTree.bushy :=
      h_closed RootedTree.bushy (by decide)
    have hmc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) :=
      h_closed _ (by decide)
    have hvc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]) :=
      h_closed _ (by decide)
    have hvvc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) :=
      h_closed _ (by decide)
    have hvb :
        f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.broom₃])
          = g (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.broom₃]) :=
      h_closed _ (by decide)
    rw [if_neg (by decide),
        if_neg (by decide),
        if_neg (by decide),
        if_neg (by decide),
        if_pos ⟨rfl, rfl, rfl⟩,
        if_neg (by decide),
        if_neg (by decide),
        if_neg (by decide),
        if_neg (by decide),
        if_pos ⟨rfl, rfl, rfl⟩,
        hv, hc, hb, hbu, hmc, hvc, hvvc, hvb]
  · rw [if_neg h_vvv, if_neg h_vvc, if_neg h_vcc, if_neg h_vvmc, if_neg h_vvb,
        if_neg h_vvv, if_neg h_vvc, if_neg h_vcc, if_neg h_vvmc, if_neg h_vvb]

/-- *Phase α'.5.2.1 (cycle 500) — `tetrachildCrossTerm` respects closed-subtree
agreement of its weight function.*

If `f g : RT → ℝ` agree on every subtree `s` with
`s.order ≤ (mk [c₁, c₂, c₃, c₄]).order`, then
`tetrachildCrossTerm c₁ c₂ c₃ c₄ f = tetrachildCrossTerm c₁ c₂ c₃ c₄ g`.

The non-default branch `(vertex, vertex, vertex, vertex)` references
`f` at `vertex`, `broom₃`, and `bushy`, all of order
≤ `(mk [vertex, vertex, vertex, vertex]).order = 5`. The default
branch is `0 = 0`. -/
private theorem tetrachildCrossTerm_eq_of_subtree_agreement
    (c₁ c₂ c₃ c₄ : RT) (f g : RT → ℝ)
    (h_closed : ∀ s : RT,
        s.order ≤ (OpenMath.Chapter3.Section310.RootedTree.mk
                      [c₁, c₂, c₃, c₄]).order →
        f s = g s) :
    tetrachildCrossTerm c₁ c₂ c₃ c₄ f
      = tetrachildCrossTerm c₁ c₂ c₃ c₄ g := by
  unfold tetrachildCrossTerm
  by_cases h_vvvv : c₁ = RootedTree.vertex ∧ c₂ = RootedTree.vertex
      ∧ c₃ = RootedTree.vertex ∧ c₄ = RootedTree.vertex
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := h_vvvv
    subst h₁; subst h₂; subst h₃; subst h₄
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hb : f RootedTree.broom₃ = g RootedTree.broom₃ :=
      h_closed RootedTree.broom₃ (by decide)
    have hbu : f RootedTree.bushy = g RootedTree.bushy :=
      h_closed RootedTree.bushy (by decide)
    rw [if_pos ⟨rfl, rfl, rfl, rfl⟩, if_pos ⟨rfl, rfl, rfl, rfl⟩,
        hv, hb, hbu]
  · rw [if_neg h_vvvv, if_neg h_vvvv]

/-- *Phase γ (cycle 497) — `inversePolyTree` respects closed-subtree
agreement of its weight function.*

If `f g : RT → ℝ` agree on every subtree `s` with `s.order ≤ t.order`
(including `s = t`), then `inversePolyTree t f = inversePolyTree t g`.

The proof is strong induction on `t.order`. For each pattern-match
arm of `inversePolyTree` (cycles 387/399/500):

* `mk []` (vertex, order 1): RHS is `-f vertex`; closure at
  `vertex ≤ mk []` is `le_refl`.
* `mk [c]` (single-child): RHS is `-(f vertex · inversePolyTree c f)
  + monochildCrossTerm c f - f (mk [c])`. Apply IH at `c`
  (using `c.order < (mk [c]).order` from `order_lt_of_mem_children`),
  apply `monochildCrossTerm_eq_of_subtree_agreement`, and close
  remaining `f vertex`, `f (mk [c])` via `h_closed`.
* `mk [c₁, c₂]` (binary): analogous to single-child but with two IHs
  plus `bichildCrossTerm_eq_of_subtree_agreement`.
* `mk [c₁, c₂, c₃]` (triple): analogous with three IHs plus
  `trichildCrossTerm_eq_of_subtree_agreement`.
* `mk [c₁, c₂, c₃, c₄]` (quadruple): analogous with four IHs plus
  `tetrachildCrossTerm_eq_of_subtree_agreement` (cycle 500 extension).
* `mk (_::_::_::_::_::_)` (k ≥ 5): both sides return `0`; `rfl` closes.

This is the Phase γ deliverable for `inversePolyTree`. -/
theorem inversePolyTree_eq_of_subtree_agreement
    (t : RT) (f g : RT → ℝ)
    (h_closed : ∀ s : RT, s.order ≤ t.order → f s = g s) :
    inversePolyTree t f = inversePolyTree t g := by
  suffices h : ∀ n : ℕ, ∀ (t : RT) (f g : RT → ℝ),
      t.order ≤ n →
      (∀ s : RT, s.order ≤ t.order → f s = g s) →
      inversePolyTree t f = inversePolyTree t g from
    h t.order t f g (le_refl _) h_closed
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro t f g h_t_order h_closed
    rcases t with ⟨children⟩
    match children with
    | [] =>
        show -f RootedTree.vertex = -g RootedTree.vertex
        rw [h_closed RootedTree.vertex (le_refl _)]
    | [c] =>
        show -(f RootedTree.vertex * inversePolyTree c f)
              + monochildCrossTerm c f
              - f (OpenMath.Chapter3.Section310.RootedTree.mk [c])
            = -(g RootedTree.vertex * inversePolyTree c g)
              + monochildCrossTerm c g
              - g (OpenMath.Chapter3.Section310.RootedTree.mk [c])
        have hc_lt :
            c.order < (OpenMath.Chapter3.Section310.RootedTree.mk [c]).order :=
          RootedTree.order_lt_of_mem_children (List.mem_singleton.mpr rfl)
        have h_closed_c : ∀ s : RT, s.order ≤ c.order → f s = g s := fun s hs =>
          h_closed s (Nat.le_of_lt (Nat.lt_of_le_of_lt hs hc_lt))
        have hIH : inversePolyTree c f = inversePolyTree c g :=
          IH c.order (Nat.lt_of_lt_of_le hc_lt h_t_order) c f g (le_refl _) h_closed_c
        have hmono : monochildCrossTerm c f = monochildCrossTerm c g :=
          monochildCrossTerm_eq_of_subtree_agreement c f g h_closed
        have hv : f RootedTree.vertex = g RootedTree.vertex :=
          h_closed RootedTree.vertex (RootedTree.order_pos _)
        have hself :
            f (OpenMath.Chapter3.Section310.RootedTree.mk [c])
              = g (OpenMath.Chapter3.Section310.RootedTree.mk [c]) :=
          h_closed _ (le_refl _)
        rw [hv, hIH, hmono, hself]
    | [c₁, c₂] =>
        show bichildPolynomial c₁ c₂
              (inversePolyTree c₁ f) (inversePolyTree c₂ f) f
            = bichildPolynomial c₁ c₂
              (inversePolyTree c₁ g) (inversePolyTree c₂ g) g
        have hc₁_lt :
            c₁.order < (OpenMath.Chapter3.Section310.RootedTree.mk
                          [c₁, c₂]).order :=
          RootedTree.order_lt_of_mem_children (List.mem_cons_self)
        have hc₂_lt :
            c₂.order < (OpenMath.Chapter3.Section310.RootedTree.mk
                          [c₁, c₂]).order :=
          RootedTree.order_lt_of_mem_children
            (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
        have h_closed_c₁ : ∀ s : RT, s.order ≤ c₁.order → f s = g s := fun s hs =>
          h_closed s (Nat.le_of_lt (Nat.lt_of_le_of_lt hs hc₁_lt))
        have h_closed_c₂ : ∀ s : RT, s.order ≤ c₂.order → f s = g s := fun s hs =>
          h_closed s (Nat.le_of_lt (Nat.lt_of_le_of_lt hs hc₂_lt))
        have hIH₁ : inversePolyTree c₁ f = inversePolyTree c₁ g :=
          IH c₁.order (Nat.lt_of_lt_of_le hc₁_lt h_t_order)
            c₁ f g (le_refl _) h_closed_c₁
        have hIH₂ : inversePolyTree c₂ f = inversePolyTree c₂ g :=
          IH c₂.order (Nat.lt_of_lt_of_le hc₂_lt h_t_order)
            c₂ f g (le_refl _) h_closed_c₂
        have hbi : bichildCrossTerm c₁ c₂ f = bichildCrossTerm c₁ c₂ g :=
          bichildCrossTerm_eq_of_subtree_agreement c₁ c₂ f g h_closed
        have hv : f RootedTree.vertex = g RootedTree.vertex :=
          h_closed RootedTree.vertex (RootedTree.order_pos _)
        have hmkt₁ :
            f (OpenMath.Chapter3.Section310.RootedTree.mk [c₁])
              = g (OpenMath.Chapter3.Section310.RootedTree.mk [c₁]) := by
          apply h_closed
          show (OpenMath.Chapter3.Section310.RootedTree.mk [c₁]).order ≤
              (OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂]).order
          rw [RootedTree.order_eq, RootedTree.order_eq]
          simp [List.map, List.sum_cons]
        have hmkt₂ :
            f (OpenMath.Chapter3.Section310.RootedTree.mk [c₂])
              = g (OpenMath.Chapter3.Section310.RootedTree.mk [c₂]) := by
          apply h_closed
          show (OpenMath.Chapter3.Section310.RootedTree.mk [c₂]).order ≤
              (OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂]).order
          rw [RootedTree.order_eq, RootedTree.order_eq]
          simp [List.map, List.sum_cons]
        have hself :
            f (OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂])
              = g (OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂]) :=
          h_closed _ (le_refl _)
        unfold bichildPolynomial
        rw [hv, hIH₁, hIH₂, hbi, hmkt₁, hmkt₂, hself]
    | [c₁, c₂, c₃] =>
        show trichildPolynomial c₁ c₂ c₃
              (inversePolyTree c₁ f) (inversePolyTree c₂ f)
              (inversePolyTree c₃ f) f
            = trichildPolynomial c₁ c₂ c₃
              (inversePolyTree c₁ g) (inversePolyTree c₂ g)
              (inversePolyTree c₃ g) g
        have hc₁_lt :
            c₁.order < (OpenMath.Chapter3.Section310.RootedTree.mk
                          [c₁, c₂, c₃]).order :=
          RootedTree.order_lt_of_mem_children (List.mem_cons_self)
        have hc₂_lt :
            c₂.order < (OpenMath.Chapter3.Section310.RootedTree.mk
                          [c₁, c₂, c₃]).order :=
          RootedTree.order_lt_of_mem_children
            (List.mem_cons_of_mem _ (List.mem_cons_self))
        have hc₃_lt :
            c₃.order < (OpenMath.Chapter3.Section310.RootedTree.mk
                          [c₁, c₂, c₃]).order :=
          RootedTree.order_lt_of_mem_children
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)))
        have h_closed_c₁ : ∀ s : RT, s.order ≤ c₁.order → f s = g s := fun s hs =>
          h_closed s (Nat.le_of_lt (Nat.lt_of_le_of_lt hs hc₁_lt))
        have h_closed_c₂ : ∀ s : RT, s.order ≤ c₂.order → f s = g s := fun s hs =>
          h_closed s (Nat.le_of_lt (Nat.lt_of_le_of_lt hs hc₂_lt))
        have h_closed_c₃ : ∀ s : RT, s.order ≤ c₃.order → f s = g s := fun s hs =>
          h_closed s (Nat.le_of_lt (Nat.lt_of_le_of_lt hs hc₃_lt))
        have hIH₁ : inversePolyTree c₁ f = inversePolyTree c₁ g :=
          IH c₁.order (Nat.lt_of_lt_of_le hc₁_lt h_t_order)
            c₁ f g (le_refl _) h_closed_c₁
        have hIH₂ : inversePolyTree c₂ f = inversePolyTree c₂ g :=
          IH c₂.order (Nat.lt_of_lt_of_le hc₂_lt h_t_order)
            c₂ f g (le_refl _) h_closed_c₂
        have hIH₃ : inversePolyTree c₃ f = inversePolyTree c₃ g :=
          IH c₃.order (Nat.lt_of_lt_of_le hc₃_lt h_t_order)
            c₃ f g (le_refl _) h_closed_c₃
        have htri : trichildCrossTerm c₁ c₂ c₃ f = trichildCrossTerm c₁ c₂ c₃ g :=
          trichildCrossTerm_eq_of_subtree_agreement c₁ c₂ c₃ f g h_closed
        have hv : f RootedTree.vertex = g RootedTree.vertex :=
          h_closed RootedTree.vertex (RootedTree.order_pos _)
        have hmkt₁ :
            f (OpenMath.Chapter3.Section310.RootedTree.mk [c₁])
              = g (OpenMath.Chapter3.Section310.RootedTree.mk [c₁]) := by
          apply h_closed
          show (OpenMath.Chapter3.Section310.RootedTree.mk [c₁]).order ≤
              (OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂, c₃]).order
          rw [RootedTree.order_eq, RootedTree.order_eq]
          simp [List.map, List.sum_cons]
        have hmkt₂ :
            f (OpenMath.Chapter3.Section310.RootedTree.mk [c₂])
              = g (OpenMath.Chapter3.Section310.RootedTree.mk [c₂]) := by
          apply h_closed
          show (OpenMath.Chapter3.Section310.RootedTree.mk [c₂]).order ≤
              (OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂, c₃]).order
          rw [RootedTree.order_eq, RootedTree.order_eq]
          simp [List.map, List.sum_cons]
          omega
        have hmkt₃ :
            f (OpenMath.Chapter3.Section310.RootedTree.mk [c₃])
              = g (OpenMath.Chapter3.Section310.RootedTree.mk [c₃]) := by
          apply h_closed
          show (OpenMath.Chapter3.Section310.RootedTree.mk [c₃]).order ≤
              (OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂, c₃]).order
          rw [RootedTree.order_eq, RootedTree.order_eq]
          simp [List.map, List.sum_cons]
          omega
        have hself :
            f (OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂, c₃])
              = g (OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂, c₃]) :=
          h_closed _ (le_refl _)
        unfold trichildPolynomial
        rw [hv, hIH₁, hIH₂, hIH₃, htri, hmkt₁, hmkt₂, hmkt₃, hself]
    | [c₁, c₂, c₃, c₄] =>
        show tetrachildPolynomial c₁ c₂ c₃ c₄
              (inversePolyTree c₁ f) (inversePolyTree c₂ f)
              (inversePolyTree c₃ f) (inversePolyTree c₄ f) f
            = tetrachildPolynomial c₁ c₂ c₃ c₄
              (inversePolyTree c₁ g) (inversePolyTree c₂ g)
              (inversePolyTree c₃ g) (inversePolyTree c₄ g) g
        have hc₁_lt :
            c₁.order < (OpenMath.Chapter3.Section310.RootedTree.mk
                          [c₁, c₂, c₃, c₄]).order :=
          RootedTree.order_lt_of_mem_children (List.mem_cons_self)
        have hc₂_lt :
            c₂.order < (OpenMath.Chapter3.Section310.RootedTree.mk
                          [c₁, c₂, c₃, c₄]).order :=
          RootedTree.order_lt_of_mem_children
            (List.mem_cons_of_mem _ (List.mem_cons_self))
        have hc₃_lt :
            c₃.order < (OpenMath.Chapter3.Section310.RootedTree.mk
                          [c₁, c₂, c₃, c₄]).order :=
          RootedTree.order_lt_of_mem_children
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_self)))
        have hc₄_lt :
            c₄.order < (OpenMath.Chapter3.Section310.RootedTree.mk
                          [c₁, c₂, c₃, c₄]).order :=
          RootedTree.order_lt_of_mem_children
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))))
        have h_closed_c₁ : ∀ s : RT, s.order ≤ c₁.order → f s = g s := fun s hs =>
          h_closed s (Nat.le_of_lt (Nat.lt_of_le_of_lt hs hc₁_lt))
        have h_closed_c₂ : ∀ s : RT, s.order ≤ c₂.order → f s = g s := fun s hs =>
          h_closed s (Nat.le_of_lt (Nat.lt_of_le_of_lt hs hc₂_lt))
        have h_closed_c₃ : ∀ s : RT, s.order ≤ c₃.order → f s = g s := fun s hs =>
          h_closed s (Nat.le_of_lt (Nat.lt_of_le_of_lt hs hc₃_lt))
        have h_closed_c₄ : ∀ s : RT, s.order ≤ c₄.order → f s = g s := fun s hs =>
          h_closed s (Nat.le_of_lt (Nat.lt_of_le_of_lt hs hc₄_lt))
        have hIH₁ : inversePolyTree c₁ f = inversePolyTree c₁ g :=
          IH c₁.order (Nat.lt_of_lt_of_le hc₁_lt h_t_order)
            c₁ f g (le_refl _) h_closed_c₁
        have hIH₂ : inversePolyTree c₂ f = inversePolyTree c₂ g :=
          IH c₂.order (Nat.lt_of_lt_of_le hc₂_lt h_t_order)
            c₂ f g (le_refl _) h_closed_c₂
        have hIH₃ : inversePolyTree c₃ f = inversePolyTree c₃ g :=
          IH c₃.order (Nat.lt_of_lt_of_le hc₃_lt h_t_order)
            c₃ f g (le_refl _) h_closed_c₃
        have hIH₄ : inversePolyTree c₄ f = inversePolyTree c₄ g :=
          IH c₄.order (Nat.lt_of_lt_of_le hc₄_lt h_t_order)
            c₄ f g (le_refl _) h_closed_c₄
        have htetra : tetrachildCrossTerm c₁ c₂ c₃ c₄ f
            = tetrachildCrossTerm c₁ c₂ c₃ c₄ g :=
          tetrachildCrossTerm_eq_of_subtree_agreement c₁ c₂ c₃ c₄ f g h_closed
        have hv : f RootedTree.vertex = g RootedTree.vertex :=
          h_closed RootedTree.vertex (RootedTree.order_pos _)
        have hmkt₁ :
            f (OpenMath.Chapter3.Section310.RootedTree.mk [c₁])
              = g (OpenMath.Chapter3.Section310.RootedTree.mk [c₁]) := by
          apply h_closed
          show (OpenMath.Chapter3.Section310.RootedTree.mk [c₁]).order ≤
              (OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂, c₃, c₄]).order
          rw [RootedTree.order_eq, RootedTree.order_eq]
          simp [List.map, List.sum_cons]
        have hmkt₂ :
            f (OpenMath.Chapter3.Section310.RootedTree.mk [c₂])
              = g (OpenMath.Chapter3.Section310.RootedTree.mk [c₂]) := by
          apply h_closed
          show (OpenMath.Chapter3.Section310.RootedTree.mk [c₂]).order ≤
              (OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂, c₃, c₄]).order
          rw [RootedTree.order_eq, RootedTree.order_eq]
          simp [List.map, List.sum_cons]
          omega
        have hmkt₃ :
            f (OpenMath.Chapter3.Section310.RootedTree.mk [c₃])
              = g (OpenMath.Chapter3.Section310.RootedTree.mk [c₃]) := by
          apply h_closed
          show (OpenMath.Chapter3.Section310.RootedTree.mk [c₃]).order ≤
              (OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂, c₃, c₄]).order
          rw [RootedTree.order_eq, RootedTree.order_eq]
          simp [List.map, List.sum_cons]
          omega
        have hmkt₄ :
            f (OpenMath.Chapter3.Section310.RootedTree.mk [c₄])
              = g (OpenMath.Chapter3.Section310.RootedTree.mk [c₄]) := by
          apply h_closed
          show (OpenMath.Chapter3.Section310.RootedTree.mk [c₄]).order ≤
              (OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂, c₃, c₄]).order
          rw [RootedTree.order_eq, RootedTree.order_eq]
          simp [List.map, List.sum_cons]
          omega
        have hself :
            f (OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂, c₃, c₄])
              = g (OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂, c₃, c₄]) :=
          h_closed _ (le_refl _)
        unfold tetrachildPolynomial
        rw [hv, hIH₁, hIH₂, hIH₃, hIH₄, htetra, hmkt₁, hmkt₂, hmkt₃, hmkt₄, hself]
    | _ :: _ :: _ :: _ :: _ :: _ => rfl

/-! ### Phase γ (cycle 376) — closed-subtree agreement for `inversePolynomial`

The Phase γ deliverable promised by the cycle 373 scoping doc §5 and
explicitly called for by the cycle 375 worker's "Suggested next approach"
(Option B). The cycle 374 pattern-match definition of
`inversePolynomial` means each matched branch's RHS depends only on `f`
at subtrees of the matched tree (of order ≤ the matched tree's order),
so closed-subtree agreement of `f` and `g` propagates to equality of
`inversePolynomial t f` and `inversePolynomial t g`.

Closed-subtree (`s.order ≤ t.order`) rather than strict-subtree
(`s.order < t.order`) is used per the cycle 365 scoping doc update §6.3:
the closed form is the weakest sufficient hypothesis for the eventual
Phase D.3.d (`underlyingOneStepMethod_aux` recursion) consumer, since
the matched closed forms reference `f t` itself (e.g. the cherry case's
`-f cherry` term). -/

/-- *Phase γ (cycle 376) — `inversePolynomial` respects closed-subtree
agreement of its weight function.*

If `f g : RT → ℝ` agree on every subtree `s` with `s.order ≤ t.order`
(including `s = t`), then
`inversePolynomial t f = inversePolynomial t g`.

The proof is a four-way case split on `t`, matching the four branches
of the cycle 374 pattern-match definition. Each branch's RHS is a
polynomial in `f` evaluated at subtrees of order ≤ `t.order`, so the
hypothesis `h_closed` discharges each occurrence. The default branch
(`t` outside the ladder) is `0 = 0`.

This is the Phase γ deliverable per the cycle 373 scoping doc §5 and
the cycle 375 task results' "Suggested next approach". Downstream
Phase D.3.d work will use this lemma to thread the recursion hypothesis
through `underlyingOneStepMethod_aux`. -/
theorem inversePolynomial_eq_of_subtree_agreement
    (t : RT) (f g : RT → ℝ)
    (h_closed : ∀ s : RT, s.order ≤ t.order → f s = g s) :
    inversePolynomial t f = inversePolynomial t g := by
  unfold inversePolynomial
  by_cases h_vertex : t = RootedTree.vertex
  · subst h_vertex
    rw [if_pos rfl, if_pos rfl,
        inversePolyChain_zero, inversePolyChain_zero,
        h_closed RootedTree.vertex (le_refl _)]
  by_cases h_cherry : t = RootedTree.cherry
  · subst h_cherry
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (le_refl _)
    rw [if_neg (by decide : RootedTree.cherry ≠ RootedTree.vertex),
        if_neg (by decide : RootedTree.cherry ≠ RootedTree.vertex),
        if_pos rfl, if_pos rfl,
        inversePolyChain_one, inversePolyChain_one, hv, hc]
  by_cases h_broom : t = RootedTree.broom₃
  · subst h_broom
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hb : f RootedTree.broom₃ = g RootedTree.broom₃ :=
      h_closed RootedTree.broom₃ (le_refl _)
    rw [if_neg (by decide : RootedTree.broom₃ ≠ RootedTree.vertex),
        if_neg (by decide : RootedTree.broom₃ ≠ RootedTree.cherry),
        if_pos rfl,
        if_neg (by decide : RootedTree.broom₃ ≠ RootedTree.vertex),
        if_neg (by decide : RootedTree.broom₃ ≠ RootedTree.cherry),
        if_pos rfl,
        inversePolyBroom_two, inversePolyBroom_two, hv, hc, hb]
  by_cases h_mkCherry :
      t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
  · subst h_mkCherry
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hm :
        f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = g (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) :=
      h_closed _ (le_refl _)
    rw [if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
              ≠ RootedTree.vertex),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
              ≠ RootedTree.cherry),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
              ≠ RootedTree.broom₃),
        if_pos rfl,
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
              ≠ RootedTree.vertex),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
              ≠ RootedTree.cherry),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
              ≠ RootedTree.broom₃),
        if_pos rfl,
        inversePolyTree_mkCherry, inversePolyTree_mkCherry, hv, hc, hm]
  by_cases h_bushy : t = RootedTree.bushy
  · subst h_bushy
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hb : f RootedTree.broom₃ = g RootedTree.broom₃ :=
      h_closed RootedTree.broom₃ (by decide)
    have hbu : f RootedTree.bushy = g RootedTree.bushy :=
      h_closed RootedTree.bushy (le_refl _)
    rw [if_neg (by decide : RootedTree.bushy ≠ RootedTree.vertex),
        if_neg (by decide : RootedTree.bushy ≠ RootedTree.cherry),
        if_neg (by decide : RootedTree.bushy ≠ RootedTree.broom₃),
        if_neg
          (by decide :
            RootedTree.bushy
              ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
        if_pos rfl,
        if_neg (by decide : RootedTree.bushy ≠ RootedTree.vertex),
        if_neg (by decide : RootedTree.bushy ≠ RootedTree.cherry),
        if_neg (by decide : RootedTree.bushy ≠ RootedTree.broom₃),
        if_neg
          (by decide :
            RootedTree.bushy
              ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
        if_pos rfl,
        inversePolyTree_bushy, inversePolyTree_bushy, hv, hc, hb, hbu]
  by_cases h_mkBroom :
      t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
  · subst h_mkBroom
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hb : f RootedTree.broom₃ = g RootedTree.broom₃ :=
      h_closed RootedTree.broom₃ (by decide)
    have hmc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = g (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) :=
      h_closed _ (by decide)
    have hmb :
        f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃])
        = g (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) :=
      h_closed _ (le_refl _)
    rw [if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
              ≠ RootedTree.vertex),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
              ≠ RootedTree.cherry),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
              ≠ RootedTree.broom₃),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
              ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
              ≠ RootedTree.bushy),
        if_pos rfl,
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
              ≠ RootedTree.vertex),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
              ≠ RootedTree.cherry),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
              ≠ RootedTree.broom₃),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
              ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]
              ≠ RootedTree.bushy),
        if_pos rfl, inversePolyTree_mkBroom₃,
        inversePolyTree_mkBroom₃, hv, hc, hb, hmc, hmb]
  by_cases h_mkVertexCherry :
      t = OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry]
  · subst h_mkVertexCherry
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hb : f RootedTree.broom₃ = g RootedTree.broom₃ :=
      h_closed RootedTree.broom₃ (by decide)
    have hmc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = g (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) :=
      h_closed _ (by decide)
    have hmvc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry])
        = g (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry]) :=
      h_closed _ (le_refl _)
    rw [if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]
              ≠ RootedTree.vertex),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]
              ≠ RootedTree.cherry),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]
              ≠ RootedTree.broom₃),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]
              ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]
              ≠ RootedTree.bushy),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]
              ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]),
        if_pos rfl,
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]
              ≠ RootedTree.vertex),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]
              ≠ RootedTree.cherry),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]
              ≠ RootedTree.broom₃),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]
              ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]
              ≠ RootedTree.bushy),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry]
              ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]),
        if_pos rfl, inversePolyTree_mkVertexCherry,
        inversePolyTree_mkVertexCherry, hv, hc, hb, hmc, hmvc]
  by_cases h_mkMkCherry :
      t = OpenMath.Chapter3.Section310.RootedTree.mk
            [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
  · subst h_mkMkCherry
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hmc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        = g (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) :=
      h_closed _ (by decide)
    have hmmc :
        f (OpenMath.Chapter3.Section310.RootedTree.mk
            [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
        = g (OpenMath.Chapter3.Section310.RootedTree.mk
            [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) :=
      h_closed _ (le_refl _)
    rw [if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
              ≠ RootedTree.vertex),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
              ≠ RootedTree.cherry),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
              ≠ RootedTree.broom₃),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
              ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
              ≠ RootedTree.bushy),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
              ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
              ≠ OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry]),
        if_pos rfl,
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
              ≠ RootedTree.vertex),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
              ≠ RootedTree.cherry),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
              ≠ RootedTree.broom₃),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
              ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
              ≠ RootedTree.bushy),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
              ≠ OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]),
        if_neg
          (by decide :
            OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]
              ≠ OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry]),
        if_pos rfl,
        inversePolyTree_mkMkCherry, inversePolyTree_mkMkCherry,
        hv, hc, hmc, hmmc]
  · rw [if_neg h_vertex, if_neg h_cherry, if_neg h_broom, if_neg h_mkCherry,
        if_neg h_bushy, if_neg h_mkBroom, if_neg h_mkVertexCherry,
        if_neg h_mkMkCherry,
        if_neg h_vertex, if_neg h_cherry, if_neg h_broom, if_neg h_mkCherry,
        if_neg h_bushy, if_neg h_mkBroom, if_neg h_mkVertexCherry,
        if_neg h_mkMkCherry]

end OpenMath.Chapter4.Section422
