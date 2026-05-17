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

/-! ### Phase D.3.b — linear coefficient extraction (cycle 360)

Per Butcher §422 p. 359 (`extraction/raw_text/ch04.txt:1158`), the
proof of `thm:422A` (Theorem 422A — every preconsistent, stable
linear multistep method admits a member of `G₁` satisfying (422a))
relies on the structural claim:

> The coefficient of η(t) in η⁻ⁱ(t) is equal to i·(-1)^r(t), and
> there are no other terms in η⁻ⁱ(t) with orders greater than r(t)−1.

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

/-- *Phase D.3.b (cycle 360) — named helper:* the linear-coefficient
**residual** in the textbook decomposition of `η⁻ⁱ(t)`. Definitional
on the §383 quotient (per §6.3 quotient-faithfulness discipline):
`linearResidualAt i η_q t = Φ_{η_q^(-i)}(t) - i·(-1)^r(t)·Φ_{η_q}(t)`,
isolating the "other terms" (Butcher's phrase) after extracting the
linear-in-η(t) part.

`noncomputable` because `elementaryWeightQ_phi` is `noncomputable`
(via `Quotient.lift` in `Section381.lean:4759`); does not depend on
representative choice. -/
noncomputable def linearResidualAt (i : ℕ)
    (η_q : Quotient PhiEquivalent.setoidSigma) (t : RT) : ℝ :=
  elementaryWeightQ_phi (η_q ^ (-(i : ℤ))) t
    - (i : ℝ) * (-1)^t.order * elementaryWeightQ_phi η_q t

/-- *Phase D.3.b (cycle 360) Sub-deliverable 1 — signature-pinning
split form for the linear coefficient of η(t) in η⁻ⁱ(t).*
Definitional rearrangement of `linearResidualAt`'s defining
equation. The structural content of the textbook claim
("coefficient of η(t) is i·(-1)^r(t)") is shipped at vertex via
`linearResidualAt_vertex_eq_zero` and at `i = 1` at arbitrary `t`
via `linearResidualAt_one_mk_eq`; the parametricity claim
("`linearResidualAt` depends only on strict subtrees of `t`") is
deferred to cycle 361. -/
theorem coeff_eta_t_in_eta_zpow_neg (i : ℕ)
    (η_q : Quotient PhiEquivalent.setoidSigma) (t : RT) :
    elementaryWeightQ_phi (η_q ^ (-(i : ℤ))) t
      = (i : ℝ) * (-1)^t.order * elementaryWeightQ_phi η_q t
        + linearResidualAt i η_q t := by
  unfold linearResidualAt
  ring

/-- *Phase D.3.b (cycle 360) Sub-deliverable 2 — base case at vertex.*
At the single-vertex tree `τ` (`r(τ) = 1`, no strict subtrees), the
residual is zero. This corroborates Butcher's "there are no other
terms in η⁻ⁱ(t) with orders greater than r(t)−1" specialised to
`r(t) = 1`, where the "other terms" set is empty.

Proof: cycle 341 P3 (`elementaryWeightQ_phi_zpow_vertex`) gives
`Φ_{η_q^n}(τ) = n·Φ_{η_q}(τ)` for all `n : ℤ`. At `n = -(i : ℤ)`,
this yields `Φ_{η_q^(-i)}(τ) = -(i : ℝ)·Φ_{η_q}(τ)`. With
`vertex.order = 1` (by `rfl`, cf. `Section310.lean:125`), the
residual is `-i·Φ - i·(-1)¹·Φ = -i·Φ + i·Φ = 0`. -/
theorem linearResidualAt_vertex_eq_zero (i : ℕ)
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    linearResidualAt i η_q RootedTree.vertex = 0 := by
  unfold linearResidualAt
  rw [elementaryWeightQ_phi_zpow_vertex]
  have h_ord : RootedTree.vertex.order = 1 := rfl
  rw [h_ord]
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
        - (-1)^t.order * M.elementaryWeight t := by
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

/-- *Phase D.3.b (cycle 360) — non-vacuity: split form at
vertex with `explicitEuler`, `i = 1`.* Exercises the
`coeff_eta_t_in_eta_zpow_neg` split form at the vertex with the
canonical `explicitEuler` representative. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (-((1 : ℕ) : ℤ))) RootedTree.vertex
      = ((1 : ℕ) : ℝ) * (-1)^(RootedTree.vertex.order)
          * elementaryWeightQ_phi
              (Quotient.mk PhiEquivalent.setoidSigma
                ⟨1, RKTableau.explicitEuler⟩) RootedTree.vertex
        + linearResidualAt 1
            (Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) RootedTree.vertex :=
  coeff_eta_t_in_eta_zpow_neg 1
    (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
    RootedTree.vertex

/-- *Phase D.3.b (cycle 360) — non-vacuity: closed form at `i = 1`
at `cherry` with `explicitEuler`.* Exercises
`linearResidualAt_one_mk_eq` at the order-2 tree `cherry`,
providing the first non-vertex witness of the closed-form expression
for the residual via cycle 358's `elementaryWeightQ_phi_inv_mk`. -/
example :
    linearResidualAt 1
        (Quotient.mk PhiEquivalent.setoidSigma
          ⟨1, RKTableau.explicitEuler⟩) RootedTree.cherry
      = - (∑ i : Fin 1,
              RKTableau.explicitEuler.b i *
                RKTableau.explicitEuler.derivativeWeightWithSrc
                  RKTableau.explicitEuler.inverse i RootedTree.cherry)
        - (-1)^(RootedTree.cherry.order)
            * RKTableau.explicitEuler.elementaryWeight RootedTree.cherry :=
  linearResidualAt_one_mk_eq RKTableau.explicitEuler RootedTree.cherry

end OpenMath.Chapter4.Section422
