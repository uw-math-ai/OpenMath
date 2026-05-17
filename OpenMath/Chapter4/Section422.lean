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

end OpenMath.Chapter4.Section422
