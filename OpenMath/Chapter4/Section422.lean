import Mathlib
import OpenMath.Chapter3.Section301
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

end OpenMath.Chapter4.Section422
