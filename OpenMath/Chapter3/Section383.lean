import OpenMath.Chapter3.Section310
import Mathlib.Data.Multiset.Powerset
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Butcher §383 — The Runge–Kutta group: forests and multiplicative mappings

This file formalises the foundational object of Butcher §383
(*Numerical Methods for Ordinary Differential Equations*, 3rd ed.,
page 287), namely the convolution product on multiplicative mappings
from forests to ℝ, together with **Lemma 383A** — the convolution of
two multiplicative mappings is multiplicative.

## Textbook statement (Lemma 383A, quoted verbatim)

> Let α and β be multiplicative mappings from the forests to the real
> numbers. Then αβ is multiplicative.

with the product defined by equation (383a):

> (αβ)(S) = Σ_{R ⊑ S} α(S \ R) β(R).

## Faithfulness notes

* Butcher's *forest* (page 287) is "a set of vertices V and a set of
  edges E … such that each vertex appears as the second member of at
  most one edge", with components being rooted trees. We encode a
  forest as `Multiset RootedTree`, i.e. an unordered collection of
  rooted trees with multiplicities. This matches Butcher's "extended
  multiplicatively from trees to forests" convention: a function
  `α : Forest → ℝ` extends from trees to forests by taking the
  product of its values on the components, which respects multiset
  addition (forest concatenation) automatically.

* The textbook's sub-forest relation `R ⊑ S` reduces, in this
  encoding, to `R ≤ S` as multisets. The induced "set difference"
  `S \ R` becomes multiset subtraction `S - R`.

* The sum `Σ_{R ⊑ S}` is interpreted as a sum over `S.powerset`. When
  `S` has duplicated trees, `S.powerset` enumerates each sub-multiset
  with the appropriate multiplicity (e.g. `({a,a} : Multiset _).powerset`
  lists `{a}` twice), which matches Butcher's combinatorial intent:
  each "way of selecting a sub-forest" is counted distinctly.

* `IsMultiplicative` includes the empty-forest normalisation
  `α 0 = 1` (the empty product is 1).

## Key technical lemma

The proof of `multiplicative_conv` (Lemma 383A) reduces, after
unfolding multiplicativity of `α` and `β`, to the combinatorial
identity

  `(S + T).powerset = (S.powerset ×ˢ T.powerset).map (fun p => p.1 + p.2)`

which we prove as `_PowersetAdd.powerset_add` below — this lemma is
**not** in Mathlib at the time of writing.
-/

/-- `DecidableEq` for `RootedTree`. The auto-`deriving` handler does not
fire on nested inductives (`RootedTree` contains `List RootedTree`), so we
fall back to `Classical.decEq`. This makes definitions that depend on it
(e.g. `Multiset.sub`) `noncomputable`, which is acceptable here because
we only use `convProduct` for stating and proving propositions. -/
noncomputable instance : DecidableEq OpenMath.Chapter3.Section310.RootedTree :=
  Classical.decEq _

namespace OpenMath.Chapter3.Section383

open OpenMath.Chapter3.Section310

/-! ### Helper: Mathlib gap — `powerset_add` and a sum-product identity -/

namespace _PowersetAdd

open Multiset

variable {α β : Type*}

/-- Auxiliary distribution lemma: `s ×ˢ (t.map f) = (s ×ˢ t).map (fun p => (p.1, f p.2))`. -/
private theorem product_map_right (s : Multiset α) (t : Multiset β) {γ : Type*} (f : β → γ) :
    s ×ˢ (t.map f) = (s ×ˢ t).map (fun p => (p.1, f p.2)) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s IH =>
    rw [Multiset.cons_product, Multiset.cons_product, IH]
    simp [Multiset.map_add, Multiset.map_map]

/-- The powerset of a sum of multisets is the multiset of all
componentwise-summed pairs of sub-multisets. -/
theorem powerset_add (s t : Multiset α) :
    (s + t).powerset = (s.powerset ×ˢ t.powerset).map (fun p => p.1 + p.2) := by
  induction t using Multiset.induction with
  | empty =>
    simp only [Multiset.powerset_zero, add_zero]
    -- Goal: s.powerset = (s.powerset ×ˢ {0}).map (fun p => p.1 + p.2)
    have h_prod : s.powerset ×ˢ ({(0 : Multiset α)} : Multiset _)
        = s.powerset.map (fun a => (a, (0 : Multiset α))) := by
      simp [SProd.sprod, Multiset.product]
    rw [h_prod, Multiset.map_map]
    refine (Multiset.map_id' _).symm.trans ?_
    refine Multiset.map_congr rfl (fun a _ => ?_)
    simp
  | cons b t IH =>
    rw [Multiset.add_cons, Multiset.powerset_cons, IH, Multiset.powerset_cons]
    rw [Multiset.product_add, Multiset.map_add]
    congr 1
    rw [product_map_right]
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun p _ => ?_)
    simp only [Function.comp_apply]
    rw [Multiset.add_cons]

/-- Sum-version of `Multiset.prod_map_product_eq_prod_prod`: for
real-valued maps `f, g`, the product of sums factors as a sum over
the cartesian product of multisets. -/
theorem sum_mul_sum_eq_sum_product (s : Multiset α) (t : Multiset β)
    (f : α → ℝ) (g : β → ℝ) :
    (s.map f).sum * (t.map g).sum
      = ((s ×ˢ t).map (fun p => f p.1 * g p.2)).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s IH =>
    rw [Multiset.map_cons, Multiset.sum_cons, add_mul, IH,
        Multiset.cons_product, Multiset.map_add, Multiset.sum_add,
        Multiset.map_map]
    congr 1
    rw [← Multiset.sum_map_mul_left]
    rfl

end _PowersetAdd

/-! ### Forests and multiplicative mappings -/

/-- A **forest** of rooted trees (Butcher §383): an unordered
collection of rooted trees with multiplicities, encoded as a
`Multiset` over `RootedTree`. The empty forest is `(0 : Forest)`,
and forest concatenation is multiset addition. -/
abbrev Forest : Type := Multiset RootedTree

/-- A function `α : Forest → ℝ` is **multiplicative** (Butcher §383,
page 287, "extended multiplicatively from trees to forests") if it
sends the empty forest to `1` and forest concatenation to the product
of its values on the parts. -/
def IsMultiplicative (α : Forest → ℝ) : Prop :=
  α 0 = 1 ∧ ∀ s t : Forest, α (s + t) = α s * α t

/-- Equation (383a): the **convolution product** of two functions
`α β : Forest → ℝ`. Defined by

  `(αβ)(S) = Σ_{R ≤ S} α(S - R) · β(R)`

where the sum is taken over `S.powerset` (each sub-multiset weighted
by the number of ways it can be extracted from `S`). -/
noncomputable def convProduct (α β : Forest → ℝ) (S : Multiset RootedTree) : ℝ :=
  (S.powerset.map (fun R : Multiset RootedTree => α (S - R) * β R)).sum

/-! ### Lemma 383A — convolution preserves multiplicativity -/

/-- **Butcher §383 Lemma 383A** — the convolution product of two
multiplicative forest mappings is multiplicative.

> Let α and β be multiplicative mappings from the forests to the real
> numbers. Then αβ is multiplicative. -/
theorem multiplicative_conv {α β : Forest → ℝ}
    (hα : IsMultiplicative α) (hβ : IsMultiplicative β) :
    IsMultiplicative (convProduct α β) := by
  refine ⟨?_, ?_⟩
  · -- Empty-forest normalisation: (αβ)(0) = α(0) · β(0) = 1.
    show ((Multiset.powerset (0 : Multiset RootedTree)).map _).sum = 1
    rw [Multiset.powerset_zero]
    simp [hα.1, hβ.1]
  · -- Multiplicativity on (S + T).
    intro S T
    show ((Multiset.powerset (S + T)).map
            (fun R : Multiset RootedTree => α (S + T - R) * β R)).sum
       = ((Multiset.powerset S).map
            (fun R : Multiset RootedTree => α (S - R) * β R)).sum
       * ((Multiset.powerset T).map
            (fun R : Multiset RootedTree => α (T - R) * β R)).sum
    -- Step 1: rewrite (S+T).powerset using powerset_add.
    rw [_PowersetAdd.powerset_add (s := S) (t := T), Multiset.map_map]
    -- Step 2: rewrite each summand using subtraction-on-pairs and
    -- multiplicativity of α and β.
    have hSummand :
        ∀ p ∈ S.powerset ×ˢ T.powerset,
          ((fun R : Multiset RootedTree => α (S + T - R) * β R)
              ∘ fun p : Multiset RootedTree × Multiset RootedTree => p.1 + p.2) p
            = (α (S - p.1) * β p.1) * (α (T - p.2) * β p.2) := by
      intro p hp
      simp only [Multiset.mem_product, Multiset.mem_powerset] at hp
      obtain ⟨h1, h2⟩ := hp
      simp only [Function.comp_apply]
      have hsub : (S + T) - (p.1 + p.2) = (S - p.1) + (T - p.2) := by
        ext x
        simp only [Multiset.count_sub, Multiset.count_add]
        have c1 : Multiset.count x p.1 ≤ Multiset.count x S :=
          Multiset.count_le_of_le _ h1
        have c2 : Multiset.count x p.2 ≤ Multiset.count x T :=
          Multiset.count_le_of_le _ h2
        omega
      rw [hsub, hα.2, hβ.2]
      ring
    rw [show ((S.powerset ×ˢ T.powerset).map
              ((fun R : Multiset RootedTree => α (S + T - R) * β R)
                ∘ fun p : Multiset RootedTree × Multiset RootedTree => p.1 + p.2)).sum
            = ((S.powerset ×ˢ T.powerset).map
              (fun p : Multiset RootedTree × Multiset RootedTree =>
                (α (S - p.1) * β p.1) * (α (T - p.2) * β p.2))).sum
            from congrArg Multiset.sum (Multiset.map_congr rfl hSummand)]
    -- Step 3: split the product over the cartesian product into a
    -- product of sums.
    rw [_PowersetAdd.sum_mul_sum_eq_sum_product]

/-! ### Non-vacuity witness -/

/-- The constant-`1` mapping is multiplicative. This is the trivial
non-vacuity witness for `IsMultiplicative`. -/
theorem isMultiplicative_const_one :
    IsMultiplicative (fun _ : Forest => (1 : ℝ)) :=
  ⟨rfl, fun _ _ => by ring⟩

/-! ### Lemma 383B — convolution is associative -/

/-- Key combinatorial bijection: for fixed `S`, summing first over
`Q ≤ S` and then over `T ≤ S - Q` is the same as summing first over
`R ≤ S` and then over `Q ≤ R` with `T = R - Q`.

This is the multiset analogue of the textbook reindexing
`Σ_{Q ⊑ R ⊑ S} f(R-Q, Q) = Σ_{Q ⊑ S, T ⊑ S-Q} f(T, Q)` via the
bijection `(Q, T) ↔ (Q + T, Q)`. The proof is by induction on `S`,
applying the IH three times to three reparameterised versions of `f`. -/
private theorem double_powerset_swap
    (S : Multiset RootedTree)
    (f : Multiset RootedTree → Multiset RootedTree → ℝ) :
    ((S.powerset).bind
        (fun Q => (S - Q).powerset.map (fun T => f Q T))).sum
      = ((S.powerset).bind
          (fun R => R.powerset.map (fun Q => f Q (R - Q)))).sum := by
  induction S using Multiset.induction generalizing f with
  | empty => simp
  | cons a s IH =>
    -- Setup: cons-cons cancellation in multiset subtraction.
    have hcons_sub : ∀ (m n : Multiset RootedTree), a ::ₘ m - a ::ₘ n = m - n := by
      intros; ext y; simp only [Multiset.count_sub, Multiset.count_cons]; omega
    rw [Multiset.powerset_cons]
    simp only [Multiset.add_bind, Multiset.bind_map, Multiset.sum_add]
    -- We have to prove A + B = C + D, where:
    --   A = Σ Q ≤ s. Σ T ≤ a::s - Q. f Q T
    --   B = Σ Q ≤ s. Σ T ≤ a::s - a::Q. f (a::Q) T
    --   C = Σ R ≤ s. Σ Q ≤ R. f Q (R - Q)        -- = IH RHS for f
    --   D = Σ R ≤ s. Σ Q ≤ a::R. f Q (a::R - Q)
    -- Plan: split A and D into two pieces each:
    --   A = A1 + Z, where A1 = Σ Q ≤ s. Σ T ≤ s - Q. f Q T   (= IH-LHS for f)
    --                  Z  = Σ Q ≤ s. Σ T ≤ s - Q. f Q (a::T)
    --   B = B', where B' = Σ Q ≤ s. Σ T ≤ s - Q. f (a::Q) T  (= IH-LHS for `fun Q T => f (a::Q) T`)
    --   D = W + V, where W = Σ R ≤ s. Σ Q ≤ R. f Q (a::(R - Q))  (= IH-RHS for `fun Q T => f Q (a::T)`)
    --                  V = Σ R ≤ s. Σ Q ≤ R. f (a::Q) (R - Q)    (= IH-RHS for `fun Q T => f (a::Q) T`)
    -- So by IH thrice: A = C + W (matching C in RHS); B = V; D = W + V; total: A + B = C + W + V = C + D.
    -- The first split uses `Multiset.cons_sub_of_le` (Q ≤ s ⇒ a::s - Q = a::(s-Q)) and `Multiset.powerset_cons`.
    -- The second uses `hcons_sub` (a::s - a::Q = s - Q) and `Multiset.powerset_cons` (for D).
    -- Step 1: rewrite A as A1 + Z.
    have hA :
        (s.powerset.bind fun Q => Multiset.map (fun T => f Q T) (a ::ₘ s - Q).powerset).sum
          = (s.powerset.bind fun Q => Multiset.map (fun T => f Q T) (s - Q).powerset).sum
          + (s.powerset.bind fun Q => Multiset.map (fun T => f Q (a ::ₘ T)) (s - Q).powerset).sum := by
      rw [← Multiset.sum_add, ← Multiset.bind_add]
      refine congrArg Multiset.sum (Multiset.bind_congr (fun Q hQ => ?_))
      have hQs : Q ≤ s := Multiset.mem_powerset.mp hQ
      rw [Multiset.cons_sub_of_le _ hQs, Multiset.powerset_cons,
          Multiset.map_add, Multiset.map_map]
      rfl
    -- Step 2: rewrite B in LHS form using hcons_sub.
    have hB :
        (s.powerset.bind fun Q =>
          Multiset.map (fun T => f (a ::ₘ Q) T) (a ::ₘ s - a ::ₘ Q).powerset).sum
          = (s.powerset.bind fun Q =>
              Multiset.map (fun T => f (a ::ₘ Q) T) (s - Q).powerset).sum := by
      refine congrArg Multiset.sum (Multiset.bind_congr (fun Q _ => ?_))
      rw [hcons_sub]
    -- Step 3: rewrite D as W + V (in RHS form).
    have hD :
        (s.powerset.bind fun R =>
          Multiset.map (fun Q => f Q (a ::ₘ R - Q)) (a ::ₘ R).powerset).sum
          = (s.powerset.bind fun R =>
              Multiset.map (fun Q => f Q (a ::ₘ (R - Q))) R.powerset).sum
          + (s.powerset.bind fun R =>
              Multiset.map (fun Q => f (a ::ₘ Q) (R - Q)) R.powerset).sum := by
      rw [← Multiset.sum_add, ← Multiset.bind_add]
      refine congrArg Multiset.sum (Multiset.bind_congr (fun R _ => ?_))
      rw [Multiset.powerset_cons, Multiset.map_add]
      congr 1
      · -- Q ≤ R branch: a ::ₘ R - Q = a ::ₘ (R - Q).
        refine Multiset.map_congr rfl (fun Q hQR => ?_)
        rw [Multiset.cons_sub_of_le _ (Multiset.mem_powerset.mp hQR)]
      · -- Q = a ::ₘ Q' branch: a ::ₘ R - a ::ₘ Q' = R - Q'.
        rw [Multiset.map_map]
        refine Multiset.map_congr rfl (fun Q' _ => ?_)
        simp only [Function.comp_apply]
        rw [hcons_sub]
    -- Step 4: apply IH three times.
    rw [hA, hB, hD]
    rw [IH f, IH (fun Q T => f Q (a ::ₘ T)), IH (fun Q T => f (a ::ₘ Q) T)]
    ring

/-- Expansion of the LHS of associativity as a double sum. -/
private theorem convProduct_assoc_lhs_eq (α β γ : Forest → ℝ) (S : Forest) :
    convProduct (convProduct α β) γ S
      = ((S.powerset).bind
          (fun Q => (S - Q).powerset.map
            (fun T => α (S - Q - T) * β T * γ Q))).sum := by
  unfold convProduct
  rw [Multiset.sum_bind]
  refine congrArg Multiset.sum (Multiset.map_congr rfl (fun Q _ => ?_))
  exact (Multiset.sum_map_mul_right).symm

/-- Expansion of the RHS of associativity as a double sum. -/
private theorem convProduct_assoc_rhs_eq (α β γ : Forest → ℝ) (S : Forest) :
    convProduct α (convProduct β γ) S
      = ((S.powerset).bind
          (fun R => R.powerset.map
            (fun Q => α (S - R) * β (R - Q) * γ Q))).sum := by
  unfold convProduct
  rw [Multiset.sum_bind]
  refine congrArg Multiset.sum (Multiset.map_congr rfl (fun R _ => ?_))
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl (fun Q _ => ?_))
  ring

/-- **Butcher §383 Lemma 383B** — the convolution product on
forest mappings is associative.

> Let α, β and γ be multiplicative mappings from forests to the real
> numbers. Then (αβ)γ = α(βγ).

Faithfulness note: the textbook hypothesises multiplicativity of
α, β, γ, but its proof uses only the algebraic structure of the
convolution sum (not multiplicativity). The Lean statement therefore
drops the hypothesis — a faithful generalisation. -/
theorem convProduct_assoc (α β γ : Forest → ℝ) :
    convProduct (convProduct α β) γ = convProduct α (convProduct β γ) := by
  funext S
  rw [convProduct_assoc_lhs_eq, convProduct_assoc_rhs_eq]
  rw [double_powerset_swap S (fun Q T => α (S - Q - T) * β T * γ Q)]
  refine congrArg Multiset.sum (Multiset.bind_congr (fun R hR => ?_))
  refine Multiset.map_congr rfl (fun Q hQR => ?_)
  have hQR' : Q ≤ R := Multiset.mem_powerset.mp hQR
  have h1 : S - Q - (R - Q) = S - R := by
    rw [← Multiset.sub_add_eq_sub_sub, add_comm, Multiset.sub_add_cancel hQR']
  rw [h1]

/-! ### Lemma 383C — existence of left and right inverses in G₁ -/

/-- The convolution-product identity element on G₁: equals `1` on the
empty forest and `0` elsewhere. This is the multiplicative-mapping
analogue of the unit element in the Runge–Kutta group. -/
noncomputable def convOne : Forest → ℝ :=
  fun F => if F = 0 then 1 else 0

/-- Closed-form inverse for a multiplicative forest mapping `α`:
`convInverse α F = (-1)^|F| · ∏_{t ∈ F} α({t})`.

**Faithfulness note**: Butcher §383 (page 310) constructs the inverse
β by induction on tree order, using the formula
`β(t) := -α(t) - φ(t, α, β)` where `φ` involves α and β at
strictly-smaller trees. In our forest encoding, however, the
sub-multisets of a single-tree forest `{t}` are just `{∅, {t}}`, so
the convolution sum on `{t}` collapses to `α({t}) + β({t})` with no
φ-term. Hence the inductive recurrence reduces to a closed form
`β({t}) := -α({t})`, which extends multiplicatively to a forest by
the displayed product. -/
noncomputable def convInverse (α : Forest → ℝ) : Forest → ℝ :=
  fun F => (-1) ^ (Multiset.card F) *
    (F.map (fun t => α ((t ::ₘ 0 : Multiset RootedTree)))).prod

/-- The constant-`convOne` mapping is multiplicative: `convOne 0 = 1`
and `convOne (s + t) = convOne s · convOne t`. -/
theorem isMultiplicative_convOne : IsMultiplicative convOne := by
  refine ⟨?_, ?_⟩
  · simp [convOne]
  · intro s t
    unfold convOne
    by_cases hs : s = 0
    · by_cases ht : t = 0
      · simp [hs, ht]
      · simp [hs, ht]
    · by_cases ht : t = 0
      · simp [hs, ht]
      · have hst : s + t ≠ 0 := by
          intro h
          apply hs
          have hs_le : s ≤ s + t := Multiset.le_add_right s t
          rw [h] at hs_le
          exact Multiset.le_zero.mp hs_le
        simp [hs, ht, hst]

/-- `convInverse α` is multiplicative for any `α` (multiplicativity of
α is **not** required — the closed form is multiplicative by
construction). -/
theorem convInverse_isMultiplicative (α : Forest → ℝ) :
    IsMultiplicative (convInverse α) := by
  refine ⟨?_, ?_⟩
  · -- convInverse α 0 = 1
    simp [convInverse]
  · -- convInverse α (s + t) = convInverse α s * convInverse α t
    intro s t
    unfold convInverse
    rw [Multiset.card_add, Multiset.map_add, Multiset.prod_add, pow_add]
    ring

/-- Per-singleton zero: `(α · convInverse α)({t}) = 0`. The
convolution sum on `({t} : Forest)` reduces to
`α({t}) + convInverse α ({t}) = α({t}) - α({t}) = 0`. -/
theorem convProduct_singleton_eq_zero
    {α : Forest → ℝ} (hα : IsMultiplicative α) (t : RootedTree) :
    convProduct α (convInverse α) ((t ::ₘ 0 : Multiset RootedTree)) = 0 := by
  unfold convProduct
  rw [Multiset.powerset_cons, Multiset.powerset_zero]
  simp only [Multiset.map_add, Multiset.map_singleton,
             Multiset.sum_add, Multiset.sum_singleton]
  -- Goal: α (t ::ₘ 0 - 0) * convInverse α 0 + α (t ::ₘ 0 - (t ::ₘ 0)) * convInverse α (t ::ₘ 0) = 0
  have hsub : (t ::ₘ 0 : Multiset RootedTree) - (t ::ₘ 0) = 0 := tsub_self _
  rw [hsub, Multiset.sub_zero]
  -- Goal: α (t ::ₘ 0) * convInverse α 0 + α 0 * convInverse α (t ::ₘ 0) = 0
  unfold convInverse
  simp [hα.1, Multiset.card_zero]

/-- Per-singleton zero (symmetric form): `(convInverse α · α)({t}) = 0`. -/
theorem convProduct_singleton_symm_eq_zero
    {α : Forest → ℝ} (hα : IsMultiplicative α) (t : RootedTree) :
    convProduct (convInverse α) α ((t ::ₘ 0 : Multiset RootedTree)) = 0 := by
  unfold convProduct
  rw [Multiset.powerset_cons, Multiset.powerset_zero]
  simp only [Multiset.map_add, Multiset.map_singleton,
             Multiset.sum_add, Multiset.sum_singleton]
  have hsub : (t ::ₘ 0 : Multiset RootedTree) - (t ::ₘ 0) = 0 := tsub_self _
  rw [hsub, Multiset.sub_zero]
  unfold convInverse
  simp [hα.1, Multiset.card_zero]

/-- **Right-inverse property**: `convProduct α (convInverse α) = convOne`. -/
theorem convProduct_convInverse
    {α : Forest → ℝ} (hα : IsMultiplicative α) :
    convProduct α (convInverse α) = convOne := by
  funext F
  unfold convOne
  induction F using Multiset.induction with
  | empty =>
    -- (αβ)(0) = α(0) · β(0) = 1.
    show ((Multiset.powerset (0 : Multiset RootedTree)).map _).sum = (if (0 : Forest) = 0 then 1 else 0)
    rw [Multiset.powerset_zero]
    simp [hα.1, (convInverse_isMultiplicative α).1]
  | cons t rest IH =>
    -- (αβ)(t ::ₘ rest) = (αβ)({t} + rest) = (αβ)({t}) · (αβ)(rest) = 0 · _ = 0.
    have hαβ : IsMultiplicative (convProduct α (convInverse α)) :=
      multiplicative_conv hα (convInverse_isMultiplicative α)
    have hcons : (t ::ₘ rest : Multiset RootedTree) = (t ::ₘ 0) + rest := by
      rfl
    rw [hcons, hαβ.2, convProduct_singleton_eq_zero hα]
    have hne : (t ::ₘ 0 : Multiset RootedTree) + rest ≠ 0 := by
      intro h
      have hmem : t ∈ ((t ::ₘ 0 : Multiset RootedTree) + rest) := by
        rw [Multiset.mem_add]
        left
        exact Multiset.mem_cons_self t 0
      rw [h] at hmem
      exact (Multiset.notMem_zero t) hmem
    simp

/-- **Left-inverse property**: `convProduct (convInverse α) α = convOne`. -/
theorem convProduct_convInverse_symm
    {α : Forest → ℝ} (hα : IsMultiplicative α) :
    convProduct (convInverse α) α = convOne := by
  funext F
  unfold convOne
  induction F using Multiset.induction with
  | empty =>
    show ((Multiset.powerset (0 : Multiset RootedTree)).map _).sum = (if (0 : Forest) = 0 then 1 else 0)
    rw [Multiset.powerset_zero]
    simp [hα.1, (convInverse_isMultiplicative α).1]
  | cons t rest IH =>
    have hβα : IsMultiplicative (convProduct (convInverse α) α) :=
      multiplicative_conv (convInverse_isMultiplicative α) hα
    have hcons : (t ::ₘ rest : Multiset RootedTree) = (t ::ₘ 0) + rest := by
      rfl
    rw [hcons, hβα.2, convProduct_singleton_symm_eq_zero hα]
    have hne : (t ::ₘ 0 : Multiset RootedTree) + rest ≠ 0 := by
      intro h
      have hmem : t ∈ ((t ::ₘ 0 : Multiset RootedTree) + rest) := by
        rw [Multiset.mem_add]
        left
        exact Multiset.mem_cons_self t 0
      rw [h] at hmem
      exact (Multiset.notMem_zero t) hmem
    simp

/-- **Butcher §383 Lemma 383C** — existence of left and right
inverses for any α ∈ G₁.

> Given α ∈ G₁, there exist a left inverse and a right inverse.

We exhibit `convInverse α` (a closed-form construction) as both a
left and right inverse, witnessing the existential constructively.

**Faithfulness caveat**: this is the inverse for *our* `convProduct`,
which uses multiset sub-selection (`R ≤ S` as multisets). Butcher's
own §383 convolution sums over vertex subsets of `V(S)` (allowing
edge-removal partitions), which produces a richer convolution and a
correspondingly richer inverse formula (the partition sum of
Lemma 383D). The inverse-existence claim is true in both algebras;
the *closed-form formula* differs. See
`.prover-state/issues/convolution_vertex_vs_multiset.md` for full
discussion. -/
theorem exists_inverse_of_isMultiplicative
    {α : Forest → ℝ} (hα : IsMultiplicative α) :
    ∃ β : Forest → ℝ, IsMultiplicative β ∧
      convProduct α β = convOne ∧ convProduct β α = convOne :=
  ⟨convInverse α, convInverse_isMultiplicative α,
   convProduct_convInverse hα, convProduct_convInverse_symm hα⟩

end OpenMath.Chapter3.Section383
