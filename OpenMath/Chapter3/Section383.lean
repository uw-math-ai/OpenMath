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

end OpenMath.Chapter3.Section383
