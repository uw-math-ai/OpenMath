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

end OpenMath.Chapter3.Section383
