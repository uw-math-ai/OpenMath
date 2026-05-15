import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Butcher §310 — Rooted trees and elementary differentials

This file formalises Definition 310A (the elementary differential) from
Butcher's *Numerical Methods for Ordinary Differential Equations*
(3rd ed., page 172).

## Textbook statement (Definition 310A, quoted)

> Given a tree `t` and a function `f : ℝ^N → ℝ^N`, analytic in a
> neighbourhood of `y`, the 'elementary differential' `F(t)(y)` is
> defined by
>
>     F(τ)(y)              = f(y),
>     F([t₁, t₂, …, t_m])  = f^{(m)}(y) (F(t₁)(y), F(t₂)(y), …, F(t_m)(y)).
>
> Note that the tensor interpretation of the second formula is written as
>
>     F^i([t₁, t₂, …, t_m]) = f^{i}_{j₁,j₂,…,j_m}
>                              · F^{j₁}(t₁) F^{j₂}(t₂) ⋯ F^{j_m}(t_m).

## Design choices

* **Rooted-tree representation.** Butcher uses unordered rooted trees
  (Section 300), so the canonical Lean primitive would be
  `Multiset RootedTree` for the children. However Lean 4's strict-positivity
  check rejects `inductive RootedTree | mk : Multiset RootedTree → RootedTree`
  because `Multiset` is built as a `Quot` of `List`, which is not a
  recognised positive functor. We therefore fall back to
  `inductive RootedTree | mk : List RootedTree → RootedTree`.
  This bakes a child *order* into the data type that is not present in
  Butcher's textbook. Two observations make this faithful for `def:310A`:

  1. The recursive case `F(t) = f^{(m)}(y)(F(t₁), …, F(t_m))` applies the
     `m`-th Fréchet derivative of `f`, which is a **symmetric** continuous
     multilinear map (Schwarz's theorem). Hence permuting the children
     leaves `F(t)(y)` invariant on smooth `f` — the spurious order in the
     `List` representation does not leak into observable behaviour of the
     elementary differential.
  2. A genuine quotient-by-permutation type (`Multiset`-style or
     `Sym`-style) can be built later as a quotient of this `List`
     representation if downstream proofs need to reason about trees as
     unordered objects (e.g. to define `α(t)`, `σ(t)`). It is **not**
     needed for the elementary differential itself.

  We document this divergence with an explicit comment on `RootedTree`
  and the symmetry of `iteratedFDeriv` (cf. `iteratedFDeriv_symm` in
  Mathlib) makes `elementaryDiff` invariant under child permutation
  whenever `f` is sufficiently smooth.

* **Codomain.** Butcher takes `f : ℝ^N → ℝ^N`. We work over an abstract
  real normed space `E` with `f : E → E`, since `iteratedFDeriv` is
  already polymorphic in the underlying space and this avoids an
  intrusive `{N : ℕ}` parameter throughout. Specialising to
  `E := Fin N → ℝ` recovers the textbook signature exactly.

* **Smoothness.** The textbook hypothesises `f` analytic. The Lean
  *definition* is unconditional — `iteratedFDeriv ℝ k f y` is defined for
  arbitrary `f` (returning the zero multilinear map at non-smooth
  points), so the recursive formula `f^{(m)}(y)(F(t₁)(y), …, F(t_m)(y))`
  always type-checks. Theorems about `elementaryDiff` will require
  `ContDiff ℝ k f` for the appropriate `k`; those hypotheses live on
  the theorems, not the definition.
-/

namespace OpenMath.Chapter3.Section310

/-- A rooted tree (Butcher §300, §310): a root vertex together with a
finite list of subtrees attached to it.

The single-vertex tree `τ = •` is `RootedTree.mk []` (no children).
A tree `[t₁, t₂, …, t_m]` with subtrees `t₁, …, t_m` attached to a fresh
root is `RootedTree.mk [t₁, t₂, …, t_m]`.

**Note on order.** Butcher's trees are unordered (rooted trees up to
graph isomorphism, Section 300). We use `List` rather than `Multiset` for
strict-positivity reasons (see file docstring). The order of children
is irrelevant for the elementary differential because
`iteratedFDeriv` produces a symmetric multilinear map. -/
inductive RootedTree : Type
  | mk : List RootedTree → RootedTree

namespace RootedTree

mutual
  /-- The order of a rooted tree: the total number of vertices.

  For the single-vertex tree `mk []` this is `1`. For `mk [t₁, …, t_m]`
  it is `1 + order(t₁) + … + order(t_m)`. This matches Butcher's `r(t)`
  column in Table 300(I).

  We use mutual recursion with `orderSum` (running total over a child
  list) so that `order` is structurally recursive and reduces under
  `rfl` / `decide`. -/
  def order : RootedTree → ℕ
    | mk children => 1 + orderSum children
  /-- Running sum of `order` over a list of subtrees. Helper for `order`'s
  mutual recursion through `List`. -/
  def orderSum : List RootedTree → ℕ
    | [] => 0
    | t :: ts => order t + orderSum ts
end

/-- The single-vertex tree `τ = •` (Butcher §300). -/
def vertex : RootedTree := mk []

/-- The tree `[τ]`: a root with one child leaf. Order 2. -/
def cherry : RootedTree := mk [vertex]

/-- The tree `[τ, τ]`: a root with two child leaves. Order 3. -/
def broom₃ : RootedTree := mk [vertex, vertex]

example : vertex.order = 1 := rfl
example : cherry.order = 2 := rfl
example : broom₃.order = 3 := rfl

/- ### `θ(t)` — exact-solution operator weight

Recursive scaffold for the §312 elementary-weight machinery. By
construction `θ(t) = 1` for every rooted tree; the recursive form
`θ(mk children) = ∏ θ(cᵢ)` matches the tree-product structure of the
exact-solution group `E`.

This is **NOT** the textbook `lem:310B` (Elementary Differential Weight
Formula), which requires a separate `α : RootedTree → ℝ` definition and
a non-trivial sum identity. `theta` is the trivial-weight scaffold that
the future `α(t)`-machinery will compose with. -/

mutual
  /-- The (trivial) exact-solution operator weight `θ(t)`.

  Defined recursively as `θ(τ) = 1` and `θ([t₁, …, t_m]) = ∏ᵢ θ(tᵢ)`.
  See `theta_eq_one` for the closure `∀ t, θ(t) = 1`. -/
  def theta : RootedTree → ℝ
    | mk children => thetaProd children
  /-- Running product of `theta` over a list of subtrees. -/
  def thetaProd : List RootedTree → ℝ
    | [] => 1
    | t :: ts => theta t * thetaProd ts
end

/-- `thetaProd cs` collapses to the standard `(cs.map theta).prod`. -/
theorem thetaProd_eq_map_prod (children : List RootedTree) :
    thetaProd children = (children.map theta).prod := by
  induction children with
  | nil => rfl
  | cons t ts ih => simp [thetaProd, ih]

mutual
  /-- The exact-solution operator weight is identically 1. -/
  theorem theta_eq_one : ∀ t : RootedTree, theta t = 1
    | mk children => by
        show thetaProd children = 1
        exact thetaProd_eq_one children
  /-- The list helper `thetaProd` is identically 1. -/
  theorem thetaProd_eq_one : ∀ ts : List RootedTree, thetaProd ts = 1
    | [] => rfl
    | t :: ts => by
        show theta t * thetaProd ts = 1
        rw [theta_eq_one t, thetaProd_eq_one ts]
        ring
end

example : theta vertex = 1 := theta_eq_one _
example : theta cherry = 1 := theta_eq_one _
example : theta broom₃ = 1 := theta_eq_one _

end RootedTree

/-- Butcher §310, Definition 310A — the **elementary differential**
`F(t)(y)` of a rooted tree `t` with respect to a function `f : E → E`.

Recursive definition (Butcher equations (310g) and (310h)):

* `F(τ)(y) = f(y)` (single-vertex tree),
* `F([t₁, …, t_m])(y) = f^{(m)}(y)(F(t₁)(y), …, F(t_m)(y))`,

where `f^{(m)} = iteratedFDeriv ℝ m f` is the `m`-th total Fréchet
derivative of `f`, interpreted as a continuous multilinear map.

The `Fin children.length` index runs over the children of the root in
the underlying `List` order; symmetry of `iteratedFDeriv` for smooth
`f` makes the value independent of this order. -/
noncomputable def elementaryDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y : E) : RootedTree → E
  | RootedTree.mk children =>
      iteratedFDeriv ℝ children.length f y
        (fun i : Fin children.length => elementaryDiff f y (children.get i))
termination_by t => t
decreasing_by
  simp_wf
  show sizeOf (children.get i) < 1 + sizeOf children
  exact Nat.lt_add_left 1 (List.sizeOf_get children i)

end OpenMath.Chapter3.Section310
