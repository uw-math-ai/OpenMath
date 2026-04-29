import OpenMath.Chapter3.Section310
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Butcher §312 — Elementary weights (Definition 312A)

This file formalises Definition 312A from Butcher's *Numerical Methods
for Ordinary Differential Equations* (3rd ed., page 178).

## Textbook statement (Definition 312A, quoted verbatim from `def_312A.json`)

> Let `(c, A, b)` denote the tableau for an `s`-stage Runge–Kutta method.
> Then the 'elementary weights' `Φ(t)`, the 'internal weights' `Φᵢ(t)`,
> and the 'derivative weights' `(Φᵢ D)(t)` for `t ∈ T` and
> `i = 1, 2, …, s` are defined by
>
>     (Φᵢ D)(τ)              = 1,                              (312a)
>     Φᵢ(t)                  = Σⱼ aᵢⱼ (Φⱼ D)(t),               (312b)
>     (Φᵢ D)([t₁ t₂ ⋯ tₖ])   = Πⱼ Φᵢ(tⱼ),                      (312c)
>     Φ(t)                   = Σᵢ bᵢ (Φᵢ D)(t).                (312d)
>
> This definition is used recursively. First `Φᵢ D` is found for `t = τ`,
> using (312a), then `Φᵢ` is evaluated for this single vertex tree, and
> so on.

## Faithfulness note

(312a)–(312d) ARE the textbook definition — Butcher writes "this
definition is used recursively". There is no separate textual
definition that (312a)–(312d) characterise, so there is **no
faithfulness divergence** of the kind that affected
`RootedTree.symmetry` (where σ has a textual group-theoretic definition
that diverges from the recursive formula). The recursion IS the
concept.

## Structural choice

We use the proven cycle-017 mutual-recursion pattern
(`symmetry` / `symmetryProd`, `density` / `densityProd`):

* `derivativeWeight M i t` — recursion on the tree `t`.
* `derivativeWeightProd M i children` — list helper, recursion on the
  list `children`.

Both functions thread the tableau `M` and the stage index `i` unchanged
through the mutual pair. The `Fin s`-indexed sum in `derivativeWeightProd`
varies `j` only inside the recursive call, not in the structural
position. This guarantees structural recursion through `List`.

`internalWeight` and `elementaryWeight` are then non-recursive
abbreviations.
-/

namespace OpenMath.Chapter3.Section312

open OpenMath.Chapter3.Section310

/-- A Runge–Kutta tableau over the reals with `s` stages.

This is Butcher's `(c, A, b)` data, where `A : Matrix (Fin s) (Fin s) ℝ`
is the coefficient matrix, `b : Fin s → ℝ` is the weight vector, and
`c : Fin s → ℝ` is the abscissa vector. All three are independent data;
consistency conditions like `cᵢ = Σⱼ aᵢⱼ` are theorems about specific
tableaux, not part of the data definition. -/
structure RKTableau (s : ℕ) where
  /-- Coefficient matrix `A = (aᵢⱼ)`. -/
  A : Matrix (Fin s) (Fin s) ℝ
  /-- Weight vector `b = (bᵢ)`. -/
  b : Fin s → ℝ
  /-- Abscissa vector `c = (cᵢ)`. -/
  c : Fin s → ℝ

namespace RKTableau

/-- Concrete witness — the explicit (forward) Euler method as a
1-stage Runge–Kutta tableau. -/
def explicitEuler : RKTableau 1 where
  A := 0
  b := fun _ => 1
  c := fun _ => 0

/- ### Derivative weights `(Φᵢ D)(t)` and the list helper

Mutual recursion on the tree structure. The tableau `M` and the stage
index `i` are threaded unchanged; the structural argument is the tree
(or list of trees). The recursive call inside the sum is on `j`, which
is purely a value-level variation — Lean's structural-recursion checker
therefore accepts the pair. -/

mutual
  /-- `(Φᵢ D)(t)` — derivative weight at stage `i` for tree `t`.
  Definitions (312a) and (312c). -/
  noncomputable def derivativeWeight {s : ℕ} (M : RKTableau s) (i : Fin s) :
      RootedTree → ℝ
    | RootedTree.mk children => derivativeWeightProd M i children
  /-- Helper for `derivativeWeight`: the running product of internal
  weights `Φᵢ(tⱼ)` over a list of subtrees, written so that structural
  recursion through `List` is visible to Lean. -/
  noncomputable def derivativeWeightProd {s : ℕ} (M : RKTableau s) (i : Fin s) :
      List RootedTree → ℝ
    | [] => 1
    | t :: ts =>
        (∑ j : Fin s, M.A i j * derivativeWeight M j t) *
          derivativeWeightProd M i ts
end

/-- `Φᵢ(t)` — internal weight at stage `i`. Definition (312b). -/
noncomputable def internalWeight {s : ℕ} (M : RKTableau s)
    (t : RootedTree) (i : Fin s) : ℝ :=
  ∑ j : Fin s, M.A i j * M.derivativeWeight j t

/-- `Φ(t)` — elementary weight. Definition (312d). -/
noncomputable def elementaryWeight {s : ℕ} (M : RKTableau s)
    (t : RootedTree) : ℝ :=
  ∑ i : Fin s, M.b i * M.derivativeWeight i t

/- ### Bridge: list helper collapses to the standard `List.prod` form -/

/-- `derivativeWeightProd M i children` collapses to the standard
`(children.map (Φᵢ ·)).prod` form. The cons case unfolds the helper
and rewrites the leading sum into `internalWeight`. -/
theorem derivativeWeightProd_eq_map_prod {s : ℕ} (M : RKTableau s)
    (i : Fin s) (children : List RootedTree) :
    M.derivativeWeightProd i children =
      (children.map (fun t => M.internalWeight t i)).prod := by
  induction children with
  | nil => rfl
  | cons t ts ih =>
      show (∑ j : Fin s, M.A i j * M.derivativeWeight j t) *
            M.derivativeWeightProd i ts =
          M.internalWeight t i *
            (ts.map (fun t' => M.internalWeight t' i)).prod
      rw [ih]
      rfl

/- ### Theorem 312A — the four defining equations as named API -/

/-- (312a) — `(Φᵢ D)(τ) = 1`. -/
theorem derivativeWeight_vertex {s : ℕ} (M : RKTableau s) (i : Fin s) :
    M.derivativeWeight i RootedTree.vertex = 1 := by
  show M.derivativeWeightProd i [] = 1
  rfl

/-- (312b) — `Φᵢ(t) = Σⱼ aᵢⱼ (Φⱼ D)(t)`. True by definition; named for
downstream API stability. -/
theorem internalWeight_eq {s : ℕ} (M : RKTableau s) (t : RootedTree)
    (i : Fin s) :
    M.internalWeight t i = ∑ j : Fin s, M.A i j * M.derivativeWeight j t :=
  rfl

/-- (312c) — `(Φᵢ D)([t₁ ⋯ tₖ]) = Πⱼ Φᵢ(tⱼ)`. -/
theorem derivativeWeight_mk {s : ℕ} (M : RKTableau s)
    (children : List RootedTree) (i : Fin s) :
    M.derivativeWeight i (RootedTree.mk children) =
      (children.map (fun t => M.internalWeight t i)).prod := by
  show M.derivativeWeightProd i children =
        (children.map (fun t => M.internalWeight t i)).prod
  exact derivativeWeightProd_eq_map_prod M i children

/-- (312d) — `Φ(t) = Σᵢ bᵢ (Φᵢ D)(t)`. True by definition; named for
downstream API stability. -/
theorem elementaryWeight_eq {s : ℕ} (M : RKTableau s) (t : RootedTree) :
    M.elementaryWeight t = ∑ i : Fin s, M.b i * M.derivativeWeight i t :=
  rfl

/- ### Sanity check on the explicit Euler witness

For forward Euler (s = 1, A = 0, b = 1, c = 0), the order-1 condition
is `Φ(τ) = 1` (i.e. `Σᵢ bᵢ = 1`). We check that the elementary weight
of the single-vertex tree evaluates correctly. -/

example : explicitEuler.elementaryWeight RootedTree.vertex = 1 := by
  show ∑ i : Fin 1, explicitEuler.b i * explicitEuler.derivativeWeight i RootedTree.vertex = 1
  simp [explicitEuler, derivativeWeight_vertex]

end RKTableau

end OpenMath.Chapter3.Section312
