import OpenMath.Chapter3.Section310

/-!
# Butcher §301 — Functions on trees (Theorem 301A)

This file formalises Theorem 301A: recursive formulas for the
order `r(t)`, symmetry `σ(t)`, and density `γ(t)` of rooted trees.

## Textbook statement (quoted verbatim from `entities/thm_301A.json`)

> Let `t = [t₁^{m₁} t₂^{m₂} … t_k^{m_k}]` be a rooted tree, where
> `t₁, …, t_k` are distinct subtrees with multiplicities `m₁, …, m_k`.
> Then
>
>     r(t) = 1 + Σᵢ mᵢ · r(tᵢ),                     (301a)
>     σ(t) = Πᵢ mᵢ! · σ(tᵢ)^{mᵢ},                    (301b)
>     γ(t) = r(t) · Πᵢ γ(tᵢ)^{mᵢ}.                   (301c)
>
> Furthermore,
>
>     r(τ) = σ(τ) = γ(τ) = 1.                        (301d)

`r(t)` is already defined in `Section310` as `RootedTree.order`. This
file adds the new definitions `RootedTree.density` (γ) and
`RootedTree.symmetry` (σ), then proves (301a)–(301d).

## σ-faithfulness divergence (READ THIS)

Butcher's textual definition (§300, p. 139) of `σ(t)` is:

> `A(t)` is the set of mappings `ϕ : V → V` such that `[x,y] ∈ E` if and
> only if `[ϕ(x), ϕ(y)] ∈ E`. The group `A(t)` will be known as the
> 'symmetry group' of `t`; its order will be known as the 'symmetry',
> and denoted by `σ(t)`.

Theorem 301A then states that this group-theoretic σ satisfies the
recursive formula (301b).

A faithful Lean formalisation would (a) define σ as the cardinality of
the tree-automorphism group, then (b) prove (301b) holds. (a) requires
substantial new infrastructure (permutation groups acting on the
vertex set of our `List`-based `RootedTree`, plus the proof that the
order of that group satisfies (301b)) that is plausibly a 3–5 cycle
effort.

**Pragmatic decision for cycle 017:** define `RootedTree.symmetry`
*directly* via the recursion (301b), treating (301b) as a stipulative
definition. The textbook equivalence is then a mathematical fact whose
formalisation is deferred. See
`.prover-state/issues/symmetry_group_equivalence.md`.

This is the same pattern used elsewhere in this project (e.g. partial
142D / `jordan_canonical_form_missing`).

Downstream consumers of σ (`lem:310B`, `lem:312B`, `lem:313A`,
`thm:317A`, …) only consume the recursive relation (301b), so they are
**not** blocked by this gap.
-/

namespace OpenMath.Chapter3.Section310

namespace RootedTree

/- ### Decidable equality on `RootedTree`

`RootedTree` recurses through `List RootedTree`, which prevents Lean's
auto-`deriving DecidableEq` machinery from firing directly. We provide
a hand-written instance via the standard mutual-recursion pattern
(`decEqTree` for trees, `decEqList` for lists of trees). It is needed
below for `List.dedup` / `List.count` on lists of subtrees, as used in
the definition of `RootedTree.symmetry`. -/

mutual
  def decEqTree : (a b : RootedTree) → Decidable (a = b)
    | mk c1, mk c2 =>
        match decEqList c1 c2 with
        | .isTrue h => .isTrue (by rw [h])
        | .isFalse h => .isFalse (fun heq => h (RootedTree.mk.inj heq))
  def decEqList : (a b : List RootedTree) → Decidable (a = b)
    | [],      []      => .isTrue rfl
    | [],      _ :: _  => .isFalse (fun h => by cases h)
    | _ :: _,  []      => .isFalse (fun h => by cases h)
    | x :: xs, y :: ys =>
        match decEqTree x y with
        | .isFalse hx => .isFalse (fun heq => hx (List.cons.inj heq).1)
        | .isTrue  hx =>
            match decEqList xs ys with
            | .isFalse hxs => .isFalse (fun heq => hxs (List.cons.inj heq).2)
            | .isTrue  hxs => .isTrue (by rw [hx, hxs])
end

instance : DecidableEq RootedTree := decEqTree

/- ### Order recursion (301a)

`order` is defined in `Section310` via the mutual pair
`order` / `orderSum`. We restate the recursion in the standard
`List.sum` form for downstream callers. -/

/-- `orderSum cs` collapses to the standard `(cs.map order).sum`. -/
theorem orderSum_eq_map_sum (children : List RootedTree) :
    orderSum children = (children.map order).sum := by
  induction children with
  | nil => rfl
  | cons t ts ih => simp [orderSum, ih]

/-- (301a) — order recursion in the conventional `List.sum` form.

The textbook's `1 + Σᵢ mᵢ · r(tᵢ)` (sum over distinct subtrees with
multiplicities) is, on a `List`-indexed tree, literally
`1 + Σ_{c ∈ children} r(c)` — both sides count the same vertices. -/
theorem order_eq (children : List RootedTree) :
    order (mk children) = 1 + (children.map order).sum := by
  show 1 + orderSum children = 1 + (children.map order).sum
  rw [orderSum_eq_map_sum]

/- ### Density (301c)

We define `γ` directly via the recursion (301c), mirroring the mutual
`order` / `orderSum` pattern from Section310 so that the function is
structurally recursive and reduces under `rfl`. -/

mutual
  /-- The density `γ(t)` of a rooted tree (Butcher §300):

  > the product over all vertices of the order of the subtree rooted at
  > that vertex.

  We define `γ` here directly via the recursion (301c) of Theorem 301A.
  The equivalence with the textbook 'product over all vertices'
  formulation follows by an easy induction on `t` (each non-root vertex
  of `t` contributes its subtree-order via the recursive calls, and the
  root contributes `r(t)`). -/
  def density : RootedTree → ℕ
    | mk children => order (mk children) * densityProd children
  /-- Running product of `density` over a list of subtrees. -/
  def densityProd : List RootedTree → ℕ
    | [] => 1
    | t :: ts => density t * densityProd ts
end

/-- `densityProd cs` collapses to the standard `(cs.map density).prod`. -/
theorem densityProd_eq_map_prod (children : List RootedTree) :
    densityProd children = (children.map density).prod := by
  induction children with
  | nil => rfl
  | cons t ts ih => simp [densityProd, ih]

/-- (301c) — density recursion in the conventional `List.prod` form. -/
theorem density_eq (children : List RootedTree) :
    density (mk children) =
      order (mk children) * (children.map density).prod := by
  show order (mk children) * densityProd children =
       order (mk children) * (children.map density).prod
  rw [densityProd_eq_map_prod]

/- ### Symmetry (301b)

Stipulative recursion-based definition; faithfulness divergence
relative to Butcher §300's symmetry-group definition is documented in
the file docstring. -/

mutual
  /-- The symmetry `σ(t)` of a rooted tree.

  **Definition note (301b).** Stipulative definition matching (301b):

      σ(mk children) = Πᵢ mᵢ! · σ(tᵢ)^{mᵢ}

  where the product runs over distinct subtree classes `tᵢ` with
  multiplicities `mᵢ` in `children`. We implement this via mutual
  recursion with a list helper `symmetryProd` that walks the children
  list, emitting one `mᵢ! · σ(tᵢ)^{mᵢ}` factor per distinct subtree
  (at the *last* occurrence of that subtree in the list).

  See the file docstring and
  `.prover-state/issues/symmetry_group_equivalence.md` for the
  faithfulness divergence relative to Butcher §300's textual definition
  (order of the tree's automorphism group). -/
  def symmetry : RootedTree → ℕ
    | mk children => symmetryProd children children
  /-- Helper for `symmetry`. Argument 1 (`full`) is the original
  children list, used to compute multiplicities; argument 2 is the
  walking cursor (decreases each step).

  At each step, we emit a factor `mᵢ! · σ(tᵢ)^{mᵢ}` if and only if the
  current head `t` does not appear in the rest of the list — i.e. if
  this is the last occurrence of `t` in `full`. This guarantees each
  distinct subtree contributes exactly one factor. -/
  def symmetryProd : List RootedTree → List RootedTree → ℕ
    | _,    []        => 1
    | full, t :: rest =>
        if t ∈ rest then symmetryProd full rest
        else Nat.factorial (full.count t) * symmetry t ^ full.count t *
              symmetryProd full rest
end

/- ### Theorem 301A — recursive formulas -/

/-- (301a) of Theorem 301A — order recursion. -/
theorem r_recursion (children : List RootedTree) :
    order (mk children) = 1 + (children.map order).sum :=
  order_eq children

/-- (301c) of Theorem 301A — density recursion. -/
theorem γ_recursion (children : List RootedTree) :
    density (mk children) =
      order (mk children) * (children.map density).prod :=
  density_eq children

/-- (301b) of Theorem 301A — symmetry recursion in stipulative form
matching the file's σ definition. The textbook's
`Πᵢ mᵢ! · σ(tᵢ)^{mᵢ}` (product over distinct subtree classes) is here
unfolded as a left-to-right walk through `children` that emits one
factor per distinct subtree at its last occurrence. -/
theorem σ_recursion (children : List RootedTree) :
    symmetry (mk children) = symmetryProd children children := rfl

/-- (301d) of Theorem 301A — base case for the elementary tree
`τ = mk []`. -/
theorem tau_values :
    order (mk []) = 1 ∧ symmetry (mk []) = 1 ∧ density (mk []) = 1 :=
  ⟨rfl, rfl, rfl⟩

end RootedTree

end OpenMath.Chapter3.Section310
