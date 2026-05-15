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

/-- Every rooted tree has at least one vertex (the root), so its order
is positive. -/
theorem order_pos : ∀ t : RootedTree, 0 < t.order
  | mk children => by
      show 0 < 1 + orderSum children
      omega

mutual
  /-- `γ(t) > 0` for every rooted tree (every product factor is
  positive: the root order is `≥ 1`, and each subtree's density is
  positive by structural induction). -/
  theorem density_pos : ∀ t : RootedTree, 0 < density t
    | mk children => by
        show 0 < order (mk children) * densityProd children
        exact Nat.mul_pos (order_pos _) (densityProd_pos children)
  /-- List companion to `density_pos`: the running density product is
  positive. -/
  theorem densityProd_pos : ∀ cs : List RootedTree, 0 < densityProd cs
    | [] => by decide
    | t :: ts => by
        show 0 < density t * densityProd ts
        exact Nat.mul_pos (density_pos t) (densityProd_pos ts)
end

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

mutual
  /-- `σ(t) > 0` for every rooted tree. The `symmetryProd` walk emits
  factors of the form `mᵢ! · σ(tᵢ)^{mᵢ}` (each positive by induction +
  `Nat.factorial_pos` + `pow_pos`); the empty-cursor base case is `1`. -/
  theorem symmetry_pos : ∀ t : RootedTree, 0 < symmetry t
    | mk children => by
        show 0 < symmetryProd children children
        exact symmetryProd_pos children children
  /-- List companion to `symmetry_pos`: the running `symmetryProd`
  cursor walk is positive at every cursor state. -/
  theorem symmetryProd_pos :
      ∀ full cursor : List RootedTree, 0 < symmetryProd full cursor
    | _, [] => by show (0 : ℕ) < 1; decide
    | full, t :: rest => by
        unfold symmetryProd
        split_ifs with h
        · exact symmetryProd_pos full rest
        · refine Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) ?_) ?_
          · exact pow_pos (symmetry_pos t) (full.count t)
          · exact symmetryProd_pos full rest
end

/-- (301d) of Theorem 301A — base case for the elementary tree
`τ = mk []`. -/
theorem tau_values :
    order (mk []) = 1 ∧ symmetry (mk []) = 1 ∧ density (mk []) = 1 :=
  ⟨rfl, rfl, rfl⟩

/- ### α(t) — elementary weight (Butcher equation (302a))

We define `α(t)` directly from Butcher's Theorem 302A formula:

    α(t) = r(t)! / (σ(t) · γ(t))                          (302a)

This is the textbook definition of the elementary weight α (Butcher
§302, page 142). Butcher introduces α(t) textually as the number of
distinct labellings of `t` satisfying conditions (i)–(iii) of §302 (each
vertex labelled exactly once; equivalent labellings under symmetry
counted once; labels along every edge increasing root-to-leaf). Theorem
302A then states that this combinatorial α satisfies the closed-form
(302a).

A fully faithful formalisation would (a) define α as a count of label
sets satisfying (i)–(iii), then (b) prove (302a) holds. (a) requires
substantial new infrastructure (vertex labellings on `List`-based trees,
the symmetry group action, the monotone-edge constraint). We adopt the
same pragmatic convention used for `RootedTree.symmetry` (see file
docstring's "σ-faithfulness divergence"): define α via the closed form
(302a) and treat the combinatorial equivalence as an unformalised
mathematical fact (filed alongside the σ-symmetry-group gap).

Downstream consumers (`lem:310B`, `lem:312B`, etc.) only consume the
closed-form value, so they are unaffected by the gap. -/

/-- The elementary weight `α(t)` of a rooted tree (Butcher §302,
equation (302a)):

    α(t) = r(t)! / (σ(t) · γ(t)).

See the section comment above for the faithfulness convention: α is
defined here directly via (302a) rather than as the combinatorial
labelling count of Butcher §302's (i)–(iii). -/
noncomputable def alphaWeight (t : RootedTree) : ℝ :=
  (Nat.factorial (order t) : ℝ) / ((symmetry t : ℝ) * (density t : ℝ))

/-- Base case (Butcher Table 310(II), row r=1): `α(τ) = 1`. Combines
(301d) `r(τ) = σ(τ) = γ(τ) = 1` with the definition (302a)
`α(τ) = 1!/(1·1) = 1`. -/
theorem alphaWeight_vertex : alphaWeight (mk []) = 1 := by
  unfold alphaWeight
  obtain ⟨hr, hs, hd⟩ := tau_values
  rw [hr, hs, hd]
  norm_num

/-- Butcher §302 α(t) is strictly positive: `r(t)! > 0` (factorials
are positive), `σ(t) > 0`, and `γ(t) > 0`, so the quotient
`r(t)!/(σ(t)γ(t))` is positive. -/
theorem alphaWeight_pos (t : RootedTree) : 0 < alphaWeight t := by
  unfold alphaWeight
  apply div_pos
  · exact_mod_cast Nat.factorial_pos t.order
  · apply mul_pos
    · exact_mod_cast symmetry_pos t
    · exact_mod_cast density_pos t

example : alphaWeight vertex = 1 := alphaWeight_vertex

example : alphaWeight cherry = 1 := by
  unfold alphaWeight
  rw [show order cherry = 2 from rfl,
      show symmetry cherry = 1 from rfl,
      show density cherry = 2 from rfl]
  norm_num [Nat.factorial]

example : alphaWeight broom₃ = 1 := by
  unfold alphaWeight
  rw [show order broom₃ = 3 from rfl,
      show symmetry broom₃ = 2 from rfl,
      show density broom₃ = 3 from rfl]
  norm_num [Nat.factorial]

/-- Non-trivial witness: the asymmetric order-4 tree `[τ, [τ]]` (root with
two distinct subtrees: a leaf and a cherry) has `α = 3`. This is
row r=4, second entry of Butcher Table 310(II) (the `f'(f, f'f)` tree).
Order 4, symmetry 1 (no automorphism — leaf and cherry are distinct),
density 4·1·2·1 = 8, so α = 4!/(1·8) = 3. -/
example : alphaWeight (mk [vertex, cherry]) = 3 := by
  unfold alphaWeight
  rw [show order (mk [vertex, cherry]) = 4 from rfl,
      show symmetry (mk [vertex, cherry]) = 1 from rfl,
      show density (mk [vertex, cherry]) = 8 from rfl]
  norm_num [Nat.factorial]

/-- Non-trivial witness: the 3-ladder `mk [cherry]` (root with a cherry
as only child) has `α = 1`. This is row r=3, second entry of Butcher
Table 310(II) — the depth-2 chain `f'(f'f)`. Order 3, symmetry 1
(single-child chain has no automorphism), density 3·2·1 = 6,
so α = 3!/(1·6) = 1. -/
example : alphaWeight (mk [cherry]) = 1 := by
  unfold alphaWeight
  rw [show order (mk [cherry]) = 3 from rfl,
      show symmetry (mk [cherry]) = 1 from rfl,
      show density (mk [cherry]) = 6 from rfl]
  norm_num [Nat.factorial]

/-- Non-trivial witness: the broom-of-4 tree `mk [vertex, vertex, vertex]`
(root with three leaves) has `α = 1`. This is row r=4, fourth entry of
Butcher Table 310(II) — the `f'''(f, f, f)` tree. Order 4, symmetry 3! = 6
(three indistinguishable leaves), density 4·1·1·1 = 4, so
α = 4!/(6·4) = 1. -/
example : alphaWeight (mk [vertex, vertex, vertex]) = 1 := by
  unfold alphaWeight
  rw [show order (mk [vertex, vertex, vertex]) = 4 from rfl,
      show symmetry (mk [vertex, vertex, vertex]) = 6 from rfl,
      show density (mk [vertex, vertex, vertex]) = 4 from rfl]
  norm_num [Nat.factorial]

/-- Non-trivial witness: the lifted broom-3 tree `mk [broom₃]`
(root with `broom₃ = [τ,τ]` as only child) has `α = 1`. This is
row r=4, third entry of Butcher Table 310(II) — the depth-2 tree
`f'(f''(f,f))`. Order 4, symmetry 2 (broom₃'s two leaves remain
indistinguishable when lifted), density 4·3·1·1 = 12, so
α = 4!/(2·12) = 1. -/
example : alphaWeight (mk [broom₃]) = 1 := by
  unfold alphaWeight
  rw [show order (mk [broom₃]) = 4 from rfl,
      show symmetry (mk [broom₃]) = 2 from rfl,
      show density (mk [broom₃]) = 12 from rfl]
  norm_num [Nat.factorial]

/-- Non-trivial witness: the 4-ladder `mk [mk [cherry]]` (chain of
depth 4) has `α = 1`. This is row r=4, first entry of Butcher Table
310(II) — the deeply nested `f'(f'(f'f))`. Order 4, symmetry 1
(single-child chain has no symmetry), density 4·3·2·1 = 24, so
α = 4!/(1·24) = 1. -/
example : alphaWeight (mk [mk [cherry]]) = 1 := by
  unfold alphaWeight
  rw [show order (mk [mk [cherry]]) = 4 from rfl,
      show symmetry (mk [mk [cherry]]) = 1 from rfl,
      show density (mk [mk [cherry]]) = 24 from rfl]
  norm_num [Nat.factorial]

/- ### Butcher Table 310(II) row r=5 — α-witnesses for all 9 unordered
rooted trees of order 5. Each `example` exercises the (302a) definition
of α on a specific tree, computing the (order, σ, γ) triple by `rfl` on
the recursive definitions of `RootedTree.order`, `RootedTree.symmetry`,
and `RootedTree.density`, then closing the resulting numerical equality
by `norm_num`. Together with the r ≤ 4 witnesses above, this saturates
Butcher's small-tree data table through r = 5. -/

/-- Non-trivial witness: the 5-ladder `mk [mk [mk [cherry]]]`
(chain of depth 5) has `α = 1`. Row r=5 of Butcher Table 310(II) —
the deeply nested `f'(f'(f'(f'f)))`. Order 5, symmetry 1 (single-child
chain has no automorphism), density 5·4·3·2·1 = 120, so
α = 5!/(1·120) = 1. -/
example : alphaWeight (mk [mk [mk [cherry]]]) = 1 := by
  unfold alphaWeight
  rw [show order (mk [mk [mk [cherry]]]) = 5 from rfl,
      show symmetry (mk [mk [mk [cherry]]]) = 1 from rfl,
      show density (mk [mk [mk [cherry]]]) = 120 from rfl]
  norm_num [Nat.factorial]

/-- Non-trivial witness: the broom-of-5 tree
`mk [vertex, vertex, vertex, vertex]` (root with four leaves) has
`α = 1`. Row r=5 of Butcher Table 310(II) — the `f''''(f, f, f, f)`
tree. Order 5, symmetry 4! = 24 (four indistinguishable leaves),
density 5·1·1·1·1 = 5, so α = 5!/(24·5) = 1. -/
example : alphaWeight (mk [vertex, vertex, vertex, vertex]) = 1 := by
  unfold alphaWeight
  rw [show order (mk [vertex, vertex, vertex, vertex]) = 5 from rfl,
      show symmetry (mk [vertex, vertex, vertex, vertex]) = 24 from rfl,
      show density (mk [vertex, vertex, vertex, vertex]) = 5 from rfl]
  norm_num [Nat.factorial]

/-- Non-trivial witness: two cherries `mk [cherry, cherry]` has
`α = 3`. Row r=5 of Butcher Table 310(II) — the `f''(f'f, f'f)` tree.
Order 5, symmetry 2 (two indistinguishable cherries → 2! · σ(cherry)²
= 2 · 1 = 2), density 5·2·2 = 20, so α = 5!/(2·20) = 3. -/
example : alphaWeight (mk [cherry, cherry]) = 3 := by
  unfold alphaWeight
  rw [show order (mk [cherry, cherry]) = 5 from rfl,
      show symmetry (mk [cherry, cherry]) = 2 from rfl,
      show density (mk [cherry, cherry]) = 20 from rfl]
  norm_num [Nat.factorial]

/-- Non-trivial witness: a cherry plus two leaves
`mk [cherry, vertex, vertex]` has `α = 6`. Row r=5 of Butcher Table
310(II) — the `f'''(f, f, f'f)` tree. Order 5, symmetry 2 (cherry
distinct from leaves: 1!·σ(cherry)¹=1; two indistinguishable leaves:
2!·σ(τ)²=2), density 5·2·1·1 = 10, so α = 5!/(2·10) = 6. -/
example : alphaWeight (mk [cherry, vertex, vertex]) = 6 := by
  unfold alphaWeight
  rw [show order (mk [cherry, vertex, vertex]) = 5 from rfl,
      show symmetry (mk [cherry, vertex, vertex]) = 2 from rfl,
      show density (mk [cherry, vertex, vertex]) = 10 from rfl]
  norm_num [Nat.factorial]

/-- Non-trivial witness: the lifted broom-of-4 tree
`mk [mk [vertex, vertex, vertex]]` (root with `mk [v,v,v]` as only
child) has `α = 1`. Row r=5 of Butcher Table 310(II) — the depth-2
tree `f'(f'''(f, f, f))`. Order 5, symmetry 6 (single child inherits
σ(mk [v,v,v]) = 3! = 6), density 5·4 = 20, so α = 5!/(6·20) = 1. -/
example : alphaWeight (mk [mk [vertex, vertex, vertex]]) = 1 := by
  unfold alphaWeight
  rw [show order (mk [mk [vertex, vertex, vertex]]) = 5 from rfl,
      show symmetry (mk [mk [vertex, vertex, vertex]]) = 6 from rfl,
      show density (mk [mk [vertex, vertex, vertex]]) = 20 from rfl]
  norm_num [Nat.factorial]

/-- Non-trivial witness: the lifted "lifted broom-3" tree
`mk [mk [broom₃]]` has `α = 1`. Row r=5 of Butcher Table 310(II) —
the depth-3 tree `f'(f'(f''(f, f)))`. Order 5, symmetry 2 (single
child inherits σ(mk [broom₃]) = 2), density 5·12 = 60, so
α = 5!/(2·60) = 1. -/
example : alphaWeight (mk [mk [broom₃]]) = 1 := by
  unfold alphaWeight
  rw [show order (mk [mk [broom₃]]) = 5 from rfl,
      show symmetry (mk [mk [broom₃]]) = 2 from rfl,
      show density (mk [mk [broom₃]]) = 60 from rfl]
  norm_num [Nat.factorial]

/-- Non-trivial witness: the lifted asymmetric order-4 tree
`mk [mk [vertex, cherry]]` has `α = 3`. Row r=5 of Butcher Table
310(II) — the depth-3 tree `f'(f'(f, f'f))`. Order 5, symmetry 1
(single child inherits σ(mk [vertex, cherry]) = 1), density 5·8 = 40,
so α = 5!/(1·40) = 3. -/
example : alphaWeight (mk [mk [vertex, cherry]]) = 3 := by
  unfold alphaWeight
  rw [show order (mk [mk [vertex, cherry]]) = 5 from rfl,
      show symmetry (mk [mk [vertex, cherry]]) = 1 from rfl,
      show density (mk [mk [vertex, cherry]]) = 40 from rfl]
  norm_num [Nat.factorial]

/-- Non-trivial witness: broom-3 plus a leaf
`mk [broom₃, vertex]` has `α = 4`. Row r=5 of Butcher Table 310(II) —
the tree `f''(f''(f, f), f)`. Order 5, symmetry 2 (broom₃ distinct
from vertex; 1!·σ(broom₃)¹·1!·σ(τ)¹ = 2·1 = 2), density 5·3·1 = 15,
so α = 5!/(2·15) = 4. -/
example : alphaWeight (mk [broom₃, vertex]) = 4 := by
  unfold alphaWeight
  rw [show order (mk [broom₃, vertex]) = 5 from rfl,
      show symmetry (mk [broom₃, vertex]) = 2 from rfl,
      show density (mk [broom₃, vertex]) = 15 from rfl]
  norm_num [Nat.factorial]

/-- Non-trivial witness: the 3-ladder plus a leaf
`mk [mk [cherry], vertex]` has `α = 4`. Row r=5 of Butcher Table
310(II) — the tree `f''(f'(f'f), f)`. Order 5, symmetry 1 (the
3-ladder `mk [cherry]` is distinct from the leaf and itself has
σ = 1), density 5·6·1 = 30, so α = 5!/(1·30) = 4. -/
example : alphaWeight (mk [mk [cherry], vertex]) = 4 := by
  unfold alphaWeight
  rw [show order (mk [mk [cherry], vertex]) = 5 from rfl,
      show symmetry (mk [mk [cherry], vertex]) = 1 from rfl,
      show density (mk [mk [cherry], vertex]) = 30 from rfl]
  norm_num [Nat.factorial]

end RootedTree

end OpenMath.Chapter3.Section310
