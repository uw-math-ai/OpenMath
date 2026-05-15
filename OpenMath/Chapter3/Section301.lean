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

/- ### `bseriesTerm` — Butcher §310 B-series term (cycle 254)

The summand `(h^r(t) / σ(t)) • F(t)(y₀)` of Butcher's series (310i),
together with the trivial-tree identity (the `t = τ` half of
`lem:310B`) and the θ-rewriting scaffold that the full `lem:310B`
proof goes through.

`lem:310B` itself is multi-cycle: per its `dependencies` field it
requires `thm:306A` (Taylor's theorem — unformalised) plus labeled-
tree machinery (absent — needed to state the LHS of (310i) as a sum
over labeled rooted trees with orbit divisions). Cycle 254 ships
only the pointwise prerequisites; cycle 255+ will extend to truncated
B-series and the small-r forms of `lem:310B`.

Placement note: this section was originally planned for
`Section310.lean` but `bseriesTerm` consumes `symmetry` (defined in
this file, Section301), which would create a circular import. Placed
here inside the same `OpenMath.Chapter3.Section310.RootedTree`
namespace so name resolution is unchanged. -/

/-- The per-tree B-series term `(h^r(t) / σ(t)) • F(t)(y₀)`, the
summand of Butcher's series (310i). For `f` smooth and `y₀ : E`,
this is the contribution of the rooted tree `t` to the
elementary-differential expansion of one ODE step.

The `(σ(t) : ℝ)` cast in the denominator mirrors `alphaWeight`'s
convention (line 305 of this file); `symmetry_pos` gives
`0 < σ(t)`, so the quotient is well-defined. -/
noncomputable def bseriesTerm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) (t : RootedTree) : E :=
  (h ^ order t / (symmetry t : ℝ)) • elementaryDiff f y₀ t

/-- `lem:310B` `t = τ` case: at the trivial tree, the B-series term
reduces to `h • f(y₀)`. Butcher's proof of Lemma 310B describes this
case as "obvious"; in our σ-faithful formalisation it reduces to
`σ(τ) = 1`, `r(τ) = 1`, and `iteratedFDeriv ℝ 0 f y₀` collapsing to
`f y₀` (the `Fin 0`-indexed empty-tuple input to a 0-fold
derivative, `iteratedFDeriv_zero_apply`). -/
theorem bseriesTerm_vertex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) :
    bseriesTerm f y₀ h vertex = h • f y₀ := by
  unfold bseriesTerm vertex elementaryDiff
  simp [iteratedFDeriv_zero_apply,
        show order (mk []) = 1 from rfl,
        show symmetry (mk []) = 1 from rfl]

/-- `lem:310B` rearrangement core: at every rooted tree `t`, the
B-series term is invariant under multiplication by the elementary
weight `θ(t)` of the exact-solution operator. Since `θ ≡ 1`
(`theta_eq_one`, cycle 249), this is mathematically trivial — but it
is the pointwise algebraic identity Butcher's `lem:310B` proof goes
through to relate the labeled and unlabeled forms of (310i).

**NOT** the full statement of `lem:310B`. The full lemma asserts a
re-summation identity between a labeled-tree-orbit sum (LHS,
requires labeled-tree machinery not yet built) and the θ-weighted
unlabeled sum (RHS). Cycle 254 ships only the pointwise scaffold;
the re-summation requires `thm:306A` (Taylor's theorem) plus
labeled-tree infrastructure. -/
theorem bseriesTerm_eq_theta_smul_bseriesTerm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) (t : RootedTree) :
    bseriesTerm f y₀ h t = theta t • bseriesTerm f y₀ h t := by
  rw [theta_eq_one t, one_smul]

-- §310 B-series term non-vacuity witnesses (cycle 254).

example (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesTerm f y₀ h vertex = h • f y₀ :=
  bseriesTerm_vertex f y₀ h

example (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesTerm f y₀ h cherry =
      theta cherry • bseriesTerm f y₀ h cherry :=
  bseriesTerm_eq_theta_smul_bseriesTerm f y₀ h cherry

example (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesTerm f y₀ h broom₃ =
      theta broom₃ • bseriesTerm f y₀ h broom₃ :=
  bseriesTerm_eq_theta_smul_bseriesTerm f y₀ h broom₃

/- ### Truncated rooted trees + B-series partial sums (cycle 255)

Phase A.1 + A.2 of the `lem:310B` roadmap: the bounded-order subtype
`TruncatedRootedTree N` (Lean engineering scaffold for future cycles;
Butcher does not name it), and the partial sum `bseriesPartialSum`
indexed by a hand-enumerated `Finset RootedTree`.

A `Fintype (TruncatedRootedTree N)` instance is deliberately deferred
(it would require a decidable finite enumeration of all rooted trees
up to order `N` — mathematically Cayley's formula territory). Until
then, partial sums take an explicit `Finset` of trees; for small
hand-enumerated `S`, `bseriesPartialSum f y₀ h S` approximates
Butcher's (310i) to `O(h^{N+1})` where `N` bounds the orders in `S`. -/

/-- A rooted tree of order at most `N`. The `TruncatedRootedTree N`
subtype is the natural index set for B-series partial sums truncated
at order `N` (Butcher §310, the `O(h^{N+1})`-residual form). -/
def TruncatedRootedTree (N : ℕ) : Type :=
  { t : RootedTree // order t ≤ N }

namespace TruncatedRootedTree

/-- Order projection: `order (t : TruncatedRootedTree N) ≤ N`. -/
def order {N : ℕ} (t : TruncatedRootedTree N) : ℕ :=
  RootedTree.order t.val

theorem order_le {N : ℕ} (t : TruncatedRootedTree N) : t.order ≤ N :=
  t.property

end TruncatedRootedTree

/-- B-series partial sum over a finite set of rooted trees. For a
small hand-enumerated `S`, this approximates the full B-series
`(310i)` to `O(h^{N+1})` where `N` bounds the orders in `S`. -/
noncomputable def bseriesPartialSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) (S : Finset RootedTree) : E :=
  ∑ t ∈ S, bseriesTerm f y₀ h t

@[simp]
theorem bseriesPartialSum_empty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) :
    bseriesPartialSum f y₀ h ∅ = 0 := by
  simp [bseriesPartialSum]

theorem bseriesPartialSum_insert
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) {t : RootedTree} {S : Finset RootedTree}
    (ht : t ∉ S) :
    bseriesPartialSum f y₀ h (insert t S) =
      bseriesTerm f y₀ h t + bseriesPartialSum f y₀ h S := by
  simp [bseriesPartialSum, Finset.sum_insert ht]

/-- Singleton case (cycle 260): the B-series partial sum over `{t}`
collapses to the bare summand `bseriesTerm f y₀ h t`. Mechanical
`Finset.sum_singleton` port; downstream consumer for `lem:310B` Phase
E small-`r` cases. -/
theorem bseriesPartialSum_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) (t : RootedTree) :
    bseriesPartialSum f y₀ h {t} = bseriesTerm f y₀ h t := by
  simp [bseriesPartialSum]

/-- Disjoint-union additivity (cycle 260): the B-series partial sum
over `S₁ ∪ S₂` decomposes additively whenever `S₁` and `S₂` are
disjoint. Mechanical `Finset.sum_union` port; downstream consumer for
`lem:310B` Phase E inductive small-`r` cases (split trees of order
`≤ N` into trees of order exactly `N` and order `< N`). -/
theorem bseriesPartialSum_union
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) {S₁ S₂ : Finset RootedTree}
    (hDisj : Disjoint S₁ S₂) :
    bseriesPartialSum f y₀ h (S₁ ∪ S₂) =
      bseriesPartialSum f y₀ h S₁ + bseriesPartialSum f y₀ h S₂ := by
  simp [bseriesPartialSum, Finset.sum_union hDisj]

-- §310 B-series partial sum non-vacuity witnesses (cycle 255).

example (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesPartialSum f y₀ h {vertex} = h • f y₀ := by
  rw [bseriesPartialSum, Finset.sum_singleton]
  exact bseriesTerm_vertex f y₀ h

example (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesPartialSum f y₀ h {vertex, cherry} =
      h • f y₀ + bseriesTerm f y₀ h cherry := by
  have hcv : (vertex : RootedTree) ∉ ({cherry} : Finset RootedTree) := by
    simp [Finset.mem_singleton, vertex, cherry]
  rw [show ({vertex, cherry} : Finset RootedTree) =
        insert vertex {cherry} from rfl,
      bseriesPartialSum_insert _ _ _ hcv,
      bseriesPartialSum, Finset.sum_singleton, bseriesTerm_vertex]

-- §310 B-series partial sum singleton non-vacuity witness (cycle 260):
-- exercises `bseriesPartialSum_singleton` + `bseriesTerm_vertex`.

example (y₀ h : ℝ) :
    bseriesPartialSum (id : ℝ → ℝ) y₀ h
        ({vertex} : Finset RootedTree)
      = h • y₀ := by
  rw [bseriesPartialSum_singleton, bseriesTerm_vertex]; rfl

/-- If every tree in `S` has order at most `N`, then every `t ∈ S`
lifts to a `TruncatedRootedTree N`. Useful for stating B-series
truncation results indexed by `TruncatedRootedTree N`. -/
theorem exists_truncated_of_forall_order_le
    {N : ℕ} {S : Finset RootedTree}
    (hS : ∀ t ∈ S, RootedTree.order t ≤ N) :
    ∀ t ∈ S, ∃ t' : TruncatedRootedTree N, t'.val = t := by
  intro t ht
  exact ⟨⟨t, hS t ht⟩, rfl⟩

/- ### α-weighted B-series partial sum (cycle 256)

Butcher (310i) is the α-weighted sum
`Σ_t α(t)·(h^r(t)/σ(t))·F(t)(y₀)`. Cycle 255 shipped the
unweighted summand `bseriesTerm` and its partial sum
`bseriesPartialSum`; cycle 256 adds the α-weighted companion as a
named summand `bseriesAlphaTerm` and partial sum
`bseriesAlphaPartialSum`. The two share their `_empty`/`_insert`
shape, so downstream cycles can re-use the cycle-255 tactical
recipes verbatim. -/

/-- The α-weighted per-tree B-series summand
`α(t) • (h^r(t)/σ(t)) • F(t)(y₀)` of Butcher's series (310i).

Factored as `alphaWeight t • bseriesTerm f y₀ h t` so that the
cycle-255 `bseriesTerm_*` rewrite library applies pointwise. -/
noncomputable def bseriesAlphaTerm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) (t : RootedTree) : E :=
  alphaWeight t • bseriesTerm f y₀ h t

/-- At the trivial tree `τ = vertex = mk []`, the α-weight is `1`
(`alphaWeight_vertex`, cycle 250), so the α-weighted summand
collapses to the bare `bseriesTerm_vertex` value `h • f y₀`. -/
theorem bseriesAlphaTerm_vertex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) :
    bseriesAlphaTerm f y₀ h vertex = h • f y₀ := by
  unfold bseriesAlphaTerm
  rw [show alphaWeight vertex = 1 from alphaWeight_vertex,
      one_smul, bseriesTerm_vertex]

/-- Butcher's series (310i), partial-sum form: the α-weighted
B-series approximation truncated to a hand-supplied
`Finset RootedTree`. For small `S`, this matches the textbook
`Σ_{t ∈ T} α(t)·(h^r(t)/σ(t))·F(t)(y₀)` exactly. -/
noncomputable def bseriesAlphaPartialSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) (S : Finset RootedTree) : E :=
  ∑ t ∈ S, bseriesAlphaTerm f y₀ h t

@[simp]
theorem bseriesAlphaPartialSum_empty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) :
    bseriesAlphaPartialSum f y₀ h ∅ = 0 := by
  simp [bseriesAlphaPartialSum]

theorem bseriesAlphaPartialSum_insert
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) {t : RootedTree} {S : Finset RootedTree}
    (ht : t ∉ S) :
    bseriesAlphaPartialSum f y₀ h (insert t S) =
      bseriesAlphaTerm f y₀ h t + bseriesAlphaPartialSum f y₀ h S := by
  simp [bseriesAlphaPartialSum, Finset.sum_insert ht]

/-- Singleton case (cycle 260): the α-weighted B-series partial sum
over `{t}` collapses to the bare α-weighted summand
`bseriesAlphaTerm f y₀ h t`. Mechanical `Finset.sum_singleton` port;
matches the cycle-260 `bseriesPartialSum_singleton` shape on the
α-weighted family. -/
theorem bseriesAlphaPartialSum_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) (t : RootedTree) :
    bseriesAlphaPartialSum f y₀ h {t} = bseriesAlphaTerm f y₀ h t := by
  simp [bseriesAlphaPartialSum]

/-- Disjoint-union additivity (cycle 260): the α-weighted B-series
partial sum over `S₁ ∪ S₂` decomposes additively whenever `S₁` and
`S₂` are disjoint. Mechanical `Finset.sum_union` port; matches the
cycle-260 `bseriesPartialSum_union` shape on the α-weighted family. -/
theorem bseriesAlphaPartialSum_union
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) {S₁ S₂ : Finset RootedTree}
    (hDisj : Disjoint S₁ S₂) :
    bseriesAlphaPartialSum f y₀ h (S₁ ∪ S₂) =
      bseriesAlphaPartialSum f y₀ h S₁ + bseriesAlphaPartialSum f y₀ h S₂ := by
  simp [bseriesAlphaPartialSum, Finset.sum_union hDisj]

-- §310 (310i) α-weighted partial sum non-vacuity witnesses (cycle 256).

example (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesAlphaPartialSum f y₀ h {vertex} = h • f y₀ := by
  rw [bseriesAlphaPartialSum, Finset.sum_singleton]
  exact bseriesAlphaTerm_vertex f y₀ h

example (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesAlphaPartialSum f y₀ h {vertex, cherry} =
      h • f y₀ + bseriesAlphaTerm f y₀ h cherry := by
  have hcv : (vertex : RootedTree) ∉ ({cherry} : Finset RootedTree) := by
    simp [Finset.mem_singleton, vertex, cherry]
  rw [show ({vertex, cherry} : Finset RootedTree) =
        insert vertex {cherry} from rfl,
      bseriesAlphaPartialSum_insert _ _ _ hcv,
      bseriesAlphaPartialSum, Finset.sum_singleton, bseriesAlphaTerm_vertex]

-- §310 (310i) α-weighted partial sum singleton non-vacuity witness
-- (cycle 260): exercises `bseriesAlphaPartialSum_singleton` +
-- `bseriesAlphaTerm_vertex`.

example (y₀ h : ℝ) :
    bseriesAlphaPartialSum (id : ℝ → ℝ) y₀ h
        ({vertex} : Finset RootedTree)
      = h • y₀ := by
  rw [bseriesAlphaPartialSum_singleton, bseriesAlphaTerm_vertex]; rfl

/- ### Exact-solution B-series partial sum (cycle 266)

Butcher §312 expresses the exact-solution operator `E` via the
B-series whose per-tree coefficient is `h^{r(t)} / (σ(t) · γ(t))`.
Equivalently this is `α(t)/r(t)! · bseriesTerm` (with the factorial
denominator `γ(t)`, since `γ(t) = r(t) · ∏ γ(tᵢ)` collects the
factorial-style multiplicity from the recursion — invisible at
`r = 1` where `γ(τ) = 1!`, but bites at `r ≥ 2`).

This differs from cycle 256's `bseriesAlphaTerm := α • bseriesTerm`,
which is the Butcher-(310i)-form *RK-method* B-series term **without**
the `1/r!` factor. Both forms are valid textbook objects but for
different purposes: `bseriesAlphaTerm` is the RK-method B-series
(used in `lem:310B`'s LHS), while `bseriesExactTerm` is the
**exact-solution Taylor B-series** (used to bridge with Butcher §311's
Taylor expansion of the exact solution).

Concretely, at the cherry `t = [τ]` with `r = 2`, `σ = 1`, `γ = 2`:
* `bseriesAlphaTerm f y₀ h cherry` = `1 · (h²/1) · F(cherry)(y₀)`
  = `h² · (f' · f)` (no `1/2` factor).
* `bseriesExactTerm f y₀ h cherry` = `(h² / (1 · 2)) · F(cherry)(y₀)`
  = `(h²/2) · (f' · f)` (the factor required by Taylor's theorem).

The Phase E.1 bridge `lem_311A_order_two_partialSum` (Section311)
consumes `bseriesExactTerm`, not `bseriesAlphaTerm`. -/

/-- The per-tree summand of the **exact-solution B-series**
(Butcher §312):

  `bseriesExactTerm f y₀ h t = (h^{r(t)} / (σ(t) · γ(t))) • F(t)(y₀)`.

Equivalently `α(t)/r(t)! · bseriesTerm`: the `1/r(t)!` factor is
collected into the `γ(t)` denominator via `γ(t) = r(t) · ∏ γ(tᵢ)`
(Butcher (301a)). See the section comment for the cycle-256
`bseriesAlphaTerm` distinction.

`density_pos t` (= `γ(t) > 0`) and `symmetry_pos t` ensure the
quotient is well-defined for every `t`. -/
noncomputable def bseriesExactTerm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) (t : RootedTree) : E :=
  (h ^ order t / ((symmetry t : ℝ) * (density t : ℝ))) •
    elementaryDiff f y₀ t

/-- At the trivial tree `τ = vertex = mk []`: `r(τ) = σ(τ) = γ(τ) = 1`
(`tau_values`), so the exact-solution coefficient collapses to `h¹`,
and `elementaryDiff f y₀ vertex = f y₀`. Hence
`bseriesExactTerm f y₀ h vertex = h • f y₀`. -/
theorem bseriesExactTerm_vertex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) :
    bseriesExactTerm f y₀ h vertex = h • f y₀ := by
  unfold bseriesExactTerm vertex elementaryDiff
  simp [iteratedFDeriv_zero_apply,
        show order (mk []) = 1 from rfl,
        show symmetry (mk []) = 1 from rfl,
        show density (mk []) = 1 from rfl]

/-- **Scalar closed form at the cherry tree.** For `f : ℝ → ℝ`, the
exact-solution B-series term at `cherry = mk [vertex]` is
`h²/2 · (f'(y₀) · f(y₀))`.

This is the load-bearing faithfulness check distinguishing
`bseriesExactTerm` from cycle 256's `bseriesAlphaTerm`: the latter
gives `h² · (f' · f)` at the cherry, the former gives `h²/2 · (f' · f)`
— the missing `1/r!` factor that makes Taylor's theorem fire. -/
theorem bseriesExactTerm_cherry_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h cherry = h^2 / 2 * (deriv f y₀ * f y₀) := by
  unfold bseriesExactTerm cherry
  rw [show order (mk [vertex]) = 2 from rfl,
      show symmetry (mk [vertex]) = 1 from rfl,
      show density (mk [vertex]) = 2 from rfl]
  -- Compute `elementaryDiff f y₀ (mk [vertex])`.
  have hED : elementaryDiff f y₀ (mk [vertex]) = deriv f y₀ * f y₀ := by
    unfold elementaryDiff
    have hED_v : elementaryDiff f y₀ vertex = f y₀ := by
      show elementaryDiff f y₀ (mk []) = f y₀
      unfold elementaryDiff
      exact iteratedFDeriv_zero_apply _
    -- `iteratedFDeriv ℝ 1 f y₀ ![f y₀] = fderiv ℝ f y₀ (f y₀) = f y₀ • deriv f y₀`.
    show iteratedFDeriv ℝ 1 f y₀
            (fun i : Fin 1 => elementaryDiff f y₀ ([(vertex : RootedTree)].get i))
          = deriv f y₀ * f y₀
    rw [iteratedFDeriv_one_apply, fderiv_eq_smul_deriv,
        show [(vertex : RootedTree)].get (0 : Fin 1) = vertex from rfl, hED_v,
        smul_eq_mul]
    ring
  rw [hED, smul_eq_mul]
  push_cast
  ring

/-- **Scalar closed form at `broom₃ = mk [vertex, vertex]`.** For
`f : ℝ → ℝ`, the exact-solution B-series term at `broom₃` is
`h³/6 · (f''(y₀) · f(y₀)²)`.

Cycle 267 / Phase E.1 extension: the order-3 second-derivative term
of the exact-solution Taylor expansion (Butcher Table 310(II) row
r=3, first tree). Combined with `bseriesExactTerm_mkCherry_scalar`,
this discharges the order-3 partial-sum bridge to cycle 257's
`lem_311A_order_three`.

Coefficients: `r(broom₃) = 3`, `σ(broom₃) = 2`, `γ(broom₃) = 3`, so
`h^r / (σ · γ) = h³ / (2·3) = h³/6`. -/
theorem bseriesExactTerm_broom₃_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h broom₃
      = h^3 / 6 * (deriv (deriv f) y₀ * (f y₀) ^ 2) := by
  unfold bseriesExactTerm broom₃
  rw [show order (mk [vertex, vertex]) = 3 from rfl,
      show symmetry (mk [vertex, vertex]) = 2 from rfl,
      show density (mk [vertex, vertex]) = 3 from rfl]
  -- Compute `elementaryDiff f y₀ (mk [vertex, vertex])`.
  have hED : elementaryDiff f y₀ (mk [vertex, vertex])
      = deriv (deriv f) y₀ * (f y₀) ^ 2 := by
    have hED_v : elementaryDiff f y₀ vertex = f y₀ := by
      show elementaryDiff f y₀ (mk []) = f y₀
      unfold elementaryDiff
      exact iteratedFDeriv_zero_apply _
    unfold elementaryDiff
    show iteratedFDeriv ℝ 2 f y₀
            (fun i : Fin 2 => elementaryDiff f y₀
              ([(vertex : RootedTree), vertex].get i))
          = deriv (deriv f) y₀ * (f y₀) ^ 2
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
        Fin.prod_univ_two,
        show ([(vertex : RootedTree), vertex] : List RootedTree).get (0 : Fin 2)
          = vertex from rfl,
        show ([(vertex : RootedTree), vertex] : List RootedTree).get (1 : Fin 2)
          = vertex from rfl,
        hED_v,
        show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    ring
  rw [hED, smul_eq_mul]
  push_cast
  ring

/-- **Scalar closed form at the depth-2 chain `mk [cherry]`.** For
`f : ℝ → ℝ`, the exact-solution B-series term at `mk [cherry]` is
`h³/6 · ((f'(y₀))² · f(y₀))`.

Cycle 267 / Phase E.1 extension: the order-3 first-derivative-squared
term of the exact-solution Taylor expansion (Butcher Table 310(II)
row r=3, second tree — the depth-2 chain `f'(f'·f)`). Combined with
`bseriesExactTerm_broom₃_scalar`, this discharges the order-3
partial-sum bridge to cycle 257's `lem_311A_order_three`.

Coefficients: `r(mk [cherry]) = 3`, `σ(mk [cherry]) = 1`,
`γ(mk [cherry]) = 6`, so `h^r / (σ · γ) = h³ / (1·6) = h³/6`. -/
theorem bseriesExactTerm_mkCherry_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h (mk [cherry])
      = h^3 / 6 * ((deriv f y₀) ^ 2 * f y₀) := by
  unfold bseriesExactTerm
  rw [show order (mk [cherry]) = 3 from rfl,
      show symmetry (mk [cherry]) = 1 from rfl,
      show density (mk [cherry]) = 6 from rfl]
  -- Compute `elementaryDiff f y₀ (mk [cherry])`.
  have hED : elementaryDiff f y₀ (mk [cherry])
      = (deriv f y₀) ^ 2 * f y₀ := by
    -- Re-derive `elementaryDiff f y₀ cherry = deriv f y₀ * f y₀`
    -- (the intermediate step of cycle 266's `bseriesExactTerm_cherry_scalar`).
    have hED_v : elementaryDiff f y₀ vertex = f y₀ := by
      show elementaryDiff f y₀ (mk []) = f y₀
      unfold elementaryDiff
      exact iteratedFDeriv_zero_apply _
    have hED_cherry : elementaryDiff f y₀ cherry = deriv f y₀ * f y₀ := by
      show elementaryDiff f y₀ (mk [vertex]) = deriv f y₀ * f y₀
      unfold elementaryDiff
      show iteratedFDeriv ℝ 1 f y₀
              (fun i : Fin 1 => elementaryDiff f y₀
                ([(vertex : RootedTree)].get i))
            = deriv f y₀ * f y₀
      rw [iteratedFDeriv_one_apply, fderiv_eq_smul_deriv,
          show [(vertex : RootedTree)].get (0 : Fin 1) = vertex from rfl, hED_v,
          smul_eq_mul]
      ring
    unfold elementaryDiff
    show iteratedFDeriv ℝ 1 f y₀
            (fun i : Fin 1 => elementaryDiff f y₀ ([cherry].get i))
          = (deriv f y₀) ^ 2 * f y₀
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
        Fin.prod_univ_one,
        show ([cherry] : List RootedTree).get (0 : Fin 1) = cherry from rfl,
        hED_cherry, iteratedDeriv_one]
    ring
  rw [hED, smul_eq_mul]
  push_cast
  ring

/-- **Scalar closed form at `bushy = mk [vertex, vertex, vertex]`.** For
`f : ℝ → ℝ`, the exact-solution B-series term at `bushy` is
`h⁴/24 · (f'''(y₀) · f(y₀)³)`.

Cycle 268 / Phase E.1 extension: the order-4 third-derivative term
of the exact-solution Taylor expansion (Butcher Table 310(II) row
r=4, first tree). Coefficients: `r(bushy) = 4`, `σ(bushy) = 6`,
`γ(bushy) = 4`, so `h^r / (σ·γ) = h⁴ / 24`. -/
theorem bseriesExactTerm_bushy_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h bushy
      = h^4 / 24 * (deriv (deriv (deriv f)) y₀ * (f y₀) ^ 3) := by
  unfold bseriesExactTerm bushy
  rw [show order (mk [vertex, vertex, vertex]) = 4 from rfl,
      show symmetry (mk [vertex, vertex, vertex]) = 6 from rfl,
      show density (mk [vertex, vertex, vertex]) = 4 from rfl]
  -- Compute `elementaryDiff f y₀ (mk [vertex, vertex, vertex])`.
  have hED : elementaryDiff f y₀ (mk [vertex, vertex, vertex])
      = deriv (deriv (deriv f)) y₀ * (f y₀) ^ 3 := by
    have hED_v : elementaryDiff f y₀ vertex = f y₀ := by
      show elementaryDiff f y₀ (mk []) = f y₀
      unfold elementaryDiff
      exact iteratedFDeriv_zero_apply _
    unfold elementaryDiff
    show iteratedFDeriv ℝ 3 f y₀
            (fun i : Fin 3 => elementaryDiff f y₀
              ([(vertex : RootedTree), vertex, vertex].get i))
          = deriv (deriv (deriv f)) y₀ * (f y₀) ^ 3
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
        Fin.prod_univ_three,
        show ([(vertex : RootedTree), vertex, vertex] : List RootedTree).get
              (0 : Fin 3) = vertex from rfl,
        show ([(vertex : RootedTree), vertex, vertex] : List RootedTree).get
              (1 : Fin 3) = vertex from rfl,
        show ([(vertex : RootedTree), vertex, vertex] : List RootedTree).get
              (2 : Fin 3) = vertex from rfl,
        hED_v,
        show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
        show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    ring
  rw [hED, smul_eq_mul]
  push_cast
  ring

/-- **Scalar closed form at `mk [vertex, cherry]`.** For `f : ℝ → ℝ`,
the exact-solution B-series term at the order-4 tree `mk [vertex, cherry]`
is `h⁴/8 · (f''(y₀) · f'(y₀) · f(y₀)²)`.

Cycle 268 / Phase E.1 extension: the order-4 second-derivative ×
first-derivative term of the exact-solution Taylor expansion (Butcher
Table 310(II) row r=4, second tree). Coefficients: `r = 4`, `σ = 1`,
`γ = 8`, so `h^r / (σ·γ) = h⁴ / 8`. -/
theorem bseriesExactTerm_mkVertexCherry_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h (mk [vertex, cherry])
      = h^4 / 8 * (deriv (deriv f) y₀ * deriv f y₀ * (f y₀) ^ 2) := by
  unfold bseriesExactTerm
  rw [show order (mk [vertex, cherry]) = 4 from rfl,
      show symmetry (mk [vertex, cherry]) = 1 from rfl,
      show density (mk [vertex, cherry]) = 8 from rfl]
  -- Compute `elementaryDiff f y₀ (mk [vertex, cherry])`.
  have hED : elementaryDiff f y₀ (mk [vertex, cherry])
      = deriv (deriv f) y₀ * deriv f y₀ * (f y₀) ^ 2 := by
    have hED_v : elementaryDiff f y₀ vertex = f y₀ := by
      show elementaryDiff f y₀ (mk []) = f y₀
      unfold elementaryDiff
      exact iteratedFDeriv_zero_apply _
    have hED_cherry : elementaryDiff f y₀ cherry = deriv f y₀ * f y₀ := by
      show elementaryDiff f y₀ (mk [vertex]) = deriv f y₀ * f y₀
      unfold elementaryDiff
      show iteratedFDeriv ℝ 1 f y₀
              (fun i : Fin 1 => elementaryDiff f y₀
                ([(vertex : RootedTree)].get i))
            = deriv f y₀ * f y₀
      rw [iteratedFDeriv_one_apply, fderiv_eq_smul_deriv,
          show [(vertex : RootedTree)].get (0 : Fin 1) = vertex from rfl, hED_v,
          smul_eq_mul]
      ring
    unfold elementaryDiff
    show iteratedFDeriv ℝ 2 f y₀
            (fun i : Fin 2 => elementaryDiff f y₀
              ([(vertex : RootedTree), cherry].get i))
          = deriv (deriv f) y₀ * deriv f y₀ * (f y₀) ^ 2
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
        Fin.prod_univ_two,
        show ([(vertex : RootedTree), cherry] : List RootedTree).get
              (0 : Fin 2) = vertex from rfl,
        show ([(vertex : RootedTree), cherry] : List RootedTree).get
              (1 : Fin 2) = cherry from rfl,
        hED_v, hED_cherry,
        show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    ring
  rw [hED, smul_eq_mul]
  push_cast
  ring

/-- **Scalar closed form at `mk [broom₃]`.** For `f : ℝ → ℝ`, the
exact-solution B-series term at the order-4 tree `mk [broom₃]` is
`h⁴/24 · (f'(y₀) · f''(y₀) · f(y₀)²)`.

Cycle 268 / Phase E.1 extension: the order-4 first-derivative ×
second-derivative term of the exact-solution Taylor expansion
(Butcher Table 310(II) row r=4, third tree). Coefficients:
`r(mk [broom₃]) = 4`, `σ(mk [broom₃]) = 2` (σ-recursion
`σ(mk [t]) = 1!·σ(t)^1 = σ(t)`, with `σ(broom₃) = 2`),
`γ(mk [broom₃]) = 12`, so `h^r / (σ·γ) = h⁴ / 24`. -/
theorem bseriesExactTerm_mkBroom₃_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h (mk [broom₃])
      = h^4 / 24 * (deriv f y₀ * deriv (deriv f) y₀ * (f y₀) ^ 2) := by
  unfold bseriesExactTerm
  rw [show order (mk [broom₃]) = 4 from rfl,
      show symmetry (mk [broom₃]) = 2 from rfl,
      show density (mk [broom₃]) = 12 from rfl]
  -- Compute `elementaryDiff f y₀ (mk [broom₃])`.
  have hED : elementaryDiff f y₀ (mk [broom₃])
      = deriv f y₀ * deriv (deriv f) y₀ * (f y₀) ^ 2 := by
    have hED_v : elementaryDiff f y₀ vertex = f y₀ := by
      show elementaryDiff f y₀ (mk []) = f y₀
      unfold elementaryDiff
      exact iteratedFDeriv_zero_apply _
    -- Inner: elementaryDiff f y₀ broom₃ = f''(y₀) · f(y₀)²
    -- (cycle 267 `bseriesExactTerm_broom₃_scalar` derivation, at
    -- the elementaryDiff level).
    have hED_broom : elementaryDiff f y₀ broom₃
        = deriv (deriv f) y₀ * (f y₀) ^ 2 := by
      show elementaryDiff f y₀ (mk [vertex, vertex]) = _
      unfold elementaryDiff
      show iteratedFDeriv ℝ 2 f y₀
              (fun i : Fin 2 => elementaryDiff f y₀
                ([(vertex : RootedTree), vertex].get i))
            = deriv (deriv f) y₀ * (f y₀) ^ 2
      rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
          Fin.prod_univ_two,
          show ([(vertex : RootedTree), vertex] : List RootedTree).get
                (0 : Fin 2) = vertex from rfl,
          show ([(vertex : RootedTree), vertex] : List RootedTree).get
                (1 : Fin 2) = vertex from rfl,
          hED_v,
          show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
      ring
    unfold elementaryDiff
    show iteratedFDeriv ℝ 1 f y₀
            (fun i : Fin 1 => elementaryDiff f y₀ ([broom₃].get i))
          = deriv f y₀ * deriv (deriv f) y₀ * (f y₀) ^ 2
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
        Fin.prod_univ_one,
        show ([broom₃] : List RootedTree).get (0 : Fin 1) = broom₃ from rfl,
        hED_broom, iteratedDeriv_one]
    ring
  rw [hED, smul_eq_mul]
  push_cast
  ring

/-- **Scalar closed form at `mk [mk [cherry]]`.** For `f : ℝ → ℝ`, the
exact-solution B-series term at the order-4 tree `mk [mk [cherry]]`
(the depth-3 chain) is `h⁴/24 · ((f'(y₀))³ · f(y₀))`.

Cycle 268 / Phase E.1 extension: the order-4 first-derivative-cubed
term of the exact-solution Taylor expansion (Butcher Table 310(II)
row r=4, fourth tree). Coefficients: `r(mk [mk [cherry]]) = 4`,
`σ(mk [mk [cherry]]) = 1`, `γ(mk [mk [cherry]]) = 24`, so
`h^r / (σ·γ) = h⁴ / 24`. -/
theorem bseriesExactTerm_mkMkCherry_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h (mk [mk [cherry]])
      = h^4 / 24 * ((deriv f y₀) ^ 3 * f y₀) := by
  unfold bseriesExactTerm
  rw [show order (mk [mk [cherry]]) = 4 from rfl,
      show symmetry (mk [mk [cherry]]) = 1 from rfl,
      show density (mk [mk [cherry]]) = 24 from rfl]
  -- Compute `elementaryDiff f y₀ (mk [mk [cherry]])`.
  have hED : elementaryDiff f y₀ (mk [mk [cherry]])
      = (deriv f y₀) ^ 3 * f y₀ := by
    have hED_v : elementaryDiff f y₀ vertex = f y₀ := by
      show elementaryDiff f y₀ (mk []) = f y₀
      unfold elementaryDiff
      exact iteratedFDeriv_zero_apply _
    have hED_cherry : elementaryDiff f y₀ cherry = deriv f y₀ * f y₀ := by
      show elementaryDiff f y₀ (mk [vertex]) = deriv f y₀ * f y₀
      unfold elementaryDiff
      show iteratedFDeriv ℝ 1 f y₀
              (fun i : Fin 1 => elementaryDiff f y₀
                ([(vertex : RootedTree)].get i))
            = deriv f y₀ * f y₀
      rw [iteratedFDeriv_one_apply, fderiv_eq_smul_deriv,
          show [(vertex : RootedTree)].get (0 : Fin 1) = vertex from rfl, hED_v,
          smul_eq_mul]
      ring
    -- Inner: elementaryDiff f y₀ (mk [cherry]) = (f'(y₀))² · f(y₀)
    -- (cycle 267 `bseriesExactTerm_mkCherry_scalar` derivation, at the
    -- elementaryDiff level).
    have hED_mkCherry : elementaryDiff f y₀ (mk [cherry])
        = (deriv f y₀) ^ 2 * f y₀ := by
      unfold elementaryDiff
      show iteratedFDeriv ℝ 1 f y₀
              (fun i : Fin 1 => elementaryDiff f y₀ ([cherry].get i))
            = (deriv f y₀) ^ 2 * f y₀
      rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
          Fin.prod_univ_one,
          show ([cherry] : List RootedTree).get (0 : Fin 1) = cherry from rfl,
          hED_cherry, iteratedDeriv_one]
      ring
    unfold elementaryDiff
    show iteratedFDeriv ℝ 1 f y₀
            (fun i : Fin 1 => elementaryDiff f y₀ ([mk [cherry]].get i))
          = (deriv f y₀) ^ 3 * f y₀
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
        Fin.prod_univ_one,
        show ([mk [cherry]] : List RootedTree).get (0 : Fin 1)
          = mk [cherry] from rfl,
        hED_mkCherry, iteratedDeriv_one]
    ring
  rw [hED, smul_eq_mul]
  push_cast
  ring

/- ### Cycle 269 / Phase E.1 — order-5 per-tree scalar closed forms

Nine new `bseriesExactTerm_*_scalar` closed-form theorems for the nine
unordered rooted trees of order 5 (Butcher Table 310(II) row r=5).
Each follows the cycle 266–268 mechanical recipe:

1. Unfold `bseriesExactTerm`, rewrite `(r, σ, γ)` by `rfl` reductions.
2. Establish the inline `elementaryDiff` closed form via
   `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` and the appropriate
   `Fin.prod_univ_{one,two,three,four}` arity hook.
3. For one-child wrapping trees, reuse the cycle 266–268
   `iteratedFDeriv ℝ 1` mechanism.
4. Reduce nested `iteratedDeriv` via `iteratedDeriv_succ` + `iteratedDeriv_one`.
5. Close with `smul_eq_mul`, `push_cast`, `ring`.

Together with cycle 268's four order-4 closed forms and cycle 266–267's
order ≤ 3 closed forms, these 9 lemmas saturate the per-tree library
through order 5, ready for cycle 270's 17-tree partial-sum bridge to
cycle 259's `lem_311A_order_five`. -/

/-- **Scalar closed form at `bushy₄ = mk [vertex, vertex, vertex, vertex]`.**
For `f : ℝ → ℝ`, the exact-solution B-series term at the order-5 tree
`bushy₄` is `h⁵/120 · (f''''(y₀) · f(y₀)⁴)`.

Cycle 269 / Phase E.1 (T1, order 5, first row of Butcher Table 310(II)
r=5). Coefficients: `r(bushy₄) = 5`, `σ(bushy₄) = 4! = 24`,
`γ(bushy₄) = 5`, so `h^r / (σ·γ) = h⁵ / 120`. -/
theorem bseriesExactTerm_bushy₄_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h bushy₄
      = h^5 / 120 * (deriv (deriv (deriv (deriv f))) y₀ * (f y₀) ^ 4) := by
  unfold bseriesExactTerm bushy₄
  rw [show order (mk [vertex, vertex, vertex, vertex]) = 5 from rfl,
      show symmetry (mk [vertex, vertex, vertex, vertex]) = 24 from rfl,
      show density (mk [vertex, vertex, vertex, vertex]) = 5 from rfl]
  have hED : elementaryDiff f y₀ (mk [vertex, vertex, vertex, vertex])
      = deriv (deriv (deriv (deriv f))) y₀ * (f y₀) ^ 4 := by
    have hED_v : elementaryDiff f y₀ vertex = f y₀ := by
      show elementaryDiff f y₀ (mk []) = f y₀
      unfold elementaryDiff
      exact iteratedFDeriv_zero_apply _
    unfold elementaryDiff
    show iteratedFDeriv ℝ 4 f y₀
            (fun i : Fin 4 => elementaryDiff f y₀
              ([(vertex : RootedTree), vertex, vertex, vertex].get i))
          = deriv (deriv (deriv (deriv f))) y₀ * (f y₀) ^ 4
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
        Fin.prod_univ_four,
        show ([(vertex : RootedTree), vertex, vertex, vertex] :
              List RootedTree).get (0 : Fin 4) = vertex from rfl,
        show ([(vertex : RootedTree), vertex, vertex, vertex] :
              List RootedTree).get (1 : Fin 4) = vertex from rfl,
        show ([(vertex : RootedTree), vertex, vertex, vertex] :
              List RootedTree).get (2 : Fin 4) = vertex from rfl,
        show ([(vertex : RootedTree), vertex, vertex, vertex] :
              List RootedTree).get (3 : Fin 4) = vertex from rfl,
        hED_v,
        show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_succ,
        show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
        show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    ring
  rw [hED, smul_eq_mul]
  push_cast
  ring

/-- **Scalar closed form at `mk [mk [mk [cherry]]]`.** For `f : ℝ → ℝ`,
the exact-solution B-series term at the order-5 chain `mk [mk [mk [cherry]]]`
is `h⁵/120 · ((f'(y₀))⁴ · f(y₀))`.

Cycle 269 / Phase E.1 (T9, the depth-5 chain `f'(f'(f'(f'·f)))`).
Coefficients: `r = 5`, `σ = 1` (single-child chain), `γ = 120 = 5!`,
so `h^r / (σ·γ) = h⁵ / 120`. -/
theorem bseriesExactTerm_mkMkMkCherry_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h (mk [mk [mk [cherry]]])
      = h^5 / 120 * ((deriv f y₀) ^ 4 * f y₀) := by
  unfold bseriesExactTerm
  rw [show order (mk [mk [mk [cherry]]]) = 5 from rfl,
      show symmetry (mk [mk [mk [cherry]]]) = 1 from rfl,
      show density (mk [mk [mk [cherry]]]) = 120 from rfl]
  have hED : elementaryDiff f y₀ (mk [mk [mk [cherry]]])
      = (deriv f y₀) ^ 4 * f y₀ := by
    have hED_v : elementaryDiff f y₀ vertex = f y₀ := by
      show elementaryDiff f y₀ (mk []) = f y₀
      unfold elementaryDiff
      exact iteratedFDeriv_zero_apply _
    have hED_cherry : elementaryDiff f y₀ cherry = deriv f y₀ * f y₀ := by
      show elementaryDiff f y₀ (mk [vertex]) = deriv f y₀ * f y₀
      unfold elementaryDiff
      show iteratedFDeriv ℝ 1 f y₀
              (fun i : Fin 1 => elementaryDiff f y₀
                ([(vertex : RootedTree)].get i))
            = deriv f y₀ * f y₀
      rw [iteratedFDeriv_one_apply, fderiv_eq_smul_deriv,
          show [(vertex : RootedTree)].get (0 : Fin 1) = vertex from rfl, hED_v,
          smul_eq_mul]
      ring
    have hED_mkCherry : elementaryDiff f y₀ (mk [cherry])
        = (deriv f y₀) ^ 2 * f y₀ := by
      unfold elementaryDiff
      show iteratedFDeriv ℝ 1 f y₀
              (fun i : Fin 1 => elementaryDiff f y₀ ([cherry].get i))
            = (deriv f y₀) ^ 2 * f y₀
      rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
          Fin.prod_univ_one,
          show ([cherry] : List RootedTree).get (0 : Fin 1) = cherry from rfl,
          hED_cherry, iteratedDeriv_one]
      ring
    have hED_mkMkCherry : elementaryDiff f y₀ (mk [mk [cherry]])
        = (deriv f y₀) ^ 3 * f y₀ := by
      unfold elementaryDiff
      show iteratedFDeriv ℝ 1 f y₀
              (fun i : Fin 1 => elementaryDiff f y₀ ([mk [cherry]].get i))
            = (deriv f y₀) ^ 3 * f y₀
      rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
          Fin.prod_univ_one,
          show ([mk [cherry]] : List RootedTree).get (0 : Fin 1)
            = mk [cherry] from rfl,
          hED_mkCherry, iteratedDeriv_one]
      ring
    unfold elementaryDiff
    show iteratedFDeriv ℝ 1 f y₀
            (fun i : Fin 1 => elementaryDiff f y₀
              ([mk [mk [cherry]]].get i))
          = (deriv f y₀) ^ 4 * f y₀
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
        Fin.prod_univ_one,
        show ([mk [mk [cherry]]] : List RootedTree).get (0 : Fin 1)
          = mk [mk [cherry]] from rfl,
        hED_mkMkCherry, iteratedDeriv_one]
    ring
  rw [hED, smul_eq_mul]
  push_cast
  ring

/-- **Scalar closed form at `mk [vertex, broom₃]`.** For `f : ℝ → ℝ`,
the exact-solution B-series term at the order-5 tree `mk [vertex, broom₃]`
is `h⁵/30 · ((f''(y₀))² · f(y₀)³)`.

Cycle 269 / Phase E.1 (T3, Butcher Table 310(II) row r=5).
Coefficients: `r = 5`, `σ = 2` (σ-recursion at multi-distinct children:
`1!·σ(v)·1!·σ(broom₃) = 1·1·1·2`), `γ = 15`, so
`h^r / (σ·γ) = h⁵ / 30`. -/
theorem bseriesExactTerm_mkVertexBroom₃_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h (mk [vertex, broom₃])
      = h^5 / 30 * ((deriv (deriv f) y₀) ^ 2 * (f y₀) ^ 3) := by
  unfold bseriesExactTerm
  rw [show order (mk [vertex, broom₃]) = 5 from rfl,
      show symmetry (mk [vertex, broom₃]) = 2 from rfl,
      show density (mk [vertex, broom₃]) = 15 from rfl]
  have hED : elementaryDiff f y₀ (mk [vertex, broom₃])
      = (deriv (deriv f) y₀) ^ 2 * (f y₀) ^ 3 := by
    have hED_v : elementaryDiff f y₀ vertex = f y₀ := by
      show elementaryDiff f y₀ (mk []) = f y₀
      unfold elementaryDiff
      exact iteratedFDeriv_zero_apply _
    have hED_broom : elementaryDiff f y₀ broom₃
        = deriv (deriv f) y₀ * (f y₀) ^ 2 := by
      show elementaryDiff f y₀ (mk [vertex, vertex]) = _
      unfold elementaryDiff
      show iteratedFDeriv ℝ 2 f y₀
              (fun i : Fin 2 => elementaryDiff f y₀
                ([(vertex : RootedTree), vertex].get i))
            = deriv (deriv f) y₀ * (f y₀) ^ 2
      rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
          Fin.prod_univ_two,
          show ([(vertex : RootedTree), vertex] : List RootedTree).get
                (0 : Fin 2) = vertex from rfl,
          show ([(vertex : RootedTree), vertex] : List RootedTree).get
                (1 : Fin 2) = vertex from rfl,
          hED_v,
          show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
      ring
    unfold elementaryDiff
    show iteratedFDeriv ℝ 2 f y₀
            (fun i : Fin 2 => elementaryDiff f y₀
              ([(vertex : RootedTree), broom₃].get i))
          = (deriv (deriv f) y₀) ^ 2 * (f y₀) ^ 3
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
        Fin.prod_univ_two,
        show ([(vertex : RootedTree), broom₃] : List RootedTree).get
              (0 : Fin 2) = vertex from rfl,
        show ([(vertex : RootedTree), broom₃] : List RootedTree).get
              (1 : Fin 2) = broom₃ from rfl,
        hED_v, hED_broom,
        show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    ring
  rw [hED, smul_eq_mul]
  push_cast
  ring

/-- **Scalar closed form at `mk [bushy]`.** For `f : ℝ → ℝ`,
the exact-solution B-series term at the order-5 tree `mk [bushy]`
is `h⁵/120 · (f'''(y₀) · f'(y₀) · f(y₀)³)`.

Cycle 269 / Phase E.1 (T6, the depth-2 tree `f'(f'''(f,f,f))`).
Coefficients: `r = 5`, `σ = 6` (one-child rule: `σ(mk [t]) = σ(t)`,
with `σ(bushy) = 3! · σ(v)³ = 6`), `γ = 20`, so
`h^r / (σ·γ) = h⁵ / 120`. -/
theorem bseriesExactTerm_mkBushy_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h (mk [bushy])
      = h^5 / 120 * (deriv (deriv (deriv f)) y₀ * deriv f y₀ * (f y₀) ^ 3) := by
  unfold bseriesExactTerm
  rw [show order (mk [bushy]) = 5 from rfl,
      show symmetry (mk [bushy]) = 6 from rfl,
      show density (mk [bushy]) = 20 from rfl]
  have hED : elementaryDiff f y₀ (mk [bushy])
      = deriv (deriv (deriv f)) y₀ * deriv f y₀ * (f y₀) ^ 3 := by
    have hED_v : elementaryDiff f y₀ vertex = f y₀ := by
      show elementaryDiff f y₀ (mk []) = f y₀
      unfold elementaryDiff
      exact iteratedFDeriv_zero_apply _
    have hED_bushy : elementaryDiff f y₀ bushy
        = deriv (deriv (deriv f)) y₀ * (f y₀) ^ 3 := by
      show elementaryDiff f y₀ (mk [vertex, vertex, vertex]) = _
      unfold elementaryDiff
      show iteratedFDeriv ℝ 3 f y₀
              (fun i : Fin 3 => elementaryDiff f y₀
                ([(vertex : RootedTree), vertex, vertex].get i))
            = deriv (deriv (deriv f)) y₀ * (f y₀) ^ 3
      rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
          Fin.prod_univ_three,
          show ([(vertex : RootedTree), vertex, vertex] : List RootedTree).get
                (0 : Fin 3) = vertex from rfl,
          show ([(vertex : RootedTree), vertex, vertex] : List RootedTree).get
                (1 : Fin 3) = vertex from rfl,
          show ([(vertex : RootedTree), vertex, vertex] : List RootedTree).get
                (2 : Fin 3) = vertex from rfl,
          hED_v,
          show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
          show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
      ring
    unfold elementaryDiff
    show iteratedFDeriv ℝ 1 f y₀
            (fun i : Fin 1 => elementaryDiff f y₀ ([bushy].get i))
          = deriv (deriv (deriv f)) y₀ * deriv f y₀ * (f y₀) ^ 3
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
        Fin.prod_univ_one,
        show ([bushy] : List RootedTree).get (0 : Fin 1) = bushy from rfl,
        hED_bushy, iteratedDeriv_one]
    ring
  rw [hED, smul_eq_mul]
  push_cast
  ring

/-- **Scalar closed form at `mk [mk [broom₃]]`.** For `f : ℝ → ℝ`,
the exact-solution B-series term at the order-5 tree `mk [mk [broom₃]]`
is `h⁵/120 · (f''(y₀) · (f'(y₀))² · f(y₀)²)`.

Cycle 269 / Phase E.1 (T8, the depth-3 tree `f'(f'(f''(f,f)))`).
Coefficients: `r = 5`, `σ = 2` (σ-recursion through TWO one-child
wrappers: `σ(mk [mk [broom₃]]) = σ(mk [broom₃]) = σ(broom₃) = 2`),
`γ = 60`, so `h^r / (σ·γ) = h⁵ / 120`. -/
theorem bseriesExactTerm_mkMkBroom₃_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h (mk [mk [broom₃]])
      = h^5 / 120 *
          (deriv (deriv f) y₀ * (deriv f y₀) ^ 2 * (f y₀) ^ 2) := by
  unfold bseriesExactTerm
  rw [show order (mk [mk [broom₃]]) = 5 from rfl,
      show symmetry (mk [mk [broom₃]]) = 2 from rfl,
      show density (mk [mk [broom₃]]) = 60 from rfl]
  have hED : elementaryDiff f y₀ (mk [mk [broom₃]])
      = deriv (deriv f) y₀ * (deriv f y₀) ^ 2 * (f y₀) ^ 2 := by
    have hED_v : elementaryDiff f y₀ vertex = f y₀ := by
      show elementaryDiff f y₀ (mk []) = f y₀
      unfold elementaryDiff
      exact iteratedFDeriv_zero_apply _
    have hED_broom : elementaryDiff f y₀ broom₃
        = deriv (deriv f) y₀ * (f y₀) ^ 2 := by
      show elementaryDiff f y₀ (mk [vertex, vertex]) = _
      unfold elementaryDiff
      show iteratedFDeriv ℝ 2 f y₀
              (fun i : Fin 2 => elementaryDiff f y₀
                ([(vertex : RootedTree), vertex].get i))
            = deriv (deriv f) y₀ * (f y₀) ^ 2
      rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
          Fin.prod_univ_two,
          show ([(vertex : RootedTree), vertex] : List RootedTree).get
                (0 : Fin 2) = vertex from rfl,
          show ([(vertex : RootedTree), vertex] : List RootedTree).get
                (1 : Fin 2) = vertex from rfl,
          hED_v,
          show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
      ring
    have hED_mkBroom : elementaryDiff f y₀ (mk [broom₃])
        = deriv f y₀ * deriv (deriv f) y₀ * (f y₀) ^ 2 := by
      unfold elementaryDiff
      show iteratedFDeriv ℝ 1 f y₀
              (fun i : Fin 1 => elementaryDiff f y₀ ([broom₃].get i))
            = deriv f y₀ * deriv (deriv f) y₀ * (f y₀) ^ 2
      rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
          Fin.prod_univ_one,
          show ([broom₃] : List RootedTree).get (0 : Fin 1) = broom₃ from rfl,
          hED_broom, iteratedDeriv_one]
      ring
    unfold elementaryDiff
    show iteratedFDeriv ℝ 1 f y₀
            (fun i : Fin 1 => elementaryDiff f y₀ ([mk [broom₃]].get i))
          = deriv (deriv f) y₀ * (deriv f y₀) ^ 2 * (f y₀) ^ 2
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
        Fin.prod_univ_one,
        show ([mk [broom₃]] : List RootedTree).get (0 : Fin 1)
          = mk [broom₃] from rfl,
        hED_mkBroom, iteratedDeriv_one]
    ring
  rw [hED, smul_eq_mul]
  push_cast
  ring

/-- **Scalar closed form at `mk [mk [vertex, cherry]]`.** For
`f : ℝ → ℝ`, the exact-solution B-series term at the order-5 tree
`mk [mk [vertex, cherry]]` is `h⁵/40 · (f''(y₀) · (f'(y₀))² · f(y₀)²)`.

Cycle 269 / Phase E.1 (T7, the depth-3 tree `f'(f'(f,f'·f))`).
Coefficients: `r = 5`, `σ = 1` (one-child wraps an asymmetric
order-4 tree with `σ = 1`), `γ = 40`, so `h^r / (σ·γ) = h⁵ / 40`. -/
theorem bseriesExactTerm_mkMkVertexCherry_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h (mk [mk [vertex, cherry]])
      = h^5 / 40 *
          (deriv (deriv f) y₀ * (deriv f y₀) ^ 2 * (f y₀) ^ 2) := by
  unfold bseriesExactTerm
  rw [show order (mk [mk [vertex, cherry]]) = 5 from rfl,
      show symmetry (mk [mk [vertex, cherry]]) = 1 from rfl,
      show density (mk [mk [vertex, cherry]]) = 40 from rfl]
  have hED : elementaryDiff f y₀ (mk [mk [vertex, cherry]])
      = deriv (deriv f) y₀ * (deriv f y₀) ^ 2 * (f y₀) ^ 2 := by
    have hED_v : elementaryDiff f y₀ vertex = f y₀ := by
      show elementaryDiff f y₀ (mk []) = f y₀
      unfold elementaryDiff
      exact iteratedFDeriv_zero_apply _
    have hED_cherry : elementaryDiff f y₀ cherry = deriv f y₀ * f y₀ := by
      show elementaryDiff f y₀ (mk [vertex]) = deriv f y₀ * f y₀
      unfold elementaryDiff
      show iteratedFDeriv ℝ 1 f y₀
              (fun i : Fin 1 => elementaryDiff f y₀
                ([(vertex : RootedTree)].get i))
            = deriv f y₀ * f y₀
      rw [iteratedFDeriv_one_apply, fderiv_eq_smul_deriv,
          show [(vertex : RootedTree)].get (0 : Fin 1) = vertex from rfl, hED_v,
          smul_eq_mul]
      ring
    have hED_mkVCherry : elementaryDiff f y₀ (mk [vertex, cherry])
        = deriv (deriv f) y₀ * deriv f y₀ * (f y₀) ^ 2 := by
      unfold elementaryDiff
      show iteratedFDeriv ℝ 2 f y₀
              (fun i : Fin 2 => elementaryDiff f y₀
                ([(vertex : RootedTree), cherry].get i))
            = deriv (deriv f) y₀ * deriv f y₀ * (f y₀) ^ 2
      rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
          Fin.prod_univ_two,
          show ([(vertex : RootedTree), cherry] : List RootedTree).get
                (0 : Fin 2) = vertex from rfl,
          show ([(vertex : RootedTree), cherry] : List RootedTree).get
                (1 : Fin 2) = cherry from rfl,
          hED_v, hED_cherry,
          show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
      ring
    unfold elementaryDiff
    show iteratedFDeriv ℝ 1 f y₀
            (fun i : Fin 1 => elementaryDiff f y₀
              ([mk [vertex, cherry]].get i))
          = deriv (deriv f) y₀ * (deriv f y₀) ^ 2 * (f y₀) ^ 2
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
        Fin.prod_univ_one,
        show ([mk [vertex, cherry]] : List RootedTree).get (0 : Fin 1)
          = mk [vertex, cherry] from rfl,
        hED_mkVCherry, iteratedDeriv_one]
    ring
  rw [hED, smul_eq_mul]
  push_cast
  ring

/-- **Scalar closed form at `mk [vertex, vertex, cherry]`.** For
`f : ℝ → ℝ`, the exact-solution B-series term at the order-5 tree
`mk [vertex, vertex, cherry]` is `h⁵/20 · (f'''(y₀) · f'(y₀) · f(y₀)³)`.

Cycle 269 / Phase E.1 (T2, Butcher Table 310(II) row r=5).
Coefficients: `r = 5`, `σ = 2` (`2!·σ(v)²·1!·σ(cherry)¹ = 2`),
`γ = 10`, so `h^r / (σ·γ) = h⁵ / 20`. -/
theorem bseriesExactTerm_mkVertexVertexCherry_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h (mk [vertex, vertex, cherry])
      = h^5 / 20 *
          (deriv (deriv (deriv f)) y₀ * deriv f y₀ * (f y₀) ^ 3) := by
  unfold bseriesExactTerm
  rw [show order (mk [vertex, vertex, cherry]) = 5 from rfl,
      show symmetry (mk [vertex, vertex, cherry]) = 2 from rfl,
      show density (mk [vertex, vertex, cherry]) = 10 from rfl]
  have hED : elementaryDiff f y₀ (mk [vertex, vertex, cherry])
      = deriv (deriv (deriv f)) y₀ * deriv f y₀ * (f y₀) ^ 3 := by
    have hED_v : elementaryDiff f y₀ vertex = f y₀ := by
      show elementaryDiff f y₀ (mk []) = f y₀
      unfold elementaryDiff
      exact iteratedFDeriv_zero_apply _
    have hED_cherry : elementaryDiff f y₀ cherry = deriv f y₀ * f y₀ := by
      show elementaryDiff f y₀ (mk [vertex]) = deriv f y₀ * f y₀
      unfold elementaryDiff
      show iteratedFDeriv ℝ 1 f y₀
              (fun i : Fin 1 => elementaryDiff f y₀
                ([(vertex : RootedTree)].get i))
            = deriv f y₀ * f y₀
      rw [iteratedFDeriv_one_apply, fderiv_eq_smul_deriv,
          show [(vertex : RootedTree)].get (0 : Fin 1) = vertex from rfl, hED_v,
          smul_eq_mul]
      ring
    unfold elementaryDiff
    show iteratedFDeriv ℝ 3 f y₀
            (fun i : Fin 3 => elementaryDiff f y₀
              ([(vertex : RootedTree), vertex, cherry].get i))
          = deriv (deriv (deriv f)) y₀ * deriv f y₀ * (f y₀) ^ 3
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
        Fin.prod_univ_three,
        show ([(vertex : RootedTree), vertex, cherry] : List RootedTree).get
              (0 : Fin 3) = vertex from rfl,
        show ([(vertex : RootedTree), vertex, cherry] : List RootedTree).get
              (1 : Fin 3) = vertex from rfl,
        show ([(vertex : RootedTree), vertex, cherry] : List RootedTree).get
              (2 : Fin 3) = cherry from rfl,
        hED_v, hED_cherry,
        show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
        show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    ring
  rw [hED, smul_eq_mul]
  push_cast
  ring

/-- **Scalar closed form at `mk [vertex, mk [cherry]]`.** For
`f : ℝ → ℝ`, the exact-solution B-series term at the order-5 tree
`mk [vertex, mk [cherry]]` is `h⁵/30 · (f''(y₀) · (f'(y₀))² · f(y₀)²)`.

Cycle 269 / Phase E.1 (T4, Butcher Table 310(II) row r=5).
Coefficients: `r = 5`, `σ = 1` (multi-distinct children:
`1!·σ(v)·1!·σ(mk [cherry]) = 1`), `γ = 30`, so
`h^r / (σ·γ) = h⁵ / 30`. -/
theorem bseriesExactTerm_mkVertexMkCherry_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h (mk [vertex, mk [cherry]])
      = h^5 / 30 *
          (deriv (deriv f) y₀ * (deriv f y₀) ^ 2 * (f y₀) ^ 2) := by
  unfold bseriesExactTerm
  rw [show order (mk [vertex, mk [cherry]]) = 5 from rfl,
      show symmetry (mk [vertex, mk [cherry]]) = 1 from rfl,
      show density (mk [vertex, mk [cherry]]) = 30 from rfl]
  have hED : elementaryDiff f y₀ (mk [vertex, mk [cherry]])
      = deriv (deriv f) y₀ * (deriv f y₀) ^ 2 * (f y₀) ^ 2 := by
    have hED_v : elementaryDiff f y₀ vertex = f y₀ := by
      show elementaryDiff f y₀ (mk []) = f y₀
      unfold elementaryDiff
      exact iteratedFDeriv_zero_apply _
    have hED_cherry : elementaryDiff f y₀ cherry = deriv f y₀ * f y₀ := by
      show elementaryDiff f y₀ (mk [vertex]) = deriv f y₀ * f y₀
      unfold elementaryDiff
      show iteratedFDeriv ℝ 1 f y₀
              (fun i : Fin 1 => elementaryDiff f y₀
                ([(vertex : RootedTree)].get i))
            = deriv f y₀ * f y₀
      rw [iteratedFDeriv_one_apply, fderiv_eq_smul_deriv,
          show [(vertex : RootedTree)].get (0 : Fin 1) = vertex from rfl, hED_v,
          smul_eq_mul]
      ring
    have hED_mkCherry : elementaryDiff f y₀ (mk [cherry])
        = (deriv f y₀) ^ 2 * f y₀ := by
      unfold elementaryDiff
      show iteratedFDeriv ℝ 1 f y₀
              (fun i : Fin 1 => elementaryDiff f y₀ ([cherry].get i))
            = (deriv f y₀) ^ 2 * f y₀
      rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
          Fin.prod_univ_one,
          show ([cherry] : List RootedTree).get (0 : Fin 1) = cherry from rfl,
          hED_cherry, iteratedDeriv_one]
      ring
    unfold elementaryDiff
    show iteratedFDeriv ℝ 2 f y₀
            (fun i : Fin 2 => elementaryDiff f y₀
              ([(vertex : RootedTree), mk [cherry]].get i))
          = deriv (deriv f) y₀ * (deriv f y₀) ^ 2 * (f y₀) ^ 2
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
        Fin.prod_univ_two,
        show ([(vertex : RootedTree), mk [cherry]] : List RootedTree).get
              (0 : Fin 2) = vertex from rfl,
        show ([(vertex : RootedTree), mk [cherry]] : List RootedTree).get
              (1 : Fin 2) = mk [cherry] from rfl,
        hED_v, hED_mkCherry,
        show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    ring
  rw [hED, smul_eq_mul]
  push_cast
  ring

/-- **Scalar closed form at `mk [cherry, cherry]`.** For `f : ℝ → ℝ`,
the exact-solution B-series term at the order-5 tree `mk [cherry, cherry]`
is `h⁵/40 · (f''(y₀) · (f'(y₀))² · f(y₀)²)`.

Cycle 269 / Phase E.1 (T5, Butcher Table 310(II) row r=5).
Coefficients: `r = 5`, `σ = 2` (`2!·σ(cherry)² = 2`), `γ = 20`, so
`h^r / (σ·γ) = h⁵ / 40`. -/
theorem bseriesExactTerm_mkCherryCherry_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h (mk [cherry, cherry])
      = h^5 / 40 *
          (deriv (deriv f) y₀ * (deriv f y₀) ^ 2 * (f y₀) ^ 2) := by
  unfold bseriesExactTerm
  rw [show order (mk [cherry, cherry]) = 5 from rfl,
      show symmetry (mk [cherry, cherry]) = 2 from rfl,
      show density (mk [cherry, cherry]) = 20 from rfl]
  have hED : elementaryDiff f y₀ (mk [cherry, cherry])
      = deriv (deriv f) y₀ * (deriv f y₀) ^ 2 * (f y₀) ^ 2 := by
    have hED_v : elementaryDiff f y₀ vertex = f y₀ := by
      show elementaryDiff f y₀ (mk []) = f y₀
      unfold elementaryDiff
      exact iteratedFDeriv_zero_apply _
    have hED_cherry : elementaryDiff f y₀ cherry = deriv f y₀ * f y₀ := by
      show elementaryDiff f y₀ (mk [vertex]) = deriv f y₀ * f y₀
      unfold elementaryDiff
      show iteratedFDeriv ℝ 1 f y₀
              (fun i : Fin 1 => elementaryDiff f y₀
                ([(vertex : RootedTree)].get i))
            = deriv f y₀ * f y₀
      rw [iteratedFDeriv_one_apply, fderiv_eq_smul_deriv,
          show [(vertex : RootedTree)].get (0 : Fin 1) = vertex from rfl, hED_v,
          smul_eq_mul]
      ring
    unfold elementaryDiff
    show iteratedFDeriv ℝ 2 f y₀
            (fun i : Fin 2 => elementaryDiff f y₀
              ([cherry, cherry].get i))
          = deriv (deriv f) y₀ * (deriv f y₀) ^ 2 * (f y₀) ^ 2
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
        Fin.prod_univ_two,
        show ([cherry, cherry] : List RootedTree).get
              (0 : Fin 2) = cherry from rfl,
        show ([cherry, cherry] : List RootedTree).get
              (1 : Fin 2) = cherry from rfl,
        hED_cherry,
        show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    ring
  rw [hED, smul_eq_mul]
  push_cast
  ring

/-- Exact-solution B-series, partial-sum form: the §312 exact-solution
B-series truncated to a hand-supplied `Finset RootedTree`. Differs
from cycle 256's `bseriesAlphaPartialSum` by the `1/γ(t)` factor in
each summand. -/
noncomputable def bseriesExactPartialSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) (S : Finset RootedTree) : E :=
  ∑ t ∈ S, bseriesExactTerm f y₀ h t

@[simp]
theorem bseriesExactPartialSum_empty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) :
    bseriesExactPartialSum f y₀ h ∅ = 0 := by
  simp [bseriesExactPartialSum]

theorem bseriesExactPartialSum_insert
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) {t : RootedTree} {S : Finset RootedTree}
    (ht : t ∉ S) :
    bseriesExactPartialSum f y₀ h (insert t S) =
      bseriesExactTerm f y₀ h t + bseriesExactPartialSum f y₀ h S := by
  simp [bseriesExactPartialSum, Finset.sum_insert ht]

/-- Singleton case: the exact-solution B-series partial sum over `{t}`
collapses to the bare summand `bseriesExactTerm f y₀ h t`. -/
theorem bseriesExactPartialSum_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) (t : RootedTree) :
    bseriesExactPartialSum f y₀ h {t} = bseriesExactTerm f y₀ h t := by
  simp [bseriesExactPartialSum]

/-- Disjoint-union additivity: the exact-solution B-series partial sum
over `S₁ ∪ S₂` decomposes additively whenever `S₁` and `S₂` are
disjoint. -/
theorem bseriesExactPartialSum_union
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) {S₁ S₂ : Finset RootedTree}
    (hDisj : Disjoint S₁ S₂) :
    bseriesExactPartialSum f y₀ h (S₁ ∪ S₂) =
      bseriesExactPartialSum f y₀ h S₁ + bseriesExactPartialSum f y₀ h S₂ := by
  simp [bseriesExactPartialSum, Finset.sum_union hDisj]

-- §312 exact-solution B-series partial sum non-vacuity witnesses (cycle 266).

example (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactPartialSum f y₀ h {vertex} = h • f y₀ := by
  rw [bseriesExactPartialSum_singleton, bseriesExactTerm_vertex]

example (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactPartialSum f y₀ h {vertex, cherry} =
      h • f y₀ + h^2 / 2 * (deriv f y₀ * f y₀) := by
  have hcv : (vertex : RootedTree) ∉ ({cherry} : Finset RootedTree) := by
    simp [Finset.mem_singleton, vertex, cherry]
  rw [show ({vertex, cherry} : Finset RootedTree) =
        insert vertex {cherry} from rfl,
      bseriesExactPartialSum_insert _ _ _ hcv,
      bseriesExactPartialSum_singleton, bseriesExactTerm_vertex,
      bseriesExactTerm_cherry_scalar]

example (y₀ h : ℝ) :
    bseriesExactPartialSum (id : ℝ → ℝ) y₀ h
        ({vertex} : Finset RootedTree)
      = h • y₀ := by
  rw [bseriesExactPartialSum_singleton, bseriesExactTerm_vertex]; rfl

-- Cycle 269 non-vacuity: trivial-ODE exact-solution B-series term at the
-- order-5 chain `mk [mk [mk [cherry]]]` collapses to zero. Exercises
-- `bseriesExactTerm_mkMkMkCherry_scalar` end-to-end on `f := 0`.
example (y₀ h : ℝ) :
    bseriesExactTerm (fun _ : ℝ => (0 : ℝ)) y₀ h (mk [mk [mk [cherry]]])
      = 0 := by
  rw [bseriesExactTerm_mkMkMkCherry_scalar]
  simp

end RootedTree

end OpenMath.Chapter3.Section310
