# Issue: σ defined as recursion (301b), not as symmetry-group order

## Blocker

`RootedTree.symmetry` (cycle 017, `OpenMath/Chapter3/Section301.lean`)
is defined directly via the recursive equation (301b) of Theorem 301A,
treated as a stipulative definition. Butcher §300's textual definition
of `σ(t)` is the *order of the automorphism group of `t`* — a
permutation-group-theoretic quantity. The equivalence between the two
characterisations is not formalised this cycle.

## Quoted textbook definition (Butcher §300, p. 139)

> Let `A(t)` denote the group of automorphisms on a particular labelling
> of `t`. That is, `A(t)` is the set of mappings `ϕ : V → V` such that
> `[x,y] ∈ E` if and only if `[ϕ(x), ϕ(y)] ∈ E`. The group `A(t)` will
> be known as the 'symmetry group' of `t`; its order will be known as
> the 'symmetry', and denoted by `σ(t)`.

## Quoted textbook claim (Butcher Theorem 301A, equation (301b))

> Let `t = [t₁^{m₁} t₂^{m₂} … t_k^{m_k}]` be a rooted tree, where
> `t₁, …, t_k` are distinct subtrees with multiplicities `m₁, …, m_k`.
> Then
>
>     σ(t) = Πᵢ mᵢ! · σ(tᵢ)^{mᵢ}.

The mathematical content of (301b) is:

1. Define `σ` as the order of the automorphism group of `t` (the
   group-theoretic definition).
2. Prove that the recursion `σ(mk children) = Πᵢ mᵢ! · σ(tᵢ)^{mᵢ}`
   holds.

Cycle 017 instead **uses the recursion as the definition** and skips
step 2.

## Context (current Lean code)

```lean
-- OpenMath/Chapter3/Section301.lean
mutual
  def symmetry : RootedTree → ℕ
    | mk children => symmetryProd children children
  def symmetryProd : List RootedTree → List RootedTree → ℕ
    | _,    []        => 1
    | full, t :: rest =>
        if t ∈ rest then symmetryProd full rest
        else Nat.factorial (full.count t) * symmetry t ^ full.count t *
              symmetryProd full rest
end
```

By construction, `σ_recursion : symmetry (mk children) =
symmetryProd children children` holds by `rfl`, and unfolding
`symmetryProd` over the children list emits the textbook factor
`mᵢ! · σ(tᵢ)^{mᵢ}` exactly once per distinct subtree (at the *last*
occurrence in the list).

## What was tried

Cycle 017 weighed two formalisations:

- **Group-theoretic σ (faithful).** Define σ via `Fintype.card`/`Nat.card`
  of the automorphism subgroup of `Equiv.Perm (vertices of t)`
  preserving the edge relation. Then prove (301b) by analysing the
  block decomposition of `A(t)` as `(Πᵢ S_{mᵢ}) ⋉ (Πᵢ A(tᵢ)^{mᵢ})`.
  This requires building (a) a Lean model of "vertex set of `t`" for
  our `List`-based `RootedTree`, (b) the edge-preserving permutation
  subgroup, (c) a structural-recursion proof of the block decomposition
  via wreath products. Estimated effort: 3–5 cycles.

- **Stipulative σ via (301b) (this cycle).** Take (301b) as the
  definition. Document the divergence; downstream consumers only need
  the recursion, so they are unblocked.

The latter was chosen for cycle 017 to keep the σ-definition unblocked
for downstream Chapter 3 work.

## Possible solutions

1. **Defer faithfully.** Build the permutation-group infrastructure in a
   future cycle (or as a separate `OpenMath/Chapter3/Section300_Auto.lean`
   helper file). Prove (301b) as a theorem against the
   `RootedTree.symmetry` recursion of this cycle, then expose both as
   equivalent. This is the long-term faithful resolution.

2. **Document and accept (current state).** Keep the recursive
   definition as canonical. Mark this issue as `wontfix-low-priority`
   if no downstream theorem ever genuinely needs the group-theoretic
   characterisation. Most "tree symmetry" reasoning in Butcher's
   Chapter 3 reduces to the recursive identity (301b) anyway.

3. **Hybrid.** Define an opaque `tree_aut_card : RootedTree → ℕ`
   abstractly (without constructing the group) and prove `σ =
   tree_aut_card` only as a `sorry`'d goal in a separate file, so
   downstream code can transparently use either form. This pushes the
   gap into a single named `sorry` rather than a definition mismatch.

## Downstream impact

The transitive `dependents` list of `thm:301A`
(`def:310A`, `def:388D`, `thm:302A`, `thm:372A`, and through them
`lem:310B`, `lem:312B`, `lem:313A`, `thm:317A`, `thm:311D`, …) only
consume the recursive relation (301b) — none requires the
permutation-group characterisation. **No downstream theorem is blocked
by this gap.** This is a faithfulness divergence for our own
bookkeeping, not a logical obstacle.

## Recommendation

Defer (option 1) until either (a) a downstream theorem genuinely needs
the group-theoretic characterisation, or (b) we want to close the
faithfulness gap proactively (likely once permutation-group / `Equiv.Perm`
infrastructure is already needed for another part of Chapter 3,
e.g. `def:388D`). In the meantime the recursive definition is sound,
documented, and unblocks all current work.
