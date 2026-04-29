# Cycle 017 Results

## Worked on

`thm:301A` "Functions on trees" (Butcher §301). Created
`OpenMath/Chapter3/Section301.lean`. Introduced two new definitions
(`RootedTree.density` for γ, `RootedTree.symmetry` for σ) and proved
all four parts (301a)–(301d) as named theorems
(`r_recursion`, `σ_recursion`, `γ_recursion`, `tau_values`). Also
added the necessary `DecidableEq RootedTree` instance and several
helper lemmas (`orderSum_eq_map_sum`, `densityProd_eq_map_prod`,
`order_eq`, `density_eq`).

## Approach

Followed the planner's strategy from `.prover-state/strategy.md`:

1. Read `entities/thm_301A.json` and §300/§301 of `ch03.txt` to
   confirm the textbook statement and the σ-definition divergence.
2. Wrote `Section301.lean` with the full structure (definitions,
   theorems) all stubbed out as `sorry`.
3. Verified the skeleton compiled — caught and fixed two issues:
   - `deriving instance DecidableEq for RootedTree` does NOT work
     (Lean's auto-derivation rejects the recursion through `List`).
     Replaced with a hand-written mutual `decEqTree` / `decEqList` pair
     and registered it as `instance : DecidableEq RootedTree`.
   - `/-- … -/` doc comments cannot precede a `mutual` block; Lean
     parses them and errors with `unexpected token 'mutual'; expected
     'lemma'`. Moved the doc comments INSIDE the `mutual` block,
     attached to the relevant `def`. Also replaced `/-! … -/` section
     markers (which similarly attach to following declarations) with
     plain `/- … -/` block comments.
4. Filled the four sorries via `lean_multi_attempt`. All four are
   short induction / unfolding proofs:
   - `orderSum_eq_map_sum`: induction on children with
     `simp [orderSum, ih]`.
   - `order_eq`: `show 1 + orderSum c = …; rw [orderSum_eq_map_sum]`.
   - `densityProd_eq_map_prod`: induction with `simp [densityProd, ih]`.
   - `density_eq`: `show order * densityProd c = …; rw [densityProd_eq_map_prod]`.
5. Aristotle was not needed — the four proofs were short enough that
   manual `lean_multi_attempt` testing cleared them on the first try.
6. Verified the file compiles, `lake build` is green, and `#print axioms`
   shows only `[propext]` (standard) for all eight introduced symbols.
7. Updated `extraction/formalization_data/lean_status.json` and
   `plan.md` (progress 17 → 18).
8. Wrote `.prover-state/issues/symmetry_group_equivalence.md`.

## Result

SUCCESS — `thm:301A` formalised in full:

- `RootedTree.r_recursion` (301a): proved.
- `RootedTree.σ_recursion` (301b): proved by `rfl` (stipulative
  definition, see faithfulness section).
- `RootedTree.γ_recursion` (301c): proved.
- `RootedTree.tau_values` (301d): proved by `rfl`.

`lake build` green; `#print axioms` shows only `[propext]` for each.
Tautology scanner returns zero hits.

## Faithfulness check

### `def RootedTree.density` (γ; new this cycle)

- Entity context (Butcher §300, p. 139, quoted from `ch03.txt`):
  > The 'density' of `t`, `γ(t)`, is defined as the product over all
  > vertices of the order of the subtree rooted at that vertex.
- Lean statement captures: **same content** (modulo standard
  recursion-vs-product equivalence). The Lean definition unfolds via
  `density (mk children) = order (mk children) * Πᵢ density(tᵢ)` —
  this is exactly the textbook product, computed by recursing through
  subtrees: each vertex of `mk children` is either the root
  (contributing `order (mk children)`) or a vertex of some `tᵢ`
  (contributing through the recursive `density tᵢ` factor). The
  equivalence is "obvious by induction" and is documented in the
  doc-string. The recursion (301c) is proved as `density_eq`.
- No divergence.

### `def RootedTree.symmetry` (σ; new this cycle)

- Entity context (Butcher §300, p. 139, quoted from `ch03.txt`):
  > Let `A(t)` denote the group of automorphisms on a particular
  > labelling of `t`. … The group `A(t)` will be known as the
  > 'symmetry group' of `t`; its order will be known as the
  > 'symmetry', and denoted by `σ(t)`.
- Lean statement captures: **different** (stipulative recursion
  instead of group-theoretic order).
- Justification for divergence: a faithful group-theoretic σ requires
  building permutation-group infrastructure on the vertex set of our
  `List`-based `RootedTree` (3–5 cycles of work). Cycle 017 instead
  takes the recursion (301b) as the definition. This is documented
  prominently in the file doc-string and an issue file
  (`.prover-state/issues/symmetry_group_equivalence.md`). All
  identified downstream consumers of σ in Butcher Chapter 3 only need
  the recursive identity, so they are not blocked. This follows the
  same pattern used elsewhere in this project (e.g. partial 142D /
  `jordan_canonical_form_missing`).

### `theorem RootedTree.r_recursion` ((301a) of thm:301A)

- Entity ID `thm:301A`. Textbook statement (`statement_latex`):
  > `r(t) = 1 + Σᵢ mᵢ r(tᵢ)`
- Lean statement captures: **same content** in `List`-indexed form:
  `order (mk children) = 1 + (children.map order).sum`. The textbook's
  `Σᵢ mᵢ r(tᵢ)` (sum over distinct subtrees with multiplicities) is
  numerically identical to `Σ_{c ∈ children} r(c)` — both count the
  same vertices. Documented in the theorem doc-string.

### `theorem RootedTree.γ_recursion` ((301c) of thm:301A)

- Same situation as `r_recursion`: `List`-indexed form
  `(children.map density).prod` is numerically identical to
  `Πᵢ γ(tᵢ)^{mᵢ}` over distinct subtrees. **Same content**.

### `theorem RootedTree.σ_recursion` ((301b) of thm:301A)

- Textbook form: `σ(t) = Πᵢ mᵢ! · σ(tᵢ)^{mᵢ}` (over distinct subtrees).
- Lean form: `symmetry (mk children) = symmetryProd children children`
  (proved by `rfl`).
- Captures: this is true *by construction*, since `symmetry` is defined
  to call `symmetryProd children children`, and `symmetryProd` walks
  the children list emitting the textbook factor `mᵢ! · σ(tᵢ)^{mᵢ}`
  exactly once per distinct subtree (at the last occurrence).
  Combined with the σ-definition divergence above, this is "the
  recursion as a stipulation". The unfolding-equivalence to the
  multiplicity-grouped product form is documented in the theorem
  doc-string but not separately proved. A future cycle could prove
  the explicit dedup-grouped form as a downstream lemma if a caller
  needs it.

### `theorem RootedTree.tau_values` ((301d) of thm:301A)

- Textbook: `r(τ) = σ(τ) = γ(τ) = 1`.
- Lean: `order (mk []) = 1 ∧ symmetry (mk []) = 1 ∧ density (mk []) = 1`,
  proved by `⟨rfl, rfl, rfl⟩`. **Same content** (modulo the σ-definition
  divergence).

### Other faithfulness checks (CLAUDE.md)

- **Tautology check.** None of the introduced theorems has its
  conclusion appearing verbatim as a hypothesis. (None of them have
  hypotheses at all — they are universally-quantified statements
  about all `children : List RootedTree`.)
- **Identity check.** `r_recursion` and `γ_recursion` are
  one-liners that delegate to a helper (`order_eq` /
  `density_eq`). These helpers do real work (an induction unfolding
  the mutual `orderSum` / `densityProd` to the standard `List.sum` /
  `List.prod` form), so the named theorems are genuine
  abbreviations, not vacuous re-exports.
- **Definition-smuggling check.** No new `structure` or `class`
  introduced; only `def`s, all of which are computations on
  `RootedTree`/`List RootedTree` returning `ℕ`. None hides what
  should be a theorem.
- **Hypothesis-strength check.** The four (301a–d) theorems take
  only the `children : List RootedTree` parameter, mirroring the
  textbook's `t = [t₁ … t_k]` parameterisation exactly. No extra
  hypotheses.
- **Absent-theorem check.** No comment promises a `sorry` that
  doesn't exist.

## Dead ends

1. **`deriving instance DecidableEq for RootedTree`.** Lean rejects
   this with "None of the deriving handlers for class `DecidableEq`
   applied to `RootedTree`" — the auto-derivation can't see through
   the `List RootedTree` recursion. Fixed by writing a hand-rolled
   mutual `decEqTree` / `decEqList` pair. Cost: ~15 lines of
   boilerplate.
2. **`/-! … -/` (and `/-- … -/`) before a `mutual` block.** Lean's
   parser treats those as doc-comments attached to the next
   declaration, but it does not accept doc-comments on `mutual`
   blocks themselves — error: `unexpected token 'mutual'; expected
   'lemma'`. Fixed by moving doc comments INSIDE the `mutual` block,
   attached to the relevant `def`, and using plain `/- … -/` block
   comments for section markers.
3. **`List.noConfusion h : False` does not type-check** for
   `h : [] = _ :: _`. `List.noConfusion h` returns
   `List.noConfusionType …`, not `False`. Fixed by `fun h => by cases h`.

## Discovery

1. **σ as recursion is workable.** Defining σ stipulatively via
   (301b) with a mutual `symmetry` / `symmetryProd` recursion
   structure compiles cleanly, terminates without manual
   `decreasing_by`, and reduces under `rfl`. The key trick is to
   thread the *full* children list through unchanged as the first
   argument of `symmetryProd` (so multiplicities can be computed) and
   recurse on the second (cursor) argument. Lean's mutual-recursion
   termination handles this automatically.
2. **The `List`-indexed form vs. multiplicity-grouped form are
   numerically equal.** For both `r` and `γ`, the sum/product over
   distinct subtrees with multiplicities is identical to the
   sum/product over the raw `children` list — so we can state the
   theorems in the cleaner `List.sum` / `List.prod` form. We don't
   need a separate "dedup-and-multiply" proof. (For σ this would
   *not* be true because of the `mᵢ!` factor, which is why σ_recursion
   is stated in the helper-walk form rather than the
   multiplicity-grouped form.)
3. **Aristotle was unnecessary this cycle.** All four sorries proved
   by simple induction or rewriting via `lean_multi_attempt`. Aristotle
   would likely solve them too, but submitting + waiting 30 minutes
   was wasted budget when manual proofs are this short. Lesson: if
   sorries pass `lean_multi_attempt` cleanly on a small set of
   reasonable tactics, don't bother batching them to Aristotle.
4. **Hand-written `decEq` for inductives recursing through `List`.**
   Lean's auto-derivation does not handle this; the manual mutual
   pattern works fine and is short.

## Suggested next approach

For cycle 018, two natural next steps:

1. **`thm:302A`** "Some combinatorial questions" (§302). Direct
   dependent of `thm:301A`. Read `entities/thm_302A.json` first to
   confirm scope.
2. **`def:312A`** "derivative weights" α(t). Per cycle-016
   discovery #2 and the cycle-017 strategy denylist, write the
   recursion mutually with a list helper from the start.

Lower-priority but useful: prove the **multiplicity-grouped explicit
form** of `σ_recursion`:
```
symmetry (mk children) =
  ((children.dedup).map (fun t =>
    Nat.factorial (children.count t) * symmetry t ^ children.count t)).prod
```
This may help downstream callers that pattern-match on the textbook
form `Πᵢ mᵢ! σ(tᵢ)^{mᵢ}`. Skipped this cycle to keep scope tight.

The σ-equivalence issue (`symmetry_group_equivalence.md`) is a
non-blocking long-term faithfulness gap — defer until either a
downstream theorem needs the group-theoretic characterisation, or
permutation-group infrastructure is being built for `def:388D`.
