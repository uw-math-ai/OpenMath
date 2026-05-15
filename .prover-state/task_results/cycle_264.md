# Cycle 264 Results

## Worked on
§300 Phase A.2 heterogeneous-labelling non-vacuity (Option 1 from cycle 263
task results / consultant-advice-cycle-263 §C Option 1). Goal:
demonstrate cycle 263's weakened `LabelledRootedTree.setoid` is
non-trivial by exhibiting two genuinely-distinct labellings of the
two-leaf tree `mk [vertex, vertex]` that are Setoid-identified under the
leaf-swap permutation.

## Approach
Follow the planner's verbatim consultant-verified recipe C.1–C.6:
1. Define `doubleVertex := mk [vertex, vertex]` and `leftLeaf` /
   `rightLeaf : Vertex doubleVertex` via the `Vertex.child` constructor
   with explicit `Fin 2` indices.
2. Prove three distinctness lemmas via `intro h; cases h` (memory
   `feedback_indexed_inductive_cases_disjoint.md`).
3. Define `leafSwapAutomorphism : TreeAutomorphism doubleVertex` using
   `Equiv.swap leftLeaf rightLeaf` and `Equiv.swap_apply_of_ne_of_ne` for
   root-fixing.
4. Define `canonicalDoubleVertex` and `swappedDoubleVertex` (canonical
   labelling vs canonical post-composed with the swap permutation).
5. Prove `canonical_equiv_swapped` via the leaf-swap automorphism witness
   plus `simp [Equiv.trans_apply, Equiv.swap_apply_self]`.
6. Prove `labellings_distinct` via injectivity of
   `canonicalLabelling doubleVertex` applied to `leftLeaf ≠ rightLeaf`.
7. Ship a bottom-line `example` exhibiting both.

## Result
SUCCESS — all of C.1–C.6 shipped. Final file
`OpenMath/Chapter3/Section300.lean` compiles axiom-clean. Sorry count
remains 0. `lean_verify` on `labellings_distinct` and
`canonical_equiv_swapped` reports the standard
`[propext, Classical.choice, Quot.sound]` axiom set. Tautology scanner
regex yields zero hits.

Three planner-template deviations from the verbatim recipe:

1. **`leafSwapAutomorphism` must be `noncomputable`**. `Equiv.swap`
   requires `DecidableEq`, and the project's `instDecidableEqVertex` is
   `Classical.decEq`-based (`noncomputable`). Lean's compiler raised
   "consider marking it as 'noncomputable'" — added the keyword.

2. **`labellings_distinct`'s `have heval := by rw [h]` left an
   unsolved-rfl goal**. After `rw [h]`, the goal reduced to
   `swappedDoubleVertex.labelling leftLeaf = swappedDoubleVertex.labelling leftLeaf`,
   syntactically `rfl`-closeable but Lean's `rw` did not auto-close —
   likely `Eq.mpr`/dependent-typing plumbing on `Equiv` application.
   Switched to a direct congruence:
   `congrArg (fun e : Vertex doubleVertex ≃ Fin (order doubleVertex) => e leftLeaf) h`.
   Subsequent `simpa` chain on `Equiv.trans_apply, Equiv.swap_apply_left`
   closed the proof unchanged.

3. **Bottom-line `example` reshaped from existential to conjunction on
   named witnesses**. The planner's
   `∃ a b, a.labelling ≠ b.labelling ∧ Equiv a b` does not type-check:
   `a.labelling ≠ b.labelling` is heterogeneously typed
   (`Vertex a.underlying ≃ ...` vs `Vertex b.underlying ≃ ...`) when
   `a.underlying` and `b.underlying` are not unified. Replaced with
   `Equiv canonicalDoubleVertex swappedDoubleVertex ∧
   canonicalDoubleVertex.labelling ≠ swappedDoubleVertex.labelling`
   where both `.underlying` reduce to `doubleVertex` and the `≠` is
   well-typed.

## Faithfulness check
For each new `def` or `theorem` introduced this cycle:

- `RootedTree.doubleVertex : RootedTree := mk [vertex, vertex]`
  — engineering scaffold (def-equal to `RootedTree.broom₃`). The alias
    clarifies the role of vertex naming in the leaf-swap construction.
    Not a textbook entity ID. Same content as `broom₃`.

- `RootedTree.leftLeaf` / `rightLeaf : Vertex doubleVertex`
  — engineering scaffolds. Not textbook entities. Both are leaf vertices
    of `mk [vertex, vertex]`; distinct by definition of `Vertex.child`
    at different `Fin 2` indices.

- `leftLeaf_ne_rightLeaf` / `leftLeaf_ne_root` / `rightLeaf_ne_root`
  — engineering scaffolds. Trivial constructor distinctness on an
    indexed inductive.

- `leafSwapAutomorphism : TreeAutomorphism doubleVertex`
  — engineering scaffold. Satisfies the cycle 263 weakened
    `TreeAutomorphism` (perm + root-fixing). NOT a Butcher full
    tree-automorphism (does not enforce recursive child-subtree
    structure preservation). The leaf-swap of a two-leaf tree IS a full
    Butcher tree-automorphism in this case (the two children are
    isomorphic), so the witness coincides with what Butcher's stronger
    definition would also admit. Faithfulness check on the weakened
    `TreeAutomorphism` definition itself is unchanged from cycle 263.

- `canonicalDoubleVertex` / `swappedDoubleVertex : LabelledRootedTree`
  — engineering scaffolds. Concrete inhabitants of the cycle 262
    `LabelledRootedTree` structure.

- `canonical_equiv_swapped` — engineering theorem witnessing
  non-vacuity of `LabelledRootedTree.Equiv` on heterogeneous (non-equal)
  labellings. Confirms the cycle 263 Setoid genuinely identifies
  distinct labellings.

- `labellings_distinct` — engineering theorem witnessing that the
  Setoid is not the discrete `Eq` setoid.

- Bottom-line `example` — engineering witness. Lean statement captures
  the consultant-advice-cycle-263 §C Option 1 deliverable
  (reshaped from existential to conjunction on named witnesses; see
  Result §3 above).

**Faithfulness verdict**: No new textbook entity claims. All new
definitions are engineering scaffolds validating cycle 263's
infrastructure. No definition smuggling: `labellings_distinct` proves
function-inequality of two `Equiv`s, NOT a textbook claim about
σ-faithfulness orbit counts. No tautologies: every theorem does real
work (each closes via constructor-disjoint cases, injectivity, or
congruence — not via identity re-export).

## Dead ends

1. **`have heval := by rw [h]` failed despite reducing to a `rfl` goal**.
   See Result §2 above. The fix (`congrArg`) is robust and easier to
   reason about, but the underlying `rw` failure is surprising. Possible
   future investigation: characterize when `rw` on a `FunLike` /
   `CoeFun`-coerced equality fails to auto-close `rfl`.

2. **Existential statement of `a.labelling ≠ b.labelling` doesn't
   type-check**. See Result §3 above. The fix (named-witness
   conjunction) is unambiguously correct and arguably stronger as a
   demonstration (no existential unpacking required).

## Discovery

- **`rw` on `Equiv`-typed equalities can leave a syntactic-`rfl` goal
  unsolved**. Workaround: `congrArg (fun e => e v) h` where `e` is the
  function being applied. Worth adding to memory if it recurs.

- **`Equiv.swap_apply_of_ne_of_ne` takes `x ≠ a → x ≠ b → swap a b x = x`,
  not `a ≠ x → b ≠ x → ...`**. The `h.symm` calls in the
  `leafSwapAutomorphism.perm_root` proof are forced by this orientation.
  This is exactly the recipe-verified-at-HEAD direction in consultant
  advice §D, no surprise.

- **Indexed-inductive `cases h` closes on distinct `Vertex.child i _`
  vs `Vertex.root`**. Lean's `cases` tactic on an `Eq` between distinct
  constructors of an indexed inductive successfully derives `False` —
  no need for `Vertex.noConfusion` (memory
  `feedback_indexed_inductive_cases_disjoint.md` was directly applicable).

## Suggested next approach

The planner now has three viable Phase A.2 follow-ups:

1. **Option 2 (multi-cycle)**: Strengthen `TreeAutomorphism` to the full
   recursive structure-preservation predicate. Requires a `mutual` block
   through `List RootedTree` per
   `feedback_rootedtree_nested_induction.md`. Risks the
   cycle 149/200/201 rollback pattern but is the canonical path to
   Butcher's `def:300C` and Phase A.3 σ-faithfulness orbit count.

2. **Option 3 (multi-cycle)**: Phase B (`thm:306A` multivariate Taylor /
   multinomial). Bypassable per `lem_310B_plan.md` §4.2 if Phase D
   routes through multilinear elementary-differentials directly.

3. **Option 4 (single-cycle pivot)**: `lem:342A` or another textbook
   entity not requiring the `RootedTree` infrastructure. Pauses §310
   momentum but ships textbook progress.

Personal lean: Option 2 is the structurally-correct continuation but
high-risk; Option 4 is safe and ships textbook value; Option 3 is the
deepest infrastructure investment. Recommend the planner weigh the §310
roadmap completion against textbook breadth.

A note on the cycle 263 phantom-template invocation (planner §K): cycle
264's "stuck on" field was likewise empty going into this cycle, but the
strategy was concrete and direct — the consultant phase did real
planning work. Worker confirms the strategy was clear and actionable;
no rerouting needed.
