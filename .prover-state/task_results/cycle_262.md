# Cycle 262 Results

## Worked on

Phase A.2 (partial) of `.prover-state/issues/lem_310B_plan.md`. Extended
`OpenMath/Chapter3/Section300.lean` with six new public declarations on top
of cycle 261's `Vertex` / `vertices` / `vertices_card` infrastructure:

1. `Vertex.mem_vertices` — completeness lemma: every `v : Vertex t` is in
   `vertices t`.
2. `instFintypeVertex` — `noncomputable instance Fintype (Vertex t)` from
   `vertices t` + `Vertex.mem_vertices`.
3. `Fintype.card_vertex_eq_order` — `Fintype.card (Vertex t) = order t`,
   reframing of cycle 261's `vertices_card`.
4. `LabelledRootedTree` — structure: `underlying : RootedTree` plus
   `labelling : Vertex underlying ≃ Fin (order underlying)`.
5. `canonicalLabelling` — `noncomputable def` via
   `Fintype.equivFinOfCardEq` applied to `Fintype.card_vertex_eq_order`.
6. `canonicalVertex` / `canonicalCherry` / `canonicalBroom₃` — three
   explicit `LabelledRootedTree` witnesses, plus three `rfl` examples
   confirming `underlying.order = 1, 2, 3` respectively.

Total new LOC: ~93 (file grew from 179 to 272 lines).

## Approach

Followed the strategy's §D step-by-step recipe exactly. No deviations
were necessary.

- §D.1 (`Vertex.mem_vertices`): well-founded recursion using
  `termination_by t _ => t` with the cycle 261 `decreasing_by` pattern
  (`simp_wf` + `Nat.lt_add_left 1 (List.sizeOf_get cs i)`). Pattern-matched
  on `(mk cs, Vertex.root)` and `(mk cs, Vertex.child i v)`. `root` case
  uses `Finset.mem_insert_self`; `child` case uses `Finset.mem_insert_of_mem`
  + `Finset.mem_biUnion` + `Finset.mem_image` and the IH recursive call
  `Vertex.mem_vertices v`.

- §D.2 (`Fintype.card_vertex_eq_order`): the `show (vertices t).card =
  order t` definitional reframing fired immediately — under our explicit
  `Fintype.mk ⟨vertices t, _⟩` instance, `Fintype.card (Vertex t) =
  (Finset.univ : Finset (Vertex t)).card` and `Finset.univ` reduces to
  the chosen `elems` field, i.e. `vertices t`. No fallback to
  `Finset.card_univ` + extensionality was needed.

- §D.3 (`canonicalLabelling`): `Fintype.equivFinOfCardEq` existed under
  the exact strategy-projected name (verified via `lean_loogle` before
  writing). No name-drift fallback was needed.

- §D.4 (three witnesses): all three `LabelledRootedTree`s ship as
  `noncomputable def` with `canonicalLabelling` applied to the small-tree
  constants from `Section310.lean`. The three `example : ….order = n :=
  rfl` checks compile via the existing `order` recursion's `rfl` reduction
  on small constants (cycle 261 used the same pattern in `example :
  (RootedTree.vertices RootedTree.cherry).card = 2`).

## Result

**SUCCESS.** All six target declarations compile axiom-clean.

`lake env lean OpenMath/Chapter3/Section300.lean` exits 0 with no
diagnostics. `lake env lean OpenMath/Chapter3.lean` (aggregator) exits 0.
`lake build OpenMath.Chapter3.Section300` exits 0 (`✔ [1933/1933] Built
OpenMath.Chapter3.Section300 (2.6s)`).

Sorry count in `Section300.lean`: 0 (verified via `grep`). Repo-wide sorry
count: 0 (cycle 261 was 0; this cycle adds none).

`#print axioms` verdict on all new public declarations:

- `Vertex.mem_vertices`: `[propext, Classical.choice, Quot.sound]`
- `instFintypeVertex`: `[propext, Classical.choice, Quot.sound]`
- `Fintype.card_vertex_eq_order`: `[propext, Classical.choice, Quot.sound]`
- `canonicalLabelling`: `[propext, Classical.choice, Quot.sound]`
- `canonicalVertex` / `canonicalCherry` / `canonicalBroom₃`: each
  `[propext, Classical.choice, Quot.sound]`

All axiom-clean (the `Classical.choice` dependency is expected from the
noncomputable `instDecidableEqVertex` instance, the noncomputable
`vertices`, and `Fintype.equivFinOfCardEq`).

Tautology-scanner regex `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$`
returns 0 matches on the new code. No `h_<name>` identifiers were
introduced this cycle (the only fresh local names are `cs`, `i`, `v`
in pattern-match positions).

## Faithfulness check

For each new public declaration introduced this cycle:

### `Vertex.mem_vertices`

- Entity ID: engineering scaffold (no direct Butcher analogue).
- Textbook statement (implicit): every vertex of `t` belongs to the set
  of vertices `V(t)` — Butcher §300 p. 139 treats `V(t)` informally as
  "the points of t".
- Lean statement captures: **same content**. The Finset `vertices t`
  enumerates the underlying `Type` `Vertex t`; this lemma is its
  completeness/`elems_complete` half (the other half — the `Fintype`
  instance — is `instFintypeVertex`).

### `instFintypeVertex`

- Entity ID: engineering scaffold.
- Lean statement captures: **same content** as the implicit Butcher
  claim that `V(t)` is finite (Butcher §300 p. 139 treats `r(t)` as a
  finite count).

### `Fintype.card_vertex_eq_order`

- Entity ID: maps to `lem:310B` Phase A.1's foundational identity (cycle
  261 shipped `vertices_card` at the `Finset` level; this cycle reframes
  for the `Fintype` API).
- Butcher statement (paraphrased from §300 p. 139): `r(t)` is the number
  of vertices of `t`.
- Lean statement captures: **same content** as cycle 261's
  `vertices_card`. Both `Fintype.card (Vertex t)` and `(vertices t).card`
  equal `order t`; the proof reduces to cycle 261's identity via the
  `Fintype.mk` definitional unfolding.

### `LabelledRootedTree`

- Entity ID: `def:300C` (Butcher §300 around p. 140 — labelled rooted
  trees).
- Butcher statement: "a labelled rooted tree is a rooted tree with vertex
  set `V` carrying a bijection `V → {1, 2, …, |V|}`. Two labellings are
  equivalent if they differ by an automorphism of the underlying tree."
- Lean statement captures: **weaker** (raw labelling, not quotient by
  tree-automorphism).
- Justification for divergence: Butcher's `def:300C` is a *quotient*
  type (labellings modulo tree-automorphism). Cycle 262 exposes the raw
  pre-quotient: a `RootedTree` together with one explicit
  `Vertex t ≃ Fin (order t)` bijection. The tree-automorphism `Setoid`
  (and the orbit-count theorem `Nat.card (Quotient …) = r(t)!/σ(t)`)
  is deferred per `.prover-state/issues/lem_310B_plan.md` §4.1 to
  cycle 263+ (Phase A.2 completion) and Phase A.3, respectively. This
  is a structural pre-step — the raw labelling type is itself
  Butcher-faithful as an *intermediate* object; the divergence is
  bookkeeping (no textbook claim is misstated).

### `canonicalLabelling`

- Entity ID: engineering scaffold (Butcher does not single out a
  canonical labelling).
- Lean statement captures: **engineering scaffold**. Provides one
  specific labelling per `RootedTree` for non-vacuity purposes; Butcher
  treats labellings up to automorphism, so the choice of representative
  is structurally invisible at the quotient level. Documented as such
  in the docstring.

### `canonicalVertex` / `canonicalCherry` / `canonicalBroom₃`

- Entity ID: engineering scaffolds (concrete non-vacuity witnesses).
- Lean statement captures: **same content** as the implicit Butcher
  claim that any small rooted tree can be labelled (cycle 261's
  `cherry`, `broom₃` witnesses are recovered with explicit labellings
  here).

No tautology, identity, definition-smuggling, or hypothesis-strength
violations detected by the pre-commit checklist.

## Dead ends

No dead ends this cycle. Each sub-piece (§D.1 through §D.4) closed on
the first attempt:

- §D.1's well-founded recursion did not need the §F.1-mitigation
  mutual-recursion factoring; the direct `termination_by t _ => t` +
  `decreasing_by` pattern works as in cycle 261.
- §D.2's `show (vertices t).card = order t` worked without the §D.2-fallback
  `Finset.univ = vertices t` extensionality argument.
- §D.3's `Fintype.equivFinOfCardEq` existed under the exact name. No
  variant search (`Fintype.equivOfCardEq`, manual `finCongr`-compose,
  `Equiv.ofBijective` fallback) was needed.

The only minor friction was a single unused-variable lint warning on
`termination_by t v => t` (the `v` is unused in the measure). Fixed by
renaming to `termination_by t _ => t` in one line.

Stale-`.olean` confusion: my first `#print axioms` check ran against a
not-yet-rebuilt `.olean`, causing "Unknown constant" errors. Resolved
with `lake build OpenMath.Chapter3.Section300`. Worth remembering:
`lake env lean <file>` rebuilds the file's olean but does *not*
propagate to downstream `import`-consumers; explicit `lake build` is
needed before cross-file axiom checks.

## Discovery

1. **`Fintype.equivFinOfCardEq` lives in `Mathlib.Data.Fintype.EquivFin`**
   (verified via `lean_loogle`). The signature is
   `{α : Type u} [Fintype α] {n : ℕ} (h : Fintype.card α = n) : α ≃ Fin n`.
   No `[DecidableEq α]` requirement — our `instDecidableEqVertex` is
   technically not needed for `canonicalLabelling`, but it's already there
   for `Finset.image` reasons.

2. **`Fintype.mk` + `show` plays nicely for card-reframing**: when an
   `instance : Fintype α` is built via the explicit constructor
   `⟨S, h⟩` with `S : Finset α`, the chain
   `Fintype.card α → (Finset.univ : Finset α).card → S.card` reduces
   definitionally. `show S.card = …` is the cleanest reframing pattern;
   no `Finset.card_univ` rewrite is needed.

3. **`canonicalLabelling` is propagation-friendly for `noncomputable
   def`**: even though `LabelledRootedTree.labelling` is an `Equiv`
   built from `Classical.choice`-using `Fintype.equivFinOfCardEq`, the
   structure constructors (`canonicalVertex` etc.) compose cleanly. The
   alternative `noncomputable abbrev` workaround mentioned in §D.4 was
   not needed.

4. **Cycle 262 ships the raw labelling type; cycle 263 is now well-set
   up for the tree-automorphism `Setoid`.** The next cycle's work will
   define a `LabelledRootedTree.Equiv` relation (or `Setoid` instance)
   based on automorphisms of the underlying `RootedTree`, build a
   `Quotient`, and prove non-vacuity by exhibiting a two-leaf
   automorphism on `mk [vertex, vertex]`. The relevant Mathlib hooks
   to verify before starting cycle 263: `Equiv.Perm`, `Setoid.r`,
   `Quotient`, `MulAction.orbit`.

## Suggested next approach

**Cycle 263 (recommended)**: Phase A.2 completion — tree-automorphism
`Setoid` on `LabelledRootedTree`. Concrete deliverables:

1. **`treeAutomorphism : RootedTree → Type`** (or `Equiv.Perm`-based) —
   recursive predicate / type for automorphisms of a `RootedTree`.
   Key recursive identity: an automorphism of `mk cs` is a permutation
   `π : Equiv.Perm (Fin cs.length)` such that `cs.get i` is isomorphic
   to `cs.get (π i)` for each `i`, together with one automorphism per
   child subtree. Two routes:
   - **Route A (recursive predicate)**: define `treeAutomorphism` by
     recursion on `RootedTree`, mirroring `decEqTree` / `decEqList`
     mutual-recursion (Section301.lean lines 73-90).
   - **Route B (`Equiv.Perm (Vertex t)` subtype)**: a tree-automorphism
     is a `Equiv.Perm (Vertex t)` whose action commutes with the
     parent-child structure (i.e. `Vertex.child i v` is sent to
     `Vertex.child (π_root i) (φ_i v)` for some recursive auxiliary
     data). Heavier machinery but plugs directly into Mathlib's
     `MulAction.orbit` framework.

   Recommended: **Route A** for cycle 263 (simpler, faithful to
   Butcher's recursive treatment), with Route B deferred to Phase C if
   needed for `card_orbit_mul_card_stabilizer_eq_card_group`.

2. **`LabelledRootedTree.Setoid` (or `Equiv` predicate)** — two
   labellings `l₁, l₂ : Vertex t ≃ Fin (order t)` are equivalent if
   there exists a tree-automorphism `φ : treeAutomorphism t` such that
   `l₂ = l₁ ∘ φ.toEquiv` (with appropriate type-coercion plumbing).

3. **Non-vacuity**: exhibit two labellings of `mk [vertex, vertex]`
   related by the leaf-swap automorphism, and one labelling of `cherry`
   whose only equivalence-class member is itself (σ(cherry) = 1).

**Estimated LOC**: ~150-200. **Axiom-clean target**: yes.

**Cycle 264+ outlook**: If cycle 263 closes Phase A.2, cycle 264 can
optionally tackle Phase A.3 (orbit-size theorem `Nat.card (orbit …) =
r(t)!/σ(t)`) — this is the σ-faithfulness identity from
`.prover-state/issues/symmetry_group_equivalence.md`. If A.3 looks
hard, defer per `lem_310B_plan.md` §4.1 risk assessment and proceed
to Phase B or Phase D.

**Alternative for cycle 263**: if the tree-automorphism `Setoid`
proves to be a multi-cycle effort, fall back to the cycle 260 §342
scouting recommendation — `lem:342A` (342a) shifted Legendre
orthogonality — as a parallel single-cycle entry point. This was
flagged in `lem_310B_plan.md` §8 as a credible pivot if the §310 path
stalls.

`lean_status.json` and `plan.md` were deliberately not modified this
cycle per strategy §G (cycle 262 is engineering infrastructure; the
`lem:310B` row remains `[ ]` / `unformalized` until Phase F closes).
