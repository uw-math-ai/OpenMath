# Cycle 261 strategy

## §A — Status snapshot

Cycle 260 SHIPPED clean: `lem_310B_plan.md` (774-line multi-phase
scoping doc) + four `Finset.sum_*` API enrichment lemmas in
`OpenMath/Chapter3/Section301.lean`. All axiom-clean, repo sorry
count = 0. No supervisor regression to address.

Both candidate cycle-261 entry points flagged in the cycle 260 task
results are credible single-cycle ships:

* **Direction 1**: Phase A.1 of `lem_310B_plan.md` — `RootedTree.Vertex`
  predicate + `vertices` enumeration + `vertices_card`. Maintains
  §310/§311 strategic momentum; lays foundation for the multi-cycle
  `lem:310B` plan (8–14 cycle estimate per §5 of the plan).
* **Direction 2**: `lem:342A` (342a) shifted-Legendre orthogonality
  on `[0,1]`. Independent fresh-entity pivot.

To keep the supervisor's score trajectory positive (cycle 260
scored +1), cycle 261 must ship axiom-clean, sorry-clean, with a
substantive deliverable.

## §B — Cycle 261 priority — Direction 1 (RECOMMENDED)

Ship **Phase A.1 of `lem_310B_plan.md`**: `RootedTree.Vertex`
inductive predicate + `RootedTree.vertices` `Finset` enumeration +
`vertices_card` identity (`(vertices t).card = order t`), with
three non-vacuity witnesses on `cherry`, `broom₃`, and
`mk [vertex, cherry]`.

### Rationale

1. **Sequential momentum.** Cycles 254–260 have been §310/§311
   infrastructure work. Cycle 260's scoping doc explicitly
   identifies Phase A.1 as the highest-confidence single-cycle
   entry point into the multi-cycle `lem:310B` plan. Pivoting
   away now (to Direction 2) loses the planning investment.
2. **Concrete deliverables already specified.** `lem_310B_plan.md`
   §7 lists the five concrete artifacts and the axiom-clean
   target. Worker has minimal scoping work — implement against
   the plan.
3. **Cycle 017 template applies directly.** The mutual `density`
   recursion in `OpenMath/Chapter3/Section301.lean:123-179`
   (visible at HEAD) is the canonical template for any
   `RootedTree`-mutual-recursion proof. Three relevant patterns:
   - Line 123-140: `mutual def density / densityProd` pair,
     mirroring the `RootedTree.mk` / `List RootedTree` nesting.
   - Line 142-147: `densityProd_eq_map_prod` reformulation via
     `List.prod`, allowing standard list-induction reasoning.
   - Line 164-178: `mutual theorem density_pos / densityProd_pos`,
     companion positivity statements proved by mutual structural
     recursion. This is the proof template for `vertices_card`.

### Concrete deliverables (5 declarations + 3 examples)

All in a **NEW file** `OpenMath/Chapter3/Section300.lean`. **Do
NOT** extend `Section310.lean` or `Section301.lean` — the new
`Vertex` type is genuinely §300 infrastructure (vertex/edge
structure of rooted trees), and the planner anticipates
Phase A.2/A.3 also living in `Section300.lean`. Keeping it
separate keeps the cycle 017 mutual-recursion proofs in
`Section301.lean` uncontaminated.

The new file's `import` line:

```lean
import OpenMath.Chapter3.Section310
```

since `Vertex` needs the `RootedTree` type defined in
`Section310.lean`. Add `import OpenMath.Chapter3.Section300` to
`OpenMath/Chapter3.lean` (the aggregator) so cycle 261's
deliverables are picked up by `lake build`.

#### Deliverable 1 — `RootedTree.Vertex : RootedTree → Type`

```lean
namespace OpenMath.Chapter3.Section310

namespace RootedTree

/-- A vertex of a rooted tree: either the root, or a vertex of one
of the children. The `child` constructor packages a child index `i`
and a vertex of the i-th child. -/
inductive Vertex : RootedTree → Type
  | root {cs : List RootedTree} : Vertex (mk cs)
  | child {cs : List RootedTree} (i : Fin cs.length) :
      Vertex (cs.get i) → Vertex (mk cs)

end RootedTree
end OpenMath.Chapter3.Section310
```

Lean's elaborator infers the implicit `cs` argument from the
`Vertex (mk cs)` target type.

#### Deliverable 2 — `DecidableEq (Vertex t)` instance

Lean 4 does NOT auto-derive `DecidableEq` for inductives that
recurse over nested `List RootedTree` types. Two routes:

**Route A — mutual decidability (cleaner, ~30 LOC)** mirroring
the cycle 017 `decEqTree` / `decEqList` block at
`Section301.lean:73-92`. The key challenge: when two
`Vertex.child i v` and `Vertex.child j w` are compared, we need
both `i = j` (for the indices) AND the underlying vertices `v`
and `w` to be equal under a transport along the index equality.
The `hij ▸ v` transport is the right primitive but care is needed
on the `injEq` extraction.

**Route B — noncomputable `Classical.decEq` (1 line, safe
fallback)**:

```lean
noncomputable instance {t : RootedTree} : DecidableEq (Vertex t) :=
  Classical.decEq _
```

`Classical.decEq` only introduces `Classical.choice`, which is
already in the codebase's axiom baseline. **Route B is acceptable
and recommended for Phase A.1** — the cycle 261 deliverable's
mathematical content is `vertices_card`, not computable
enumeration. A future cycle can replace with Route A if needed.

#### Deliverable 3 — `vertices : (t : RootedTree) → Finset (Vertex t)`

Build via mutual recursion: a `Finset` for `vertices t` and a
`Finset` for the children's contribution. Sketch:

```lean
mutual
  noncomputable def vertices : (t : RootedTree) → Finset (Vertex t)
    | mk cs =>
        insert Vertex.root (verticesFromChildren cs)

  noncomputable def verticesFromChildren :
      (cs : List RootedTree) → Finset (Vertex (mk cs))
    | [] => ∅
    | _ :: _ =>
        Finset.univ.biUnion (fun i : Fin cs.length =>
          (vertices (cs.get i)).image (Vertex.child i))
end
```

**Implementation risks**:

- `Finset.image` requires `DecidableEq (Vertex (mk cs))` (handled
  by Deliverable 2). The `noncomputable` keyword is needed since
  Deliverable 2 uses `Classical.decEq` (Route B).
- `Finset.biUnion` over `Fin cs.length` requires
  `[Fintype (Fin cs.length)]` (automatic) plus `DecidableEq` on
  the target (handled).
- The mutual block must terminate. Structural recursion on the
  `RootedTree` should work — each recursive call to `vertices` is
  on a structurally smaller subtree `cs.get i`.

**Fallback if `Finset` is too heavy**: drop down to `List
(Vertex t)` and prove `vertices_length` instead of
`vertices_card`. This trades the "set" flavour for fast
elaboration. Acceptable if Deliverable 3 stalls past 60 minutes.

#### Deliverable 4 — `vertices_card : (vertices t).card = order t`

Mutual structural induction template from `Section301.lean:159-178`
(`order_pos` / `density_pos`). For the `mk cs` case:

```lean
mutual
  theorem vertices_card : ∀ t : RootedTree,
      (vertices t).card = order t
    | mk cs => by
        show (insert Vertex.root (verticesFromChildren cs)).card
          = 1 + orderSum cs
        rw [Finset.card_insert_of_not_mem ?_]
        · congr 1
          exact verticesFromChildren_card cs
        · -- Vertex.root ∉ verticesFromChildren cs: by case analysis,
          -- every member of verticesFromChildren is Vertex.child _ _
          sorry  -- MUST close — see proof sketch below

  theorem verticesFromChildren_card : ∀ cs : List RootedTree,
      (verticesFromChildren cs).card = orderSum cs
    | [] => by simp [verticesFromChildren, orderSum]
    | t :: ts => by
        sorry  -- MUST close — uses IH + Finset.card_biUnion +
               -- disjointness of Vertex.child i vs Vertex.child j for i ≠ j
end
```

**Key sub-lemma**: `Vertex.root ∉ verticesFromChildren cs` reduces
to: every element of `verticesFromChildren cs` is constructed by
`Vertex.child _ _`, and `Vertex.root ≠ Vertex.child _ _` by
constructor injectivity (`Vertex.noConfusion` or pattern match on
the equality).

**Disjointness for `card_biUnion`**: for `i j : Fin cs.length`
with `i ≠ j`, the images of `(Vertex.child i) ∘ vertices (cs.get i)`
and `(Vertex.child j) ∘ vertices (cs.get j)` are disjoint because
`Vertex.child i _ = Vertex.child j _` forces `i = j` (constructor
injectivity again).

**Sorry count rule**: cycle 261's deliverable MUST ship with
sorry count = 0. If `vertices_card` cannot be closed cleanly,
ABORT to §C fallback.

#### Deliverable 5 — Three non-vacuity examples

```lean
example : (RootedTree.vertices RootedTree.cherry).card = 2 := by
  rw [RootedTree.vertices_card]; rfl

example : (RootedTree.vertices RootedTree.broom₃).card = 3 := by
  rw [RootedTree.vertices_card]; rfl

example : (RootedTree.vertices
            (RootedTree.mk [RootedTree.vertex, RootedTree.cherry])).card
        = 4 := by
  rw [RootedTree.vertices_card]; rfl
```

If `order cherry = 2` requires more than `rfl`, use
`decide` or `simp [RootedTree.order, RootedTree.orderSum]`.

### Axiom budget

`Classical.choice` (via `Classical.decEq` in Deliverable 2) is in
the standard `[propext, Classical.choice, Quot.sound]` baseline.
NO new axioms beyond this trio are acceptable. `#print axioms
OpenMath.Chapter3.Section310.RootedTree.vertices_card` must
return exactly `[propext, Classical.choice, Quot.sound]`.

### LOC budget

**Target**: 80–120 LOC for `Section300.lean` (~150 LOC inclusive
of docstrings + examples + aggregator update). Per cycle 260
scoping doc.

### Time budget

~2 hours focused work.

## §C — Cycle 261 ABORT threshold and fallback

If Phase A.1's `vertices` definition or `vertices_card` proof
**stalls beyond 90 minutes** without compilation progress, ABORT
Direction 1 and pivot to **Direction 2** (`lem:342A` (342a)).

Concrete abort triggers:
- (a) The `Finset.biUnion` definition refuses to elaborate due to
  nested-inductive motive issues. Try the `List`-fallback once
  before aborting.
- (b) The disjointness proof in `verticesFromChildren_card`
  requires more than one auxiliary helper lemma.
- (c) `decEqVertex` mutual block (Route A) exceeds 30 LOC. Switch
  to Route B (`Classical.decEq`) once before aborting.

The abort criterion mirrors cycle 200's rollback discipline:
sorry-first scaffolds for multi-cycle targets are FORBIDDEN per
supervisor policy. Better to ship Direction 2 axiom-clean than
Direction 1 with a `sorry` in `vertices_card`.

## §D — Direction 2 fallback — `lem:342A` (342a) orthogonality

If Direction 1 aborts per §C, ship a single-cycle deliverable on
the §342 cluster:

### Concrete deliverable

New file `OpenMath/Chapter3/Section342.lean` shipping:

1. `noncomputable def shiftedLegendre (n : ℕ) : Polynomial ℝ` —
   the shifted Legendre polynomial `P_n^*(x) := P_n(2x - 1)` on
   `[0, 1]`. Via Mathlib's `Polynomial.legendre` (verify path
   with `lean_local_search "legendre"` first thing in the worker
   session) composed with the linear shift `2X - 1`.

2. `theorem shiftedLegendre_orthogonal {m n : ℕ} (hmn : m ≠ n) :
   ∫ x in (0:ℝ)..1, (shiftedLegendre m).eval x *
                    (shiftedLegendre n).eval x = 0` — (342a)
   orthogonality on `[0, 1]`. Closure: change-of-variables
   `u := 2x - 1` reduces to Mathlib's orthogonality on `[-1, 1]`
   plus Jacobian `du/2`. Use
   `intervalIntegral.integral_comp_mul_left` or similar.

3. `theorem shiftedLegendre_eval_one (n : ℕ) :
   (shiftedLegendre n).eval 1 = 1` — (342b) normalization.
   Closure: `P_n(1) = 1` (Mathlib) + `2·1 - 1 = 1`.

4. Three non-vacuity examples for `n = 0, 1, 2` exercising both
   theorems with explicit Legendre values.

### Risk

**Verify Mathlib's Legendre polynomial API FIRST** before
committing. Run `lean_local_search "Legendre"` and
`lean_loogle "Polynomial.*legendre"` at session start. If
Mathlib's Legendre infrastructure is too sparse to support
`shiftedLegendre_orthogonal` in a single cycle, ABORT
Direction 2 and pivot to **Direction 3** (§E).

### Axiom budget

`[propext, Classical.choice, Quot.sound]`. NO new axioms.

### LOC budget

~80–120 LOC.

## §E — Direction 3 last-resort fallback — Section319 helper extraction

If both Direction 1 and Direction 2 abort, ship a **pure
refactor** extracting three private helpers from
`OpenMath/Chapter3/Section319.lean` (`geometric_sum_one_plus_pos`,
`geometric_sum_one_plus_zero`, `pow_one_add_le_exp`) into a new
file `OpenMath/Helpers/GeometricExp.lean`. Update `Section319.lean`
to import the new file. ~120 LOC moved, zero new content.
Cycle-neutral on sorry count but counts as a substantive ship.

This fallback was floated in cycle 248 task results and is a
guaranteed-clean refactor.

## §F — DO NOT do these (cycle 261 specific)

- **Do NOT extend the order-N specialisation chain** (cycle 259's
  `lem_311A_order_five` chain). Cycle 259 explicitly cut off the
  chain at order 5; cycle 260 confirmed. Further extensions are
  forbidden — combinatorial growth, no new mathematical content,
  and substantive §311 work requires `lem:310B` Phase A
  infrastructure.

- **Do NOT ship sorry-first scaffolds for Phase A or any phase
  of `lem_310B_plan.md`.** Cycle 200/201 rollback and cycle
  149/150 `def:530B` rollback both forbid sorry-first scaffolds
  for multi-cycle targets. Every phase must close axiom-clean.

- **Do NOT name the cycle 261 deliverable `lem_310B`.** The
  Phase A.1 deliverable is `vertices_card` (vertex enumeration
  scaffold). `lem:310B` is the eventual multi-phase capstone
  (Phase F.1) and must not be claimed prematurely. Plan.md row
  for `lem:310B` stays `[ ]` and `lean_status.json` row stays
  `unformalized` for cycle 261.

- **Do NOT attempt the full `lem:310B` proof.** Multi-cycle work
  per `lem_310B_plan.md` §5 (8–14 cycles).

- **Do NOT define `Vertex` recursing via `RootedTree.rec`'s
  motive directly.** The nested inductive `RootedTree | mk :
  List RootedTree → RootedTree` interacts poorly with non-mutual
  `Vertex` definitions per the memory
  `feedback_rootedtree_nested_induction`. The inductive
  declaration with explicit `root`/`child` constructors above is
  fine, but the PROOFS of `vertices_card` etc. must use the
  cycle 017 `mutual theorem` block pattern from
  `Section301.lean:159-178` — not raw `RootedTree.recOn` /
  `induction t`.

- **Do NOT compile `OpenMath/Chapter4/Section441.lean`.** GPFS
  pathology has produced 43+ consecutive timeouts since cycle
  182. Per `.prover-state/issues/cycle_182_gpfs_slowness.md`,
  skip any §441 compile attempts entirely. Cycle 260 did NOT
  touch §441.

- **Do NOT poll any Aristotle projects.** There are no pending
  Aristotle submissions for cycle 261 (per the cycle 260 task
  results). No `mcp__aristotle__` calls needed.

- **Do NOT modify `scripts/autonomous_loop.py`.** Loop-maintainer
  territory per CLAUDE.md.

- **Do NOT raise `maxHeartbeats`** above 200000. If
  `decEqVertex`'s mutual block stalls, switch to
  `Classical.decEq` (Route B above).

- **Do NOT introduce `axiom`/`constant` declarations.**

## §G — Worker workflow

1. **(5 min)** Read this strategy file and
   `.prover-state/issues/lem_310B_plan.md` §3 (project hooks)
   and §7 (cycle 261 entry point).
2. **(15 min)** Read `OpenMath/Chapter3/Section301.lean:73-179`
   for the cycle 017 mutual-recursion templates: `decEqTree`,
   `density`, `densityProd_eq_map_prod`, `density_eq`,
   `density_pos`, `densityProd_pos`. These are the canonical
   patterns for Deliverables 2, 3, and 4.
3. **(5 min)** Verify `RootedTree.cherry`, `RootedTree.broom₃`,
   `RootedTree.vertex`, `RootedTree.order`, `RootedTree.orderSum`
   are at the expected locations in
   `OpenMath/Chapter3/Section310.lean` (Grep). They are —
   `cherry` @ line 111, `broom₃` @ line 114, `vertex` @ line 108
   per HEAD inspection.
4. **(60–90 min)** Implement Deliverables 1–5 in
   `OpenMath/Chapter3/Section300.lean`. Run
   `lake env lean OpenMath/Chapter3/Section300.lean` after each
   deliverable to catch issues early. **TIMEOUT WATCH**: if any
   single `lake env lean` call exceeds 5 minutes on
   `Section300.lean`, suspect a `Decidable` instance loop or a
   mutual-recursion well-foundedness issue — break the proof
   down or switch `DecidableEq` to Route B (`Classical.decEq`).
5. **(10 min)** Add `import OpenMath.Chapter3.Section300` to
   `OpenMath/Chapter3.lean`. Run `lake env lean
   OpenMath/Chapter3.lean` to verify the aggregator builds.
6. **(10 min)** Run `lake build OpenMath.Chapter3.Section300`
   to refresh the `.olean`, then `#print axioms` on
   `RootedTree.vertices_card` and confirm
   `[propext, Classical.choice, Quot.sound]`. This `lake build`
   step is essential — `lake env lean` does NOT update `.olean`
   files, so `#print axioms` against the freshly-edited
   declaration would otherwise report `unknownIdentifier`.
7. **(5 min)** Tautology-scanner check:
   `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section300.lean`
   should return no matches.
8. **(20 min)** Write `.prover-state/task_results/cycle_261.md`
   per CLAUDE.md template. Faithfulness check on Deliverables 1,
   3, 4 (the new `def`s and `theorem`).
9. **(5 min)** Update `extraction/formalization_data/lean_status.json`
   ONLY IF a textbook entity is closed (NOT the case for Phase
   A.1 — `vertices_card` is engineering infrastructure, not a
   Butcher entity). Likewise `plan.md`. Cycle 261's deliverable
   is engineering scaffolding; neither file needs updating
   beyond a cosmetic `Recent commits` refresh.
10. **(5 min)** Commit with a message of the form
    `Cycle 261 — §300 RootedTree.Vertex + vertices_card (lem:310B Phase A.1) SHIPPED.`

## §H — Faithfulness rationale

Deliverable 1 (`Vertex`): Butcher §300 (p. 139) defines vertices
informally as "the points of a tree". Our inductive `root` /
`child` constructors faithfully capture the same notion: every
vertex is either the root or sits inside a specific child
position. The `Fin cs.length` index plus the recursive
`Vertex (cs.get i)` argument matches Butcher's "vertex of the
i-th subtree" framing verbatim.

Deliverable 3 (`vertices`): the enumeration as a `Finset`
faithfully represents "the set of vertices" Butcher refers to in
§300's automorphism-group discussion. Each vertex appears exactly
once; the `Finset` structure ensures this.

Deliverable 4 (`vertices_card = order`): the natural
"|V(t)| = r(t)" identity. Butcher's §300 defines `r(t)` as "the
number of vertices of t", so the identity is by definition;
formally, it requires the mutual induction on `RootedTree`
against the cycle 017 `order_eq` recursion.

Phase A.1 has **no faithfulness divergence**. The σ-faithfulness
gap (`symmetry_group_equivalence.md`) does NOT bite here —
`vertices` is the literal vertex-set enumeration, not the
symmetry-group-quotient construction.

## §I — Success criteria (cycle 261 grading checklist)

- [ ] `OpenMath/Chapter3/Section300.lean` exists, ≤ 200 LOC.
- [ ] `OpenMath/Chapter3.lean` imports `Section300`.
- [ ] `lake env lean OpenMath/Chapter3/Section300.lean` exits 0.
- [ ] `lake env lean OpenMath/Chapter3.lean` exits 0.
- [ ] `lake build OpenMath.Chapter3.Section300` exits 0.
- [ ] `grep -c sorry OpenMath/Chapter3/Section300.lean` returns 0.
- [ ] `grep -c sorry OpenMath/Chapter3/Section{301,310,311}.lean`
      unchanged (no regression on cycle 248–260 deliverables).
- [ ] `#print axioms OpenMath.Chapter3.Section310.RootedTree.vertices_card`
      returns `[propext, Classical.choice, Quot.sound]`.
- [ ] Tautology-scanner regex returns no matches on
      `Section300.lean`.
- [ ] `task_results/cycle_261.md` written with the seven CLAUDE.md
      sections (Worked on / Approach / Result / Faithfulness check
      / Dead ends / Discovery / Suggested next approach).
- [ ] Three non-vacuity `example`s verify `vertices_card` fires
      on `cherry`, `broom₃`, and `mk [vertex, cherry]`.
- [ ] Commit message of the form
      `Cycle 261 — §300 RootedTree.Vertex + vertices_card (lem:310B Phase A.1) SHIPPED.`

If Direction 2 (`lem:342A`) or Direction 3 (Section319 refactor)
is shipped instead, adjust the file/symbol names accordingly.
The axiom-clean + sorry-clean + non-vacuity criteria apply
uniformly across all three directions.

## §J — Suggested cycle 262+ trajectory (planning only)

Per `lem_310B_plan.md` §5, if cycle 261 ships Phase A.1 cleanly:

* **Cycle 262**: Phase A.2 — `LabelledRootedTree` structure +
  tree-automorphism `Setoid`. ~150–200 LOC. Builds on cycle 261's
  `Vertex` enumeration.
* **Cycle 263**: Phase A.3 — orbit-size theorem
  `Nat.card (orbit …) = r(t)!/σ(t)` OR defer per
  `symmetry_group_equivalence.md`. ~100–150 LOC.
* **Cycles 264–266**: Phase B (Taylor) or skip per
  `lem_310B_plan.md` §4.2 bypass.
* **Cycles 267+**: Phase C (orbit-counting bridge), Phase D
  (multilinear lift), Phase E (small-r `lem:310B` cases),
  Phase F (general `lem:310B` capstone). See `lem_310B_plan.md`
  §5 for the full breakdown.

If cycle 261 ships Direction 2 (`lem:342A`) instead:

* **Cycle 262**: extend `lem:342A` properties (342c parity, 342d
  norm) or pivot to `lem:342B` (Gaussian quadrature exactness).
  Per `lem_310B_plan.md` §8.3, `lem:342B` consumes `lem:342A`
  (342g) so the §342 cluster has a multi-cycle structure of its
  own.
