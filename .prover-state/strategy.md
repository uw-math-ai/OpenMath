# Cycle 264 Strategy

## A. Target

**Option 1 from cycle 263 task results** — heterogeneous-labelling non-vacuity for the
cycle 263 weakened `LabelledRootedTree.setoid`.

Ship a witness showing that the `Setoid` identifies **two genuinely-distinct
labellings** of `RootedTree.mk [vertex, vertex]` (the two-leaf tree) under the
leaf-swap permutation. Cycle 263 only shipped reflexivity witnesses; reflexivity
alone is true for the trivial `Eq` setoid, so without this check the cycle 263
deliverable could be vacuously trivial.

This is THE recommendation from both the cycle 263 task results §"Suggested next
approach" Option 1 AND the consultant-advice-cycle-263 §C Option 1. Both
analyses agree, with a verified-Mathlib-API recipe.

## B. Why this and not the other options

- **Option 2 (strengthen TreeAutomorphism to full recursive predicate)**:
  multi-cycle, requires a `mutual` block through `List RootedTree`. Risks the
  cycle 149/200/201 sorry-first rollback pattern. **DO NOT attempt this cycle.**
- **Option 3 (Phase B `thm:306A`)**: multi-cycle Taylor/multinomial work,
  bypassable per `lem_310B_plan.md` §4.2. Planner decision needed before any
  Phase B attempt. **DO NOT attempt this cycle.**
- **Option 4 (pivot to `lem:342A`)**: legitimate single-cycle alternative, but
  abandons §310 momentum without closing the non-vacuity gap. Reserve as
  cycle 265+ choice after Option 1 lands.

Option 1 ships a self-contained ~50–70 LOC clean deliverable; cycle 265's
planner can then decide between strengthening (Option 2), Phase B (Option 3),
or pivoting (Option 4) with the §310 non-vacuity story complete.

## C. Concrete deliverables (append to `OpenMath/Chapter3/Section300.lean` after line 389)

Follow `.prover-state/issues/consultant_advice_cycle_263.md` §D verbatim.
The recipes there have been verified against Mathlib at HEAD by the consultant.

### C.1 — Definitions

```lean
def doubleVertex : RootedTree := mk [vertex, vertex]

def leftLeaf : Vertex doubleVertex :=
  Vertex.child ⟨0, by show 0 < 2; omega⟩ Vertex.root

def rightLeaf : Vertex doubleVertex :=
  Vertex.child ⟨1, by show 1 < 2; omega⟩ Vertex.root
```

Try `(0 : Fin 2)` / `(1 : Fin 2)` form first as it may elaborate cleaner; fall
back to `⟨0, _⟩` with `omega`/`decide` if needed.

### C.2 — Distinctness theorems (three)

```lean
theorem leftLeaf_ne_rightLeaf : leftLeaf ≠ rightLeaf := by
  intro h; cases h
-- fallback if `cases h` fails: `exact absurd h (by decide)`

theorem leftLeaf_ne_root : leftLeaf ≠ Vertex.rootOf doubleVertex := by
  intro h; cases h

theorem rightLeaf_ne_root : rightLeaf ≠ Vertex.rootOf doubleVertex := by
  intro h; cases h
```

Memory `feedback_indexed_inductive_cases_disjoint.md` applies: `cases h` on
disjoint constructors of an indexed inductive closes by absurdity. If
`Vertex.rootOf doubleVertex` doesn't reduce to `Vertex.root` by `rfl`, prefix
with `show leftLeaf ≠ Vertex.root` (and similarly for the other two).

### C.3 — `leafSwapAutomorphism`

```lean
def leafSwapAutomorphism : TreeAutomorphism doubleVertex where
  perm := Equiv.swap leftLeaf rightLeaf
  perm_root := by
    exact Equiv.swap_apply_of_ne_of_ne
      (fun h => leftLeaf_ne_root h.symm)
      (fun h => rightLeaf_ne_root h.symm)
```

### C.4 — Two distinct labellings + equivalence witness

```lean
noncomputable def canonicalDoubleVertex : LabelledRootedTree :=
  { underlying := doubleVertex
    labelling := canonicalLabelling doubleVertex }

noncomputable def swappedDoubleVertex : LabelledRootedTree :=
  { underlying := doubleVertex
    labelling := (Equiv.swap leftLeaf rightLeaf).trans (canonicalLabelling doubleVertex) }

theorem canonical_equiv_swapped :
    LabelledRootedTree.Equiv canonicalDoubleVertex swappedDoubleVertex := by
  refine ⟨rfl, leafSwapAutomorphism, ?_⟩
  intro v
  show canonicalLabelling doubleVertex v =
      ((Equiv.swap leftLeaf rightLeaf).trans (canonicalLabelling doubleVertex))
        (Equiv.swap leftLeaf rightLeaf v)
  simp [Equiv.trans_apply, Equiv.swap_apply_self]
```

**Field-order verification step** before writing C.4: cycle 263's
`LabelledRootedTree.Equiv` is in `OpenMath/Chapter3/Section300.lean` lines
~323-340. READ those lines first via Read tool to confirm the exact shape (∃
underlying-equality, ∃ TreeAutomorphism, ∀ vertex predicate, etc.) and adjust
`refine ⟨…⟩` order to match.

### C.5 — Distinctness of labellings

```lean
theorem labellings_distinct :
    canonicalDoubleVertex.labelling ≠ swappedDoubleVertex.labelling := by
  intro h
  apply leftLeaf_ne_rightLeaf
  apply (canonicalLabelling doubleVertex).injective
  have heval : canonicalDoubleVertex.labelling leftLeaf =
               swappedDoubleVertex.labelling leftLeaf := by rw [h]
  simpa [canonicalDoubleVertex, swappedDoubleVertex,
         Equiv.trans_apply, Equiv.swap_apply_left] using heval
```

If the `simpa` chain doesn't fire, try `lean_multi_attempt` with variations
on the `Equiv.trans` / `Equiv.swap_apply_left` rewrite ordering. Possible
alternative: use `Function.funext_iff` to obtain the pointwise version of `h`
explicitly.

### C.6 — Bottom-line non-vacuity example

```lean
example :
    ∃ a b : LabelledRootedTree,
      a.labelling ≠ b.labelling ∧ LabelledRootedTree.Equiv a b :=
  ⟨canonicalDoubleVertex, swappedDoubleVertex,
   labellings_distinct, canonical_equiv_swapped⟩
```

Adjust the `∧` order if `LabelledRootedTree.Equiv` ⇒ `≠` direction reads
differently from this template.

## D. Verified Mathlib hooks (from consultant analysis at HEAD)

| Goal | Lemma | File |
|---|---|---|
| `swap a b : Perm α` | `Equiv.swap` | `Mathlib/Logic/Equiv/Basic.lean:631` |
| `swap a b a = b` | `Equiv.swap_apply_left` | line 647 |
| `swap a b b = a` | `Equiv.swap_apply_right` | line 651 |
| `x ≠ a → x ≠ b → swap a b x = x` | `Equiv.swap_apply_of_ne_of_ne` | line 654 |
| `(swap a b).trans (swap a b) = refl _` | `Equiv.swap_swap` | line 662 |
| `Equiv.trans_apply` | std | std |
| `Equiv.injective` | std | std |

No new Mathlib infrastructure needed.

## E. Process

1. (5 min) Read `OpenMath/Chapter3/Section300.lean` lines 280-389 to confirm
   the cycle 263 `LabelledRootedTree.Equiv` signature, `TreeAutomorphism`
   field names, and `canonicalLabelling`'s type. Use `lean_hover_info` if
   needed.
2. (45 min) Ship C.1 through C.6 in order, running
   `lake env lean OpenMath/Chapter3/Section300.lean` after each block. Each
   block should compile clean before moving on.
3. (10 min) Verify aggregator: `lake env lean OpenMath/Chapter3.lean`.
4. (5 min) Axiom-clean check via `lean_verify` on `labellings_distinct` and
   `canonical_equiv_swapped`. Expected:
   `[propext, Classical.choice, Quot.sound]` only.
5. (10 min) Run tautology scanner regex:
   `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section300.lean`
   — expect zero hits. If hits appear (e.g. `:= h_foo` patterns), apply the
   `h_<name> → h<name>` rename workaround per
   `tautology_scanner_false_positives.md`.
6. (10 min) Update `.prover-state/issues/lem_310B_plan.md` §4.1 with a cycle
   264 update subsection documenting the non-vacuity closure (analogous to the
   cycle 261/262/263 entries already present).
7. (5 min) Write `.prover-state/task_results/cycle_264.md` per the
   CLAUDE.md template (Worked on / Approach / Result / Faithfulness check /
   Dead ends / Discovery / Suggested next approach).
8. Commit.

## F. Aristotle suitability

**Medium-high.** Steps C.1–C.3 and C.5–C.6 are mechanical with the right
Mathlib lemma names. Step C.4 routes through cycle 263's freshly-defined
`LabelledRootedTree.Equiv`, which Aristotle hasn't seen.

**Submission strategy**: optional. If you do submit, send the **entire
deliverable C.1–C.6** as one job with the cycle 263 file at HEAD plus this
strategy as context. Single 30-minute poll discipline per CLAUDE.md.

**Do NOT block** on Aristotle — the consultant-verified recipes are direct.
Manual closure should complete in <90 minutes total.

## G. What NOT to do

- Do **NOT** strengthen `TreeAutomorphism` to a full recursive predicate. That
  is Option 2 / Phase A.3 multi-cycle work; risks cycle 149/200/201 rollback
  pattern.
- Do **NOT** attempt Phase B (`thm:306A` multinomial Taylor) — multi-cycle,
  per `lem_310B_plan.md` §4.2.
- Do **NOT** attempt `lem:310B` itself — multi-cycle infrastructure, see
  `lem_310B_plan.md` §5 Phases A–F.
- Do **NOT** label this cycle's deliverable with a textbook entity ID; do not
  update `lean_status.json` for `lem:310B` or `def:300C`. This is
  **infrastructure validation**, not a textbook entity closure.
- Do **NOT** introduce `axiom`, `constant`, or `sorry`. Cycle 264's bar is
  "ship axiom-clean or skip the cycle entirely".
- Do **NOT** raise `maxHeartbeats` above 200000.
- Do **NOT** attempt to compile `OpenMath/Chapter4/Section441.lean` on GPFS —
  43+ consecutive timeouts since cycle 182, skip per
  `cycle_182_gpfs_slowness.md`.
- Do **NOT** edit `scripts/autonomous_loop.py`. The empty "What I'm stuck on"
  phantom is loop-maintainer territory per
  `consultant_advice_cycle_248.md` §I and
  `tautology_scanner_false_positives.md`.
- Do **NOT** rename your deliverable to `lem_310B_*` — that name is reserved
  for the actual textbook lemma.

## H. Previously-failed approaches — do not repeat

- `induction t with | mk children ih =>` on `RootedTree` fails (nested
  inductive). Use `mutual` + structural pattern matching, or pattern-match
  `t = mk cs` first (per cycle 263's `Vertex.rootOf` precedent).
- `subst hEq` on a projection equality `a.field = b.field` fails. Destructure
  `a`/`b` first (`obtain ⟨…⟩ := a`), then `cases hEq`.
- Universe-polymorphism inference on a structure with `Equiv` fields fails
  without explicit `: Type` annotation.

## I. Abort criteria

If steps C.1–C.3 do not compile within 30 minutes total, STOP and:
1. Document the specific Lean error in `.prover-state/issues/`.
2. Roll back any partial edits to `Section300.lean` to ensure sorry count
   stays at 0.
3. Write `task_results/cycle_264.md` documenting the stall.
4. Do NOT ship a partial deliverable with sorries.

If steps C.4–C.5 stall (the most delicate, due to `Equiv.coe_fn` /
`Quotient.mk` plumbing), keep C.1–C.4 + a partial witness exhibiting
`canonical_equiv_swapped` and treat `labellings_distinct` (C.5) as the stretch
goal — ship without it if the `simpa` chain doesn't fire.

## J. Success criteria

- **Minimum (P1)**: ship C.1–C.4 + C.6 axiom-clean. ~50 LOC over HEAD. Sorry
  count remains 0.
- **Full (P1 + P2)**: also ship C.5 (`labellings_distinct`). ~70 LOC over HEAD.
- **Stretch (P3)**: the `example` in C.6 uses both `labellings_distinct` and
  `canonical_equiv_swapped` together — confirming the Setoid is genuinely
  non-trivial via a single named witness.

Cycle 263 was a clean infrastructure ship. Cycle 264 should be a clean
infrastructure-validation ship. Cycle 265+ pivots based on the planner's
choice among Option 2 / 3 / 4.

## K. Note on the recurring "stuck on" phantom

Cycle 263's "What I'm stuck on" field was empty. This is the **6th confirmed
phantom-template invocation** (cycles 015, 040, 174, 180, 248, 263). The
consultant phase was invoked against a clean cycle ship. Worker MUST NOT treat
the phantom as a real blocker; pivot directly to route-finding. The standing
recommendation in `consultant_advice_cycle_248.md` §I (short-circuit
consultant phase when stuck-on is empty AND sorry count is 0) applies — but
that's loop-maintainer territory, not worker territory.
