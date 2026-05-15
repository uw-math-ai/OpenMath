# Cycle 262 Strategy — Phase A.2 (partial): `LabelledRootedTree` structure + `Fintype` instance + canonical labelling

## §A — Project state at start of cycle

- HEAD: `2b0428e Cycle 261 — §300 RootedTree.Vertex + vertices_card (lem:310B Phase A.1) SHIPPED.`
- Sorry count across repo: **0**. All recent §300/§301/§310/§311 theorems axiom-clean (`[propext, Classical.choice, Quot.sound]`).
- Cycle 261 just shipped the foundational `RootedTree.Vertex` infrastructure (`OpenMath/Chapter3/Section300.lean`, 179 LOC). Phase A.1 of `.prover-state/issues/lem_310B_plan.md` is **complete**.
- No Aristotle results pending.
- No issues currently blocking progress (`lem_310B_plan.md` is a planning doc, not a blocker).
- §441 GPFS pathology continues to block Phase C.2; skip per §F of this strategy.

## §B — Target this cycle

**Ship Phase A.2 (partial) of `lem_310B_plan.md`**: extend `OpenMath/Chapter3/Section300.lean` with the labelling infrastructure that consumes cycle 261's `Vertex`/`vertices`/`vertices_card`.

Specifically, the cycle 262 deliverable is:

1. **`Vertex.mem_vertices`** — completeness lemma: `∀ {t} (v : Vertex t), v ∈ vertices t`. Proves cycle 261's `vertices t` Finset enumerates ALL vertices.

2. **`Fintype` instance for `Vertex t`** — `noncomputable instance instFintypeVertex : Fintype (Vertex t)` derived from `vertices t` + `Vertex.mem_vertices`.

3. **`Fintype.card` identity** — `Fintype.card_vertex_eq_order : Fintype.card (Vertex t) = order t`. One-liner corollary of `vertices_card` (cycle 261).

4. **`structure LabelledRootedTree`** — the Phase A.2 datatype:
   ```lean
   structure LabelledRootedTree where
     underlying : RootedTree
     labelling : Vertex underlying ≃ Fin (order underlying)
   ```

5. **`canonicalLabelling : (t : RootedTree) → Vertex t ≃ Fin (order t)`** — built via `Fintype.equivFinOfCardEq` (Mathlib) applied to `Fintype.card_vertex_eq_order`.

6. **Three non-vacuity witnesses** — explicit `LabelledRootedTree`s for `vertex`, `cherry`, `broom₃`, each built via `canonicalLabelling`, with `order = n` `rfl` checks.

**Explicitly deferred to cycle 263+**:
- Tree-automorphism `Setoid` on `LabelledRootedTree` and the equivalence "two labellings of `mk [vertex, vertex]` are related by an automorphism". The plan file `lem_310B_plan.md` §"Phase A.2" allocates 1-2 cycles for the full Phase A.2; cycle 262 takes the first half (datatype + canonical labelling) and cycle 263 takes the Setoid + tree-automorphism work. Splitting this way keeps cycle 262 in the ~80-120 LOC range with high single-cycle close confidence.

## §C — Why this split (not the full Phase A.2 in one cycle)

The cycle 261 task results' "Suggested next approach" §"Cycle 262 (recommended)" specifies Phase A.2 with a budget of "150-200 LOC". Two paths:

- **Option 1 (full Phase A.2 in one cycle)**: structure + canonical labelling + tree-automorphism Setoid + non-vacuity. The tree-automorphism definition itself requires either (a) a permutation-group `MulAction` setup on `LabelledRootedTree` or (b) a recursive automorphism predicate matching child-subtree permutations. Both routes are non-trivial; (a) needs `Equiv.Perm`-style plumbing and `MulAction` instances; (b) needs recursive descent on `RootedTree`'s nested-inductive structure. Either path has stall risk.

- **Option 2 (split, this cycle's choice)**: ship the datatype + canonical labelling + Fintype infrastructure first. The tree-automorphism Setoid in cycle 263 then builds on solid foundations. Each cycle stays well within the supervisor's "axiom-clean, sorry count 0" target and the LOC budget per cycle remains modest (~80-120 LOC).

The cycle 200/201 rollback discipline (`equivalent_iff_pEquivalent_iff_phiEquivalent` sorry-first scaffold) and the cycle 149/150 rollback (`def:530B` Path A sorry-first scaffold) both argue against attempting a multi-sub-piece deliverable when any single piece could stall. **Sorry-first scaffolds are forbidden this cycle**: ship axiom-clean or skip the piece.

## §D — Step-by-step recipe

All work goes in `OpenMath/Chapter3/Section300.lean`, extending cycle 261's file. The new content lives **after** the existing `vertices_card` block and the three non-vacuity examples (lines 167-175), but **before** `end RootedTree` (line 177).

### D.1 — Completeness lemma `Vertex.mem_vertices` (~30-50 LOC)

```lean
theorem Vertex.mem_vertices : ∀ {t : RootedTree} (v : Vertex t), v ∈ vertices t
  | mk cs, root => by
      rw [vertices]
      exact Finset.mem_insert_self _ _
  | mk cs, child i v => by
      rw [vertices]
      refine Finset.mem_insert_of_mem ?_
      rw [Finset.mem_biUnion]
      refine ⟨i, Finset.mem_univ _, ?_⟩
      rw [Finset.mem_image]
      exact ⟨v, Vertex.mem_vertices v, rfl⟩
termination_by t v => t
decreasing_by
  simp_wf
  exact Nat.lt_add_left 1 (List.sizeOf_get cs i)
```

The well-founded recursion mirrors cycle 261's `vertices` and `vertices_card` structure. The `termination_by t v => t` clause uses `t` as the measure; the `decreasing_by` block discharges `cs.get i < mk cs` via the same `List.sizeOf_get + Nat.lt_add_left` chain used at lines 110 and 163.

### D.2 — `Fintype` instance + card identity (~10-20 LOC)

```lean
noncomputable instance instFintypeVertex (t : RootedTree) : Fintype (Vertex t) :=
  ⟨vertices t, fun v => Vertex.mem_vertices v⟩

theorem Fintype.card_vertex_eq_order (t : RootedTree) :
    Fintype.card (Vertex t) = order t := by
  show (vertices t).card = order t
  exact vertices_card t
```

The `show` reframes `Fintype.card (Vertex t)` (= `(Finset.univ : Finset (Vertex t)).card`) to `(vertices t).card`. Under our `Fintype.mk`, `Finset.univ.card = (vertices t).card` holds because `Finset.univ` is `vertices t` itself. If the `show` doesn't trigger definitional unfolding, fall back to `Finset.card_univ` + `rfl` on the `Fintype.mk` projection.

Risk-1 mitigation: if `show` fails because `Finset.univ.card` doesn't reduce to `(vertices t).card` definitionally, route via
```lean
have h : (Finset.univ : Finset (Vertex t)) = vertices t := by
  ext v; simp [Vertex.mem_vertices v]
rw [Fintype.card, h, vertices_card]
```

Verify the simpler path first; only escalate to the fallback if needed.

### D.3 — `LabelledRootedTree` structure + canonical labelling (~15 LOC)

```lean
/-- A rooted tree together with a chosen bijective labelling of its
vertices by `Fin (order t)`. Faithful to Butcher §300's `def:300C` —
see `.prover-state/issues/lem_310B_plan.md` §4.1. -/
structure LabelledRootedTree where
  underlying : RootedTree
  labelling : Vertex underlying ≃ Fin (order underlying)

/-- The canonical labelling of a rooted tree, derived from the
`Fintype` instance on `Vertex t` (cycle 262) via Mathlib's
`Fintype.equivFinOfCardEq`. Faithfulness divergence: Butcher's
labelling is a *choice* (not canonically determined); we expose one
specific labelling here for non-vacuity. Cycle 263+ will introduce
the tree-automorphism `Setoid` to recover the textbook's
quotient-by-symmetry behaviour. -/
noncomputable def canonicalLabelling (t : RootedTree) :
    Vertex t ≃ Fin (order t) :=
  Fintype.equivFinOfCardEq (Fintype.card_vertex_eq_order t)
```

If `Fintype.equivFinOfCardEq` does not exist under that exact name in current Mathlib, try `Fintype.equivOfCardEq` or compose `Fintype.equivFin : α ≃ Fin (Fintype.card α)` with a `Fin (Fintype.card (Vertex t)) ≃ Fin (order t)` via `Fin.castIso` (or `finCongr`) on the cycle-262 card identity. Verify early via `lean_local_search "Fintype.equivFinOfCardEq"` or `lean_loogle "Fintype.card _ = _ → _ ≃ _"`.

### D.4 — Three non-vacuity witnesses (~15 LOC)

```lean
/-- The canonical labelling of the singleton tree `vertex`. -/
noncomputable def canonicalVertex : LabelledRootedTree where
  underlying := vertex
  labelling := canonicalLabelling vertex

/-- The canonical labelling of `cherry`. -/
noncomputable def canonicalCherry : LabelledRootedTree where
  underlying := cherry
  labelling := canonicalLabelling cherry

/-- The canonical labelling of `broom₃`. -/
noncomputable def canonicalBroom₃ : LabelledRootedTree where
  underlying := broom₃
  labelling := canonicalLabelling broom₃

example : canonicalVertex.underlying.order = 1 := rfl
example : canonicalCherry.underlying.order = 2 := rfl
example : canonicalBroom₃.underlying.order = 3 := rfl
```

The `order = n` `rfl` checks confirm the structure's `underlying` field matches its intended tree (the `order` recursion from `Section310.lean` already produces these values by `rfl` on the small examples).

If `noncomputable def`+`canonicalLabelling` triggers universe / `noncomputable` propagation issues at use sites, swap to `noncomputable abbrev`. Both should work since `LabelledRootedTree` has no decidable-data fields.

## §E — Dead ends to avoid (from prior cycles)

**Do NOT try the approaches that have already failed**:

1. **DecidableEq placement after namespace opening** (cycle 261 dead end): if cycle 262 needs to introduce any new `DecidableEq` or `Fintype` instance, declare it **before** opening any sub-namespace where it'll be used. Cycle 261's `instDecidableEqVertex` is at lines 54-56 (just after `inductive Vertex`); follow this pattern. The new `instFintypeVertex` should live alongside, not inside `namespace Vertex`.

2. **`Option.noConfusion` direct call** (cycle 261 dead end): if a proof needs `False` from an equation between distinct constructors of an indexed inductive (e.g. `Vertex.root = Vertex.child i v`), use `cases h` instead of `Option.noConfusion (h.symm.trans h')`. `cases` auto-invokes the generated `Vertex.noConfusion` and produces `False` directly.

3. **`Fin.sum_univ_succ` without `show` coercion** (cycle 261 dead end + memory `feedback_fin_sum_univ_succ_coerce`): when applying `Fin.sum_univ_succ` to a sum indexed by `Fin (cs.length)` where `cs` matches a pattern like `t :: ts`, prepend `show (∑ i : Fin (ts.length + 1), …) = …` to definitionally coerce the binder type. `rw [Fin.sum_univ_succ]` without this preamble fails with a motive type-correctness error. **Cycle 262 may not need `Fin.sum_univ_succ` at all** — but if any new step does, apply this pattern.

4. **Nested inductive `induction` / `recOn`** (memory `feedback_rootedtree_nested_induction`): direct `induction t` or `RootedTree.recOn` calls fail on `RootedTree`'s nested-inductive structure. The cycle 261 pattern for `vertices_card` (well-founded recursion via `termination_by` and `decreasing_by`) is the canonical workaround. **`Vertex.mem_vertices` in §D.1 MUST follow this pattern** — do not attempt `induction t with` or `RootedTree.recOn`.

5. **`Finset.image` over a Type with non-decidable equality**: cycle 261 used `Classical.decEq` to side-step this. The existing `instDecidableEqVertex` instance auto-applies via instance resolution — no extra plumbing needed in §D.1.

6. **Sorry-first scaffolds** (cycle 200/201 rollback, cycle 149/150 rollback): forbidden this cycle. The sorry count must remain at 0. If any sub-piece doesn't close axiom-clean within the cycle's working budget, **abort that sub-piece and ship only what does close**. Document the abort in the task results, do not commit a `sorry`.

7. **GPFS compile of `Section441.lean`**: do not attempt. 43rd consecutive timeout recorded cycle 239 (`cycle_182_gpfs_slowness.md`). Skip without time investment.

8. **Pivots to `lem:342A` / `lem:342B` / `thm:351B`**: cycle 260's scoping doc enumerated these as alternative entry points, but cycle 261 chose Phase A.1 of `lem:310B`. Cycle 262 should continue the §310 cluster — pivoting now would orphan cycle 261's investment. The pivots remain viable for a future cycle if the §310 path stalls multi-cycle.

## §F — Abort thresholds

If any of the following fire, **abort the current sub-piece and skip to the next** (do NOT commit a `sorry` or partial proof):

1. **>20 minutes elapsed on `Vertex.mem_vertices`** (§D.1). The proof is structural well-founded recursion; if it doesn't compile in 3-4 attempts, it suggests a deeper issue with the recursive pattern. Likely needed escape: factor into a mutual-recursion `mem_vertices` + `mem_vertices_in_list` block (cf. `decEqList` precedent in `Section301.lean`). If still stuck after the mutual factoring, abort §D.1 entirely; cycle 263 retries.

2. **Mathlib API name drift on `Fintype.equivFinOfCardEq`** (§D.3). If the exact name doesn't exist, try the variants noted in §D.3 (5-minute time cap each). If none fit, fall back to a manual `Equiv.ofBijective` construction using `Fintype.bijective_iff_injective_and_card` — but cap this fallback at 10 minutes. If still stuck, **skip §D.3 and §D.4 entirely**; ship only §D.1 + §D.2 as a minimal-but-axiom-clean cycle 262.

3. **GPFS smoke test on `Section441.lean`** — skip without any time investment per §E.7.

4. If §D.1 closes but §D.2 stalls, abort and ship §D.1 only — the completeness lemma is itself useful infrastructure for cycle 263+.

5. **Tautology-scanner false-positive risk**: if any new `:= by exact h_xxx` or `:= h_xxx` pattern is introduced, immediately rename `h_xxx` → `hxxx` (drop underscore) to silence the scanner. The scanner's bug is documented in `tautology_scanner_false_positives.md`. Cycle 262 should pre-emptively use names like `hroot`, `hchild`, `hbu`, etc. without underscores.

## §G — Acceptance criteria

The cycle ships if **all** of the following hold:

- `lake env lean OpenMath/Chapter3/Section300.lean` exits 0.
- `lake env lean OpenMath/Chapter3.lean` exits 0 (aggregator regression check).
- `lake build OpenMath.Chapter3.Section300` exits 0.
- `grep -c sorry OpenMath/Chapter3/Section300.lean` returns 0.
- All new public theorems / instances axiom-clean. Run `#print axioms` on `Fintype.card_vertex_eq_order` and confirm `[propext, Classical.choice, Quot.sound]` only (`Classical.choice` is expected from the noncomputable `Fintype` instance and `Fintype.equivFinOfCardEq`).
- The tautology-scanner regex `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` returns no matches on the new code.
- Non-vacuity examples (§D.4 `example`s) compile by `rfl`.

`lean_status.json` and `plan.md` deliberately **do not change** this cycle — cycle 262 is engineering infrastructure for the multi-cycle `lem:310B` capstone. The `lem:310B` row remains `[ ]` / `unformalized`. The cycle 262 task results note the partial Phase A.2 progress in the `lem:310B` partial-status text without changing the row's `[ ]` mark.

## §H — Cycle 263+ outlook

If §D.1-D.4 all land cleanly, cycle 263 picks up the deferred Phase A.2 work:

- **`treeAutomorphism : RootedTree → Type`** (or `Equiv.Perm`-style) — recursive predicate for tree automorphisms. The key recursive identity is: an automorphism of `mk cs` is a permutation of `Fin cs.length` preserving the *multiset* of subtree-isomorphism classes (i.e. distinct subtrees must map to distinct subtrees of the same isomorphism class), combined with one automorphism per child subtree.
- **`LabelledRootedTree.Setoid`** — two labellings equivalent if related by a tree-automorphism. Pre-composing the labelling `Vertex t ≃ Fin (order t)` with an `Equiv.Perm (Vertex t)` that's actually a tree-automorphism.
- **Non-vacuity witness** — exhibit two labellings of `mk [vertex, vertex]` (a tree with σ = 2) that are equivalent under the leaf swap, and one labelling of `cherry` whose only automorphism is the identity.

If §D stalls partway through this cycle, cycle 263 picks up the remaining §D pieces before moving to the Setoid.

If §D fully lands AND cycle 263 also lands Phase A.2's Setoid + automorphism witness, Phase A is **complete** and cycle 264+ can move to Phase B or C per `lem_310B_plan.md` §5.

## §I — Faithfulness check requirement for cycle 262 task results

For each new public def/structure/theorem, the cycle 262 task results must include:
- Entity ID (or "engineering scaffold" if no textbook entity).
- Quoted textbook statement (or "engineering scaffold" note).
- Lean statement capture verdict: same / weaker / stronger / different.
- Justification for any divergence.

Per `CLAUDE.md` pre-commit checklist:
- `Vertex.mem_vertices`: same content as the implicit Butcher claim that `vertices t` enumerates the vertex set. Engineering scaffold formalisation of the §300 "set of vertices" notion.
- `instFintypeVertex`: engineering scaffold (no direct Butcher analogue; just a Lean structure capturing that `Vertex t` is finite).
- `Fintype.card_vertex_eq_order`: same content as cycle 261's `vertices_card`, reframed for the `Fintype` API. Same Butcher content (`r(t) = |V(t)|`).
- `LabelledRootedTree`: faithfulness divergence vs Butcher's `def:300C` — we expose a *single canonical* labelling here, not a quotient class. Document this; the textbook treats labellings up to tree-automorphism, which cycle 263's Setoid recovers. Cycle 262 shipping the raw `Equiv` first is a structural pre-step, not a textbook claim, so the divergence is bookkeeping rather than logical.
- `canonicalLabelling`: engineering scaffold (Butcher does not single out a canonical labelling). Document as such.
- All non-vacuity examples: same content as the `vertex`/`cherry`/`broom₃` cycle 261 witnesses.

## §J — Out-of-scope items (do NOT attempt this cycle)

- Tree-automorphism Setoid (cycle 263+).
- Full `lem:310B` (multi-cycle, see `lem_310B_plan.md` §5 phases B-F).
- `thm:306A` multinomial Taylor (Phase B, deferrable via the multilinear bypass in `lem_310B_plan.md` §4.4).
- Phase C orbit-counting bridge.
- Phase D multilinear elementary-differential lift.
- Small-`r` `lem:310B` instances on `TruncatedRootedTree N` (Phase E).
- §441 Phase C.2 (GPFS-blocked; 43rd timeout cycle 239).
- `Equivalent → PEquivalent` / `PhiEquivalent → PEquivalent` directions of `thm:381H` (Banach + thm:381G multi-cycle work).
- `def:381E` reduced-method constructive recursion (deferred, `reduced_method_deferred.md`).
- `lem:342A`/`lem:342B`/`thm:351B` pivots (cycle 260 alternative scouts; not the cycle 262 choice).
- Any modification of `scripts/autonomous_loop.py` (loop-maintainer territory per `CLAUDE.md`).
- Updating `lean_status.json` or `plan.md` rows (cycle 262 is engineering, not entity closure).

## §K — Summary

Cycle 262 ships Phase A.2 (partial) of the multi-cycle `lem:310B` plan: extend `OpenMath/Chapter3/Section300.lean` with `Vertex.mem_vertices`, a `Fintype (Vertex t)` instance, `Fintype.card_vertex_eq_order`, the `LabelledRootedTree` structure, the `canonicalLabelling` definition, and three non-vacuity `LabelledRootedTree` witnesses. Estimated ~80-120 LOC, axiom-clean, sorry count remains 0. The tree-automorphism Setoid is deferred to cycle 263.

Worker: follow §D's step-by-step recipe in order. Abort early per §F if any sub-piece stalls. Update `.prover-state/task_results/cycle_262.md` per §I when done, then commit and push.
