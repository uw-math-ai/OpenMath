# Cycle 343 — strategy

## §A. State at HEAD

Cycle 342 (commit `cbc1aca`) shipped Phase D.1 of `def:422B` cleanly:

* `OpenMath/Chapter4/Section422.lean` is at HEAD, 674 LOC, 0 sorries,
  tautology-scanner clean. Verified with
  `git log -1 -- OpenMath/Chapter4/Section422.lean` (`cbc1aca`) and
  `wc -l` (674).
* New public theorems landed this cycle (all axiom-clean
  `[propext, Classical.choice, Quot.sound]`):
  * `Eq422a_at_vertex_linear` — reduces (422a) at `u = τ` to a linear
    equation in `η(τ)`.
  * `Eq422a_at_vertex_linear_of_isConsistent` — consistency
    strengthening recovering Butcher's textbook η-coefficient.
  * `Eq422a_at_vertex_eta_eq` — closed-form `η(τ) = sum_β / (coef_α +
    coef_β)` under a non-vanishing-coefficient hypothesis.

The supervisor's score=1 for cycle 342 reflects the standing phantom-
verdict bug (`phantom_commit_verdict_pattern.md`) — the work IS at
HEAD. **Do not re-derive Phase D.1.** Trust git state.

§422 multi-phase plan status per `.prover-state/issues/def_422B_path.md`:

* Phase 0 wire-up (cycle 336) — closed.
* Phase A.0 `D` operator pin (cycles 337+338) — closed.
* Phase B `Group.zpow` non-vacuity (cycle 339) — closed.
* Phase C (422a) condition predicate (cycle 340) — closed.
* Phase D pre-infrastructure τ-additivity (cycle 341) — closed.
* **Phase D.1 closed-form `η(τ)` base case (cycle 342) — closed.**
* **Phase D.2 well-founded recursion infrastructure — open (this cycle's target).**
* Phase D.3 inductive step, Phase E lift+seal, Phase F (`thm:422A`)
  — deferred.

## §B. Primary target — Phase D.2 (well-founded recursion on `RootedTree.order`)

Per `def_422B_path.md` §5 row D.2 (60–100 LOC estimate, single cycle,
low–medium risk). The deliverable is the well-founded recursion
infrastructure that Phase D.3's inductive step will consume to
recurse on subtrees by strictly decreasing `RootedTree.order`.

### B.1. What is already in place (verified)

* `OpenMath/Chapter3/Section310.lean:98` — `RootedTree.order : RootedTree → ℕ`
  (mutual with `orderSum : List RootedTree → ℕ`).
* `OpenMath/Chapter3/Section301.lean:159` — `order_pos : ∀ t, 0 < t.order`.
* `OpenMath/Chapter3/Section301.lean:101` — `orderSum_eq_map_sum`.
* `OpenMath/Chapter3/Section301.lean:112` — `order_eq`.
* `OpenMath/Chapter3/Section310.lean:204` — existing `termination_by +
  decreasing_by` pattern using Lean's auto-generated `sizeOf` recursor
  on `RootedTree` (the `theta`/`thetaProd` mutual block at lines
  204–208 already terminates by `sizeOf`).
* `OpenMath/Chapter3/Section301.lean:626` — `TruncatedRootedTree N`
  subtype + `order_le` accessor.

### B.2. What needs to ship in cycle 343

Concrete deliverables in priority order (do **P1 first**, then **P2**;
P3 is documentation-only stretch):

**P1 — `RootedTree.order_lt_of_mem_children` (subtree strict-descent
lemma, ~10–20 LOC).** For `t = mk children` and `c ∈ children`,
`c.order < t.order`. Proof recipe:

* Unfold via `order_eq` (Section301:112) to get
  `t.order = 1 + (children.map RootedTree.order).sum`.
* Bound `c.order ≤ (children.map RootedTree.order).sum` via
  `List.le_sum_of_mem` (or equivalent) applied to `c.order ∈
  (children.map order)` (mem follows from `c ∈ children` via
  `List.mem_map_of_mem`).
* Conclude `c.order < t.order` by adding 1.

If `List.le_sum_of_mem` does not exist verbatim in current Mathlib,
fallback: induct on `children` directly (~15 LOC). Use
`lean_local_search "List.le_sum"` and `lean_loogle "_ ≤ List.sum _"`
to find the right name. **Verify axiom-clean** via `#print axioms`.

**P2 — `WellFoundedRelation` instance via `RootedTree.order` (~10
LOC).** Build

```lean
instance : WellFoundedRelation RootedTree :=
  { rel := fun a b => a.order < b.order
    wf  := InvImage.wf RootedTree.order Nat.lt_wfRel.wf }
```

If `InvImage.wf` namespace has drifted, alternatives to try (use
`lean_local_search`):

* `Subrelation.wf`
* `WellFounded.onFun`
* `measure RootedTree.order` (Mathlib has `measure` as the
  canonical name for `InvImage Nat.lt ...`)

A safer Lean-4 spelling:

```lean
instance : WellFoundedRelation RootedTree :=
  measure RootedTree.order
```

Add two non-vacuity examples:

```lean
example : (RootedTree.vertex).order < (RootedTree.cherry).order := by decide
example : (RootedTree.cherry).order < (RootedTree.broom₃).order := by decide
```

(`vertex`/`cherry`/`broom₃` are defined in Section310; `decide` should
close once `order` definitionally unfolds. If `decide` stalls, fall
back to `simp [RootedTree.order, ...]; norm_num`.)

**P3 (stretch, documentation only — only if P1+P2 close in <60 min;
NO sorry, NO axiom).** Append a `/-- … -/` docstring block to
`Section422.lean` (immediately before the `Eq422a` definition or at
the end of the file) sketching the Phase D.3 inductive-step solver's
target signature. Example block:

```lean
/-!
### Phase D.3 (cycle 344+) preview

The inductive step solver will have a signature similar to:

```
noncomputable def underlyingEta_aux {k : ℕ}
    (M : LinearMultistepMethod k)
    (hPre : M.IsPreconsistent) (hStab : M.IsStable) :
    RootedTree → ℝ
```

terminating by `t.order` (well-founded via `Section301`'s instance).
Base case `t = τ` uses cycle 342's `Eq422a_at_vertex_eta_eq`. The
recursive case at `t = mk children` solves the linear equation in
`η(t)` by substituting `η` at proper sub-trees `c ∈ children`
(strict descent by P1) and at `t = mk children`'s own row.
-/
```

**DO NOT scaffold the `def` with `sorry`** — sorry count must stay at
0 (cycle 149/150, 200/201 rollback precedents).

### B.3. Verification checklist for primary deliverables

After P1+P2 land:

1. `lake env lean OpenMath/Chapter3/Section301.lean` → exit 0.
2. `lake env lean OpenMath/Chapter3.lean` → exit 0 (aggregator).
3. `grep -c sorry OpenMath/Chapter3/Section301.lean` → 0.
4. Tautology scanner clean:
   `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section301.lean`
   → no hits.
5. `#print axioms OpenMath.Chapter3.Section310.RootedTree.order_lt_of_mem_children`
   → `[propext, Classical.choice, Quot.sound]` only (or just
   `[Quot.sound]` if the proof is purely structural).
6. `#print axioms` on the WellFoundedRelation instance → check it
   does NOT depend on `sorryAx`.

### B.4. File placement decision

**Place P1 (`order_lt_of_mem_children`) in
`OpenMath/Chapter3/Section301.lean`** near `order_pos` (line 159) —
it's an intrinsic `RootedTree`-API lemma about `order`, not §422-
specific.

**Place P2 (`WellFoundedRelation` instance) in
`OpenMath/Chapter3/Section301.lean`** immediately after P1. The
instance is reusable infrastructure that future cycles (Phase D.3
plus any other RootedTree-recursive definitions) will consume.

Adding `import OpenMath.Chapter3.Section301` to `Section422.lean` is
already in place (cycle 338); no aggregator changes needed.

If P1+P2 turn out to need machinery only available in `Section310`'s
namespace (unlikely — `Section301` imports `Section310`), place them
there instead. But `Section301` is preferred since it hosts the rest
of the `order` API.

**Namespace**: put both inside `namespace OpenMath.Chapter3.Section310`
(matching the existing `order_pos`'s home) so `RootedTree.order_lt_of_mem_children`
resolves via dot notation.

## §C. Backup plan — stability bridge for `Eq422a_at_vertex_eta_eq`

If P1+P2 stall (Mathlib name drift on `InvImage.wf` etc.) and 30+ min
are spent without progress on the WellFoundedRelation instance,
**pivot to the stability bridge** as the cycle's deliverable.

### C.1. Deliverable

A new public theorem in `OpenMath/Chapter4/Section422.lean` (after
`Eq422a_at_vertex_eta_eq`):

```lean
theorem Eq422a_at_vertex_eta_eq_of_stable_preconsistent
    {k : ℕ} (M : LinearMultistepMethod k) (hk : 0 < k)
    (hStable : M.IsStable) (hPre : M.IsPreconsistent)
    (η_q : Quotient PhiEquivalent.setoidSigma)
    (hEq : Eq422a M η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex
      = sum_β M / (coef_α M + coef_β M)
```

where `sum_β`, `coef_α`, `coef_β` are exactly cycle 342's abbreviations
(worker should grep the cycle 342 source for the canonical naming).

### C.2. Proof recipe

Bridge `coef_α + coef_β ≠ 0` to cycle 178's
`ρPoly_deriv_eval_one_pos_of_stable_preconsistent` (in
`OpenMath/Chapter4/Section441.lean`):

1. Under preconsistency, `coef_α(M) = sum_β(M)` (this is
   `M.SatisfiesEq404b` recast — already used by cycle 342's
   `Eq422a_at_vertex_linear_of_isConsistent`).
2. Cycle 174's `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`
   plus cycle 178's `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`
   imply `coef_α(M) > 0` under stability + preconsistency.
3. `coef_β(M) = Σ_{i : Fin (k+1)} i · M.β i`. The sign of this is NOT
   directly controlled by stability — but if `coef_α > 0` and the
   problem only needs `coef_α + coef_β ≠ 0`, it suffices to show
   `coef_α + coef_β > 0` or to find a different non-vanishing
   argument.
4. Apply `Eq422a_at_vertex_eta_eq` (cycle 342) with the derived
   non-vanishing hypothesis.

### C.3. If C.2 step 3 cannot be discharged

Time-box: if after 30 min of search the `coef_α + coef_β ≠ 0`
inequality cannot be derived from existing §441 infrastructure +
preconsistency, **abandon the stability bridge** and either:

* Fall back to backup §D (Phase D.3 small-tree manual case), OR
* Accept Phase D.2 deferral and ship a smaller P1-only deliverable
  (just `order_lt_of_mem_children`, ~15 LOC, axiom-clean) as the
  cycle's only ship. P1 alone is a useful infrastructure lemma even
  without P2.

Document the dead end in this strategy file's epilogue so cycle 344+
planners know the gap.

## §D. Tertiary backup — manual closed-form at `u = cherry`

Only if BOTH §B and §C stall.

* Specialize `Eq422a M η_q` at `u = cherry := mk [vertex]` (already
  defined in Section310).
* Derive a `cherry`-specific analogue of cycle 341 P1/P2/P3 (additivity
  of `elementaryWeightQ_phi` at `cherry`) — but note: cycle 341's
  P1/P2/P3 are stated for `u = vertex` and use the specific
  combinatorial structure of `RootedTree.vertex` (a leaf, so
  `derivativeWeightWithSrc` recursion bottoms out at the empty-list
  base case). At `cherry = mk [vertex]`, the recursion descends one
  step into `vertex` — so the cherry-specific lemmas would be:
  `elementaryWeightQ_phi (η_q · D) cherry =
   elementaryWeightQ_phi η_q vertex` (since `D` collapses the leaf),
  plus the analogous mul/inv/zpow rules.
* Solve for `η(cherry)` in terms of `η(τ)` (cycle 342) plus `M.α`,
  `M.β`.

This is ~150 LOC scope and is the natural Phase D.3 entry point;
only ship in cycle 343 if §B and §C are both blocked. Otherwise defer
to cycle 344.

## §E. What NOT to do this cycle

* **DO NOT attempt the Phase D.3 inductive step in full** (multi-cycle,
  ~150–300 LOC per `def_422B_path.md` §5 row D.3). The single-tree
  manual case (§D backup) is the only Phase D.3 work appropriate
  for one cycle.
* **DO NOT re-derive cycle 342 Phase D.1 work.** It is at HEAD,
  axiom-clean, verified. The phantom commit verdict is a
  supervisor-side bug (`phantom_commit_verdict_pattern.md`).
* **DO NOT submit Aristotle jobs.** Phase D.2 is structural Lean
  type-class engineering, not premise selection — Aristotle's
  strength does not apply here. Cycle 342 strategy explicitly
  forbade Aristotle for the same reason; same logic holds.
* **DO NOT change file placement of cycle 342 deliverables.** Keep
  `Eq422a_at_vertex_linear` and its corollaries where they are.
* **DO NOT pivot to a fresh entity.** Cycle 342 task results §F
  notes "pivot pressure starts mounting" but Phase D.2/D.3 are still
  ~2-3 cycles from sealing `def:422B`. Finish the streak. Pivot
  candidates in `cycle_336_pivot_options.md` and
  `def_422B_path.md` §8 remain available for cycle 346+ if needed.
* **DO NOT raise `maxHeartbeats` above 200000.** None of the Phase
  D.2 work approaches that limit.
* **DO NOT introduce sorry / axiom / constant.** Phase D.2
  deliverables must be axiom-clean per project rules. The cycle
  149/150 (`def:530B` Path A scaffold) and 200/201 (`thm:381H`
  sorry-first scaffold) rollback precedents apply here too.
* **DO NOT add the P3 stretch as a `def ... := sorry`** scaffold.
  Sorry count must remain 0. P3 is documentation-only (Lean-comment
  block).
* **DO NOT attempt to compile `Section441.lean` locally.** 43+
  consecutive GPFS timeouts since cycle 182 per
  `cycle_182_gpfs_slowness.md`. The stability bridge backup (§C) can
  cite cycle 178's symbols by name without recompiling §441.
* **DO NOT edit `scripts/autonomous_loop.py`.** Phantom-verdict
  remediation is loop-maintainer territory.

## §F. Faithfulness considerations

For each new public symbol introduced:

* **P1 `order_lt_of_mem_children`**: pure `RootedTree`-API lemma. Not
  a textbook-named entity; no faithfulness divergence concern.
* **P2 `WellFoundedRelation RootedTree` instance**: Lean-engineering
  scaffold. No textbook analogue.
* **P3 (if shipped as docstring)**: documentation only, no code
  obligation.

Backup C deliverable `Eq422a_at_vertex_eta_eq_of_stable_preconsistent`:
strict strengthening of cycle 342's `Eq422a_at_vertex_eta_eq` (drops
the explicit `coef_α + coef_β ≠ 0` hypothesis in favor of `IsStable +
IsPreconsistent`). This matches Butcher §422 p. 1163's textbook
implicit "by stability the coefficient is non-zero" — surfacing
that bridge explicitly is a faithfulness improvement.

Backup D deliverable `Eq422a_at_cherry_*`: specialization of the
(422a) condition at a specific order-2 tree. Honest specialization
of cycle 340's `Eq422a`, no faithfulness concern.

## §G. Cycle 343 ship checklist

1. (5 min) Verify §A's HEAD state. Run
   `git log -1 -- OpenMath/Chapter4/Section422.lean` and confirm
   `cbc1aca`. `wc -l OpenMath/Chapter4/Section422.lean` should give
   674. Skip if both match.
2. (10 min) Verify §B.1 hooks exist at expected lines via
   `grep -n` on Section301.lean / Section310.lean.
3. (60–80 min) Ship P1 + P2 (§B.2). Place in
   `OpenMath/Chapter3/Section301.lean` per §B.4.
4. (5–10 min) Verify axiom-clean (§B.3 checklist).
5. (10 min) Update `.prover-state/issues/def_422B_path.md` §5 with
   cycle 343 closure note (Phase D.2 closed; cycle 344 starts
   Phase D.3).
6. (5 min) Write `.prover-state/task_results/cycle_343.md`.
7. Commit. Branch tip should advance to cycle 343's commit.

If §B stalls per §C.3 timeout, time-box at 30 min and pivot to §C
(stability bridge) or §D (manual cherry case) as documented.

## §H. Expected output

* **Best case (P1+P2 land)**: cycle 343 closes Phase D.2 of `def:422B`
  in ~30–40 LOC. `Section301.lean` grows ~25–35 LOC; nothing else
  changes. `def:422B` row in `lean_status.json` stays `partial`
  (Phase D.3 / E / F remain). Cycle 344 attempts Phase D.3.
* **P1+P2+P3 stretch**: same as best case plus a Phase D.3 signature
  docstring-only sketch in `Section422.lean`.
* **Backup C (stability bridge)**: cycle 343 closes a strengthening
  of cycle 342's `Eq422a_at_vertex_eta_eq`. `def:422B` stays `partial`;
  Phase D.2 deferred to cycle 344.
* **Backup D (manual cherry)**: cycle 343 ships the order-2 manual
  case as a Phase D.3 stepping stone. `def:422B` stays `partial`;
  Phase D.2 deferred.

In all cases: 0 sorries, axiom-clean, no faithfulness divergences
introduced beyond those documented in §F.

## §I. Cross-references

* `.prover-state/issues/def_422B_path.md` §5 row D.2 — the Phase D.2
  spec (60–100 LOC, single cycle, low–medium risk).
* `.prover-state/task_results/cycle_342.md` §"Suggested next
  approach" — worker's three-option recommendation; this strategy
  picks option 1 (Phase D.2) with option 2 (stability bridge) as
  backup.
* `.prover-state/issues/phantom_commit_verdict_pattern.md` — standing
  supervisor-side bug; not actionable from worker side.
* `OpenMath/Chapter3/Section301.lean:159` (`order_pos`),
  `:101` (`orderSum_eq_map_sum`), `:112` (`order_eq`) — existing
  RootedTree.order API the P1 lemma will compose with.
* `OpenMath/Chapter3/Section310.lean:204` — existing
  `termination_by + decreasing_by` pattern (uses `sizeOf`; P2 builds
  the order-based `WellFoundedRelation` for future consumers that
  prefer `order` over `sizeOf`).
