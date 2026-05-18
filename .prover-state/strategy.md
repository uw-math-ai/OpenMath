# Cycle 375 Strategy — §422 Sub-lemma A Phase β.1 ship

## §A Recommendation

Ship **Phase β.1** of `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md`:
prove the bridge lemma
`elementaryWeightQ_phi η_q⁻¹ t = inversePolynomial t (elementaryWeightQ_phi η_q)`
on the four trees matched by cycle 374's `inversePolynomial` pattern
match (`vertex`, `cherry`, `broom₃`, `mk [cherry]`).

This is the strict cycle 374 → 375 continuation that the scoping doc
and cycle 374 task results both anticipated. Each case reduces to the
corresponding cycle 341 P2 / 367 / 368 / 369 closed-form theorem via
`unfold inversePolynomial` + `if_*` rewrites.

## §B Context

Cycle 374 shipped (axiom-clean, `OpenMath/Chapter4/Section422.lean`
lines 4187–4309):

* `inversePolynomial : RT → (RT → ℝ) → ℝ` — explicit `if-then-else`
  cascade matching `vertex` ↦ `-(f vertex)`, `cherry` ↦
  `(f vertex)^2 - f cherry`, `broom₃` ↦
  `-(f vertex)^3 + 2·f vertex·f cherry - f broom₃`, `mk [cherry]` ↦
  `-(f vertex)^3 + 2·f vertex·f cherry - f (mk [cherry])`, with `0`
  default for all other trees.
* Four calibration `example`s confirming each branch evaluates as
  expected.

Cycle 374 task results §"Suggested next approach" explicitly
recommends Option A (Phase β.1 on four-tree ladder) as the cycle 375
target.

The four closed-form theorems Phase β.1 will consume are all
shipped and axiom-clean:

| Tree         | Theorem name                        | Approx. line | Cycle |
|--------------|-------------------------------------|--------------|-------|
| `vertex`     | `elementaryWeightQ_phi_inv_vertex`  | ~415         | 341   |
| `cherry`     | `elementaryWeightQ_phi_inv_cherry`  | 2376         | 367   |
| `broom₃`     | `elementaryWeightQ_phi_inv_broom₃`  | 2538         | 368   |
| `mk [cherry]`| `elementaryWeightQ_phi_inv_mkCherry`| 2772         | 369   |

## §C Concrete deliverables

Add four named theorems to `OpenMath/Chapter4/Section422.lean`,
appended just after the cycle 374 calibration block (after line
~4309, before the closing `end OpenMath.Chapter4.Section422`).

### C.1 — `elementaryWeightQ_phi_inv_eq_inversePolynomial_vertex`

```lean
theorem elementaryWeightQ_phi_inv_eq_inversePolynomial_vertex
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi η_q⁻¹ RootedTree.vertex
      = inversePolynomial RootedTree.vertex (elementaryWeightQ_phi η_q) := by
  unfold inversePolynomial
  rw [if_pos rfl]
  exact elementaryWeightQ_phi_inv_vertex η_q
```

### C.2 — `elementaryWeightQ_phi_inv_eq_inversePolynomial_cherry`

```lean
theorem elementaryWeightQ_phi_inv_eq_inversePolynomial_cherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi η_q⁻¹ RootedTree.cherry
      = inversePolynomial RootedTree.cherry (elementaryWeightQ_phi η_q) := by
  unfold inversePolynomial
  rw [if_neg (by decide), if_pos rfl]
  exact elementaryWeightQ_phi_inv_cherry η_q
```

### C.3 — `elementaryWeightQ_phi_inv_eq_inversePolynomial_broom₃`

Same recipe with two `if_neg (by decide)` before `if_pos rfl`,
closing by `elementaryWeightQ_phi_inv_broom₃`.

### C.4 — `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkCherry`

Same recipe with three `if_neg (by decide)` before `if_pos rfl`,
closing by `elementaryWeightQ_phi_inv_mkCherry`.

**Important — name resolution**: at the top level of `Section422.lean`,
`RootedTree.mk [RootedTree.cherry]` written naively may resolve to
*Mathlib's* `_root_.RootedTree`, NOT our
`OpenMath.Chapter3.Section310.RootedTree`. Per cycle 374 Discovery #1,
fully qualify:
`OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]`
when writing `mk [cherry]` literals in theorem statements. Matches the
convention at `Section422.lean:2774`.

### C.5 — Optional stretch: aggregator theorem

If the four ladder theorems land cleanly, optionally also ship:

```lean
theorem elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder
    (η_q : Quotient PhiEquivalent.setoidSigma) (t : RT)
    (ht : t = RootedTree.vertex ∨ t = RootedTree.cherry
        ∨ t = RootedTree.broom₃
        ∨ t = OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.cherry]) :
    elementaryWeightQ_phi η_q⁻¹ t
      = inversePolynomial t (elementaryWeightQ_phi η_q) := by
  rcases ht with h | h | h | h <;> subst h
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_vertex η_q
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_cherry η_q
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_broom₃ η_q
  · exact elementaryWeightQ_phi_inv_eq_inversePolynomial_mkCherry η_q
```

This packages all four as a "Phase β.1 done on the matched ladder"
single named theorem for downstream consumers.

### C.6 — LOC and verification

LOC budget: ~50–80 LOC total (10–15 LOC per theorem × 4, plus
optional aggregator ~15 LOC).

Verification:

1. `lake env lean OpenMath/Chapter4/Section422.lean` — must exit clean.
2. `lake build OpenMath.Chapter4.Section422` — must rebuild clean.
3. `grep -c sorry OpenMath/Chapter4/Section422.lean` — must remain
   at 5 lines (1 code sorry + 4 docstring mentions), unchanged.
4. `#print axioms` on each new theorem (via a temporary RT-aliased
   check file per cycle 374 Dead End #2) must return
   `[propext, Classical.choice, Quot.sound]` only.

## §D What NOT to do

* **Do NOT pursue Option B (Phase α.2 expansion)** — extending
  `inversePolynomial` to `bushy`, `mk [broom₃]`, `mk [vertex, cherry]`
  is strictly easier but provides less Phase β progress. Cycle 374
  task results §"Suggested next approach" recommends Option A first.
* **Do NOT pursue Option C (well-founded recursion refinement)** —
  multi-cycle research, risks partial scaffold under single-cycle
  budget. Per cycle 374 task results, "Recommended only if Options
  A and B are both judged exhausted."
* **Do NOT discharge the cycle 365 grandfathered sorry** at line
  ~2279 (`powRep_sum_eq_of_strict_subtree_agreement`). It is still
  Phase ε, projected cycle 378+. Leave untouched.
* **Do NOT pivot to a fresh entity**. `def:422B` is the active
  multi-cycle target; pivoting now wastes both cycle 373 scoping
  and cycle 374 ship investment.
* **Do NOT add new sorries** beyond the cycle 365 grandfathered one.
  The streak is at 39 substantive + 1 doc consecutive axiom-clean
  cycles since 336; preserve it.
* **Do NOT use bare `RootedTree.mk [...]`** at the top level — it
  resolves to Mathlib's `_root_.RootedTree`. Use full qualification
  `OpenMath.Chapter3.Section310.RootedTree.mk [...]` per cycle 374
  Discovery #1.
* **Do NOT use `simp [inversePolynomial]`** as a one-shot — the
  pattern is `unfold inversePolynomial; rw [if_neg, if_neg, …,
  if_pos rfl]` per cycle 374's calibration examples (the cycle 374
  worker established this works cleanly; `simp` may over-normalize).
* **Do NOT raise `maxHeartbeats`** above 200000.
* **Do NOT edit `scripts/autonomous_loop.py`** — loop-maintainer
  territory.
* **Do NOT attempt Section441 compile** — 43+ GPFS timeouts since
  cycle 182, per `.prover-state/issues/cycle_182_gpfs_slowness.md`.

## §E Approaches already ruled out (do NOT retry)

From `def_422B_phase_D_3_scoping.md` (cycle 366 update, lines
1346–1407) — these failed for closing **Sub-lemma A's general body**
and are documented here so cycle 375 does not retry them:

1. Direct `Quotient.inductionOn₂` on η_q and η_q' + cycle 358
   `_inv_mk` expansion fails because the two `(M.powRep (m+1)).2.b j
   · M.derivativeWeightWithSrc M.inverse j t` sums range over
   different `Fin` types when `M.1 ≠ M'.1`. Cycle 362's
   `derivativeWeightWithSrc_eq_of_strict_subtree_agreement` only
   substitutes the **source** tableau, not the inner one.
2. Strong induction on `t.order` using cycle 362 alone fails for
   the same reason (inner-tableau heterogeneity).

**These are NOT cycle 375's concern**. Cycle 375 ships Phase β.1
(per-tree bridge lemmas) using `inversePolynomial`'s explicit
pattern match — sidestepping the heterogeneity issue entirely
because the bridge is stated and proved tree-by-tree, not via the
recursive substitution argument.

## §F Pre-flight checks before writing Lean code

1. **Verify cycle 341's vertex theorem name**: `grep -n
   "elementaryWeightQ_phi_inv_vertex" OpenMath/Chapter4/Section422.lean`
   to confirm exact name and signature. The cycle 374 calibration
   example for `vertex` should give a working call template.
2. **Verify cycle 367/368/369 theorem signatures**: each is
   `(η_q : Quotient PhiEquivalent.setoidSigma) : ...` — confirm
   that's the only argument needed (no `M` representative
   destructuring at the call site).
3. **Confirm `by decide` fires on each `RootedTree` inequality**:
   `vertex ≠ cherry`, `vertex ≠ broom₃`, `vertex ≠ mk [cherry]`,
   `cherry ≠ broom₃`, `cherry ≠ mk [cherry]`, `broom₃ ≠ mk [cherry]`.
   Cycle 374 used `by decide` successfully on all four trees in
   calibration examples; cycle 375 should hit the same pattern.
4. **Confirm the four cycle 374 calibration `example`s compile**
   (they should be unchanged at HEAD; if a downstream edit broke
   them, address that first).

## §G Risk assessment

| Risk | Severity | Mitigation |
|---|---|---|
| `RootedTree.mk` name resolution to Mathlib | medium | Full qualification per cycle 374 Discovery #1 (§C.4 above) |
| `by decide` fails on a `RootedTree` inequality | low | Fall back to `injection h with hidx _; exact absurd hidx (by decide)` or `cases h` per memory `feedback_indexed_inductive_cases_disjoint.md` |
| Cycle 341/367/368/369 theorem signature drift | low | Pre-flight check §F.1–F.2 catches this |
| `unfold inversePolynomial` doesn't unfold | low | The cycle 374 calibration examples confirm it works; if it fails, the cycle 374 ship is broken which would be a regression bug |
| Aggregator theorem (C.5) syntax issue | low | Optional stretch; ship the four primary theorems first, then aggregator |

All risks are LOW or MEDIUM with known mitigations. No HIGH-risk
items.

## §H Exit criteria

Cycle 375 succeeds when:

1. Four new theorems (`_vertex`, `_cherry`, `_broom₃`, `_mkCherry`
   variants of the bridge) shipped axiom-clean.
2. Optional aggregator theorem shipped axiom-clean (or deferred).
3. `lake build OpenMath.Chapter4.Section422` clean exit.
4. Sorry count unchanged (still 5 lines / 1 code sorry).
5. §422 axiom-clean streak advances to 40 substantive + 1 doc.
6. `task_results/cycle_375.md` written with full faithfulness
   check section.
7. `def_422B_subLemmaA_inductive_plan.md` §10 (or equivalent
   per-cycle update section) updated with the Phase β.1 closure
   note matching cycle 374's update style.

## §I Cycle 376 outlook

If cycle 375 closes Phase β.1 cleanly, cycle 376 has two natural
paths per `def_422B_subLemmaA_inductive_plan.md` §5–§7:

* **Phase β.2 (1 cycle)**: clean up the recursive bridging if cycle
  358 `_inv_mk` requires intermediate lemmas to align with the Phase
  α recursive shape. Likely a `Quotient.lift` plumbing step. Only
  needed if Phase β.1 hits an unexpected obstacle (no obstacle
  anticipated since the four bridges are atomic per-tree).
* **Phase γ (1 cycle)**:
  `inversePolynomial_eq_of_subtree_agreement` — pure structural
  induction on Phase α's recursion. If `inversePolynomial` were
  recursive (Phase α' form), this would be the standard
  agreement-of-strict-subtrees argument. With the pattern-match
  form, this reduces to four trivial case-splits (each branch's
  RHS depends only on `f` at strict subtrees of the matched tree,
  by inspection). Likely shorter than Phase β.1.

Cycle 376 planner should consult `def_422B_subLemmaA_inductive_plan.md`
§5 phase decomposition. Total horizon: Phase β/γ/δ/ε projected for
cycles 376–379 if each ships in a single cycle.

## §J Bottom-line directive

Cycle 375 ships Phase β.1: four per-tree bridge lemmas
`elementaryWeightQ_phi_inv_eq_inversePolynomial_<tree>` for
`<tree> ∈ {vertex, cherry, broom₃, mkCherry}`. Each ~10 LOC,
axiom-clean, `unfold + if_* rewrites + exact <cycle ladder
theorem>`. Sorry count unchanged. Streak preserved at 40
substantive + 1 doc.
