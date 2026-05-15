# Cycle 269 Strategy — §310/§311 Phase E.1 order-5 (Phase 1 of 2):
# nine new per-tree `bseriesExactTerm_*_scalar` closed forms

## §0 Where we are

Cycle 268 shipped Phase E.1 of `.prover-state/issues/lem_310B_plan.md`
at order 4 (scalar `ℝ → ℝ`):

* `bseriesExactTerm_bushy_scalar` (h⁴/24 · f'''·f³)
* `bseriesExactTerm_mkVertexCherry_scalar` (h⁴/8 · f''·f'·f²)
* `bseriesExactTerm_mkBroom₃_scalar` (h⁴/24 · f'·f''·f²; σ(mk [broom₃]) = 2)
* `bseriesExactTerm_mkMkCherry_scalar` (h⁴/24 · (f')³·f)
* `lem_311A_order_four_partialSum` (bridge to cycle 258's order-4
  closed-form polynomial via 8-tree `bseriesExactPartialSum`)

All five axiom-clean (`[propext, Classical.choice, Quot.sound]`).
Sorry count: **0** across the whole repo. No blocker in the
"What I'm stuck on" field; no pending Aristotle results.

Branch tip: `4c92bf7 Cycle 268 — §310/§311 Phase E.1 order-4
partial-sum bridge SHIPPED.`

Cycle 268 task-results §"Suggested next approach" priority:

1. **Order-5 partial-sum bridge** (LOW risk, mechanical) ← TARGETED
2. Polymorphic-`E` lift (MEDIUM-HIGH risk, multilinear plumbing)
3. Pivot to `lem:342A` (single-cycle independent target)

Order-5 closure is the deliberate cutoff from cycle 259
(`iteratedDeriv_five_via_ode` ladder ends there) and provides a
**clean narrative stopping point**: Phase E.1 closes at the same
order as cycle 259's `lem_311A_order_five` itself. After cycle 270
ships the 17-tree bridge, the planner pivots — either to `lem:342A`,
or to polymorphic-`E` lifting (Phase D.2 / E.2), or to a fresh
chapter.

## §A Cycle 269 deliverable: 9 new per-tree closed forms

Per the LOC trajectory of cycles 266–268, the order-5 work cannot
fit in one cycle:

| cycle | trees added | bridge trees | LOC |
|-------|-------------|--------------|-----|
| 266   | 1 (cherry)  | 2 (order-2)  | ~230 |
| 267   | 2           | 4 (order-3)  | ~210 |
| 268   | 4           | 8 (order-4)  | ~492 |
| 269 (this) | **9**  | **DEFER**    | est. ~450 |
| 270 (next) | 0      | 17 (order-5) | est. ~500 |

**Cycle 269 ships only the per-tree closed forms.** The 17-tree
partial-sum bridge `lem_311A_order_five_partialSum` is deferred to
cycle 270.

Rationale: cycle 268's bridge alone was ~290 LOC for 8 trees with
7 non-membership lemmas; extending to 17 trees with 16 non-membership
lemmas pushes the combined deliverable well past 1000 LOC. Splitting
keeps both cycles within the working envelope and gives cycle 270
a single concentrated target.

## §B The 9 order-5 trees and their closed forms (verified)

All nine trees have `r = 5`. Coefficients computed below were
**verified by hand** against cycle 259's `lem_311A_order_five`
Bell coefficients `(1, 7, 4, 11, 1)`. The σ-recursion was applied
carefully — multi-child cases (T2, T3, T5) and one-child cases
(T6, T7, T8, T9) follow different patterns of
`σ(mk children) = ∏_{distinct subtree types} mᵢ! · σ(tᵢ)^{mᵢ}`.

| # | Tree | r | σ | γ | coef · h⁵ | Elementary differential (scalar) |
|---|------|---|---|---|-----------|-----------------------------------|
| T1 | `mk [v,v,v,v]` | 5 | 4!=24 | 5 | h⁵/120 | f''''·f⁴ |
| T2 | `mk [v,v,cherry]` | 5 | 2 | 10 | h⁵/20 | f'''·f'·f³ |
| T3 | `mk [v,broom₃]` | 5 | 2 | 15 | h⁵/30 | (f'')²·f³ |
| T4 | `mk [v,mk [cherry]]` | 5 | 1 | 30 | h⁵/30 | f''·(f')²·f² |
| T5 | `mk [cherry,cherry]` | 5 | 2 | 20 | h⁵/40 | f''·(f')²·f² |
| T6 | `mk [bushy]` | 5 | 6 | 20 | h⁵/120 | f'''·f'·f³ |
| T7 | `mk [mk [v,cherry]]` | 5 | 1 | 40 | h⁵/40 | f''·(f')²·f² |
| T8 | `mk [mk [broom₃]]` | 5 | 2 | 60 | h⁵/120 | f''·(f')²·f² |
| T9 | `mk [mk [mk [cherry]]]` | 5 | 1 | 120 | h⁵/120 | (f')⁴·f |

**Faithfulness re-derivation** (worker MUST verify):

* σ(mk [broom₃]) = 2 (cycle 268 P3 caught this — propagates here to T8).
  σ recursion at one-child trees: `σ(mk [t]) = 1!·σ(t)^1 = σ(t)`.
  So σ(mk [broom₃]) = σ(broom₃) = 2!·σ(v)² = 2. ✓
* σ(mk [mk [broom₃]]) = σ(mk [broom₃]) = 2. ← T8 coefficient `1/(2·60) = 1/120`,
  **not** `1/60`.
* σ(mk [v,broom₃]) = `1!·σ(v)·1!·σ(broom₃)` = `1·1·1·2` = 2. ← T3 coefficient `1/(2·15)`.
* σ(bushy) = σ(mk [v,v,v]) = `3!·σ(v)³` = 6. (Verified by existing example
  at `Section301.lean`.)
* σ(mk [bushy]) = σ(bushy) = 6 (one-child rule). T6 coefficient `1/(6·20) = 1/120`.
* σ(mk [v,v,cherry]) = `2!·σ(v)²·1!·σ(cherry)¹` = `2·1·1·1` = 2.
* σ(mk [cherry,cherry]) = `2!·σ(cherry)²` = `2·1` = 2.

**Coefficient sums by monomial** (cross-check vs cycle 259):

| Monomial | Trees | Contributions (·h⁵/120) | Total (cycle 259) |
|----------|-------|--------------------------|---------------------|
| f''''·f⁴ | T1 | 1 | **1** ✓ |
| f'''·f'·f³ | T2, T6 | 6 + 1 | **7** ✓ |
| (f'')²·f³ | T3 | 4 | **4** ✓ |
| f''·(f')²·f² | T4, T5, T7, T8 | 4 + 3 + 3 + 1 | **11** ✓ |
| (f')⁴·f | T9 | 1 | **1** ✓ |

All five sums match `lem_311A_order_five`'s Bell coefficients `(1, 7, 4, 11, 1)`
verbatim. ✓

## §C Deliverables (P1–P10)

All theorem deliverables land in `OpenMath/Chapter3/Section301.lean`
inside the existing `namespace OpenMath.Chapter3.Section310.RootedTree`
block, immediately after cycle 268's `bseriesExactTerm_mkMkCherry_scalar`
and **before** the existing `bseriesExactPartialSum` block (so the new
per-tree facts are available to cycle 270's bridge work).

Plus one new `def` alias at `Section310.lean` (sister to existing
`vertex`, `cherry`, `broom₃`, `bushy` from cycle 268).

### P1. `Section310.lean` — `bushy₄` alias

```lean
/-- `[τ, τ, τ, τ]`: the order-5 tree with four leaves attached to the root.
Sister to the cycle 268 alias `bushy = mk [vertex, vertex, vertex]`. -/
def bushy₄ : RootedTree := mk [vertex, vertex, vertex, vertex]
```

Optional but recommended for symmetry with cycle 268's naming.
Alternative is to inline `mk [vertex, vertex, vertex, vertex]` at each
T1 call site.

### P2–P10. Per-tree closed forms in `Section301.lean`

Each follows the cycle 268 mechanical recipe (§E below). State the
theorem precisely, then prove via `unfold` + (order, σ, γ) `rfl`-reduce
+ `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` at the appropriate
depth + `Fin.prod_univ_n` + nested `iteratedDeriv_succ` + final `ring`.

| Deliverable | Theorem | Tree | Closed form |
|-------------|---------|------|-------------|
| P2 | `bseriesExactTerm_bushy₄_scalar` | T1 | `h^5 / 120 * (iteratedDeriv 4 f y₀ * (f y₀)^4)` |
| P3 | `bseriesExactTerm_mkVertexVertexCherry_scalar` | T2 | `h^5 / 20 * (iteratedDeriv 3 f y₀ * deriv f y₀ * (f y₀)^3)` |
| P4 | `bseriesExactTerm_mkVertexBroom₃_scalar` | T3 | `h^5 / 30 * ((iteratedDeriv 2 f y₀)^2 * (f y₀)^3)` |
| P5 | `bseriesExactTerm_mkVertexMkCherry_scalar` | T4 | `h^5 / 30 * (iteratedDeriv 2 f y₀ * (deriv f y₀)^2 * (f y₀)^2)` |
| P6 | `bseriesExactTerm_mkCherryCherry_scalar` | T5 | `h^5 / 40 * (iteratedDeriv 2 f y₀ * (deriv f y₀)^2 * (f y₀)^2)` |
| P7 | `bseriesExactTerm_mkBushy_scalar` | T6 | `h^5 / 120 * (iteratedDeriv 3 f y₀ * deriv f y₀ * (f y₀)^3)` |
| P8 | `bseriesExactTerm_mkMkVertexCherry_scalar` | T7 | `h^5 / 40 * (iteratedDeriv 2 f y₀ * (deriv f y₀)^2 * (f y₀)^2)` |
| P9 | `bseriesExactTerm_mkMkBroom₃_scalar` | T8 | `h^5 / 120 * (iteratedDeriv 2 f y₀ * (deriv f y₀)^2 * (f y₀)^2)` |
| P10 | `bseriesExactTerm_mkMkMkCherry_scalar` | T9 | `h^5 / 120 * ((deriv f y₀)^4 * f y₀)` |

**Type signature template** (uniform across P2–P10):

```lean
theorem bseriesExactTerm_<name>_scalar (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h <tree> = <closed-form> := by
  …
```

No `ContDiff` hypothesis is needed: `bseriesExactTerm` is a definitional
expression in `iteratedFDeriv ℝ n f y₀`, and `iteratedFDeriv` is defined
unconditionally (returning the zero multilinear map if `f` is not
differentiable enough). The scalar collapse via
`iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` works at the
definitional level. Compare cycle 268's `bseriesExactTerm_bushy_scalar`
signature — no hypotheses.

## §D Recommended ordering

1. **P1** (bushy₄ alias) — trivial single-line `def`. Compile
   `Section310.lean` to refresh the olean cache before consumers fire.
2. **P2** (T1, bushy₄) — depth-4 outer iteratedFDeriv. Use
   `Fin.prod_univ_four`; if missing in Mathlib, fall back to
   `Fin.prod_univ_succ` × 3 + `Fin.prod_univ_zero`. Validates the
   depth-4 pattern.
3. **P10** (T9, mk[mk[mk[cherry]]]) — deepest nesting, all single-child
   σ=1, simplest algebraically. Closing this early validates the
   multi-level cherry chain via three nested `iteratedFDeriv ℝ 1`
   applications.
4. **P4** (T3, mk[v,broom₃]) — σ-faithfulness checkpoint at multi-distinct
   children (σ=2 from `1!·σ(v)·1!·σ(broom₃) = 2`).
5. **P7** (T6, mk[bushy]) — single-child σ=σ(bushy)=6, exercises the
   one-child rule at the largest σ value among the 9.
6. **P9** (T8, mk[mk[broom₃]]) — σ=2 propagated through TWO one-child
   wrappers. The most delicate σ check (and the load-bearing cycle 268
   precedent).
7. **P8** (T7, mk[mk[v,cherry]]) — single-child wrapping a multi-child.
8. **P3** (T2, mk[v,v,cherry]) — multi-distinct-children with cherry,
   the trickiest depth-3 outer recipe.
9. **P5** (T4, mk[v,mk[cherry]]) — depth-2 outer with one-child inner.
10. **P6** (T5, mk[cherry,cherry]) — depth-2 outer with two identical
    cherries (σ=2 from `2!·σ(cherry)² = 2`).

This ordering front-loads σ-faithfulness sanity (P4, P7, P9 are σ ≠ 1
cases) and saves the trickiest multi-child outer recipes (P3, P5, P6)
for last when the worker has matured the pattern on the easier cases.

## §E Mechanical recipe (cycle 267/268 template, scaled to order 5)

For each `bseriesExactTerm_<tree>_scalar` theorem:

```lean
theorem bseriesExactTerm_<tree>_scalar (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h <tree>
      = h^5 / <σ·γ> * <closed-form-monomial> := by
  unfold bseriesExactTerm <any-tree-aliases-used>
  -- Rfl-reduce (order, σ, γ):
  have horder : order <tree> = 5 := rfl
  have hσ : symmetry <tree> = <σ-value> := rfl
  have hγ : density <tree> = <γ-value> := rfl
  rw [horder, hσ, hγ]
  -- Establish elementaryDiff closed form (inline or via private helper):
  show (h^5 / ((<σ-value> : ℝ) * <γ-value>)) • elementaryDiff f y₀ <tree>
        = h^5 / <σ·γ> * <monomial>
  rw [show elementaryDiff f y₀ <tree> = <scalar-ED-expression> from ?_]
  · -- Final scalar arithmetic
    push_cast
    ring
  · -- Substep: prove the elementaryDiff equality
    -- For depth-N outer iteratedFDeriv, apply:
    --   iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod
    --   Fin.prod_univ_N
    --   iteratedFDeriv_zero_apply (for vertex children)
    --   inner sub-lemmas for non-vertex children (cherry, broom₃,
    --     mk[cherry], broom₃, mk[v,cherry], etc.).
    -- For one-child trees mk [t], use iteratedFDeriv ℝ 1 ... =
    --   fderiv ℝ f y₀ (ED(t)) = deriv f y₀ • ED(t) (scalar)
    -- via iteratedFDeriv_one_apply + fderiv_eq_smul_deriv + smul_eq_mul
    -- (cycle 266 recipe).
    …
```

**Key Mathlib hooks** (all verified at HEAD by cycles 266/267/268):

* `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` —
  `iteratedFDeriv ℝ n f y₀ m = (∏ i, m i) • iteratedDeriv n f y₀`.
  In `Mathlib.Analysis.Calculus.IteratedDeriv.Defs`.
* `iteratedFDeriv_zero_apply` — `iteratedFDeriv ℝ 0 f y₀ m = f y₀`.
* `iteratedFDeriv_one_apply` + `fderiv_eq_smul_deriv` + `smul_eq_mul` —
  the order-1 recipe from cycle 266.
* `Fin.prod_univ_one`, `Fin.prod_univ_two`, `Fin.prod_univ_three` —
  in `Mathlib.Algebra.BigOperators.Fin`.
* `Fin.prod_univ_four` — verify via `lean_local_search "Fin.prod_univ"`.
  If missing, fall back to `Fin.prod_univ_succ` × 3 + `Fin.prod_univ_zero`.
* `iteratedDeriv_succ`, `iteratedDeriv_one` — derivative unfolding.

**Concrete elementaryDiff closed forms to use** (re-derived inline,
or quoted from earlier cycle's theorem if available):

* ED(vertex) on scalars = `f y₀` (trivially).
* ED(cherry) on scalars = `deriv f y₀ * f y₀` (cycle 266).
* ED(broom₃) on scalars = `iteratedDeriv 2 f y₀ * (f y₀)^2` (cycle 267).
* ED(mk[cherry]) on scalars = `(deriv f y₀)^2 * f y₀` (cycle 267).
* ED(bushy) on scalars = `iteratedDeriv 3 f y₀ * (f y₀)^3` (cycle 268).
* ED(mk[v,cherry]) on scalars = `iteratedDeriv 2 f y₀ * deriv f y₀ * (f y₀)^2` (cycle 268).
* ED(mk[broom₃]) on scalars = `deriv f y₀ * iteratedDeriv 2 f y₀ * (f y₀)^2` (cycle 268).
* ED(mk[mk[cherry]]) on scalars = `(deriv f y₀)^3 * f y₀` (cycle 268).

These eight ED closed forms are NOT stated as standalone lemmas at
HEAD — they appear inline inside the cycle 266–268 `bseriesExactTerm_*_scalar`
proofs. Cycle 269 should follow the same inline pattern (don't extract
as private lemmas unless the same ED is re-used 3+ times in cycle 269).

## §F Non-vacuity (P11)

After P10, add ONE non-vacuity `example` covering the trivial ODE
`f := 0`. Pattern from cycle 268:

```lean
example (y₀ h : ℝ) :
    bseriesExactTerm (fun _ : ℝ => (0 : ℝ)) y₀ h (mk [mk [mk [cherry]]])
      = 0 := by
  rw [bseriesExactTerm_mkMkMkCherry_scalar]
  simp
```

This exercises one of the 9 theorems end-to-end. ONE example is
sufficient for cycle 269's bar — don't add 9 separate witnesses.

## §G LOC budget

* `Section310.lean`: +5 LOC (bushy₄ alias).
* `Section301.lean`: +400–500 LOC (9 per-tree closed forms, ~45–55 LOC each).
* `Section311.lean`: 0 LOC delta (bridge deferred to cycle 270).

Total target: **~450 LOC**. If trending toward 600+ LOC midway through,
the worker should consider deferring P3, P5, P6 (the depth-3 multi-child
recipes) to cycle 270 alongside the bridge.

## §H What NOT to try

* **Do NOT introduce ANY `sorry`.** Cycles 200/201 rolled back
  sorry-first scaffolds for multi-cycle targets; cycle 138/139 rolled
  back a sorry'd general-`n` `thm:550A`; cycles 149/150 rolled back
  `def:530B`'s sorry'd Path A scaffold. Cycle 269's deliverable bar is
  "ship axiom-clean or skip the cycle". Half-finished closed forms do
  not count.

* **Do NOT attempt the 17-tree partial-sum bridge
  `lem_311A_order_five_partialSum` in cycle 269.** It is the explicit
  cycle 270 target. Trying to fit it in this cycle was the reason for
  the §A split. Cycle 268 spent ~290 LOC on the 8-tree bridge; the
  17-tree version needs 16 non-membership lemmas plus all 9 cycle 269
  per-tree closed forms in an iterated `Finset.insert` chain.

* **Do NOT attempt polymorphic-`E` lift of any cycle 266–268 closed
  form** (Phase D.1 / E.2). Cycle 271+ scope per cycle 268 task results
  §"Suggested next approach" Option 2. The multilinear-map curry/uncurry
  plumbing for arbitrary `E : Type*` is MEDIUM-HIGH risk and ad-hoc
  lifts inflate LOC unpredictably.

* **Do NOT pivot to `lem:342A`** mid-cycle. Cycle 269's directive is
  Phase E.1 order-5 closure. Pivot is cycle 271's planner decision after
  cycle 270 ships the bridge.

* **Do NOT rename, audit, or modify any cycle 248–268 theorem.** All
  are axiom-clean; the cycle 268 task results contain extensive
  faithfulness checks. Touching them risks scanner false positives per
  `.prover-state/issues/tautology_scanner_false_positives.md`.

* **Do NOT touch `OpenMath/Chapter4/Section441.lean`.** 43+ consecutive
  GPFS timeouts since cycle 182; skip per
  `.prover-state/issues/cycle_182_gpfs_slowness.md`. The deferred Phase
  C.2 work there is loop-maintainer territory.

* **Do NOT raise `maxHeartbeats`** above 200000. If a per-tree closed
  form stalls during `ring` or `simp`, decompose by extracting an
  intermediate `have` for the elementaryDiff identity. Cycle 268's P3
  (mk [broom₃]) precedent: the inner `hED_broom` block was extracted
  rather than inlined.

* **Do NOT edit `scripts/autonomous_loop.py`** or the prompt-builder.

* **Do NOT introduce `axiom`/`constant`** declarations. Per CLAUDE.md.

* **Do NOT use `Polynomial.ext`** (cycles 172/173 stalled here). N/A
  for cycle 269 (no polynomials involved), listed defensively.

* **Do NOT poll Aristotle** more than once if a job is submitted.
  Cycle 269 should not need Aristotle — the recipe is mechanical from
  cycles 267/268. If a single P-deliverable proves unexpectedly hard
  (>60 min on one theorem), submit ONCE to Aristotle and continue
  manual work on the remaining theorems while it runs.

## §I Faithfulness check (mandatory pre-commit)

Per CLAUDE.md "Pre-Commit Faithfulness Checklist":

For each P2–P10 closed form:

1. **Anchor entity**: `def:312A` (exact-solution B-series form per
   Butcher §312), with `def:310A` for elementaryDiff. None of the 9
   theorems should claim or update `lem:310B` status — they are stepping
   stones for Phase E.1 of `lem_310B_plan.md`, not the textbook lemma
   itself.
2. **σ-recursion verification**: independently compute σ via the
   recursion `σ(mk children) = ∏_{distinct subtree types} mᵢ! · σ(tᵢ)^{mᵢ}`.
   For T3, T5: multi-distinct-children case (different formula than
   T6, T7, T8 one-child case).
3. **γ-recursion verification**: `γ(mk children) = r(t) · ∏_{children} γ(c)`
   (NOT distinct-only). Cycle 268's task results document this at P3
   (σ=2 via single-distinct one-child but γ uses all children).
4. **Coefficient cross-check**: sum the 9 coefficients grouped by monomial;
   verify against cycle 259's `lem_311A_order_five` Bell coefficients
   (1, 7, 4, 11, 1). The table in §B is the reference; ANY mismatch is a
   hard stop — re-derive, do NOT commit.
5. **Tautology / identity / absent-theorem check**: each theorem is a
   substantive computational equality (left side `bseriesExactTerm`,
   right side closed-form scalar polynomial). No `:= h` or
   `exact h_<name>` closers.

## §J Sequencing

Verification commands (optional but recommended at cycle start):

```bash
git log -1 --format='%H %s'  # confirm at 4c92bf7
grep -c sorry OpenMath/Chapter3/Section301.lean  # confirm 0
grep -c sorry OpenMath/Chapter3/Section311.lean  # confirm 0
```

Phase 1 (~5 min): write P1 (`bushy₄` alias) at `Section310.lean`.
`lake env lean OpenMath/Chapter3/Section310.lean` — verify clean.
Run `lake build OpenMath.Chapter3.Section310` to refresh the olean for
downstream consumers (cycle 268's lesson — see "Discovery" §).

Phase 2 (~120 min): work through P2, P10, P4, P7, P9 in that order
(σ-validation front-loaded). Each ~45 min: write, compile, fix.
Run `lake env lean OpenMath/Chapter3/Section301.lean` after each.

Phase 3 (~120 min): work through P8, P3, P5, P6 (multi-child outer).
Hardest of the nine; allocate slack here.

Phase 4 (~10 min): add ONE non-vacuity example (per §F).

Phase 5 (~15 min):
* `lake env lean OpenMath/Chapter3.lean` — full chapter rebuild.
* `#print axioms` on all 9 new theorems — confirm
  `[propext, Classical.choice, Quot.sound]` only.
* `grep -c sorry OpenMath/Chapter3/Section{301,310,311}.lean` — confirm
  all 0.
* `lean_status.json` `lem:310B` row stays `unformalized` (Phase E.1 is
  one stepping stone, not the lemma itself). Add cycle 269 note to its
  `notes` field if present.
* `plan.md` `lem:310B` row stays `[ ]`. Update its inline note to
  reference cycle 269's nine new per-tree closed forms.
* Append cycle 269 closure update to
  `.prover-state/issues/lem_310B_plan.md` §"Phase E.1" (after the
  cycle 268 entry).

Phase 6 (~15 min): write `.prover-state/task_results/cycle_269.md`
following cycle 268's template. Include faithfulness check covering
all 9 theorems with σ-recursion cross-references.

Phase 7 (~10 min): commit + push. Cycle 270 picks up the 17-tree
partial-sum bridge.

## §K Recovery / abort thresholds

* If P2 (the first depth-4 outer iteratedFDeriv) stalls past 60 min,
  abort the cycle and pivot to **only** P10 + P4 + P7 (the simpler
  one-child-wrapping cases). Three axiom-clean closed forms is well
  above CLAUDE.md's minimum-progress bar.
* If `Fin.prod_univ_four` is missing from Mathlib at HEAD, fall back to
  `Fin.prod_univ_succ` × 3 + `Fin.prod_univ_zero` for P2 only. All other
  deliverables use `Fin.prod_univ_{one,two,three}` already verified by
  cycles 266–268.
* If σ verification fails on T3/T5/T8 mid-proof (i.e. `rfl` doesn't fire
  for `symmetry <tree> = <value>`), STOP and re-derive. Do NOT guess;
  the cycle 268 P3 σ=2 catch was exactly this scenario. The σ table in
  §B was independently verified — if Lean disagrees, the strategy file
  is wrong and the worker should escalate via the task results.
* If any per-tree coefficient cross-check (§I step 4) fails to match the
  cycle 259 Bell coefficient sum, STOP. Do NOT commit a theorem whose
  closed form is inconsistent with the established order-5 expansion.

## §L Cycle 270 preview (so the worker doesn't accidentally do its work)

Once cycle 269 lands the 9 closed forms, cycle 270's deliverable is:

* `lem_311A_order_five_partialSum` at `Section311.lean` — bridge cycle
  259's `lem_311A_order_five` closed-form polynomial residual to
  `bseriesExactPartialSum f y₀ h S` where S is the 17-tree Finset
  `{vertex, cherry, broom₃, mk [cherry], bushy, mk [v,cherry],
  mk [broom₃], mk [mk [cherry]], bushy₄, mk [v,v,cherry], mk [v,broom₃],
  mk [v,mk [cherry]], mk [cherry,cherry], mk [bushy], mk [mk [v,cherry]],
  mk [mk [broom₃]], mk [mk [mk [cherry]]]}`.

* 16 non-membership lemmas for the iterated `Finset.insert` chain
  (cycle 268 pattern: each `simp [vertex, cherry, broom₃, bushy, bushy₄]`
  on `RootedTree.mk.injEq`).

* One non-vacuity witness `example` exercising the bridge on
  `f := 0, yex := const y₀`.

Estimated cycle 270 budget: ~500 LOC. After cycle 270 lands, **Phase E.1
is fully closed up to order 5 in the scalar setting**, matching cycle
259's deliberate order-5 cutoff and providing a clean stopping point
for the §310/§311 multi-cycle thread.

Cycle 271+ planner decides: pivot to `lem:342A` (single-cycle, fresh),
polymorphic-`E` lift (Phase D.2 / E.2, multi-cycle), or fresh chapter
entry.
