# Cycle 164 Strategy — def:530B/C Path A r-parametric refactor Phase B.3 (reconciliation)

## Context (one-paragraph state)

Cycle 163 closed Phase B.1 (parametric `HasOrderRelativeTo_explicit`
witnesses) and Phase B.2 (parametric `HasOrder_explicit` wrappers)
for `def:530B`/`def:530C` Path A axiom-clean. Four new theorems +
seven private helper lemmas; +302 LOC; sorry count remained 0.
Eight consecutive cycles (156–163) have advanced this same area;
the parametric infrastructure (`paddedREulerGLM (r : ℕ)`,
`padCompatStartingMethodR (r : ℕ)`) now subsumes the hand-written
`r ∈ {1, 2, 3, 4}` × `p ∈ {0, 1}` grid in *content*, but the
hand-written instances (cycles 156/157/159/161) still coexist as
independent definitions with their own witnesses. Cycle 163's
"Suggested next approach" lists Phase B.3 (reconciliation lemmas) as
candidate #1 for this cycle, gated by whether the reconciliations
close cleanly.

No Aristotle results pending. No sorries in the codebase.

## Priority 0 — No Aristotle incorporation needed

There are no completed Aristotle jobs awaiting incorporation. Skip
straight to Priority 1.

## Priority 1 — Phase B.3 reconciliation lemmas (PRIMARY DELIVERABLE)

### Goal

Land four reconciliation lemmas asserting that the parametric padded
GLM family specializes to the cycle-156/159/161 hand-written
instances, plus the analogous reconciliations for the parametric
starting family. Eight lemmas total. **Do NOT attempt retirement of
the hand-written instances this cycle** — that is cycle 165's job
per cycle 163's explicit recommendation.

### Concrete deliverables

In `OpenMath/Chapter5/Section520.lean` (immediately after the
`paddedREulerGLM` definition), prove:

```lean
theorem paddedREulerGLM_zero_eq_explicitEulerGLM :
    paddedREulerGLM 0 = explicitEulerGLM := by
  -- close by ext + fin_cases + simp/rfl/decide

theorem paddedREulerGLM_one_eq_padded2DEulerGLM :
    paddedREulerGLM 1 = padded2DEulerGLM := by
  -- close by ext + fin_cases + simp/rfl/decide

theorem paddedREulerGLM_two_eq_padded3DEulerGLM :
    paddedREulerGLM 2 = padded3DEulerGLM := by
  -- close by ext + fin_cases + simp/rfl/decide

theorem paddedREulerGLM_three_eq_padded4DEulerGLM :
    paddedREulerGLM 3 = padded4DEulerGLM := by
  -- close by ext + fin_cases + simp/rfl/decide
```

In `OpenMath/Chapter5/Section530.lean` (immediately after the
`padCompatStartingMethodR` definition), prove the analogous four
starting-family reconciliations:

```lean
theorem padCompatStartingMethodR_zero_eq_trivialStartingMethod :
    padCompatStartingMethodR 0 = trivialStartingMethod
theorem padCompatStartingMethodR_one_eq_padCompatStartingMethod :
    padCompatStartingMethodR 1 = padCompatStartingMethod
theorem padCompatStartingMethodR_two_eq_pad3CompatStartingMethod :
    padCompatStartingMethodR 2 = pad3CompatStartingMethod
theorem padCompatStartingMethodR_three_eq_pad4CompatStartingMethod :
    padCompatStartingMethodR 3 = pad4CompatStartingMethod
```

### Closure recipe

The two families have different surface bodies (`paddedREulerGLM`
uses `Matrix.of fun i j => if … then 1 else 0`; the hand-written
instances use `!![…]` literal matrices). They are *value-equal*
because both reduce to the same indicator matrix at concrete `r`,
but proving so requires unfolding both forms.

Try in this exact order at each reconciliation:

1. **`rfl`** — quickest test. The `Matrix.of fun i j => if … then 1
   else 0` and `!![1, 0; 0, 0]`-style bodies might not be definitionally
   equal, so this likely fails. If it works, ship.
2. **GLM-side**: open the GLM structure with `ext` (or
   `cases h : paddedREulerGLM 1`), then prove A/U/B/V agree
   matrix-wise. For each matrix: `ext i j; fin_cases i <;> fin_cases j
   <;> simp [paddedREulerGLM, padded2DEulerGLM, Matrix.of_apply]`. If
   `simp` doesn't close, append `<;> decide` or `<;> rfl`.
3. **Starting-family side**: `ext` to expose `stages`, `method`. The
   `stages` field is `fun _ => 1` on both sides — `funext i; rfl` or
   `rfl` should close. The `method` field requires `funext i;
   fin_cases i <;> simp [padCompatStartingMethodR, padCompatMethodR,
   padCompatStartingMethod, padCompatMethod, pad3CompatStartingMethod,
   pad3CompatMethod, pad4CompatStartingMethod, pad4CompatMethod]`. The
   `i.val = 0` branch should reduce to `trivialGeneralizedRK = trivialGeneralizedRK`
   (by `rfl`); the other branches should reduce to
   `zeroGeneralizedRK = zeroGeneralizedRK` (by `rfl`).

If the GLM structure doesn't have a usable `ext` lemma exposing the
four matrix fields, fall back to manual field equalities:
`refine ⟨?_, ?_, ?_, ?_⟩` (or whatever the constructor / mk shape
exposes), then close each field by the `ext + fin_cases + simp`
recipe above.

### Verification gate

After each lemma lands, verify with:
```bash
lake env lean OpenMath/Chapter5/Section520.lean
lake env lean OpenMath/Chapter5/Section530.lean
```
Both must exit 0 with no `sorry` warnings. Then `mcp__lean-lsp__lean_verify`
on each new theorem fully-qualified — expect axioms
`[propext, Classical.choice, Quot.sound]` only.

### Time-box and abort condition

**30-minute budget for the eight reconciliations combined.**

Abort condition: if *any* of the eight reconciliations resists the
recipe above after **15 minutes of focused effort on that single
lemma** (i.e., `simp` reductions don't close, manual unfolding gets
stuck on coercion/elaboration mismatches), STOP and document the
specific blocker in `.prover-state/issues/def_530B_phase_B3_blocker.md`.
Then pivot to Priority 2 below for the remainder of the cycle.

Likely failure modes worth flagging if they bite:
- `Fin (1 + 1)` vs `Fin 2` definitional mismatch — try `Nat.add_zero`,
  `show … from rfl`, or `convert … using 0` to bridge.
- `Matrix.of` not unfolding under `simp` — explicitly add
  `Matrix.of_apply` to the simp set.
- `!![…]` notation not unfolding — try `simp [Matrix.cons_val_zero,
  Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]` or
  `decide`.
- GLM structure's `ext` lemma absent — fall back to constructor
  matching as above.

## Priority 2 — Backup pivot if Phase B.3 stalls

If Phase B.3 aborts (a single reconciliation eats > 15 minutes), do
NOT throw away the cycle. Pivot to a clean fresh definition entity.
Recommended target: **`def:451A` G-stable** (Chapter 5 §451).

### Why `def:451A` is the right backup

- Chapter 5 continuity: builds directly on the existing §510 GLM
  infrastructure (`GeneralLinearMethod`, `IsStable`, etc.).
- Definition-shape: encoded in roughly the same single-cycle pattern
  used for `def:357A` (B-stability), `def:357B` (algebraic stability),
  `def:520E` (A-stable), `def:520F` (L-stable), `def:525A`
  (G-symplectic), `def:542A` (Runge–Kutta stability), `def:551A`
  (inherent Runge–Kutta stability) — all axiom-clean single-cycle
  deliverables.
- Topo order: `def:451A` has no Chapter-5 prerequisites that aren't
  already done.

### Concrete backup steps

1. **Read the entity data**: `extraction/formalization_data/entities/def_451A.json`
   for the textbook statement, LaTeX, and dependency list.
2. **Search Mathlib first**: `mcp__lean-lsp__lean_local_search "Gstable"`,
   `mcp__lean-lsp__lean_leansearch "G-stability"`,
   `mcp__lean-lsp__lean_leansearch "positive definite matrix bilinear form"`.
   If a Mathlib equivalent exists, reuse it.
3. **Encode the predicate** as a `def` or `Prop`-valued function
   in a new section of `OpenMath/Chapter5/Section450.lean` (or
   wherever fits the §451 numbering). Match the textbook
   verbatim — the textbook G-stability characterization is via
   *existence of a positive definite symmetric matrix G* such that
   a quadratic form inequality holds. Encode as
   `∃ G, G.PosDef ∧ G.IsSymm ∧ ∀ <quadratic-form-inequality>`.
4. **Build a non-vacuity witness**: at minimum, a trivial witness
   (e.g., `trivialZeroGLM` with `G := 1`) satisfies G-stability
   vacuously. If the strategy admits a substantive witness in the
   single-cycle budget (e.g., `implicitMidpointGLM` from cycle
   135 — algebraically stable methods are G-stable), pursue it;
   otherwise the trivial witness suffices for cycle 164's
   non-vacuity rule.
5. **Verify axiom-clean**: `mcp__lean-lsp__lean_verify
   OpenMath.Chapter5.Section450.G_stable_witness_name`. Expect
   `[propext, Classical.choice, Quot.sound]` only.
6. **Update `lean_status.json`** and `plan.md` for `def:451A`.

### Time-box for backup

If Phase B.3 aborts at the 15-minute mark, the remaining ~75-minute
budget for `def:451A` is realistic. If `def:451A` itself runs into
infrastructure shortfalls (positive-definite matrix machinery,
quadratic-form inequalities), file an issue file and ship whatever
substantive partial progress is in hand.

## Priority 3 — Update bookkeeping (always)

Regardless of which priority lands, before commit:

1. Update `plan.md` for any newly-completed entity (Phase B.3 doesn't
   change `def:530B`/`def:530C` row status — they remain `[~]`
   pending Path B; backup `def:451A` would flip its row from `[ ]`
   to `[x]` if it lands).
2. Update `extraction/formalization_data/lean_status.json` for each
   entity touched.
3. Write `.prover-state/task_results/cycle_164.md` covering Result,
   Faithfulness check, Dead ends, Discovery, Suggested next approach.
4. Tautology-scanner regex check:
   ```
   rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/
   ```
   Should return only the pre-existing
   `OpenMath/Chapter5/Section514.lean:601` hit (a known false
   positive). If a new hit appears, apply the cosmetic
   `h_<name>` → `h<name>` rename per the standing
   `.prover-state/issues/tautology_scanner_false_positives.md`.

## What NOT to do

The following approaches are explicitly forbidden this cycle:

1. **DO NOT attempt retirement of the hand-written
   `padded{2,3,4}DEulerGLM` / `pad{2,3,4}CompatStartingMethod`
   instances or their cycle 156/157/159/161 witnesses.** That is
   cycle 165's deliverable, gated on Phase B.3 closing first. Any
   attempt to combine reconciliation + retirement in a single cycle
   risks landing a half-finished refactor; ship Phase B.3 cleanly
   first.

2. **DO NOT attempt Path B** (implicit branch of `def:530B`/`def:530C`)
   solo. Path B requires `ContractingWith` / `Function.IsFixedPt`
   infrastructure for the implicit stage equations; it is a
   multi-cycle campaign and is explicitly deferred per
   `.prover-state/issues/def_530B_scaffold_strategy.md`.

3. **DO NOT touch `aux_515D_construct_ell_U_phi_A`'s `_hc_nn` /
   `_hc_le_one` faithfulness divergence.** §515D is closed
   axiom-clean (cycle 124); the `_hc_nn` / `_hc_le_one` propagation
   to `stable_consistent_isConvergent` is a known divergence
   documented in `.prover-state/issues/stable_consistent_isConvergent_hc_nn.md`.
   Removing it is a multi-cycle Chapter-5 cleanup pass, not a
   single-cycle deliverable.

4. **DO NOT submit Aristotle jobs for Phase B.3** or for the
   `def:451A` backup. Phase B.3 is `ext`/`fin_cases`/`simp`/`decide`
   territory — Aristotle has historically been weak on parametric
   `Fin`-indexed sums and indicator-matrix unfolding, per the cycle
   162/163 anti-pattern lists. The `def:451A` backup is also
   definition-shape work that closes by direct construction, not
   premise selection.

5. **DO NOT attempt `thm:550A` general-`n`.** That Aristotle job has
   been cancelled twice (cycles 141, 151) and requires either
   cofactor-expansion induction or eigenvalue-density infrastructure
   — multi-cycle work. The seven concrete-`n` stepping stones
   (n = 1..7) are sufficient empirical evidence; further stepping
   stones add marginal value per cycle 150's task results.

6. **DO NOT raise `maxHeartbeats`** above 200000. If a Phase B.3
   reconciliation triggers heartbeat issues during
   `simp [paddedREulerGLM, padded{k}DEulerGLM]`, decompose: prove
   A/U/B/V matrix equalities as four separate private helper lemmas
   first, then combine in the GLM-level reconciliation.

7. **DO NOT re-poll Aristotle** in this cycle. There are no pending
   jobs, and the standing CLAUDE.md rule (poll once at most after
   30-min sleep) is moot.

8. **DO NOT introduce `axiom` or `constant` declarations.** The
   project rule is absolute.

## Open issues (informational)

The following blockers are documented in `.prover-state/issues/`
and are NOT being addressed this cycle:

- `AN_stability_deferred.md` — `def:356A` AN-stability deferred.
- `def_530B_scaffold_strategy.md` — Path B (implicit branch) of
  `def:530B`/`def:530C` deferred.
- `thm_550A_general_n.md` — `thm:550A` general-`n` deferred.
- `stable_consistent_isConvergent_hc_nn.md` — `_hc_nn` /
  `_hc_le_one` faithfulness divergence in §515D capstone.
- Various other entries — see `.prover-state/issues/` for the full
  list.

These are tracked for future planning cycles.
