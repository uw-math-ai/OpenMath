# Cycle 104 Strategy — Close `lem:515B` sub-lemmas + main combination

## Context

Cycle 103 opened `lem:515B` with a sorry-first scaffold in
`OpenMath/Chapter5/Section515.lean`. Three sorries remain:

| Line | Symbol | Difficulty |
|------|--------|------------|
| 914  | `aux_515B_lipschitz_bridge` | **CHEAP** — pattern of `aux_T4_bound` (cycle 101) |
| 953  | `aux_515B_eta_contraction`  | **HARD** — needs `(I − h₀L|A|)^{-1}` positivity (M-matrix) |
| 1038 | `GeneralLinearMethod.localStepError_bound` | **MEDIUM** — composition |

Aristotle batch was submitted in cycle 103 (project
`4688b630-d9c9-4f86-9572-7e4bd9a6b0b8`, submitted 2026-05-03 17:52
UTC) covering all three.

## Priority 0 (FIRST 10 MINUTES): Check Aristotle ONCE

Run **exactly once** at the start of the cycle:

```
mcp__aristotle__get_status project_id=4688b630-d9c9-4f86-9572-7e4bd9a6b0b8
```

If the project has finished (`status = COMPLETED` or has extractable
proofs):

1. `mcp__aristotle__download_result project_id=4688b630-...`
2. `mcp__aristotle__extract_result` to pull each lemma's body.
3. For each returned proof:
   - Verify it compiles standalone (`lake env lean OpenMath/Chapter5/Section515.lean`).
   - Verify axioms are clean (`#print axioms <symbol>` returns only
     `[propext, Classical.choice, Quot.sound]`).
   - Insert into the file at the corresponding sorry site.

If the project is still `IN_PROGRESS` after this single check, **do
not poll again**. Proceed with the manual plan below; any later
returned proofs can be incorporated in cycle 105.

## Priority 1: Close `aux_515B_lipschitz_bridge` MANUALLY (line 914)

This is the easiest sorry and is high-confidence. The proof structure
is well-established by `aux_T4_bound` from cycle 101 (same file).
Use `lean_local_search` for `aux_T4_bound` to copy the shape.

**Goal** (signature at line 906):
```
|h * ∑ j, B i j * (f (Y_hat j) - f (Y j))|
  ≤ h * L * ∑ j, |B i j| * |Y_hat j - Y j|
```
under `0 ≤ L`, `LipschitzWith L.toNNReal f`, `0 ≤ h`.

**Proof recipe** (target ≤ 30 LOC):

1. `rw [abs_mul, abs_of_nonneg _hh]` to peel out the leading `h`
   from the LHS magnitude.
2. Apply `mul_le_mul_of_nonneg_left _ _hh` to remove the leading
   `h` on both sides; goal becomes
   `|∑ j, B i j * (f (Y_hat j) - f (Y j))| ≤ L * ∑ j, |B i j| * |Y_hat j - Y j|`.
3. Use `Finset.abs_sum_le_sum_abs` to push `|·|` inside the LHS
   sum: goal becomes `∑ j, |B i j * (f (Y_hat j) - f (Y j))| ≤ ...`.
4. Use `Finset.mul_sum` (rewrite the RHS as `∑ L * |B i j| * |...|`).
5. Apply `Finset.sum_le_sum` to compare summand-wise.
6. For each summand:
   - `rw [abs_mul]` for `|B i j * (f (Y_hat j) - f (Y j))|`.
   - Apply `mul_le_mul_of_nonneg_left _ (abs_nonneg _)` to factor
     out `|B i j|`.
   - Bound `|f (Y_hat j) - f (Y j)| ≤ L * |Y_hat j - Y j|` via
     `_hf_lip.dist_le_mul` + `Real.dist_eq` + `NNReal.coe_toNNReal _hL`.

**Reference pattern**: cycle 101's `aux_T4_bound` (~30 LOC, same
structure). Read its proof body via `lean_local_search "aux_T4_bound"`
or by direct `Read` of `Section515.lean` if you need the exact
tactic shape.

**Pitfalls** (do NOT repeat from prior cycles):
- `LipschitzWith.dist_le_mul` returns `dist (f a) (f b) ≤ ↑K * dist a b`
  with `K : ℝ≥0`. Bridge to `ℝ` via
  `simpa [Real.dist_eq, ← NNReal.coe_le_coe, NNReal.coe_mul,
         Real.coe_toNNReal _ _hL]`.
- Per `feedback_add_le_add_left_dispatch.md`: prefer `linarith` /
  `gcongr` over `add_le_add_left` for left-constant scaling — the
  argument order may surprise you.

## Priority 2: Close `localStepError_bound` composition (line 1038)

The main theorem is a composition of:

* `aux_515B_residual_decomposition` (cycle 103, **already closed**).
* `aux_515B_lipschitz_bridge` (Priority 1, will be closed this
  cycle).
* `aux_515B_eta_contraction` (Priority 3 — may remain `sorry`).

**Important**: `localStepError_bound` does NOT depend on the
*proofs* of the sub-lemmas, only on their *types*. Even if
`aux_515B_eta_contraction` remains as `sorry`, we can still close
`localStepError_bound` by *applying* the sub-lemma. The composition
chain is structural, not analytical.

**Witness** for the existential `∃ K`:
```
K i := h * (∑ j, M.B i j * f (Y j))
       + (∑ j, M.V i j * yt_prev j)
       - (u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
       - ∑ j, M.V i j * δ j
```
Equivalently (after `aux_515B_residual_decomposition`):
`K i = (∑ j, M.V i j * (yt_prev j − y_prev j)) − (∑ j, M.V i j * δ j)
       + (the residual against the EXACT-stage-equation solution)
       + h * (∑ j, M.B i j * (f (Y j) − f (Ŷ_exact j)))`
where `Ŷ_exact` solves the implicit stage equation with `yt_prev`
replaced by `y(xn1) u + h y'(xn1) v`.

**Plan** (target ≤ 100 LOC):

1. **Identity clause**: with K *defined* as `LHS − ∑ V·δ`, the
   equation `LHS = ∑ V·δ + K i` becomes a `ring` identity.
   Apply `aux_515B_residual_decomposition` first to get the
   structure (use `M`, `yt_prev`, `y_prev := fun k => u k * yex xn1 + v k * h * deriv yex xn1`,
   `δ`, `Y`, `f`, `yex`, `xn1`, `u`, `v`, `i` as arguments).

2. **Bound clause** `|K i| ≤ α h δ_max + β h²`. Decompose:
   * `K = K_residual + K_correction` where:
     - `K_residual` is the §515A-style residual against the
       *exact-stage-equation* solution `Ŷ_exact`.
     - `K_correction = h Σ B·(f(Y) − f(Ŷ_exact))`.
   * **`K_residual`**: this matches the cycle-102 `localStageError_bound_b`
     bound shape — `½h²L²M c² + h²L²M Σ|A·c| + h²L²M(½|u| + |v| + Σ|B·c|)`
     terms — exactly the components inside the textbook β formula
     (without the `h₀ L Σ|B|·phi_A` term, which arises from the
     correction). Bound using `lem:515A` with `Ŷ_exact` substituted.
     If this turns out to be too intricate, factor it as
     `aux_515B_kresidual_bound` (a sub-lemma) and apply.
   * **`K_correction`**: bounded by `aux_515B_lipschitz_bridge` →
     `h L Σ|B|·|Y_j − Ŷ_exact_j|`. The differences `|Y_j − Ŷ_exact_j|`
     ARE the η-vector that `aux_515B_eta_contraction` controls.
     Apply `aux_515B_eta_contraction` (regardless of whether its
     proof is `sorry` — its *signature* is what we need).
   * **Combine**: the `h L Σ|B|·ell_U_j δ_max` term collapses to
     `α h δ_max` via `_hα_def`. The `h³L³M²Σ|B|·phi_A_j` term plus
     the residual bounds collapse to `β h²` via `_hβ_def` (using
     `h ≤ h₀`).

3. **Aristotle-friendly batching**: if the manual composition
   stalls past 60 LOC of intermediate goals, factor a single
   `aux_515B_main_combination` private lemma whose statement is
   the bound clause assuming the three sub-lemmas as named
   hypotheses, and submit it to Aristotle as a *second* batch.
   Do NOT block on this submission; defer to cycle 105.

**Faithfulness check** (per CLAUDE.md):
- The conclusion is `∃ K, identity ∧ bound`. Identity is non-trivial
  (`aux_515B_residual_decomposition` does the algebraic work).
  Bound is non-trivial (composes three sub-lemmas).
- `K` is constructed; it is not a hypothesis.
- The proxy parameters `α, β, δ_max` are weakened upper bounds, not
  the textbook's literal maxima — already documented in the
  cycle-103 docstring. No new faithfulness deviation.

## Priority 3: `aux_515B_eta_contraction` (line 953) — TRIAGE

This is the **infrastructure-blocked** sub-lemma. The textbook
proof requires the M-matrix monotonicity principle:

> If `x ≤ M·x + b` with `M ≥ 0` (entrywise) and `(I − M)^{-1}` exists
> with non-negative entries, then `x ≤ (I − M)^{-1}·b`.

Specifically, with `M = h₀ L |A|` (entrywise),
`(I − h₀L|A|)^{-1} ≥ 0` follows from M-matrix theory
(Perron–Frobenius / Neumann series) under `ρ(M) < 1`. This is
multi-cycle Mathlib infrastructure.

### Decision tree

**3a. If Aristotle returned `aux_515B_eta_contraction`** (Priority
0): use it. Done.

**3b. If Aristotle did NOT return it**, choose ONE of:

**(b-i) Defer with issue file (DEFAULT — recommended).** Write
`.prover-state/issues/lem_515B_eta_contraction_deferred.md`
documenting:

- The M-matrix infrastructure gap.
- The Neumann-series proof outline:
  ```
  |η| ≤ hL|A|·|η| + (Σ|U|·δ_max + h²L²M(½c² + Σ|A·c|))
  ⇒  (I − hL|A|)·|η| ≤ rhs
  ⇒  (I − h₀L|A|)·|η| ≤ rhs   (since h ≤ h₀ and |A|, |η| ≥ 0)
  ⇒  |η| ≤ (I − h₀L|A|)^{-1} · rhs = ell_U·δ_max + h²L²M·phi_A
  ```
- Cross-link to `cesaro_inverse_I_minus_V.md` (the analogous
  `(I − V)^{-1}` infrastructure for §514 — same flavor of
  Banach-perturbation argument).
- Mathlib pointers: search for `Matrix.IsM`, M-matrix scaffolding.
  Use `lean_local_search "diagonally dominant"` /
  `lean_local_search "Neumann"` /
  `lean_loogle "Matrix _ _ _ → Matrix _ _ _"` (for `inv` /
  `nonsing_inv` patterns).
- Estimated cost: 2–3 cycles for the M-matrix skeleton, then one
  more cycle to close `aux_515B_eta_contraction`.

This leaves `aux_515B_eta_contraction` as `sorry`. Per CLAUDE.md
non-vacuity, the proxy parameter shape (with `_hellU_eq` /
`_hphiA_eq` side conditions) ensures the lemma is *not*
tautological — it correctly conditions the conclusion on the
existence of `ell_U`, `phi_A` solving the linear systems. The
lemma is genuinely provable; the *gap* is the existence/positivity
of the inverse.

**(b-ii) Re-submit a smaller piece to Aristotle**, ONLY if
Priority 1 + Priority 2 closed by mid-cycle and time remains.
Decompose `aux_515B_eta_contraction` into:
- A specialization to `h = h₀` (eliminates one parameter).
- A `Finset.induction_on` over `Fin s` size — works for triangular
  `A` (lower-triangular case is explicit RK; closed-form solvable).
- Submit as a fresh Aristotle batch; do NOT poll, defer to cycle
  105 evaluation.

**Do NOT attempt (b-iii)**: a *manual* full M-matrix proof in this
cycle. The infrastructure footprint is too large
(Perron–Frobenius for non-negative matrices, Neumann-series
convergence, monotonicity of inverse) and would dwarf the cycle's
other priorities.

## What NOT to try (failed approaches from prior cycles)

These are explicitly listed; do NOT repeat:

1. **`Finset.sum_le_sum_nbij'`** — does not exist in Mathlib (cycle
   050). For sum-le-sum via injective reindexing, use
   `← Finset.sum_image hinj` then
   `Finset.sum_le_sum_of_subset_of_nonneg`.

2. **`add_le_add_left hA c` for left-constant addition monotonicity**
   — the produced shape may be `a + c ≤ b + c` instead of
   `c + a ≤ c + b`. Use `linarith [hA]` or `gcongr` instead.

3. **Unicode `𝟙` as identifier suffix** — breaks the parser
   (cycle 099). Reserve `𝟙` for operators/notation; use ASCII
   identifiers like `B1`, `bone`, `ones_vec`.

4. **Polling Aristotle more than once per cycle** — CLAUDE.md
   explicit. One check at start of cycle is enough; another at end
   is acceptable only if Priority 1 + Priority 2 wrapped early.

5. **Editing `scripts/autonomous_loop.py`** — not the worker's
   responsibility. Scanner / prompt-builder bugs go in
   `tautology_scanner_false_positives.md` for the loop maintainer.

6. **Raising `maxHeartbeats` above 200000** — explicit CLAUDE.md
   rule. Decompose into helpers instead. The current §515.lean has
   no `maxHeartbeats` overrides — keep it that way.

7. **Introducing `axiom`/`constant`** — never. The η-contraction
   inverse-positivity gap is real Mathlib infrastructure, not
   axiom-bypass territory.

8. **Mass refactoring the `lem:515B` signature** — the cycle 103
   docstring documents four faithfulness deviations
   (proxy maxima, two ell-vectors, deferred inverse infrastructure,
   pointwise `|K i|`). Do NOT alter the signature this cycle; the
   composition in Priority 2 must match the cycle-103 shape.

## Pre-commit checklist

Before committing:

1. **Build**: `lake env lean OpenMath/Chapter5/Section515.lean`
   succeeds with at most 1 sorry (`aux_515B_eta_contraction` if
   Priority 3 deferred). Aim for 0 sorries.

2. **Axioms** (for each new/modified theorem):
   ```
   lake build OpenMath.Chapter5.Section515
   #print axioms OpenMath.Chapter5.Section510.GeneralLinearMethod.localStepError_bound
   #print axioms OpenMath.Chapter5.Section510.aux_515B_lipschitz_bridge
   ```
   Both should return `[propext, Classical.choice, Quot.sound]`
   only — no `sorryAx` (a residual sorry in
   `aux_515B_eta_contraction` is acceptable for `localStepError_bound`'s
   axiom check ONLY if `localStepError_bound` does not unfold its
   proof; since we apply it as a black-box hypothesis, this is
   fine — but verify with `#print axioms`).

   **Important**: `lake env lean <file>` does NOT update the
   .olean cache. Run `lake build OpenMath.Chapter5.Section515`
   BEFORE `#print axioms` to avoid stale-cache `sorryAx` false
   positives (this trick saved cycle 072).

3. **Faithfulness check**: for `localStepError_bound`, the
   docstring already documents the four deviations from the
   textbook. No new deviations expected from cycle 104's
   composition. Re-verify the K-witness against the
   `aux_515B_residual_decomposition` shape.

4. **Update `lean_status.json`**: `lem:515B` is currently `[ ]`
   (planned). Bump to `[~]` (in progress, partial) if
   `aux_515B_eta_contraction` remains as `sorry`; bump to `[x]`
   (complete) if all three close.

5. **Update `plan.md`**: same status bump as `lean_status.json`.

6. **Write `.prover-state/task_results/cycle_104.md`**:
   - "Worked on": close lem:515B sub-lemmas and main theorem.
   - "Approach": Aristotle check + Priority 1 manual + Priority 2
     composition + Priority 3 triage decision.
   - "Result": SUCCESS / PARTIAL / FAILED with explicit sorry
     count delta (e.g. "3 → 1, with `aux_515B_eta_contraction`
     deferred").
   - "Faithfulness check": tabulate the §515.lean lemmas
     introduced/modified.
   - "Suggested next approach": cycle 105 should focus on either
     (a) M-matrix infrastructure to close
     `aux_515B_eta_contraction`, or (b) `lem:515C` (next §515
     entity, depends on `lem:515B`).

7. **Commit message** (shape):
   ```
   Cycle 104 — close lem:515B lipschitz bridge + main composition
   ```
   or analogous shape based on what landed.

8. **Push** to `origin/Main/Experiments`.

## Stretch goals (only if Priorities 1 + 2 + 3 wrap by 75% of cycle time)

* **Stretch A**: Begin `lem:515C` scaffold (entity
  `entities/lem_515C.json`: "Accumulated error estimate for
  multistep methods"). Sorry-first scaffold + 1 trivial helper.
  Submit a small Aristotle batch.

* **Stretch B**: Begin M-matrix infrastructure file
  `OpenMath/Chapter5/MMatrix.lean` (or extend `Section515.lean`)
  with `(I − cM)·x ≤ b ∧ M ≥ 0 ∧ ρ(cM) < 1 ⇒ x ≤ (I − cM)^{-1}·b`,
  the canonical M-matrix theorem. This is the long-term unblock for
  `aux_515B_eta_contraction`.

Do NOT attempt both stretch goals in one cycle.

## Summary table

| Priority | Symbol | Action | Status |
|----------|--------|--------|--------|
| 0 | (Aristotle) | One status check; incorporate returned proofs | mandatory |
| 1 | `aux_515B_lipschitz_bridge` | Manual close (~30 LOC) | mandatory |
| 2 | `localStepError_bound` | Composition (~100 LOC) | mandatory |
| 3 | `aux_515B_eta_contraction` | Triage: Aristotle / defer-with-issue / smaller batch | conditional |
| 4 (stretch A) | `lem:515C` | Scaffold | optional |
| 4 (stretch B) | `MMatrix.lean` | Infrastructure | optional |

**Minimum acceptable cycle outcome**: Priority 1 closed manually +
Priority 2 closed (composition) + Priority 3 triaged (deferral
issue written if not Aristotle-returned). Sorry count goes 3 → 1
(η contraction deferred). A 0-sorry outcome (3 → 0) is the cycle
goal but not strictly required.
