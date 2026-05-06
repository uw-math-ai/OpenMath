# Cycle 162 Results

## Worked on
`def:530B`/`def:530C` Path A — r-parametric refactor Phase A.

Specifically: introduced a single parametric padded GLM family
`paddedREulerGLM (r : ℕ)` and a parametric starting family
`padCompatStartingMethodR (r : ℕ)` that subsume the cycles 156/159/161
hand-written `r ∈ {1, 2, 3}` (in current indexing) instances, plus
four basic structure lemmas. Phase B (parametric witnesses,
reconciliation lemmas) was deferred to cycle 163 per the strategy.

## Approach
Followed the cycle 162 strategy verbatim:

1. **Step 1.2 (Section520)** — added `paddedREulerGLM (r : ℕ) :
   GeneralLinearMethod 1 (r + 1)` after `padded4DEulerGLM` using the
   `Matrix.of`-based body specified in the strategy:
   ```
   A := !![0]
   U := Matrix.of fun (_ : Fin 1) (j : Fin (r + 1)) =>
          if j.val = 0 then 1 else 0
   B := Matrix.of fun (i : Fin (r + 1)) (_ : Fin 1) =>
          if i.val = 0 then 1 else 0
   V := Matrix.of fun (i j : Fin (r + 1)) =>
          if i.val = 0 ∧ j.val = 0 then 1 else 0
   ```

2. **Step 1.3 (Section530)** — added `padCompatMethodR` and
   `padCompatStartingMethodR` after `pad4CompatStartingMethod`:
   ```
   padCompatMethodR r := fun i =>
     if i.val = 0 then trivialGeneralizedRK else zeroGeneralizedRK
   padCompatStartingMethodR r where
     stages := fun _ => 1
     method := padCompatMethodR r
   ```

3. **Step 1.4 (four basic structure lemmas)** — proved axiom-clean:
   - `paddedREulerGLM_isExplicit (r : ℕ)` — vacuous closure at
     `s = 1` (`fin_cases i; fin_cases j; rfl`).
   - `padCompatStartingMethodR_isNonDegenerate (r : ℕ)` — witness
     `⟨0, Nat.succ_pos r⟩`, then unfold +
     `StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero` to reduce
     to `(1 : ℝ) ≠ 0`.
   - `padCompatStartingMethodR_constituents_isExplicit (r : ℕ)` —
     `by_cases hi : i.val = 0`; index 0 cites
     `trivialGeneralizedRK_isExplicit`, `i.val ≠ 0` closes vacuously
     with `fin_cases a; fin_cases b; rfl`.
   - `padCompatStartingMethodR_applyExplicit (r : ℕ) (f : ℝ → ℝ) (y₀ h : ℝ)`
     — `funext i; show (padCompatMethodR r i).explicitApply ...; unfold;
     by_cases hi : i.val = 0` then `simp [hi]; exact
     trivialGeneralizedRK_explicitApply f y₀ h` at index 0,
     `simp [hi]; exact zeroGeneralizedRK_explicitApply f y₀ h`
     elsewhere.

4. **Step 1.5 (verification)** — `lake env lean OpenMath/Chapter5/Section{520,530}.lean`
   and `lake env lean OpenMath/Chapter5.lean` all exit 0.
   `mcp__lean-lsp__lean_verify` on each of the four new theorems
   returned axioms `[propext, Classical.choice, Quot.sound]` only.

5. **Step 1.6 (state updates)** — bumped `cycle` for `def:530B`
   and `def:530C` to 162 in
   `extraction/formalization_data/lean_status.json`; appended cycle 162
   notes to both rows; updated the `def:530B` and `def:530C` rows of
   `plan.md`; appended a "Cycle 162 update" section with Phase B
   planning notes to
   `.prover-state/issues/def_530B_scaffold_strategy.md`.

Aristotle was **not** invoked this cycle, per the strategy's "failed
approaches to avoid" list (historical Aristotle weakness on
parametric `Fin`-indexed sums and decidable-equality case splits).
The four lemmas were closed manually within the cycle.

## Result
SUCCESS — all four new theorems compile axiom-clean
(`[propext, Classical.choice, Quot.sound]`). Sorry count remained at 0
in both `Section520.lean` and `Section530.lean`. Three new
declarations (`paddedREulerGLM`, `padCompatMethodR`,
`padCompatStartingMethodR`) and four new theorems
(`paddedREulerGLM_isExplicit`,
`padCompatStartingMethodR_isNonDegenerate`,
`padCompatStartingMethodR_constituents_isExplicit`,
`padCompatStartingMethodR_applyExplicit`) landed. Hand-written
`r ∈ {1, 2, 3, 4}` instances coexist with the parametric family;
reconciliation lemmas deferred to cycle 163 Phase B.3 per the
strategy.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `def paddedREulerGLM (r : ℕ) : GeneralLinearMethod 1 (r + 1)`
- Internal helper, not a textbook entity. The textbook does not
  define a parametric padded explicit-Euler GLM family. This is
  Lean-side scaffolding for `def:530B`/`def:530C` Path A non-vacuity
  witnesses, analogous to the existing hand-written
  `padded2DEulerGLM`/`padded3DEulerGLM`/`padded4DEulerGLM` from
  cycles 133/159/161 (Section520) and `padCompatStartingMethod`
  family from cycles 156/159/161 (Section530).
- Lean construction: row 0 is the active explicit-Euler channel
  (`U[0,0] = 1`, `B[0,0] = 1`, `V[0,0] = 1`); rows `1, …, r` are
  passively-decoupled zero channels.
- No textbook divergence to flag — it is not a textbook concept;
  it is helper infrastructure.

### `def padCompatMethodR (r : ℕ)`, `def padCompatStartingMethodR (r : ℕ)`
- Same internal-helper status. The textbook discusses starting
  methods in §530 (def:530A) but does not define this specific
  parametric heterogeneous-stages instance. The active row 0
  (`trivialGeneralizedRK`, `b₀ = 1`) provides non-degeneracy; the
  inactive rows `1, …, r` (`zeroGeneralizedRK`, `b₀ = 0`) mesh with
  the zero channels of `paddedREulerGLM r` for a clean Phase B.1
  zero-collapse on the `i.val ≠ 0` indices of the parametric
  HasOrderRelativeTo witnesses.
- No textbook divergence to flag.

### `theorem paddedREulerGLM_isExplicit (r : ℕ) : (paddedREulerGLM r).IsExplicit`
- Textbook: not a textbook theorem; supports `def:530B`/`def:530C`
  Path A's "explicit branch" restriction.
- Lean statement: `(paddedREulerGLM r).IsExplicit` for the
  Section510 GLM-side `IsExplicit` predicate
  (strict-lower-triangular `A` block).
- Tautology check: the hypothesis-free conclusion `(paddedREulerGLM
  r).IsExplicit` is a substantive structural fact about the 1×1
  zero `A`-block. Not a tautology.
- Identity check: proof is `intro i j _; fin_cases i; fin_cases j;
  rfl`, a vacuous closure at `s = 1`. This is the same proof shape
  used by `padded{2,3,4}DEulerGLM_isExplicit`; not a vacuous
  re-export.

### `theorem padCompatStartingMethodR_isNonDegenerate (r : ℕ) : (padCompatStartingMethodR r).IsNonDegenerate`
- Textbook: not a textbook theorem; non-degeneracy is required by
  `def:530C`'s existential clause, so this lemma supplies it for
  the parametric family.
- Lean statement: standard `IsNonDegenerate` from Section530;
  proof unfolds to `(1 : ℝ) ≠ 0` via the index-0
  `trivialGeneralizedRK` constituent, mirroring cycles 156/159/161.
- Tautology check: clean. The conclusion is not a hypothesis.
- Identity check: proof uses
  `StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero` to reduce
  to the substantive computation `(1 : ℝ) ≠ 0`; real work, not a
  re-export.

### `theorem padCompatStartingMethodR_constituents_isExplicit (r : ℕ) : ∀ i, ((padCompatStartingMethodR r).method i).IsExplicit`
- Textbook: not a textbook theorem; required by
  `HasOrderRelativeTo_explicit`/`HasOrder_explicit` predicates'
  `hS : ∀ i, (S.method i).IsExplicit` clause.
- Lean statement: standard `IsExplicit` from Section530 GRK side
  (strict-lower-triangular `A`).
- Tautology check: clean. The case-split `by_cases hi : i.val = 0`
  closes index 0 by citing `trivialGeneralizedRK_isExplicit`
  (substantive cycle 151 lemma) and `i.val ≠ 0` by vacuous
  closure on the 1×1 zero `A`-block of `zeroGeneralizedRK`.
- Identity check: real case-split, not a re-export.

### `theorem padCompatStartingMethodR_applyExplicit (r : ℕ) (f : ℝ → ℝ) (y₀ h : ℝ) : (padCompatStartingMethodR r).applyExplicit f y₀ h = fun i => if i.val = 0 then y₀ + h * f y₀ else 0`
- Textbook: not a textbook theorem; computational closed form for
  the parametric starting family's `applyExplicit` under the
  Section510-side internal helper, mirrors cycles 156/159/161's
  `pad{n}CompatStartingMethod_applyExplicit` for `n ∈ {2, 3, 4}`.
- Lean statement: closed form returning `y₀ + h · f(y₀)` at index
  0 (active `trivialGeneralizedRK` channel) and `0` elsewhere
  (inactive `zeroGeneralizedRK` channels).
- Tautology check: clean. The conclusion is a substantive equality
  of `Fin (r + 1) → ℝ` functions.
- Identity check: real `funext + by_cases + cite` proof, not a
  re-export.

No textbook divergence to flag — none of the four lemmas restate a
named textbook entity. They support the existing
`HasOrderRelativeTo_explicit`/`HasOrder_explicit` predicates
(cycles 153/155, faithful to def:530B/C) at the parametric `r + 1`
level; the predicates themselves remain unchanged from cycles
153/155 and continue to encode Butcher's def:530B/C statement
verbatim under the explicit Path A restriction.

Hypothesis-strength check: all four parametric lemmas are
statements *over* `r : ℕ` with no extra hypotheses. The proofs
discharge by the same machinery as the existing concrete-r
counterparts; no hypotheses were strengthened to make the proofs
go through.

## Dead ends
* Initial proof of `padCompatStartingMethodR_isNonDegenerate`
  attempted intermediate `show`-rewrites with `⟨0, _⟩` placeholder;
  the elaborator failed to synthesize the `isLt` proof from the
  underscore. Fixed by skipping the intermediate `show` and going
  directly from `refine ⟨⟨0, Nat.succ_pos r⟩, ?_⟩` into
  `unfold padCompatStartingMethodR padCompatMethodR; simp` followed
  by `(1 : ℝ) ≠ 0`.
* Initial `lake env lean Section530.lean` after Section520 edit
  failed to resolve `paddedREulerGLM` until `lake build
  OpenMath.Chapter5.Section520` was run to refresh the `.olean`.
  Standard issue, not a real dead end — just a reminder that the
  per-file lean check needs an up-to-date imported `.olean`.

## Discovery
* The strategy's choice of `r + 1` indexing (rather than `r` with a
  `0 < r` hypothesis) makes the parametric family genuinely
  total — no `NeZero` or `Nat.succ_pos` pollution at use sites.
  This came up immediately in the non-degeneracy proof: the witness
  index `⟨0, Nat.succ_pos r⟩` typechecks for any `r : ℕ`.
* The `Matrix.of fun ...` construction unfolds well under `simp`
  and `unfold`. No new heartbeat tuning was required for any of
  the four lemmas (well below the 200000 cap).
* The `applyExplicit` closed-form proof works just as well with
  `by_cases hi : i.val = 0` as with `fin_cases i` (the latter only
  fires at concrete `r`). This pattern should port directly to the
  Phase B.1 parametric witnesses.

## Suggested next approach
Cycle 163 should land Phase B per the cycle 162 issue update:

1. **Phase B.1** — parametric `HasOrderRelativeTo_explicit`
   witnesses
   - `paddedREulerGLM_hasOrderZero_padCompatStartingR (r : ℕ)`
     (p = 0)
   - `paddedREulerGLM_hasOrderOne_padCompatStartingR (r : ℕ)`
     (p = 1)
   Closure: `intro i; by_cases hi : i.val = 0`. At index 0 cite
   the cycle 158 (p = 1) / cycle 160 (p = 0) Taylor + Lipschitz
   helpers after the standard SM[0]/ES[0] closed-form rewrites.
   At `i.val ≠ 0`, the `applyExplicit` closed form returns 0; the
   `paddedREulerGLM r`'s `B[i]` and `V[i]` rows for `i ≥ 1` are
   also 0, so the entire `Diff` is 0 and `Asymptotics.isBigO_zero`
   closes the goal. Estimated ~150–250 LOC for both witnesses.

2. **Phase B.2** — parametric `def:530C` wrappers
   `paddedREulerGLM_hasOrderZero (r : ℕ)` and `_hasOrderOne (r : ℕ)`,
   trivial corollaries citing Phase B.1, exhibiting
   `padCompatStartingMethodR r` as the existential witness with
   `padCompatStartingMethodR_isNonDegenerate r` for non-degeneracy.

3. **Phase B.3** (optional / stretch) — reconciliation lemmas
   (`paddedREulerGLM 1 = padded2DEulerGLM`, etc.) close by
   `ext + simp` since `Matrix.of`-bodies vs `!![..]`-bodies unfold
   differently. Ship only if clean; do not block on them.

After Phase B lands cleanly, cycle 164 should pivot to a fresh
entity. The cycle 162 strategy's recommended candidate list (in
estimated tractability order):
1. `def:451A` G-stable (§451, Chapter 4 LMM) — definition +
   non-vacuity witness.
2. `def:422B` underlying one-step method (§422, Chapter 4 LMM) —
   definition + companion theorem `thm:422A`.
3. `def:442A` principal sheet (§441, Chapter 4 LMM) — definition.
4. `thm:535A` underlying one-step method (GLM, §535, Chapter 5) —
   GLM analog of `thm:422A`.
5. `thm:541A` types of DIMSIM methods (§541, Chapter 5).
