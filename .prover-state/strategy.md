# Cycle 243 Strategy

## Context (read first)

Cycle 242 closed `thm:523B` (algebraic-stability inequality) axiom-clean,
completing §523 in full (`thm:523A` cycle 241 + `thm:523B` cycle 242).
The cycle 242 task results suggested three candidates for cycle 243:

1. **`thm:521B`** (Maximum stability order for given steps) — flagged as
   "single-cycle candidate if it reduces to a degree-counting argument".
2. **`thm:535A`** (Underlying one-step method, GLM) — likely needs §530-§534.
3. **§523 residual helper** — stretch, ~10 LOC.

Planner inspected entity JSONs:

* **`thm:521B`** is **NOT a single-cycle target**. Butcher's proof
  requires contour integration (`(1/2πi) ∮ φ(t) exp_p*(tz) dt` over a
  counter-clockwise contour `C` with radius `R > k`), partial-fraction
  expansion of `φ(t) = Π (t+j)^{-νj-1}`, and an existence + non-existence
  induction on `k`. Multi-cycle infrastructure (Mathlib's contour-integral
  framework + identity-of-meromorphic-functions arguments).
* **`thm:541A`** (DIMSIM types) is similarly NOT single-cycle — Taylor
  expansion analysis plus §532 order-theory infrastructure.
* **`def:422B`** (underlying one-step method, LMM) — definitional but
  references `G_1` (group of elementary weight functions on trees) and
  the (422a) defining equation; requires §388 group infrastructure not
  fully in place.
* **`def:388F`** (commutator condition) — definitionally short but
  requires a tree-horizontal-product `tu` that is not yet in
  `OpenMath/Chapter3/Section301.lean`.

**Conclusion**: among the planner-suggested candidates, only the **§523
residual helper** is a certain single-cycle ship. To make the cycle
substantive, P1 ships the residual helper *and* P2 investigates one
additional fresh entity for cycle 244 planning purposes.

---

## Priority 1 (ship target) — `algebraicStability_residual`

**Location**: `OpenMath/Chapter5/Section523.lean`, **insert immediately after** `algebraicStability_identity` (line 222) and **before** its non-vacuity `example` block (line 234). Place the new theorem in the same `namespace OpenMath.Chapter5.Section510` block.

**Statement** (exact signature — copy verbatim, no modifications):

```lean
/-- *Algebraic-stability residual form (§523 corollary of
`algebraicStability_identity`).* Under the same hypotheses as
`algebraicStability_identity` (symmetric `D` and the GLM step
equations `hStage`, `hOut`), the difference `‖y_next‖²_G − ‖y_prev‖²_G`
factors as `2⟨hF, Y⟩_D − ‖hF ⊕ y_prev‖²_M`.

This is the textbook stepping-stone between `thm:523A`'s identity
(an equation of three terms) and `thm:523B`'s inequality. No sign
hypotheses are needed: it is a pure algebraic rearrangement. -/
theorem GeneralLinearMethod.algebraicStability_residual
    (M : GeneralLinearMethod s r)
    (D : Matrix (Fin s) (Fin s) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ)
    (hD : D.IsSymm)
    (h : ℝ) (F Y : Fin s → ℝ) (y_prev y_next : Fin r → ℝ)
    (hStage : ∀ i, Y i = h * (∑ j, M.A i j * F j) + ∑ j, M.U i j * y_prev j)
    (hOut : ∀ i, y_next i = h * (∑ j, M.B i j * F j) + ∑ j, M.V i j * y_prev j) :
    y_next ⬝ᵥ (G *ᵥ y_next) - y_prev ⬝ᵥ (G *ᵥ y_prev)
      = 2 * ((fun i => h * F i) ⬝ᵥ (D *ᵥ Y))
        - (Sum.elim (fun i => h * F i) y_prev)
            ⬝ᵥ (M.algebraicStabilityMatrix D G *ᵥ
                  Sum.elim (fun i => h * F i) y_prev) := by
  have hId := M.algebraicStability_identity D G hD h F Y y_prev y_next hStage hOut
  linarith
```

**Expected proof body**: 2 lines (`have hId := …; linarith`). The
identity from cycle 241 has the shape `‖y_next‖²_G = ‖y_prev‖²_G + …`,
so rearranging to `‖y_next‖²_G − ‖y_prev‖²_G = …` is a `linarith` away.

**Risk**: very low. The identity is named, `linarith` handles the linear
rearrangement of three real-valued terms.

**Faithfulness check (mandatory)**:

* Entity ID: this is a *new helper lemma* not in
  `extraction/formalization_data/entities/`. It is **infrastructure
  for §523**, not a textbook entity. Document this in the docstring
  (already in the template above). Do **NOT** add a `lean_status.json`
  row for it.
* Tautology check: conclusion is *not* a hypothesis; the equation
  reorganises three terms from `hId`. ✓
* Identity check: proof is `linarith` after `have hId`, not `exact h`. ✓
* Hypothesis strength: identical hypothesis set as
  `algebraicStability_identity` (cycle 241). No new strengthening. ✓
* Smuggling: no new `def`, `structure`, or `class`. ✓

**Non-vacuity** (mandatory, immediately after the theorem):

Add a one-witness `example` mirroring cycle 241/242's pattern at
`(s, r) = (1, 1)` `explicitEulerGLM` with `D = Matrix.diagonal d`,
`G = Matrix.diagonal g`. Take `hStage`/`hOut` as hypotheses (no
concrete construction needed). The example body is:

```lean
example (d g h : ℝ) (F Y : Fin 1 → ℝ) (y_prev y_next : Fin 1 → ℝ)
    (hStage : ∀ i, Y i =
      h * (∑ j, explicitEulerGLM.A i j * F j) + ∑ j, explicitEulerGLM.U i j * y_prev j)
    (hOut : ∀ i, y_next i =
      h * (∑ j, explicitEulerGLM.B i j * F j) + ∑ j, explicitEulerGLM.V i j * y_prev j) :
    y_next ⬝ᵥ (Matrix.diagonal (fun _ : Fin 1 => g) *ᵥ y_next)
      - y_prev ⬝ᵥ (Matrix.diagonal (fun _ : Fin 1 => g) *ᵥ y_prev)
      = 2 * ((fun i => h * F i) ⬝ᵥ (Matrix.diagonal (fun _ : Fin 1 => d) *ᵥ Y))
        - (Sum.elim (fun i => h * F i) y_prev)
            ⬝ᵥ (explicitEulerGLM.algebraicStabilityMatrix
                  (Matrix.diagonal (fun _ : Fin 1 => d))
                  (Matrix.diagonal (fun _ : Fin 1 => g)) *ᵥ
                  Sum.elim (fun i => h * F i) y_prev) :=
  explicitEulerGLM.algebraicStability_residual _ _
    (Matrix.isSymm_diagonal _) h F Y y_prev y_next hStage hOut
```

**Verification checklist**:

1. `mcp__lean-lsp__lean_diagnostic_messages` on
   `OpenMath/Chapter5/Section523.lean` returns no errors and no
   warnings.
2. `mcp__lean-lsp__lean_verify` on
   `OpenMath.Chapter5.Section510.GeneralLinearMethod.algebraicStability_residual`
   returns exactly `[propext, Classical.choice, Quot.sound]`.
3. `grep -c sorry OpenMath/Chapter5/Section523.lean` returns 0.

This ships independently of P2. If P2 stalls, P1 alone is a valid
cycle deliverable (~30 LOC of substantive content).

---

## Priority 2 (stretch) — investigate fresh `[ ]` entity

**Only attempt P2 after P1 lands.** If P1 hits any unexpected blocker
(non-existent Mathlib lemma, etc.), stop and document.

### P2 deliverables, in increasing order of ambition

**(P2a) Companion §523 lemma — preferred if budget allows**

Add ONE small companion lemma to `Section523.lean`. Candidate
signature:

```lean
/-- *Algebraic-stability via dissipativity bound.* Under the PSD
hypotheses on `M`, symmetric `D`, and a strict dissipativity bound
`⟨hF, Y⟩_D ≤ −c · ‖hF ⊕ y_prev‖²_M / 2` (for some `c ≥ 1`), the
GLM step is strictly contracting:
`‖y_next‖²_G + (c − 1) · ‖hF ⊕ y_prev‖²_M ≤ ‖y_prev‖²_G`. -/
theorem GeneralLinearMethod.algebraicStability_contracting
    (M : GeneralLinearMethod s r)
    (D : Matrix (Fin s) (Fin s) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ)
    (hD : D.IsSymm)
    (hM_psd : (M.algebraicStabilityMatrix D G).PosSemidef)
    (h : ℝ) (F Y : Fin s → ℝ) (y_prev y_next : Fin r → ℝ)
    (hStage : ∀ i, Y i = h * (∑ j, M.A i j * F j) + ∑ j, M.U i j * y_prev j)
    (hOut : ∀ i, y_next i = h * (∑ j, M.B i j * F j) + ∑ j, M.V i j * y_prev j)
    (c : ℝ) (hc : 1 ≤ c)
    (hContract : 2 * ((fun i => h * F i) ⬝ᵥ (D *ᵥ Y))
                  ≤ -(c - 1) * ((Sum.elim (fun i => h * F i) y_prev)
                    ⬝ᵥ (M.algebraicStabilityMatrix D G *ᵥ
                          Sum.elim (fun i => h * F i) y_prev))) :
    y_next ⬝ᵥ (G *ᵥ y_next)
      + (c - 1) * ((Sum.elim (fun i => h * F i) y_prev)
          ⬝ᵥ (M.algebraicStabilityMatrix D G *ᵥ
                Sum.elim (fun i => h * F i) y_prev))
      ≤ y_prev ⬝ᵥ (G *ᵥ y_prev) := by
  have hRes := M.algebraicStability_residual D G hD h F Y y_prev y_next hStage hOut
  have hMq :
      0 ≤ (Sum.elim (fun i => h * F i) y_prev)
            ⬝ᵥ (M.algebraicStabilityMatrix D G *ᵥ
                  Sum.elim (fun i => h * F i) y_prev) := by
    simpa using hM_psd.dotProduct_mulVec_nonneg _
  linarith
```

This generalises cycle 242's `algebraicStability_inequality` (the
`c = 1` case recovers it after the `(c - 1)` term vanishes). Proof
is a `linarith` from the residual (P1) + the PSD bound (cycle 242
pattern). Estimated ~25 LOC + non-vacuity example.

**Faithfulness**: NOT a textbook entity (`thm:523B` is Butcher's
named inequality; this is a strict-contraction strengthening
useful for `thm:523` applications). Document accordingly. No new
`lean_status.json` row.

If P2a elaborates within ~15 min: ship it. If not: switch to P2b.

**(P2b) Document cycle-244 candidate — fallback if P2a stalls**

Write a 2-paragraph note at the end of
`.prover-state/task_results/cycle_243.md` identifying ONE concrete
fresh `[ ]` row from `plan.md` that is NOT blocked by:
- `AN_stability_deferred.md`
- `jordan_canonical_form_missing.md`
- `rouche_theorem_missing.md`
- `cycle_182_gpfs_slowness.md` (§441 cluster)
- the §388 tree-horizontal-product gap (e.g. `def:388F`)
- the §380 thm:381G / thm:381H prerequisite gap

Useful candidates to investigate:
- `lem:319A` (Global truncation error, RK) — analogous to
  `thm:212A` for Euler; check `Section213.lean` for the shape
  template, and `entities/lem_319A.json` for hypotheses.
- `def:442A` (Principal sheet, §441) — definition only; check
  whether it requires §441 infrastructure (likely blocked by GPFS)
  or is self-contained.
- `cor:550C` (Inverse of companion matrix derivative basis) —
  corollary to cycles 138-150's doubly-companion-matrix work;
  check if the seven concrete-`n` stepping stones suffice.
- `thm:443A` (Order arrows for linear multistep methods, §441) —
  also §441-cluster, GPFS-blocked.

Read entity JSONs via `cat
extraction/formalization_data/entities/<id>.json`. Write the
cycle 244 planner-note in the cycle results' "Suggested next
approach" section: include statement, recommended Lean file
location, dependency footprint, and estimated LOC.

Do NOT attempt the proof in cycle 243.

---

## What NOT to attempt

* **Do NOT touch `thm:521B`**. Multi-cycle (contour integration +
  partial fractions). Investigated and ruled out by cycle 243 planner.
* **Do NOT touch `thm:541A`**. Multi-cycle (Taylor expansion analysis
  + §532 order theory).
* **Do NOT touch `def:422B`, `def:388D`, `def:388F`**. All require
  tree-product or §388-group-quotient machinery not yet in
  `Section301.lean` / `Section381.lean`.
* **Do NOT touch §441 path**. Per
  `.prover-state/issues/cycle_182_gpfs_slowness.md`, 44 consecutive
  GPFS timeouts on `Section441.lean` smoke tests. The cycle 240
  worker sidestepped this by creating new `Section441B.lean`; do
  not regress.
* **Do NOT modify `scripts/autonomous_loop.py`**. Per CLAUDE.md
  and `phantom_commit_verdict_pattern.md` — loop-maintainer
  territory.
* **Do NOT raise `maxHeartbeats`** above 200000.
* **Do NOT introduce `axiom` or `constant`**.
* **Do NOT poll Aristotle** — no jobs were submitted by cycle 242.
* **Do NOT alter cycle 241/242 deliverables**
  (`algebraicStability_identity`, `algebraicStability_inequality`,
  or `algebraicStabilityMatrix`). P1's `linarith` consumes
  `algebraicStability_identity` verbatim; do not refactor it.

---

## Past failures to avoid (from attempts.md)

* Cycle 219's `Equivalent.symm` first attempt failed due to
  universe-polymorphism issue (`auto-bound universes pick fresh
  levels per reference`). Section523.lean does not have this concern
  (no `Equivalent` references), but be aware if you investigate any
  §381-related entities in P2.
* Cycle 167 `Section454.lean` learned that `simp only [Matrix.dotProduct]`
  does NOT fire — `dotProduct` is at root namespace, not
  `Matrix.dotProduct`. If you write any `dotProduct` simp invocations
  for P2a, use bare `dotProduct` (already open via `open Matrix` in
  `Section523.lean` line 63).
* Cycle 226's direct tree-induction approaches for compose
  Φ-equivalence failed structurally — **do not** try direct tree
  induction for any §388/§383 entity without first checking whether
  Aristotle has been delegated.

---

## Cycle 243 execution order

1. **(5 min)** Read `OpenMath/Chapter5/Section523.lean` to confirm
   structure (already inspected by planner; file is 314 LOC, no
   sorries, axiom-clean through cycle 242). Use `mcp__lean-lsp__lean_file_outline`
   for a token-efficient overview if needed.
2. **(15 min)** Insert P1 theorem + non-vacuity example via `Edit`
   tool. Run `mcp__lean-lsp__lean_diagnostic_messages` after each
   insertion.
3. **(5 min)** Run `mcp__lean-lsp__lean_verify` on the new theorem;
   confirm axiom-clean (expected
   `[propext, Classical.choice, Quot.sound]`).
4. **(P2 budget, ~30 min)** Either ship P2a if it elaborates within
   the first ~15 min of attempting, OR drop to P2b.
5. **(15 min)** Write `.prover-state/task_results/cycle_243.md`
   following CLAUDE.md template. Include faithfulness check section
   even though P1 is a helper (document the "not a textbook entity"
   status explicitly).
6. **(5 min)** Commit: stage the modified file
   (`OpenMath/Chapter5/Section523.lean`) and the task results.
   Mention "Cycle 243 — §523 algebraicStability_residual SHIPPED"
   in the commit subject. Push.

Total budget: ~70 min P1 path; ~100 min including P2.

---

## Success criteria

* `OpenMath/Chapter5/Section523.lean` compiles cleanly, 0 sorries,
  axiom-clean.
* `algebraicStability_residual` axiom-clean
  (`[propext, Classical.choice, Quot.sound]`).
* Non-vacuity example present and typechecks.
* `task_results/cycle_243.md` documents the deliverable + a
  cycle-244-planner-friendly note (P2b at minimum, P2a if shipped).
* No regression on cycles 241/242 landmarks
  (`algebraicStability_identity`, `algebraicStability_inequality`,
  `algebraicStabilityMatrix`).

Counts as substantive cycle even if P2 yields only the cycle-244
note: P1 alone ships a textbook-stepping-stone helper completing
§523's three-form identity-residual-inequality story.
