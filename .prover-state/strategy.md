# Cycle 509 Strategy — §422 Phase α'.7.0 `nchildPolynomial` signature + n ≤ 4 base cases

## §A. Context

Cycle 508 (`task_results/cycle_508.md`, commit `fac7c67`) closed by
shipping the 1556-LOC Phase α'.7 `nchildPolynomial` scoping doc at
`.prover-state/issues/def_422B_phase_alpha_prime_7_nchildPolynomial_scoping.md`.
The §422 axiom-clean streak now stands at **79 substantive + 8 doc**
(cycles 336–508).

**Cycle 509 is the first Lean-implementation cycle of the Phase α'.7
multi-cycle track.** It is the entry point named explicitly in the
cycle 508 scoping doc §9 and §6.0, in `task_results/cycle_508.md`
"Suggested next approach", and in the cycle 508 strategy §H.

The sole code-level sorry remains
`OpenMath/Chapter4/Section422.lean:2279` (cycle 365's
`powRep_sum_eq_of_strict_subtree_agreement` general body, **144 cycles
open**). Cycle 509 does **NOT** attempt this sorry — it is multi-cycle
Phase β.2 / δ / ε territory (cycles ~520–525+) gated on Phase α'.7's
parametric infrastructure.

## §B. Cycle 509 deliverable (single substantive item)

Execute **Phase α'.7.0** per the cycle 508 scoping doc §6.0 / §9.2:
ship the parametric `nchildPolynomial` family signature, the
`nchildCrossTerm` skeleton, and 5 calibration theorems reducing the
parametric form to the existing per-arity helpers at n ∈ {0, 1, 2, 3,
4}.

* **Target file**: `OpenMath/Chapter4/Section422.lean`, insertion point
  immediately after `tetrachildPolynomial` (line ~14869+) and before
  `inversePolyTree` (line 14905).
* **LOC budget**: ~200–300 LOC, **MED risk**.
* **Sorry count target**: **5 (unchanged)** — the new helpers must
  compile to closed bodies; no scaffold sorries past end-of-cycle.
* **Axiom-clean target**: `#print axioms` returns `[propext,
  Classical.choice, Quot.sound]` on all 5 new calibration theorems and
  on `nchildPolynomial` itself.
* **Warm rebuild target**: ≤ 8 min (cycle 508 baseline ~5 min on the
  19299-LOC file; cycle 509 expected ~19500–19600 LOC).

### §B.1 Required components (in order of file insertion)

#### §B.1.1 `nchildPolynomial` definition

Per the cycle 508 scoping doc §2.1.3 + §4.1 recommendations:

* **Indexing convention**: `Fin n` (forced by Discovery #3 in
  `cycle_508.md` — cycle 358's `_inv_mk` already uses `Fin n` for the
  stage-index `i`, so the cycle 358 bridge in Phase α'.7.2 will need
  `Fin n`-typed manipulation regardless).

* **Body form**: subset-sum (Option A) per §4.1. Strawman shape:

  ```lean
  noncomputable def nchildPolynomial (n : ℕ)
      (children : Fin n → RT)
      (inv_children : Fin n → ℝ)
      (f : RT → ℝ) : ℝ :=
    -- Block ∅: all-constant
    -(f RootedTree.vertex * ∏ i : Fin n, inv_children i)
    -- Single-child blocks
    - ∑ ℓ₀ : Fin n,
        (∏ i ∈ Finset.univ.erase ℓ₀, inv_children i)
          * f (OpenMath.Chapter3.Section310.RootedTree.mk [children ℓ₀])
    -- Mixed cross-term blocks (|S| ∈ {2, …, n-1})
    + nchildCrossTerm n children inv_children f
    -- Self-kernel block
    - f (OpenMath.Chapter3.Section310.RootedTree.mk
            (List.ofFn (fun i : Fin n => children i)))
  ```

  Important: `nchildCrossTerm` must be **defined first** (or
  forward-declared via mutual block) so `nchildPolynomial` can
  reference it.

* **Termination**: no recursion at this stage — the body is a flat
  expression over `Finset` aggregates, so Lean's structural recursion
  is not invoked. R1 (termination obstruction) does not bite at cycle
  509 because `nchildCrossTerm` at n ≤ 4 dispatches via `match n with`
  and recurses only into the existing per-arity helpers (themselves
  non-recursive).

#### §B.1.2 `nchildCrossTerm` definition

Per §5.1 + §6.0's "Deliverable 2": ship a `match n with` skeleton
with arms for n ∈ {0, 1, 2, 3, 4} reducing to existing per-arity
helpers; higher-n arms return 0 placeholder.

```lean
noncomputable def nchildCrossTerm (n : ℕ)
    (children : Fin n → RT) (inv_children : Fin n → ℝ)
    (f : RT → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => bichildCrossTerm (children 0) (children 1) f
  | 3 => trichildCrossTerm (children 0) (children 1) (children 2) f
  | 4 => tetrachildCrossTerm
            (children 0) (children 1) (children 2) (children 3) f
  | _ + 5 => 0  -- placeholder; Phase α'.7.3+ extends this
```

Notes:

* The existing helpers' signatures (verified by `grep` against HEAD):
  - `bichildCrossTerm (t₁ t₂ : RT) (f : RT → ℝ)` at line 14362.
  - `monochildCrossTerm (c : RT) (f : RT → ℝ)` at line 14429 (used at
    n = 1 indirectly via the single-child block, NOT here at n = 1).
  - `trichildCrossTerm` at line 14495.
  - `tetrachildCrossTerm` at line 14668.
* At n = 1, the cycle 392 `monochildCrossTerm` is **already absorbed
  into the single-child block** of `nchildPolynomial`, so
  `nchildCrossTerm 1 _ _ _ = 0` is correct (the |S| = 1 block is
  promoted to a single-child block, not a "cross-term" block).
* The `_ + 5 => 0` catch-all is the **same R6.B-style obstruction**
  as `inversePolyTree`'s catch-all at k ≥ 5 — it is **intentional**
  and is documented in cycle 509 task results §Faithfulness as a
  scoping-level limitation that Phase α'.7.3+ (cycle 512+) extends.
  The faithfulness contract for cycle 509 is **only at n ≤ 4**.

#### §B.1.3 Calibration theorems (5 ships)

Ship 5 theorems proving the parametric form reduces to existing
helpers at n ∈ {0, 1, 2, 3, 4}. Naming convention follows §4.3 of the
scoping doc:

1. **`nchildPolynomial_zero`**: at n = 0, the parametric form equals
   `-f vertex` (matches `inversePolyTree (mk []) f`). Proof: `unfold
   nchildPolynomial nchildCrossTerm; simp` should close.

2. **`nchildPolynomial_eq_one`** (or `_monochildPolynomial` if a
   monochild helper is introduced): at n = 1 with `children = ![c]`,
   `inv_children = ![inv_c]`, the parametric form equals the cycle
   392 / 391 monochild expansion. Proof: `unfold nchildPolynomial
   nchildCrossTerm; simp [Fin.sum_univ_one, Finset.prod_singleton];
   ring`.

3. **`nchildPolynomial_eq_bichildPolynomial`** at n = 2: parametric
   form equals `bichildPolynomial c₁ c₂ inv₁ inv₂ f`. Proof: `unfold
   nchildPolynomial nchildCrossTerm bichildPolynomial; simp
   [Fin.sum_univ_two, Fin.prod_univ_two]; ring`.

4. **`nchildPolynomial_eq_trichildPolynomial`** at n = 3: parametric
   form equals `trichildPolynomial c₁ c₂ c₃ inv₁ inv₂ inv₃ f`. Proof:
   same template with `Fin.sum_univ_three` / `Fin.prod_univ_three`.

5. **`nchildPolynomial_eq_tetrachildPolynomial`** at n = 4: parametric
   form equals `tetrachildPolynomial c₁ c₂ c₃ c₄ inv₁ inv₂ inv₃ inv₄
   f`. Proof: `unfold nchildPolynomial nchildCrossTerm
   tetrachildPolynomial; simp [Fin.sum_univ_four / Fin.prod_univ_four
   if they exist, else `Fin.sum_univ_succ` × 4]; ring`.

For each, the headline statement should use `Matrix.cons` (`![..]`)
literals to populate the `Fin n → α` arguments — this matches the
cycle 510 calibration witness style (§6.1 of the scoping doc) and
keeps the proofs mechanical.

If the n = 3 or n = 4 cases prove tricky (e.g., `Fin.sum_univ_four`
is not in Mathlib), fall back to per-position `Fin.sum_univ_succ`
unfolds followed by `ring`. This is exactly the pattern in
`feedback_fin_sum_univ_succ_coerce.md`: prepend `show (∑ i : Fin (n +
1), …) = …` to coerce the binder type before applying
`Fin.sum_univ_succ`.

### §B.2 Mathlib hooks to consider

Per the cycle 508 scoping doc §6.2's hooks list (carried over to
cycle 509 where relevant):

* `Finset.prod_univ_zero`, `Finset.prod_univ_one`, `Finset.prod_univ_two`
  — likely exist; use `lean_local_search` (or `lean_loogle` with
  pattern `∏ i ∈ Finset.univ, _ = _`) to verify before citing.
* `Fin.sum_univ_zero`, `Fin.sum_univ_one`, `Fin.sum_univ_two`,
  `Fin.sum_univ_three`, `Fin.sum_univ_four` — `Fin.sum_univ_two` is
  standard; higher arity may not exist as named lemmas. Fall back to
  `Fin.sum_univ_succ` cascade (see `feedback_fin_sum_univ_succ_coerce.md`).
* `Matrix.cons_val_zero`, `Matrix.cons_val_one`, `Matrix.cons_val_succ`
  — for unpacking `![c₁, c₂, c₃, c₄]` in calibration proofs.
* `List.ofFn` lemmas: `List.ofFn_succ`, `List.ofFn_zero` — for the
  self-kernel term in `nchildPolynomial`.

If a hook is missing, **build it as a private helper lemma in
Section422.lean** (per CLAUDE.md "If Mathlib is missing something,
**build it yourself**"). Do NOT block on Mathlib gaps.

### §B.3 Bookkeeping deliverables

1. **`extraction/formalization_data/lean_status.json`**: bump
   `def:422B.cycle_completed_at` from 508 to 509; append a one-line
   note to `def:422B.note` reflecting the Phase α'.7.0 ship.
   `status` stays `partial`.

2. **`plan.md`**: append a cycle 509 closure paragraph to the
   `def:422B` row's note, mirroring the cycle 506/507/508 format
   ("Cycle 509 ships §422 Phase α'.7.0: `nchildPolynomial` family
   signature + n ≤ 4 base cases reducing to per-arity helpers (5
   calibration theorems)...").

3. **`.prover-state/task_results/cycle_509.md`**: standard 7-section
   format (Worked on / Approach / Result / Faithfulness check / Dead
   ends / Discovery / Suggested next approach).

## §C. What NOT to do this cycle

* Do **NOT** attempt the **cycle 358 → `nchildPolynomial` bridge
  theorem** (`elementaryWeightQ_phi_inv_eq_nchildPolynomial`). That
  is Phase α'.7.2 / cycle 511's deliverable per scoping doc §6.2 (~300–
  500 LOC, **HIGH risk**, `2^n`-way case analysis). Cycle 509 ships
  the parametric form's calibration against per-arity helpers ONLY —
  not against cycle 358's `_inv_mk` source-of-truth formula.

* Do **NOT** extend `nchildCrossTerm` past n = 4. The `_ + 5 => 0`
  catch-all is intentional. Phase α'.7.3 (cycle 512+) ships the k = 5
  closed-form witness `_inv_bushy₅`; Phase α'.7.5 (cycle 517+) extends
  `nchildCrossTerm` to n = 5. Do NOT pre-empt either.

* Do **NOT** touch the cycle 365 grandfathered sorry at
  `Section422.lean:2279`. It is the Phase ε (cycle 524+) target,
  dependent on Phase α'.7's full pipeline.

* Do **NOT** refactor `inversePolyTree` (line 14905) to use
  `nchildPolynomial`. The two helpers **coexist** until the cycle 358
  bridge lands at cycle 511. Per scoping doc §9.4: "The new helper
  coexists with the per-arity cascade until the bridge theorem is in
  place."

* Do **NOT** ship calibration witnesses against cycle 499–504's
  empirical `_inv_*` theorems (bushy₄, vvvc, vvcc, vccc, cccc).
  Those are Phase α'.7.1 / cycle 510's deliverables per scoping doc
  §6.1. Cycle 509's 5 calibration theorems target the per-arity
  helpers (`bichildPolynomial`, `trichildPolynomial`, etc.), NOT the
  cycle 499–504 empirical surface.

* Do **NOT** introduce a new `class` or `structure`. The deliverables
  are `def`s and `theorem`s only. (Per CLAUDE.md: any new
  `class`/`structure` requires a concrete witness in the same cycle.)

* Do **NOT** introduce `axiom` or `constant` declarations.

* Do **NOT** raise `maxHeartbeats` above 200000. If a calibration
  proof times out, decompose it (e.g., split the n = 4 calibration
  into a 4-step manual `show` chain rather than letting `ring` close
  the whole thing).

* Do **NOT** compile `OpenMath/Chapter4/Section441.lean` — it is
  GPFS-blocked (43+ consecutive multi-minute timeouts, per
  `cycle_182_gpfs_slowness.md`). Cycle 509's `lake env lean`
  verification target is **`OpenMath/Chapter4/Section422.lean` only**.

* Do **NOT** modify `scripts/autonomous_loop.py` or address any
  tautology-scanner / empty-stuck-on / consultant-loop issues — those
  are loop-maintainer territory per
  `.prover-state/issues/tautology_scanner_false_positives.md`.

* Do **NOT** pivot to a fresh entity. The §422 cluster's Phase α'.7
  Lean track is the natural compounding move. Pivot decisions for
  cycle ~519+ are explicitly deferred to scoping doc §8 R9 and §6.6.

* Do **NOT** ship a sorry-first scaffold without single-cycle closure.
  Per scoping doc §10 + the cycle 138/139 + cycle 149/150 + cycle
  200/201 rollback precedent (recorded in cycle 508 strategy §D):
  cycle 509's `nchildPolynomial`, `nchildCrossTerm`, and the 5
  calibration theorems must all be **fully closed** by end-of-cycle.
  Sorry count stays at 5.

## §D. Approaches explicitly known to fail (do not retry)

Cycle 509 inherits the following failure modes from prior §422
cycles and the cycle 508 scoping doc §8 risk inventory:

* **`simp [recursive-def, name-eq-thm]` over-unfolds** — per memory
  `feedback_simp_recursive_def_overunfolds.md`. When proving the
  calibration theorems, do NOT use `simp [nchildPolynomial,
  nchildCrossTerm, bichildPolynomial, …]`. Use targeted `unfold` +
  `simp [Fin.sum_univ_succ, Finset.prod_univ_succ, …]` + `ring`.

* **`ring` def opacity** — per memory `feedback_ring_def_opacity.md`.
  `ring` cannot bridge `f (mk [args])` to `f namedTree` when
  `namedTree` is a non-reducible `def`. For cycle 509's calibration
  theorems, this is unlikely to bite since the helpers' bodies do not
  reference named trees like `cherry` or `broom₃` — but if the n = 3
  or n = 4 calibration's `ring` step fails, insert `show ...` to
  canonicalize before `ring`.

* **`lake env lean` does not refresh olean** — per memory
  `feedback_lake_env_lean_no_olean_update.md`. Cycle 509 will use
  `lake env lean OpenMath/Chapter4/Section422.lean` for the
  per-iteration compile check, but the final axiom verification
  (`#print axioms nchildPolynomial`, etc.) requires `lake build
  OpenMath.Chapter4.Section422` first to refresh the olean.

* **Fin.sum_univ_succ binder-type mismatch** — per memory
  `feedback_fin_sum_univ_succ_coerce.md`. `Fin.sum_univ_succ` won't
  match `∑ i : Fin (cs.length), …` directly. The cycle 509 calibration
  proofs at n = 3, 4 may need `show (∑ i : Fin (n + 1), …) = …`
  prepends to coerce the binder type definitionally.

* **`alphaWeight`-style definition smuggling (cycle 250)** — defined
  `α(t) = 1/γ(t)` (smuggled shortcut) instead of textbook
  combinatorial form. Cycle 509's `nchildPolynomial` is **NOT a
  Butcher concept**; it is internal infrastructure (faithfulness
  contract documented in scoping doc §8.6 R6: contract via the cycle
  358 bridge in Phase α'.7.2, not via direct textbook equivalence).
  The cycle 509 task results §Faithfulness must explicitly state
  this: `nchildPolynomial` is an internal helper, faithfulness
  contract is via cycle 358 bridge (Phase α'.7.2 / cycle 511), not
  direct textbook correspondence.

* **Sorry-first scaffold without single-cycle closure**: see §C above
  for the cycle 138/139 + 149/150 + 200/201 rollback precedent. Cycle
  509 must close every sorry it opens.

## §E. Cycle 509 success criteria

* `nchildPolynomial` and `nchildCrossTerm` defined in
  `OpenMath/Chapter4/Section422.lean` after `tetrachildPolynomial`
  (line ~14869+) and before `inversePolyTree` (line 14905), per
  scoping doc §6.0 + §9.2.

* 5 calibration theorems shipped (`nchildPolynomial_zero`,
  `nchildPolynomial_eq_one` or analogue at n = 1,
  `_eq_bichildPolynomial`, `_eq_trichildPolynomial`,
  `_eq_tetrachildPolynomial`), each proved without sorry and closing
  by `unfold` + `simp` + `ring` or a small `show`-canonicalize +
  `ring` template.

* **Sorry count**: 5 (unchanged — 4 docstring + 1 grandfathered cycle
  365 at line 2279). `grep -c sorry OpenMath/Chapter4/Section422.lean
  = 5`.

* **Axiom-clean**: `#print axioms nchildPolynomial`,
  `#print axioms nchildCrossTerm`, and `#print axioms
  nchildPolynomial_eq_<...>` (×5) each return `[propext,
  Classical.choice, Quot.sound]`.

* **Build status**: `lake build OpenMath.Chapter4.Section422`
  succeeds (≤ 8 min warm rebuild target).

* **LOC delta**: ~200–300 in `OpenMath/Chapter4/Section422.lean`
  (19299 → ~19500–19600).

* **§422 axiom-clean streak**: 79 substantive + 8 doc → **80
  substantive + 8 doc** (cycles 336–509).

* `extraction/formalization_data/lean_status.json` `def:422B.cycle_completed_at`
  = 509 (status unchanged: `partial`).

* `plan.md` `def:422B` row has cycle 509 closure paragraph appended.

* `.prover-state/task_results/cycle_509.md` written with the standard
  7-section format.

## §F. Faithfulness check (cycle 509)

Per CLAUDE.md's "Pre-Commit Faithfulness Checklist":

### For `nchildPolynomial` (new `def`):

* **Entity correspondence**: `nchildPolynomial` is **NOT a Butcher
  concept**. It is internal infrastructure for the §422 cluster's
  Phase β.2 obstruction at k ≥ 5. The faithfulness contract is via
  the cycle 358 bridge theorem (Phase α'.7.2 / cycle 511), not via
  direct textbook equivalence. **Document this explicitly** in cycle
  509 task results §Faithfulness — name the theorem `nchildPolynomial`
  helper, NOT a Butcher concept, contract pending Phase α'.7.2 cycle
  511 bridge.

* **Definition-smuggling check**: cycle 509 ships only the parametric
  form's signature; it does NOT claim equivalence to any Butcher-level
  theorem. The 5 calibration theorems prove equivalence to the
  **existing internal helpers** (`bichildPolynomial`, etc.), which
  themselves are pre-existing infrastructure (cycle 387/399/500). No
  definition smuggling at the cycle 509 level — the smuggling-risk
  surfaces at cycle 511's cycle 358 bridge, NOT here.

### For `nchildCrossTerm` (new `def`):

* Same faithfulness analysis as `nchildPolynomial`: internal helper,
  contract via cycle 511 bridge.

* The `_ + 5 => 0` catch-all is **NOT** a smuggling: it is an
  explicit scoping-level limitation that documents cycle 509 commits
  only through n ≤ 4. The catch-all behaviour at k ≥ 5 will be
  replaced at Phase α'.7.5 (cycle 517+).

### For each of the 5 calibration theorems:

* **Tautology check**: the conclusion is `nchildPolynomial n … = …childPolynomial …`,
  NOT a re-export of any hypothesis. Real algebraic content (the
  parametric form unfolds to the per-arity form). Not a tautology.

* **Identity check**: proofs are `unfold + simp + ring` (or
  `show ... ; ring`); no `exact h` short-circuits. Each theorem
  performs algebraic simplification, not identity dispatch.

* **Hypothesis strength check**: hypotheses are the children + inv_children
  + f values — minimal, matches the per-arity helpers' hypothesis sets
  verbatim. No strengthening.

* **Absent theorem check**: each calibration theorem is shipped in
  closed form. No "will be proved with sorry" comments.

### Pre-commit faithfulness scan command:

```bash
grep -c sorry OpenMath/Chapter4/Section422.lean    # expect 5
grep "axiom\|constant" OpenMath/Chapter4/Section422.lean | wc -l  # expect 0 new
```

## §G. Aristotle batch

**LOW utility for cycle 509.** Per scoping doc §6.0: "Aristotle: low
utility — these are mechanical reductions. Skip Aristotle for cycle
509."

The 5 calibration theorems are each ~5–20 LOC `unfold + simp + ring`
closures; manual proof is faster than the 30-minute Aristotle
turnaround.

**Exception**: if the n = 4 calibration's `ring` step fails
unexpectedly (e.g., the `tetrachildCrossTerm`'s 5-branch cascade
doesn't fold cleanly via `simp [tetrachildCrossTerm]`), submit
**ONE** Aristotle job for the n = 4 calibration only and continue
manually with n ≤ 3 in parallel. Do NOT batch all 5 to Aristotle —
the n ≤ 3 cases should close in seconds manually.

## §H. Cycle 509 entry point (concrete step-by-step)

Follow this sequence; do not improvise:

1. **Pre-flight reading** (15 min):
   - Read this strategy (§A–§J) and `.prover-state/issues/def_422B_phase_alpha_prime_7_nchildPolynomial_scoping.md`
     §§1–11 (skim §3 block decomposition + §4 strawman + §6.0 Phase
     α'.7.0 + §9 cycle 509 entry point in full).
   - Read `OpenMath/Chapter4/Section422.lean` at lines 14362–14905
     to inspect the existing per-arity helpers' bodies + signatures.
   - Read cycle 358's `elementaryWeightQ_phi_inv_mk` body at
     `OpenMath/Chapter4/Section422.lean:582+` for the `Fin n`
     indexing convention precedent.

2. **Verify the insertion point** (5 min):
   ```bash
   grep -n "^noncomputable def tetrachildPolynomial\|^noncomputable def inversePolyTree" \
     OpenMath/Chapter4/Section422.lean
   ```
   Expect `14869` (tetrachildPolynomial) and `14905` (inversePolyTree).
   The new helpers go between these two.

3. **Ship `nchildCrossTerm` first** (~30 min):
   - Write the `match n with` skeleton per §B.1.2.
   - Compile-check: `lake env lean OpenMath/Chapter4/Section422.lean`
     (~5 min warm). Sorry count should remain at 5 (no new sorries
     introduced by this def).

4. **Ship `nchildPolynomial` second** (~30 min):
   - Write the body per §B.1.1's subset-sum strawman.
   - Compile-check. Sorry count remains at 5.

5. **Ship the 5 calibration theorems** (~60 min):
   - `nchildPolynomial_zero` (5–10 LOC, mechanical).
   - `nchildPolynomial_eq_one` (10–20 LOC; may need `Fin.sum_univ_one`
     + `Finset.prod_singleton`).
   - `nchildPolynomial_eq_bichildPolynomial` (15–25 LOC; `Fin.sum_univ_two`
     + `Fin.prod_univ_two` or fallback to `Fin.sum_univ_succ` cascade).
   - `nchildPolynomial_eq_trichildPolynomial` (20–35 LOC; same
     template, n = 3).
   - `nchildPolynomial_eq_tetrachildPolynomial` (25–50 LOC; same
     template, n = 4).
   - Compile-check after each theorem.

6. **Verify** (15 min):
   - `lake build OpenMath.Chapter4.Section422` (~5–8 min warm) — needed
     before `#print axioms` checks per memory
     `feedback_lake_env_lean_no_olean_update.md`.
   - Run `#print axioms nchildPolynomial`, `#print axioms
     nchildCrossTerm`, `#print axioms nchildPolynomial_eq_<arity>`
     for each of the 5 theorems. Each should print `[propext,
     Classical.choice, Quot.sound]`.
   - `grep -c sorry OpenMath/Chapter4/Section422.lean` → 5.

7. **Bookkeeping** (15 min):
   - Bump `extraction/formalization_data/lean_status.json`
     `def:422B.cycle_completed_at` from 508 to 509; append a one-line
     note.
   - Append a cycle 509 closure paragraph to `plan.md`'s `def:422B`
     row.
   - Write `.prover-state/task_results/cycle_509.md` with the standard
     7-section format.

8. **Commit** (5 min):
   - `git add` the modified files (`OpenMath/Chapter4/Section422.lean`,
     `extraction/formalization_data/lean_status.json`, `plan.md`,
     `.prover-state/task_results/cycle_509.md`, plus any heartbeat /
     history updates).
   - Commit with message format matching cycle 508: "Cycle 509 —
     §422 Phase α'.7.0 `nchildPolynomial` family signature + n ≤ 4
     base cases (5 calibration theorems) ship."

**Total wall time estimate**: ~3–4 hours including compile waits.
Well under any cycle time budget.

## §I. Note on the recurring "empty stuck-on" template phantom

The cycle 508 prompt may again exhibit the empty-stuck-on phantom
pattern documented across cycles 015 / 040 / 174 / 180 / 248 / 263 /
491 / 505 / 506 / 507 / 508 (11 confirmed instances now). The cycle 509
worker should NOT diagnose this pattern as a real blocker; cycle 509's
deliverable is Phase α'.7.0 per §B above. If the consultant phase
fires against cycle 509's ship, the standing recommendation from
`consultant_advice_cycle_248.md` §I and
`tautology_scanner_false_positives.md` §D3 applies: the supervisor's
prompt-builder should short-circuit on infrastructure-development
cycles where the strategy specifies the exact deliverable. Worker
MUST NOT modify `scripts/autonomous_loop.py`.

## §J. Bottom-line directive

Cycle 509 ships **3 things into `OpenMath/Chapter4/Section422.lean`**:

1. `noncomputable def nchildPolynomial (n : ℕ) (children : Fin n → RT)
   (inv_children : Fin n → ℝ) (f : RT → ℝ) : ℝ` — subset-sum body per
   §B.1.1.

2. `noncomputable def nchildCrossTerm (n : ℕ) (children : Fin n → RT)
   (inv_children : Fin n → ℝ) (f : RT → ℝ) : ℝ` — `match n with`
   skeleton at n ∈ {0, 1, 2, 3, 4} + `_ + 5 => 0` catch-all per §B.1.2.

3. **5 calibration theorems** at n ∈ {0, 1, 2, 3, 4} reducing the
   parametric form to the per-arity helpers per §B.1.3.

Plus the standard bookkeeping (`lean_status.json` cycle counter bump,
`plan.md` closure paragraph, `task_results/cycle_509.md`).

**LOC delta**: ~200–300 in `Section422.lean`. **Sorry count
unchanged at 5**. **Axiom-clean on all 5 new theorems**. §422 streak
advances to **80 substantive + 8 doc**.

Cycle 510 (Phase α'.7.1) consumes cycle 509's calibration theorems
to ship the n = 4 calibration witnesses against cycles 499–504's
empirical surface (`bushy₄`, `vvvc`, `vvcc`, `vccc`, `cccc`). Cycle
511 (Phase α'.7.2) ships the cycle 358 bridge theorem.

### §J.1 Time budget

* Pre-flight + insertion-point verification: ~20 min.
* `nchildCrossTerm` + `nchildPolynomial` definitions: ~60 min.
* 5 calibration theorems: ~60 min.
* Compile + axiom verification: ~20 min.
* Bookkeeping + commit: ~20 min.
* **Total**: ~3 hours.

No Aristotle wait (§G). No GPFS-blocked file compiles (Section441 is
explicitly excluded per §C).

### §J.2 Quality bar for the cycle 509 ship

* **Mechanical proof shape**: each of the 5 calibration theorems
  should close in ≤ 50 LOC via `unfold + simp + ring` or `unfold +
  show + ring`. If any theorem exceeds 50 LOC, **stop** and re-read
  the existing helpers' bodies to identify what's misaligning — do
  NOT bandage with `nlinarith` / `polyrith` / `field_simp` cascades.

* **No sorry-first**: every component must be closed by
  end-of-cycle. Per §C: cycle 138/139 + 149/150 + 200/201 rollback
  precedent — scaffold sorries past end-of-cycle get rolled back.

* **Faithfulness explicit**: cycle 509 task results §Faithfulness
  must state that `nchildPolynomial` and `nchildCrossTerm` are
  internal helpers (NOT Butcher concepts), faithfulness contract
  pending the Phase α'.7.2 cycle 511 bridge. Document the `_ + 5 =>
  0` catch-all as a scoping-level limitation.

* **No premature generalization**: do NOT attempt a uniform-in-n
  `nchildPolynomial_correct` meta-theorem at cycle 509. That is
  Phase α'.7.6 / cycle 519+ territory (§6.6 Option (iii)). Cycle 509
  ships only the parametric form + 5 calibration witnesses.
