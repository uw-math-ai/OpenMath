# Cycle 140 Strategy

## Recap of state at end of cycle 139

* **Sorry count: 0.** Cycle 139 closed cycle 138's regression by removing
  the general-`n` `doublyCompanionMatrix_det_factorization` statement
  from `OpenMath/Chapter5/Section550.lean`. Both the cycle-138 n=1
  witness (`doublyCompanionMatrix_det_factorization_n_one`) and the
  fresh §530 leaf (`def:530A` with two non-vacuity witnesses) survived
  intact and axiom-clean.
* **Cycle 138 was REVERTED (score −2) solely** because sorry count rose
  0 → 1. Lesson: do **not** introduce sorry-first scaffolds. Every
  cycle 140 deliverable must compile axiom-clean.
* **Two Aristotle jobs from cycle 138 are still in flight**, both
  targeting `thm:550A`:
  * Job A — full general-`n`:
    project `7062c2a2-4a8b-4fae-b694-9355e06427a9`
    (last status check cycle 139: IN_PROGRESS, 4 %).
  * Job B — focused `n = 2`:
    project `70f26d67-b37e-4eda-b946-64c9f4616612`
    (last status check cycle 139: IN_PROGRESS, 3 %).
  By cycle 140 these jobs will have had ≈ 24 hours of compute, well
  past the textbook 30-minute window — a single poll this cycle is
  expected to find them either complete or genuinely stuck.

## Priority 0 — Aristotle poll (MANDATORY, do first)

Run **one** `mcp__aristotle__get_status` call on each of the two
project IDs above (in parallel, single message). Per CLAUDE.md, do
NOT re-poll. Branch on the result:

* **Both COMPLETE with clean proofs** → Priority 1A (full reinstatement).
* **Job A (general-n) COMPLETE** → Priority 1A.
* **Only Job B (n=2) COMPLETE** → Priority 1B (n=2 reinstatement
  via Aristotle's proof).
* **Both still IN_PROGRESS or returned junk** → fall through to
  Priority 2.
* **Both FAILED outright** → cancel both via
  `mcp__aristotle__cancel_project` to free the slots, then go to
  Priority 2.

After polling, write a short note in the cycle 140 task results
recording the status outcomes (so future cycles know whether the
jobs are stale).

## Priority 1A — reinstate `thm:550A` general-n if Aristotle delivered

If Aristotle Job A returned a clean general-`n` proof:

1. **Extract** the proof body via `mcp__aristotle__extract_result`
   (project `7062c2a2-4a8b-4fae-b694-9355e06427a9`). Read the
   extracted file and identify the proof of
   `doublyCompanionMatrix_det_factorization`.
2. **Reinstate the statement** in
   `OpenMath/Chapter5/Section550.lean` directly after
   `doublyCompanionMatrix_det_factorization_n_one`. The statement
   shape (matching cycle-138 scaffold):
   ```
   theorem doublyCompanionMatrix_det_factorization
       {n : ℕ} (α β : Fin n → ℂ) :
       Asymptotics.IsBigO (nhds (0 : ℂ))
         (fun z : ℂ =>
           (1 - z • doublyCompanionMatrix α β).det
             - alphaPoly α z * betaPoly β z)
         (fun z : ℂ => z ^ (n + 1))
   ```
3. **Inline Aristotle's proof body verbatim**, then
   `lake env lean OpenMath/Chapter5/Section550.lean` to verify it
   compiles. If it fails, attempt at most ONE round of mechanical
   adaptation (e.g. import additions, simp-set tweaks) — do **not**
   spend the cycle rewriting a returned proof. If adaptation fails,
   abandon the inlining and fall through to Priority 2.
4. **Axiom check** via `lean_verify` on the fully qualified name. If
   it returns anything beyond `[propext, Classical.choice, Quot.sound]`,
   abort the inlining and fall through to Priority 2 — Butcher's §550
   theorem is one of the load-bearing characterisations and must be
   axiom-clean.
5. **Update bookkeeping**:
   * `extraction/formalization_data/lean_status.json` — flip
     `thm:550A` to `formalized`, cycle 140, lean_symbol pointing at
     the new theorem.
   * `plan.md` — flip the `thm:550A` row to `[x]`.
   * `.prover-state/issues/thm_550A_general_n.md` — prepend a "Status
     update (cycle 140) — RESOLVED" stanza.

## Priority 1B — reinstate `thm:550A` n=2 only if only Job B delivered

If only Job B returned a clean n=2 proof:

1. Extract via `mcp__aristotle__extract_result` on project
   `70f26d67-b37e-4eda-b946-64c9f4616612`.
2. Add a new theorem `doublyCompanionMatrix_det_factorization_n_two`
   parallel in shape to the existing `_n_one`, with
   `Fin 2 → ℂ` arguments and conclusion bounding by `z ^ 3`.
3. Same axiom check as Priority 1A. Update `lean_status.json` to add
   the new lean_symbol as a sub-witness (do NOT promote `thm:550A` to
   `formalized` — the general-`n` statement is still missing).
4. Then continue to Priority 2 if there is cycle budget remaining
   (n=2 alone is light; ~30 min of work).

## Priority 2 — Manual `n = 2` closure (DEFAULT path if Aristotle did not deliver)

This is the **default path** for cycle 140 if Aristotle is still in
flight. The n=2 case is mechanical (`Matrix.det_fin_two` plus ring
arithmetic, paralleling cycle 138's n=1 closure) and provides a
substantive stepping stone toward general-`n` while remaining
axiom-clean.

### Concrete construction

Add the following theorem to `OpenMath/Chapter5/Section550.lean`
immediately after `doublyCompanionMatrix_det_factorization_n_one`:

```
theorem doublyCompanionMatrix_det_factorization_n_two
    (α β : Fin 2 → ℂ) :
    Asymptotics.IsBigO (nhds (0 : ℂ))
      (fun z : ℂ =>
        (1 - z • doublyCompanionMatrix α β).det
          - alphaPoly α z * betaPoly β z)
      (fun z : ℂ => z ^ 3)
```

### Algebraic skeleton (verified by hand against the existing definition)

For `n = 2`, the doubly companion matrix unfolds to
```
X = !![-α 0, -α 1 - β 1;
       1,     -β 0]
```
(row 0 col 0: `i.val = 0`, `j.val + 1 = 1 ≠ 2`, so `-α 0`; row 0
col 1: `i.val = 0`, `j.val + 1 = 2 = n`, so `-α (n-1) - β (n-1) =
-α 1 - β 1`; row 1 col 0: `i.val ≠ 0`, `j.val + 1 = 1 ≠ 2`,
`i.val = j.val + 1 = 1`, so `1`; row 1 col 1: `i.val ≠ 0`,
`j.val + 1 = 2 = n`, so `-β (n - i.val - 1) = -β 0`.)

Hence
```
I - zX = !![1 + zα 0,   z(α 1 + β 1);
            -z,          1 + zβ 0]
```
and `Matrix.det_fin_two` gives
```
det(I - zX) = (1 + zα 0)(1 + zβ 0) - z(α 1 + β 1)·(-z)
            = (1 + zα 0)(1 + zβ 0) + z²(α 1 + β 1)
            = 1 + (α 0 + β 0) z
                + (α 0 · β 0 + α 1 + β 1) z².
```
Meanwhile,
```
α(z) · β(z) = (1 + α 0 z + α 1 z²)(1 + β 0 z + β 1 z²)
            = 1 + (α 0 + β 0) z
                + (α 0 · β 0 + α 1 + β 1) z²
                + (α 0 · β 1 + α 1 · β 0) z³
                + α 1 · β 1 · z⁴.
```
The residue is therefore
```
det - α·β = -(α 0 · β 1 + α 1 · β 0) z³ - α 1 · β 1 · z⁴
          = z³ · (-(α 0 · β 1 + α 1 · β 0) - α 1 · β 1 · z),
```
which is `O(z³) = O(z^{2+1})` near 0.

### Tactic plan (mirror of `_n_one`)

**Step 1a** — add a private simp lemma paralleling the existing
`doublyCompanionMatrix_one_eq`:
```
@[simp]
private lemma doublyCompanionMatrix_two_eq (α β : Fin 2 → ℂ) :
    doublyCompanionMatrix α β
      = !![-α 0, -α 1 - β 1;
           1,    -β 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [doublyCompanionMatrix]
```
If `simp [doublyCompanionMatrix]` doesn't fully close one of the
four entries, fall back to per-case `if_pos`/`if_neg` rewrites with
explicit `decide`/`Fin.val_zero`/`Fin.val_succ` evidence.

**Step 1** — establish the closed-form residue:
```
have h_diff : (fun z : ℂ =>
    (1 - z • doublyCompanionMatrix α β).det
      - alphaPoly α z * betaPoly β z)
    = (fun z : ℂ =>
        z^3 * (-(α 0 * β 1 + α 1 * β 0) - α 1 * β 1 * z)) := by
  funext z
  rw [doublyCompanionMatrix_two_eq]
  -- Reduce 1 - z • !![…] to a !![…] form.
  have hmat :
      (1 - z • !![-α 0, -α 1 - β 1; 1, -β 0]
         : Matrix (Fin 2) (Fin 2) ℂ)
        = !![1 + z * α 0, z * (α 1 + β 1);
             -z,            1 + z * β 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  rw [hmat, Matrix.det_fin_two]
  simp [alphaPoly, betaPoly, Fin.sum_univ_succ, Fin.sum_univ_zero]
  ring
rw [h_diff]
```

**Step 2** — bridge `z³ · (linear in z)` to `O(z³)`. The cleanest
formulation:
```
-- Goal: IsBigO (𝓝 0)
--   (fun z => z^3 * (-(α 0 * β 1 + α 1 * β 0) - α 1 * β 1 * z))
--   (fun z => z^3)
refine (Asymptotics.isBigO_refl (fun z : ℂ => z^3) _).mul_isBigO ?_
-- Now: IsBigO (𝓝 0)
--   (fun z => -(α 0*β 1 + α 1*β 0) - α 1*β 1*z)  (fun _ => 1)
exact (Asymptotics.isBigO_const_const _ one_ne_zero _).add
        ((Asymptotics.isBigO_id (𝓝 0)).const_mul_left _ |>.trans
         (Asymptotics.isBigO_const_const _ one_ne_zero _))
```
(If the `mul_isBigO` lemma name doesn't match Mathlib's, search via
`lean_local_search "IsBigO" "mul"` or `lean_loogle "IsBigO _ _"`.
The fallback is `Asymptotics.IsBigO.mul (isBigO_refl …) (h : IsBigO …)`.)

**Step 2 fallback (preferred if Step 2 above is fiddly)** — split
the residue additively as
```
(fun z => z^3 * c0) + (fun z => z^4 * c1)
```
where `c0 := -(α 0 · β 1 + α 1 · β 0)` and `c1 := -(α 1 · β 1)`,
then prove each summand is `O(z^3)` separately:
* `z^3 * c0`: via `(isBigO_refl _ _).const_mul_left c0`.
* `z^4 * c1 = z^3 * (z * c1)`: via `(isBigO_refl _ _).mul_isBigO`
  with the inner `z * c1` being `O(1)` near `0`
  (`(isBigO_id (𝓝 0)).const_mul_left c1` is `O(z) ⊆ O(1)` since
  `z → 0` ⇒ `z` is bounded near `0` ⇒ `z^4 = O(z^3)` because
  `z^4 = z^3 · z` with `z` bounded).

If both Step 2 routes fight the type system for > 30 minutes, fall
through to Priority 3 B1.

### Verification protocol

* `lake env lean OpenMath/Chapter5/Section550.lean` — must succeed
  without any sorry.
* `lean_verify OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization_n_two`
  — must return `[propext, Classical.choice, Quot.sound]`.
* `lake build OpenMath.Chapter5` — must remain green (~2790 jobs).

### Bookkeeping if Priority 2 succeeds

* `extraction/formalization_data/lean_status.json` — keep `thm:550A`
  as `partial`, but extend the `notes` field to mention the n=2
  lean_symbol alongside the existing `_n_one`.
* `plan.md` `thm:550A` row — extend the cycle-139 note to mention
  the new n=2 stepping stone.
* `.prover-state/issues/thm_550A_general_n.md` — prepend a "Cycle
  140 update" stanza recording the n=2 closure as additional
  evidence the formula is correct, and noting that general-`n`
  remains open.

### Time budget

* Aristotle poll + decision branching: 5 minutes.
* Manual n=2 closure: 60–75 minutes (mostly unfold + ring + IsBigO
  plumbing).
* Bookkeeping + axiom checks: 15 minutes.
* Total: ≈ 90 minutes, well within a single cycle.

## Priority 3 — Backup plans if Priority 2 stalls

The `IsBigO`-of-polynomial reasoning at Step 2 of Priority 2 is the
most likely sticking point. Two escape hatches, in order of
preference:

### B1 (preferred) — drop to a pointwise residue identity

If Step 2 won't compile within ~30 minutes of attempts, simplify the
target to a **pointwise polynomial-equality witness**, not an
asymptotic statement. Replace the n=2 theorem with:

```
theorem doublyCompanionMatrix_det_residue_n_two
    (α β : Fin 2 → ℂ) (z : ℂ) :
    (1 - z • doublyCompanionMatrix α β).det
        - alphaPoly α z * betaPoly β z
      = z^3 * (-(α 0 * β 1 + α 1 * β 0) - α 1 * β 1 * z)
```

This is just Priority-2 Step 1's `h_diff` exposed as a public theorem.
It still provides a substantive n=2 witness (the closed-form residue
identity is the load-bearing piece for any `IsBigO` upgrade) and is
purely algebraic, so it lands axiom-clean by `simp + ring` without
needing the asymptotic plumbing. The `IsBigO` upgrade can come in a
later cycle.

Bookkeeping: same as Priority 2, but lean_symbol points at
`_residue_n_two` instead of `_factorization_n_two`.

### B2 — pivot to a substantive non-trivial §530 starting-method witness

If Priority 2 is genuinely blocked (e.g. `Matrix.det_fin_two` does
not unfold cleanly against the `if-then-else`-laden
`doublyCompanionMatrix` definition, or the `!![…]` notation refuses
to elaborate at `Fin 2 × Fin 2` over `ℂ`), pivot away from §550 and
enrich §530.

Add to `OpenMath/Chapter5/Section530.lean`:

* A **2-stage trivial generalized RK** `twoStageGeneralizedRK : GeneralizedRungeKuttaMethod 2`
  with `c = ![0, 1/2]`, `A = !![0, 0; 1/2, 0]`, `b₀ = 1`,
  `b = ![0, 1]` (an explicit-midpoint-style 2-stage tableau).
* A **mixed-stages starting method** `mixedStartingMethod : StartingMethod 2`
  with `stages 0 = 1, stages 1 = 2`, `method 0 := trivialGeneralizedRK`,
  `method 1 := twoStageGeneralizedRK`. This demonstrates the
  heterogeneous-`s_i` capability is non-vacuous (currently only
  the constant `stages = fun _ => 1` case is witnessed).
* `mixedStartingMethod_isNonDegenerate` — exhibits the `i = 0`
  constituent's `b₀ = 1 ≠ 0` via the same
  `isNonDegenerate_iff_exists_b₀_ne_zero` route.

This delivers **two new structures + one axiom-clean theorem** that
genuinely exercise the dependent-stages design. Strictly substantive
(not just renaming the trivial witness).

Bookkeeping: leave `lean_status.json` `def:530A` row at cycle 139
(no status change needed; this is just a richer non-vacuity story).
Mention the new mixed-stages witness in the `def:530A` `notes` field.

## What NOT to do this cycle

* **Do NOT introduce a sorry-first scaffold for `thm:550A`
  general-`n`.** Cycle 138's −2 score is the canonical example. If
  Aristotle hasn't returned, the n=2 manual closure is the path; do
  not stage a general-`n` statement with `sorry` body.
* **Do NOT poll Aristotle more than once.** Per CLAUDE.md. One
  status check per project at the start of the cycle, no follow-ups.
* **Do NOT submit a fresh Aristotle job for general-n while Job A
  is still IN_PROGRESS.** Duplicates spend.
* **Do NOT attempt the manual cofactor-expansion / induction proof
  for general-`n`.** Per `thm_550A_general_n.md` and cycle-139 task
  results, this is multi-cycle infrastructure (~150–300 LOC across
  2–3 cycles). It is explicitly out of scope for cycle 140.
* **Do NOT raise `maxHeartbeats`.** CLAUDE.md hard rule.
* **Do NOT cherry-pick a cosmetic Chapter 3 leaf** (e.g.
  `def:381F` / `def:381B` / `def:381D`) as a substitute for
  Priority 2/3. `def:381F` is **blocked** by the deferred
  `reducedMethod` construction (see
  `.prover-state/issues/reduced_method_deferred.md`); the others are
  pure renaming exercises that don't justify a cycle.
* **Do NOT open `def:530B` / `def:530C` ("order relative to a
  starting method").** These genuinely require Taylor-expansion
  infrastructure for the `SM` and `ES` composition (see cycle 139
  task results §"Suggested next approach"); they are multi-cycle and
  high-risk for a single-cycle deliverable.
* **Do NOT touch `scripts/autonomous_loop.py`** or any harness file.
  Per CLAUDE.md and `tautology_scanner_false_positives.md` (loop-
  maintainer territory).
* **Do NOT modify `extraction/raw_text/` or
  `extraction/formalization_data/entities/`.** Both are
  regenerated; updates go to `extraction/extensions/` (none
  needed this cycle) or `lean_status.json`.

## Pre-commit checklist (mandatory)

Before `git add` / `git commit`, verify:

1. **Sorry count**:
   `Grep '\bsorry\b' OpenMath/ --output_mode count` — confirm zero
   matches in proof bodies (docstring/comment matches OK; verify
   manually).
2. **Axiom-clean**: every new public theorem returns
   `[propext, Classical.choice, Quot.sound]` from `lean_verify`.
3. **Build**: `lake build OpenMath.Chapter5` exits with all jobs
   green (expected ~2790 jobs after this cycle's additions).
4. **`lean_status.json`**: rows for `thm:550A` (and `def:530A` if
   touched under B2) carry the cycle 140 reference and a clear
   lean_symbol pointer.
5. **Faithfulness check** in `cycle_140.md` covers every new `def`,
   `structure`, and `theorem` introduced this cycle — quote the
   textbook entity, confirm the Lean statement matches (or document
   any deviation explicitly).
6. **`plan.md`** reflects any status changes.
7. **Tautology scanner sanity**: no `:= h_<name>` or `exact h_<name>`
   patterns introduced (rename to `hname` form if necessary, per
   `.prover-state/issues/tautology_scanner_false_positives.md`).

## Decision tree summary

```
Cycle 140 entry
  │
  ├─ Poll Aristotle Jobs A (general-n) and B (n=2)  ← MANDATORY
  │
  ├─ Job A returned clean? ──→ Priority 1A: reinstate general-n
  │     │                       (full closure of thm:550A)
  │     └─ axiom check fails? ─→ fall through to Priority 2
  │
  ├─ Only Job B returned clean? ──→ Priority 1B: add n=2 from
  │     │                            Aristotle, then continue to
  │     │                            Priority 2 if budget permits
  │     └─ axiom check fails? ─→ fall through to Priority 2
  │
  ├─ Neither returned (default expected outcome) ─→ Priority 2:
  │     │                           manual n=2 closure
  │     └─ Step 2 IsBigO plumbing stalls ─→ Priority 3 B1 (residue
  │                                          identity) or B2 (§530
  │                                          mixed-stages witness)
  │
  └─ Both FAILED outright ──→ cancel both, then Priority 2
```

## Expected deliverable

A single commit with one of:

* **(Best case)** `thm:550A` reinstated at general `n`, axiom-clean,
  flipped to `formalized` in `lean_status.json` and `plan.md`.
* **(Default expected)** New axiom-clean theorem
  `doublyCompanionMatrix_det_factorization_n_two` adding a 2x2
  witness for §550, plus the helper simp lemma
  `doublyCompanionMatrix_two_eq`. `thm:550A` remains `partial` with
  two stepping stones (n=1 and n=2).
* **(Backup)** Either the pointwise residue identity B1
  (`doublyCompanionMatrix_det_residue_n_two`) or the §530
  enrichment B2 (mixed-stages starting method), depending on which
  Step-2 obstruction bites.

Whatever the deliverable, sorry count must remain 0 and all new
public theorems must verify axiom-clean.
