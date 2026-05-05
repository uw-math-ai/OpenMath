# Cycle 130 strategy

## Status snapshot

* No pending Aristotle results; no in-flight jobs.
* No sorries on the branch (verified via `## Sorry locations` in the
  prompt).
* Cycle 129 closure landed at `5eb5ae0` — `def:525A` is now witnessed
  axiom-clean by *both* `explicitEulerGLM` (trivial G=D=0 witness) and
  `implicitMidpointGLM` (substantive G=D=1 witness).
* Progress: 66 / 175 entities formalized.

## Target

**Primary**: `def:542A` — *Runge–Kutta stability* of a general linear
method (Butcher §542, page 445).

**Secondary** (do this *after* primary lands and only if budget
permits): two mirror lemmas
`implicitMidpointGLM_isStable` and
`implicitMidpointGLM_isConsistent` in
`OpenMath/Chapter5/Section510.lean`. Cycle 129 task results
flagged these as "one-line proofs" mirroring the existing
`explicitEulerGLM_*` pair — the `V` blocks coincide so the proofs
will copy verbatim modulo the structure name.

These are explicitly *secondary*. If primary takes longer than
expected, ship primary alone — do NOT bundle.

## Why `def:542A` is the right pick

* It is a leaf definition (no proof obligations beyond non-vacuity).
* All the infrastructure it needs is already in
  `OpenMath/Chapter5/Section520.lean`:
  * `GeneralLinearMethod.stabilityMatrix` (line 96).
  * `GeneralLinearMethod.stabilityFunction` (line 150,
    `(w • 1 − M(z)).det` = `Φ(w,z)`).
  * `explicitEulerGLM_stabilityFunction` (line 461) gives
    `Φ(w,z) = w − 1 − z` — this *is* the witness equation modulo a
    rearrangement.
* It unblocks two downstream entities directly: `def:551A`
  ("Inherent Runge–Kutta stability") and the §550–§553 cluster's
  hooks into RK-stability.
* The textbook example `r = 1` (which both `explicitEulerGLM` and
  `implicitMidpointGLM` satisfy) gives a clean, unconditional
  non-vacuity witness without any 2×2 Mathlib gymnastics.

## Textbook statement (verbatim from `entities/def_542A.json`)

> A general linear method `(A, U, B, V)` has 'Runge–Kutta stability'
> if the characteristic polynomial given by (542a) has the form
>
>     `Φ(w, z) = w^(r−1) (w − R(z))`.
>
> For a method with Runge–Kutta stability, the rational function
> `R(z)` is known as the 'stability function' of the method.

`Φ(w, z) := det(wI − M(z))` per (542a). Our existing
`GeneralLinearMethod.stabilityFunction` is *exactly* this `Φ`
(verified by `stabilityFunction_eq_zero_iff_mem_spectrum` at
Section520.lean:528, which uses `Matrix.eval_charpoly`).

## Encoding choices

Add to `OpenMath/Chapter5/Section520.lean` (extending the existing
`OpenMath.Chapter5.Section510` namespace where `stabilityFunction`
lives — *not* a new file; this keeps the §520/§542 stability cluster
together in one place):

```lean
/-- §542A: a general linear method `M : GeneralLinearMethod s r`
has *Runge–Kutta stability* if its stability function `Φ(w, z)`
factorises as `w^(r−1) · (w − R z)` for some scalar function
`R : ℂ → ℂ`. Such an `R` is then called the *stability function*
of `M` (a rational function in the textbook). -/
def GeneralLinearMethod.IsRKStable {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  ∃ R : ℂ → ℂ, ∀ w z : ℂ,
    M.stabilityFunction w z = w ^ (r - 1) * (w - R z)
```

Notes:

* `r - 1` is natural-number subtraction. For `r = 0`, `r - 1 = 0`
  and the equation collapses to `Φ(w,z) = w − R(z)` — but `r = 0`
  means `Φ(w, z) = det (w • 1 − M(z))` over the empty matrix, which
  is `1`, so `1 = w − R z` is solvable only by an `R` *depending on
  `w`* — i.e. NOT solvable as a function of `z` alone (for the
  fixed `R z`, varying `w` would give `1 = w₁ − R z = w₂ − R z`
  forcing `w₁ = w₂`, contradiction). The `r = 0` branch is therefore
  never RK-stable, which is the right behaviour.
* For `r ≥ 1`, `r − 1` is the textbook `r − 1`.
* Use `R : ℂ → ℂ` (not `RatFunc ℂ`) — the textbook calls `R` rational
  but the *predicate* statement only needs a function. If a
  downstream theorem (e.g. §550A/B) requires rationality, it can be
  added then. Do NOT pre-emptively bring in `RatFunc`.

## Witness statement

```lean
/-- §542 non-vacuity: explicit Euler GLM has Runge–Kutta
stability with `R(z) = 1 + z`. -/
theorem explicitEulerGLM_isRKStable :
    explicitEulerGLM.IsRKStable := by
  refine ⟨fun z => 1 + z, ?_⟩
  intro w z
  rw [explicitEulerGLM_stabilityFunction]
  -- Goal: w - 1 - z = w ^ (1 - 1) * (w - (1 + z))
  -- Simplify: 1 - 1 = 0, w^0 = 1, then `ring`.
  simp [pow_zero]
  ring
```

A second witness on `implicitMidpointGLM` is **out of scope** for
this cycle. Reason: it requires computing
`implicitMidpointGLM.stabilityFunction w z` from scratch, which
involves `(I - z·!![1/2])⁻¹` over `ℂ`. That's clean math but ~50
LOC of matrix-inverse plumbing, and we already have the `r=1` slot
filled by explicit Euler. Defer to a later cycle if/when needed.

## Step-by-step recipe (worker action items)

1. **Read first** (~3 min):
   * `extraction/formalization_data/entities/def_542A.json` (statement
     + context).
   * `OpenMath/Chapter5/Section520.lean` lines 96–200 (look at how
     `stabilityFunction` is defined and how
     `explicitEulerGLM_stabilityFunction` is proved at line 461).
   * `OpenMath/Chapter5/Section510.lean` lines 144–195 (witness
     pattern for `explicitEulerGLM_isPreconsistent` /
     `_isStable` / `_isConsistent`).

2. **Decide insertion point**: append `IsRKStable` and
   `explicitEulerGLM_isRKStable` to `OpenMath/Chapter5/Section520.lean`
   inside `namespace OpenMath.Chapter5.Section510`, after
   `explicitEulerGLM_hasStabilityOrder_one` (around line ~500). Do
   NOT make a new file.

3. **Encode the predicate** as shown in §"Encoding choices" above.

4. **Encode the witness** as shown in §"Witness statement" above.
   Verify with `lake env lean OpenMath/Chapter5/Section520.lean`.
   Expected wall time: ≤ 90s. The `simp [pow_zero]; ring` closer
   may need adjustment — if `r - 1 = 0` doesn't reduce by `simp`
   alone, try the fallback ladder in §"Backup plan" below.

5. **Axiom-clean check**:
   ```
   #print axioms explicitEulerGLM_isRKStable
   ```
   Expected: `[propext, Classical.choice, Quot.sound]`. If `sorryAx`
   appears, the `simp; ring` closer is incomplete. (Note: per
   prior cycle's discovery, `lake env lean <file>` does NOT update
   the `.olean` cache — run `lake build OpenMath.Chapter5.Section520`
   before `#print axioms` to avoid stale-cache `sorryAx` false
   positives.)

6. **Update `extraction/formalization_data/lean_status.json`**:
   set `def:542A` row to `formalized`, with `lean_file` =
   `OpenMath/Chapter5/Section520.lean` and `lean_symbol` =
   `OpenMath.Chapter5.Section510.GeneralLinearMethod.IsRKStable`,
   matching the cycle-128 schema for `def:525A` (look at the row
   for that entity if unsure of the JSON shape).

7. **Update `plan.md`** Chapter 5 §54 row for `def:542A` from
   `[ ]` to `[x]` with a brief annotation
   `OpenMath/Chapter5/Section520.lean (cycle 130, axiom-clean)` and
   bump the progress counter from 66 to 67.

8. **Faithfulness checklist** (mandatory per CLAUDE.md):
   * Quote textbook statement in `cycle_130.md` task results.
   * Confirm `IsRKStable` captures `Φ(w,z) = w^{r-1}(w − R(z))`
     verbatim (it does — direct transcription).
   * Definition smuggling check: we are NOT defining RK stability
     as the existence of an `R` extracted from `Φ` (which would be
     vacuous); we are defining it as the *factorisation existing*,
     which has real algebraic content (vacuous for `r = 0`,
     non-trivial for `r ≥ 1`). ✓
   * Tautology check on the witness: the conclusion `IsRKStable` is
     existential over `R`; the witness `R z := 1 + z` is computed,
     not extracted from a hypothesis. ✓

9. **(SECONDARY, only if 8 finishes within ~60 min wall)**:
   add `implicitMidpointGLM_isStable` and
   `implicitMidpointGLM_isConsistent` to `Section510.lean`
   immediately after `implicitMidpointGLM_isPreconsistent` (line
   ~228). Both proofs should copy `explicitEulerGLM_isStable`
   (line 167) and `explicitEulerGLM_isConsistent` (line 184)
   verbatim modulo the GLM structure name — the `V` and `U`
   matrices are identical (`!![1]`) so the proofs go through. If
   either deviates by more than 2 lines from the explicit Euler
   version, STOP — there's an unexpected dependency on `A` and you
   should ship just the primary.

10. **Write `cycle_130.md`** per the CLAUDE.md template, including
    the faithfulness check from step 8 and a list of any deviations
    in step 9. Commit with message
    `Cycle 130 — formalize def:542A Runge–Kutta stability (axiom-clean)`
    plus a one-line note about the secondary deliverables if they
    landed.

11. **Push**.

## What NOT to try (explicitly rejected approaches)

* **Do NOT** start §550 doubly-companion-matrix infrastructure this
  cycle (`thm:550A`, `thm:550B`, `cor:550C`). It is multi-cycle work
  per the cycle 129 worker's notes and would not produce a
  committable single-cycle deliverable.
* **Do NOT** attempt the Butcher (525d) 2×2 G-symplectic witness
  this cycle. Cycle 129 explicitly recategorised it as "additional
  polish" rather than load-bearing now that the implicit-midpoint
  witness lands; it is no longer time-critical and would consume the
  cycle's budget without advancing the entity count.
* **Do NOT** attempt `thm:521B` ("Maximum stability order for given
  steps") this cycle. Its textbook proof uses contour integrals,
  partial fractions, and rational-function complexity arguments —
  multi-cycle work requiring infrastructure we don't have.
* **Do NOT** attempt `def:530A` ("non-degenerate") this cycle. It
  depends on a notion of "starting method" (a sequence of generalized
  Runge–Kutta methods) that is not yet formalized; the dependency
  list in its JSON is empty only because the extractor missed the
  upstream "starting method" structure.
* **Do NOT** introduce `RatFunc ℂ` for `R(z)`. Plain `ℂ → ℂ` is
  sufficient for the predicate; the textbook's "rational" adjective
  is informational, not structural for this definition.
* **Do NOT** add an `(r_pos : 0 < r)` hypothesis to `IsRKStable`.
  The `r = 0` case being unsatisfiable is the correct behaviour
  (matches the textbook's implicit `r ≥ 1`).
* **Do NOT** make `explicitEulerGLM_isRKStable` use
  `decide` or `omega` — it's a real algebraic identity over `ℂ`,
  the closer must be `ring` (post-simplification of `w^0`).
* **Do NOT** create `OpenMath/Chapter5/Section542.lean` for this
  one definition. Section520 already contains `IsAStable`,
  `IsLStable`, `HasStabilityOrder`, and the §520D
  instability-region work — it is the established home for stability
  predicates. A new file would fragment the cluster.
* **Do NOT** poll Aristotle this cycle (no jobs are in flight, and
  this work is not Aristotle-suitable — predicate definition +
  10-line `simp; ring` closer).
* **Do NOT** edit `scripts/autonomous_loop.py` (loop-maintainer
  territory; see standing
  `tautology_scanner_false_positives.md`).
* **Do NOT** raise `maxHeartbeats`.

## Backup plan if the primary stalls

Most likely failure mode: `simp [pow_zero]; ring` doesn't close the
witness because `r - 1` for `r = 1` doesn't reduce automatically.

Fallback ladder, in order of preference:

1. Spell out `(1 : ℕ) - 1 = 0` explicitly:
   ```lean
   have hr : (1 : ℕ) - 1 = 0 := rfl
   rw [hr, pow_zero, one_mul]
   ring
   ```
2. Use `Nat.sub_self` if `rfl` doesn't fire.
3. Use `show w - 1 - z = w ^ 0 * (w - (1 + z)); rw [pow_zero,
   one_mul]; ring`.
4. If all of the above fail (would be surprising), the closer is
   `convert ?_ using 2` followed by manual rewrite — but this is
   strong evidence of a mis-statement. Re-check the predicate
   shape against the textbook before spending > 15 min on the
   closer.

If after 30 min the witness still doesn't close, STOP and write
the issue file
`.prover-state/issues/def_542A_witness_blocker.md` with the goal
state and a diagnosis. A failed witness on the textbook's
canonical `r = 1` example is itself a meaningful cycle output.

## Score budget

* Primary alone (def:542A formalized + axiom-clean witness +
  lean_status + plan.md): score 2.
* Primary + secondary (implicitMidpointGLM_isStable +
  implicitMidpointGLM_isConsistent): score 2 (the secondary
  is upkeep, doesn't change the entity count).
* Primary stall but issue file written: score 1.
* No commit lands: score ≤ 0 (CLAUDE.md "zero-changes is
  unacceptable").
