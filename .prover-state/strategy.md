# Strategy — cycle 273

## A. Where we are

Cycle 272 shipped two axiom-clean §342 results in
`OpenMath/Chapter3/Section342.lean`:

* **(342e) Rodrigues' formula** `C(n!) * P_n^* = C((-1)^n) * D^n (X^n (1-X)^n)`
  via lift from Mathlib's ℤ[X] `factorial_mul_shiftedLegendre_eq`.
* **`butcherShiftedLegendre_natDegree`**: `natDegree = n`.

Plus three (342e) non-vacuity `example`s at `n ∈ {0, 1, 2}`. File now
246 LOC, 0 sorries, three Butcher properties closed (342b/c/e) +
degree. (342a)/(342d)/(342f)/(342g) remain unformalised.

There are **no pending Aristotle results**, **no current sorries**,
and **no stuck items**. The cycle 272 task results' suggested next
sequence: "(1) (342f) recurrence if tractable; otherwise (2) fire
Aristotle (342a) + (4) lem:310B Phase A.1 in parallel" (but Phase A.1
is already shipped per `lem_310B_plan.md` cycle 261 closure — the
suggestion is stale).

## B. Decision

**Two parallel tracks.** Fire-and-forget Aristotle on (342a) at
cycle start, then manually attempt (342f) three-term recurrence
with a clear fallback.

### Track 1 — Fire-and-forget Aristotle on (342a) orthogonality

Submit at cycle start; do NOT poll this cycle (CLAUDE.md rule, single
poll discipline applies to the *next* cycle). The (342a) submission
benefits enormously from cycle 272's (342e) Rodrigues now being
available as a citable hypothesis. Strategy template below in §C.1.

### Track 2 — Manual (342f) three-term recurrence

Butcher (342f):
```
n · P_n^*(x) = (2x - 1)(2n - 1) · P_{n-1}^*(x) - (n - 1) · P_{n-2}^*(x)
```

For our convention `butcherShiftedLegendre n = (-1)^n · (shiftedLegendre n).map (Int.castRingHom ℝ)`,
the polynomial-ring identity is:
```
C (n : ℝ) * butcherShiftedLegendre n
  = (C 2 * X - C 1) * C ((2*n - 1 : ℝ)) * butcherShiftedLegendre (n - 1)
    - C ((n - 1 : ℝ)) * butcherShiftedLegendre (n - 2)
```
for `n ≥ 2` (with the `(n-1)` and `(n-2)` arithmetic on ℕ requiring
`n ≥ 2`).

**Risk: MEDIUM**. Cycle 272 task results flagged this as ~150 LOC
with uncertain Mathlib hook availability. The strategy in §C.2 below
takes a definite route (coefficient-comparison via
`coeff_shiftedLegendre`) with an explicit fallback if the route
exceeds 60 minutes.

### Track 3 (fallback if Track 2 stalls) — small §342 corollaries

If (342f) doesn't close within the 60-minute budget, ship instead
two small but useful §342 helpers documented in §C.3 — corollaries
of cycle 271/272 work that are guaranteed to close in <30 min each.

## C. Recipes

### C.1 — Aristotle (342a) orthogonality submission

**Target statement**:
```lean
theorem butcherShiftedLegendre_orthogonal {m n : ℕ} (hmn : m ≠ n) :
    ∫ x in (0 : ℝ)..1,
      (butcherShiftedLegendre m).eval x *
      (butcherShiftedLegendre n).eval x = 0
```

**Submission file**: `.prover-state/aristotle_submissions/cycle_273/342a_orthogonality.lean`.

**Content**: include the *full Section342.lean header + imports +
butcherShiftedLegendre definition* (so Aristotle's environment is
self-contained), plus cycle 271/272's shipped theorems
(`butcherShiftedLegendre_eval_one`, `butcherShiftedLegendre_eval_one_sub`,
`butcherShiftedLegendre_rodrigues`, `butcherShiftedLegendre_natDegree`)
as **named hypotheses** that Aristotle can cite directly. Aristotle
sometimes fails to discover them from `import OpenMath.Chapter3.Section342`
alone.

**Prompt hint** (in the snippet docstring): "Use Rodrigues' formula
`butcherShiftedLegendre_rodrigues` plus integration by parts `n` times.
The boundary terms vanish because `D^k (X^n (1-X)^n)` has factors of
both `X^{n-k+...}` and `(1-X)^{n-k+...}` at every `k < n`, so they
all vanish at both endpoints `0` and `1`."

**Submit via** `mcp__aristotle__submit_file`. Capture the project ID
in `.prover-state/aristotle_submissions/cycle_273/README.md`.

**Do NOT poll this cycle.** Cycle 274's planner will check status.

### C.2 — Manual (342f) recurrence via coefficient comparison

**60-minute time-box.** If not closing by then, fall back to §C.3.

**Approach**: use `Polynomial.ext` (coefficient-by-coefficient) on
both sides over ℝ[X]. The key step is reducing to Mathlib's
`coeff_shiftedLegendre` (verified to exist at
`Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean:84-85`):

```
(shiftedLegendre n).coeff k = (-1)^k * n.choose k * (n + k).choose n
```

**Step 1**: state for `n ≥ 2` only (avoids `n - 1`, `n - 2` ℕ-subtraction
edge cases). Use the explicit `Nat.succ`-pattern:

```lean
theorem butcherShiftedLegendre_recurrence (n : ℕ) :
    (Polynomial.C ((n + 2 : ℕ) : ℝ)) * butcherShiftedLegendre (n + 2)
      = (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * (Polynomial.C ((2 * (n + 2) - 1 : ℕ) : ℝ))
        * butcherShiftedLegendre (n + 1)
      - (Polynomial.C ((n + 1 : ℕ) : ℝ)) * butcherShiftedLegendre n
```

**Step 2** (the load-bearing tactic): unfold
`butcherShiftedLegendre`, apply `Polynomial.ext` over ℝ[X], and
push the coefficient computation through `Polynomial.map`:

```lean
apply Polynomial.ext
intro k
unfold butcherShiftedLegendre
simp only [Polynomial.coeff_mul, Polynomial.coeff_sub,
           Polynomial.coeff_mul_C, Polynomial.coeff_C_mul,
           Polynomial.coeff_X_mul, Polynomial.coeff_C,
           Polynomial.coeff_map, Polynomial.coeff_X,
           Polynomial.coeff_one, Polynomial.coeff_sub]
-- now both sides reduce to expressions involving
-- `((-1)^k * n.choose k * (n + k).choose n : ℤ) : ℝ`-style terms.
```

**Step 3**: simplify with `coeff_shiftedLegendre` (search Mathlib
for its current statement first via `lean_local_search`) and
close with `push_cast; ring` over ℝ.

If `ring` doesn't fire because the binomial identity isn't
algebraically obvious, fall back to:

```lean
-- Alternative closure: Polynomial.funext (eval-pointwise)
-- This requires hf_inj for Polynomial → ℝ-function injectivity
-- on infinite fields, which holds for ℝ via `Polynomial.funext`
-- in Mathlib (verify at HEAD; check `lean_loogle "Polynomial.funext"`)
apply Polynomial.funext
intro x
unfold butcherShiftedLegendre
simp [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_map]
-- evaluate both sides at a real x; recurrence becomes
-- a real-arithmetic identity in `shiftedLegendre` evaluations
-- + binomial coefficients. The `ring` here will need to consume
-- Pascal-style identities — likely needs further unfolding.
```

The `Polynomial.funext` route may be cleaner because it sidesteps
binomial-coefficient comparison entirely, reducing to a real-valued
polynomial identity that `ring` handles.

**Step 4**: ship non-vacuity witnesses:
* `butcherShiftedLegendre_recurrence_n_zero`: instantiate at `n = 0`
  giving the explicit `2·P_2^* = (2X-1)·3·P_1^* - 1·P_0^*` identity.
* `butcherShiftedLegendre_recurrence_n_one`: at `n = 1`.

**Step 5**: update plan/lean_status.

**Mathlib hooks already verified at HEAD**:
* `Polynomial.coeff_shiftedLegendre` (line 84,
  `ShiftedLegendre.lean`).
* `Polynomial.shiftedLegendre_eval_symm` (line 110).
* `Polynomial.degree_shiftedLegendre`, `natDegree_shiftedLegendre`
  (lines 91, 99) — `@[simp]`.
* `Polynomial.factorial_mul_shiftedLegendre_eq` (line 46) — already
  consumed by cycle 272.
* `Polynomial.neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq`
  (line 102).

**Mathlib hooks to verify before relying on**:
* `Polynomial.funext` for ℝ[X] (presumably present; `lean_loogle`).
* `Polynomial.coeff_X_mul`, `Polynomial.coeff_C_mul` semantics
  (need to confirm with `lean_hover_info`).

### C.3 — Fallback small helpers (only if §C.2 stalls)

Three small axiom-clean §342 deliverables (~15-30 LOC total),
each guaranteed to close in <30 min:

**Helper 1** — `butcherShiftedLegendre_eval_zero`:
```lean
theorem butcherShiftedLegendre_eval_zero (n : ℕ) :
    (butcherShiftedLegendre n).eval 0 = (-1 : ℝ) ^ n := by
  have h := butcherShiftedLegendre_eval_one_sub n 1
  rw [show (1 - 1 : ℝ) = 0 by ring,
      butcherShiftedLegendre_eval_one] at h
  linarith [h]
```

**Helper 2** — `butcherShiftedLegendre_zero`:
```lean
theorem butcherShiftedLegendre_zero :
    butcherShiftedLegendre 0 = Polynomial.C 1 := by
  unfold butcherShiftedLegendre
  -- shiftedLegendre 0 = 1 over ℤ[X]; map and (-1)^0 = 1 collapse
  simp [Polynomial.shiftedLegendre, Polynomial.map_one]
```
(Verify `Polynomial.shiftedLegendre` at `n = 0` reduces to `1` first
via `lean_multi_attempt`; if not, use `coeff_shiftedLegendre` to
prove coefficient-by-coefficient.)

**Helper 3** — `butcherShiftedLegendre_one`:
```lean
theorem butcherShiftedLegendre_one :
    butcherShiftedLegendre 1 = Polynomial.C 2 * Polynomial.X - Polynomial.C 1
```
Prove via `Polynomial.ext` + `coeff_shiftedLegendre` at `n = 1`,
each `k ∈ {0, 1}`.

Ship all three with three small `example` non-vacuity witnesses
(e.g. `butcherShiftedLegendre_eval_zero 2 = 1`,
`butcherShiftedLegendre_eval_zero 3 = -1`).

## D. What NOT to try

* **Do NOT attempt (342a) orthogonality manually.** It needs
  integration by parts on Rodrigues' formula, vanishing boundary
  terms via `D^k (X^n (1-X)^n)`-product-rule analysis, and
  `MeasureTheory.IntegrationByParts` plumbing. This is multi-cycle
  work — let Aristotle take a swing first.

* **Do NOT attempt (342d) `∫₀¹ P_n^*² = 1/(2n+1)` or
  (342g) n distinct real zeros in (0,1).** Both depend on (342a)
  orthogonality. Blocked until Track 1 returns.

* **Do NOT raise `maxHeartbeats` above 200000.** If `ring` or `simp`
  hits the limit on (342f), decompose into named per-coefficient
  helpers per cycle 150's n=7 stepping-stone precedent
  (the `matrix7_oneMinusZSmul_det` split for §550).

* **Do NOT submit `Section441.lean` smoke tests on GPFS.** 43rd
  consecutive timeout was cycle 239. Skip per
  `.prover-state/issues/cycle_182_gpfs_slowness.md`.

* **Do NOT introduce `axiom` or `constant` declarations.**

* **Do NOT introduce sorries.** Cycles 149/200/201 all rolled back
  sorry-first scaffolds; the bar is "ship axiom-clean or skip the
  cycle's substantive goal and ship a smaller deliverable".

* **Do NOT pivot to lem:310B Phase A.3 (orbit-counting σ-faithfulness)
  this cycle.** It requires strengthening `TreeAutomorphism` from
  cycle 263's weakened root-fixing form to the full recursive
  structure-preservation predicate (multi-cycle `mutual` block per
  `feedback_rootedtree_nested_induction.md`). Stay in §342.

* **Do NOT pivot to thm:351B, lem:342B, or thm:302C.** thm:351B has
  5-8 cycle prerequisite chain per cycle 260's scoping; lem:342B
  is sequentially blocked by lem:342A; thm:302C is independent but
  unrelated to current §342 momentum.

* **Do NOT modify `scripts/autonomous_loop.py`.** The empty stuck-on
  field this cycle is a known phantom-prompt-builder bug per
  `.prover-state/issues/consultant_advice_cycle_263.md`. Loop
  maintainer territory.

* **Do NOT consume the full cycle budget on (342f) if first attempt
  stalls.** Time-box at 60 minutes from the start of Track 2. If
  not closing, fall back to §C.3 helpers cleanly.

## E. Cycle execution order

1. **(0-5 min)** Read this strategy. Run pre-flight verification:
   ```bash
   git log -1 --format='%H %s'           # confirm at HEAD
   wc -l OpenMath/Chapter3/Section342.lean
   grep -c sorry OpenMath/Chapter3/Section342.lean
   lake env lean OpenMath/Chapter3/Section342.lean   # smoke test
   ```
   Expected: HEAD `a2bec5e`, 246 LOC, 0 sorries, clean exit.

2. **(5-15 min)** Track 1: build Aristotle submission file
   `.prover-state/aristotle_submissions/cycle_273/342a_orthogonality.lean`
   per §C.1. Submit via `mcp__aristotle__submit_file`. Write
   `.prover-state/aristotle_submissions/cycle_273/README.md` with
   project ID + submission timestamp + prompt hint.

3. **(15-75 min)** Track 2: attempt manual (342f) recurrence per
   §C.2. Time-box at 60 minutes. If closing cleanly: ship + plan/
   status updates + task results. If stalled at 60 min: revert any
   intermediate edits, fall back to §C.3.

4. **(75-90 min, if §C.3 fallback)** Ship Helpers 1+2+3 from §C.3.
   Each is <30 min; expect to ship 2-3 of them.

5. **(90-105 min)** Write `task_results/cycle_273.md`. Document:
   * Track 1 submission ID + timestamp.
   * Track 2 outcome (success/fallback).
   * Faithfulness check on any new entity-named theorems.
   * Suggested cycle 274 priorities (poll Aristotle (342a) + decide
     based on result).

6. **(105-120 min)** Update `plan.md` / `lean_status.json` if a new
   Butcher sub-property closed (342f or any §C.3 helper). Commit
   + push (the worker handles this normally — do NOT skip).

## F. Faithfulness checklist (for any new entity-named theorem)

For each new `theorem` with a Butcher-named target (e.g.
`butcherShiftedLegendre_recurrence`):

- [ ] Quote the textbook statement verbatim from
  `extraction/formalization_data/entities/lem_342A.json` (or
  reference Butcher §342 if the sub-property is not in the JSON).
- [ ] Confirm Lean statement captures the same content; document
  any reformulation (e.g. `n ≥ 2` shifted to `n + 2`) in the
  docstring.
- [ ] **Definition smuggling check**: are you NOT defining a textbook
  concept as one of its consequences? (e.g. don't define
  "P_n^* satisfies the recurrence" as the conclusion of a theorem
  that's actually about a different polynomial. The recurrence
  formula must be a genuine consequence of the cycle 271
  `butcherShiftedLegendre` definition.)
- [ ] **Tautology check**: does the conclusion appear verbatim as a
  hypothesis? (For (342f), no — the recurrence is a genuine
  polynomial identity, not a restatement of any hypothesis.)
- [ ] **Hypothesis strength**: are any hypotheses stronger than
  Butcher requires? (Should only need `n : ℕ` — no analytic
  hypotheses for (342f) since it's pure polynomial arithmetic.)

## G. Risk profile + abort threshold

* **R1 (Track 2, MEDIUM-HIGH)**: `Polynomial.ext` + binomial
  coefficient comparison may not close via `push_cast; ring` if the
  Pascal identity `(k+1) · choose(n+2, k+1) = (n+2) · choose(n+1, k)`
  doesn't fall out automatically. *Mitigation*: try
  `Polynomial.funext` route first; it sidesteps binomial identities
  by reducing to real-valued polynomial identity in
  `eval`-ed `shiftedLegendre` values.

* **R2 (Track 2, MEDIUM)**: `Polynomial.coeff_shiftedLegendre` name
  may have drifted at HEAD. *Mitigation*: `lean_local_search
  "coeff_shiftedLegendre"` at minute 5 of Track 2 to confirm.

* **R3 (Track 2, LOW)**: ℕ-subtraction handling for `n - 1, n - 2`.
  *Mitigation*: state for `n + 2` (Nat.succ pattern), giving
  `n + 2 ≥ 2` automatically.

* **R4 (Track 3 fallback, LOW)**: Helper 2 (`butcherShiftedLegendre 0
  = C 1`) may not unfold by `simp [Polynomial.shiftedLegendre]`
  directly. *Mitigation*: case-split via `Polynomial.ext` and prove
  per-coefficient with `coeff_shiftedLegendre`.

**Abort threshold for Track 2**: 60 minutes from the start of
attempting (342f). If `Polynomial.ext` + simp + `push_cast; ring`
hasn't closed and `Polynomial.funext` + `ring` hasn't closed,
fall back to §C.3 immediately. Do NOT keep grinding.

**Abort threshold for Track 3**: 30 minutes per helper. If any
helper stalls (e.g. `simp` doesn't reduce `shiftedLegendre 0`),
ship the other helpers and document the stall.

## H. Score model

* **Score +2**: Track 2 (342f) ships axiom-clean + Track 1
  Aristotle submitted.
* **Score +1**: Track 2 stalls but Track 3 ships ≥2 helpers
  axiom-clean + Track 1 submitted.
* **Score 0**: Track 3 ships only 1 helper + Track 1 submitted (or
  Aristotle submission failed to fire).
* **Score -1**: nothing ships (no clean closure) but no
  regressions (sorry count stays 0).
* **Score -2**: introduce sorries OR break existing axiom-clean
  theorems.

A clean Track 2 + Track 1 fire is the +2 target. A clean Track 3
+ Track 1 is the +1 floor. Both are realistic for cycle 273.
