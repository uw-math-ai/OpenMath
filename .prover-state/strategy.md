# Cycle 286 Strategy — §342 (342f) Aristotle poll + n=10 fallback

## Context

Cycle 285 cancelled the long-stalled Aristotle project `c8b8f138` (12%
across three consecutive cycle-polls) and submitted a strengthened
resubmission **`efe4940e-0931-4fb2-8549-7eafab20d7f7`** at end of cycle
285 (status: QUEUED). The replacement bundles cycle 281's
`leadingCoeff = C(2n, n)`, cycle 277's iterated-IBP machinery, explicit
small-`n` axioms for n=0..8, witnessed recurrence at n=2..8, and the
verbatim textbook proof sketch.

The §342 (342f) ladder now covers n=2..9 (cycle 285 shipped n=9).
Sorry count: 0. Axiom-clean. `lake env lean OpenMath/Chapter3.lean`
exits 0.

## Priority 0 (MANDATORY): Single-poll Aristotle `efe4940e`

**Tool**: `mcp__aristotle__get_status` on project_id
`efe4940e-0931-4fb2-8549-7eafab20d7f7`.

**Discipline**: ONE poll only. CLAUDE.md prohibits re-polling within
a cycle. Decide on the single observation.

Branch on the result:

### Branch A — Aristotle status COMPLETE (integrate the proof)

1. `mcp__aristotle__download_result` → retrieve the proof.
2. Extract helper lemmas into a new file
   **`OpenMath/Chapter3/Section342RecurrenceHelpers.lean`** under
   namespace `OpenMath.Chapter3.Section342Helpers` (mirror cycle 281's
   `Section342NormSqHelpers.lean` pattern). Cycle 281 precedent: helper
   files isolate substantive Mathlib plumbing (IBP, Beta integrals,
   arithmetic identities) from the textbook-specific main file.
3. Ship the general theorem
   `butcherShiftedLegendre_recurrence (n : ℕ) (hn : 2 ≤ n) :
   (n : ℝ) • butcherShiftedLegendre n
     = C (2 * n - 1 : ℝ) · (C 2 · X − C 1) · butcherShiftedLegendre (n − 1)
       − C (n − 1 : ℝ) · butcherShiftedLegendre (n − 2)` in
   `OpenMath/Chapter3/Section342.lean`, citing the helper file.
4. Verify axiom-clean via `mcp__lean-lsp__lean_verify` on each new
   declaration. Expected: `[propext, Classical.choice, Quot.sound]`.
5. Confirm n=2..9 explicit witnesses (cycles 282/283/284/285) still
   compile against the new general theorem (do not remove them — they
   serve as non-vacuity at the small-n end and are independent direct
   computations).
6. Run `lake env lean OpenMath/Chapter3.lean` and confirm exit 0.
7. Update `extraction/formalization_data/lean_status.json`: `lem:342A`
   row stays `partial` because (342g) — `P_n^*` has `n` distinct real
   zeros in `(0, 1)` — is still open. Note (342f) closed in cycle 286.
8. **P2 stretch (if budget allows)**: fire-and-forget Aristotle on
   (342g). Submission file recipe in
   `.prover-state/issues/lem_342A_g_zeros_scoping.md`; cite (342a),
   (342f), `butcherShiftedLegendre_natDegree`, and the explicit small-n
   forms as axioms.

### Branch B — Aristotle status IN_PROGRESS at any %

Ship n=10 ladder rung manually. Recipe is mechanical port of cycle
285's n=9:

1. **Verify n=10 coefficients via Python integer arithmetic before
   touching Lean** (cycle 285 precedent: catches sign / Pascal-identity
   errors before they hit the build). Use
   `coeff_shiftedLegendre n k = (-1)^k · C(n,k) · C(n+k, n)` at n=10,
   then flip by outer Butcher sign `(-1)^10 = +1` (even — no
   per-coefficient sign flip beyond what `coeff_shiftedLegendre` gives).
   Leading coefficient: `+C(20, 10) = +184756`. Constant term:
   `P_10^*(0) = +1` (matches `(-1)^10`). Sanity: `P_10^*(1) = 1`
   (matches (342b)) — sum of all coefficients should be 1.

2. **Verify n=10 recurrence in Python integer arithmetic before Lean**:
   `10 · P_10^*(x) ?= 19 · (2x − 1) · P_9^*(x) − 9 · P_8^*(x)` should
   yield identical descending-coefficient vectors. The `(2n−1, n−1) =
   (19, 9)` instantiation matches Butcher (342f).

3. **Lean ship — `butcherShiftedLegendre_ten`**: cycle 277/279 even-n
   template. Outer Butcher sign `(-1)^10 = +1` is trivial (no
   `(-1)^n` peel-off complications). Recipe:
   ```
   unfold butcherShiftedLegendre
   ext k
   simp only [coeff_C_mul, coeff_map, coeff_shiftedLegendre]
   match k with
   | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => decide-style
   | k+11 => Nat.choose_eq_zero_of_lt tail
   ```
   With per-arm `norm_num` and `decide`-helpers for the `Nat.choose`
   evaluations at k=2..9 (cycle 285's exact pattern).

4. **Lean ship — `butcherShiftedLegendre_recurrence_ten`**: cycle 282+
   template `Polynomial.funext → rw [_ten, _nine, _eight] → simp [eval_*]
   → ring`.

5. Both theorems verified axiom-clean via `lean_verify`.

6. `lake env lean OpenMath/Chapter3/Section342.lean` exit 0. Aggregator
   build optional but recommended.

7. Sorry count remains 0. Leave Aristotle `efe4940e` running for cycle
   287 poll.

### Branch C — Aristotle status COMPLETE_WITH_ERRORS

Apply suggested fixes per cycle 277's pattern. Specifically:

1. Read Aristotle's `ARISTOTLE_SUMMARY.md` (via
   `mcp__aristotle__extract_result` or download).
2. Diff Aristotle's edited submission against
   `.prover-state/aristotle_submissions/cycle_285/342f_recurrence_v2.lean`
   to identify the actual fix (e.g. namespace resolution, simp set
   ordering, lemma renaming).
3. Apply the fix locally and retest with `lake env lean
   OpenMath/Chapter3/Section342RecurrenceHelpers.lean` (or wherever
   the helpers land).
4. If the fixes are small (namespace, single-line), ship as
   Branch A. If they require substantive restructuring (>50 LOC of
   tactic changes), fall back to Branch B (n=10 ladder rung) and
   defer integration to cycle 287.

### Branch D — Aristotle status FAILED or CANCELLED

1. Document the failure in
   `.prover-state/issues/cycle_286_aristotle_failure.md` summarising
   the strengthened-resubmission attempt outcome.
2. Execute Branch B (n=10 ladder rung) as the cycle's substantive
   deliverable.
3. Escalation note: if cycle 287's cycle 285+286 evidence base
   shows the strengthened resubmission also fails, the planner
   should pivot to **manual closure** of (342f) using cycle 281's
   `leadingCoeff` infrastructure. A 3–4 cycle manual proof is
   feasible:
   - Cycle X: form `Q := LHS − RHS` and prove `Q.natDegree < n`
     via leading-coefficient cancellation
     (`n · C(2n, n) = 2(2n−1) · C(2n−2, n−1)` Pascal identity).
   - Cycle X+1: prove `Q.aeval` vanishes on `{P_0^*, …, P_{n−1}^*}`
     basis via (342a) orthogonality + cycle 277's IBP machinery.
   - Cycle X+2: combine: `Q.natDegree < n` + Q ⊥ first `n`
     Legendre polynomials + Mathlib density of polynomials in
     `L²([0,1])` forces `Q = 0`.
   - Cycle X+3: cleanup + non-vacuity.

## Priority 1 (only if Branch B/C/D fires AND Branch A is NOT viable next cycle): fire-and-forget Aristotle on (342g)

After shipping the cycle 286 substantive deliverable (either n=10
rung or Branch A general theorem):

1. Build `.prover-state/aristotle_submissions/cycle_286/342g_zeros.lean`
   per the recipe in `.prover-state/issues/lem_342A_g_zeros_scoping.md`.
2. Cite as axioms: (342a) `butcherShiftedLegendre_orthogonal` (cycle
   277), (342f) `butcherShiftedLegendre_recurrence` if Branch A
   landed, `butcherShiftedLegendre_natDegree` (cycle 272),
   `butcherShiftedLegendre_eval_one_sub` (cycle 271, for parity),
   `butcherShiftedLegendre_eval_one` (cycle 271), and the explicit
   small-n forms for sanity.
3. Strategy hint in the prompt: "sign-change contradiction. Suppose
   `P_n^*` has fewer than `n` sign-change zeros in `(0, 1)`. Take
   their product polynomial `Q := ∏ᵢ (X − xᵢ)` of degree < n. By
   (342a), `∫₀¹ P_n^* · Q = 0`. But `P_n^* · Q` has constant sign on
   `(0, 1)` (by construction of `xᵢ` as the sign-change zeros) and
   is nonzero on a positive-measure set, so the integral is nonzero.
   Contradiction."
4. Submit via `mcp__aristotle__submit_file`. Record project_id in
   this cycle's task results.

**Skip this priority entirely if Branch A fires** — the cycle 286
deliverable will already saturate the available LOC budget and
Aristotle job slot.

## What NOT to attempt

- **DO NOT re-poll Aristotle `efe4940e` within cycle 286.** CLAUDE.md
  is explicit: one poll per cycle.
- **DO NOT cancel Aristotle `efe4940e` before single-polling it.**
  The cycle 285 resubmission was deliberate; only third+ stall (cycle
  287's poll showing no movement) justifies cancellation.
- **DO NOT attempt manual general (342f) closure this cycle.** The
  3–4 cycle plan in Branch D's escalation is for cycle 287+ if
  Aristotle fails again. Cycle 286's manual ship target is the n=10
  ladder rung, NOT the general theorem.
- **DO NOT attempt to compile `OpenMath/Chapter4/Section441.lean`.**
  43+ consecutive GPFS timeouts since cycle 182 per
  `.prover-state/issues/cycle_182_gpfs_slowness.md`. Skip entirely.
- **DO NOT raise `maxHeartbeats` above 200000.** If n=10 closed-form
  expansion stalls (which would be surprising — cycles 277/278/279
  proved the even-n template at depths 4/5/6), decompose into smaller
  per-coefficient lemmas, do not increase heartbeats.
- **DO NOT introduce `axiom` or `constant` declarations.** All
  cycle 286 deliverables must be axiom-clean
  (`[propext, Classical.choice, Quot.sound]`).
- **DO NOT introduce `sorry`s.** Cycles 149/150, 200/201, and 138/139
  all rolled back sorry-first scaffolds for multi-cycle targets.
  Cycle 286's bar: ship axiom-clean or skip the deliverable.
- **DO NOT pivot to a fresh entity this cycle.** §342 (342f)
  closure is mid-flight (Aristotle resubmission live, n=10 manual
  ladder rung is a clean fallback). Pivoting now would waste the
  cycle 285 resubmission investment.
- **DO NOT modify `scripts/autonomous_loop.py`.** Loop-maintainer
  territory per CLAUDE.md.

## Failed approaches to avoid (from `attempts.md` / prior cycles)

- **Aristotle on (342f) without strengthening**: project `c8b8f138`
  stalled at 12% for three consecutive cycles (283/284/285). Cycle
  285 cancelled and resubmitted with cycle 281's `leadingCoeff`,
  cycle 277's iterated-IBP machinery, n=0..8 explicit forms, and
  n=2..8 recurrence base cases axiomatized. Do not re-submit a
  weaker version.
- **`Polynomial.ext` (cycle 273)**: requires Pascal-style `Nat.choose`
  identities that `ring` cannot fold. Use `Polynomial.funext + ring`
  (cycle 180 onward) for `Polynomial ℝ` constant arithmetic; for the
  explicit-form expansions, use the `coeff_C_mul + coeff_shiftedLegendre
  + match k` recipe (cycle 276 onward).
- **(342f) without (342a) orthogonality**: cycle 273 attempted both
  `Polynomial.ext` and `Polynomial.funext` routes; both require
  binomial identities that `ring` cannot close, plus Mathlib has no
  standard Legendre infrastructure. The cycle 277 (342a) closure
  unblocked Bonnet-style arguments (now used in Aristotle `efe4940e`'s
  proof sketch).
- **Section441-touch GPFS smoke tests**: 43+ consecutive timeouts.
  Skip.

## Verification checklist (must pass before commit)

1. `lake env lean OpenMath/Chapter3/Section342.lean` — exit 0.
2. (If Branch A) `lake env lean OpenMath/Chapter3/Section342RecurrenceHelpers.lean`
   — exit 0.
3. `lake env lean OpenMath/Chapter3.lean` (aggregator) — exit 0.
4. `mcp__lean-lsp__lean_verify` axiom-clean on each new public theorem.
5. Sorry count audit: `grep -c sorry OpenMath/Chapter3/Section342.lean`
   should output `0` (cycle history mentions don't count; check actual
   proof terms).
6. Faithfulness check (CLAUDE.md mandatory):
   - For new `def`s (only Branch A): quote textbook statement from
     `extraction/formalization_data/entities/lem_342A.json`, confirm
     Lean type matches.
   - For new theorems: tautology check (conclusion ≠ hypothesis
     verbatim), identity check (proof not just `exact h`), hypothesis
     strength check (no extra hypotheses vs textbook), absent theorem
     check (no promised `sorry`s in comments).
7. Update `extraction/formalization_data/lean_status.json` only if a
   textbook entity status changes (Branch A: `lem:342A` cycle bump to
   286 but status remains `partial` until (342g) closes; Branch B:
   `lem:342A` cycle bump only, status unchanged).
8. Update `plan.md` only if `lem:342A` row's progress note needs
   updating (append cycle 286 line to the existing partial-status
   note; do NOT flip `[~]` to `[x]` until (342g) closes).

## Task results structure for cycle 286

Write `.prover-state/task_results/cycle_286.md`:

```markdown
# Cycle 286 Results

## Worked on
- P0 (mandatory): single-poll Aristotle `efe4940e`. Result: <status>.
- P1: <Branch A integration / Branch B n=10 ship / Branch C fixes>.
- P2 stretch (if applicable): fire-and-forget Aristotle on (342g).

## Approach
<per branch>

## Result
<SUCCESS / FAILED — explanation>

## Faithfulness check
<per CLAUDE.md checklist>

## Dead ends
<approaches that didn't work and why>

## Discovery
<anything learned that's useful for cycle 287+>

## Suggested next approach
<what cycle 287's planner should consider>
```

## Bottom-line cycle 286 directive

1. Single-poll `efe4940e`.
2. Branch A (COMPLETE) → integrate as helper file + general theorem.
3. Branch B/C/D → ship n=10 ladder rung manually (cycle 285's n=9
   template).
4. P2 stretch (Branch A only): fire-and-forget Aristotle on (342g).
5. Maintain sorry count 0, axiom-clean discipline, no GPFS-blocked
   §441 work.
