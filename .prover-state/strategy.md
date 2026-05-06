# Cycle 149 Strategy

## Status snapshot

- Sorry count: **0** (clean baseline maintained for 9+ consecutive cycles).
- Last 5 cycles: 144 (n=3) → 145 (n=4) → 146 (def:520E/F r=2 negative
  witnesses) → 147 (n=5) → 148 (n=6 + Aristotle general-n submission).
- Plan progress: 69 / 175 entities.
- thm:515D (the §515 capstone) is closed and axiom-clean since cycle 124.
- thm:550A: six concrete-`n` axiom-clean stepping stones (n = 1..6);
  general-n still deferred. Aristotle project
  `2c4630b2-2998-4d4a-af88-c2f83fbd9eda` was submitted in cycle 148
  packaging all six closed proofs as in-context templates.

## Priority 0 (≤5 min) — Aristotle single-poll

**Action**: Run `mcp__aristotle__get_status` ONCE on project
`2c4630b2-2998-4d4a-af88-c2f83fbd9eda`. Per CLAUDE.md single-poll
discipline: this is the cycle's only allowed Aristotle poll on
this project; do NOT re-poll within this cycle.

### Decision tree

- **If COMPLETE with a clean proof body**:
  1. `mcp__aristotle__extract_result` to retrieve the Lean code.
  2. Reinstate the general-`n` statement
     `doublyCompanionMatrix_det_factorization` in
     `OpenMath/Chapter5/Section550.lean` (cycle 139 removed it; cycle 148
     packaged all six concrete-n proofs as in-context templates).
  3. Verify with `lake env lean OpenMath/Chapter5/Section550.lean`.
  4. `lean_verify` to confirm `[propext, Classical.choice, Quot.sound]`
     only — REJECT if any other axiom appears.
  5. Update `extraction/formalization_data/lean_status.json`:
     `thm:550A` → `formalized` (drop `partial`).
  6. Update `plan.md` line 218 (thm:550A row): drop the `[~]` and
     replace with `[x]`; trim the long status comment to a single
     line referencing the general-n closure cycle.
  7. Update `.prover-state/issues/thm_550A_general_n.md` with a
     "RESOLVED cycle 149" header noting Aristotle closure.
  8. Commit + push. Cycle done.
  9. Skip Priority 1.

- **If FAILED, CANCELLED, or returns garbage** (e.g. uses `sorry`,
  invokes `axiom`, references missing definitions): do NOT spend
  cycle time debugging Aristotle output. Cancel the project via
  `mcp__aristotle__cancel_project` and move directly to Priority 1.

- **If still IN_PROGRESS at any percentage**: leave it running, move
  to Priority 1. Do NOT cancel — a future cycle may poll it again.
  (Cycle 141's Aristotle Job A was cancelled at 6% after 24h, which
  is the historical baseline for "intractable" — anything earlier
  than that is still potentially viable.)

## Priority 1 (60–90 min) — Open `def:530B` with sorry-first scaffold

**Target**: `def:530B` "Order relative to starting method (530B)"
(`extraction/formalization_data/entities/def_530B.json`, page 432).

**Why this target**:
- Builds directly on cycle 139's §530 `StartingMethod` infrastructure
  in `OpenMath/Chapter5/Section530.lean` (already 259 LOC,
  `trivialStartingMethod` + `mixedStartingMethod` non-vacuity
  witnesses landed).
- Topologically next: `def:530B` is the only `[ ]` entry in §530 with
  all dependencies satisfied (`def:530A` done cycle 139). `def:530C`
  depends on `def:530B` and is a one-line existential corollary.
- §550 ladder has hit diminishing returns per cycle 148 task results
  ("n=7 unlikely to be worth the cycle").
- def:525A G-symplecticity already has BOTH trivial (cycle 128
  `explicitEulerGLM_isGSymplectic` G=D=0) AND substantive
  (`implicitMidpointGLM_isGSymplectic` G=D=1) witnesses in
  `OpenMath/Chapter5/Section525.lean`; chasing the Butcher (525d)
  √3 witness adds a 3rd witness without adding non-vacuity content.
  Skip.

**Textbook content** (Butcher §530, p. 432):
> "Consider a general linear method M and a non-degenerate starting
> method S. The method M has order p relative to S if the results
> found from SM and ES agree to within O(h^{p+1})."

The textbook compares two `(Fin r) → ℝ` vectors:
- `SM(y₀, h)` — first apply starting method `S` to `y₀` to produce
  `r` initial values; then carry out one step of `M` with stepsize
  `h` to produce a new `r`-vector of approximations.
- `ES(y₀, h)` — first advance the exact solution forward by time
  `h` to `y(x₀+h)`; then apply each member of `S` to `y(x₀+h)`.

"Agree to within `O(h^{p+1})`" means
`‖SM(y₀, h) - ES(y₀, h)‖ = O(h^{p+1})` as `h → 0`.

### Sorry-first scaffold (Lean shape)

In `OpenMath/Chapter5/Section530.lean`, add (after the existing
`mixedStartingMethod` block):

```lean
section OrderRelativeToStartingMethod

variable {s r : ℕ}

/-- The vector `SM(y₀, h)` from def:530B: starting method `S`
constructs initial approximations from `y₀`, then GLM `M` carries
out one step. -/
noncomputable def applyStartingThenStep
    (M : GeneralLinearMethod s r) (S : StartingMethod r)
    (f : ℝ → ℝ) (y₀ : ℝ) (h : ℝ) : Fin r → ℝ :=
  sorry  -- compose: S applied to y₀ → r-vector; then one M-step
         -- of size h on that r-vector with RHS f.

/-- The vector `ES(y₀, h)` from def:530B: exact-solution evolution
by time `h`, then starting method `S` applied to `y(x₀+h)`. -/
noncomputable def applyExactThenStarting
    (S : StartingMethod r) (yex : ℝ → ℝ) (x₀ h : ℝ) : Fin r → ℝ :=
  sorry  -- compose: yex(x₀+h) → ℝ; then S applied to that scalar
         -- gives r-vector.

/-- Definition 530B: M has order `p` relative to non-degenerate
starting method `S` if `SM` and `ES` agree to `O(h^{p+1})`. -/
def GeneralLinearMethod.HasOrderRelativeTo
    (M : GeneralLinearMethod s r) (S : StartingMethod r)
    (_hS : S.IsNonDegenerate) (p : ℕ) : Prop :=
  ∀ (f : ℝ → ℝ) (yex : ℝ → ℝ) (x₀ y₀ : ℝ),
    yex x₀ = y₀ → (∀ t, HasDerivAt yex (f (yex t)) t) →
    (fun h : ℝ =>
      applyStartingThenStep M S f y₀ h
        - applyExactThenStarting S yex x₀ h)
    =O[nhds 0] (fun h => h ^ (p + 1))

end OrderRelativeToStartingMethod
```

(Adjust sub-namespaces / `noncomputable` markers as needed for
existing scope. Use `import Mathlib.Analysis.Asymptotics.Asymptotics`
or a similar location for `=O[nhds 0]` if not already imported in
Section530.)

### Definition smuggling check

CRITICAL: `applyStartingThenStep` and `applyExactThenStarting` are
*operations on real-valued functions*, not Prop. They must compute
the textbook quantities faithfully. Specifically:

- `applyStartingThenStep` should match Butcher's notation `SM`: the
  starting method `S` constructs `r` initial approximations
  `y₀^{[i]} ≈ y(x₀ + b₀^{(i)} h)` (or some variant — read §530
  closely), then the GLM applies `[A U; B V]` to produce `r` outputs.
- `applyExactThenStarting` should match Butcher's `ES`: advance the
  *exact* `yex` by `h`, then apply each starting-method
  generalized-RK to `yex(x₀+h)` to produce an `r`-vector.

The textbook's "ES" notation specifically means `E ∘ S` where `E`
is the exact-flow operator and `S` is the starting method. Make
sure the order of composition matches what §530 actually says.

If the precise textbook semantics is unclear after a careful read
of `extraction/raw_text/ch05.txt §530`, write a structured issue
file (`.prover-state/issues/def_530B_SM_ES_semantics.md`) and
defer the operator definitions to a planning cycle.

### Non-vacuity strategy

After the scaffold compiles (sorry'd or with skeleton bodies), add a
non-vacuity witness — preferably **sorry-first** with the goal of
closing it later, or **vacuously-trivial** if the predicate is
satisfied for any nonexistent / minimal witness.

Two candidate witnesses, in order of cleanness:

1. **Trivial GLM × trivial starting method, `p = 0` order**:
   The `explicitEulerGLM` (`(s, r) = (1, 1)`) paired with
   `trivialStartingMethod` (single-stage with `b₀ = 1`) — verify
   they trivially agree at `h = 0` (both sides equal `y₀`), so the
   `O(h)` bound is trivially attained. Encode as:
   ```lean
   theorem explicitEulerGLM_hasOrderZero_trivialStarting :
     explicitEulerGLM.HasOrderRelativeTo trivialStartingMethod
       trivialStartingMethod_isNonDegenerate 0 := by
     sorry
   ```
   Submit to Aristotle; close manually if Aristotle fails.

2. **Refutability witness**: pair some GLM with a starting method
   for which order > 0 fails. This rules out `HasOrderRelativeTo`
   being trivially-true.

The cycle deliverable bar is: scaffold compiles + non-vacuity
witness exists (sorry-first OK if the proof body is non-trivial).
Per CLAUDE.md "If you use an equivalent formulation, add an
explicit equivalence lemma" — if `applyStartingThenStep` ends up
diverging from the textbook `SM`, prove the equivalence as a
separate lemma in the same cycle or document the divergence in an
issue file.

### Aristotle batch (parallel to manual work)

Once the scaffold compiles with sorry'd bodies for
`applyStartingThenStep`, `applyExactThenStarting`, and the
non-vacuity witness, batch-submit them to Aristotle (~3 jobs).
Use `mcp__aristotle__submit_file` with the entire scaffold as
context.

Single-poll the batch at the END of the cycle (or defer the poll
to cycle 150 if the cycle clock is up).

## Priority 2 (5–10 min) — Housekeeping

- Update `plan.md` Chapter 5 row for `def:530B`: change `[ ]` to
  `[~]` (in-progress) with a brief status note (sorry'd scaffold +
  non-vacuity witness; cycle 149 reference).
- Update `extraction/formalization_data/lean_status.json` row for
  `def:530B`: `unformalized` → `partial` with cycle 149 reference.
- Cycle results in `.prover-state/task_results/cycle_149.md` per
  CLAUDE.md format.

## What NOT to try (explicit blacklist)

1. **Do NOT continue the n=7 / n=8 thm:550A ladder.** Cycle 148 task
   results explicitly flagged this as diminishing returns. Six rungs
   is enough in-context evidence; further laddering is busy-work
   without payoff. Aristotle's general-n submission is the correct
   path forward.

2. **Do NOT attempt manual general-`n` closure of thm:550A this
   cycle.** It is multi-cycle infrastructure work (cofactor
   expansion induction or eigenvalue-density argument). Cycle 141
   confirmed Aristotle gave up at 6% after 24h on the eigenvalue
   path. If cycle 149's poll comes back IN_PROGRESS, just wait —
   do not duplicate the effort manually.

3. **Do NOT re-poll Aristotle project `2c4630b2-…` more than once.**
   CLAUDE.md single-poll rule. The poll is the cycle's only Aristotle
   interaction with that project.

4. **Do NOT chase the def:525A Butcher (525d) √3 witness.** def:525A
   non-vacuity is already saturated: cycle 128 has both trivial
   (G=D=0, explicitEulerGLM) AND substantive (G=D=1,
   implicitMidpointGLM) witnesses in
   `OpenMath/Chapter5/Section525.lean`. The Butcher (525d) witness
   would be a 3rd witness primarily useful for supporting thm:534A's
   order-4 analysis, which is far downstream and not on the critical
   path.

5. **Do NOT raise `maxHeartbeats`** above 200000. If
   `applyStartingThenStep` / `applyExactThenStarting` proofs hit
   the timeout, decompose into helper lemmas.

6. **Do NOT introduce `axiom` or `constant` declarations** for the
   SM/ES operators. If their definition is unclear from the
   textbook, defer to a planning cycle (issue file) rather than
   axiomatising.

7. **Do NOT silently weaken `def:530B`'s statement to a tautology.**
   Per CLAUDE.md pre-commit faithfulness checklist: the predicate
   must capture the *primary mathematical meaning* (Butcher's
   "agree to within `O(h^{p+1})`"), not a syntactic simplification.
   If your scaffold collapses to `True ∧ True` or a vacuous
   quantifier pattern, escalate to an issue file.

8. **Do NOT modify `scripts/autonomous_loop.py`.** Loop-maintainer
   territory; existing tautology-scanner false-positive issue
   (cycle 015 issue file) remains unfixed but is not blocking.

9. **Do NOT batch-submit to Aristotle before the manual scaffold
   compiles.** Aristotle needs the scaffold's sorry'd bodies to
   know what it's targeting. Submission before compile = wasted
   compute.

## Backup plans (if Priority 1 stalls)

- **B1 (semantic ambiguity in SM/ES)**: if `applyStartingThenStep`
  and `applyExactThenStarting` cannot be cleanly defined from
  Butcher's text alone, write
  `.prover-state/issues/def_530B_SM_ES_semantics.md` documenting
  the ambiguity (which clause depends on `b₀^{(i)}`? which on
  `c^{(i)}`? what is the abscissa pattern?). Land the issue + a
  partial scaffold (just the predicate skeleton + a sorry'd
  non-vacuity) as the cycle deliverable. Sorry count goes 0 → 1
  but the sorry locus is well-documented.

- **B2 (def:530B too heavy)**: if the SM/ES operators take more
  than 60 min of cycle time, scope down to: just the
  `HasOrderRelativeTo` predicate signature (with sorry'd
  `applyStartingThenStep` + sorry'd `applyExactThenStarting` body)
  + sorry'd non-vacuity witness. Document in cycle results. Cycle
  150 closes the operator definitions and the witness.

- **B3 (Aristotle returns mid-cycle COMPLETE for thm:550A)**:
  abandon Priority 1 mid-stream, incorporate the general-n proof,
  and close thm:550A. Cycle 150 then opens def:530B fresh.

- **B4 (zero-progress fallback)**: if both Aristotle and the
  def:530B scaffold both stall, write a substantive issue file
  documenting the def:530B ambiguity (as B1) and commit. Per
  CLAUDE.md: "A cycle with zero changes is unacceptable. At minimum,
  decompose a sorry or write an issue."

## Pre-commit checklist (must run before `git push`)

Per CLAUDE.md pre-commit faithfulness checklist:

- [ ] `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
- [ ] `lean_verify` on each new public definition / theorem returns
      `[propext, Classical.choice, Quot.sound]` (or `sorryAx` only
      if the sorry locus is documented in the cycle results).
- [ ] Sorry count vs. cycle 148 baseline: 0. Cycle 149 may end
      with sorry count 0 (Aristotle path), 1 (sorry-first scaffold
      with non-vacuity sorry'd), or up to 3 (def:530B operators +
      predicate non-vacuity all sorry'd). Document in cycle results.
- [ ] No new `axiom` or `constant` declarations.
- [ ] `extraction/formalization_data/entities/def_530B.json`
      consulted; predicate matches the textbook statement (or
      divergence documented in an issue file).
- [ ] `plan.md` and `lean_status.json` reflect the cycle outcome.
- [ ] `.prover-state/task_results/cycle_149.md` written per CLAUDE.md
      format.

## Estimated timeline

- Priority 0 (Aristotle poll): 5 min.
- Priority 1 (def:530B scaffold + sorry-first witness + Aristotle
  batch submission): 60–90 min.
- Priority 2 (housekeeping + commit): 10 min.

Total: **75–105 min**.

Cycle 149 is a "structural" cycle, not an analytical one. The
deliverable bar is "scaffold lands clean" not "all sorries closed".
Per the cycle 148 pattern (sorry count → 0 maintained), the worker
should NOT push toward zero sorries at the cost of analytical
correctness or rushed semantics. A sorry-first scaffold with
documented faithfulness is the correct shape.
