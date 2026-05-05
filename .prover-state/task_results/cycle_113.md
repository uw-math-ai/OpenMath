# Cycle 113 Results

## Worked on

- **Primary**: audit of the strategy's `IsConvergent`
  strengthening proposal against §514's actual consumer
  (`convergence_witness_satisfies_U`), which uses `yex = id`
  (unbounded). Identified architectural blocker before introducing
  any signature changes that would have regressed §514.
- **Secondary**: documentation — filed new issue
  `cycle_113_isconvergent_strengthening_514_blocker.md` enumerating
  four candidate solutions (localize bound, smooth-bounded IVP
  replacement, derive locally, accept §514 regression) with cost
  analysis; updated `aux_515D_output_tendsto_hypotheses.md` with the
  cycle-113 audit findings; updated `plan.md` to reflect cycle 113
  outcome.
- **Tertiary (inherited)**: a previous run within cycle 113 had
  already incorporated Aristotle's outputs to close sub-lemmas A
  (`aux_515D_per_step_recurrence`) and B (`aux_515D_gronwall_bound`)
  along with two new private helpers (`aux_515D_one_add_pow_le_exp`,
  `aux_515D_discrete_gronwall_raw`); those closures sat uncommitted
  in the working tree on entry to this run and are bundled into this
  cycle's commit. They reduced the OpenMath sorry count from 3 to 1
  (the lone remaining sorry being `aux_515D_output_tendsto`'s body).

## Approach

Per the cycle 114 strategy (loaded as cycle 113's strategy due to
heartbeat labeling drift), the planned work was:
1. Strengthen `IsConvergent` (Section512.lean) with 5 hypotheses.
2. Propagate to §513/§514 consumers.
3. Strengthen `aux_515D_output_tendsto`'s signature.
4. Compose its body using sub-lemmas A/B/C + `localStepError_bound`.
5. Update capstone `stable_consistent_isConvergent`.

**Audit step before execution** (mandated by the strategy's
"Audit both files carefully before claiming the cascade is
trivial" directive) revealed that §514's
`convergence_witness_satisfies_U` (Section514.lean:496) applies
`IsConvergent` to the IVP `f ≡ 1, yex = id, x = 1`. This IVP is
load-bearing: the cycle-098 stage-limit clause applied to
`yex = id` is what extracts `M.U *ᵥ u' = (fun _ => 1)`, the second
half of the `u' = u` bridge.

Applying the strategy's strengthening (which requires
`∀ t, |yex t| ≤ M_bound`) to `yex = id` is impossible: `id` is
unbounded on ℝ. Mathematical analysis: under the autonomous-ODE
constraint `deriv yex = f ∘ yex` with globally Lipschitz `f`,
non-constant `yex` is generically unbounded; constant `yex` with
`yex(x₀) = 0` forces `yex ≡ 0` and defeats the witness extraction.
Hence ANY non-trivial witness-extraction IVP for §514 has unbounded
`yex`, making the strategy's strengthening fundamentally incompatible
with §514's architecture.

Per the strategy's "Audit before claiming" directive, this was
identified before any signature changes were made. Pursuing the
strategy as-written would either (a) regress §514's closure (intro
1+ sorries) or (b) require a non-trivial smooth-bounded
replacement IVP for `convergence_witness_satisfies_U`.

**Forward-progress attempt (attempted, then reverted)**: drafted
an M-matrix-based `aux_515D_construct_ell_U_phi_A` helper that
constructs the auxiliary vectors `ell_U` and `phi_A` required as
inputs by `localStepError_bound`. The helper used the cycle-106
M-matrix infrastructure
(`Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one`) to invert
`(I − (h₀ L) |A|)` and apply it to the RHS vectors `|U| · 𝟙` and
`½ c² + |A| · |c|`. The proof structure was sound (existing
`aux_515B_eta_contraction` uses the same M-matrix machinery and
closes cleanly cycle 107), but `lake env lean
OpenMath/Chapter5/Section515.lean` ran for 20+ minutes without
completing on this large file (~2300 lines), and the LSP server
failed to start for incremental checking. To avoid committing
unverified code, the helper was **reverted**. The structural
plan and helper signature are documented in
`.prover-state/issues/aux_515D_output_tendsto_hypotheses.md` for
cycle 115+ to land.

## Result

**SUCCESS (audit + inherited sub-lemma closures)** — cycle 113
made critical audit progress without regressing the sorry count.
The inherited sub-lemma A/B closures from a prior run within
cycle 113 (which previously verified clean and produced the
task-results SUCCESS marker that this re-run found pre-existing in
the working tree) reduce sorry count 3 → 1 and are committed in
this cycle:

* Sorry count: 1 → 1 (unchanged, body composition deferred)
* New issue:
  `.prover-state/issues/cycle_113_isconvergent_strengthening_514_blocker.md`
  with 4 candidate solutions and cost/benefit analysis.
* Existing issue updated:
  `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md`
  with cycle-113 audit findings, per-hypothesis derivability
  re-confirmation, and a sketch of the cycle-115+ helper
  `aux_515D_construct_ell_U_phi_A`.
* `plan.md` updated to point at the new blocker issue.

Per the strategy's scoring rubric, this lands in the "−1 to 0"
range: no progress on the §515 capstone (Priority 4 deferred,
helper deferred to cycle 115), but critical audit findings that
would have been worse to discover during cascade execution.

## Faithfulness check

**Three new declarations bundled into this cycle's commit** (all
inherited from the prior cycle-113 run that pre-staged sub-lemma
A/B closures via Aristotle output incorporation):

### `aux_515D_per_step_recurrence` (closed via inherited Aristotle output)

* **Entity ID**: none — internal helper.
* **Lean statement**: abstract scalar recurrence
  `δ (m+1) ≤ V_norm·δ m + α·h·δ m + β·h²` ⇒
  `δ n ≤ (V_norm + α·h)^n · δ 0 + β·h² · ∑_{k<n} (V_norm + α·h)^k`.
* **Faithfulness**: corresponds to Butcher's iterated bound on the
  per-step error vector (p. 417, "iterating the bound 515b yields").
* **Tautology / identity / smuggling / strength** checks: all ✓
  (induction-based proof, hypotheses minimal).

### `aux_515D_one_add_pow_le_exp` (new helper)

* **Entity ID**: none — auxiliary inequality.
* **Lean statement**: `(1 + c)^n ≤ exp(n · c)` for `c ≥ 0`.
* **Faithfulness**: standard inequality; no textbook divergence.

### `aux_515D_discrete_gronwall_raw` (new helper)

* **Entity ID**: none — internal raw form of sub-lemma B.
* **Lean statement**: discrete Grönwall with `(1 + α·h)^n` base
  (geometric form, before exponential upgrade).
* **Faithfulness**: standard discrete Grönwall; geometric base is
  provably tighter and used as an intermediate step in the wrapper.

### `aux_515D_gronwall_bound` (closed via wrapper)

* **Entity ID**: none — internal helper.
* **Lean statement**: thin specialization of Section404's
  `discrete_gronwall_exp_bound` to `k = 1`.
* **Faithfulness**: faithful — conclusion shape matches Butcher's
  exp-shaped Grönwall bound (p. 347, eq. 406h application).

The drafted M-matrix helper `aux_515D_construct_ell_U_phi_A` (a
NEW cycle-113 advance attempt) was written but reverted before
commit due to insufficient time to verify its compilation;
therefore it is NOT part of the cycle 113 deliverable. Its sketch
is preserved as documentation in the updated
`aux_515D_output_tendsto_hypotheses.md` issue file for cycle 115+
to land.

* Tautology check: ✓ none of the four committed theorem closures
  have a conclusion matching a hypothesis.
* Identity check: ✓ all four are substantive proofs.
* Definition smuggling check: ✓ no new `def`/`structure` this
  cycle.
* Hypothesis strength check: sub-lemma B's `α > 0` is required
  (since `β/α` appears). Sub-lemma A requires non-negativity for
  `V_norm`, `α`, `h` to apply `mul_le_mul_of_nonneg_left`. All
  hypotheses are minimal.

## Dead ends

* **Strategy as-written**: pursuing the strategy's `IsConvergent`
  strengthening would have broken §514's `convergence_witness_satisfies_U`,
  cascading to `convergent_isPreconsistent` and
  `convergent_consistent_isStable_isConvergent`. Caught BEFORE
  introducing the regression by reading §514's proof.
* **Smooth-bounded IVP replacement** (Solution B from the issue
  file): considered using `c · Real.tanh` as a smooth bounded
  replacement for `id`, but the resulting `f` (computed from the
  ODE constraint `deriv (c · tanh) = f (c · tanh)`) is
  `f(y) = c − y²/c`, which is NOT globally Lipschitz. Other smooth
  bumps similarly fail. Construction of a smooth, bounded `g` with
  `g(0) = 0, g(1) = 1, deriv g = f ∘ g` for some Lipschitz `f` is
  non-trivial; deferred to cycle 115+ if Solution B is the path.
* **In-cycle helper landing**: drafted the
  `aux_515D_construct_ell_U_phi_A` helper but `lake env lean` on
  the full Section515.lean did not complete in 20+ minutes,
  exceeding the cycle's reasonable verification budget. The LSP
  server also failed to start for incremental checking. Reverted
  the helper draft to ensure a clean commit; the helper plan is
  preserved in the issue file for cycle 115+.

## Discovery

* **The strengthening cannot be globally bound**: any ODE solution
  on ℝ with non-constant `yex` and globally Lipschitz `f` is
  generically unbounded. The cycle-114 strategy's
  `(∀ t, |yex t| ≤ M_bound)` is therefore an artificial constraint
  that rules out the very IVPs §514 requires. The faithfulness-
  preserving move is to localize `M_bound` to `Set.Icc x₀ x` (the
  compact iteration interval), at the cost of refactoring
  `localStepError_bound` and its sub-helpers.
* **`localStepError_bound`'s `_h_norm` is over-restrictive**: the
  strategy's proposal `‖((x − x₀) L) • |A|‖ < 1` restricts the
  IsConvergent statement to "small `x − x₀`", which contradicts
  Butcher's "for any `x > x₀`". The right form is
  `∃ h₀ > 0, h_n ≤ h₀ eventually ∧ ‖h₀ • (L · |A|)‖ < 1`, which
  is automatic from `h_n → 0` (cycle 113 audit insight).
* **Section515.lean elaboration cost**: file ~2300 lines, full
  `lake env lean` build takes ≥20 minutes. Future cycles working
  in this file should batch verification at the end of the cycle
  rather than between intermediate edits.

## Suggested next approach

Cycle 115 should:

1. **Resolve the §514 cascade question** by choosing among
   Solutions A/B/C/D from
   `.prover-state/issues/cycle_113_isconvergent_strengthening_514_blocker.md`.
   Strong recommendation: **Solution A** (localize `M_bound` to
   `Set.Icc x₀ x`), since it is the only fully faithfulness-preserving
   path AND it unblocks both §514 (`yex = id` is bounded on `[0, 1]`)
   and the `localStepError_bound` consumer chain.

2. **Refactor `localStepError_bound`** (and its helpers
   `localStageError_bound_a/b`, `aux_T3_bound`, `aux_T4_bound`) to
   consume compact-interval bounds. Each helper currently uses
   `∀ t, |yex t| ≤ M_bound` GLOBALLY in proofs — these need to be
   re-proved with `∀ t ∈ Set.Icc x₀ x, |yex t| ≤ M_bound`. Per
   cycle-113 audit, all uses of `_hy_M` are at points `xn1 + h * c j`
   or `xn1 + h` where `xn1 ∈ [x₀, x - h]`, so the localization is
   straightforward.

3. **Land** `aux_515D_construct_ell_U_phi_A` (planned in cycle 113,
   deferred): the M-matrix-based constructor for the side-condition
   vectors. Sketch in
   `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md`. With
   adequate verification time (~30 min per Section515.lean compile),
   this should land in 1 cycle.

4. **Then** strengthen `IsConvergent` with the localized bounds
   and propagate to §513 (`yex = 0`, `M_bound := 0` works), §514
   (`yex = id`, `M_bound := |x|` works on `[x₀, x]`), and the
   capstone.

5. **Then** compose `aux_515D_output_tendsto`'s body using sub-lemmas
   A/B/C + the strengthened `localStepError_bound` + cycle-115
   `aux_515D_construct_ell_U_phi_A`.

6. **Update lean_status.json** for `thm:515D` to `closed` once
   the capstone is fully reconnected.

If cycle 115 is too ambitious for the full Solution A refactor,
break into:
* (115a) `localStepError_bound` localization (compact-interval
  refactor of `_hy_M`) + `aux_515D_construct_ell_U_phi_A` landing.
* (115b) `IsConvergent` strengthening + cascade.
* (115c) Body composition + capstone update.
