# Cycle 120 Results

## Worked on

* **Aristotle hygiene** (Priority 0 of cycle 120 strategy):
  - Polled Job 2 (`63045685-...`, cycle 117): `IN_PROGRESS` at 38% — left running.
  - Polled Job 3 (`e68b3d59-...`, cycle 118 narrowed): `IN_PROGRESS` at 11% — left running.
  - Submitted Job 4 (`fb7ce569-...`) for `aux_515D_iterated_V_bound`.
* **`aux_515D_iterated_V_bound`** (Priority 1, the load-bearing helper from
  `.prover-state/issues/aux_515D_iterated_V_bound.md`'s Path A): introduced
  and proved manually at `OpenMath/Chapter5/Section515.lean:1854`.
* **Job 4 cancellation**: cancelled after manual closure (cycle 120 doesn't
  need Aristotle's redundant attempt; freed the slot for cycle 121).
* **Priority 2 deferred**: chose not to attempt the body composition of
  `aux_515D_max_deviation_geometric_bound` this cycle. Per strategy:
  "If only iterated-V helper closes: net advance is +1 closed sub-helper" —
  this is a valid cycle outcome.

## Approach

### Priority 1 (`aux_515D_iterated_V_bound`)

**Strategy chosen**: a crude `C' := r · C` bound proved entrywise via
the Frobenius norm, instead of the strategy's recommended
`Matrix.linfty_opNorm`-based `C' := √r · C` bridge.

**Why crude was better**:
- Section515.lean opens `scoped Matrix.Norms.Frobenius`, making the
  default `‖·‖` for matrices the Frobenius norm.
- `Matrix.linfty_opNorm_mulVec` (the strategy's preferred Mathlib
  lemma) expects the linfty op norm to be the default norm in scope —
  it doesn't typecheck against the Frobenius default in our file
  without explicit annotation, scope manipulation, or a Frobenius ↔
  linfty op norm bridge lemma (which I couldn't find in Mathlib for
  this specific direction).
- The crude bound avoids both issues: prove `|V^k_{i,j}| ≤ ‖V^k‖_F ≤ C`
  directly (entrywise dominance), then sum over the row to get
  `∑_i |V^k_{j,i}| ≤ r · C`.
- For §515D, the constant `C'` doesn't have to be tight — only
  non-negative and a function of stability. `r · C` works fine.

**Proof structure** (~70 LOC):
1. Extract `C, hC_nn, hC` from `hStab`.
2. Set `S := ∑_a ∑_b ((V^k) a b)^2` (the squared Frobenius sum).
3. Bridge `‖V^k‖^2 = S` via `Matrix.frobenius_norm_def`,
   `Real.sqrt_eq_rpow`, `Real.sq_sqrt`, with `Real.rpow_two` to
   bridge real-vs-nat exponent for `sq_abs`.
4. Prove entrywise bound: `|(V^k) j i|^2 ≤ S` (single term ≤ sum)
   ⇒ `|(V^k) j i| ≤ ‖V^k‖_F ≤ C` via `abs_le_of_sq_le_sq`.
5. Apply `Finset.sup'_le`: for each `j`, expand `(V^k *ᵥ x) j` as
   a finset sum, use `Finset.abs_sum_le_sum_abs`, then bound each
   summand `|(V^k) j i| · |x i| ≤ C · sup'_l |x l|`.
6. Sum over `r` summands gives `(r · C) · sup'_l |x l|`.

### Priority 2 (deferred)

Considered the strategy's Step 2a (add `0 ≤ M.glmAbscissae v`
hypothesis) and Step 2b (~120 LOC composition) but chose to defer:
- Step 2a requires propagating the new hypothesis upstream to
  `aux_515D_max_deviation_bound_tendsto_zero`,
  `aux_515D_componentwise_deviation_tendsto_zero`,
  `aux_515D_output_tendsto`, and `stable_consistent_isConvergent`.
- Risk of breaking §513 / §514 cascades is non-trivial (similar
  precedent: cycle 116 Phase 2's Frobenius propagation).
- Step 2b's 120 LOC is genuinely intricate (M-matrix construction +
  per-step chain + iterated-V invocation + geometric closed form).
- Strategy explicitly authorizes "+1 closed sub-helper" as valid.

Documented Priority 2's structure for cycle 121 in
`.prover-state/issues/aux_515D_iterated_V_bound.md` (Cycle 120 update
section) and `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md`
(Cycle 120 update section).

## Result

**SUCCESS — partial closure of §515D's outermost analytical layer.**

* New helper `aux_515D_iterated_V_bound` introduced and **fully proved**
  at `OpenMath/Chapter5/Section515.lean:1854` (no `sorry`, no `axiom`).
* `#print axioms`-equivalent verification via `lean_verify`:
  `aux_515D_iterated_V_bound` uses only `propext`, `Classical.choice`,
  `Quot.sound` — standard Lean axioms only.
* Build status: `lake env lean OpenMath/Chapter5/Section515.lean`
  succeeds with the same warning profile as cycle 119: pre-existing
  `unused variable hβ_nn` (line 1713) and pre-existing simp arg lint
  (line 1722), plus the single remaining `sorry` warning at line 1961
  (the `aux_515D_max_deviation_geometric_bound` body — narrowed in
  cycle 119, still open after cycle 120).
* Cycle 120's deliverable: structural advance — the iterated-V
  infrastructure is now available for cycle 121's
  `aux_515D_max_deviation_geometric_bound` body composition.

**Sorry-count delta**: 0 net (one helper added with full proof; the
existing geometric_bound sorry remains).

**`thm:515D` status**: still `partial`. Will become `formalized`
when cycle 121 closes `aux_515D_max_deviation_geometric_bound`.

## Faithfulness check

For the new helper introduced this cycle:

- **Entity**: `aux_515D_iterated_V_bound` (private helper, NOT a
  textbook theorem; supports `thm:515D`).
  - Textbook source: implicitly used in Butcher §515D's stability
    + consistency ⇒ convergence proof, where the iterated `V`-norm
    bound enters via the discrete-Grönwall argument. The textbook
    does not state this as a separate lemma — it is a standard
    consequence of `M.IsStable`'s power-boundedness.
  - Lean statement captures: a clean Mathlib-flavored bridge from
    operator-norm power-boundedness to the sup'-form bound on
    matrix-vector products. **same content** as Path A of
    `.prover-state/issues/aux_515D_iterated_V_bound.md`.
  - **No textbook divergence**: the helper is a Mathlib glue lemma,
    not a textbook restatement. The hypothesis `M.IsStable`'s data
    is consumed exactly as in `Section514.IsStable.powerBound`.
  - **Tautology check**: PASS. The conclusion (sup'-form vector
    bound) does NOT appear verbatim as a hypothesis; the hypothesis
    is the operator-norm-of-power bound `‖V^k‖ ≤ C`.
  - **Identity check**: PASS. The proof is ~70 LOC of genuine bridge
    work: entrywise Frobenius bound + row-sum + `Finset.sup'_le`.
    Not a single `exact h` re-export.
  - **Hypothesis strength check**: PASS. `hStab : ∃ C, 0 ≤ C ∧ ∀ k,
    ‖V^k‖ ≤ C` is exactly `M.IsStable`'s data
    (`Section514.IsStable.powerBound`'s output). Not strengthened.
    `[Nonempty (Fin r)]` is required for `Finset.sup'` to typecheck.
  - **Absent theorem check**: PASS. Lemma is fully introduced; not
    promised in a comment.

For the existing `aux_515D_max_deviation_geometric_bound` (NOT modified
this cycle):
- Signature unchanged from cycle 119.
- `_hc_nn : 0 ≤ M.glmAbscissae v` NOT yet added (deferred to cycle 121).
- The sorry at line 1961 remains (cycle 119's narrowing).

## Dead ends

1. **`Matrix.linfty_opNorm_mulVec` direct application** failed because
   our scope's default Matrix norm is Frobenius (via
   `open scoped Matrix.Norms.Frobenius`), not linfty op. The lemma's
   `‖A‖` resolves to the linfty op norm instance, not Frobenius.
   Section514.lean works around this by also opening
   `Matrix.Norms.Operator` — Section515 doesn't, by design (the
   surrounding M-matrix proofs need Frobenius).

2. **`Matrix.norm_entry_le_entrywise_sup_norm`** failed because it
   uses the *entrywise sup* norm instance (the default in
   `Mathlib.Analysis.Matrix.Normed`), not Frobenius. Type mismatch
   with `‖V^k‖_F` in our scope.

3. **`Matrix.frobenius_norm_def` direct rewrite** had a real-vs-nat
   exponent mismatch: the inner `^ 2` in the definition is
   `Real.rpow x (2 : ℝ)`, but our `S := ∑ ((V^k) a b)^2` parsed `^ 2`
   as `^ (2 : ℕ)`. Resolved via `Real.rpow_two` bridge.

4. **`sq_abs _` (unbound metavariable)**: Lean failed to infer the
   argument's `LinearOrder` type from context. Resolved by passing
   the explicit argument `sq_abs ((V ^ k) a b)`.

## Discovery

1. **Frobenius default in §515 has consequences**: the choice to open
   `Matrix.Norms.Frobenius` (made in cycle 100 for the M-matrix
   proofs at `aux_515D_construct_ell_U_phi_A`) makes the otherwise
   convenient `Matrix.linfty_opNorm_mulVec` lemma harder to invoke.
   For future cycles working with `M.IsStable`'s `‖V^k‖ ≤ C` bound,
   the entrywise route via `Matrix.frobenius_norm_def` is the
   preferred path. The `Real.rpow_two` bridge handles the
   real-vs-nat exponent mismatch for `sq_abs`.

2. **`abs_le_of_sq_le_sq` is the right tool** for converting squared
   inequalities to absolute-value inequalities in Mathlib (rather
   than `Real.sqrt_le_sqrt` + `Real.sqrt_sq` chains).

3. **Crude `r · C` constants suffice for §515D**: the geometric bound
   does NOT require tight constants. This unlocks simpler proof
   strategies that avoid Cauchy-Schwarz / `Real.sqrt` complications.

## Suggested next approach

**For cycle 121**: tackle the body composition of
`aux_515D_max_deviation_geometric_bound`. The infrastructure is now
fully resourced:

* `aux_515D_construct_ell_U_phi_A` (cycle 114): M-matrix construction
  for `ell_U`, `phi_A`. Requires `0 ≤ c` hypothesis.
* `localStepError_bound` (cycle 116 strengthened): per-step error
  bound, parameterized over `α`, `β`, with localized `M_bound` on
  `Set.uIcc xn1 (xn1 + h*c_j)`.
* `aux_515D_per_step_recurrence` (cycle 113): scalar geometric closed
  form `δ n ≤ (V_norm + α·h)^n · δ 0 + β·h² · Σ_{k<n} (V_norm + α·h)^k`.
* `aux_515D_iterated_V_bound` (cycle 120, this cycle): converts
  `∃ C, ‖V^k‖ ≤ C` into the sup'-form vector bound on `V^k *ᵥ x`.
* `aux_515D_one_add_pow_le_exp` (cycle 113): bridges `(1+c)^n ≤ exp(n·c)`.

**Decision points for cycle 121**:

(a) **`0 ≤ c` hypothesis propagation**: must decide whether to add
    `(_hc_nn : ∀ i, 0 ≤ M.glmAbscissae v i)` to the entire chain
    `aux_515D_max_deviation_geometric_bound` →
    `aux_515D_max_deviation_bound_tendsto_zero` →
    `aux_515D_componentwise_deviation_tendsto_zero` →
    `aux_515D_output_tendsto` →
    `stable_consistent_isConvergent`.
    Risk: §513 / §514 cascade integrity (per Backup B3 of cycle
    120 strategy). Recommended: try locally first, only propagate
    if §513/§514 don't break.

(b) **Composition split**: if the 120 LOC composition proves too
    intricate in one go, split into Backup B2 of cycle 120 strategy:
    introduce `aux_515D_per_step_chain` as a sub-helper that
    encapsulates the per-step recurrence chain, sorry'd, then
    submit to Aristotle.

(c) **Aristotle Job 4 was cancelled** — could be re-submitted for
    `aux_515D_max_deviation_geometric_bound`'s body composition (with
    abstract axioms for the helpers including `aux_515D_iterated_V_bound`).
    Likely tractable for Aristotle since the geometric helper is
    self-contained and the helpers are abstract.

(d) **End-of-cycle status of Aristotle Jobs 2 and 3**: Job 2 (cycle
    117 vector signature) and Job 3 (cycle 118 narrowed scalar)
    were both `IN_PROGRESS` at the end of cycle 120. Cycle 121 must
    re-poll and decide whether to leave / cancel / incorporate.
    NOTE: cycle 119's narrowing has already replaced Job 3's target
    body (cycle 118 helper is closed), so Job 3's results may be
    redundant. Job 2's results (cycle 117 vector form) might still
    be useful if the geometric_bound body composition stalls.
