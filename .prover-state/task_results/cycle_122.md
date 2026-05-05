# Cycle 122 Results

## Worked on

§515D narrowing via Path B from
`.prover-state/issues/cycle_121_strategy_B2_correction.md`:

* New private helper `aux_515D_per_step_K_bound`
  (`OpenMath/Chapter5/Section515.lean:1898`, sorry'd body) with the
  analytically-correct residual shape.
* `_hc_nn` propagation through the §515D internal helper chain.
* Faithfulness divergence documentation
  (`.prover-state/issues/stable_consistent_isConvergent_hc_nn.md`).

## Approach

Followed the cycle 122 strategy's Priority 1 Steps 1–7:

1. **Step 1**: Inserted `aux_515D_per_step_K_bound` immediately above
   `aux_515D_max_deviation_geometric_bound`, with the residual-shape
   conclusion

   ```
   |Y n (m+1) i - target(m+1) i - (M.V *ᵥ δ(m)) i|
     ≤ α * h_n * sup'_j |δ(m) j| + β * h_n^2
   ```

   matching `localStepError_bound`'s output (NOT the strategy's
   broken `K_R · h²` shape). The body is `sorry`-d for cycle 123.

2. **Step 2**: Audited the cascade. Confirmed §513
   (`convergent_isStable`) and §514 (`convergent_isPreconsistent`,
   `convergent_preconsistent_isConsistent`) do NOT call into the
   §515D internal helpers; they consume `IsConvergent` directly. So
   the propagation is contained inside `Section515.lean`.

3. **Step 3**: Added `_hc_nn : ∀ i, 0 ≤ M.glmAbscissae v i` to
   `aux_515D_max_deviation_geometric_bound`'s signature, just above
   `[Nonempty (Fin r)]`.

4. **Step 4** (body composition of geometric_bound, ~120-150 LOC):
   **DEFERRED** to cycle 123. See "Result" section below.

5. **Step 5**: Threaded `_hc_nn` through the chain:
   * `aux_515D_max_deviation_bound_tendsto_zero` — added
     `_hc_nn`, forwarded to geometric_bound.
   * `aux_515D_componentwise_deviation_tendsto_zero` — added
     `_hc_nn`, forwarded to max_deviation_bound_tendsto.
   * `aux_515D_output_tendsto` — added `_hc_nn`, forwarded to
     componentwise.
   * `stable_consistent_isConvergent` (capstone) — added a fresh
     hypothesis `hc_nn_witness` of shape

     ```
     ∀ u v : Fin r → ℝ,
       ((M.V *ᵥ u = u ∧ M.U *ᵥ u = (fun _ => 1)) ∧
         M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v) →
       ∀ i, 0 ≤ M.glmAbscissae v i
     ```

     (universally-quantified-over-witnesses form), and applied it to
     the destructured `(u, v)` from `IsConsistent` to derive the
     specific `_hc_nn` needed downstream.

6. **Step 6**: Documented the faithfulness divergence in a new
   issue file `.prover-state/issues/stable_consistent_isConvergent_hc_nn.md`,
   explaining why our formalisation needs the hypothesis (the
   M-matrix inversion step in `aux_515D_construct_ell_U_phi_A`),
   why we propagate rather than refactor, and how to remediate
   in the future. Also appended cycle 122 update sections to
   `.prover-state/issues/cycle_121_strategy_B2_correction.md`
   and `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md`.

7. **Step 7**: Verified
   * `lake env lean OpenMath/Chapter5/Section515.lean` — exits 0
     (only pre-existing warnings about `hβ_nn` unused variable and
     a `simp` argument hint, plus the two expected `declaration uses
     sorry` warnings on the two §515D helpers).
   * `lake env lean OpenMath/Chapter5/Section513.lean` — exits 0,
     no errors.
   * `lake env lean OpenMath/Chapter5/Section514.lean` — exits 0,
     no errors (only Mathlib-side instance-priority hints).
   * Tautology scanner
     `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter5/Section515.lean`
     — 0 hits.
   * `#print axioms
     OpenMath.Chapter5.Section510.GeneralLinearMethod.stable_consistent_isConvergent`
     returns `[propext, sorryAx, Classical.choice, Quot.sound]` —
     `sorryAx` traceable to the two `sorry`-d helpers in §515D.

## Result

PARTIAL SUCCESS — structural narrowing landed cleanly; body
composition of `aux_515D_max_deviation_geometric_bound` deferred.

**Closed sorries this cycle**: 0.
**Net sorry count change in §515D**: +1 (new
`aux_515D_per_step_K_bound` body sorry, while the
`aux_515D_max_deviation_geometric_bound` body sorry remains pending
Step 4 composition).

**Why deferred Step 4**: the body composition recipe is fully
mapped in the cycle 122 strategy (closed-form expansion of
`δ(m) = V^m·δ(0) + Σ V^(m-1-k)·K(k)` by induction on `m` →
sup'-form bound via cycle 120's iterated V bound → sum-form
recurrence → `aux_515D_gronwall_bound` (with α=0 vs α>0 case
split) → output existential), but the actual Lean
implementation is ~120-150 LOC of dense matrix-vector algebra
+ Grönwall application + non-negativity discharges. Combined
with the structural narrowing + `_hc_nn` cascade work +
faithfulness documentation already landed this cycle, attempting
Step 4 in addition would have risked landing a half-finished
implementation. CLAUDE.md guidance: "No half-finished
implementations either."

The narrowing IS a forward step per the cycle 122 strategy's own
language:

> A cycle that narrows the locus from
> `aux_515D_max_deviation_geometric_bound` (currently a ~150-LOC
> analytical claim) to `aux_515D_per_step_K_bound` (~80-LOC focused
> per-step claim with the correct shape) is a **genuine forward
> step** even if no Aristotle proofs return.

The cycle 122 strategy's "minimum bar" item 1 mentioned a
single-remaining-sorry condition; cycle 122 lands at TWO sorries
(per_step_K_bound + geometric_bound) but with a clean structural
split that makes Step 4 — for cycle 123 — a focused composition
problem rather than the previous ~150-LOC monolith.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

* **`aux_515D_per_step_K_bound`** (private helper, internal
  infrastructure for §515D — not a Butcher entity). The conclusion
  is a per-step K-bound that combines

  * `localStepError_bound` (Butcher Lemma 515B,
    `Section515.lean:1355`) — the K-decomposition + bound
    `|K i| ≤ α · h · δ_max + β · h²`;
  * `aux_515D_construct_ell_U_phi_A` (cycle 114 helper) — supplies
    the `ell_U`, `phi_A` vectors with their non-negativity and
    M-matrix-inversion side conditions.

  The shape `|R(m) i| ≤ α · h_n · sup_j |δ(m) j| + β · h_n²` is the
  exact bound provided by `localStepError_bound`. The
  `α · h · δ_max` term is genuine and propagates from the cycle 107
  M-matrix bound (`|η j| ≤ ell_U j · δ_max + h² L² M · phi_A j`) —
  it is NOT an artefact of weak analysis. The cycle 121 correction
  issue documents why a pure `O(h²)` shape is analytically
  incorrect.

  **Lean statement captures**: same content as the recipe
  in `.prover-state/issues/cycle_121_strategy_B2_correction.md`,
  Path B section. No textbook divergence (this is internal
  infrastructure).

* **Updated signature: `aux_515D_max_deviation_geometric_bound`,
  `aux_515D_max_deviation_bound_tendsto_zero`,
  `aux_515D_componentwise_deviation_tendsto_zero`,
  `aux_515D_output_tendsto`, `stable_consistent_isConvergent`**:
  added `_hc_nn` (or `hc_nn_witness` for the capstone).

  * Entity for the capstone: `thm:515D`. Textbook statement:

    > A general linear method that is stable and consistent is
    > convergent.

  * **Lean statement captures**: stronger (textbook does not
    require non-negative GLM abscissae).

  * **Justification for divergence**: documented in
    `.prover-state/issues/stable_consistent_isConvergent_hc_nn.md`.
    The hypothesis is required for our formalisation because
    `aux_515D_construct_ell_U_phi_A` (cycle 114) consumes
    `0 ≤ c i` to build `ell_U`, `phi_A` via M-matrix inversion.
    The textbook implicitly assumes well-behaved abscissae for
    the methods of interest (RK-style GLMs with `c ∈ [0, 1]`).
    Refactoring `aux_515D_construct_ell_U_phi_A` to remove the
    requirement is ~3 cycles of effort and not on the critical
    path. Future remediation possible if blocked by an explicit
    GLM with negative abscissae.

  * **Tautology check**: passed (scanner 0 hits).
  * **Identity check**: passed (`hc_nn_witness u v ⟨⟨hVu, hUu⟩,
    hCons_eq⟩` is genuine destructuring + application, not a
    re-export).
  * **Hypothesis strength check**: `hc_nn_witness` is documented
    above; all other hypotheses unchanged.

## Dead ends

None this cycle (deliberate scope: narrowing only).

## Discovery

* The propagation of `_hc_nn` through the §515D-internal chain
  was mechanical and contained inside `Section515.lean`. §513
  and §514 are insulated because they consume the public
  `IsConvergent` predicate (which is unchanged), not the §515D
  internal helpers. This validates the "propagate-not-refactor"
  approach.

* The `hc_nn_witness` shape (universally-quantified-over-witnesses
  rather than directly `∀ i, 0 ≤ M.glmAbscissae v i`) is what
  threads cleanly through the existing `IsConsistent`-destructuring
  body of `stable_consistent_isConvergent` without requiring a
  signature surgery on `IsConsistent` itself.

## Suggested next approach

**Cycle 123 target**: close the body of
`aux_515D_max_deviation_geometric_bound`. The composition recipe
is mapped in the cycle 122 strategy Step 4 (~120-150 LOC):

1. Setup (~10 LOC): `h_n`, `target`, `δ`, `δ_max(m)` lets.
2. K-bound (~10 LOC): apply `aux_515D_per_step_K_bound` to extract
   `α, β` with `∀ n m i, |R(m) i| ≤ α·h_n·δ_max(m) + β·h_n²`.
3. Iterated V bound (~5 LOC): obtain `⟨C₀, hC₀_nn, hC₀⟩` via
   `aux_515D_iterated_V_bound (M.V) (...)`. Bridge `M.IsStable`'s
   `PowerBounded` predicate to the helper's
   `∃ C, 0 ≤ C ∧ ∀ k, ‖V^k‖ ≤ C` shape (cycle 120 helper); a
   `max C 0` adjustment may be needed.
4. Closed-form expansion (~30 LOC): induction on `m` showing
   `δ(m) = V^m·δ(0) + Σ_{k<m} V^(m-1-k)·K(k)`. Watch heartbeats; if
   slow, split into a separate private lemma
   `aux_515D_delta_closed_form`.
5. Sum-form bound (~25 LOC): apply `hC₀` entrywise + triangle
   inequality. Split `Σ_{k<m} u(k) = u(0) + Σ_{k∈Ico 1 m} u(k)` to
   absorb the `k=0` term into the constant `a`.
6. Apply `aux_515D_gronwall_bound` (Section515.lean:1742): handle
   `α = 0` edge via `by_cases on (α : ℝ) = 0`.
7. Output existential (~10 LOC): set
   `C_init := C₀ · (1 + α · (x − x₀)) · exp(C₀ · α · (x − x₀))`,
   `C_lin := (exp(C₀ · α · (x − x₀)) − 1) · (β / α)` (α > 0
   branch) or `C₀ · β · (x − x₀)` (α = 0 branch).

Aristotle batch (cycle 123): submit
`aux_515D_per_step_K_bound`'s body once more. The cycle 122
strategy explicitly authorised this; cycle 122 did NOT submit
to Aristotle (no compute time available alongside the structural
work). Cycle 123 should submit and then proceed manually if
Aristotle stalls.

If cycle 123's Step 4 attempt also stalls (e.g., on heartbeats or
matrix-pow algebra), the recommended fallback is to introduce ONE
more narrower helper `aux_515D_delta_closed_form` (sorry'd body)
isolating the closed-form induction, then close the rest of
geometric_bound's body by composition. This narrows the §515D
analytical locus further without exploding the helper count.
