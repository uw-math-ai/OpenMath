# Cycle 103 strategy — open `lem:515B` with sorry-first scaffold

## Status (start of cycle 103)

* `lem:515A` is **complete** as of cycle 102 — both inequalities
  (515a) `localStageError_bound_a` and (515b) `localStageError_bound_b`
  are sorry-free in `OpenMath/Chapter5/Section515.lean` and
  axiom-clean (`[propext, Classical.choice, Quot.sound]`).
* §515 has **0 sorries** at HEAD = `a78292a`.
* Aristotle: no pending submissions.

## This cycle's target — `lem:515B`

**Entity ID**: `lem:515B` ("Stability and Consistency Imply
Convergence (515B)", Butcher §515, p. 414).

**Path**: `extraction/formalization_data/entities/lem_515B.json`
(read this FIRST before writing any Lean).

**File**: continue in `OpenMath/Chapter5/Section515.lean` (do NOT
create a new file — keep all of §515 in one place).

### Textbook statement (verbatim from `entities/lem_515B.json`)

> Under the conditions of Lemma 515A, the exact solution and the
> computed solution in a step are related by
>
>   `ỹ_i^{[n]} − y_i^{[n]} = Σ_{j=1}^r V_{ij}(ỹ_j^{[n−1]} − y_j^{[n−1]}) + K_i^{[n]}`,
>
> where
>
>   `‖K^{[n]}‖ ≤ h α max_{i=1}^r |ỹ_i^{[n−1]} − y_i^{[n−1]}| + β h²`,
>
> with α and β:
>
>   `α = L max_{i=1}^s |ℓ_i|`,
>   `β = L² M max_{i=1}^s [½|u_i| + |v_i| + Σ_j |b_{ij} c_j| + h₀ L Σ_j |b_{ij}| ϕ_j]`,
>
> where ℓ solves
>   `Σ_{j=1}^s (δ_{ij} − h₀ L |a_{ij}|) ℓ_j = Σ_{j=1}^s |U_{ij}|`,
> and ϕ is as in Lemma 515A:
>   `Σ_{j=1}^s (δ_{ij} − h₀ L |a_{ij}|) ϕ_j = ½ c_i² + Σ_j |a_{ij} c_j|`.

**IMPORTANT — two different "ell" vectors.** The textbook uses
**two distinct vectors**, both unique solutions to
`(I − h₀L|A|) x = rhs` with different RHS:

* `ℓ_U` (for `α`): RHS is `Σ_k |U_{·k}|`, i.e. row-sums of `|U|`.
* `ϕ_A` (for `β`, identified with `lem:515A`'s `ϕ`): RHS is
  `½c² + |A||c|`.

The line "where ϕ is as in Lemma 515A" in the JSON refers ONLY
to the second vector, not the first. Encode them as TWO separate
parameters.

We do NOT have matrix-invertibility / Banach contraction
infrastructure for `(I − h₀L|A|)` yet; we will **continue cycle
100/102's pattern** of taking these vectors as **parameters with
linear-system side conditions**, NOT constructing them. This
avoids adding multi-cycle linear-algebra infrastructure inside
this cycle.

## Approach — sorry-first scaffold + Aristotle batch

### Priority 1 — read the data (5 min)

1. `cat extraction/formalization_data/entities/lem_515B.json` — confirm
   the statement above. If you find a discrepancy with the strategy's
   reading (especially around the two-ell question), file a short
   note in `.prover-state/issues/lem_515B_two_ells.md` documenting
   which reading the Lean adopts and why. Do NOT silently change
   the strategy.

### Priority 2 — sorry-first scaffold of `lem:515B` (~150 LOC, ≤45 min)

Add to `OpenMath/Chapter5/Section515.lean`, at the bottom of the
existing `namespace OpenMath.Chapter5.Section510` block (after
`localStageError_bound_b` ends ~line 829).

The signature must include parameters representing **both** the
previous-step error and the cycle-102 hypotheses. Recommended shape:

```lean
/-- **Butcher Lemma 515B** — local error propagation across one
GLM step.

`α`, `β`, and the auxiliary vectors `ell_U`, `phi_A` are
abstracted as parameters with their defining equations.
A future cycle (once `(I − h₀L|A|)`-inversion infrastructure is
in place) will construct `ell_U` and `phi_A` and discharge the
side conditions. -/
theorem GeneralLinearMethod.localStepError_bound {s r : ℕ}
    (M : GeneralLinearMethod s r)
    -- numerical parameters
    {h h₀ L M_bound : ℝ}
    (hh_nonneg : 0 ≤ h) (hh_le : h ≤ h₀) (h₀_pos : 0 < h₀)
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    -- f and the exact solution yex
    (f : ℝ → ℝ) (hf_lip : LipschitzWith L.toNNReal f)
    (yex : ℝ → ℝ)
    (hy_C1 : ContDiff ℝ 1 yex)
    (hy_ode : ∀ t, deriv yex t = f (yex t))
    (hy_M : ∀ t, |yex t| ≤ M_bound)
    (hy'_LM : ∀ t, |deriv yex t| ≤ L * M_bound)
    (xn1 : ℝ)
    -- consistency vectors
    (u v : Fin r → ℝ)
    (hVu : M.V *ᵥ u = u) (hUu : M.U *ᵥ u = (fun _ => 1))
    (hCons : M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v)
    (c : Fin s → ℝ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (hc_def : c = M.glmAbscissae v)
    -- Aux vectors (parameters with linear-system side conditions)
    (ell_U phi_A : Fin s → ℝ)
    (hell_U_nonneg : ∀ i, 0 ≤ ell_U i)
    (hphi_A_nonneg : ∀ i, 0 ≤ phi_A i)
    (hellU_eq : ∀ i,
      ell_U i - h₀ * L * (∑ j, |M.A i j| * ell_U j)
        = ∑ j, |M.U i j|)
    (hphiA_eq : ∀ i,
      phi_A i - h₀ * L * (∑ j, |M.A i j| * phi_A j)
        = (1/2) * (c i)^2 + ∑ j, |M.A i j * c j|)
    -- Previous-step error δ_k = ỹ_k^{[n−1]} − y_k^{[n−1]}, plus the two
    -- previous-step vectors so the input on the y-side is hy_prev (not
    -- the textbook proxy `u_j y(xn1) + v_j h y'(xn1)`).
    (yt_prev y_prev : Fin r → ℝ)
    (δ : Fin r → ℝ)
    (hδ_def : ∀ k, δ k = yt_prev k - y_prev k)
    -- Computed stage Y satisfies the implicit GLM stage equation against y_prev.
    (Y : Fin s → ℝ)
    (hY_stage : ∀ i,
      Y i = h * (∑ j, M.A i j * f (Y j))
            + ∑ j, M.U i j * y_prev j) :
    ∃ K : Fin r → ℝ,
      -- (1) the propagation identity
      (∀ i,
        (u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
          - (∑ j, M.V i j * y_prev j)
          - h * (∑ j, M.B i j * f (Y j))
          = (∑ j, M.V i j * δ j) + K i)
      -- (2) the K bound
    ∧ (∀ i,
        |K i|
        ≤ h * (L * (Finset.univ.sup'
                ⟨Finset.univ_nonempty_of_pos s_pos⟩
                (fun k : Fin s => ell_U k)))
              * (Finset.univ.sup'
                ⟨Finset.univ_nonempty_of_pos r_pos⟩
                (fun k : Fin r => |δ k|))
          + (L^2 * M_bound *
             Finset.univ.sup' ⟨Finset.univ_nonempty_of_pos s_pos⟩
               (fun k : Fin s =>
                 (1/2) * |u k| + |v k|
                 + (∑ j, |M.B k j * c j|)
                 + h₀ * L * (∑ j, |M.B k j| * phi_A j))) * h^2) := by
  sorry
```

**Practical pitfalls in stating this**:

1. `Finset.univ.sup'` requires a non-emptiness witness. Either:
   - Add `(s_pos : 0 < s)` and `(r_pos : 0 < r)` as hypotheses
     (textbook-faithful — methods with 0 stages or 0 inputs don't
     exist), and pull witness via `Finset.univ_nonempty_of_pos`
     (verify name with `lean_local_search`).
   - Or use `Finset.sup` / `iSup` over `[CompleteLattice ℝ]` (no —
     ℝ isn't `CompleteLattice`).
   - Or embed the entire sup'-bound argument in a proxy `(α β : ℝ)`
     parameters with side conditions
     `hα_eq : α = L * max ...` and `hβ_eq : β = L² M · max ...`
     similarly to how cycles 100/102 handled `c`. **This is the
     recommended path** — it sidesteps the sup'-non-emptiness
     plumbing entirely. Then the bound is plain
     `|K i| ≤ h * α * δ_max + β * h²` with `δ_max` itself a
     parameter satisfying `(hδ_max : ∀ k, |δ k| ≤ δ_max)`.

2. The side-condition `hellU_eq` uses `Σ_j |M.A i j| * ell_U j` for
   the matrix-vector product `(|A| · ell_U) i`. Don't confuse with
   `Matrix.mulVec` — write the explicit Finset.sum to keep
   `linear_combination`/`ring` friendly.

3. The textbook's `‖K^{[n]}‖` is the **vector ∞-norm**, but in
   Butcher's notation `‖K^{[n]}‖ = max_i |K_i^{[n]}|`. Our
   formulation states it pointwise as `∀ i, |K i| ≤ ...`, which
   is equivalent (and stronger when `δ_max` is the actual `max|δ|`).
   This is faithful — document.

**Recommended FINAL signature shape (with α, β proxies)**:

```lean
theorem GeneralLinearMethod.localStepError_bound {s r : ℕ}
    (s_pos : 0 < s) (r_pos : 0 < r)
    (M : GeneralLinearMethod s r)
    {h h₀ L M_bound α β δ_max : ℝ}
    -- ... (same numeric/f/yex hypotheses as above) ...
    -- ... (same consistency hypotheses) ...
    -- Aux vectors and proxies
    (ell_U phi_A : Fin s → ℝ)
    (hell_U_nonneg : ∀ i, 0 ≤ ell_U i)
    (hphi_A_nonneg : ∀ i, 0 ≤ phi_A i)
    (hellU_eq : ∀ i, ell_U i - h₀ * L * (∑ j, |M.A i j| * ell_U j)
                  = ∑ j, |M.U i j|)
    (hphiA_eq : ∀ i, phi_A i - h₀ * L * (∑ j, |M.A i j| * phi_A j)
                  = (1/2) * (c i)^2 + ∑ j, |M.A i j * c j|)
    (hα_def : ∀ i, L * ell_U i ≤ α)
    (hβ_def : ∀ i, L^2 * M_bound *
                ((1/2) * |u i| + |v i|
                 + (∑ j, |M.B i j * c j|)
                 + h₀ * L * (∑ j, |M.B i j| * phi_A j)) ≤ β)
    -- Previous step
    (yt_prev y_prev δ : Fin r → ℝ)
    (hδ_def : ∀ k, δ k = yt_prev k - y_prev k)
    (hδ_max : ∀ k, |δ k| ≤ δ_max)
    (hδ_max_nonneg : 0 ≤ δ_max)
    -- Stage equation
    (Y : Fin s → ℝ)
    (hY_stage : ∀ i, Y i = h * (∑ j, M.A i j * f (Y j))
                          + ∑ j, M.U i j * y_prev j) :
    ∃ K : Fin r → ℝ,
      (∀ i, …propagation identity…)
      ∧ (∀ i, |K i| ≤ h * α * δ_max + β * h^2) := by
  sorry
```

**Compile check after writing**: `lake env lean OpenMath/Chapter5/Section515.lean`
must succeed. Expected output: at most 1 `declaration uses sorry`
warning (the new `localStepError_bound`). NO existing sorries
should appear (file currently has 0).

### Priority 3 — decompose into 4 named sub-lemmas (~80 LOC, ≤30 min)

The textbook proof structure:

1. **(515c invocation)**: from cycle 102's `localStageError_bound_b`,
   `|y_i^{[n]} − h Σ b_{ij} f(Ŷ_j) − Σ V_{ij} y_j^{[n−1]}|
       ≤ h²L²M(½|u_i|+|v_i|+Σ|b_{ij}c_j|)`. Here `Ŷ_j = yex(xn1+h c_j)`.

2. **(Lipschitz bridge → 515d)**: bound
   `h Σ |b_{ij}| |f(Ŷ_j) − f(Y_j)| ≤ hL Σ|b_{ij}| |Ŷ_j − Y_j|`.

3. **(η stage estimate)**: from the stage equation
   `|Ỹ_j − Y_j − Σ U_{jk} δ_k| ≤ hL Σ|a_{jk}| |Ỹ_k − Y_k|`,
   conclude `|Ỹ_j − Y_j| ≤ ell_U_j · max|δ_k|` (uses `hellU_eq`
   plus `h ≤ h₀`).

4. **(Composition)**: combine (1)+(2)+(3) into the `K` bound.

Sub-lemmas to scaffold (each as `private theorem aux_515B_*` with
`sorry`):

* `aux_515B_residual_decomposition`: the algebraic identity
  separating `Σ V·δ` from `K_i`. **Closed manually this cycle**
  (no sorry).
* `aux_515B_lipschitz_bridge`: Lipschitz application to
  `f(Ŷ_j) − f(Y_j)`. → Submit to Aristotle.
* `aux_515B_eta_contraction`: the `(I − h₀L|A|)` inversion.
  Hypothesis: `∀ j, |Ỹ_j − Y_j − Σ U_{jk} δ_k| ≤ hL Σ|a_{jk}| |Ỹ_k − Y_k|`.
  Conclusion: `∀ j, |Ỹ_j − Y_j| ≤ ell_U_j · max|δ_k|`. → Submit to
  Aristotle (this is the hardest piece).
* `aux_515B_main_combination`: final composition (1)+(2)+(3).
  → Submit to Aristotle.

If `aux_515B_residual_decomposition` is more than ~15 lines,
decompose it further. The expected proof is **purely algebraic**:
it should close via `ring` after introducing
`δ k := yt_prev k - y_prev k` and rewriting
`Σ M.V i j * y_prev j = Σ M.V i j * yt_prev j − Σ M.V i j * δ j`.

### Priority 4 — submit ~5 jobs to Aristotle (~10 min)

CLAUDE.md directs you to submit ~5 jobs and sleep 30 minutes.

Stage submissions in
`.prover-state/aristotle_submissions/cycle_103/` matching the
cycle 100/101 layout (`decomposition_attempt.lean` +
`sub_lemmas.lean`). Submit:

1. `aux_515B_lipschitz_bridge` (cheap).
2. `aux_515B_eta_contraction` (hardest).
3. `aux_515B_main_combination` (medium).
4. The full `localStepError_bound` itself (long shot, but free
   compute).
5. A bonus: a stronger version of `aux_515B_lipschitz_bridge`
   that combines the Lipschitz step with the cycle-102
   `aux_T3'_bound` pattern (composition of pointwise Lipschitz
   estimates).

Use `mcp__aristotle__submit_directory` with the
`cycle_103/` directory. After submitting, do **not** poll. Sleep
~30 min OR proceed with manual proof of
`aux_515B_residual_decomposition` while Aristotle runs. Check
Aristotle ONCE near end of cycle.

### Priority 5 — manually close `aux_515B_residual_decomposition` (≤30 min)

Expected ~10–15 lines. The proof is purely algebraic:

```lean
private theorem aux_515B_residual_decomposition {s r : ℕ}
    (M : GeneralLinearMethod s r)
    {h : ℝ}
    (yt_prev y_prev δ : Fin r → ℝ)
    (hδ_def : ∀ k, δ k = yt_prev k - y_prev k)
    (Y : Fin s → ℝ)
    (f : ℝ → ℝ)
    (yex : ℝ → ℝ)
    (xn1 : ℝ)
    (u v : Fin r → ℝ)
    (i : Fin r) :
    (u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
      - (∑ j, M.V i j * y_prev j)
      - h * (∑ j, M.B i j * f (Y j))
    = (∑ j, M.V i j * δ j)
      + ((u i * yex (xn1 + h) + v i * h * deriv yex (xn1 + h))
         - (∑ j, M.V i j * yt_prev j)
         - h * (∑ j, M.B i j * f (Y j))) := by
  -- Σ V·y_prev = Σ V·yt_prev - Σ V·δ.
  have hsplit : ∑ j, M.V i j * y_prev j
              = (∑ j, M.V i j * yt_prev j) - (∑ j, M.V i j * δ j) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hδ_def j]; ring
  rw [hsplit]; ring
```

Test with `lean_multi_attempt` or compile incrementally — if `ring`
chokes on the trailing expression, try `linarith` or rewrite the
subtraction with `sub_sub_eq_add_sub`.

### Priority 6 — task results, faithfulness, commit

Write `.prover-state/task_results/cycle_103.md` documenting:

* Sorry count: 0 → N (count after this cycle).
* What sub-lemmas were stubbed; which closed manually; which
  submitted to Aristotle.
* Faithfulness: explicitly note the textbook deviation around the
  `α, β, δ_max` proxy parameters (vs. textbook `Finset.sup'`-style
  max-of-vector). The proxies are weaker (any upper bound works,
  not just the tight max), but the conclusion is preserved.
* Faithfulness: carry through `_hc_nonneg` and document.
* Faithfulness: the `r_pos` and `s_pos` hypotheses if used.
* Aristotle submission ID and timestamp (NOT polled).

Then commit. Format the message as:
`Cycle 103 — open lem:515B with sorry-first scaffold (NN sub-lemmas, MM closed)`.

Verify the commit landed:

```bash
git log -1 --format='%H %s'
git diff HEAD~1 HEAD --stat
git rev-parse HEAD
git rev-parse origin/Main/Experiments
```

If `HEAD` and `origin/Main/Experiments` disagree, push. Cycle 071's
"staged but not committed" pattern must NOT recur.

## What NOT to do this cycle

* Do **NOT** attempt to construct `ell_U` or `phi_A` as outputs of
  Banach contraction or `(I − h₀L|A|)` inversion this cycle. That
  is multi-cycle infrastructure. Take them as **parameters** with
  linear-system side conditions, mirroring how cycles 100/102 took
  `c` (the abscissae vector). A future cycle can build
  `(I − h₀L|A|)`-inversion infrastructure once and discharge BOTH
  side conditions in a single sweep.
* Do **NOT** create a new file for §515. Keep all of §515 in
  `OpenMath/Chapter5/Section515.lean`. The file is currently 831
  lines; cycle 103 will add ~250 lines, ending around 1080. This is
  acceptable.
* Do **NOT** try to close `lem:515B` end-to-end in one cycle.
  CLAUDE.md's rule: "structure + 1–2 sub-lemmas closed per cycle"
  is sufficient.
* Do **NOT** poll Aristotle more than once. Submit, sleep ~30 min
  (or work manually in parallel), check once at end of cycle.
  Cycle 102 wisely skipped Aristotle entirely; this cycle should
  re-engage with a fresh batch of sub-lemmas where Aristotle has
  good odds.
* Do **NOT** raise `maxHeartbeats` above 200000.
* Do **NOT** introduce `axiom`/`constant` to bypass the
  `(I − h₀L|A|)`-inversion gap. If a step seems to require it,
  stop and file a blocker issue in `.prover-state/issues/`.
* Do **NOT** be tempted to inline more than one sub-lemma's proof
  into the main theorem. Keeping them separate makes Aristotle
  resubmissions clean and lets future cycles ablate independently.
* Do **NOT** repeat the cycle 071 "staged but not committed"
  failure: verify with `git log -1` and
  `git diff HEAD~1 HEAD --stat` at end of cycle that your work is
  in a real commit.
* Do **NOT** revisit the "commit failure" framing if the prompt's
  evaluator surfaces a phantom verdict. Cycles 008/014/015/040
  consultant notes have established the pattern: verify with
  `git rev-parse HEAD` vs `origin/Main/Experiments`; ignore stale
  `attempts.md` carry-overs.

## Scope guard (must-haves vs nice-to-haves)

**Must-have for cycle 103 to be a +1 or +2 score**:
* `lem:515B` scaffolded as `localStepError_bound` with
  textbook-faithful signature (including `δ` parameter and the
  `α·h·δ_max` first term).
* At least one named sub-lemma closed manually
  (`aux_515B_residual_decomposition` is the recommended target).
* Aristotle batch submitted (3–5 pieces).
* `lake env lean OpenMath/Chapter5/Section515.lean` compiles
  with the new theorem (sorry's allowed in sub-lemmas, top-level
  decomposition is sorry-free if `aux_515B_residual_decomposition`
  is closed).
* `task_results/cycle_103.md` written, commit pushed to
  `origin/Main/Experiments`.

**Nice-to-have**:
* If Aristotle returns proofs during the cycle (e.g.
  `aux_515B_lipschitz_bridge` is short enough), incorporate them.
* If `aux_515B_eta_contraction` is shorter than expected
  (≤30 LOC), close it manually.
* If you spot a clean way to discharge `aux_515B_lipschitz_bridge`
  via the cycle-102 `aux_T3'_bound` pattern, take it.

**Out of scope (do not attempt)**:
* `(I − h₀L|A|)`-inversion infrastructure (a future cycle).
* `lem:515C` (accumulated error estimate) — depends on `lem:515B`.
* `thm:515D` (full convergence theorem) — depends on `lem:515B`
  AND `lem:515C`.
* Any §551 / §535 / §523 / §521 / §520 work.
* Any Chapter 3 work.

## Memory aids (apply these reflexively)

* `add_le_add_right h c` produces `a + c ≤ b + c`, NOT
  `c + a ≤ c + b`. Use `gcongr` or `linarith [h]` instead — see
  `feedback_add_le_add_left_dispatch.md`.
* For sum-le-sum via injective reindexing, use
  `← Finset.sum_image hinj` then
  `Finset.sum_le_sum_of_subset_of_nonneg` — see
  `feedback_finset_sum_le_sum_nbij_nonexistent.md`.
* For triangle inequality on sums, the Mathlib name is
  `abs_add_le`, NOT `abs_add` (cycle 102 finding).
* For monotone calc cascades over absolute values, prefer
  `gcongr; exact <key_lemma>` over `add_le_add_right` /
  `mul_le_mul_of_nonneg_left` to avoid unification ambiguity
  (cycle 102 finding).
* `set X := ...` followed by `linear_combination` works
  cleanly: `ring` treats the `set` abbreviation as opaque
  (cycle 102 finding).
* When specializing `aux_T3_bound` at `c_i := 1`, plain `simpa`
  collapses `(1/2) * h^2 * L^2 * M_bound * 1^2` →
  `(1/2) * h^2 * L^2 * M_bound` (cycle 102 finding).
* `Finset.sum_sub_distrib` swaps `∑(a − b)` ↔ `(∑a) − (∑b)` and
  is the right tool for splitting `Σ V·y_prev` into `Σ V·ỹ_prev − Σ V·δ`.

## Cross-references

* `extraction/formalization_data/entities/lem_515B.json` — textbook
  statement. Read this first.
* `OpenMath/Chapter5/Section515.lean:516–829` — cycle 100/101/102's
  `localStageError_bound_a` and `localStageError_bound_b`. The
  proof of `lem:515B` will invoke `localStageError_bound_b` directly.
* `.prover-state/task_results/cycle_102.md` — most recent cycle's
  record, with the suggestion to scaffold `lem:515B`.
* `.prover-state/issues/u_prime_equals_u_bridge.md` — RESOLVED in
  cycle 099; included for §515 context only, no impact on cycle 103.
* `.prover-state/issues/glm_isconvergent_strengthened.md` — context
  for `def:512A`'s strengthening; matters for `thm:515D` later but
  NOT this cycle.
