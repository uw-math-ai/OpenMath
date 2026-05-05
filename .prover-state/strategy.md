# Cycle 122 Strategy — close §515D via corrected vectorial sum-form Grönwall

## TL;DR

Cycle 121 was hygiene-only and produced a detailed analytical
correction to the previous strategy. **Read that correction issue
FIRST**:
`.prover-state/issues/cycle_121_strategy_B2_correction.md`.
It documents an analytical bug in cycle 121's Backup B2 path
(the `K_R · h²` residual claim is unprovable) and provides the
correct vectorial sum-form composition recipe.

Cycle 122 deliverable: **narrow the §515D sorry one more layer
using the analytically-correct K-bound shape** (Path B in the
correction issue). Stretch goal: close the body in full (Path A).

The remaining sorry is at
`OpenMath/Chapter5/Section515.lean:1995` inside
`aux_515D_max_deviation_geometric_bound`.

## Priority 0 — Mandatory reading (5 minutes)

Read all of:

1. `.prover-state/issues/cycle_121_strategy_B2_correction.md` —
   the corrected analytical outline. The full vectorial path
   (Path A) and the narrowed-helper fallback (Path B) are both
   spelled out there. Internalise the residual bound

   `|K m i| ≤ α · h_n · sup_j |δ(m) j| + β · h_n²`

   (NOT `K_R · h²`). The `α · h · δ_max` term is genuine and
   comes from `localStepError_bound`'s output
   (`Section515.lean:1407`).

2. `.prover-state/issues/aux_515D_iterated_V_bound.md` (the
   cycle 120 closure note at the bottom). Confirms that
   `aux_515D_iterated_V_bound` (declared by cycle 120 around
   `Section515.lean:1854`) gives
   `sup_i |((V^k) *ᵥ x) i| ≤ C₀ · sup_j |x j|`
   for any `k`, any `x`, with `C₀ := r · C` derived from
   `M.IsStable`.

3. `aux_515D_max_deviation_geometric_bound`'s signature
   (`Section515.lean:1961-1995`) — the target. Note especially
   that it does **not** currently take `_hc_nn` as a hypothesis;
   that gap is what blocked the cycle 121 attempt and will be
   propagated through this cycle.

4. `localStepError_bound`'s signature
   (`Section515.lean:1355-1407`) — confirm the K-bound output
   shape `|K i| ≤ α * h * δ_max + β * h^2` and the requirement
   for `_hc_nonneg : ∀ i, 0 ≤ c i`.

5. `M.glmAbscissae` definition (`Section515.lean:98-100`):
   `M.glmAbscissae v = M.A *ᵥ 1 + M.U *ᵥ v`. Neither term is
   forced non-negative by `IsConsistent` / `IsStable` — confirms
   Path A1 (internal proof of `0 ≤ c`) is not viable.

## Priority 1 — Narrow the §515D sorry via Path B (primary deliverable)

**Goal**: replace the current sorry with a composition that uses
ONE new private helper (sorry body), so the §515D analytical
core is isolated to a focused per-step K-bound claim with the
analytically-correct shape.

### Step 1 — Introduce the new helper

Add a new `private theorem aux_515D_per_step_K_bound` immediately
above `aux_515D_max_deviation_geometric_bound` (around line 1960).
**Crucial**: use the corrected residual shape from the cycle 121
correction issue, NOT the strategy's broken `K_R · h²` form.

```lean
/-- **Per-step K-bound for the vectorial recurrence (Path B
narrowing, cycle 122).**

For each `n ≥ 1` and each step `m + 1 ≤ n`, the residual
  `R(m) := δ(m+1) − M.V *ᵥ δ(m)`
satisfies the analytically correct shape

  `|R(m) i| ≤ α · h_n · sup_j |δ(m) j| + β · h_n²`,

with `α, β` non-negative constants depending on the GLM and the
problem data, where `δ(k) i := Y n k i − target(k) i` and
`target(k) i := u_i · yex(x₀ + k·h_n) + v_i · h_n · deriv yex(x₀ + k·h_n)`.

This lemma packages the per-step application of
`localStepError_bound` (Section515.lean:1355) plus
`aux_515D_construct_ell_U_phi_A` (Section515.lean:1213). Its body
remains `sorry`-d in cycle 122; the body composition is gated on
the `_hc_nn : ∀ i, 0 ≤ M.glmAbscissae v i` hypothesis (now
propagated through the §515D helper chain). -/
private theorem aux_515D_per_step_K_bound {s r : ℕ}
    (M : GeneralLinearMethod s r)
    (_hStab : M.IsStable)
    {f : ℝ → ℝ} {L : NNReal} (_hf_lip : LipschitzWith L f)
    {x₀ y₀ : ℝ} {yex : ℝ → ℝ}
    (_hyex_x₀ : yex x₀ = y₀)
    (_hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x)
    {u v : Fin r → ℝ}
    (_hVu : M.V *ᵥ u = u) (_hUu : M.U *ᵥ u = (fun _ => 1))
    (_hCons_eq : M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v)
    {x : ℝ} (_hxx : x₀ < x)
    {M_bound : ℝ} (_hM_nn : 0 ≤ M_bound)
    (_hyex_C1 : ContDiff ℝ 1 yex)
    (_hyex_M : ∀ t ∈ Set.Icc x₀ x, |yex t| ≤ M_bound)
    (_hyex'_LM : ∀ t ∈ Set.Icc x₀ x, |deriv yex t| ≤ (L : ℝ) * M_bound)
    (_h_norm : ‖(((x - x₀) * (L : ℝ)) • M.A.map (fun a => |a|) :
                 Matrix (Fin s) (Fin s) ℝ)‖ < 1)
    (_hc_nn : ∀ i, 0 ≤ M.glmAbscissae v i)   -- NEW propagated hypothesis
    [Nonempty (Fin r)]
    (Y : ℕ → ℕ → Fin r → ℝ) (Y_int : ℕ → Fin s → ℝ)
    (_hY_iter : ∀ n : ℕ, 0 < n →
      M.IsGLMSolution ((x - x₀) / (n : ℝ)) f (Y n) ∧
      (∀ i, Y_int n i =
              (∑ j, M.A i j * (((x - x₀) / (n : ℝ)) * f (Y_int n j)))
              + (∑ j, M.U i j * Y n n j))) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
      ∀ n : ℕ, 0 < n → ∀ m : ℕ, m + 1 ≤ n →
        let h_n := (x - x₀) / (n : ℝ)
        let target := fun (k : ℕ) (i : Fin r) =>
          u i * yex (x₀ + (k : ℝ) * h_n)
            + v i * h_n * deriv yex (x₀ + (k : ℝ) * h_n)
        let δ := fun (k : ℕ) (i : Fin r) => Y n k i - target k i
        ∀ i : Fin r,
          |Y n (m+1) i - target (m+1) i - (M.V *ᵥ (δ m)) i|
            ≤ α * h_n
                * Finset.sup' Finset.univ Finset.univ_nonempty
                    (fun j => |δ m j|)
              + β * h_n^2 := by
  sorry
```

Use `camelCase` hypothesis names (`hStab`, `hfLip`, `hcNn`, etc.)
to avoid the standing tautology-scanner regression. The
underscore-prefixed `_hc_nn` form above is for the SIGNATURE; in
the body, bind via `(hcNn := _hc_nn)` style if you reference it
by hand.

### Step 2 — Cascade-impact audit BEFORE editing

Confirm that the propagated `_hc_nn` is contained inside §515D's
helper chain only:

* §513 (`convergent_isStable` in `Section513.lean`) does NOT call
  `aux_515D_max_deviation_geometric_bound`. **Unaffected** by
  the propagation.
* §514 (`convergent_isPreconsistent` /
  `convergent_preconsistent_isConsistent` in `Section514.lean`)
  does NOT call `aux_515D_max_deviation_geometric_bound`.
  **Unaffected.**
* The forward chain inside §515D is:
  `aux_515D_max_deviation_geometric_bound`
   ← `aux_515D_max_deviation_bound_tendsto_zero` (cycle 118)
   ← `aux_515D_componentwise_deviation_tendsto_zero` (cycle 117,
      `Section515.lean:2268`)
   ← `aux_515D_output_tendsto`
   ← `stable_consistent_isConvergent` (capstone).

So `_hc_nn` propagates **only inside §515D's helper chain**. Each
intermediate caller takes `_hc_nn` as a hypothesis and forwards it.
At the §515D capstone level, `_hc_nn` becomes a hypothesis on
`stable_consistent_isConvergent` itself — a faithfulness
divergence to be documented (Step 6 below).

If, while editing, you discover that any of §513 / §514 / §515D's
non-§515D-internal consumers genuinely needs `_hc_nn`, **STOP** and
rewrite the strategy as a planning-only deliverable (cycle 123 will
re-plan).

### Step 3 — Add `_hc_nn` to `aux_515D_max_deviation_geometric_bound`

Add `(_hc_nn : ∀ i, 0 ≤ M.glmAbscissae v i)` to the signature of
`aux_515D_max_deviation_geometric_bound` (line 1961). Place it
just above `[Nonempty (Fin r)]` to match the strategy's natural
hypothesis ordering.

### Step 4 — Compose the body of `aux_515D_max_deviation_geometric_bound`

Use the corrected vectorial sum-form Grönwall recipe from the
cycle 121 correction issue (§"What is actually true and provable"
+ §"Recommended path for cycle 122"):

```text
1. Setup (~10 LOC): set h_n := (x − x₀)/n, target, δ, δ_max(m).
2. K-bound (~10 LOC): apply aux_515D_per_step_K_bound to extract
   α, β with ∀ n m i, |R(m) i| ≤ α·h_n·δ_max(m) + β·h_n².
3. Iterated V (~5 LOC): obtain ⟨C₀, hC₀_nn, hC₀⟩ from
   aux_515D_iterated_V_bound applied to M.V and _hStab.
4. Closed-form expansion (~30 LOC): induction on m showing
   δ(m) = V^m·δ(0) + Σ_{k<m} V^(m−1−k)·K(k)
   (where K(k) := δ(k+1) − V·δ(k)).
5. Sum-form bound (~25 LOC): apply hC₀ entrywise to derive
   sup_i|δ(m) i| ≤ a + α'·h_n·Σ_{k<m} sup_i|δ(k) i| + β'·h_n²·m
   with a := (C₀ + C₀·α·h_n)·sup_i|δ(0) i|, α' := C₀·α, β' := C₀·β.
   (Split the K(k) sum at k=0 and absorb δ(0) into a.)
6. Grönwall (~15 LOC): apply aux_515D_gronwall_bound
   (Section515.lean:1742) to get the closed-form exp(α'·Δx)
   bound. Handle α'=0 edge via `by_cases` on `α'`.
7. Output (~10 LOC): set
     C_init := C₀ · (1 + α·(x−x₀)) · exp(C₀·α·(x−x₀))
     C_lin  := (exp(C₀·α·(x−x₀)) − 1) · (β/α)   -- α > 0 branch
     C_lin  := C₀·β·(x−x₀)                      -- α = 0 branch
   Discharge non-negativity via positivity / linarith.
```

Total: ~105 LOC outer composition. Build incrementally — verify
compile after each step. If Step 4 (induction on `m`) blows up
heartbeats, split into a separate private lemma
`aux_515D_delta_closed_form`.

### Step 5 — Propagate `_hc_nn` up the §515D-internal chain

Add `(_hc_nn : ∀ i, 0 ≤ M.glmAbscissae v i)` to the signatures of:

* `aux_515D_max_deviation_bound_tendsto_zero` (cycle 118 helper)
* `aux_515D_componentwise_deviation_tendsto_zero` (cycle 117,
  `Section515.lean:2268`)
* `aux_515D_output_tendsto`
* `stable_consistent_isConvergent` (the §515D capstone)

In each case, the body of the calling lemma threads `_hc_nn`
through to the callee. The cascade work is mechanical text edit
plus the body-edit at the capstone (where `_hc_nn` becomes a
named hypothesis on the theorem signature itself, supplied by
the caller of `IsConvergent`).

### Step 6 — Document the faithfulness divergence

Create `.prover-state/issues/stable_consistent_isConvergent_hc_nn.md`
explaining:

* The textbook (Butcher §515) does NOT require `0 ≤ c` on the
  GLM abscissae. The textbook implicitly assumes well-behaved
  abscissae for the methods of interest (e.g. Runge–Kutta-style
  GLMs with `c ∈ [0, 1]`).
* Our formalisation requires it because
  `aux_515D_construct_ell_U_phi_A` (cycle 114) consumes it as a
  hypothesis to construct the M-matrix bounds via
  `Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one` (which only
  applies to entrywise-non-negative inputs).
* Cycle 122 propagates `_hc_nn` upstream rather than refactoring
  `aux_515D_construct_ell_U_phi_A` (refactor would be ~3 cycles
  of effort and is not on the critical path).
* Future remediation: revisit if a downstream consumer (e.g.
  applying `IsConvergent` to an explicit GLM with negative
  abscissae) is genuinely blocked.

Also update `.prover-state/issues/cycle_121_strategy_B2_correction.md`
with a "Cycle 122 update" section recording the narrowing.

### Step 7 — Verify

* `lake env lean OpenMath/Chapter5/Section515.lean` must exit 0.
* Run `lake build OpenMath.Chapter5.Section515` to refresh the
  olean cache (per cycle 072 lesson — `lake env lean` does NOT
  update the cache).
* The ONE remaining `sorry` in §515D should be in
  `aux_515D_per_step_K_bound`'s body, NOT in
  `aux_515D_max_deviation_geometric_bound`.
* Tautology scanner: run
  `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter5/Section515.lean`
  — must return 0 hits.
* Run `#print axioms` on
  `OpenMath.Chapter5.Section510.GeneralLinearMethod.stable_consistent_isConvergent`
  via a small test file or `lean_verify`. Expected:
  `[propext, sorryAx, Classical.choice, Quot.sound]` with `sorryAx`
  traceable only to `aux_515D_per_step_K_bound`'s body.
* Build §513 / §514 to confirm no cascade regressions:
  `lake env lean OpenMath/Chapter5/Section513.lean` and
  `lake env lean OpenMath/Chapter5/Section514.lean`. Both must
  exit 0.

## Priority 2 — Aristotle (single-shot submission)

Submit `aux_515D_per_step_K_bound`'s body as ONE Aristotle project
once Priority 1 is committed. Use the abstract-axioms pattern
from cycle 116. Submit ONCE; do NOT poll this cycle (CLAUDE.md is
explicit). Cycle 123 will check the result.

Do NOT submit the outer composition
(`aux_515D_max_deviation_geometric_bound` body) to Aristotle — it
is being closed manually this cycle.

## Priority 3 (stretch) — Close `aux_515D_per_step_K_bound`'s body

If Priority 1 (Steps 1–7) lands quickly (< ~2 hours of cycle
time remaining), attempt the body of `aux_515D_per_step_K_bound`
directly. Recipe:

1. **Define h_n, target, δ, δ_max.** Match the signature's `let`
   bindings.
2. **Apply `aux_515D_construct_ell_U_phi_A`** (`Section515.lean:1213`)
   with `c := M.glmAbscissae v`, `_hc_nonneg := _hc_nn`, and
   `h_norm := _h_norm`. Extract `ell_U`, `phi_A` and the four
   side conditions.
3. **Set α, β.** From `aux_515D_construct_ell_U_phi_A`'s output:
   ```
   α := (L : ℝ) * Finset.sup' Finset.univ Finset.univ_nonempty
            (fun i => ∑ j, |M.B i j| * ell_U j)
   β := (L : ℝ)^2 * M_bound *
          Finset.sup' Finset.univ Finset.univ_nonempty
            (fun i => (1/2) * |u i| + |v i|
                       + (∑ j, |M.B i j * (M.glmAbscissae v) j|)
                       + (x - x₀) * (L : ℝ)
                          * (∑ j, |M.B i j| * phi_A j))
   ```
   (`α` and `β` come from the `_hα_def` / `_hβ_def` bounds in
   `localStepError_bound`'s signature; the `sup'` here is a
   uniform-over-`i` envelope so it satisfies `_hα_def` /
   `_hβ_def` for each `i`.)
4. **For each `n ≥ 1, m+1 ≤ n`**: apply `localStepError_bound`
   with
   * `h := h_n`, `h₀ := x − x₀` (so `h ≤ h₀` since `n ≥ 1`),
   * `xn1 := x₀ + m · h_n`,
   * `yt_prev := Y n m`,
   * `c := M.glmAbscissae v` with `_hc_nonneg := _hc_nn`,
   * the `_hα_def` / `_hβ_def` choices supply the chosen α, β,
   * stage values come from `_hY_iter`'s `IsGLMSolution`
     decomposition.
   Extract `K : Fin r → ℝ` with the per-step recurrence.
5. **Convert to sup'-norm form**: use `Finset.sup'_le` /
   `Finset.le_sup'` to bound
   `sup_i |K(m) i| ≤ α·h·sup_j|δ(m) j| + β·h²`
   from `localStepError_bound`'s conclusion `|K i| ≤ α·h·δ_max + β·h²`.

Estimated ~100 LOC if all hypotheses align cleanly. If any
hypothesis mismatch shows up, leave the helper sorry'd and let
Aristotle (Priority 2) try in parallel.

## Explicit DO-NOT list

* **DO NOT** treat the cycle 121 correction issue's analysis as
  optional. Read it before writing any Lean.
* **DO NOT** attempt the strategy's old `K_R · h²` residual claim.
  It is analytically wrong; the `α · h · δ_max` term cannot be
  absorbed (cycle 121 issue file shows the algebraic obstruction).
  Use the corrected shape from this strategy's Step 1.
* **DO NOT** invoke `aux_515D_per_step_recurrence`
  (`Section515.lean:1681`) directly on the sup-norm. Its scalar
  `(V_norm + α·h)^n` form blows up for stable but non-contracting
  `V` (cycle 118 dead end). Use the **vectorial** path:
  closed-form expansion + cycle 120 iterated V bound +
  `aux_515D_gronwall_bound` (sum-form).
* **DO NOT** try Path A1 (internal proof of `0 ≤ M.glmAbscissae v`).
  `M.glmAbscissae v = M.A *ᵥ 1 + M.U *ᵥ v` (`Section515.lean:98–100`)
  — neither term is forced non-negative by `IsConsistent` /
  `IsStable` / `IsPreconsistent`. Path A1 is not viable; this
  strategy uses Path A2 (propagate `_hc_nn` upstream as a
  documented faithfulness divergence).
* **DO NOT** modify §513 (`convergent_isStable`) or §514
  (`convergent_isPreconsistent`,
  `convergent_preconsistent_isConsistent`). They do not consume
  `_hc_nn`. The cascade audit (Step 2 above) confirms this. If
  a §513/§514 build break appears, STOP and re-plan — it means
  the propagation has gone wider than expected.
* **DO NOT** raise `maxHeartbeats` above 200000. If the
  closed-form-expansion induction (Step 4) is slow, decompose
  into separate `have` blocks per induction step or split into
  a separate private lemma.
* **DO NOT** introduce new `axiom`/`constant` declarations.
* **DO NOT** edit `scripts/autonomous_loop.py` to fix the
  scanner — that is loop-maintainer territory
  (`.prover-state/issues/tautology_scanner_false_positives.md`).
  Use camelCase hypothesis names this cycle.
* **DO NOT** poll Aristotle more than once this cycle. CLAUDE.md
  is explicit. Submit Priority 2 once; do not check status until
  cycle 123.
* **DO NOT** rename, delete, or restructure the cycle 120
  `aux_515D_iterated_V_bound` lemma — it is the load-bearing
  tool for Step 4–5 of Priority 1 and was renamed in cycle 121.
  Touching it again risks scanner regression.
* **DO NOT** widen the `IsConvergent`, `IsConsistent`, or
  `IsStable` definitions. The propagated `_hc_nn` lives on
  `stable_consistent_isConvergent`'s signature directly, NOT
  inside `IsConvergent`. Adding it inside `IsConvergent` would
  break §513 / §514 cascades again (cycle 113 lesson).

## Bookkeeping

* If Priority 1 lands cleanly (one-helper narrowing achieved):
  update `lean_status.json`'s `thm:515D` row to record cycle 122
  with status still `partial`.
* Do NOT mark `thm:515D` as `formalized` unless
  `aux_515D_per_step_K_bound`'s body is also closed (Priority 3
  succeeds).
* Update `plan.md`'s §515 row only if status changes to
  `formalized`. Otherwise update only the inline note for the
  `thm:515D` row.
* Append a cycle 122 update note to
  `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md`
  documenting the new narrowing and the `_hc_nn` propagation.
* Append a cycle 122 update to
  `.prover-state/issues/cycle_121_strategy_B2_correction.md`
  recording resolution of the strategy bug.

## Cycle 122 minimum bar

A successful cycle 122 must:

1. Either close `aux_515D_max_deviation_geometric_bound`'s body
   in full (using cycle 120's iterated V bound) — closing the
   §515D helper chain modulo `aux_515D_per_step_K_bound`'s sorry,
   **or** close `aux_515D_per_step_K_bound` directly (Priority 3),
   **or** at minimum land a structurally-correct narrowing
   (Priority 1 Steps 1–7) so the remaining sorry is in a focused
   per-step K-bound helper with the analytically-correct shape
   AND `_hc_nn` propagated through the §515D internal chain.
2. Compile clean
   (`lake env lean OpenMath/Chapter5/Section515.lean` exits 0).
3. Tautology scanner: 0 hits in `Section515.lean`.
4. `#print axioms stable_consistent_isConvergent` shows
   `sorryAx` traceable only to the new K-bound helper (or the
   geometric-bound body if Priority 1 Steps 4 is also achieved).
5. No unintended cascade regressions in §513 / §514 / §515 (run
   `lake build OpenMath.Chapter5.Section515` to check).

A cycle that narrows the locus from
`aux_515D_max_deviation_geometric_bound` (currently a ~150-LOC
analytical claim) to `aux_515D_per_step_K_bound` (~80-LOC focused
per-step claim with the correct shape) is a **genuine forward
step** even if no Aristotle proofs return.
