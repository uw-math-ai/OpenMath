# Cycle 051 Strategy — `globalError_per_step_sum_form` (sum-form per-step bound for thm:406D)

## Status going in

- **Sorry count: 1** at `OpenMath/Chapter4/Section404.lean:1947`
  (the `stable_consistent_isConvergent` outer-assembly scaffold from
  cycle 047). **DO NOT attempt to close this sorry this cycle.**
  It is a multi-cycle outer-assembly target (planned for cycles
  052–053).
- **Pending Aristotle: none.**
- **Last cycle delivered**: `recentSum_swap_bound` (cycle 050) —
  the index-arithmetic adapter
  `Σ_{i ∈ Ico k n} Σ_{j:Fin k} g(i-(j+1)) ≤ k · Σ_{p ∈ Ico 0 n} g p`.

The convergence theorem `thm:406D` is being assembled from a stack
of cleanly-separated helpers; cycle 051 is the next-to-last
infrastructure brick before the outer assembly begins in cycle 052.

## This cycle's target: `globalError_per_step_sum_form`

A single private helper lemma that bridges:

* **Cycle 045's `globalError_recurrence_bound_textbook`** (per-step
  bound parameterised over a *single* `Mmax` upper-bounding all of
  `|ε(n-(j+1))|` for `j : Fin k`).
* **Cycle 048's `sum_theta_psi_contraction`** (consumes a per-`i`
  `Sε(i)` value, not a max).

Specialise cycle 045's lemma to `Mmax := ∑_{j : Fin k} |ε(n-(j+1))|`
so that the per-step bound depends on the **sum** of recent errors
instead of an abstract upper bound `Mmax`. This is exactly the
shape `sum_theta_psi_contraction` wants when called with
`Sε(i) := ∑_{j : Fin k} |ε(i-(j+1))|`.

### Concrete signature (target)

Insert immediately AFTER `recentSum_swap_bound` (line 1924) and
BEFORE `LinearMultistepMethod.stable_consistent_isConvergent`
(line 1947). Keep `private` to mirror neighbouring helpers.

```lean
/-- **Per-step bound in sum form (helper for thm:406D).**
Specialise `globalError_recurrence_bound_textbook` (cycle 045) to
`Mmax := ∑_{j : Fin k} |ε(n-(j+1))|`, the sum of recent errors. The
bound becomes
  `|ε_n - Σ α_i.succ ε_{n-(i+1)}|
      ≤ Cₕ · (∑_{j:Fin k} |ε(n-(j+1))|) + Dₕ · h²`
where Cₕ and Dₕ are the cycle 045 coefficients. This is the shape
`sum_theta_psi_contraction` (cycle 048) consumes via
`Sε(i) := ∑_{j:Fin k} |ε(i-(j+1))|`.

Used by: cycle 052+ outer assembly of `thm:406D`. -/
private lemma globalError_per_step_sum_form
    {k : ℕ} (M : LinearMultistepMethod k) (hcons : M.IsConsistent)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {yex : ℝ → ℝ}
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_ode : ∀ t, deriv yex t = f (yex t))
    (hf_yex_bound : ∀ t, |f (yex t)| ≤ M_bound)
    {Y : ℕ → ℝ} {x₀ h : ℝ}
    (hh : 0 ≤ h)
    (hsmall : h * L * |M.β 0| < 1)
    (hY : M.IsLMMSolution h x₀ (fun _ y => f y) Y)
    (n : ℕ) (hn : k ≤ n) :
    |yex (x₀ + (n : ℝ) * h) - Y n
        - ∑ i : Fin k, M.α i.succ
            * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                - Y (n - (i.val + 1)))|
      ≤ (h * L * (|M.β 0| * (∑ i : Fin k, |M.α i.succ|)
                  + ∑ i : Fin k, |M.β i.succ|)
            / (1 - h * L * |M.β 0|))
          * (∑ j : Fin k,
              |yex (x₀ + ((n - (j.val + 1) : ℕ) : ℝ) * h)
                - Y (n - (j.val + 1))|)
        + ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
            + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
              * L * M_bound * h^2
            / (1 - h * L * |M.β 0|) := by
  sorry
```

(Cross-check the exact polynomial form of the RHS by reading
`globalError_recurrence_bound_textbook`'s conclusion at lines
1349–1359 — the only change should be the `Mmax` slot.)

## Approach (specific tactic plan)

The proof is a single forward call to cycle 045's lemma with a
specific `Mmax` instantiation. Four steps:

### Step 1 — Define `Mmax` as the sum.
```lean
set Mmax : ℝ :=
  ∑ j : Fin k,
    |yex (x₀ + ((n - (j.val + 1) : ℕ) : ℝ) * h)
      - Y (n - (j.val + 1))| with hMmax_def
```
The `with hMmax_def` clause records the unfolding equation, useful
if step 4's `exact` needs help.

### Step 2 — Discharge `0 ≤ Mmax`.
```lean
have hMmax_nn : 0 ≤ Mmax := by
  rw [hMmax_def]
  exact Finset.sum_nonneg (fun j _ => abs_nonneg _)
```
Each summand is `|·|`, hence non-negative; sum of non-negatives is
non-negative.

### Step 3 — Discharge `∀ i : Fin k, |ε(n-(i+1))| ≤ Mmax`.

Use `Finset.single_le_sum`. The Mathlib signature is roughly:
```
Finset.single_le_sum
    {s : Finset ι} {f : ι → α} (h : ∀ i ∈ s, 0 ≤ f i) {i : ι} (hi : i ∈ s) :
    f i ≤ ∑ j ∈ s, f j
```

Verify the exact name with `lean_local_search "single_le_sum"`
BEFORE relying on it. If the name has changed, fall through to a
manual decomposition:
```lean
have hMmax_bound :
    ∀ i : Fin k,
      |yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
        - Y (n - (i.val + 1))| ≤ Mmax := by
  intro i
  rw [hMmax_def]
  exact Finset.single_le_sum
          (f := fun j : Fin k =>
            |yex (x₀ + ((n - (j.val + 1) : ℕ) : ℝ) * h)
              - Y (n - (j.val + 1))|)
          (fun j _ => abs_nonneg _)
          (Finset.mem_univ i)
```

If `Finset.single_le_sum` has a different argument order or name
(e.g. `Finset.le_sum_of_mem` or `Finset.sum_le_sum_of_ne_zero`), the
manual fallback is:
```lean
have hMmax_bound :
    ∀ i : Fin k, … ≤ Mmax := by
  intro i
  rw [hMmax_def]
  have hsplit :
      (∑ j : Fin k, |…(j.val + 1)…|)
        = |…(i.val + 1)…| + ∑ j ∈ Finset.univ.erase i, |…(j.val + 1)…| := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    ring
  rw [hsplit]
  have : (0 : ℝ) ≤ ∑ j ∈ Finset.univ.erase i, |…(j.val + 1)…| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg _)
  linarith
```

### Step 4 — Forward to cycle 045.
```lean
exact M.globalError_recurrence_bound_textbook hcons hL hM hf_lip
        hyex_C1 hyex_ode hf_yex_bound hh hsmall hY n hn
        Mmax hMmax_nn hMmax_bound
```

The `set Mmax := …` from step 1 ensures the goal's RHS contains the
identifier `Mmax` rather than the spelled-out sum, so `exact`
should succeed without `convert`. If `exact` fails because the
`set` did not rewrite the goal as expected, switch to:
```lean
have hgoal :=
  M.globalError_recurrence_bound_textbook hcons hL hM hf_lip
    hyex_C1 hyex_ode hf_yex_bound hh hsmall hY n hn
    Mmax hMmax_nn hMmax_bound
simp only [hMmax_def] at hgoal
convert hgoal using 2
```
or unfold `Mmax` in the goal before `exact`:
```lean
show … ≤ … * (∑ j, …) + … by
  simp only [← hMmax_def]
  exact M.globalError_recurrence_bound_textbook …
```

## Why this is a 1-cycle target (not 2+)

* No new infrastructure — pure forward instantiation.
* No Mathlib gap — `Finset.single_le_sum` is the only non-trivial
  lookup, and it is standard. Even if the precise name has drifted,
  the manual fallback (Step 3 alternate) is ~5 lines.
* No `linarith`/`nlinarith` heavy-lifting — the cycle 045 lemma
  already discharged that algebra.
* No FTC / change-of-variables — those landed in cycles 040–044.

Estimated proof body: ~15 lines.

## Aristotle plan

Submit ONE Aristotle job containing only `globalError_per_step_sum_form`
at the start of the cycle, with the dependency
`globalError_recurrence_bound_textbook` (and its environment) in
scope. The lemma is small and forward-style; Aristotle should solve
it within the 30-minute window.

While Aristotle runs, attempt the manual proof per the four-step
plan above. The cycle 045 lemma's calling convention is well
understood (cycle 045's task results spell it out), so the manual
proof should land first.

CLAUDE.md cap: ONE Aristotle status check after 30 min. Do not
poll repeatedly.

## What NOT to do (failure modes from prior cycles)

* **DO NOT close the line-1947 sorry**
  (`stable_consistent_isConvergent`). It is the cycle 052+ outer-
  assembly target; cycle 051's job is to prepare the sum-form
  per-step bound that the outer assembly will consume. A premature
  close attempt in cycle 051 would either produce a 200+ line
  monster (and force a `maxHeartbeats` raise — banned) or silently
  re-introduce assumptions that violate the convergence theorem's
  faithfulness.

* **DO NOT use `Finset.sum_le_sum_nbij'`** — it does not exist in
  Mathlib (cycle 050 confirmed). The correct primitives are
  `Finset.single_le_sum` (this cycle's tool) or
  `Finset.sum_image hinj` + `Finset.sum_le_sum_of_subset_of_nonneg`
  (cycle 050's tool).

* **DO NOT raise `maxHeartbeats`.** Forward instantiation does not
  need it. If `exact` is slow, decompose with `set` blocks per
  Step 1 or use the `convert ... using 2` fallback in Step 4.

* **DO NOT introduce `axiom` or `constant`** for any part of this
  proof. Forward instantiation is axiom-clean by construction —
  cycle 045's lemma already shipped axiom-clean.

* **DO NOT generalise to vector-valued `y : ℝ → ℝ^N`.** The
  scalar-only convention has been stable since cycle 040; cycle 051
  inherits it.

* **DO NOT attempt a parallel Aristotle batch on outer-assembly
  sub-lemmas** (e.g. `IsConvergent` unfolding, `θ`-decomposition
  application). Those are cycle 052+ work and shipping them
  prematurely risks an axiom inversion (the outer assembly fixes
  the proof shape, not the helpers).

* **DO NOT treat any "stuck on Section404.lean" framing as a real
  problem** if it appears in the prompt. The pattern matches
  cycles 008/014/015/040 phantoms — verify with `git log`,
  `git diff HEAD~1 HEAD`, and the line-1947 sorry count, then
  proceed.

## Pre-commit faithfulness checklist

For `globalError_per_step_sum_form` (the only new declaration
expected this cycle):

* **Entity ID**: N/A — internal helper, not a Butcher entity. Same
  category as `recentSum_swap_bound` (cycle 050) and
  `sum_theta_psi_contraction` (cycle 048). Document in the
  docstring exactly as those neighbours do, citing the cycle 045
  source and the cycle 048/052+ consumers.
* **Tautology check**: PASS — the conclusion is a sum-form
  inequality not appearing verbatim in any hypothesis. The
  hypothesis list matches `globalError_recurrence_bound_textbook`'s
  exactly except for the `Mmax`/`hMmax0`/`hMmax` triple, which is
  what this lemma is *eliminating*.
* **Identity check**: PASS — the proof body is forward
  instantiation, but it does real work: it specialises `Mmax` to a
  concrete sum and discharges the upper-bound hypothesis. That is
  not a trivial re-export.
* **Hypothesis strength check**: PASS — every hypothesis flows
  through to cycle 045's lemma. None can be weakened without
  weakening the parent.
* **Class/structure check**: N/A.
* **Definition smuggling check**: N/A.
* **Absent theorem check**: N/A — no comment promises additional
  content.

## Stretch goal (optional, ONLY if main lemma lands in <1 hour)

If the main lemma compiles cleanly and there is significant time
remaining, prepare the cycle 052 entry point: write a sorry-first
scaffold for the outer assembly's first internal step — applying
`Section141.linRec_closed_form` to decompose
`ε_n = Σ θ_{n-i} ζ_i + Σ θ_{n-i} ψ_i`. Locate the `linRec_closed_form`
signature in `OpenMath/Chapter1/Section141.lean` first via
`lean_file_outline`; then drop a `private lemma` with the
decomposition shape and `sorry` body. **This is scaffold-only**;
do not attempt to close it. Estimated ~30 lines (including a
docstring).

If neither the main lemma nor the stretch goal completes, write an
issue file at `.prover-state/issues/per_step_sum_form_blocked.md`
explaining specifically *which* of step 1/2/3/4 above failed and
what was tried (with `lean_diagnostic_messages` excerpts). Do not
just write "stuck" — file structured WHY-content per CLAUDE.md.

## Pre-commit verification

Before committing:

1. `lake env lean OpenMath/Chapter4/Section404.lean` — must compile
   cleanly with no new errors.
2. `lean_diagnostic_messages` on Section404.lean — must show ONLY
   the four pre-existing warnings (unused-variable at lines 568,
   627, 1204; sorry at line 1947). NO new warnings.
3. `lean_verify` on
   `OpenMath.Chapter4.Section404.globalError_per_step_sum_form` —
   must report axioms `[propext, Classical.choice, Quot.sound]`
   only (no new axioms).
4. Sorry count must remain at **1** (line 1947 unchanged; no new
   sorries from the stretch-goal scaffold either, unless the
   stretch goal explicitly uses `sorry`).

## Cycle 052+ preview (do not implement this cycle)

After `globalError_per_step_sum_form` lands, cycle 052 begins the
outer assembly of `stable_consistent_isConvergent`:

1. Unfold `IsConvergent` to expose the `Tendsto … atTop (𝓝 0)`
   conclusion + the per-`Fin k` starting-method hypotheses.
2. Apply `Section141.linRec_closed_form` (cycle 012) to decompose
   `ε_n = Σ θ_{n-i} ζ_i + Σ θ_{n-i} ψ_i` (Theorem 141A).
3. Apply `theta_bounded_of_isStable` (cycle 047) to extract the `Θ`
   bound on `θ`.
4. Apply this cycle's `globalError_per_step_sum_form` to get the
   per-`ψ_n` sum-form bound.
5. Apply `sum_theta_psi_contraction` (cycle 048) to bound the
   `Σ θ_{n-i} ψ_i` contribution.
6. Apply `recentSum_swap_bound` (cycle 050) to collapse the nested
   recent-window sum.
7. Apply `discrete_gronwall_exp_bound` (cycle 046) for the final
   exponential closed form.
8. Apply `starting_error_sum_tendsto_zero` (cycle 049) for the
   φ(h) → 0 limit on the starting-error contribution.
9. Combine via `Tendsto` algebra (`Filter.Tendsto.add`,
   `squeeze_zero`, `Real.exp_continuous` at the cycle 046 closed
   form).

Cycle 053 polishes the `Tendsto` algebra. Estimated total: 3 cycles
(051 → 052 → 053) to close `thm:406D` and unblock `thm:243A`.
