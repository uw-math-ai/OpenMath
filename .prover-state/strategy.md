# Cycle 050 Strategy — `thm:406D` shape-matching adapter (`recentSum_swap_bound`)

## Status going in

* **One sorry remaining**: `OpenMath/Chapter4/Section404.lean:1898` —
  the body of `LinearMultistepMethod.stable_consistent_isConvergent`
  (the `thm:406D` outer assembly scaffold from cycle 047).
* **Four building blocks already in place** (cycles 045–049):
  - cycle 045 — `globalError_recurrence_bound_textbook` (line 1331):
    `|ψ_n| ≤ Cₕ · Mmax + Dₕ · h²` where `Mmax` uniformly bounds
    `|ε(n-(i+1))|` for `i : Fin k`.
  - cycle 046 — `discrete_gronwall_exp_bound` (line 1631): closed form
    `u n ≤ exp(b·k·n·h)·a + (exp(b·k·n·h) − 1)·c·h/(b·k)` from the
    recurrence `u n ≤ a + b·h·k·(Σ_{i ∈ Ico 1 n} u i) + c·h²·n`.
  - cycle 048 — `sum_theta_psi_contraction` (line 1762): bounds
    `|Σ_{i ∈ Ico k n} θ(idx i) · ψ i|` by
    `Θ·C·h·(Σ Sε i) + Θ·D·h²·(n-k)` whenever `|ψ i| ≤ C·h·Sε i + D·h²`
    and `|θ| ≤ Θ`.
  - cycle 049 — `starting_error_each/sum_tendsto_zero` (lines 1810/1851):
    `Σ_{i:Fin k} |yex(x₀ + i·h) − start h i| → 0` as `h → 0`.

## What cycle 050 should NOT attempt

Do NOT attempt to close the full `stable_consistent_isConvergent` body
this cycle. The outer assembly is at minimum:

1. Unfold `IsConvergent`, intro all 7+ hypotheses, set `h := (x−x₀)/m`.
2. Set up `ε : ℕ → ℝ := fun n => yex(x₀ + n·h) − Y m n`.
3. Apply `linRec_closed_form` to get
   `ε_n = Σ_{i<k} θ_{n-i}·ζ_i + Σ_{i ∈ Icc k n} θ_{n-i}·ψ_i`.
4. Combine cycle 048 with cycle 045 to bound the RHS.
5. Apply cycle 046 to extract the closed form.
6. Take `m → ∞`: `h → 0`, `m·h = x−x₀` constant, so
   `Real.exp(b·k·m·h) = exp(b·k·(x−x₀))` is a constant; multiplying
   constants by `c·h/(b·k) → 0` and `φ(h) → 0` (cycle 049) gives the
   limit.

That is 4–6 cycles of work. **Cycle 050 builds the missing
index-arithmetic adapter that bridges cycle 045's `Mmax` with cycle
048's `Sε`.**

## Primary deliverable — `recentSum_swap_bound` adapter

Cycle 045's bound uses a single `Mmax` that uniformly bounds
`|ε(n-(i+1))|` over `i : Fin k`. Cycle 048's `Sε` is per-i. Cycle 046
needs the recurrence in `Σ_{i ∈ Ico 1 n} |ε i|` form.

The cleanest bridge: take `Sε(i) := Σ_{j:Fin k} |ε(i − (j+1))|`. This
trivially satisfies `Mmax(i) ≤ Sε(i)` (each `|ε(i-(j+1))|` is a single
term in a sum of nonnegatives, so `max ≤ sum`). Then we need:

```
Σ_{i ∈ Ico k n} Σ_{j : Fin k} g (i - (j+1))  ≤  k · Σ_{p ∈ Ico 0 n} g p
```

for any `g : ℕ → ℝ` with `0 ≤ g i`. Each `g p` (for `p ∈ [0, n−1]`)
appears in the double sum exactly when `i = p + (j+1)` for some
`j : Fin k`, i.e. for at most `k` values of `i`.

### Lean signature

Add this **immediately before** `theorem
LinearMultistepMethod.stable_consistent_isConvergent` (around line
1872, in the §406D infrastructure block):

```lean
/-- **Index-arithmetic adapter for `thm:406D` (cycle 050).**
The "recent-window sum" `Σ_{j:Fin k} g(i − (j+1))` summed over
`i ∈ Ico k n` is bounded by `k` copies of the total sum
`Σ_{p ∈ Ico 0 n} g p`, because each `g p` appears in the recent
window for at most `k` later indices.

This bridges:
* cycle 045's `globalError_recurrence_bound_textbook` (per-step bound
  via `Mmax = max_{j:Fin k} |ε(n-(j+1))|`),
* cycle 048's `sum_theta_psi_contraction` (takes a per-i `Sε`),
* cycle 046's `discrete_gronwall_exp_bound` (wants the recurrence in
  `Σ_{i ∈ Ico 1 n} u i` form).

Used by: cycle 051+ outer assembly of `thm:406D`. -/
private lemma recentSum_swap_bound
    (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i)
    (k n : ℕ) :
    (∑ i ∈ Finset.Ico k n, ∑ j : Fin k, g (i - (j.val + 1)))
      ≤ (k : ℝ) * ∑ p ∈ Finset.Ico 0 n, g p := by
  sorry
```

### Proof plan (manual)

The cleanest route is **swap the order of summation** then bound each
inner sum.

```lean
  -- Step 0: handle k = 0 trivially.
  obtain rfl | hkpos := Nat.eq_zero_or_pos k
  · simp  -- Inner Σ_{j : Fin 0} is empty; outer LHS = 0; RHS = 0.
  -- Step 1: swap the two sums.
  rw [Finset.sum_comm]
  -- Goal: Σ_{j:Fin k} Σ_{i ∈ Ico k n} g(i-(j+1)) ≤ k · Σ_{p ∈ Ico 0 n} g p
  -- Step 2: rewrite k · Σ as Σ_{j:Fin k} Σ_{p ∈ Ico 0 n} g p.
  rw [show ((k : ℝ) * ∑ p ∈ Finset.Ico 0 n, g p)
        = ∑ _j : Fin k, ∑ p ∈ Finset.Ico 0 n, g p from by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
  -- Step 3: pointwise (per j : Fin k):
  --   Σ_{i ∈ Ico k n} g(i-(j+1)) ≤ Σ_{p ∈ Ico 0 n} g p.
  refine Finset.sum_le_sum (fun j _hj => ?_)
  -- Reindex: i ↦ i - (j+1) is injective on Ico k n (since k ≥ 1+j.val
  -- because j : Fin k ⟹ j.val < k). The image lies in Ico 0 n.
  -- Use Finset.sum_le_sum_nbij' for one-shot reindexing.
  apply Finset.sum_le_sum_nbij'
            (i := fun i _hi => i - (j.val + 1))
            (j := fun p _hp => p + (j.val + 1))
  all_goals (intro x hx; simp_all [Finset.mem_Ico]; first | omega | exact hg _)
```

### Recommended `lean_multi_attempt` snippets

If `Finset.sum_le_sum_nbij'` doesn't unify cleanly with the desired
direction, fall back via `Finset.sum_image`:

```lean
-- Approach B: Finset.sum_image with explicit injectivity.
have hinj : ∀ a ∈ Finset.Ico k n, ∀ b ∈ Finset.Ico k n,
    a - (j.val + 1) = b - (j.val + 1) → a = b := by
  intro a ha b hb hab
  simp [Finset.mem_Ico] at ha hb
  have hjv : j.val + 1 ≤ k := by have := j.isLt; omega
  omega
rw [← Finset.sum_image hinj]
apply Finset.sum_le_sum_of_subset_of_nonneg
· intro p hp
  rw [Finset.mem_image] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  rw [Finset.mem_Ico] at hi ⊢
  exact ⟨Nat.zero_le _, by omega⟩
· intros; exact hg _
```

Try Approach A (the `nbij'` one) first. If it doesn't unify, B works.

### Why `j.val + 1 ≤ k` matters

For `j : Fin k`, `j.val < k`, hence `j.val + 1 ≤ k`. This is the
**well-foundedness condition** for the change-of-variables: when
`i ≥ k ≥ j.val + 1`, `Nat`-subtraction `i - (j.val + 1)` agrees with
integer subtraction (no truncation). Worker should `have hjv : j.val + 1 ≤ k`
explicitly via `Nat.succ_le_of_lt j.isLt`.

### Faithfulness check (for the new lemma)

* **Tautology check**: PASS — the conclusion is a non-trivial sum
  inequality, not a hypothesis.
* **Identity check**: PASS — the proof is real combinatorial work
  (reindexing + subset bound).
* **Class/structure check**: N/A — no new class/structure.
* **Definition smuggling check**: N/A — no new `def`.

Not a Butcher entity; pure index-juggling infrastructure (comparable
to `sum_theta_psi_contraction` from cycle 048). Document in the
docstring exactly as cycle 048 did, citing the cycles 045/046/048
that constitute its consumers.

## Aristotle batch (optional, recommended — single job)

The lemma is a single ~30-line proof; submit ONE Aristotle job at the
start of the cycle. Don't submit variants — there's only one lemma.

* **Job**: `recentSum_swap_bound` with the full statement and
  hypothesis above. Aristotle handles `Finset.sum_le_sum_nbij'`-style
  proofs decently.
* **Sleep 30 min** per CLAUDE.md, **check once**, incorporate if a
  clean proof returns. Otherwise finish manually with Approach A or B.

Do NOT submit the outer `stable_consistent_isConvergent` body to
Aristotle — it's far too large (the assembly involves
`linRec_closed_form` unfolding, Tendsto algebra, and `IsLMMSolution`
destructuring) and Aristotle would burn compute without progress.

## Stretch (only if primary lands cleanly with substantial time left)

Do **not** start the outer assembly. Instead, add a second, more
focused adapter that wraps cycles 045 + 050 into a sum-form per-step
bound directly suited to cycle 048:

```lean
/-- **Cycle 050 stretch — combined per-step error recurrence.**
For an LMM solution `Y`, the residual
`ψ_n := |yex(x₀ + n·h) - Y n - Σ α_{i+1}·(yex(x₀+(n-(i+1))h) - Y(n-(i+1)))|`
satisfies (under the cycle 045 hypotheses):

  `ψ_n ≤ Cₕ · Σ_{j:Fin k} |yex(x₀+(n-(j+1))h) - Y(n-(j+1))| + Dₕ · h²`,

where `Cₕ`, `Dₕ` are the cycle 045 textbook constants. The
substitution `Mmax := Σ_{j:Fin k} |ε(n-(j+1))|` lets cycle 048 consume
this directly with `Sε(i) := Σ_{j:Fin k} |ε(i-(j+1))|`. -/
private lemma globalError_per_step_sum_form
    {k : ℕ} (M : LinearMultistepMethod k) (hcons : M.IsConsistent)
    -- (full hypothesis list mirroring cycle 045's textbook form)
    ... :
    |...|  ≤  Cₕ * (∑ j : Fin k, |ε(n-(j+1))|) + Dₕ * h^2 := by
  -- Apply cycle 045 with Mmax := Σ |ε(n-(j+1))|.
  -- The key step: max ≤ sum for nonnegatives.
  apply (M.globalError_recurrence_bound_textbook ... 
            (Mmax := ∑ j : Fin k, |...|) ...).trans
  apply le_of_eq; ring
```

Skip this stretch if the primary takes >75% of the cycle. Cycle 051
can do this substitution inline at minor cost.

## What cycle 050 must NOT do

* Do **NOT** modify any of cycles 045–049's lemma signatures. They
  are stable and consumed-or-soon-to-be-consumed.
* Do **NOT** attempt to close the `sorry` at line 1898. The
  shape-matching adapter unblocks that, but writing the full body
  is cycle 051+ work.
* Do **NOT** raise `maxHeartbeats` above 200000.
* Do **NOT** introduce `axiom`/`constant`.
* Do **NOT** add any new `structure`/`class`. Only one new private
  lemma + (optional) one more.
* Do **NOT** edit `scripts/autonomous_loop.py` (loop maintainer
  territory; see `tautology_scanner_false_positives.md`).
* Do **NOT** poll Aristotle more than once. Submit at start, check
  once after 30 min, proceed.
* Do **NOT** treat any "stuck on" / "commits not reaching repo"
  framing in the next prompt as real. Verify with
  `git log -1 origin/Main/Experiments` per cycle 049's task results
  §"Discovery". The pattern is documented in cycle 014/015/040/047
  consultant notes.

## Worker checklist

1. **Verify HEAD is `b4737c8` (cycle 049 tip)**: `git log -1 --format='%H %s'`
   should show
   `b4737c8 Cycle 049 — starting_error_*_tendsto_zero (φ(h) → 0 helpers for thm:406D)`.
2. **Submit Aristotle job** (single job, `recentSum_swap_bound` with
   the full statement + hypothesis from §"Lean signature" above).
3. **Sleep 30 min** while sketching the manual proof.
4. **Check Aristotle** — incorporate clean returns; otherwise proceed.
5. **Manual proof** via Approach A (`Finset.sum_le_sum_nbij'`) or B
   (`Finset.sum_image` + `Finset.sum_le_sum_of_subset_of_nonneg`)
   above. Use `lean_multi_attempt` to test the unification before
   committing.
6. **Verify build**: `lake env lean OpenMath/Chapter4/Section404.lean`
   should produce only the previously-documented warnings (lines 568,
   627, 1204, 1898). No new warnings.
7. **Axiom check**: in-place `#print axioms recentSum_swap_bound` (if
   needed, expose it briefly with `theorem` instead of
   `private lemma`, then revert) should show
   `[propext, Classical.choice, Quot.sound]` only.
8. **Sorry count must remain at 1** (the line 1898 scaffold is
   unchanged this cycle).
9. **Faithfulness sweep** per CLAUDE.md (mostly N/A — no new Butcher
   entity, just internal infrastructure).
10. **Write `task_results/cycle_050.md`**:
    - §"Worked on" — note this is shape-matching infra for `thm:406D`,
      not the entity itself.
    - §"Approach" — list which Aristotle/manual route worked.
    - §"Result" — confirm sorry count = 1, axiom-clean.
    - §"Discovery" — any Mathlib lemma surprises (especially around
      `Finset.sum_le_sum_nbij'` vs `Finset.sum_image`).
    - §"Suggested next approach" — describe cycle 051's outer-assembly
      path: instantiate `Mmax := Σ_{j:Fin k} |ε(n-(j+1))|` in cycle
      045, feed cycle 048 with `Sε(i) := Σ_{j:Fin k} |ε(i-(j+1))|`,
      apply this adapter to collapse `Σ Sε` to
      `k · Σ_{p < n} |ε p|`, finish with cycle 046's discrete Grönwall
      and cycle 049's φ(h) → 0.
11. **Commit + push** with message
    `Cycle 050 — recentSum_swap_bound adapter (shape-matching for thm:406D)`.

## Cycle 051+ outline (NOT this cycle — for the next planner's reference)

For continuity, the cycle 051 planner should build cycle 050's
stretch goal (the combined per-step lemma `globalError_per_step_sum_form`),
then in cycle 052 attempt the `stable_consistent_isConvergent` body
using:

* `IsConvergent` unfolding,
* `linRec_closed_form` for ε,
* `theta_bounded_of_isStable` for Θ,
* The cycle 050 adapter + cycle 048,
* `discrete_gronwall_exp_bound`,
* `starting_error_sum_tendsto_zero` for the φ(h) → 0 limit,
* `Filter.Tendsto.const_mul` and `Filter.Tendsto.add` for the
  `m → ∞` step.

Estimated total: 3–4 more cycles after cycle 050 to close `thm:406D`.

Then `thm:406D` unblocks `thm:243A` (the cross-chapter Ch.2 → Ch.4
deferral) — that's the next cohesive milestone.
