# Cycle 053 Strategy — `thm:406D` autonomous closed-form bound

## Status going in

- **Sorry count: 1** at `OpenMath/Chapter4/Section404.lean:2106`
  (`stable_consistent_isConvergent`, the cycle-047 outer-assembly
  scaffold). **The sorry STAYS this cycle.** Reason: real
  impedance mismatch documented below; closing it requires
  cycle 054+.
- **Pending Aristotle: none.** (Cycle 052 had a job submitted but
  didn't need it; manual proof landed first. That job will
  eventually finish; ignore unless its returned proof is shorter
  than the manual one.)
- **Last cycle (052) delivered**: `globalError_eq_linRec` and
  `globalError_closed_form` (commit `ed546f4`). With cycle 052
  landed, the entire helper chain for `thm:406D` is now in place:
  cycles 045 (per-term bound), 046 (discrete Grönwall), 047
  (theta bound), 048 (sum-theta-psi contraction), 049
  (starting-error → 0), 050 (recent-sum swap), 051 (per-step sum
  form), 052 (closed-form decomposition).

## Phantom-failure check (do this first, ~2 minutes)

The "What I'm stuck on" / `attempts.md` propagation has previously
fired stale verdicts on cycles 008, 014, 015, 035, and 052. Before
treating any "stuck" claim as real, run:

```bash
git log --oneline -3
git rev-parse HEAD origin/Main/Experiments
grep -n 'sorry' OpenMath/Chapter4/Section404.lean
```

Expected (verified at planner time):
- HEAD = `ed546f4` ("Cycle 052 — globalError_eq_linRec + closed-form …")
- HEAD == origin/Main/Experiments (push landed)
- `Section404.lean:2106` is the **only** real sorry. Lines 548 and
  2099 are docstring / comment occurrences.

If those three checks pass, treat cycle 052 as committed and
proceed to the work below. **Do NOT** modify
`scripts/autonomous_loop.py`.

---

## Why this cycle does NOT close the line-2106 sorry

Genuine impedance mismatch between the predicate and the helper
chain:

* `LinearMultistepMethod.IsConvergent` (line 305) quantifies over
  **non-autonomous** `f : ℝ → ℝ → ℝ`; its `IsLMMSolution` and
  `HasDerivAt yex (f x …) x` hypotheses use `f` evaluated at grid
  points.
* The cycle 045–052 chain (`globalError_decomposition`, `T1_bound`,
  `T2_bound`, `T3_bound`, `globalError_recurrence_bound`,
  `globalError_recurrence_bound_textbook`,
  `globalError_per_step_sum_form`, `globalError_eq_linRec`,
  `globalError_closed_form`) is built for **autonomous**
  `f : ℝ → ℝ`. `IsLMMSolution h x₀ (fun _ y => f y) Y` is the
  shape consumed throughout.

Closing `stable_consistent_isConvergent` therefore requires either
(a) generalising the entire chain to non-autonomous `f`
(substantial multi-cycle refactor), or (b) introducing an
autonomous-IVP bridge and proving the autonomous case first, then
handling the non-autonomous reduction separately.

**Cycle 053 picks path (b), step 1**: prove the autonomous
closed-form bound. This is the analytical core of `thm:406D` —
the exponential Grönwall bound on `|ε(n)|` — and is the right
next infrastructure step regardless of which path eventually
closes `IsConvergent`. Cycle 054 then turns the bound into a
Tendsto theorem (autonomous variant); cycle 055+ either
generalises the chain to non-autonomous OR files an issue
documenting the gap.

This decomposition is the natural extension of the cycle 052
worker's "Cycle 053 outer-assembly" plan, made more granular to
fit one cycle.

---

## Concrete deliverable for cycle 053

Add **two new declarations** to `Section404.lean`, immediately
above the existing `stable_consistent_isConvergent` (line 2102).
Plus update the docstring of `stable_consistent_isConvergent`.

### 1. Private helper: `globalError_recurrence_form`

Combines `globalError_closed_form` (cycle 052) +
`theta_bounded_of_isStable` (cycle 047) +
`sum_theta_psi_contraction` (cycle 048) +
`globalError_per_step_sum_form` (cycle 051) +
`recentSum_swap_bound` (cycle 050) into the discrete-Grönwall
recurrence shape that `discrete_gronwall_exp_bound` (cycle 046)
consumes.

Target shape (do NOT copy verbatim — the `_` constants need to
match `globalError_per_step_sum_form` line 1936's actual `bcoef`
and `ccoef` expressions):

```lean
open OpenMath.Chapter1.Section141 in
private lemma globalError_recurrence_form
    {k : ℕ} (hk : 0 < k) (M : LinearMultistepMethod k)
    (hcons : M.IsConsistent) (hstab : M.IsStable)
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
    (hY : M.IsLMMSolution h x₀ (fun _ y => f y) Y) :
    ∃ a b c : ℝ, 0 ≤ a ∧ 0 < b ∧ 0 ≤ c ∧
      (∀ n, 1 ≤ n →
        |yex (x₀ + (n : ℝ) * h) - Y n|
          ≤ a + b * h * (k : ℝ) *
              (∑ p ∈ Finset.Ico 1 n,
                |yex (x₀ + (p : ℝ) * h) - Y p|)
            + c * h^2 * (n : ℝ)) ∧
      |yex x₀ - Y 0| ≤ a := by
  sorry
```

The conclusion's last `|yex x₀ - Y 0| ≤ a` is the `u 0 ≤ a`
hypothesis `discrete_gronwall_exp_bound` requires (line 1634).

### 2. Public theorem: `globalError_closed_form_autonomous`

One-shot composition of `globalError_recurrence_form` with
`discrete_gronwall_exp_bound`:

```lean
/-- **Butcher Theorem 406D, autonomous-IVP form (closed-form bound).**
For a stable consistent LMM solving the autonomous IVP
`y' = f(y)` with `f` Lipschitz and `f∘yex` bounded, the global
error satisfies the exponential closed form

  `|ε(n)| ≤ exp(b·k·n·h)·a + (exp(b·k·n·h) - 1)·c·h/(b·k)`

where `a`, `b`, `c` depend on `M`, `Θ`, `L`, `M_bound`, and `h`.

The textbook conclusion (Tendsto in `IsConvergent`, which is
non-autonomous) follows from this bound by squeezing as `h → 0`;
that closure is the cycle 054+ target. The non-autonomous
generalisation (matching the full `IsConvergent` predicate) is
cycle 055+.

See the docstring on `stable_consistent_isConvergent` for the
ongoing decomposition plan. -/
theorem LinearMultistepMethod.globalError_closed_form_autonomous
    {k : ℕ} (hk : 0 < k) (M : LinearMultistepMethod k)
    (hcons : M.IsConsistent) (hstab : M.IsStable)
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
    (hY : M.IsLMMSolution h x₀ (fun _ y => f y) Y) :
    ∃ a b c : ℝ, 0 ≤ a ∧ 0 < b ∧ 0 ≤ c ∧
      ∀ n,
        |yex (x₀ + (n : ℝ) * h) - Y n|
          ≤ Real.exp (b * (k : ℝ) * (n : ℝ) * h) * a
            + (Real.exp (b * (k : ℝ) * (n : ℝ) * h) - 1)
                * (c * h / (b * (k : ℝ))) := by
  obtain ⟨a, b, c, ha, hb, hc, hrec, hu0⟩ :=
    globalError_recurrence_form hk M hcons hstab hL hM hf_lip
      hyex_C1 hyex_ode hf_yex_bound hh hsmall hY
  refine ⟨a, b, c, ha, hb, hc, ?_⟩
  intro n
  exact discrete_gronwall_exp_bound
    (fun m => |yex (x₀ + (m : ℝ) * h) - Y m|)
    a b c h k ha hb hc hh hk
    (by simpa using hu0)
    hrec n
```

Note: the `simpa using hu0` may need light tweaking — the goal
shape from `discrete_gronwall_exp_bound`'s `hu0` parameter is
`u 0 ≤ a` where `u 0 = |yex (x₀ + 0 * h) - Y 0| = |yex x₀ - Y 0|`.
Use `Nat.cast_zero`, `zero_mul`, `add_zero` to bridge.

### 3. Update `stable_consistent_isConvergent` docstring

Replace the current docstring (lines 2080–2101) — keep the `sorry`
at line 2106 — with one that explains the autonomous bound is
landed and the cycle 054+ Tendsto target. Suggested replacement:

```lean
/-- **Butcher Theorem 406D (p. 347): a stable consistent linear
multistep method is convergent.** [STATUS: scaffold; closure
deferred to cycle 055+.]

The full `IsConvergent` predicate is non-autonomous (`f : ℝ → ℝ → ℝ`),
but the cycle 045–052 helper chain is built for autonomous
`f : ℝ → ℝ`. The analytical core (the exponential closed-form
bound on `|ε(n)|`) lands in this cycle (053) as
`globalError_closed_form_autonomous`. Cycle 054 will turn that
bound into the autonomous-IVP Tendsto theorem
(`stable_consistent_isConvergent_autonomous`). Cycle 055+ then
generalises the chain to non-autonomous `f`, OR files an issue
explaining the residual gap.

Textbook statement (`entities/thm_406D.json`):
> "A stable consistent linear multistep method is convergent."

The body is `sorry` pending cycle 055+ closure. -/
theorem LinearMultistepMethod.stable_consistent_isConvergent
    ...
    M.IsConvergent := by
  sorry
```

---

## Step-by-step proof outline for `globalError_recurrence_form`

The proof chains five existing lemmas plus discrete-Grönwall
shape-matching. Use `set` aggressively to keep terms readable.

### Step 0 — Set notation

```lean
set ε : ℕ → ℝ := fun m => yex (x₀ + (m : ℝ) * h) - Y m with hε_def
set α : Fin k → ℝ := fun j => M.α j.succ with hα_def
```

### Step 1 — Extract Θ ≥ 1 (so `b > 0`)

```lean
obtain ⟨Θ, hΘ_nn, hΘ⟩ := theta_bounded_of_isStable hk M hstab
```

`Θ ≥ 1` because `θ_0 = 1` (Section141 line 115) and
`|θ_0| = 1 ≤ Θ`. To make `b > 0` (strict), use `Θ + 1` instead of
`Θ` in the eventual `b` definition — the bound only loosens.

### Step 2 — Define a, b, c

Read off the constants from `globalError_per_step_sum_form` (lines
1936–1963):

```
bcoef_h := h * L * (|M.β 0| * Σ|α| + Σ|β_succ|) / (1 - h L |β 0|)
ccoef   := ((1/2) Σ (i+1)² |α| + Σ (i+1) |β|) * L * M_bound
            / (1 - h L |β 0|)
```

Then for our recurrence form:
```
C := L * (|M.β 0| * Σ|α| + Σ|β_succ|) / (1 - h L |β 0|)
        -- so bcoef_h = h * C
b := (Θ + 1) * C + 1            -- forced > 0
c := (Θ + 1) * ccoef             -- ≥ 0
a := (Θ + 1) * (Σ_{i ∈ Finset.range k}
        |yPrime k α (fun j => ε j.val) i|)
       + 1                        -- "+1" gives slack for u 0 ≤ a
```

`a` includes the starting-error contribution from the y'-sum in
`globalError_closed_form`. The `Σ_{Finset.range k}` covers any
`min k (n+1)` for `n ≥ 0`. Adding `+ 1` ensures `|yex x₀ - Y 0| ≤ a`
(at `n = 0`, the y'-sum at index 0 is `θ_0 · y'_0 = ε 0 = yex x₀ - Y 0`,
so |yex x₀ - Y 0| ≤ Σ |y'_i| times Θ ≤ a anyway, but the slack
makes `linarith` happy).

(Detail: `b` involves dividing by `(1 - h L |β 0|)`; `hsmall`
guarantees this is positive. Also `c` and `b` may depend on `h` —
that's OK; `discrete_gronwall_exp_bound` allows it.)

### Step 3 — Apply `globalError_closed_form` (cycle 052)

```lean
intro n hn
rw [show ε n = _ from globalError_closed_form M n]
-- Goal: |Σ_{range (min k (n+1))} θ y' + Σ_{Icc k n} θ ψ| ≤ a + ...
```

### Step 4 — Triangle inequality, split into y'- and ψ-sums

```lean
refine (abs_add _ _).trans ?_
-- Now have |Σ θ y'| + |Σ θ ψ| on LHS.
```

### Step 5 — Bound the y'-sum by `a`

```lean
have h_y'_le_a :
    |∑ i ∈ Finset.range (min k (n + 1)),
        theta k α (n - i) * yPrime k α (fun j => ε j.val) i|
      ≤ Θ * (∑ i ∈ Finset.range k,
              |yPrime k α (fun j => ε j.val) i|) := by
  -- Step 5a: |Σ| ≤ Σ |·|.
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  -- Step 5b: per summand: |θ * y'| = |θ| · |y'| ≤ Θ · |y'|.
  -- Step 5c: enlarge index set min k (n+1) → range k. Use
  --          Finset.sum_le_sum_of_subset_of_nonneg with
  --          range_mono : range a ⊆ range b for a ≤ b.
  sorry  -- ~10 lines
```

Then `Θ * Σ |y'_i| ≤ a` since `(Θ + 1) ≥ Θ` and `+ 1` adds slack.

### Step 6 — Bound the ψ-sum via `sum_theta_psi_contraction`

The ψ-sum in `globalError_closed_form` is over `Finset.Icc k n`.
`sum_theta_psi_contraction` (line 1762) takes `Finset.Ico k n`.

**Convert via `Finset.Icc_eq_Ico` analogue**: `Icc k n = Ico k (n+1)`
when `n` finite. Use:
```lean
Nat.Icc_eq_range' or  -- check Mathlib name
Finset.Ico_succ_right
```
Quick verification with `lean_local_search`:
- `lean_local_search "Icc_eq_Ico"` → `Finset.Ico_succ_right :
  Finset.Ico a (b+1) = Finset.Icc a b`. So `Icc k n =
  Finset.Ico k (n+1)`.

After conversion, apply `sum_theta_psi_contraction` with
`idx i := n - i`, `Sε(i) := Σ_{j:Fin k} |ε(i - (j+1))|`,
`hψ` supplied by `globalError_per_step_sum_form` at each `i`:

```lean
have h_psi_each : ∀ i, k ≤ i → i < n + 1 →
    |ε i - ∑ j : Fin k, M.α j.succ * ε (i - 1 - j.val)|
      ≤ (h * C) * (∑ j : Fin k, |ε (i - (j.val + 1))|)
        + ccoef * h^2 := by
  intro i hki hin
  -- Apply globalError_per_step_sum_form at i.
  have := globalError_per_step_sum_form M hcons hL hM hf_lip
            hyex_C1 hyex_ode hf_yex_bound hh hsmall hY i hki
  -- Need: shape match. The (Σ |ε(...)|) on LHS uses
  -- ((i - 1 - j.val : ℕ) : ℝ) inside ε; the bound's sum on RHS
  -- of cycle 051 uses ((i - (j.val + 1) : ℕ) : ℝ). These are the
  -- same nat: `i - 1 - j.val = i - (j.val + 1)` for `i ≥ k > 0`.
  -- omega + simp_rw closes.
  sorry
```

Then `sum_theta_psi_contraction` produces:
```
|Σ_{Ico k (n+1)} θ(n-i) * ψ_i|
  ≤ Θ * (h*C) * h * (Σ_{Ico k (n+1)} Sε i) + Θ * ccoef * h² * (n+1-k)
```

(Note the `h` in `h*C`: `bcoef_h = h * C`, so the contraction's
`C h` becomes `C * h * h = C * h²`. **Re-check this carefully** —
the contraction lemma's signature is `C * h * Sε(i) + D * h^2`, so
matching with our `bcoef_h = h * C * Sε(i)` gives the contraction's
`C := C` (our cycle-051 `C`) and our cycle-051 `bcoef_h` already
has the `h` baked in, but the contraction lemma expects an `h`
multiplied separately. So actually `bcoef_h * Sε(i) =
(h * C) * Sε(i) = C * h * Sε(i)` directly matches the contraction's
form. Good, no double-`h`.)

### Step 7 — Apply `recentSum_swap_bound` (cycle 050)

```lean
have h_swap : (∑ i ∈ Finset.Ico k (n+1),
                ∑ j : Fin k, |ε (i - (j.val + 1))|)
              ≤ (k : ℝ) * (∑ p ∈ Finset.Ico 0 (n+1), |ε p|) :=
  recentSum_swap_bound (fun p => |ε p|)
    (fun p => abs_nonneg _) k (n+1)
```

### Step 8 — Re-shape `Ico 0 (n+1)` → `Ico 1 n` for Grönwall

`discrete_gronwall_exp_bound` expects the recurrence's recent
sum to be `Σ p ∈ Finset.Ico 1 n, u p`. We have
`Σ p ∈ Finset.Ico 0 (n+1), |ε p|`.

Decompose:
```
Σ_{Ico 0 (n+1)} |ε p| = |ε 0| + Σ_{Ico 1 n} |ε p| + |ε n|
```

The `|ε 0|` term: bounded by `Θ + 1 ≤ a` (initial-value
contribution to `a`).

The `|ε n|` term: this is the same as the LHS of the recurrence —
absorbing it would yield an implicit recurrence. **Avoid**: drop
the `i = n` term from the ψ-sum *before* applying
`sum_theta_psi_contraction`.

Concretely, split `Σ_{Icc k n} = Σ_{Ico k n} ∪ {n}` if `k ≤ n`, or
`Σ_{Icc k n} = ∅` if `n < k`. For `n ≥ k`: peel off the `i = n`
contribution `θ_0 · ψ_n = ψ_n` (since `θ_0 = 1`). Bound it
separately:
```
|ψ_n| ≤ bcoef_h * Σ_{j:Fin k} |ε(n-(j+1))| + ccoef * h²
```
where each `|ε(n-(j+1))|` for `j : Fin k` has index `n - (j+1) <
n`, so they all sit inside `Σ_{Ico 0 n} |ε p| ⊆ Σ_{Ico 1 n} |ε p|
∪ {ε 0}`. Bound by `bcoef_h * (Σ_{Ico 1 n} |ε p| + |ε 0|) +
ccoef * h²` (where `|ε 0|` again gets absorbed into `a`).

Then the rest of the ψ-sum (`Σ_{Ico k n}`) uses the contraction +
`recentSum_swap_bound`, yielding `Θ * bcoef_h * k *
(Σ_{Ico 0 n} |ε p|) + Θ * ccoef * h² * (n - k)`.

Combine: split `Σ_{Ico 0 n} = |ε 0| + Σ_{Ico 1 n}`. The `|ε 0|`
absorbs into `a`. The `Σ_{Ico 1 n}` is the Grönwall recent sum.
The `bcoef_h = h * C` baked-in `h` matches Grönwall's `b * h`.

For the `ccoef * h²` constants and the explicit `n` factor: note
`(n - k) ≤ n` and `1 ≤ n` (since `n ≥ k ≥ 1`), so
`Θ * ccoef * h² * (n - k) ≤ Θ * ccoef * h² * n = c * h² * n`. The
`+ ccoef * h²` from the peeled `i = n` term adds `≤ c * h² · 1 ≤
c * h² * n`. OK.

For `n < k`: the ψ-sum is empty (`Icc k n = ∅`), so the bound
collapses to `|ε n| ≤ Θ * Σ |y'_i| ≤ a` directly. The recurrence
hypothesis demands `1 ≤ n`, so `n ∈ {1, …, k-1}` here.

Combine the `n < k` and `n ≥ k` cases:
```
∀ n ≥ 1: |ε n| ≤ a + b * h * k * Σ_{Ico 1 n} |ε p| + c * h² * n
```

### Step 9 — `u 0 ≤ a`

At `n = 0`: `|ε 0| = |yex x₀ - Y 0|`. Bound by `Θ + 1` plus
slack — the y'-sum at `n = 0` is just `θ_0 · y'_0 = ε 0`, so
`|ε 0| ≤ |y'_0| ≤ Σ_{Finset.range k} |y'_i|`. Multiplied by Θ + 1
gives `≤ a`. Use `linarith` after extracting the inequality.

### Aggregate proof shape

```lean
private lemma globalError_recurrence_form ... := by
  -- Step 0–1: notation, Θ extraction.
  set ε : ℕ → ℝ := fun m => yex (x₀ + (m : ℝ) * h) - Y m with hε_def
  set α : Fin k → ℝ := fun j => M.α j.succ
  obtain ⟨Θ, hΘ_nn, hΘ⟩ := theta_bounded_of_isStable hk M hstab
  -- Step 2: define a, b, c (all explicit; non-negativity / positivity easy).
  set C : ℝ := L * (|M.β 0| * (∑ i : Fin k, |M.α i.succ|)
                    + ∑ i : Fin k, |M.β i.succ|)
                  / (1 - h * L * |M.β 0|) with hC_def
  set Dcoef : ℝ := ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
                     + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
                    * L * M_bound / (1 - h * L * |M.β 0|) with hD_def
  set y'sum : ℝ := ∑ i ∈ Finset.range k,
                     |yPrime k α (fun j : Fin k => ε j.val) i| with hy'sum_def
  set a : ℝ := (Θ + 1) * y'sum + 1 with ha_def
  set b : ℝ := (Θ + 1) * C + 1 with hb_def
  set c : ℝ := (Θ + 1) * Dcoef with hc_def
  refine ⟨a, b, c, ?_, ?_, ?_, ?_, ?_⟩
  · -- 0 ≤ a: use Θ ≥ 0, y'sum ≥ 0 (sum of |·|), `+ 1 ≥ 0`.
    sorry
  · -- 0 < b: `(Θ + 1) * C + 1 ≥ 1 > 0`.
    sorry
  · -- 0 ≤ c: `(Θ + 1) * Dcoef`. Dcoef ≥ 0 from cycle 051.
    sorry
  · -- ∀ n ≥ 1, the recurrence (the main work; ~80 lines).
    intro n hn
    sorry
  · -- |yex x₀ - Y 0| ≤ a (≤ 5 lines).
    sorry
```

---

## Aristotle plan

**Submit ONE batched job at the start of the cycle** for
`globalError_recurrence_form`. The proof is a chain of five
existing helpers; Aristotle's premise selection has a fair shot.

Aristotle prompt (rough sketch — adjust to your usual format):
> Theorem: `∃ a b c, 0 ≤ a ∧ 0 < b ∧ 0 ≤ c ∧ ∀ n ≥ 1, |ε n| ≤ a +
> b·h·k·(Σ_{Ico 1 n} |ε p|) + c·h²·n` where `ε(m) := yex(x₀ + m·h) - Y m`.
> Hypotheses: `M.IsConsistent`, `M.IsStable`, autonomous `f : ℝ → ℝ`
> Lipschitz, `yex ∈ C¹` solving `y' = f(y)`, smallness `h L |β₀| < 1`,
> `M.IsLMMSolution` data.
> Available helpers (all in this file):
> - `globalError_closed_form` (line 2062) gives the θ-decomposition
>   `ε(n) = Σ θ y' + Σ θ ψ`.
> - `theta_bounded_of_isStable` (line 1737) gives `∃ Θ ≥ 0, ∀ n, |θ n| ≤ Θ`.
> - `sum_theta_psi_contraction` (line 1762) bounds `|Σ θ ψ|` by
>   `Θ·C·h·Σ Sε + Θ·D·h²·card`.
> - `globalError_per_step_sum_form` (line 1936) gives `|ε - Σ α ε| ≤
>   bcoef·Σ|ε| + ccoef·h²`.
> - `recentSum_swap_bound` (line 1886) bounds the recent-window sum.

Sleep ~30 min after submission. **Check ONCE.** If Aristotle
returns a clean compile: incorporate. If it fails or times out:
prove manually following the Step 0–9 outline above (~120 lines).

**Do NOT submit `globalError_closed_form_autonomous` to
Aristotle.** It is a one-shot composition; Aristotle would waste
compute.

**Do NOT poll Aristotle more than once.** CLAUDE.md is explicit.

---

## Mathlib lemmas to verify before relying on

Use `lean_local_search` or `lean_loogle` to verify these names:

| Use case | Name | Rough signature |
|---|---|---|
| `Σ_{Icc a b} = Σ_{Ico a (b+1)}` | `Finset.Ico_succ_right` (or `Finset.Icc_eq_Ico`?) | `Ico a (b+1) = Icc a b` |
| `|Σ| ≤ Σ |·|` | `Finset.abs_sum_le_sum_abs` | std |
| `Σ_{range a} ⊆ Σ_{range b}` for `a ≤ b` | `Finset.range_mono` then `Finset.sum_le_sum_of_subset_of_nonneg` | std |
| `Σ_{Ico 0 (n+1)} = Σ_{Ico 0 n} + last_term` | `Finset.sum_Ico_succ_top` | needs `0 ≤ n` |
| `Σ_{Ico 0 n} = u 0 + Σ_{Ico 1 n}` | `Finset.sum_Ico_consecutive` or manual `range_eq_Ico` + split | std |
| `Real.exp_pos`, `Real.exp_continuous` | std | for cycle 054 |

When in doubt, prefer using `lean_multi_attempt` to test names
before committing to them.

---

## What NOT to do this cycle

* **Do NOT close the line-2106 sorry**. Land the autonomous bound
  only; the sorry stays. Closing it requires cycle 054+ (Tendsto)
  and cycle 055+ (non-autonomous generalisation).

* **Do NOT generalise the cycle 045–052 chain to non-autonomous
  `f : ℝ → ℝ → ℝ` this cycle.** That is a multi-cycle refactor.

* **Do NOT introduce `axiom` or `constant`**. Use `b := (Θ + 1) * C + 1`
  to ensure `b > 0` strictly, even if `Θ = 0` (which can't happen
  but the `+ 1` makes it cheap to verify).

* **Do NOT raise `maxHeartbeats`** above 200000. If `nlinarith` or
  `ring_nf` is slow, decompose into smaller `have` steps.

* **Do NOT modify `IsConvergent`** (line 305). The predicate is
  faithful; the difficulty is in the proof.

* **Do NOT cherry-pick a different theorem**. `thm:406D` is the
  current critical path; cycles 045–052 built infrastructure for
  it specifically.

* **Do NOT poll Aristotle more than once** (CLAUDE.md).

* **Do NOT modify `scripts/autonomous_loop.py`**.

* **Do NOT delete the existing `stable_consistent_isConvergent`
  scaffold.** Update its docstring; keep the body's `sorry`.

* **Do NOT include `|ε(n)|` in the Grönwall recent-window sum on
  the RHS**. That would make the recurrence implicit. Peel the
  `i = n` term from the ψ-sum in Step 8 before applying
  `recentSum_swap_bound`.

* **Do NOT try to absorb `|ε(n)|` via a `(1 - hLk) > 0`-inversion**
  inside the recurrence. The `discrete_gronwall_exp_bound` API
  takes the un-inverted form; let it handle the implicit-to-explicit
  conversion via the `(1 + bhk)^n ≤ exp(bhk·n)` step.

---

## Faithfulness check

Two new declarations, neither directly an entity:

* **`globalError_recurrence_form`** (private helper) — not a
  Butcher entity; pure infrastructure for `thm:406D`. Hypothesis
  list matches `globalError_per_step_sum_form` +
  `theta_bounded_of_isStable`. No definition smuggling. The
  conclusion is a discrete-Grönwall recurrence, not a
  re-export of a hypothesis.

* **`globalError_closed_form_autonomous`** (public theorem) —
  partial form of `thm:406D` (entity `thm_406D`). Captures the
  *closed-form bound*, not the textbook Tendsto conclusion. The
  textbook target is `IsConvergent`; this theorem is **not** it,
  but is an analytic core. Document this in the docstring and in
  `cycle_053.md`'s faithfulness section. The autonomous-only
  restriction is a documented divergence; cycle 055+ will
  generalise.

For each declaration, run the standard checklist in
`task_results/cycle_053.md`:

* TAUTOLOGY check: does the conclusion equal a hypothesis? No.
* IDENTITY check: is the proof `exact h`? No — it composes 5
  helpers + Grönwall.
* HYPOTHESIS STRENGTH check: matches Butcher §406D modulo the
  autonomous restriction. The autonomous restriction is documented.
* DEFINITION SMUGGLING check: N/A (no new `def`).
* ABSENT THEOREM check: docstring forward-references cycles
  054+/055+; both are clearly future cycles, not in-file
  promises.

---

## File / line targets

* **Insert `globalError_recurrence_form`** between line 2078
  (end of `globalError_closed_form`) and line 2080 (start of
  `stable_consistent_isConvergent` docstring).
* **Insert `globalError_closed_form_autonomous`** immediately
  after `globalError_recurrence_form` and immediately before the
  `stable_consistent_isConvergent` scaffold.
* **Update the docstring** of `stable_consistent_isConvergent`
  (lines 2080–2101) per Section 3 above. The `sorry` at line
  2106 stays (line number will shift after the insertions).

---

## Done criteria

Before committing:

1. `lake env lean OpenMath/Chapter4/Section404.lean` succeeds.
2. `grep -n 'sorry' OpenMath/Chapter4/Section404.lean | grep -v
   docstring` returns exactly **one** real `sorry` — the
   `stable_consistent_isConvergent` scaffold (line number shifted
   from 2106 by the size of the insertion). The two docstring
   occurrences (lines ~548, ~2099) remain.
3. `lean_verify
   OpenMath.Chapter4.Section404.LinearMultistepMethod.globalError_closed_form_autonomous`
   shows only `[propext, Classical.choice, Quot.sound]`. **No `sorryAx`.**
4. `lean_verify
   OpenMath.Chapter4.Section404.globalError_recurrence_form`
   shows only `[propext, Classical.choice, Quot.sound]`.
5. `extraction/formalization_data/lean_status.json` —
   `thm_406D` stays `partial` (no entity closes this cycle, but
   the autonomous form is documented progress).
6. Write `.prover-state/task_results/cycle_053.md` with all
   sections, including the faithfulness check noting the
   autonomous-only divergence.
7. Commit with message
   `Cycle 053 — globalError_closed_form_autonomous (thm:406D core bound)`.
8. **Verify push landed**: `git rev-parse HEAD origin/Main/Experiments`
   match before declaring success. Cycle 052's worker-side check
   also caught a heartbeat-only diff one last time; the
   verification commands here are the canonical anti-phantom
   ritual.

---

## Suggested cycle 054 hand-off

After cycle 053 lands, cycle 054's natural target is the
**autonomous Tendsto theorem**:

```lean
theorem LinearMultistepMethod.stable_consistent_isConvergent_autonomous
    {k : ℕ} (hk : 0 < k) (M : LinearMultistepMethod k)
    (hstab : M.IsStable) (hcons : M.IsConsistent) :
    /-- non-autonomous-free reformulation of IsConvergent --/
    ∀ (f : ℝ → ℝ) (L : ℝ≥0), LipschitzWith L f →
    ∀ (x₀ y₀ : ℝ) (yex : ℝ → ℝ), yex x₀ = y₀ →
      ContDiff ℝ 1 yex → (∀ t, deriv yex t = f (yex t)) →
      (∃ M_bound, ∀ t, |f (yex t)| ≤ M_bound) →
    ∀ (start : ℝ → Fin k → ℝ),
      (∀ i : Fin k,
        Filter.Tendsto (fun h : ℝ => start h i) (nhds 0) (nhds y₀)) →
    ∀ (x : ℝ), x₀ < x →
    ∀ (Y : ℕ → ℕ → ℝ),
      (∀ m : ℕ, 0 < m →
        (∀ i : Fin k, Y m i.val = start ((x - x₀) / (m : ℝ)) i) ∧
        M.IsLMMSolution ((x - x₀) / (m : ℝ)) x₀
                          (fun _ y => f y) (Y m)) →
      Filter.Tendsto (fun m : ℕ => Y m m - yex x) Filter.atTop (nhds 0)
```

Proof for cycle 054: take `h_m := (x - x₀) / m`, observe
`m · h_m = x - x₀`; apply `globalError_closed_form_autonomous` to
get `|ε(m)| ≤ exp(bk(x-x₀))·a + ...·h_m`; the `a` term involves
starting errors which → 0 by `starting_error_sum_tendsto_zero`
(cycle 049); the `c·h_m/(b·k)` term goes to 0 since `h_m → 0`.
Squeeze gives Tendsto to 0.

Cycle 055+: bridge from autonomous to full non-autonomous
`stable_consistent_isConvergent` (the line-2106 sorry). Likely
requires generalising the cycle 045–052 chain to non-autonomous
`f`; if that becomes too costly, file an issue documenting the
autonomous-as-core stance and accept the partial-formalisation
status for `thm_406D`.
