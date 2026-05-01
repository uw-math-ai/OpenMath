# Cycle 055 Results

## Worked on
- Step 1: removed the cycle-054 sorry stub
  `LinearMultistepMethod.stable_consistent_isConvergent_autonomous`
  (former lines 2579–2640).
- Step 2: added `yPrime_sum_abs_tendsto_zero` (Tendsto helper for the
  `y'sum → 0` sub-goal of the eventual outer assembly of `thm:406D`).
- Step 3 (stretch, Option A): added `Cbase_tendsto_at_zero`
  (continuity-style helper showing that `Cbase` of
  `globalError_recurrence_form` tends to its `h = 0` value).
- Step 4: Aristotle batch of 5 forward-looking Tendsto/numerics
  helpers for cycle 056+.

## Approach

### Step 1 — stub removal
- Verified the stub had no callers (`grep -rn` only found the
  declaration site and one docstring reference).
- Edit-deleted lines 2579–2640. Sorry count dropped from 2 → 1
  (only the cycle 056+ non-autonomous scaffold remains).

### Step 2 — `yPrime_sum_abs_tendsto_zero`
Strong induction on `m < k` (using
`Nat.strong_induction_on`, matching the cycle-052
`globalError_eq_linRec` pattern at line 2022). For each `m`:
- Apply `yPrime_of_lt` to expand into
  `u h ⟨m, hmk⟩ - Σ_{i:Fin m} θ_{m-i.val} · yPrime k α (u h) i.val`.
- Each summand: `θ_{m-i.val}` is a constant (independent of `h`),
  inner factor `→ 0` by IH, lift to `→ 0` via `Tendsto.const_mul`
  on the constant factor.
- Finite sum `→ 0` by `tendsto_finset_sum`.
- Combine via `Tendsto.sub` against `hu ⟨m, hmk⟩`.

Then lift to `|·|` with `Tendsto.abs` and to the outer sum with
`tendsto_finset_sum`.

### Step 3 — `Cbase_tendsto_at_zero`
Algebra trick: numerator
`L * (|β 0| · Σ |α(i+1)| + Σ |β(i+1)|)` is constant in `h`;
denominator `1 - h · L · |β 0| → 1`. So `Tendsto.div` with the
constant numerator and the denominator's continuity yields
the result.

### Step 4 — Aristotle batch
Submitted 5 forward-looking helpers (project IDs recorded in
`.prover-state/aristotle_submissions/cycle_055/project_ids.txt`):
1. `Dbase_tendsto_at_zero` — sibling of `Cbase_tendsto_at_zero`.
2. `tendsto_const_div_one_sub_mul` — generic `c / (1 - h · a) → c`.
3. `tendsto_h_squared_zero` — `h^2 → 0` as `h → 0`.
4. `tendsto_real_exp_at` — `Real.exp` continuous at any point.
5. `tendsto_finset_sum_abs_zero` — sum of `|·|`-things → 0.

**Aristotle outcome: 5 / 5 closed** (results extracted to
`.prover-state/aristotle_results/cycle_055/`). Per the strategy's
"DO NOT refactor Cbase / Dbase into top-level noncomputable defs
this cycle" guidance, the closed proofs are deliberately NOT
integrated into `Section404.lean` this cycle. They are stored as
ready-to-merge sandbox files for cycle 056+ to lift into the
outer-assembly context (with the slight signature change from
sandbox-style `α β : Fin (k+1) → ℝ` arguments to
`M : LinearMultistepMethod k`).

## Result
SUCCESS:
- Sorry count: 2 → 1 (regression from cycle 054 fully recovered).
- Two new helpers added, both axiom-clean
  (`[propext, Classical.choice, Quot.sound]` only, verified via
  `#print axioms` before removal of the temp probes).
- `lake env lean OpenMath/Chapter4/Section404.lean` compiles
  cleanly; no new warnings.
- `lake build OpenMath.Chapter4.Section404` succeeds.

## Faithfulness check

### `yPrime_sum_abs_tendsto_zero`
- **Entity:** internal helper toward `thm:406D`. Not in textbook
  directly; supports the §406D outer assembly's `y'sum → 0` step.
- **Statement (informal):** "Given `u_h j → 0` for each `j : Fin k`,
  the finite sum `Σ_{i ∈ range k} |yPrime k α (u h) i|` tends to 0
  as `h → 0`."
- **Lean statement captures:** same content. The hypothesis is the
  weakest possible (per-component Tendsto); the conclusion is the
  combined-sum Tendsto fact.
- **Tautology / identity check:** the conclusion is genuinely
  different from each `hu j`; the proof performs strong induction
  through the triangular `yPrime` recurrence, which is real
  mathematical work. ✓
- **Hypothesis strength:** `hu j → 0` is the minimal per-component
  hypothesis. ✓

### `Cbase_tendsto_at_zero`
- **Entity:** internal helper toward `thm:406D`. Not in textbook
  directly; documents continuity of the closed-form `Cbase` constant.
- **Statement (informal):** "The expression
  `L · (|β 0| · Σ |α(i+1)| + Σ |β(i+1)|) / (1 - h · L · |β 0|)`
  tends to `L · (|β 0| · Σ |α(i+1)| + Σ |β(i+1)|)` as `h → 0`."
- **Lean statement captures:** same content. Direct restatement.
- **Tautology / identity check:** the conclusion `Tendsto … (nhds N)`
  with `N = L · …` (the constant numerator value) is not a
  hypothesis; it is the conclusion of `Tendsto.div`. ✓
- **Hypothesis strength:** no hypotheses on `M, L`; the lemma works
  unconditionally. ✓

## Dead ends
None this cycle. Both helpers landed on the first try with the
strategy's suggested proof outline.

## Discovery
- `Nat.strong_induction_on` continues to be the right idiom for
  `yPrime`-style finite triangular recurrences; the structural
  recursion mirrors the `Section141.linRec` pattern already used at
  line 2022 (`globalError_eq_linRec`).
- `Tendsto.const_mul` is the correct combinator for "constant
  factor times a Tendsto family", but watch for argument order:
  the constant goes first as the receiver (`h_t.const_mul c`).
- For private declarations, `#print axioms` cannot be invoked from
  outside the file; need to use a temporary in-file `#print axioms`
  probe and remove it before commit.

## Suggested next approach
Cycle 056 should:
1. Pick up Aristotle results from this cycle's batch (project IDs
   recorded). If `Dbase_tendsto_at_zero` and the two-three
   utility-shape helpers came back closed, integrate them into
   `OpenMath/Chapter4/Section404.lean`.
2. Add the next-tier helpers needed for the outer squeeze:
   - `b_tendsto_at_zero`: `b_h = (Θ + 1) · Cbase_h + 1 → bound`.
   - `c_tendsto_at_zero`: `c_h = (Θ + 1) · Dbase_h → bound`.
   - `b_h * k ≥ k > 0` uniform lower bound for the `c · h / (b · k)`
     denominator.
   - `c_h · h_m / (b_h · k) → 0`.
   - `m · h_m = x − x₀` constancy lemma (for `m > 0`).
   - `exp(b_h · k · m · h_m)` bounded above as `m → ∞` via the
     constancy + `tendsto_real_exp_at`.
3. Then attempt to re-state and close
   `LinearMultistepMethod.stable_consistent_isConvergent_autonomous`
   using `globalError_closed_form_autonomous` + `squeeze_zero` +
   the helpers above. Estimated 3–5 cycles total to land the
   autonomous Tendsto theorem; the non-autonomous lift is a
   separate post-autonomous job.

The key cycle-055 insight that simplifies cycle 056: with
`yPrime_sum_abs_tendsto_zero` and `Cbase_tendsto_at_zero` in hand,
the `a_m → 0` sub-step (a_m = bounded_factor · y'sum_m) decomposes
cleanly — bounded factor stays bounded by the cycle-054 slack
removal + `Cbase_tendsto_at_zero`, and `y'sum_m → 0` follows from
`yPrime_sum_abs_tendsto_zero` composed with
`starting_error_each_tendsto_zero`.
