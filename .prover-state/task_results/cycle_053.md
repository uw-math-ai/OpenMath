# Cycle 053 Results

## Worked on
- New private helper `globalError_recurrence_form` (discrete-Grönwall
  recurrence shape, autonomous IVP).
- New public theorem
  `LinearMultistepMethod.globalError_closed_form_autonomous` (the
  exponential closed-form bound on `|ε(n)|`, autonomous IVP).
- Updated docstring on `LinearMultistepMethod.stable_consistent_isConvergent`
  documenting the autonomous-as-core decomposition (cycles 053/054/055+).
- The `stable_consistent_isConvergent` body itself stays `sorry` per the
  cycle-053 strategy (closure deferred to cycle 055+).

## Approach
Following the strategy's Step 0–9 outline for `globalError_recurrence_form`:

1. Set up `α`, `Cbase`, `Dbase`, `y'sum`, `a`, `b`, `c` via `set` (with
   `a := (Θ + (Θ+1)·Cbase·h·k + 1)·y'sum + 1`, `b := (Θ+1)·Cbase + 1`,
   `c := (Θ+1)·Dbase`).
2. Extracted `Θ ≥ 0` via `theta_bounded_of_isStable` (cycle 047).
3. Established `0 ≤ a`, `0 < b`, `0 ≤ c` and `|yex x₀ - Y 0| ≤ a` from
   `yPrime_of_lt` at index 0 plus `Finset.single_le_sum`.
4. Recurrence proof: case-split on `n < k` vs `n ≥ k`.
   - **`n < k` case:** `Icc k n = ∅`, so the ψ-sum vanishes; closed-form
     reduces to `|ε(n)| ≤ Θ·y'sum ≤ a`.
   - **`n ≥ k` case:** combined cycles 047, 048, 050, 051, 052:
     * `globalError_closed_form` (cycle 052) for the θ-decomposition.
     * Triangle inequality, then bound the y'-sum by `Θ·y'sum`.
     * Split `Σ_{Icc k n} = Σ_{Ico k n} + ψ(n)` via `Finset.Ico_add_one_right_eq_Icc`
       and `Finset.sum_Ico_succ_top` plus `theta_zero = 1` for the peeled
       `i = n` term.
     * Apply `sum_theta_psi_contraction` (cycle 048) to `Σ_{Ico k n}`,
       feeding the per-step pointwise bound from
       `globalError_per_step_sum_form` (cycle 051) via the index-rewrite
       `i - 1 - j.val = i - (j.val + 1)`.
     * Apply `recentSum_swap_bound` (cycle 050) to convert
       `Σ_{Ico k n} Σ_j |ε(i-(j+1))|` into `≤ k · Σ_{Ico 0 n} |ε p|`.
     * Bound the peeled `|ψ(n)|` via the same pointwise bound, then
       `Σ_{j:Fin k} |ε(n-(j+1))| ≤ k · Σ_{Ico 0 n}` (each summand ≤ Stot).
     * Split `Σ_{Ico 0 n} = |ε 0| + Σ_{Ico 1 n}`, bound `|ε 0| ≤ y'sum`,
       and absorb the `(n-k)` h²-term slack into `(Θ+1)·Dbase·h²·n`.
     * Final algebraic chain via `calc` to avoid `linarith` heartbeats.

`globalError_closed_form_autonomous` is a one-line composition of
`globalError_recurrence_form` and `discrete_gronwall_exp_bound` (cycle
046).

No Aristotle job submitted this cycle. Past Aristotle attempts on
similar infrastructure proofs returned `COMPLETE_WITH_ERRORS`; the
proof's structure depends on five private helpers, which would
require packaging substantial context. Manual proof was the more
reliable path.

## Result
SUCCESS.
- `lake env lean OpenMath/Chapter4/Section404.lean` compiles cleanly.
- Sorry count in the file: **1** real sorry (the existing
  `stable_consistent_isConvergent` scaffold at line 2603, retained per
  cycle-053 strategy). The two prior `sorry` text occurrences (lines
  548, 2598) are in docstrings, not tactics.
- `lean_verify` on
  `OpenMath.Chapter4.Section404.LinearMultistepMethod.globalError_closed_form_autonomous`
  returns axioms `[propext, Classical.choice, Quot.sound]` — no
  `sorryAx`, no new axioms. Since `globalError_closed_form_autonomous`
  directly invokes `globalError_recurrence_form` and produces a
  Quot.sound-only axiom set, the private helper is also free of new
  axioms transitively.

## Faithfulness check
For each new declaration introduced this cycle:

### `globalError_recurrence_form` (private helper)
- **Entity ID:** none — pure infrastructure for `thm:406D`, not a
  Butcher entity in the extraction registry.
- Hypothesis list mirrors `globalError_per_step_sum_form` (cycle 051)
  + `theta_bounded_of_isStable` (cycle 047). No definition smuggling
  (no new `def`s, only an existential).
- TAUTOLOGY check: conclusion is an existential `∃ a b c, …
  recurrence …`, not a hypothesis. ✓
- IDENTITY check: proof is a multi-step composition of five helpers
  plus algebraic combination via `calc`, ~250 lines of substantive
  work. Not vacuous. ✓
- HYPOTHESIS STRENGTH: matches the autonomous restriction documented
  in the strategy (autonomous `f : ℝ → ℝ`); same shape as cycles
  045–052 inputs. The `0 < k` is required (theta_bounded_of_isStable
  needs it; same as in cycle 047). The `M.IsConsistent` and
  `M.IsStable` hypotheses are the textbook §406D inputs.
- DEFINITION SMUGGLING: N/A (no new `def`).

### `LinearMultistepMethod.globalError_closed_form_autonomous` (public theorem)
- **Entity ID:** partial form of `thm:406D`
  (`extraction/formalization_data/entities/thm_406D.json`).
- **Textbook statement** (quoted from `thm_406D.json`):
  > "A stable consistent linear multistep method is convergent."
- **Lean statement captures:** different. The autonomous-IVP
  closed-form bound on `|ε(n)|`. The textbook `IsConvergent`
  (Definition 402A) is a Tendsto statement over non-autonomous `f`;
  this theorem produces the analytical inequality that is the
  *core* of the convergence proof, restricted to autonomous `f`.
- **Justification for divergence:** the cycle 045–052 helper chain
  is built for autonomous `f : ℝ → ℝ`. Generalising to non-autonomous
  `f : ℝ → ℝ → ℝ` is a multi-cycle refactor (cycle 055+). The
  autonomous closed-form bound is the analytical core; cycle 054
  will turn it into the autonomous Tendsto theorem; cycle 055+ will
  bridge to the full non-autonomous `IsConvergent`.
- TAUTOLOGY check: conclusion is the exponential bound, not any
  hypothesis. ✓
- IDENTITY check: proof composes `globalError_recurrence_form` with
  `discrete_gronwall_exp_bound`. Real composition. ✓
- HYPOTHESIS STRENGTH: same hypotheses as `globalError_recurrence_form`,
  documented as autonomous restriction.
- DEFINITION SMUGGLING: N/A (no new `def`).
- ABSENT THEOREM: the docstring forward-references cycles 054+ /
  055+ (`stable_consistent_isConvergent_autonomous` and the
  non-autonomous bridge). Both are clearly future-cycle targets,
  not in-file promises. ✓

## Dead ends
1. **`set` definitions causing heartbeat timeouts** — initial draft
   stored `Stot, Srec` via `set`, and the final `linarith [...]`
   chain with many opaque definitions hit the 200000-heartbeat
   ceiling. Fixed by replacing the final combine step with a
   three-stage `calc` chain. Lesson: `linarith` with 4+ `set`
   definitions in the hypotheses needs to be split into discrete
   steps.

2. **`Finset.Ico_succ_right` does not exist as a Finset lemma** —
   the strategy suggested this name, but it's only in `Set` /
   `Order.SuccPred`. The Finset version is
   `Finset.Ico_add_one_right_eq_Icc` (in
   `Mathlib/Algebra/Order/Interval/Finset/SuccPred.lean`).

3. **`Finset.range_subset` was renamed to `Finset.range_subset_range`**
   — the iff form `range a ⊆ range b ↔ a ≤ b` lives at the latter
   name in current Mathlib.

4. **`abs_add` is not the public Mathlib name** — the canonical
   non-private name is `abs_add_le`.

5. **`refine (Finset.sum_le_sum (fun i _ => ?_)).trans ?_`** —
   this confuses the elaborator (can't synthesise `g` in the
   chain). Restructured as a separate `have h_per` then
   `refine (Finset.sum_le_sum h_per).trans ?_`.

6. **`Finset.single_le_sum (f := fun p => …)`** — required explicit
   `(p : ℕ)` annotation, otherwise Lean inferred `p : ℝ`.

## Discovery
The "set + linarith" combination has a hidden cost: each `set`
definition is a let-binding the elaborator must navigate. With ~10
`set`s (Cbase, Dbase, y'sum, a, b, c, Stot, Srec, ψfn, α) and a
non-trivial inequality, `linarith` runs out of heartbeats. The
mitigation is a `calc` chain with explicit intermediate goals — each
step's `linarith` then has only 2–3 hypotheses to combine. This is
a portable lesson for cycle 054 (which will compose this bound with
limit-of-h reasoning).

The contraction lemma's `θ` parameter signature `ℕ → ℝ` plus the
`hθ : ∀ i, |θ i| ≤ Θ` shape required passing `theta k α` (the LMM-α
specialisation) and `hΘ` (which has the same shape via `set α`'s
definitional equality). This worked smoothly without an explicit
`hΘ' : ∀ n, |theta k α n| ≤ Θ` rewrite.

The `n ≥ k` case's "peel `i = n`" trick (using `theta_zero = 1`)
neatly side-steps the implicit-recurrence trap that the strategy
flagged: the closed form's `Σ_{Icc k n}` includes the `i = n` term
which would otherwise route `|ε(n)|` back into the recurrence's RHS.
Peeling lets the contraction operate on `Σ_{Ico k n}` cleanly, and
the `|ψ(n)|` peeled term is bounded directly via the per-step bound.

## Suggested next approach
**Cycle 054 target:** turn `globalError_closed_form_autonomous` into
the autonomous-IVP Tendsto theorem
`stable_consistent_isConvergent_autonomous`. Concretely:

* For each step size `h_m := (x - x₀) / m`, observe `m · h_m = x - x₀`.
* Apply `globalError_closed_form_autonomous` at `n = m` and `h = h_m`
  to get `|ε(m)| ≤ exp(b·k·(x-x₀))·a + (exp(b·k·(x-x₀)) - 1) · c·h_m/(b·k)`.
* The exponential factor is bounded uniformly in `m` (since
  `m · h_m = x - x₀` is constant).
* The `a` term involves starting errors via `y'sum`; route
  `starting_error_sum_tendsto_zero` (cycle 049) to show this → 0
  as `m → ∞` (i.e. `h_m → 0`).
* The `c·h_m/(b·k)` term goes to 0 since `h_m → 0`.
* Squeeze theorem yields `Tendsto (fun m => Y_m m - yex x) atTop (𝓝 0)`.

The non-autonomous generalisation (cycle 055+) is the residual gap
to the textbook `IsConvergent` predicate.

**Aristotle plan for cycle 054:** the squeeze argument is largely
analytic (`Filter.Tendsto`, `Real.exp_pos`, `mul_le_one`, `Squeeze`).
A self-contained version of the Tendsto step might be reasonable
to submit, but the heavy infrastructure work for `thm:406D` is now
complete.
