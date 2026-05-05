# Issue: Strengthened hypotheses required for `aux_515D_output_tendsto`

## Blocker

Composing the body of `aux_515D_output_tendsto` (currently a single
`sorry` at `OpenMath/Chapter5/Section515.lean:1599`) by chaining
the three new sub-lemmas

* `aux_515D_per_step_recurrence` (sorry — submitted to Aristotle)
* `aux_515D_gronwall_bound` (sorry — submitted to Aristotle)
* `aux_515D_squeeze` (closed cycle 112)

requires invoking `GeneralLinearMethod.localStepError_bound`
(`Section515.lean:1183`) at each iteration step. That lemma takes
hypotheses NOT currently present on `aux_515D_output_tendsto`'s
signature.

## Required strengthening

The following hypotheses must be added to `aux_515D_output_tendsto`'s
signature when its body is composed in cycle 113+ (and propagated
up to the capstone `stable_consistent_isConvergent`):

| Hypothesis | Source / why needed |
|---|---|
| `hyex_C1 : ContDiff ℝ 1 yex` | `localStepError_bound`'s `_hy_C1` |
| `hM_nn : 0 ≤ M_bound` | `localStepError_bound`'s `_hM` |
| `hyex_M : ∀ t, |yex t| ≤ M_bound` | `localStepError_bound`'s `_hy_M` |
| `hyex'_LM : ∀ t, |deriv yex t| ≤ L * M_bound` | `localStepError_bound`'s `_hy'_LM` |
| `h_norm : ‖((x - x₀) * L) • M.A.map (·\|·\|)‖ < 1` | `localStepError_bound`'s `_h_norm` (Frobenius) |

(The hypotheses `_hVu`, `_hUu`, `_hCons_eq` are already supplied via
the consistency extraction at the capstone level.)

## Faithfulness analysis

Butcher's textbook statement (thm:515D, p. 417) says merely
"a stable and consistent general linear method is convergent." The
extra five hypotheses above are NOT in the textbook statement.

Per-hypothesis derivability from the original `IsConvergent`
hypotheses (which supply: `f`, `L`, `hf_lip`, `x₀`, `y₀`, `yex`,
`yex x₀ = y₀`, `∀ x, HasDerivAt yex (f (yex x)) x`) on the compact
interval `[x₀, x]`:

* `hyex_C1`: derivable. `HasDerivAt yex (f (yex x)) x` for all `x`
  + Lipschitz `f` + `Continuous yex` (from differentiability)
  ⇒ `Continuous (deriv yex)` ⇒ `ContDiff ℝ 1 yex` (on ℝ;
  cf. `ContDiff.of_succ_iff_deriv` and friends).
* `hM_nn`, `hyex_M`: derivable on the *compact interval* `[x₀, x]`
  because `Continuous yex` on a compact set is bounded, with
  `M_bound := sSup ((fun t => |yex t|) '' Icc x₀ x)`. **But** the
  current `M_bound` formulation is on the *whole real line* — for
  the §515 proof to use a global bound, we must restrict
  `localStepError_bound` to the compact-interval setting (a known
  textbook tacit assumption).
* `hyex'_LM`: derivable from `hyex_M` + `hf_lip` + the ODE
  identity `deriv yex t = f (yex t)`: `|deriv yex t| = |f (yex t)|
  ≤ |f (yex t) - f 0| + |f 0| ≤ L · |yex t| + |f 0| ≤ L · M_bound +
  |f 0|`. So we'd need to refactor to take `M_bound' := L * M_bound
  + |f 0|` or to absorb `|f 0|` into the constant.
* `h_norm`: NOT derivable. This is a *new* condition imposed by the
  Frobenius-norm contraction argument used in `localStepError_bound`'s
  proof (cycle 107 strengthening). Butcher's proof uses the weaker
  ‖A‖_∞ < 1 condition; we propagate the stronger Frobenius condition.

## Precedent

This faithfulness divergence pattern follows:

* `is_convergent_strengthened.md` — LMM-side `IsConvergent`
  strengthening.
* `glm_isconvergent_strengthened.md` — cycle 098 GLM-side
  `IsConvergent` strengthening (added stage-limit clause).
* Cycle 107's `lem:515B` Frobenius hypothesis on
  `localStepError_bound` propagated to `lem:515D`.

The faithfulness divergence is *acceptable* per these precedents
provided it is documented and a future cycle attempts to weaken or
remove it (deriving the missing hypotheses from compactness +
continuity).

## What was tried (cycle 112)

* Opened the 3-sub-lemma scaffold (A, B, C) without modifying
  `aux_515D_output_tendsto`'s signature. Body remains a single
  `sorry` referencing the three sub-lemmas via this issue file.
* Closed sub-lemma C (squeeze) manually — `aux_515D_squeeze`.
* Submitted A and B to Aristotle (project IDs in
  `.prover-state/aristotle_submissions/cycle_112/README.md`).

## What was tried (cycle 113)

* Polled Aristotle once: both sub-lemma A
  (`aux_515D_per_step_recurrence`) and sub-lemma B
  (`aux_515D_gronwall_bound`) returned COMPLETE.
* Incorporated Aristotle's proofs verbatim, with hypothesis-name
  rename from `_h*` (cycle 112 scaffold) to `h*` (since the proof
  bodies reference them).
* Sub-lemma B required two new private helpers:
  `aux_515D_one_add_pow_le_exp` and `aux_515D_discrete_gronwall_raw`.
* Capstone signature **not** strengthened — body composition
  remains deferred to cycle 114 with all three sub-lemmas now
  available.

The capstone signature is intentionally NOT strengthened this cycle
because:
1. The body of `aux_515D_output_tendsto` is still `sorry`, so the
   strengthening would not actually be consumed.
2. Strengthening the capstone now risks cascade compile failures
   in dependent files; the change is more conservatively done in
   the same cycle as the body composition.

## Possible solutions

1. **Cycle 114**: A + B + C now closed (cycle 113); compose the
   body using all three, strengthen helper + capstone signatures
   together, document the divergence.
2. **Cycle 115+**: weaken the helper signature by deriving the
   missing hypotheses on the compact interval `[x₀, x]` from
   `IsConvergent`'s base hypotheses. This is the
   faithfulness-restoring move.
3. **Block on Mathlib**: if a cleaner Mathlib API emerges for
   "C¹ on compact interval ⇒ bounded derivative", switch to it.

## Cycle 113 audit (this run, labeled "Cycle 114" by the planner)

**Outcome**: deferred body composition; identified §514 cascade
blocker; landed M-matrix-based `ell_U/phi_A` constructor helper as
infrastructure for cycle 115+ body composition.

**Key audit finding**: the strategy's recommended strengthening of
`IsConvergent` with `(∀ t, |yex t| ≤ M_bound)` cannot be
straightforwardly cascaded to §514, because §514's
`convergence_witness_satisfies_U` (Section514.lean:496) applies
`IsConvergent` to the trivial IVP `yex = id` (which is unbounded).
By the autonomous-ODE constraint `deriv yex = f ∘ yex` plus
globally-Lipschitz `f`, all non-constant `yex` are generically
unbounded — so `IsConvergent` becomes vacuously inapplicable to
any §514-style witness-extraction IVP.

See `cycle_113_isconvergent_strengthening_514_blocker.md` for the
full analysis and four candidate solutions (localize bound to
`[x₀, x]`, replace `yex = id` with a smooth bounded function,
derive bounds locally inside the capstone, or accept §514 regression).

**Per-hypothesis cycle-115+ derivability** (re-confirmed):

* `hyex_C1`: derivable globally from `hyex_ode` + Lipschitz `f` ⇒
  `Continuous (deriv yex)` ⇒ `ContDiff ℝ 1 yex`. No localization
  needed.
* `hM_nn`, `hyex_M`: NOT derivable globally for `yex = id`.
  Localizable to `Set.Icc x₀ x` via continuity + compactness.
  Requires `localStepError_bound` refactor to consume compact-
  interval bounds.
* `hyex'_LM`: same compact-interval restriction needed.
* `h_norm`: NOT derivable as written (the strategy's `((x - x₀) * L)`
  form). Derivable by choosing `h₀ := min (x - x₀, threshold)` for
  small `threshold`, since the iteration's `h_n = (x - x₀)/n` is
  eventually `< threshold`. The strategy's strict form is overly
  restrictive — relax to `∃ h₀ > 0, h_n ≤ h₀ eventually ∧
  ‖h₀ • (L * |A|)‖ < 1`.

**Cycle 113 forward step**: built `aux_515D_construct_ell_U_phi_A`
(Section515.lean, near `aux_515D_output_tendsto`), which constructs
`ell_U` and `phi_A` satisfying the `localStepError_bound`
side-conditions from M-matrix infrastructure. This is the
load-bearing primitive for cycle 115's body composition once the
signature question is resolved.

## Cycle 114 update

**`aux_515D_construct_ell_U_phi_A` is now CLOSED** (cycle 114).

- The helper landed in `OpenMath/Chapter5/Section515.lean` between
  `aux_515B_eta_contraction` (line 1136) and the `localStepError_bound`
  docstring (line 1138).
- Verified by axiom-clean compile of `test_aux_515D.lean`
  (scratch sandbox, untracked) — exit code 0, ~21 minutes
  (slow due to `import Mathlib` on GPFS-backed olean cache).
- The proof is a direct M-matrix inversion of `(I − h₀ L |A|)`
  via `Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one` (cycle
  106) plus `Ring.mul_inverse_cancel` for the linear-system
  recovery, following the cycle 107 plumbing pattern from
  `aux_515B_eta_contraction`.

**Body composition status**: still deferred to cycle 115. The
helper alone does not unblock the body of `aux_515D_output_tendsto`
— the §514 cascade conflict (see
`cycle_113_isconvergent_strengthening_514_blocker.md`) must be
resolved first. The helper IS the load-bearing primitive that
cycle 115's body composition will consume after the cascade
question is resolved (Solution A: localize `M_bound` to
`Set.Icc x₀ x`).

## Cycle 116 update — Solution A LANDED (Phase 2)

**Strengthening LANDED.** Both `localStepError_bound`'s capstone
signature (`Section515.lean:1355`) and
`GeneralLinearMethod.IsConvergent` (`Section512.lean:171`) now
expose the four localized hypotheses required for body composition:

| Hypothesis (now in `IsConvergent` and `aux_515D_output_tendsto`) |
|---|
| `(M_bound : ℝ) (hM_nn : 0 ≤ M_bound)` |
| `(hyex_C1 : ContDiff ℝ 1 yex)` |
| `(hyex_M : ∀ t ∈ Set.Icc x₀ x, |yex t| ≤ M_bound)` |
| `(hyex'_LM : ∀ t ∈ Set.Icc x₀ x, |deriv yex t| ≤ (L : ℝ) * M_bound)` |
| `(h_norm : ‖((x - x₀) * L) • A.map abs : Matrix‖_F < 1)` |

`aux_515D_output_tendsto` (`Section515.lean:1836`) inherits the
same hypotheses; its body still has one `sorry` (cycle 117
deliverable).

**§513 / §514 cascade verification (cycle 116)**:

- §513 (`convergent_isStable`): clean migration. `yex ≡ 0, L = 0`
  ⇒ all four localized clauses trivial; Frobenius contraction
  reduces to `‖0‖_F < 1`.
- §514 (`convergence_witness_satisfies_U` and dependents): used
  Solution-A option (b) fallback. Changed `LipschitzWith 0 f` to
  `LipschitzWith 1 f` (any L ≥ 1 works for `yex = id`); discharged
  the four localized clauses inline; propagated the Frobenius
  obligation `‖A.map abs‖_F < 1` as a hypothesis to
  `convergence_witness_satisfies_U`,
  `convergent_isPreconsistent`, and
  `convergent_preconsistent_isConsistent`.

**What's needed for cycle 117**: compose the body of
`aux_515D_output_tendsto` using:

1. `aux_515D_construct_ell_U_phi_A` (cycle 114) — supplies
   `ell_U`, `phi_A`.
2. `localStepError_bound` (cycle 116 strengthened) — applied
   per step at `xn1 := x₀ + m · (x-x₀)/n`, `h := (x-x₀)/n`.
3. `aux_515D_per_step_recurrence` (cycle 113) — chains the
   per-step bounds.
4. `aux_515D_gronwall_bound` (cycle 113) — closed form.
5. `aux_515D_squeeze` (cycle 112) — extracts `δ → 0`.
6. `aux_515D_stage_eventually_bounded` (cycle 111) +
   `aux_515D_stage_tendsto` (cycle 110) — stage-side limit.

The localization restriction `Set.Icc x₀ x` ⊇ `Set.uIcc xn1 (xn1 + h)`
for each step (since `xn1 ∈ [x₀, x - h]` and `xn1 + h ≤ x`), so the
hypotheses transfer cleanly via `Set.uIcc_subset_Icc`-style lemmas.

Cycle 116 also submitted Aristotle Job 1 (project
`9ef8f033-59d5-4557-b040-cf327e6a7063`) attempting the body
composition independently. Cycle 117 will check the result.

## Cycle 117 update — body composed via decomposition fallback

**Outcome**: body of `aux_515D_output_tendsto` lands; ONE new sorry
remains in the cycle 117 stub helper.

* Aristotle Job 1 single-poll: `IN_PROGRESS / 23%` at
  2026-05-05 ~07:50 UTC. Per CLAUDE.md (do NOT re-poll), treated as a
  miss. Manual composition path executed.
* Decomposition fallback as recommended by the cycle 117 strategy:
  introduced ONE new private helper
  `aux_515D_componentwise_deviation_tendsto_zero`
  (`OpenMath/Chapter5/Section515.lean`, just above
  `aux_515D_output_tendsto`'s docstring) with hypotheses identical
  to `aux_515D_output_tendsto`'s and conclusion
  ```
  ∀ i : Fin r, Filter.Tendsto
    (fun n : ℕ =>
      Y n n i - (u i * yex x + v i * ((x - x₀) / n) * deriv yex x))
    Filter.atTop (nhds 0)
  ```
  Body remains `sorry` — the genuine discrete-Grönwall analysis
  (per-step recurrence → closed form → squeeze) is encapsulated here
  for cycle 118.
* Body of `aux_515D_output_tendsto` is a clean ~30-LOC composition:
  1. `rw [tendsto_pi_nhds]; intro i`
  2. invoke `aux_515D_componentwise_deviation_tendsto_zero` to get
     the deviation tendsto
  3. derive `(x - x₀) / n → 0` from
     `tendsto_one_div_atTop_nhds_zero_nat`
  4. derive `v i * ((x - x₀) / n) * deriv yex x → 0` via
     `Tendsto.const_mul` + `Tendsto.mul_const`
  5. add the three tendsto's (`hdev + hVterm + tendsto_const_nhds`)
     with `Tendsto.add` and unify the limits via `simpa`
  6. close with `Tendsto.congr (fun n => by ring)` to rewrite the
     summed function back to `Y n n i`.
* Build OK (`lake build OpenMath.Chapter5.Section515` — 8.9s
  re-elaborate after dependencies, 1m 19s wall). Single `sorry`
  warning at line 1873 (the deviation helper).
* `#print axioms` of
  `OpenMath.Chapter5.Section510.GeneralLinearMethod.stable_consistent_isConvergent`
  returns `[propext, sorryAx, Classical.choice, Quot.sound]` — the
  `sorryAx` traces solely to
  `aux_515D_componentwise_deviation_tendsto_zero`.
* `lean_status.json` row for `thm:515D` updated to cycle 117; status
  remains `partial` per cycle 117 strategy ("update to `formalized`
  ONLY if `aux_515D_output_tendsto` is fully closed").
* `plan.md` §515 row updated.

**What's needed for cycle 118**: close
`aux_515D_componentwise_deviation_tendsto_zero`. The cycle 117
strategy's Steps 1–9 outline applies directly:
1. (within the helper) introduce `Δx`, `Lr` constants.
2. apply `aux_515D_construct_ell_U_phi_A` once.
3. derive `α`, `β` from M.B / M.A constants and the M-matrix outputs.
4. set up the deviation `δ : ℕ → ℕ → ℝ` (max-abs over `Fin r`).
5. for each `n > 0`, iterate `localStepError_bound` across
   `m = 0, …, n-1` and bound each `K i` to derive the per-step
   inequality `δ n (m+1) ≤ V_norm·δ n m + α·h_n·δ n m + β·h_n²`.
6. apply `aux_515D_per_step_recurrence` to get the closed-form
   `(V_norm + α·h_n)^m`-bound.
7. apply `aux_515D_gronwall_bound` to convert to exp-form.
8. show `δ n 0 → 0` from `_hφ` (the `(x-x₀)/n → 0` composed with
   per-component `_hφ i`).
9. apply `aux_515D_squeeze` to conclude `δ n n → 0`.
10. (final): convert max-abs deviation tendsto-zero to per-component
    tendsto-zero via `Finset.sup'`-style bound; this is the simplest
    step and just unfolds `δ`'s definition.

The helper is a viable Aristotle Job 2 candidate if cycle 118
manual composition stalls — submit with the abstract-axioms pattern
from cycle 116.

## Cycle 119 update — Backup B1 second iteration

**Outcome**: cycle 119's `aux_515D_max_deviation_bound_tendsto_zero`
body is now **fully closed** via composition with a new narrower
helper `aux_515D_max_deviation_geometric_bound`
(`OpenMath/Chapter5/Section515.lean:1819`). Net delta: the cycle 118
sorry moves from `aux_515D_max_deviation_bound_tendsto_zero`
(line 1854 prior) to `aux_515D_max_deviation_geometric_bound`
(line 1854 now — the new helper). Sorry count remains 1; locus
narrows to a focused geometric-bound existential.

**New helper signature (cycle 119 narrower)**:

```
∃ C_init C_lin : ℝ, 0 ≤ C_init ∧ 0 ≤ C_lin ∧
  ∀ n : ℕ, 0 < n →
    sup'_i |Y n n i - target_i n|
      ≤ C_init · sup'_j |Y n 0 j - initial_target_j n|
        + C_lin · ((x - x₀) / n)
```

This isolates the discrete-Grönwall closed-form output (the 200-400
LOC analytical core gated by:
1. M-matrix `(I − h₀L|A|)`-inversion to construct `ell_U`, `phi_A`.
2. Per-step `localStepError_bound` chained across `m = 0, …, n-1`.
3. Vector-typed iterated-V bound (the cycle 118 stall point — see
   `.prover-state/issues/aux_515D_iterated_V_bound.md`).
4. Geometric closed-form via `aux_515D_per_step_recurrence` +
   `aux_515D_one_add_pow_le_exp`).

**Cycle 118 helper's body composition** (cycle 119, fully verified):

1. Apply `aux_515D_max_deviation_geometric_bound` to extract
   `C_init`, `C_lin` and the geometric bound `hbound`.
2. Define `h_n n := (x − x₀) / n` and the initial-deviation sup'
   `δ_init n := sup'_j |Y n 0 j − (u_j · y₀ + v_j · h_n · yex'(x₀))|`.
3. Define `δ_seq n := if n > 0 then C_init · δ_init n + C_lin · h_n n
   else 0`.
4. Prove `δ_seq n ≥ 0` by case split on `n > 0`.
5. Prove `δ_init → 0` per-component via `_hφ ∘ (h_n → 0)` plus
   `_hyex_x₀` bridging, then squeeze sup' below the finite sum
   (`squeeze_zero` + `tendsto_finset_sum`).
6. Prove `δ_seq → 0` via `(C_init · δ_init + C_lin · h_n)`'s
   add-of-tendsto and `Tendsto.congr'` on the eventual filter.
7. Prove the bound clause via `Finset.le_sup'` (per-component ≤ sup')
   + `hbound`.
8. Edge case `r = 0`: `Fin r` empty, bound vacuous, pick
   `δ_seq := fun _ => 0`.

**Status of `thm:515D`**: still `partial` (one sorry remains, in
the new helper). `lean_status.json` cycle reference bumped to 119.
Per cycle 119 strategy Priority 2: "If only partially closed
(Backup plan B1 executed): Update only the cycle-118-update note in
this file to point at the new narrower helper. Leave
`lean_status.json` `thm:515D` as `partial`. Plan.md row stays `[~]`."

**What's needed for cycle 120**: close
`aux_515D_max_deviation_geometric_bound`. The Backup B1 helper
isolates the genuine discrete-Grönwall analytical content. The path
forward (cycle 119 strategy Priority 1 outline, sidesteps cycle 118's
per-step ↔ Grönwall bridge):
1. Apply `aux_515D_construct_ell_U_phi_A` (cycle 114) with `h₀ := x − x₀`.
2. Derive `α`, `β` constants from `M.B`, `ell_U`, `phi_A`.
3. For each `n > 0`, set up the per-step recurrence on `δ_per_n n m`
   via `localStepError_bound` (cycle 116 strengthened) per-step.
4. Apply `aux_515D_per_step_recurrence` (cycle 113) for closed form.
5. Bound `(V_inf_norm + α·h)^n` via `aux_515D_one_add_pow_le_exp` +
   stability constant from `_hStab` (the iterated-V-bound piece).
6. Sum via geometric series + take the sup'.

The cycle 119 strategy explicitly authorizes this Backup B1
narrowing as the fallback. The new helper is documented with the
composition recipe in its docstring.

## Cycle 120 update

Cycle 120 closed Path A of `.prover-state/issues/aux_515D_iterated_V_bound.md`
by introducing and proving the new helper
`aux_515D_iterated_V_bound` at
`OpenMath/Chapter5/Section515.lean:1854`. This is the
"iterated-V-bound piece" referenced in step 5 above.

**Sorry-count delta this cycle**: −0 net (one helper added with full
proof; the geometric_bound sorry remains at the new location
`Section515.lean:1961`). The advance is structural rather than
numeric: the iterated-V infrastructure is now available for cycle
121's geometric_bound body composition.

**Status of `thm:515D`**: still `partial`. The sorry at the
geometric_bound is now armed with `aux_515D_iterated_V_bound` for
the iterated-V piece, narrowing cycle 121's composition target.

**What's needed for cycle 121**: close the body of
`aux_515D_max_deviation_geometric_bound`. The composition recipe
above (steps 1–6) is now fully resourced:
* Step 5's iterated-V piece is `aux_515D_iterated_V_bound` (cycle 120).
* Step 1's M-matrix piece is `aux_515D_construct_ell_U_phi_A` (cycle 114).
* Step 4's closed-form piece is `aux_515D_per_step_recurrence` (cycle 113).
* Step 3's per-step bound is `localStepError_bound` (cycle 116
  strengthened).

**Open faithfulness divergence (carried forward from cycle 119
strategy)**: `aux_515D_construct_ell_U_phi_A` requires
`0 ≤ M.glmAbscissae v` as a hypothesis. Cycle 119 confirmed this is
NOT derivable from `IsConsistent`. Cycle 121 must decide whether to
propagate `0 ≤ c` upward (high risk for §513 / §514 cascade integrity
per Backup B3 of cycle 120 strategy) or accept it as a local
hypothesis with documented divergence.
