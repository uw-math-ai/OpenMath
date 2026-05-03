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

The capstone signature is intentionally NOT strengthened this cycle
because:
1. The body of `aux_515D_output_tendsto` is still `sorry`, so the
   strengthening would not actually be consumed.
2. Strengthening the capstone now risks cascade compile failures
   in dependent files; the change is more conservatively done in
   the same cycle as the body composition.

## Possible solutions

1. **Cycle 113**: incorporate Aristotle results for A and B,
   compose the body using A + B + C, strengthen helper +
   capstone signatures together, document the divergence.
2. **Cycle 114+**: weaken the helper signature by deriving the
   missing hypotheses on the compact interval `[x₀, x]` from
   `IsConvergent`'s base hypotheses. This is the
   faithfulness-restoring move.
3. **Block on Mathlib**: if a cleaner Mathlib API emerges for
   "C¹ on compact interval ⇒ bounded derivative", switch to it.
