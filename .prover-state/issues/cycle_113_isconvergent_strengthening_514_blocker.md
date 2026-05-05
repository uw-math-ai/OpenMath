# Issue: `IsConvergent` strengthening with `M_bound` conflicts with §514's `yex = id` consumer

## Blocker

The cycle 114 strategy (loaded as cycle 113's strategy) calls for
strengthening `GeneralLinearMethod.IsConvergent` (Section512.lean:150)
with five hypotheses required by `localStepError_bound`:

```lean
∀ M_bound : ℝ, 0 ≤ M_bound →
  ContDiff ℝ 1 yex →
  (∀ t, |yex t| ≤ M_bound) →
  (∀ t, |deriv yex t| ≤ (L : ℝ) * M_bound) →
  ∀ x : ℝ, x₀ < x →
    ‖((x - x₀) * (L : ℝ)) • M.A.map (fun a => |a|)‖ < 1 →
  ...
```

**The fourth hypothesis `∀ t, |yex t| ≤ M_bound` is a GLOBAL bound on
`yex`.** Strengthening `IsConvergent` with this hypothesis creates a
cascade conflict with §514's `convergence_witness_satisfies_U`
(Section514.lean:496), which applies `IsConvergent` to the trivial IVP

```lean
f ≡ 1, yex = id, x₀ = 0, y₀ = 0, x = 1
```

**Problem**: `id : ℝ → ℝ` is unbounded. There exists no `M_bound : ℝ`
satisfying `∀ t, |id t| ≤ M_bound`. Therefore `IsConvergent` cannot
be applied to this IVP after strengthening, and §514's
`convergence_witness_satisfies_U` proof breaks.

## Why §514 needs `yex = id`

The cycle 099 closure of `convergence_witness_satisfies_U` extracts
`M.U *ᵥ u' = (fun _ => 1)` from the cycle-098 stage-limit clause
applied to `yex = id, x = 1` (so `yex(1) = 1`).

Specifically: the stage-limit `Y_int n → fun _ => yex(x)` together
with the stage equation forces `(M.U *ᵥ u') i * yex(x) = yex(x)`,
which gives `(M.U *ᵥ u') i = 1` whenever `yex(x) ≠ 0`.

To get `yex(x) ≠ 0` with `yex(x₀) = 0`, the IVP must have a
non-constant `yex`. By the ODE constraint `deriv yex(t) = f(yex(t))`,
non-constant `yex` with non-trivial `f` is generically **unbounded**:

* `yex = id` (used in §514) is unbounded.
* `yex = sin(αt)` would require `f(y) = α√(1 - y²/something)`, not
  globally Lipschitz.
* `yex = exp(t) - 1` is unbounded.
* The only globally bounded solutions of autonomous ODEs are
  constants — but `yex = const` with `yex(x₀) = 0` forces `yex ≡ 0`
  and `yex(x) = 0`, defeating the `M.U *ᵥ u' = 1` extraction.

**Therefore**: any IVP with `yex(x) ≠ yex(x₀)` REQUIRES unbounded
`yex` (under the autonomous-ODE + globally-Lipschitz constraints).
The cycle-114 strengthening makes `IsConvergent` inapplicable to
**all** such IVPs, breaking §514's witness extraction.

## Cascade impact

| File | Theorem | Uses `hConv` with | Compat with strengthening |
|---|---|---|---|
| Section513.lean | `convergent_isStable` (line 344) | `yex = 0`, bounded | ✓ Compatible (`M_bound := 0`) |
| Section514.lean | `convergence_witness_satisfies_U` (line 496) | `yex = id`, **unbounded** | ✗ INCOMPATIBLE |
| Section514.lean | `convergent_isPreconsistent` (line 695) | indirect via `convergence_witness_satisfies_U` | ✗ Cascades from above |
| Section514.lean | `convergent_consistent_isStable_isConvergent` (line 724) | indirect via both | ✗ Cascades from above |

Strengthening `IsConvergent` as the strategy specifies would break
**three** §514 theorems, two of which are public (`thm:514A` and the
preconsistency biconditional).

## Why the strategy missed this

The cycle 114 strategy says

> If §513 / §514 *construct* a fake `IsConvergent` to derive a
> contradiction (e.g. cycle 093's `convergent_isStable` builds an
> arbitrary IVP), the proofs WILL need to supply the 5 hypotheses
> [...] **Audit both files carefully before claiming the cascade is
> trivial.**

The strategy correctly flagged "audit both files carefully", but the
specific `yex = id` problem in §514 was not analyzed. The IVPs in
§513 and §514 are *applications* of `IsConvergent`, not
*constructions* — both proofs apply `hConv : M.IsConvergent` to
specific IVPs. §513's IVP is bounded (`yex = 0`); §514's is not
(`yex = id`).

## Possible solutions

### Solution A: Localize `M_bound` to `[x₀, x]`

Replace the global `∀ t, |yex t| ≤ M_bound` with a compact-interval
bound `∀ t ∈ Set.Icc x₀ x, |yex t| ≤ M_bound`. For `yex = id, x = 1`,
`M_bound := 1` works. For `yex = 0`, `M_bound := 0` works.

**Cost**: requires refactoring `localStepError_bound` (and its
sub-helpers `localStageError_bound_a/b`, `aux_T3_bound`, `aux_T4_bound`)
to consume compact-interval bounds rather than global ones. Each
helper currently uses `∀ t, |yex t| ≤ M_bound` GLOBALLY in proofs of
sub-bounds — these usages would each need to be re-proved with the
compact-interval restriction. Estimated cost: 1–2 cycles.

**Benefit**: the strengthening becomes faithful to the textbook (which
implicitly works on a compact interval) and §514's `yex = id` is
compatible (since `id` is bounded on `[0, 1]`).

### Solution B: Smooth-bounded replacement IVP for §514

Replace `yex = id` in `convergence_witness_satisfies_U` with a smooth,
bounded function `g` satisfying `g(0) = 0, g(1) = c ≠ 0,
ContDiff ℝ 1 g, |g| ≤ M_bound, deriv g = f ∘ g` for some Lipschitz
`f`.

**Cost**: constructing such `g, f` is non-trivial. Naive choices
like `g = c · tanh` give non-Lipschitz `f`. Requires a fresh smooth
bump-function construction, possibly via Mathlib's
`ContDiffBump`/`exp_neg_inv` machinery.

**Benefit**: §514's witness extraction is salvaged; no
`localStepError_bound` refactor needed.

### Solution C: Don't strengthen `IsConvergent`; supply hypotheses locally inside the capstone

Inside `stable_consistent_isConvergent`'s body, after `intro f L
hf_lip x₀ y₀ yex hyex_x₀ hyex_ode`, derive `M_bound`, `hyex_M`,
`hyex_C1`, `hyex'_LM` LOCALLY from `[x₀, x]` compactness, and
construct `h_norm` by choosing the iteration's `h₀` small enough.

**Cost**: requires (1) localized `localStepError_bound` (Solution A's
refactor), AND (2) compact-interval compactness arguments for
`yex` inside the capstone body. Larger than A or B alone.

**Benefit**: `IsConvergent` definition remains faithful to Butcher's
textbook (no extra hypotheses); §513/§514 cascade is unchanged.

### Solution D: Strengthen `IsConvergent` and break §514

Apply the strategy's strengthening as-is, accept the §514 breakage,
re-`sorry` `convergence_witness_satisfies_U` with a deferred fix.

**Cost**: regresses §514's closure (introduces 1+ sorries in §514).
Requires §515 capstone closure to claim a substantive net advance.

**Benefit**: §515 capstone closes cleanly; §514's deferred fix is
isolated to a single private lemma.

## Recommended next-cycle path

**Cycle 115**: Solution A (localize `M_bound` to `[x₀, x]`). Refactor
`localStepError_bound`, `localStageError_bound_a/b`, `aux_T3_bound`,
`aux_T4_bound` to consume compact-interval bounds. Then apply
strategy's strengthening (with localized `M_bound`); §514's
`convergence_witness_satisfies_U` becomes compatible (`M_bound := 1`
works on `[0, 1]`).

**Status**: documented in cycle 113 task results. Cycle 113 itself
makes a smaller forward step (M-matrix-based `ell_U/phi_A`
constructor helper) to unblock the body composition once the
signature question is resolved.

## Cycle 114 update

The cycle 114 worker landed `aux_515D_construct_ell_U_phi_A` in
`OpenMath/Chapter5/Section515.lean` (between
`aux_515B_eta_contraction` and `localStepError_bound`). This
infrastructure does NOT touch the §514 cascade or the
`IsConvergent` definition; it is the load-bearing primitive for
the future body composition of `aux_515D_output_tendsto` once
the cascade question is resolved.

**Solution A is now the favored path** for cycle 115:

1. The helper output `(ell_U i, phi_A i)` is compatible with both
   the global and the localized `M_bound` forms — its hypothesis
   `‖(h₀ L) • |A|‖ < 1` is unchanged regardless of which `M_bound`
   form `localStepError_bound` consumes.
2. §514's `yex = id` consumer becomes compatible with the
   localized form: `M_bound := |x|` works on `Set.Icc 0 x` since
   `|id t| ≤ |x|` for `t ∈ [0, x]`.
3. Solutions B (smooth-bounded replacement IVP) and C (local
   derivation in capstone) are strictly more expensive than A.
4. Solution D (regress §514) is unattractive because it adds new
   sorries.

Cycle 115 should refactor `localStepError_bound` (and helpers
`localStageError_bound_a/b`, `aux_T3_bound`, `aux_T4_bound`) to
consume `∀ t ∈ Set.Icc x₀ x, |yex t| ≤ M_bound`, then strengthen
`IsConvergent`'s clause (with the localized form), then verify
§513 / §514 still build, then compose the body of
`aux_515D_output_tendsto` using the cycle 114 helper plus the
A/B/C sub-lemmas.

## Cross-references

* `aux_515D_output_tendsto_hypotheses.md` — original hypothesis
  inventory; cycle 114 update marks the helper as CLOSED.
* `glm_isconvergent_strengthened.md` — cycle 098 precedent
  (compatible — only added stage-limit clause, no boundedness).
* `is_convergent_strengthened.md` — LMM analog precedent.
* `OpenMath/Chapter5/Section514.lean:496` —
  `convergence_witness_satisfies_U` (the breaking consumer).
* `OpenMath/Chapter5/Section515.lean::aux_515D_construct_ell_U_phi_A`
  — the cycle 114 helper.
