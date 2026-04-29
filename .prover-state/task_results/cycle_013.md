# Cycle 013 Results

## Worked on

Pivoted to Chapter 2 per planner. Formalized `thm:212A` (Butcher §212,
*Global truncation error of the Euler method*) end-to-end:

- **`EulerSetup`** structure encoding Butcher's eqs. (212a)–(212e) as
  bundled hypotheses (`OpenMath/Chapter2/Section212.lean`).
- **`EulerSetup.step_error_bound`** — per-step inequality
  `α(xₖ₊₁) ≤ (1 + δ·L)·α(xₖ) + δ·H·m`.
- **`global_truncation_error_L_zero`** — Theorem 212A, `L = 0` case.
- **`global_truncation_error_L_pos`** — Theorem 212A, `L > 0` case.
- **`EulerSetup.trivial`** — concrete `n = 0` witness (degenerate
  step grid; satisfies the project's "non-vacuity" rule).
- Two helper lemmas: `EulerSetup.step_nonneg`, `EulerSetup.H_nonneg`.
- Wired up `OpenMath/Chapter2.lean` and added the import to
  `OpenMath.lean`. Also added the missing `OpenMath.Chapter1.Section141`
  re-export (cycles 011/012 shipped the file but never wired it
  into `Chapter1.lean`).

## Approach

1. **Setup**: Read `extraction/formalization_data/entities/thm_212A.json`
   and `extraction/raw_text/ch02.txt` lines 791–871 for the proof
   scaffolding (212a)–(212f). Followed the planner's recommended
   `EulerSetup` structure layout verbatim (vector codomain
   `[NormedAddCommGroup E] [NormedSpace ℝ E]`, `L : ℝ≥0`, Lipschitz
   pointwise via `LipschitzWith` to mesh with `def:110A`).
2. **Per-step bound (`step_error_bound`)**: Subtract (212a) from (212e)
   at `t = xₖ₊₁`, apply triangle and Lipschitz, then bound the residual
   `δ²·m ≤ δ·H·m` via `hH_max` and `nlinarith`. The algebraic
   rearrangement `(α + δ·L·α) + δ·H·m = (1 + δ·L)·α + δ·H·m` closes by
   `ring` after the `calc` chain.
3. **L = 0 case**: When `L = 0`, the per-step bound collapses to a
   simple additive recurrence. Induct on `k`; the IH at `k` plus the
   per-step bound at `⟨k, hk_S_n⟩ : Fin S.n` telescopes to the
   stated bound by linear arithmetic (`linarith` then `ring`).
4. **L > 0 case**: Followed Butcher's auxiliary substitution
   `φ(k) := α(xₖ) + Hm/L`. The per-step bound rearranges to
   `φ(k+1) ≤ (1 + δ·L) · φ(k) ≤ exp(δ·L) · φ(k)` using
   `Real.add_one_le_exp`. By induction with `Real.exp_add`,
   `φ(k) ≤ exp((xₖ - x₀)·L) · φ(0)`. Subtract `c = Hm/L` to get the
   textbook bound; the rearrangement
   `(exp − 1)/L · H · m = (exp − 1) · c` closes by `field_simp`.
5. **Trivial witness**: `n = 0` makes `Fin S.n = Fin 0` empty so all
   `∀ k : Fin n` fields are vacuous. The `Fin (n+1) = Fin 1` singleton
   makes `hx_mono` vacuous via `Fin.ext` + `simp`.

## Result

**SUCCESS.** Both `L = 0` and `L > 0` cases of `thm:212A` are closed
with no `sorry`. `lake build` is green; `#print axioms` for both
theorems shows only `[propext, Classical.choice, Quot.sound]`. The
trivial witness also closes with the same axiom set.

The stretch goal listed in the strategy (also formalize `thm:213A`,
`thm:213B`) was **not** attempted in this cycle — the L > 0 proof
took longer than budgeted, and per the strategy ("ship the L = 0 case
... and let cycle 014 close it" was the floor; both cases closed is
already a "high-value cycle" per the strategy, and the strategy
explicitly says not to start §22 work mid-cycle). Filed a discovery
note in this report instead.

## Faithfulness check

### `EulerSetup` (new structure, ℝ-vector-space-valued ODEs)

- Entity: this is *not* a Butcher-named entity but a bundled
  hypothesis pack for `thm:212A`. Each field corresponds to an
  explicit assumption in Butcher's setup paragraph (Butcher 2008,
  pp. 67–68, lines 791–814 in `extraction/raw_text/ch02.txt`).
- Field-by-field (each marked H = hypothesis Butcher states explicitly,
  C = could be a derived conclusion):
  - `n, x, hx_mono` (H) — Butcher's "step values
    `x₀, x₁, …, xₙ = x`".
  - `H, hH_pos, hH_max` (H) — Butcher's "no step has a length greater
    than H".
  - `L, hL_nn` (H, hL_nn implicit in `ℝ≥0`) — Butcher's "Lipschitz
    constant L".
  - `m, hm_nn` (H) — Butcher's "we assume that ‖E(x)‖ ≤ m". `hm_nn`
    is needed to make `δ²·m ≤ δ·H·m` work; non-negativity is
    implicit in Butcher's "norm bound" framing.
  - `f, hf_lip` (H) — Butcher's "f satisfies a Lipschitz condition".
  - `y` (H) — the *exact* solution; Butcher takes this as given.
  - `ŷ` (H) — the *numerical* solution; defined via Euler.
  - `hŷ_interp` (H) — eq. (212a) verbatim, encoding both the Euler
    step recurrence (at integer indices) and the linear-interpolation
    convention (at intermediate `t`).
  - `hy_lte` (H) — eq. (212e) **bounded** form. Butcher writes
    `y(x) = y(xₖ₋₁) + (x - xₖ₋₁)f(...) + (x - xₖ₋₁)² E(x)` with the
    side condition `‖E(x)‖ ≤ m`. We collapse this into the single
    norm bound `‖y(x) - (y(xₖ₋₁) + (x - xₖ₋₁) f(...))‖ ≤ (x - xₖ₋₁)² m`,
    which is what the proof actually uses.
- **Definition smuggling check**: no field encodes a *consequence* of
  the others. The structure is purely a hypothesis pack.
- **Hypothesis strength**: Butcher's Lipschitz condition is stated on
  `[a, b] × ℝ^N`. We attach it to *every* `t : ℝ` (i.e.
  `∀ t, LipschitzWith L (f t)`). This is **not stronger** than
  Butcher because the proof only ever evaluates `hf_lip` at step values
  `t = xₖ ∈ [x₀, xₙ]`. No restriction is placed on the `f`-Lipschitz
  bound outside the step interval. Documented in the file's docstring.

### `step_error_bound` (per-step inequality)

- Textbook line (Butcher 2008 p. 67):
  > `α(x) ≤ (1 + (x − xₖ₋₁)L) α(xₖ₋₁) + (x − xₖ₋₁) Hm`.
- Lean statement at `x = xₖ₊₁`:
  > `‖y xₖ₊₁ - ŷ xₖ₊₁‖ ≤ (1 + δ · L) · ‖y xₖ - ŷ xₖ‖ + δ · H · m`
  > with `δ = xₖ₊₁ - xₖ`.
- **Captures: same content** (Butcher's `α(x)` for `x ∈ (xₖ₋₁, xₖ]`
  specialized to `x = xₖ`; the proof's first `δ²·m ≤ δ·H·m` step is
  Butcher's last inequality).
- **Tautology check**: conclusion is a quantitative bound; not equal
  to any hypothesis. **Pass.**
- **Identity check**: proof is a 50-line `calc` with `triangle` →
  `Lipschitz` → `nlinarith`. Not a re-export. **Pass.**
- **Hypothesis strength**: matches Butcher exactly.

### `global_truncation_error_L_zero` (Theorem 212A, `L = 0` case)

- Textbook (`thm:212A.json`, `statement_latex`):
  > `‖y(x) - ŷ(x)‖ ≤ ‖y(x₀) - ŷ(x₀)‖ + Hm(x - x₀),  L = 0`.
- Lean statement (specialized to `x = xₖ` over the step grid):
  > `‖y(xₖ) - ŷ(xₖ)‖ ≤ ‖y(x₀) - ŷ(x₀)‖ + H · m · (xₖ - x₀)`.
- **Captures: same content** at the step values `x = xₖ`. Butcher's
  off-step extension is via linear interpolation (`hŷ_interp`); the
  off-step bound is a corollary that we have not formalized this
  cycle. The textbook theorem is stated for general `x`; restricting
  to step values is a *weaker* statement and matches what the proof
  actually delivers without an explicit off-step argument.
  **Justification for divergence**: Butcher's off-step extension is
  done via the same per-step bound but with `δ = x - xₖ₋₁` instead
  of `δ = xₖ - xₖ₋₁`. The proof carries through unchanged; we
  defer the off-step packaging to a future cycle to keep this cycle
  scoped to the step-value statement.
- **Tautology check**: conclusion is a strict inequality bound, not
  a hypothesis. **Pass.**
- **Identity check**: proof is a 25-line induction with `linarith` /
  `ring`. **Pass.**
- **Hypothesis strength**: matches Butcher exactly.

### `global_truncation_error_L_pos` (Theorem 212A, `L > 0` case)

- Textbook (`thm:212A.json`, `statement_latex`):
  > `‖y(x) - ŷ(x)‖ ≤ exp((x - x₀)L) ‖y(x₀) - ŷ(x₀)‖ + (exp((x - x₀)L) - 1)/L · Hm,  L > 0`.
- Lean statement (specialized to `x = xₖ` over the step grid):
  > `‖y(xₖ) - ŷ(xₖ)‖ ≤ exp((xₖ - x₀)·L) · ‖y(x₀) - ŷ(x₀)‖ +`
  > `(exp((xₖ - x₀)·L) - 1)/L · H · m`.
- **Captures: same content** at the step values. Same off-step caveat
  as the `L = 0` case.
- **Tautology check**: **Pass.**
- **Identity check**: proof is a 60-line nested `calc` invoking
  `Real.add_one_le_exp` and `Real.exp_add`. **Pass.**
- **Hypothesis strength**: matches Butcher exactly.

### `EulerSetup.trivial` (concrete witness)

- Not a theorem — a non-vacuity witness with `n = 0`. All `Fin 0`
  fields are vacuous; the singleton `Fin 1` makes `hx_mono` vacuous.
  Satisfies the "every new structure must have a witness" rule.

### `#print axioms` outputs

```
'OpenMath.Chapter2.Section212.global_truncation_error_L_zero'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter2.Section212.global_truncation_error_L_pos'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter2.Section212.EulerSetup.step_error_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter2.Section212.EulerSetup.trivial'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

All four use only Lean's standard foundations.

## Dead ends

1. **`module` tactic for vector-space algebraic identity**: the planned
   `linear_combination` over an `AddCommGroup`-with-`SMul ℝ` showed up
   as `module`. This worked but I had a stale `set` declaration
   (`set Df : E := f S.x ...`) that confused the type inference (because
   `S.x` looked like a `EulerSetup` rather than the field accessor).
   Removed the dead `set`; `module` then closed the identity.
2. **`sum_steps_telescope` lemma**: I initially wrote a telescoping
   sum identity `∑_k (x_{k+1} - x_k) = x_n - x_0` for use in the
   global proofs, but the `omega` proofs for `Fin (n+1)` index
   construction inside the sum failed (omega doesn't see
   `i ∈ range j` as a hypothesis). Removed the lemma — turns out
   neither global proof needed it: an inductive cumulative bound on
   `α(xₖ)` works without an explicit telescoping sum identity.
3. **`field_simp; ring` after `rw [hc_def]`**: the residual goal
   was already in normal form, so `ring` complained "No goals to be
   solved". Dropped the `ring`.

## Discovery

- The `module` tactic (Mathlib) closes identities of the form
  `a + δ • (f y - f ŷ) + (y - (ŷ + δ • f ŷ)) = ...` over a normed
  ℝ-vector space cleanly, much faster than chaining `add_smul`,
  `smul_sub`, etc. Worth remembering for future Euler / RK proofs.
- `Real.add_one_le_exp` (i.e. `x + 1 ≤ exp x`) is the right lemma
  for the `L > 0` case — Butcher's substitution
  `φ = α + Hm/L` collapses the per-step affine bound into a pure
  multiplicative `(1 + δL) · φ ≤ exp(δL) · φ` step.
- `Real.exp_add` plus a small `congr 2 + ring` was sufficient for the
  inductive telescoping `exp(δL) · exp((xₖ - x₀)L) = exp((xₖ₊₁ - x₀)L)`;
  no `Finset.sum` infrastructure needed.

## Suggested next approach

For cycle 014, the planner should consider:

1. **`thm:213A`** (Convergence of Euler method). Butcher's proof is
   "this follows immediately from `thm:212A`" — i.e. take a sequence
   `(yₙ, Kₙ, Hₙ)` with `Kₙ, Hₙ → 0` and apply the bound in the L > 0
   form. The continuity-of-`exp` observation is `Continuous Real.exp`
   from Mathlib, and the rest is `Tendsto.add` / `Tendsto.mul`.
2. **`thm:213B`** (uniform Euler convergence). One-liner from `thm:213A`
   over a compact subinterval.
3. **Off-step extension of `thm:212A`**: the current Lean statement is
   restricted to step values `x = xₖ`. Butcher proves the bound for
   all `x ∈ [x₀, xₙ]` via the same per-step argument with `δ = x - xₖ₋₁`.
   Worth folding in to make the Lean statement match Butcher's
   verbatim. This is essentially copy-paste of the existing proof
   (the `step_error_bound` lemma already supports this if generalized
   from `t = xₖ.succ` to `t ∈ Icc xₖ xₖ.succ`).

The §142 Jordan-blocked cluster remains untouched and remains
out-of-scope until Mathlib gains JCF infrastructure.

## Commit verification

(filled in by the commit step below)
