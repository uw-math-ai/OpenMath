# Cycle 014 Results

## Worked on

- **Priority 1 (refactor):** Eliminated cycle-13 semantic-sorry-scanner false
  positives in `OpenMath/Chapter2/Section212.lean` by inlining the two
  `have h_tri₁` / `have h_tri₂` triangle-inequality blocks directly into
  the calc chain inside `EulerSetup.step_error_bound`. The two
  `:= by exact norm_add_le _ _` named-have blocks (lines 138 and 144 in
  the cycle-13 file) are now inlined as `:= norm_add_le _ _` and
  `:= norm_add_le _ _` (in the nested calc) in the calc chain.

- **Priority 2 (formalization):** Formalized `thm:213A` (Convergence of
  the Euler method) as
  `OpenMath.Chapter2.Section213.euler_convergence` in a new file
  `OpenMath/Chapter2/Section213.lean`. The new file is wired into
  `OpenMath/Chapter2.lean`. `lean_status.json` updated.

## Approach

### Priority 1

Mechanical local edit: removed both named `have h_tri₁` and `have h_tri₂`
blocks from `step_error_bound` (lines ~140–161 in the previous file) and
inlined `norm_add_le _ _` directly at the corresponding calc steps. No
semantic change to the proof. Compile-checked
(`lake env lean OpenMath/Chapter2/Section212.lean`) and re-verified
axioms via `#print axioms`.

### Priority 2

Followed the planner's recommended scaffold:

1. Set up the theorem signature with a sequence `S : ℕ → EulerSetup E`,
   shared endpoints `x₀ xN`, fixed Lipschitz constant `L : ℝ≥0`, a
   uniform local-truncation bound `M`, a per-`n` initial-error bound `K n`,
   and the two convergence hypotheses `Tendsto (fun n => (S n).H) atTop (𝓝 0)`
   and `Tendsto K atTop (𝓝 0)`. Conclusion:
   `Tendsto (fun n => ‖(S n).y xN - (S n).ŷ xN‖) atTop (𝓝 0)`.
2. Case-split on `(L : ℝ) = 0` vs `> 0` via `eq_or_lt_of_le`.
3. **`L = 0` branch.** Apply `global_truncation_error_L_zero` from
   cycle 13 at `⟨(S n).n, _⟩ : Fin ((S n).n + 1)` for each `n`,
   rewrite the endpoints with `h_x₀ n`, `h_xN n`. Combine the per-`n`
   bound with `‖(S n).y x₀ - (S n).ŷ x₀‖ ≤ K n` and
   `(S n).m ≤ M` to get
   `‖_‖ ≤ K n + (xN - x₀) * M * (S n).H`. Apply `Tendsto.add` to the
   dominating sequence and `squeeze_zero` against `norm_nonneg`.
4. **`L > 0` branch.** Same shape but with
   `E0 := exp((xN - x₀) * L)` and `C := (E0 - 1) / L * M`. The
   per-`n` bound is `‖_‖ ≤ E0 * K n + C * (S n).H`. Both summands tend
   to 0 by `Tendsto.const_mul` then `Tendsto.add`; squeeze against
   `norm_nonneg`.

Two `nlinarith` calls (the multiplicative reorderings
`(S n).H * (S n).m * (xN - x₀) ≤ (xN - x₀) * M * (S n).H` and
`(E0 - 1) / L * (S n).H * (S n).m ≤ C * (S n).H`) needed explicit
`mul_le_mul_of_nonneg_left` hints; once supplied, both go through.

Aristotle was **not** used this cycle: the proof compiled cleanly with
the planner's recipe + minor `nlinarith` hint-fixes (~6s file build).
Submitting an Aristotle batch for sub-goals that already compile would
have been wasted compute.

## Result

**SUCCESS — both priorities landed.**

Build status:

```
$ lake build
Build completed successfully (2820 jobs).
```

Axioms (all standard):

```
'OpenMath.Chapter2.Section212.EulerSetup.step_error_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter2.Section212.global_truncation_error_L_zero'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter2.Section212.global_truncation_error_L_pos'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter2.Section212.EulerSetup.trivial'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter2.Section213.euler_convergence'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry` introduced. No `axiom`/`constant` declarations. No
`maxHeartbeats` increase.

## Faithfulness check

### `OpenMath.Chapter2.Section213.euler_convergence` (new theorem, formalizing `thm:213A`)

- Entity ID and textbook statement (quoted from
  `extraction/formalization_data/entities/thm_213A.json`):
  > Under the conditions stated in the above discussion, $D_n \to 0$
  > as $n \to \infty$.

  where (per the §213 preamble in `ch02.txt` and the entity JSON's
  `context_latex`/`variables`):
  > A sequence of approximations $y_n(x)$ is computed using the
  > Euler method with stepsize bounded by $H_n$ and initial error
  > bounded by $K_n$, where $H_n$ and $K_n$ tend to zero as $n$
  > increases. The global error $D_n$ is defined as
  > $y(x) - y_n(x)$ … $f$ satisfies a Lipschitz condition.

- Lean statement captures: **same content**.
  - The Lean conclusion `Tendsto (fun n => ‖(S n).y xN - (S n).ŷ xN‖)
    atTop (𝓝 0)` is exactly Butcher's `Dₙ → 0`.
  - Hypotheses: per-`n` initial-error bound `‖(S n).y x₀ - (S n).ŷ x₀‖ ≤ K n`
    + `Tendsto K atTop (𝓝 0)` matches Butcher's "initial error bounded by Kₙ,
    Kₙ → 0". `Tendsto (fun n => (S n).H) atTop (𝓝 0)` matches
    "greatest stepsize bounded by Hₙ, Hₙ → 0". Fixed `L : ℝ≥0` shared
    across the sequence (`h_L : ∀ n, (S n).L = L`) matches Butcher's
    "f satisfies a Lipschitz condition" (a single condition, not a
    per-`n` one).

- **Tautology check.** The conclusion `Tendsto _ atTop (𝓝 0)` does
  not appear verbatim or up-to-defeq among the hypotheses. ✓
- **Identity check.** The proof is a multi-step calc + `squeeze_zero`,
  not `exact h`. It does real work — it specializes the cycle-13
  `global_truncation_error_L_*` bounds and squeezes them against the
  topological hypothesis. ✓
- **Hypothesis strength.** Two hypotheses are *added* on top of
  Butcher's textbook list, both of which are forced by Butcher's
  context but not stated in the bare §213 paragraph:
  1. `h_M_nn : 0 ≤ M` — Butcher's local-truncation constant `m` is
     defined via `‖y''(x)/2‖ ≤ m` so `m ≥ 0` is automatic; we make it
     explicit because we don't have the analytic definition of `m` in
     scope.
  2. `h_m_bound : ∀ n, (S n).m ≤ M` — Butcher's `m` is implicitly the
     same constant for the whole sequence (it depends on `y''` and
     `f`, not on the discretization). Our `EulerSetup` bundles `m`
     per-instance, so we encode "shared `m`" as "uniformly bounded by
     `M`". This is the weakest condition that still proves the
     theorem; it is not stronger than Butcher's setup.
  These are documented in the file's docstring under "Faithfulness
  notes". ✓

- **Definition smuggling check.** No new `def`/`structure`/`class` was
  introduced. The structure used is the cycle-13 `EulerSetup`. ✓
- **Absent theorem check.** The proof references only existing
  declarations: `global_truncation_error_L_zero`,
  `global_truncation_error_L_pos`, `EulerSetup.H_nonneg`,
  `EulerSetup.hm_nn`, `squeeze_zero`, `Tendsto.add`,
  `Tendsto.const_mul`, `Real.exp_pos`, `Real.one_le_exp`,
  `mul_le_mul_of_nonneg_left`. All present. ✓

### Section212.lean refactor

- No new `def`/`structure`/`theorem` introduced. Bodies of
  `step_error_bound`, `global_truncation_error_L_zero`,
  `global_truncation_error_L_pos`, and `EulerSetup.trivial` are
  unchanged at the top level; `step_error_bound` had two named
  `have h_tri_*` declarations inlined. All four declarations still
  print only `[propext, Classical.choice, Quot.sound]`. ✓

## Dead ends

- **Unicode `x̄`.** First version of `Section213.lean` used `x̄` (LaTeX
  bar) for the right endpoint, mirroring Butcher. Lean 4 rejected the
  parameter binding `(x₀ x̄ : ℝ)` with `expected token` at the bar
  character. Renamed to ASCII `xN` and added a docstring note that
  this corresponds to Butcher's `x̄`.
- **Direct `nlinarith` on the multiplicative bound.** Both
  `nlinarith` calls in the per-`n` bound failed without explicit
  `mul_le_mul_of_nonneg_left` hints. Adding the hints lets them close
  in ~6 seconds total.

## Discovery

- The combining-macron character on `x̄` is not parseable as a
  bound-variable identifier in this Lean 4 toolchain even though it
  is fine in docstring text. Future cycles formalizing entities that
  use `x̄`/`ȳ`/etc. should default to ASCII (`xN`/`yN`/etc.) with a
  docstring cross-reference.
- The cycle-13 `global_truncation_error_L_zero` and `_L_pos` lemmas
  compose cleanly with `Tendsto`-arithmetic + `squeeze_zero`. This
  is exactly the recipe for §213B and §214 (order-of-convergence)
  results: both produce a per-`n` bound of the form
  `C * (S n).H^p + (smaller terms)` and squeeze. The §213A proof is
  a model template.

## Suggested next approach

1. **Check the cycle-14 score** — Priority 1 should drop the scanner
   count to 1 (Section212.lean now has no `have ... := by exact <name>`
   patterns matching the regex).
2. **Tackle `thm:213B`** — the uniform version. The natural plan is
   the off-step extension that the planner mentioned as Priority 3:
   prove `global_truncation_error_L_zero_offstep` and
   `global_truncation_error_L_pos_offstep` over `t ∈ Icc x₀ xN`,
   then `thm:213B` is `(sup … →  0)` proved the same way as 213A
   plus a uniformity argument. The off-step bound's proof is the
   §212A inductive argument with a final partial step
   `δ := t - x_{k-1} ≤ H` rather than `δ := xₖ - x_{k-1}`. This
   cycle did not get to the off-step extension — it remains a clean
   prep task for cycle 015.
3. **Optional simplification of `EulerSetup`.** The current
   `hf_lip : ∀ t, LipschitzWith L (f t)` is global on `ℝ`, but the
   §212A proof uses it only at step values. If §213B / §214 want to
   weaken this to `∀ t ∈ Icc x₀ xN`, that is a one-line tightening
   of the field; not blocking but worth noting.

## Commit verification

- Commit SHA: `2ce1552dafc2102f151b552a3cf0d89bbc7e51d9`
- `git rev-parse HEAD == origin/Main/Experiments`: confirmed.
- Push: `c9819ae..2ce1552  Main/Experiments -> Main/Experiments`.
