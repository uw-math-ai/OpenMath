# Cycle 257 Strategy

## A. Status check

Cycle 256 was a clean ship (P1 + P2 + P3 all axiom-clean, sorry count 0).
There are no Aristotle results pending, no live blockers, no
phantom-verdict regressions. `OpenMath/Chapter3/Section311.lean` is
355 LOC at HEAD with three public theorems
(`F_tau_eval`, `lem_311A_order_one`, `lem_311A_order_two`,
`bseriesAlphaPartialSum_singleton_vertex_eq`) and one private helper
(`iteratedDeriv_two_via_ode`).

§441 Phase C.2 stays GPFS-blocked (43+ consecutive timeouts since
cycle 182, single-cycle compiles never complete). **Skip §441 work
entirely** — do NOT attempt smoke tests, do NOT poll the dead
Aristotle project. Pivot is permanent until the loop maintainer
restores GPFS health.

## B. Cycle 257 target — `lem_311A_order_three` in Section311.lean

**Primary P1 (mandatory)**: extend cycle 256's `lem_311A_order_two`
by one more Taylor order. Mechanical port of cycle 256's recipe with
one extra chain-rule layer. Estimated 150–200 LOC.

### Why this target (not the polymorphic alternative)

The cycle 256 task results recommended Path 3 (polymorphic
`lem_311A_order_one` + retrofit) as "highest leverage", but it
carries significant risk: `iteratedDeriv` is specific to ℝ-codomain
functions, and polymorphic `yex : ℝ → N` requires `iteratedFDeriv`
with `ContinuousMultilinearMap` plumbing. That refactor has open
Mathlib API questions (`iteratedFDeriv_one_apply` ↔ `fderiv` bridge,
`taylorWithinEval` polymorphic signature) that could stall the cycle.

Path 1 (order_three) is **purely additive**: copy cycle 256's
8-step recipe, add one layer to `iteratedDeriv_two_via_ode`,
bump the Taylor degree to 4, sum one more cubic-in-h residual.
No Mathlib API drift expected — `taylor_isLittleO (n := 4)` works
identically to `(n := 3)`, just like cycle 256 confirmed for
`(n := 3)` vs cycle 248's `(n := 2)`.

The polymorphic refactor stays on the long-range roadmap but should
NOT be cycle 257's deliverable.

### P1 deliverables

Add to `OpenMath/Chapter3/Section311.lean`, immediately after
`lem_311A_order_two` (line 246) and before the cycle-256 P3 bridge
(line 346):

1. **`private theorem iteratedDeriv_three_via_ode`** (~80 LOC):

   ```lean
   private theorem iteratedDeriv_three_via_ode
       {f : ℝ → ℝ} (hf_C2 : ContDiff ℝ 2 f)
       {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
       (hyex_x₀ : yex x₀ = y₀)
       (hyex_C4 : ContDiff ℝ 4 yex)
       (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
       iteratedDeriv 3 yex x₀
         = deriv (deriv f) y₀ * (f y₀)^2 + (deriv f y₀)^2 * f y₀
   ```

   Proof recipe: `iteratedDeriv_succ` once exposes
   `deriv (iteratedDeriv 2 yex) x₀`. The outer `funext` argument
   needs `iteratedDeriv 2 yex = fun x => deriv f (yex x) * f (yex x)`
   pointwise (the polymorphic version of cycle 256's
   `iteratedDeriv_two_via_ode`). Apply chain rule + product rule:

   ```
   deriv (fun x => deriv f (yex x) * f (yex x)) x₀
     = deriv (deriv f ∘ yex) x₀ · f (yex x₀)
       + deriv f (yex x₀) · deriv (f ∘ yex) x₀
     = (deriv (deriv f) (yex x₀) · deriv yex x₀) · f (yex x₀)
       + deriv f (yex x₀) · (deriv f (yex x₀) · deriv yex x₀)
     = deriv (deriv f) y₀ · f y₀ · f y₀ + deriv f y₀ · deriv f y₀ · f y₀
     = deriv (deriv f) y₀ · (f y₀)^2 + (deriv f y₀)^2 · f y₀
   ```

   The pointwise identification of `iteratedDeriv 2 yex` with
   `fun x => deriv f (yex x) * f (yex x)` is the same chain-rule
   computation as in cycle 256's `iteratedDeriv_two_via_ode`, but
   now applied at every `x` (not just `x₀`). You will need
   `ContDiff ℝ 2 f` (not just `ContDiff ℝ 1 f`) for the second
   chain-rule application, because `deriv f` itself must be
   differentiable.

   **Key Mathlib lemmas to use**: `iteratedDeriv_succ`,
   `deriv_comp`, `deriv_mul`, `(hyex_ode x).deriv`. Verify with
   `lean_local_search "deriv_mul"` if signature unclear.

2. **`theorem lem_311A_order_three`** (~100 LOC):

   ```lean
   theorem lem_311A_order_three
       {f : ℝ → ℝ} (hf_C2 : ContDiff ℝ 2 f)
       {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
       (hyex_x₀ : yex x₀ = y₀)
       (hyex_C4 : ContDiff ℝ 4 yex)
       (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
       (fun h : ℝ => yex (x₀ + h) -
           (y₀ + h * f y₀ + h^2 / 2 * (deriv f y₀ * f y₀)
            + h^3 / 6 * (deriv (deriv f) y₀ * (f y₀)^2
                          + (deriv f y₀)^2 * f y₀)))
         =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (3 + 1)) := by
     ...
   ```

   Proof recipe — copy cycle 256's `lem_311A_order_two` body
   verbatim (Section311.lean lines 246–321) with these changes:
   - `taylor_isLittleO (n := 4)` instead of `(n := 3)`.
   - `hT_eval` evaluates degree-4 Taylor:
     `yex(x₀+h) ≈ yex(x₀) + h·D¹ + h²/2·D² + h³/6·D³ + h⁴/24·D⁴`
     (one more `Finset.sum_range_succ` unfold).
   - `hderiv1_x0` and `hderiv2_x0` reused verbatim from cycle 256
     (lines 276–283).
   - **New**: `hderiv3_x0 := iteratedDeriv_three_via_ode hf_C2 hyex_x₀ hyex_C4 hyex_ode`.
   - `hres` uses `(x - x₀)^4` and collapses to `h^4`.
   - `hdiff_eq` rewrites the goal's difference into Taylor-residual
     plus the **quartic** term `h^4 / 24 * iteratedDeriv 4 yex x₀`.
   - `hquartic` is the `h^4` term as `O(h^4)` via
     `Asymptotics.isBigO_const_mul_self`.
   - Final: `rw [show (fun h : ℝ => h ^ (3 + 1)) = (fun h => h^4) from by funext; ring]`
     and `exact hres.isBigO.add hquartic`.

3. **Non-vacuity witness** (~10 LOC):

   ```lean
   example (x₀ y₀ : ℝ) :
       (fun h : ℝ => (fun _ : ℝ => y₀) (x₀ + h) -
           (y₀ + h * 0 + h^2 / 2 * (0 * 0)
            + h^3 / 6 * (0 * 0^2 + 0^2 * 0)))
         =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (3 + 1)) :=
     lem_311A_order_three (f := fun _ : ℝ => (0 : ℝ)) ...
       (by simpa using contDiff_const) rfl ...
   ```

   With `f := 0` and `yex := const y₀`: `f y₀ = 0`,
   `deriv f y₀ = 0`, `deriv (deriv f) y₀ = 0`, so the entire
   B-series collapses to `y₀`, and the residual is identically 0.
   `Asymptotics.isBigO_zero` closes the trivial bound.

### Faithfulness check (mandatory pre-commit)

For `iteratedDeriv_three_via_ode`: NOT a textbook entity (private
helper). No `entity_id` needed, but the docstring should explicitly
note "`iteratedDeriv 3 yex x₀ = f''(y₀)·f(y₀)² + f'(y₀)²·f(y₀)`
under the autonomous-ODE constraint" and credit the chain-rule +
product-rule derivation.

For `lem_311A_order_three`: SAME convention as cycle 256's
`lem_311A_order_two`. The textbook `lem:311A` is the combinatorial
labelling lemma over `T_S^*`; the cycle 257 deliverable is the
order-3 Taylor specialization that `lem:311A` underwrites in §311.
`lean_status.json` row for `lem:311A` stays `unformalized`. Do NOT
update that row. Document in the docstring (mirror cycle 256's
docstring at lines 227–245).

Tautology check: confirm
`grep -c sorry OpenMath/Chapter3/Section311.lean` returns 0 and
`rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section311.lean`
returns no matches. Hypothesis-strength check: `ContDiff ℝ 2 f` is
the minimum needed for the chain-rule cascade — `ContDiff ℝ 1 f`
would not suffice (cycle 256 already needed `ContDiff ℝ 1 f` for
order 2; one more order needs one more derivative of `f`).

### Risks (each addressable mid-cycle)

- **R1 (chain rule arity)**: `deriv_comp` for nested compositions
  may need explicit `differentiableAt` annotations on each layer.
  Cycle 256's `iteratedDeriv_two_via_ode` already shows the
  pattern (`hf_diff.differentiableAt`, `hyex_diff.differentiableAt`).
  For order 3, `deriv f` itself needs to be differentiable, which
  comes from `hf_C2.continuousOn_deriv_succ`-style API or via
  `ContDiff.differentiable_iteratedDeriv`. Verify the exact name
  with `lean_local_search "ContDiff.differentiable"` if the obvious
  path fails.

- **R2 (`deriv_mul` signature)**: the product rule
  `deriv (f·g) = f'·g + f·g'` lives in Mathlib as `deriv_mul`
  for general functions (with `DifferentiableAt` hypotheses).
  Verify the exact name with `lean_loogle "deriv (_ * _)"`. If it
  requires `DifferentiableAt`, supply via the `ContDiff` hypotheses.

- **R3 (Taylor degree-4 expansion)**: `taylor_within_apply` produces
  `Σ k ∈ range 4, ...` which `Finset.sum_range_succ` × 4 unfolds.
  Cycle 256 used the same simp set at degree 3
  (`[Finset.sum_range_succ, ..., Nat.factorial, ...]`); add one more
  application of `Finset.sum_range_succ` and the simp set should
  carry through. The `4! = 24` reduction comes from
  `Nat.factorial` definitional unfold.

- **R4 (algebraic blowup in the `ring` step)**: with three
  derivative terms (`f y₀`, `f y₀ * f' y₀`, the new quartic),
  the `ring` call after `hT_eval`'s `simp only` may produce a
  larger polynomial-arithmetic goal. Cycle 256 had `ring` close
  in default heartbeats; cycle 257 should too, but if it stalls,
  factor the algebraic identity into a separate `have h_alg : ...
  by ring` before invoking the Taylor machinery.

- **R5 (heartbeats)**: cycle 256 closed in default heartbeats.
  Cycle 257 adds one more layer; if you hit the 200 000 ceiling,
  decompose `hT_eval` into a sub-lemma with its own `simp only +
  ring` body. **Do NOT raise `maxHeartbeats`** (CLAUDE.md absolute
  rule).

## C. Stretch P2 (optional, only if P1 closes in <90 minutes)

Ship one substantive non-vacuity `example` for
`bseriesAlphaPartialSum` evaluated at a 2- or 3-element finset of
distinct trees, showing a non-trivial value. Currently cycle 256
has only `{vertex}` and `{vertex, cherry}` examples in Section301;
neither computes the α-weights at trees with non-trivial
combinatorics.

Concrete suggestion (~30 LOC), placed at the end of Section301.lean
or in Section311.lean alongside the cycle 256 P3 bridge:

```lean
example (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesAlphaPartialSum f y₀ h
        ({vertex, cherry, broom₃} : Finset RootedTree)
      = bseriesAlphaTerm f y₀ h vertex
        + bseriesAlphaTerm f y₀ h cherry
        + bseriesAlphaTerm f y₀ h broom₃ := by
  rw [bseriesAlphaPartialSum]
  -- Use Finset.sum_insert twice + Finset.sum_singleton
  ...
```

Goal: confirm the α-weighting machinery composes correctly across
multiple terms (no overlap in the insert pattern). This exercises
the full `bseriesAlphaPartialSum` pipeline on the non-trivial
members of Butcher Table 310(II) without needing to compute the
specific α-values closed-form.

**Skip P2 entirely if P1 takes the full cycle.** P2 is
nice-to-have, not required.

## D. What NOT to try

- **Do NOT attempt the polymorphic `lem_311A_order_one/two/three`
  refactor.** The `iteratedDeriv` → `iteratedFDeriv` bridge has
  open Mathlib API questions and is a multi-cycle endeavor. Stays
  on the long-range roadmap.

- **Do NOT attempt full `lem:310B`.** Requires labelled-tree quotient
  infrastructure (`def:300C`) plus `thm:306A` (Taylor's theorem
  multinomial expansion). Multi-cycle scope per cycle 254 strategy.
  Documented in plan.md.

- **Do NOT attempt small-r `lem:310B` cases.** LHS still requires
  labelled-tree machinery per cycle 255 strategy §exclusions.

- **Do NOT touch `OpenMath/Chapter4/Section441.lean`.** 43+
  consecutive GPFS timeouts since cycle 182. Skip the smoke test.
  Skip Aristotle polling. Pivot is permanent.

- **Do NOT modify `scripts/autonomous_loop.py`** (loop maintainer
  territory per CLAUDE.md and `tautology_scanner_false_positives.md`).

- **Do NOT introduce sorries.** Cycles 149 / 200 / 201 all rolled
  back sorry-first scaffolds; the cycle 257 deliverable must be
  axiom-clean or skipped entirely. If `lem_311A_order_three`
  proves harder than the recipe suggests, **abort P1 and ship a
  P3 backup** (see §E).

- **Do NOT introduce `axiom` or `constant`** declarations.

- **Do NOT raise `maxHeartbeats` above 200000** (CLAUDE.md absolute
  rule). Decompose proofs instead.

- **Do NOT update `lean_status.json` for `lem:311A`** — the row
  stays `unformalized` per cycle 248/256 convention.

- **Do NOT name your deliverable `lem_311A`** (without the
  `_order_three` suffix) — that name is reserved for the full
  combinatorial textbook lemma.

- **Do NOT poll Aristotle this cycle.** No Aristotle jobs are
  pending that would pay off in cycle 257. The CLAUDE.md "sleep
  30 min, check once" rule applies only when there's a live job
  worth checking.

## E. P3 backup — refactor extraction (only if P1 stalls)

If `lem_311A_order_three` stalls past ~90 minutes (e.g. R2 or R4
fires hard), abort P1 cleanly (revert any partial Section311 edits)
and pivot to:

**Extract cycle 247's three private helpers from Section319 into
`OpenMath/Helpers/GeometricExp.lean`**:
- `geometric_sum_one_plus_pos`
- `geometric_sum_one_plus_zero`
- `pow_one_add_le_exp`

These are pure real-analysis utilities that have nothing
specific to RK or §319. Extract them into a fresh module, update
`Section319.lean` to `import OpenMath.Helpers.GeometricExp`, and
verify the file still compiles axiom-clean. Sorry-neutral, no new
content, ~120 LOC moved + 1 import line. Guaranteed clean.

This is a "ship something useful even if P1 fails" insurance
policy. Do NOT pursue P3 unless P1 stalls.

## F. Verification checklist (mandatory before commit)

After the deliverable lands, run all of these and confirm green
exit:

```bash
# 1. File compiles standalone.
time timeout 120 lake env lean OpenMath/Chapter3/Section311.lean

# 2. Sorry count unchanged.
grep -c sorry OpenMath/Chapter3/Section311.lean
# Expected: 0

# 3. Tautology scanner regex returns 0 hits.
rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section311.lean
# Expected: no matches

# 4. Aggregator builds.
time timeout 180 lake env lean OpenMath/Chapter3.lean

# 5. Axiom check on each new public symbol.
echo '#print axioms OpenMath.Chapter3.Section311.lem_311A_order_three' \
  | lake env lean --stdin OpenMath/Chapter3/Section311.lean
# Expected: [propext, Classical.choice, Quot.sound] only.
```

If any check fails, fix or abort to P3 backup. **Do NOT commit if
sorry count rose, axiom set has `sorryAx`, or the tautology scanner
flags hits.**

## G. Commit and writeup

After all checks pass:

1. Update `.prover-state/task_results/cycle_257.md` with the
   standard sections (Worked on / Approach / Result / Faithfulness
   check / Dead ends / Discovery / Suggested next approach).

2. Update `plan.md` for `lem:311A`'s row: append to its existing
   cycle-history annotation a one-line cycle 257 note ("Cycle 257:
   shipped `lem_311A_order_three` (order-3 Taylor specialisation,
   axiom-clean) + `iteratedDeriv_three_via_ode` private chain-rule
   helper. Full `lem:311A` still unformalized."). Status remains
   `[~]` (partial).

3. Commit message follows existing pattern:
   `Cycle 257 — §311 lem_311A_order_three SHIPPED.`

4. Push to `butcher-experiments`.

## H. Suggested next approach (cycle 258+)

After cycle 257 ships, the natural cycle 258+ candidates are:

1. **Polymorphic refactor coordinated trio** (multi-cycle,
   highest-leverage): generalize `lem_311A_order_one/two/three`
   from `ℝ → ℝ` to `N : Type*` with normed-space typeclasses,
   replacing `deriv f y₀ * f y₀` with `fderiv ℝ f y₀ (f y₀)`.
   Requires resolving the `iteratedDeriv` → `iteratedFDeriv`
   bridge and `taylorWithinEval` polymorphic plumbing first. The
   most natural form §311's downstream `thm:311B` / `thm:311C`
   needs.

2. **Aristotle: small `lem:310B` case** for `r = 2` or `r = 3`
   (multi-cycle, requires `Fintype (TruncatedRootedTree N)` for
   small N first). Combines cycle 254's
   `bseriesTerm_eq_theta_smul_bseriesTerm`, cycle 255's
   `TruncatedRootedTree`, cycle 256's `bseriesAlphaPartialSum`,
   plus a small labelled-tree enumeration. High-value but
   high-risk single-cycle target.

3. **Pivot to a fresh §312 / §313 entity**: §310/§311 has had
   dedicated focus across cycles 254–257. After cycle 257's
   order_three lands, consider pivoting to `def:312A`-adjacent
   work or `lem:312B` (Elementary Weight Summation Formula),
   which cycle 256's `bseriesAlphaTerm` foundation directly
   supports.

The cycle 258 planner should choose based on which downstream
textbook landmark unblocks more entities; my read is that path 1
(polymorphic) gives the cleanest run at `thm:311B`.
