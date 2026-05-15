# Cycle 257 Results

## Worked on

Per cycle 257 strategy §B (P1 — mandatory):

- `lem_311A_order_three` (order-3 Taylor specialisation of `lem:311A`
  for `ℝ → ℝ` scalars) in `OpenMath/Chapter3/Section311.lean`.
- Private chain-rule helper `iteratedDeriv_three_via_ode`
  (`iteratedDeriv 3 yex x₀ = f''(y₀)·f(y₀)² + f'(y₀)²·f(y₀)` under
  the autonomous-ODE constraint `yex' = f ∘ yex`).
- Non-vacuity witness `example` consuming `lem_311A_order_three`
  with the zero vector field `f := 0` and constant exact solution
  `yex := const y₀`.

P2 (stretch — non-vacuity `bseriesAlphaPartialSum` example for a
3-element finset) and P3 (helpers extraction) were not pursued —
P1 closed cleanly without needing them.

## Approach

### `iteratedDeriv_three_via_ode` (private helper)

Recipe per strategy §B P1 step 1:

1. `iteratedDeriv_succ` peels off one outer derivative:
   `iteratedDeriv 3 yex x₀ = deriv (iteratedDeriv 2 yex) x₀`.
2. Pointwise identification of `iteratedDeriv 2 yex` as
   `fun x => deriv f (yex x) * f (yex x)` — same chain-rule
   computation as cycle 256's `iteratedDeriv_two_via_ode`, but
   established at every `x` (not just `x₀`) via `funext` +
   the ODE pointwise.
3. `deriv_mul` (product rule) on the resulting
   `deriv (fun x => deriv f (yex x) * f (yex x)) x₀`, gated by
   differentiability of each factor (`Differentiable ℝ (deriv f)`
   from `ContDiff.differentiable_deriv_two`, then `.comp` with
   `Differentiable ℝ yex`).
4. `deriv_comp` × 2 on each factor:
   `deriv (deriv f ∘ yex) x₀ = deriv (deriv f) (yex x₀) * deriv yex x₀`
   and
   `deriv (f ∘ yex) x₀ = deriv f (yex x₀) * deriv yex x₀`.
5. `(hyex_ode x₀).deriv` collapses `deriv yex x₀ = f (yex x₀) = f y₀`,
   then `ring` aggregates `(f''·f)·f + f'·(f'·f) = f''·f² + (f')²·f`.

`ContDiff ℝ 2 f` is exactly the regularity needed (one more chain-rule
layer than cycle 256, which needed `ContDiff ℝ 1 f`).

### `lem_311A_order_three` (main theorem)

Mechanical port of cycle 256's `lem_311A_order_two` body (Section311
lines 246–321) with the following changes:

- `taylor_isLittleO (n := 4)` instead of `(n := 3)` — fourth-order
  Taylor residual `=o[nhds x₀] (fun x => (x - x₀)^4)`.
- `hT_eval` extended to evaluate degree-4 Taylor polynomial at `x₀ + h`:
  one extra `Finset.sum_range_succ` unfold, simp set unchanged.
- `hderiv1_x0`, `hderiv2_x0` reused verbatim from cycle 256.
- New `hderiv3_x0 := iteratedDeriv_three_via_ode hf_C2 hyex_x₀ hyex_C4 hyex_ode`.
- `hres` translated to `nhds 0` over `(x - x₀)^4 = h^4`.
- `hdiff_eq` rewrites the goal's difference into Taylor-residual plus the
  quartic term `h^4 / 24 * iteratedDeriv 4 yex x₀`.
- `hquartic` is the quartic term as `O(h^4)` via
  `Asymptotics.isBigO_const_mul_self`.
- Final `hres.isBigO.add hquartic`, with `h ^ (3 + 1) = h ^ 4`
  collapse by `funext`/`ring`.

### Non-vacuity witness

With `f := 0`, `yex := const y₀`: `f y₀ = 0`, `deriv f y₀ = 0`,
`deriv (deriv f) y₀ = 0`. The B-series collapses to `y₀`, the
difference is identically zero, and the hypotheses are satisfied
by `contDiff_const` (×2) and `hasDerivAt_const`.

## Result

**SUCCESS** — `OpenMath/Chapter3/Section311.lean` compiles axiom-clean:

```
'OpenMath.Chapter3.Section311.lem_311A_order_three' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter3.Section311.bseriesAlphaPartialSum_singleton_vertex_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter3.Section311.lem_311A_order_two' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter3.Section311.lem_311A_order_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Sorry count: `0` (unchanged). Tautology scanner: no matches.
`Chapter3.lean` aggregator builds clean.

File grew from 355 to 565 LOC (+210 LOC for two new public-facing
declarations + one non-vacuity example).

## Faithfulness check

### `iteratedDeriv_three_via_ode` (private helper)

- Entity ID: NONE (private auxiliary, no textbook entity).
- Lean statement: `iteratedDeriv 3 yex x₀ = deriv (deriv f) y₀ * (f y₀)^2 + (deriv f y₀)^2 * f y₀`
  under `ContDiff ℝ 2 f`, `yex x₀ = y₀`, `ContDiff ℝ 4 yex`,
  and `∀ x, HasDerivAt yex (f (yex x)) x`.
- Mathematical content: standard chain-rule + product-rule
  computation. No textbook divergence (helper, not a textbook lemma).
- Hypothesis strength: `ContDiff ℝ 2 f` is the minimum (`deriv f`
  must be differentiable for the second chain-rule layer);
  `ContDiff ℝ 4 yex` allows the order-3 derivative without
  regularity blow-up downstream. Both documented in the docstring.

### `lem_311A_order_three`

- Entity ID: `lem:311A` (`extraction/formalization_data/entities/lem_311A.json`).
- Textbook statement (`statement_latex`):
  > "Let $S_0$ and $S = S_0 \cup\{s\}$ be sets of formal labelling
  > variables, and let $t \in T_{S_0}^*$ be a labelled rooted tree.
  > Then [combinatorial labelling sum identity involving
  > differentiations of elementary differentials]."
- Lean statement captures: **same content for the order-3 Taylor
  specialisation that `lem:311A` underwrites in §311** (the
  combinatorial labelling lemma is multi-cycle scope and not the
  cycle 257 deliverable). Specifically: the residual between the
  exact ODE solution and the third-order Taylor truncation
  `y₀ + h·F(τ₁) + (h²/2)·F(τ₂) + (h³/6)·(F(τ₃) + F(τ₃'))` (in B-series
  notation for the four trees of order ≤ 3) is `O(h^(3+1))` under
  `ContDiff ℝ 2 f` and `ContDiff ℝ 4 yex` regularity. The
  multiplicative form `deriv f y₀ * f y₀` etc. follows the same
  `ℝ → ℝ` scalar convention as cycles 248/256; the polymorphic
  version (with `fderiv ℝ f y₀ (f y₀)` and higher-order
  `iteratedFDeriv` plumbing) is deferred to cycle 258+.
- `lean_status.json` row for `lem:311A` stays `unformalized` per
  cycles 248/256 convention — only Taylor specialisations are
  shipped; full combinatorial labelling content remains absent.
- Tautology check: conclusion (asymptotic `O(h^4)` bound on a
  difference) does not appear verbatim among hypotheses (which are
  smoothness + ODE-shape constraints). ✓
- Identity check: proof is multi-step Taylor + chain rule, not a
  pass-through of any hypothesis. ✓
- Definition smuggling check: no new `def`/`structure`, only two
  `theorem` declarations and one non-vacuity `example`. ✓
- Hypothesis strength check: `ContDiff ℝ 2 f` is the minimum needed
  (cycle 256 needed `ContDiff ℝ 1 f` for one chain-rule layer; one
  more order needs one more derivative). `ContDiff ℝ 4 yex` is the
  Taylor remainder requirement (`n := 4` in `taylor_isLittleO`). ✓

## Dead ends

None this cycle — P1 recipe transferred cleanly from cycle 256 with
no R1–R5 mid-cycle risks materialising. Two transient elaboration
errors during the initial compile pass:

1. `hf_C1.differentiable le_rfl` rejected because `ContDiff.differentiable`
   expects `1 ≠ 0` (not `≤`). Fixed by switching to
   `hf_C1.differentiable_one` (the explicit specialisation for
   `n = 1`, which has no further hypotheses).
2. `Differentiable.comp` was invoked with the function argument
   instead of the second `Differentiable` instance:
   `hderivf_diff.comp yex hyex_diff` rejected. Mathlib's
   `Differentiable.comp` signature is `(hg : Differentiable 𝕜 g)
   (hf : Differentiable 𝕜 f) : Differentiable 𝕜 (g ∘ f)` — fixed by
   dropping the function arg: `hderivf_diff.comp hyex_diff`.

Both fixes single-line; total cycle time well under the 90-minute
P3-fallback threshold.

## Discovery

- `ContDiff.differentiable_deriv_two` is a single Mathlib API that
  directly yields `Differentiable ℝ (deriv f)` from `ContDiff ℝ 2 f`
  without going through `ContDiff.deriv` ↔ `iteratedDeriv 1` bridges.
  Found via `lean_loogle "ContDiff _ 2 _ → Differentiable _ (deriv _)"`
  on the first try. Good single-step search target for higher-order
  refactors.
- `deriv_mul` in Mathlib uses the binary operator form
  `deriv (c * d) x = deriv c x * d x + c x * deriv d x` (under
  `NormedRing 𝔸` `NormedAlgebra 𝕜 𝔸`), but Lean elaborates the
  pointwise lambda `fun x => c x * d x` to `c * d` transparently
  via the Pi instance. No `show`/`change` bridge needed.
- The strategy's R5 (heartbeats decomposition fallback) was
  unnecessary — Lean closed the `ring` + `simp only` steps inside
  default heartbeats even with the longer cubic-coefficient
  expression on the LHS of `hdiff_eq`.

## Suggested next approach

Per strategy §H, three candidates for cycle 258+:

1. **Polymorphic refactor of the `lem_311A_order_one/two/three` trio**
   (multi-cycle, highest-leverage): generalise from `ℝ → ℝ` to
   `N : Type*` with normed-space typeclasses, replacing
   `deriv f y₀ * f y₀` with `fderiv ℝ f y₀ (f y₀)` and higher-order
   analogs. Requires resolving the `iteratedDeriv` → `iteratedFDeriv`
   bridge and `taylorWithinEval` polymorphic plumbing first. Cleanest
   form for §311's downstream `thm:311B` / `thm:311C`.

2. **Aristotle: small `lem:310B` case** for `r = 2` or `r = 3`
   (multi-cycle, requires `Fintype (TruncatedRootedTree N)` for small
   `N` first). Combines cycle 254's `bseriesTerm_eq_theta_smul_bseriesTerm`,
   cycle 255's `TruncatedRootedTree`, cycle 256's `bseriesAlphaPartialSum`,
   plus a small labelled-tree enumeration.

3. **Pivot to a fresh §312/§313 entity**: `lem:312B` (Elementary
   Weight Summation Formula) directly consumes cycle 256's
   `bseriesAlphaTerm` foundation. After cycles 254–257 of
   §310/§311-dedicated work, a §312/§313 pivot may yield broader
   coverage of Chapter 3.

My read: path 1 (polymorphic) gives the cleanest run at `thm:311B`
and unlocks more downstream §311 entities, but path 3 (`lem:312B`)
is more concretely shippable in a single cycle and exercises cycle
256's α-weighted machinery on a textbook landmark. Cycle 258 planner
should choose based on which downstream textbook entity unblocks
more dependents.
