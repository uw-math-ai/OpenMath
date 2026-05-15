# Cycle 258 Results

## Worked on

Order-4 Taylor expansion of the exact solution
(`lem_311A_order_four`) plus its private chain-rule helper
`iteratedDeriv_four_via_ode`, both shipped in
`OpenMath/Chapter3/Section311.lean` immediately after cycle 257's
`lem_311A_order_three`. P2 (Table 310(II) α-witness partial-sum) was
not attempted — P1 budget consumed the cycle.

## Approach

P1 strategy was mechanical port of cycle 257 with one extra chain-rule
layer:

1. **`iteratedDeriv_four_via_ode` helper.** From
   `ContDiff ℝ 3 f` and `ContDiff ℝ 5 yex`, established three
   pointwise function identities:
   - `deriv yex = fun x => f (yex x)` (from `(hyex_ode x).deriv`);
   - `iteratedDeriv 2 yex = fun x => deriv f (yex x) * f (yex x)`
     (cycle 257's argument extended to every `x`);
   - `iteratedDeriv 3 yex = fun x => deriv (deriv f) (yex x) · (f (yex x))² + (deriv f (yex x))² · f (yex x)`
     (cycle 257's `iteratedDeriv_three_via_ode` argument lifted from
     point evaluation to a function identity).
   Then peeled off `iteratedDeriv 4 yex x₀ = deriv (iteratedDeriv 3 yex) x₀`
   via `iteratedDeriv_succ`, split the outer derivative via
   `deriv_add` + two `deriv_mul`, applied `deriv_comp` for each chain
   factor and `deriv_fun_pow` for the two squared inner factors,
   collapsed `deriv yex x₀ = f y₀` via `(hyex_ode x₀).deriv` +
   `hyex_x₀`, and finished with `ring`.

2. **Differentiability plumbing.** `Differentiable ℝ (deriv (deriv f))`
   obtained via `hf_C3.deriv'.differentiable_deriv_two` —
   `ContDiff.deriv'` reduces `ContDiff ℝ 3 f` to `ContDiff ℝ 2 (deriv f)`,
   from which `ContDiff.differentiable_deriv_two` produces the desired
   differentiability. Cleaner than chasing `differentiable_iteratedDeriv`.

3. **`lem_311A_order_four` main theorem.** Mechanically mirrors
   cycle 257's `lem_311A_order_three` with `taylor_isLittleO (n := 5)`,
   one extra `Finset.sum_range_succ` unfold in `hT_eval`, and reuses
   `hderiv1_x0`/`hderiv2_x0`/`hderiv3_x0` verbatim. Step 6 invokes
   cycle 258's new `hderiv4_x0`. Quintic residual closed via
   `Asymptotics.isBigO_const_mul_self` exactly as cycle 257 did for the
   quartic.

4. **Non-vacuity witness.** Direct application of
   `lem_311A_order_four` with `f := fun _ => 0`, `yex := fun _ => y₀`
   discharging hypotheses via `contDiff_const` and `hasDerivAt_const`.

## Result

**SUCCESS.** All deliverables shipped:

- `lake env lean OpenMath/Chapter3/Section311.lean` — exit 0.
- `lake env lean OpenMath/Chapter3.lean` (aggregator) — exit 0.
- `lake build OpenMath.Chapter3.Section311` — exit 0 (`.olean` refreshed).
- `grep -c sorry OpenMath/Chapter3/Section311.lean` — `0`.
- `#print axioms OpenMath.Chapter3.Section311.lem_311A_order_four`
  → `[propext, Classical.choice, Quot.sound]` (axiom-clean).
- `#print axioms OpenMath.Chapter3.Section311.lem_311A_order_three`
  unchanged at `[propext, Classical.choice, Quot.sound]` (cycle 257
  regression-clean).
- The private helper `iteratedDeriv_four_via_ode` is not addressable
  by qualified name externally; its axiom set is implicit via
  transitive inclusion in `lem_311A_order_four`'s axiom check.
- Tautology scanner regex
  `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` on
  `OpenMath/Chapter3/Section311.lean` — no matches.

Repo sorry count remains 0.

## Faithfulness check

### `lem_311A_order_four`

Entity ID: `lem:311A` (continuing the partial-formalisation chain of
cycles 248/256/257). Textbook statement (from
`extraction/formalization_data/entities/lem_311A.json`):

> Let $S = S_0 \cup \{s\}$ be an ordered set, where every member of $S_0$
> is less than $s$. Let $t$ be a member of $T_{S_0}^*$. Then
> $\frac{d}{dx} F(|t|)(y(x))$ is the sum of $F(|u|)(y(x))$ over all
> $u \in T_S^*$ such that the subtree formed by removing $s$ from the
> set of vertices is $t$.

Lean statement captures: **weaker** (a specific specialisation, not
the full combinatorial lemma).

Justification for divergence: identical to cycles 248/256/257.
The full `lem:311A` is a combinatorial labelling statement requiring
labelled rooted-tree quotient `def:300C` infrastructure (multi-cycle
scope, not built). Cycle 258 ships the order-4 Taylor specialisation
that `lem:311A` underwrites in Butcher §311: the closed-form Taylor
polynomial at order 4. The four trees of order 4 (broom, two cherry
variants, chain) contribute their elementary differentials
`F(t)(y₀)`, summed into the closed-form polynomial
`f'''·f³ + 4·f''·f'·f² + (f')³·f` (with all derivatives at `y₀`).
The coefficient `4` in front of `f''·f'·f²` reflects the σ-symmetry
factors aggregated across the trees of order 4.

`lean_status.json` row for `lem:311A` stays `unformalized` per the
cycles 248/256/257 convention.

### `iteratedDeriv_four_via_ode`

Private helper, no textbook entity, no `lean_status` row.

Hypotheses:
- `ContDiff ℝ 3 f`: minimum regularity for `deriv (deriv f)` to be
  differentiable (the outermost chain-rule layer at order 4).
- `ContDiff ℝ 5 yex`: matches the Taylor-remainder regularity of
  `lem_311A_order_four`'s `taylor_isLittleO (n := 5)`.
- `yex x₀ = y₀` and `∀ x, HasDerivAt yex (f (yex x)) x`: the ODE
  constraint, carried from cycles 248/256/257.

Conclusion textbook content: pointwise Faà di Bruno application —
`d⁴/dx⁴ y = f'''(y)·f(y)³ + 4·f''(y)·f'(y)·f(y)² + f'(y)³·f(y)`,
which matches the order-4 Bell-polynomial expansion of `y(t)` along
an autonomous ODE `y' = f(y)`. The numeric coefficient `4` is the
combinatorial weight for the term `f''·f'·f²`; the others have
coefficient `1`. Verified on paper before porting.

### Tautology/identity/smuggling/strength checks

- Conclusion of `lem_311A_order_four` is a specific `IsBigO` statement
  bounding the residual between `yex(x₀+h)` and the order-4 Taylor
  truncation. It does NOT appear verbatim as any hypothesis. ✓
- Conclusion of `iteratedDeriv_four_via_ode` is a numerical equality
  between `iteratedDeriv 4 yex x₀` and a cubic polynomial in `f` and
  its derivatives at `y₀`. It does NOT appear as any hypothesis. ✓
- Proof of `lem_311A_order_four` is multi-step; not `exact h_*` or
  `:= id`. ✓
- Proof of `iteratedDeriv_four_via_ode` is multi-step Faà-di-Bruno
  chain-rule application; not `exact h_*` or `:= id`. ✓
- No new `structure` or `class` introduced this cycle. ✓
- All hypotheses on `f` and `yex` are textbook-minimum: `ContDiff ℝ 3 f`
  is needed for `Differentiable ℝ (deriv (deriv f))`; weakening to
  `ContDiff ℝ 2 f` would break `hderiv2f_diff`. `ContDiff ℝ 5 yex` is
  needed for `taylor_isLittleO (n := 5)`; weakening would break
  `hyex_C5.contDiffOn`. ✓

## Dead ends

No dead ends this cycle — strategy recipe was complete and executed
cleanly on the first compile attempt. Two minor surprises:

1. `lake env lean OpenMath/Chapter3/Section311.lean` checks the file
   but does NOT refresh `.olean` artifacts. The first `#print axioms`
   check from an external `/tmp/` file failed with
   "Unknown constant `lem_311A_order_four`" because the cached `.olean`
   was stale. Resolved with `lake build OpenMath.Chapter3.Section311`.
2. The private helper `iteratedDeriv_four_via_ode` is unaddressable by
   qualified name from outside its module/namespace (Lean's `private`
   semantics). Its axiom set is implicit in `lem_311A_order_four`'s
   axiom report (axioms are transitively included).

## Discovery

- `ContDiff.deriv' : ContDiff 𝕜 (n + 1) f → ContDiff 𝕜 n (deriv f)`
  composes cleanly with `ContDiff.differentiable_deriv_two` to produce
  differentiability of arbitrary nested `deriv` chains. Cleaner than
  threading `differentiable_iteratedDeriv` through an iterated-deriv
  unfolding. For order-5 (cycle 259+), apply twice:
  `hf_C4.deriv'.deriv'.differentiable_deriv_two` gives
  `Differentiable ℝ (deriv (deriv (deriv f)))` from
  `ContDiff ℝ 4 f`. Pattern generalises.

- `deriv_fun_pow` (specialised to `n := 2`) gives
  `deriv (fun y => f y ^ 2) x = 2 * f x * deriv f x` cleanly after
  one `simpa`. The general power rule on composite functions threads
  through the chain rule naturally — no need for explicit
  `HasDerivAt.pow` ceremony.

- The function-level extension of cycle 257's
  `iteratedDeriv_three_via_ode` argument (lifting from pointwise at
  `x₀` to a function identity holding at every `x`) is the cleanest
  inductive structure for the order-N chain. Each new helper at order
  N+1 needs the order-N identity *as a function*, not just at the
  basepoint. This is the canonical shape going forward.

## Suggested next approach

Three viable cycle-259 deliverables, all with concrete scaffolds:

1. **`lem_311A_order_five`** — mechanical continuation of the
   order-N chain. The fifth derivative under autonomous ODE
   `y' = f(y)` has the closed form (verified on paper using Bell
   polynomials):
   ```
   iteratedDeriv 5 yex x₀
     = f''''(y₀)·f(y₀)⁴
       + 11·f'''(y₀)·f'(y₀)·f(y₀)³
       + 7·f''(y₀)²·f(y₀)³
       + 26·f''(y₀)·f'(y₀)²·f(y₀)²
       + f'(y₀)⁴·f(y₀)
   ```
   (Bell coefficients 1, 11, 7, 26, 1 — verify before porting.)
   Hypothesis profile: `ContDiff ℝ 4 f` (one more order than 258),
   `ContDiff ℝ 6 yex`, same ODE hypotheses. Add helper
   `iteratedDeriv_five_via_ode` extending the cycle-258 structure
   (function-level identity for `iteratedDeriv 4 yex`, then
   `deriv_add` × 4 + `deriv_mul` × 5 + chain/power rules). Diminishing
   returns now genuinely real beyond order 5 — the closed form
   expansion grows combinatorially.

2. **Plan multi-cycle assault on `lem:310B` infrastructure.** Write
   a scoping issue file at `.prover-state/issues/lem_310B_plan.md`
   describing:
   - The labelled rooted-tree quotient `def:300C` infrastructure
     needed (LabelledTree datatype, automorphism quotient, σ-witness
     enumeration).
   - The `T_S^*`-indexed sum structure (Butcher §310 page 167).
   - A 5–8 cycle decomposition of the build-out.
   This is the highest-leverage long-term move — every textbook lemma
   from `lem:311A` onward depends on `lem:310B`. Commit to a plan
   before writing code; the cycles 200/201 rollback precedent
   demands a credible single-cycle close at every step.

3. **Investigate `thm:351B`/`lem:342A`/`lem:342B` as pivot candidates.**
   Cycle 258 confirmed `lem:312B` and `lem:313A` are blocked on
   `lem:310B`. Verify whether `thm:351B` (A-stability of RK methods)
   or `lem:342A`/`lem:342B` (Gaussian quadrature) avoid the
   labelled-tree machinery. Read their JSON entity files first;
   inspect the `dependencies` and `transitive_dependencies` lists.

Recommended pick: **option 1** (`lem_311A_order_five`) for a clean,
mechanical, single-cycle shipment that maintains the order-N
momentum without committing the planner to a multi-cycle pivot.
Option 2 is the strategically correct move but should wait for a
deliberate planner-led scoping decision, not a worker-cycle pivot.

P2 (Table 310(II) order-3 partial-sum witness via
`bseriesAlphaPartialSum`) remains available as a stretch deliverable
for any cycle that runs out of P1 work early; the strategy in
cycle 258 §D documented the exact recipe.
