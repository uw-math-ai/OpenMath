# Cycle 259 Results

## Worked on

Order-5 Taylor expansion of the exact solution (`lem_311A_order_five`)
plus its private chain-rule helper `iteratedDeriv_five_via_ode`, both
shipped in `OpenMath/Chapter3/Section311.lean` immediately after cycle
258's `lem_311A_order_four`. This is the deliberate cutoff of the
order-N specialisation chain — orders 1 (cycle 248), 2 (cycle 256),
3 (cycle 257), 4 (cycle 258), 5 (cycle 259) all axiom-clean. P2
(`.prover-state/issues/lem_310B_plan.md`) was not attempted — P1
budget consumed the cycle.

## Approach

P1 strategy was mechanical port of cycle 258 with one extra chain-rule
layer, plus a structural switch to `HasDerivAt`-style assembly for the
helper (cleaner than cycle 258's `deriv_add` / `deriv_mul` /
`deriv_fun_pow` chain for a 3-term sum):

1. **Independent verification of Bell coefficients.** The cycle 258
   task-results §"Suggested next approach" wrote the order-5 closed
   form with coefficients `(1, 11, 7, 26, 1)`. The cycle 259 strategy
   flagged these as wrong and listed `(1, 7, 4, 11, 1)` as verified.
   I re-derived from scratch on paper by differentiating cycle 258's
   order-4 closed form `f'''·f³ + 4·f''·f'·f² + (f')³·f` term-by-term
   under `y' = f(y)`:

   - Term 1 `f'''·f³` differentiates to `f''''·f⁴ + 3·f'''·f'·f³`
     (chain rule on `f'''(y)` plus power rule on `f(y)³`).
   - Term 2 `4·f''·f'·f²` differentiates to
     `4·f'''·f'·f³ + 4·(f'')²·f³ + 8·f''·(f')²·f²`
     (triple product rule with chain rule on each factor).
   - Term 3 `(f')³·f` differentiates to `3·f''·(f')²·f² + (f')⁴·f`
     (power rule + product rule).

   Summing: `f''''·f⁴ + 7·f'''·f'·f³ + 4·(f'')²·f³ + 11·f''·(f')²·f²
   + (f')⁴·f`. Strategy was correct; cycle 258 hint was wrong.

2. **`iteratedDeriv_five_via_ode` helper.** From `ContDiff ℝ 4 f` and
   `ContDiff ℝ 6 yex`:

   - Function-level identity for `iteratedDeriv 4 yex` reuses cycle
     258's `iteratedDeriv_four_via_ode` via `funext x` +
     `(rfl : yex x = yex x)`: the cycle 258 helper applied with
     `x₀ := x` and `y₀ := yex x`. Clean and reusable.
   - Peeled `iteratedDeriv 5 yex x₀ = deriv (iteratedDeriv 4 yex) x₀`
     via `iteratedDeriv_succ`, but had to use `conv_lhs` instead of
     plain `rw [show (5 : ℕ) = 4 + 1 from rfl, iteratedDeriv_succ,
     hiter4]` because of a motive-typechecking failure (see Dead
     ends below).
   - Built four `HasDerivAt` facts via chain rule: `hB` for
     `f ∘ yex`, `hD` for `(deriv f) ∘ yex`, `hC` for
     `(deriv (deriv f)) ∘ yex`, `hA` for `(deriv (deriv (deriv f)))
     ∘ yex`, each via `(...hasDerivAt).comp x₀ hyex'`. **Key
     discovery**: for scalar→scalar, `HasDerivAt.comp` returns
     `outer_deriv * inner_deriv`, not `inner_deriv * outer_deriv`
     as the typeclass form `h' • g'` might suggest. Adjusted the
     derivative annotations accordingly.
   - Assembled the 3-term sum's derivative via `HasDerivAt.mul`,
     `HasDerivAt.const_mul (4 : ℝ)`, `HasDerivAt.pow 2`/`pow 3`,
     `HasDerivAt.add` × 2. Each step type-annotated with the
     expected lambda form (Mathlib's `HasDerivAt.mul` etc. produce
     pointwise `Pi.instMul` forms internally; the annotation
     forces lambda display so the final `.deriv` rewrite matches
     the goal syntactically).
   - Closed by `rw [hTotal.deriv, hyex_x₀]; push_cast; ring`. The
     `push_cast` handles `↑3` and `↑2` Nat → Real coercions from
     `HasDerivAt.pow`.

3. **`lem_311A_order_five` main theorem.** Mechanically mirrors
   cycle 258's `lem_311A_order_four` with:
   - `taylor_isLittleO (n := 6)` (one more than cycle 258's `n := 5`).
   - One extra `Finset.sum_range_succ` unfold in `hT_eval`.
   - New `hderiv5_x0` step invoking the new
     `iteratedDeriv_five_via_ode` helper.
   - Sextic residual `O(h⁶)` step using
     `Asymptotics.isBigO_const_mul_self` on
     `(h⁶/720)·iteratedDeriv 6 yex x₀`.
   - `h^(5+1) = h^6` collapse by `funext`/`ring`.

4. **Non-vacuity witness.** Direct application with `f := fun _ => 0`,
   `yex := fun _ => y₀` discharging hypotheses via `contDiff_const` and
   `hasDerivAt_const`. Residual collapses to identically zero.

## Result

**SUCCESS.** All deliverables shipped:

- `lake env lean OpenMath/Chapter3/Section311.lean` — exit 0.
- `lake env lean OpenMath/Chapter3.lean` (aggregator) — exit 0.
- `lake build OpenMath.Chapter3.Section311` — exit 0 (`.olean` refreshed).
- `grep -c sorry OpenMath/Chapter3/Section311.lean` — `0`.
- `#print axioms OpenMath.Chapter3.Section311.lem_311A_order_five`
  → `[propext, Classical.choice, Quot.sound]` (axiom-clean).
- `#print axioms OpenMath.Chapter3.Section311.lem_311A_order_four`
  → `[propext, Classical.choice, Quot.sound]` (cycle 258
  regression-clean).
- `#print axioms` for `lem_311A_order_three`, `_two`, `_one` all
  unchanged at `[propext, Classical.choice, Quot.sound]`.
- The private helper `iteratedDeriv_five_via_ode` is not addressable
  by qualified name externally; its axiom set is implicit via
  transitive inclusion in `lem_311A_order_five`'s axiom check.
- Tautology scanner regex
  `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` on
  `OpenMath/Chapter3/Section311.lean` — no matches.

Repo sorry count remains 0.

## Faithfulness check

### `lem_311A_order_five`

Entity ID: `lem:311A` (continuing the partial-formalisation chain of
cycles 248/256/257/258). Textbook statement (from
`extraction/formalization_data/entities/lem_311A.json`):

> Let $S = S_0 \cup \{s\}$ be an ordered set, where every member of $S_0$
> is less than $s$. Let $t$ be a member of $T_{S_0}^*$. Then
> $\frac{d}{dx} F(|t|)(y(x))$ is the sum of $F(|u|)(y(x))$ over all
> $u \in T_S^*$ such that the subtree formed by removing $s$ from the
> set of vertices is $t$.

Lean statement captures: **weaker** (a specific specialisation, not
the full combinatorial lemma).

Justification for divergence: identical to cycles 248/256/257/258.
The full `lem:311A` is a combinatorial labelling statement requiring
labelled rooted-tree quotient `def:300C` infrastructure (multi-cycle
scope, not built). Cycle 259 ships the order-5 Taylor specialisation
that `lem:311A` underwrites in Butcher §311: the closed-form Taylor
polynomial at order 5. The nine trees of order 5 contribute their
elementary differentials `F(t)(y₀)`, summed into the closed-form
polynomial `f''''·f⁴ + 7·f'''·f'·f³ + 4·(f'')²·f³ + 11·f''·(f')²·f²
+ (f')⁴·f` (with all derivatives at `y₀`). The combinatorial
coefficients `(1, 7, 4, 11, 1)` aggregate the σ-symmetry factors
across the labelled-tree contributions.

`lean_status.json` row for `lem:311A` stays `unformalized` per the
cycles 248/256/257/258 convention.

### `iteratedDeriv_five_via_ode`

Private helper, no textbook entity, no `lean_status` row.

Hypotheses:
- `ContDiff ℝ 4 f`: minimum regularity for `deriv (deriv (deriv f))`
  to be differentiable (the outermost chain-rule layer at order 5).
- `ContDiff ℝ 6 yex`: matches the Taylor-remainder regularity of
  `lem_311A_order_five`'s `taylor_isLittleO (n := 6)`.
- `yex x₀ = y₀` and `∀ x, HasDerivAt yex (f (yex x)) x`: the ODE
  constraint, carried from cycles 248/256/257/258.

Conclusion textbook content: pointwise Faà di Bruno application —
`d⁵/dx⁵ y = f''''(y)·f(y)⁴ + 7·f'''(y)·f'(y)·f(y)³ + 4·f''(y)²·f(y)³
+ 11·f''(y)·f'(y)²·f(y)² + f'(y)⁴·f(y)`,
which matches the order-5 Bell-polynomial expansion of `y(t)` along
an autonomous ODE `y' = f(y)`. The combinatorial coefficients are
verified on paper before porting; the cycle 258 task-results hint
`(1, 11, 7, 26, 1)` is wrong and was rejected per the cycle 259
strategy's R1 mitigation.

### Tautology/identity/smuggling/strength checks

- Conclusion of `lem_311A_order_five` is a specific `IsBigO` statement
  bounding the residual between `yex(x₀+h)` and the order-5 Taylor
  truncation. It does NOT appear verbatim as any hypothesis. ✓
- Conclusion of `iteratedDeriv_five_via_ode` is a numerical equality
  between `iteratedDeriv 5 yex x₀` and a quartic polynomial in `f` and
  its derivatives at `y₀`. It does NOT appear as any hypothesis. ✓
- Proof of `lem_311A_order_five` is multi-step; not `exact h_*` or
  `:= id`. ✓
- Proof of `iteratedDeriv_five_via_ode` is multi-step Faà-di-Bruno
  chain-rule application via `HasDerivAt`; not `exact h_*` or
  `:= id`. ✓
- No new `structure` or `class` introduced this cycle. ✓
- All hypotheses on `f` and `yex` are textbook-minimum: `ContDiff ℝ 4 f`
  is needed for `Differentiable ℝ (deriv (deriv (deriv f)))`;
  weakening to `ContDiff ℝ 3 f` would break `hderiv3f_diff`.
  `ContDiff ℝ 6 yex` is needed for `taylor_isLittleO (n := 6)`;
  weakening would break `hyex_C6.contDiffOn`. ✓

## Dead ends

Two surprising rough patches:

1. **`rw [show (5 : ℕ) = 4 + 1 from rfl, iteratedDeriv_succ, hiter4]`
   fails with "motive is not type correct".** Cycle 258 used the
   analogous `rw [show (4 : ℕ) = 3 + 1 from rfl, ...]` successfully
   for `iteratedDeriv 4 yex`. Why does cycle 259's `5` rewrite fail
   while cycle 258's `4` rewrite succeeded?

   Diagnosis: the goal at the cycle 259 `rw` site contains the literal
   `(7 : ℝ)` (the Bell coefficient `7`), which internally desugars
   through Lean's `OfNat` instance as
   `@Nat.instAtLeastTwoHAddOfNat 5 Nat.instNeZeroSucc : AtLeastTwo 7`.
   The internal parameter `5` (= 7 - 2) is `(5 : ℕ)` — the same
   literal `rw [(5 : ℕ) = 4 + 1]` is trying to rewrite. Plain `rw`
   over-abstracts: the motive `fun _a => ... NeZero (_a + 1) ...`
   has type `NeZero (_a + 1)` not matching the expected `NeZero 6`,
   so motive typechecking fails.

   In cycle 258, the only `(4 : ℝ)` literal on the RHS desugars with
   internal `(2 : ℕ)` (since `4 = 2 + 2`), not `(4 : ℕ)`. So the
   `(4 : ℕ) = 3 + 1` rewrite didn't conflict.

   Fix: `conv_lhs => rw [show (5 : ℕ) = 4 + 1 from rfl,
   iteratedDeriv_succ, hiter4]`. Confining the rewrite to the LHS of
   the equation skips the RHS's `(7 : ℝ)` instance and avoids the
   over-abstraction. Clean fix; no proof structure compromise.

2. **`HasDerivAt.comp` returns `outer_deriv * inner_deriv`, not
   `inner_deriv * outer_deriv`.** Mathlib's docstring for
   `HasDerivAt.comp` states the result derivative as `h' • g'`
   (`inner • outer`). For scalar→scalar this would naively give
   `inner_deriv * outer_deriv`. But the actual error message showed
   the result as `deriv f (yex x₀) * f (yex x₀)`, which is
   `outer_deriv * inner_deriv`. The `•` reduction for scalars must
   evaluate in the swapped order, or there's a hidden second `comp`
   overload that fires for matching scalar/scalar types.

   Fix: trust the error message, write the four annotations
   (`hB`, `hD`, `hC`, `hA`) with `outer_deriv * inner_deriv`
   order. Once the order matched, all four `comp` applications
   typechecked without `simpa`. `ring` at the end handles any
   remaining commutativity in the polynomial identity.

3. **`HasDerivAt.mul`/`HasDerivAt.add` produce pointwise Pi-mul form
   in display.** When chaining `hA.mul (hB.pow 3)`, the resulting
   `HasDerivAt` has its function displayed as
   `(fun x => deriv (deriv (deriv f)) (yex x)) * (fun x => f (yex x))^3`
   (pointwise multiplication of functions via `Pi.instMul`), not as
   the lambda form `fun x => A x * B x ^ 3`. While the two are defeq,
   `rw [hTotal.deriv]` against a lambda-form goal fails to syntactically
   match.

   Fix: type-annotate each intermediate `hT_i` with the explicit
   lambda form, forcing Lean's elaborator to display in lambda form
   via the expected type. After this, `hTotal.deriv` matches the
   goal cleanly. The annotations are verbose (each lists the
   exact derivative expression) but mechanical.

## Discovery

- **`conv_lhs` is the canonical fix for `(N : ℕ) = ...+1` motive
  collisions in goals with Real-number `(M : ℝ)` literals where
  `M = N + 2`.** The internal `NeZero (N + 1)` instance from the
  OfNat AtLeastTwo path captures `(N : ℕ)`; plain `rw` over-abstracts.
  Confining to one side via `conv_lhs` / `conv_rhs` is clean.
  Pattern generalises for any future Bell/combinatorial-coefficient
  proof where N+2 literals appear alongside `iteratedDeriv N`.

- **`HasDerivAt.comp` for scalar→scalar produces `g' * h'` order
  (`outer_deriv * inner_deriv`)**, despite the typeclass form
  suggesting `h' • g'`. Don't trust the smul-order; trust the
  error message. Write annotations in `g' * h'` order from the
  start.

- **Type-annotating `have hT_i : HasDerivAt (fun x => lambda_expr) _
  x₀ := ...mathlib_lemma...` is the cleanest way to force lambda
  form** after combining via `.mul`, `.pow`, `.add`, etc. Mathlib's
  combinators internally use `Pi.instMul` / `Pi.instAdd` which
  display differently. The explicit type annotation forces the
  elaborator to display in lambda form, which is what the goal's
  `deriv` operator expects.

- **Reusing prior cycles' helpers via `funext x` +
  `(rfl : yex x = yex x)`** is a clean inductive idiom. Cycle 258's
  `iteratedDeriv_four_via_ode` (which assumed `yex x₀ = y₀`) was
  reused at *every* `x` to lift it to a function identity, because
  the conclusion only used `y₀ := yex x` for substitution, and
  `rfl` proves `yex x = yex x`. Pattern: when a downstream cycle
  needs the order-N identity as a function (not just at the
  basepoint), recover via this reuse rather than re-proving.

## Suggested next approach

The order-N specialisation chain (cycles 248/256/257/258/259)
terminates here. Order 6 would require Bell coefficients
`(1, 15, 25, 10, 60, 15, 1)` or similar (paper derivation deferred);
the closed-form expansion grows combinatorially, and the substantive
§311 content beyond order 5 belongs in `lem:310B`'s labelled-tree
infrastructure.

Three viable cycle-260 deliverables:

1. **Pivot to `lem:310B` infrastructure (recommended).** Write a
   scoping issue file at `.prover-state/issues/lem_310B_plan.md`
   describing the labelled-tree quotient `def:300C` infrastructure
   needed (LabelledTree datatype, automorphism quotient, σ-witness
   enumeration), the `T_S^*`-indexed sum structure (Butcher §310
   page 167), and a 5–8 cycle decomposition. The cycle 259 strategy
   listed this as P2 stretch but it was not attempted. **This is
   the highest-leverage long-term move** — every textbook lemma
   from `lem:311A` onward depends on `lem:310B`. Cycle 200/201
   rollback precedent demands a credible single-cycle close at
   every step, so the planner should commit to the plan before
   the worker writes Lean code.

2. **Pivot to a fresh entity (`thm:351B`, `lem:342A`, `lem:342B`).**
   Cycle 258 task results flagged these as candidates that may
   avoid `lem:310B` machinery. Read their JSON entity files first
   to verify dependencies. `thm:351B` (A-stability of RK methods)
   and the Gaussian-quadrature lemmas (`lem:342A`/`B`) are
   substantive §35/§34 entities; if their `transitive_dependencies`
   don't include `lem:310B`, this is a strong pivot candidate.

3. **Polymorphic generalisation of order-1 through order-5.**
   Lift `lem_311A_order_one` through `_order_five` from `ℝ → ℝ`
   scalars to `N : Type*` with `[NormedAddCommGroup N]
   [NormedSpace ℝ N]`, using `iteratedFDeriv ℝ k f y₀` and
   multilinear-map machinery. This is bookkeeping-heavy
   (multilinear-map plumbing per cycle 248 dead-ends documented
   in cycle 248 task results) and lower-priority than (1) or (2).

Recommended pick: **option 1** (`lem:310B` planning). Maintains
the strategic momentum on the textbook's §3 chapter while
escaping the order-N specialisation dead-end. The cycle 200/201
rollback precedent strongly suggests committing to a plan before
code; cycle 259 deliberately did not attempt P2 to leave the
scoping decision to cycle 260's planner.
