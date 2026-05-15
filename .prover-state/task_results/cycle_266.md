# Cycle 266 Results

## Worked on

§310/§311 Phase E.1 closure (per strategy): introducing the
**exact-solution** B-series term `bseriesExactTerm` (Butcher §312 —
the `h^{r(t)} / (σ(t)·γ(t))` form, with `1/γ(t)` factor that cycle
256's `bseriesAlphaTerm := α • bseriesTerm` is missing), the
partial-sum API, the scalar cherry closed form, and the bridge to
cycle 256's `lem_311A_order_two`.

## Approach

Followed the strategy as written. Two files modified:

### `OpenMath/Chapter3/Section301.lean` (+~165 LOC)

Added inside the existing `OpenMath.Chapter3.Section310.RootedTree`
namespace, immediately after cycle 256's `bseriesAlphaPartialSum`
block:

1. **`bseriesExactTerm`** (`noncomputable def`):
   `(h^r(t) / (σ(t) · γ(t))) • elementaryDiff f y₀ t`. Polymorphic
   in `E : Type*` with `[NormedAddCommGroup E] [NormedSpace ℝ E]`.
   The docstring distinguishes it from cycle 256's `bseriesAlphaTerm`
   (Butcher (310i) RK-method form, without `1/γ`) and cites Butcher
   §312 + (301a) for the factorial denominator collected by `γ(t)`.

2. **`bseriesExactTerm_vertex`**: closure at `τ` —
   `bseriesExactTerm f y₀ h vertex = h • f y₀`. Proof: `unfold` +
   `simp` with `iteratedFDeriv_zero_apply` + the `rfl`-reducible
   `tau_values` (order/σ/γ all = 1 at `mk []`).

3. **`bseriesExactTerm_cherry_scalar`** (the load-bearing
   faithfulness witness): for `f : ℝ → ℝ`,
   `bseriesExactTerm f y₀ h cherry = h^2/2 * (deriv f y₀ * f y₀)`.
   Proof recipe: unfold + `rfl`-reduce `(order, σ, γ) cherry =
   (2, 1, 2)`; compute `elementaryDiff f y₀ (mk [vertex])` via
   `iteratedFDeriv_one_apply` (Mathlib) + `fderiv_eq_smul_deriv` +
   `smul_eq_mul` (scalar); `push_cast` + `ring` for the final
   numerical normalization (Nat casts of σ, γ).

4. **`bseriesExactPartialSum`** + `_empty` (`@[simp]`) + `_insert` +
   `_singleton` + `_union`: exact ports of cycle 256's
   `bseriesAlphaPartialSum_*` shape.

5. Three non-vacuity witnesses: `{vertex}` (= `h • f y₀`),
   `{vertex, cherry}` (= `h • f y₀ + h²/2 · (f' · f)`, exercises
   `bseriesExactTerm_cherry_scalar`), and `id : ℝ → ℝ` on
   `{vertex}` (= `h • y₀`).

### `OpenMath/Chapter3/Section311.lean` (+~70 LOC)

Added immediately after cycle 256's
`bseriesAlphaPartialSum_singleton_vertex_eq`:

1. **`lem_311A_order_two_partialSum`**: scalar `ℝ → ℝ` order-2
   Taylor expansion of the exact solution, restated using
   `bseriesExactPartialSum f y₀ h {vertex, cherry}` in place of the
   closed-form polynomial. Proof: rewrite the partial sum via
   `_insert` + `_singleton` (using `vertex ∉ {cherry}` via `simp`
   on the underlying `mk` constructor inequality), collapse via
   `bseriesExactTerm_vertex` + `bseriesExactTerm_cherry_scalar` +
   `smul_eq_mul` + `ring`, then `IsBigO.congr'` reduces the goal
   to cycle 256's `lem_311A_order_two`.

2. Non-vacuity witness on `f := 0, yex := const y₀` (residual
   identically zero, discharged by `lem_311A_order_two_partialSum`
   applied at the trivial witnesses).

## Result

**SUCCESS** — all P1, P2, P3, P4 deliverables shipped. No Backup B
fallback needed.

* `lake env lean OpenMath/Chapter3/Section301.lean`: exits 0.
* `lake env lean OpenMath/Chapter3/Section311.lean`: exits 0.
* `lake build OpenMath.Chapter3`: 2861 jobs, 0 errors.
* `grep -c sorry OpenMath/Chapter3/Section{301,311}.lean`: both 0.
* Tautology-scanner regex
  (`:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$`) on both files:
  no matches.
* Axiom verification on all seven new public theorems
  (`bseriesExactTerm_vertex`, `bseriesExactTerm_cherry_scalar`,
  `bseriesExactPartialSum_{empty,insert,singleton,union}`,
  `lem_311A_order_two_partialSum`): each depends only on
  `[propext, Classical.choice, Quot.sound]`.

## Faithfulness check

### `bseriesExactTerm` (new `def`)

* Entity: Butcher §312 (the exact-solution B-series). Quoted
  textbook content per the strategy §G:

  > `y(x₀+h) = Σ (h^n/n!) y^(n)(x₀)` (Taylor), combined with
  > `lem:311A`'s `y^(n)(x₀) = Σ_{r(t)=n} α(t) F(t)(y₀)`, gives
  > per-tree coefficient `h^{r(t)} · α(t)/r(t)! = h^{r(t)}/(σ(t)·γ(t))`.

* Lean statement captures: **same content** as the §312
  exact-solution coefficient.

* Divergence from cycle 256's `bseriesAlphaTerm`: explicit and
  documented in the file docstring. The two are distinct but valid
  textbook objects:
  - `bseriesAlphaTerm := α • bseriesTerm` is the Butcher-(310i)
    *RK-method* form (no `1/r!` factor; α(cherry) = 1 gives
    `h² · f' · f`).
  - `bseriesExactTerm := bseriesTerm / γ` is the *exact-solution*
    Taylor B-series form (with the `1/r!` factor collected into
    `γ(t)` via Butcher (301a) `γ(t) = r(t) · ∏ γ(tᵢ)`; at cherry
    this gives `h²/2 · f' · f`, matching Taylor's theorem).
  Both forms are valid textbook objects; `lem:310B`'s eventual
  formalisation will bridge them.

### `bseriesExactTerm_vertex`

* Captures: same content as Butcher's `α(τ) = σ(τ) = γ(τ) = r(τ) = 1`
  base case (Butcher (301d) + the `F(τ)(y) = f(y)` recursive
  base of (310g)).

### `bseriesExactTerm_cherry_scalar`

* Captures: same content as Butcher's Taylor expansion at cherry:
  `α(cherry)/2! · h² · F(cherry)(y₀) = (1/2) · h² · (f'(y₀)·f(y₀))`.
  Restricted to scalar `ℝ → ℝ` because cycle 256's
  `lem_311A_order_two` (the consumer in P3) is itself scalar; the
  polymorphic version requires the multilinear-map plumbing
  (cycle 265's HIGH-risk flag) and is cycle 267+ scope.

### `bseriesExactPartialSum` + `_empty`/`_insert`/`_singleton`/`_union`

* Captures: same content as the §312 exact-solution B-series
  truncated to a hand-supplied `Finset RootedTree`. Mechanical
  `Finset.sum_*` algebra; structurally identical to cycle 255's
  `bseriesPartialSum_*` and cycle 256's `bseriesAlphaPartialSum_*`
  on a different summand. No new mathematical content.

### `lem_311A_order_two_partialSum`

* Entity: Butcher §311 Taylor expansion of the exact solution
  (the order-2 truncation). Captures the same content as cycle
  256's `lem_311A_order_two`, restated using
  `bseriesExactPartialSum f y₀ h {vertex, cherry}`.

* Lean statement captures: **same content** — `IsBigO.congr'`
  bridges the two forms pointwise (the partial sum is
  definitionally `h • f y₀ + h²/2 · (f' · f)`).

* No new mathematical content beyond the partial-sum repackaging;
  the substantive Taylor work lives in cycle 256's underlying
  `lem_311A_order_two`.

### Pre-commit checklist

* **Tautology check**: no theorem conclusion equals one of its
  hypotheses literally. The bridge theorem's conclusion involves
  `bseriesExactPartialSum`, which does not appear in any hypothesis.
* **Identity check**: no proof is just `exact h`. The shortest
  proofs (`_empty`/`_singleton`) use `simp` to unfold the
  definition; the bridge uses a multi-step rewrite.
* **Definition-smuggling check**: `bseriesExactTerm` defines a
  genuine new object (the Butcher §312 form). The accompanying
  closure theorems (`_vertex`, `_cherry_scalar`) are real
  computational identities, not definitional unfoldings dressed up.
  Hypothesis-vs-conclusion distinction is correct everywhere.
* **Hypothesis strength check**: `lem_311A_order_two_partialSum`
  uses the same hypotheses as cycle 256's `lem_311A_order_two`
  (`ContDiff ℝ 1 f`, `yex x₀ = y₀`, `ContDiff ℝ 3 yex`,
  `∀ x, HasDerivAt yex (f (yex x)) x`) — no strengthening. The
  scalar restriction on `_cherry_scalar` is documented and
  inherited from the consumer.
* **Absent-theorem check**: no "will be proved with sorry" or "is
  stated below" promises in the new code.

## Dead ends

Two minor friction points during the cherry-scalar proof, both
resolved within ~5 minutes each:

1. **Cast handling at the σ·γ denominator**. Initial attempt
   tried `show ... ((1 : ℝ) * (2 : ℝ)) ...` after `rfl`-reducing
   `symmetry/density cherry`. Lean's elaborator preserved the
   `((1 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)` cast form, so the `show` failed
   on definitional equality. Fix: drop the intermediate `show`,
   let `rw [hED]` compute the elementaryDiff, then `smul_eq_mul`
   + `push_cast` + `ring` collapse the Nat-cast denominator.

2. **`unfold elementaryDiff` motive issue**. The first attempt
   wrote `show iteratedFDeriv ℝ ([vertex].length) ...` to match
   the unfolded form, but `[vertex].length` isn't `rfl`-reduced to
   `1` in the goal — the show pattern didn't match. Fix: rewrite
   the length first via `show iteratedFDeriv ℝ 1 ...` after the
   `unfold` (Lean accepts this because `[vertex].length = 1` by
   `rfl`).

Neither stalled the cycle. The strategy §J Aristotle fallback was
not needed.

## Discovery

* **`iteratedFDeriv_one_apply` + `fderiv_eq_smul_deriv` is the
  canonical 1-input collapse for scalar functions.** Together
  they reduce `iteratedFDeriv ℝ 1 f y₀ m` to `(m 0) * deriv f y₀`
  in the `ℝ → ℝ` case in two rewrites. This is the recipe seed
  for any future per-tree closed-form proof at order 2 (the same
  collapse will be needed at `mk [vertex]` for polymorphic `E`,
  with the multilinear-map curry chain replacing the scalar
  collapse).

* **The `bseriesAlphaTerm` vs `bseriesExactTerm` distinction is
  load-bearing.** Cycle 265's "Option 1 Phase E.1" recommendation
  would have built a literally false theorem (factor-of-2
  mismatch at cherry). The strategy's pre-flight analysis was
  correct that the factorial denominator from `γ(t)` is invisible
  at `r = 1` (where `γ(τ) = 1`) but bites at `r ≥ 2`. Future
  planners should keep both definitions in the codebase: the
  RK-method form (without `1/γ`) for `lem:310B`'s LHS, the
  exact-solution form (with `1/γ`) for §311's Taylor side.

* **Cycle 256's `lem_311A_order_two` discharges the bridge in
  one line.** Once `bseriesExactPartialSum f y₀ h {vertex, cherry}`
  is unfolded to the closed-form polynomial, the residual is
  *literally* cycle 256's conclusion. `IsBigO.congr'` does all the
  heavy lifting; no new Taylor work needed.

## Suggested next approach

Strategy §H listed cycle 267 candidates. In rough preference order:

1. **`lem_311A_order_three_partialSum`** — bridge cycle 257's
   order-3 closed form to `bseriesExactPartialSum` over the four
   trees of order ≤ 3. Same recipe as cycle 266's Phase E.1
   bridge, with `bseriesExactTerm_broom₃_scalar` and
   `bseriesExactTerm_mk_vertex_vertex_scalar` (depth-2 chain
   tree) added to the per-tree closed-form catalog. Estimated
   ~120 LOC, single cycle, axiom-clean target.

2. **Polymorphic `bseriesExactTerm_cherry` (Phase D.1
   continuation)** — lift cycle 266's scalar cherry closed form
   to general `E`. The `iteratedFDeriv_one_apply` recipe ports;
   the `fderiv_eq_smul_deriv` step becomes a `ContinuousMultilinearMap`
   evaluation. This is the cycle 265 HIGH-risk concern, but it
   now fires at a *single concrete tree* rather than over an
   abstract truncation — much easier. ~100 LOC.

3. **`lem:342A`** (Legendre orthogonality on `[0,1]`) — single-cycle,
   `lem:310B`-independent target if the §310/§311 track stalls.
   Per `lem_310B_plan.md` §8.2.

Recommend (1) for momentum. It compounds the cycle 266 work
without committing to the multilinear-map plumbing of (2), and
keeps §311 partial-sum infrastructure on track toward the full
`lem:310B` capstone.
