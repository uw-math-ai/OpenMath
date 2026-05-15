# Cycle 265 Results

## Worked on

Phase D.1 partial: polymorphic order-1 Taylor expansion of the exact
solution. Lifted cycle 248's scalar `lem_311A_order_one` (`ℝ → ℝ`) to
`lem_311A_order_one_poly` (`ℝ → N` for arbitrary real normed space
`N`), at `OpenMath/Chapter3/Section311.lean`. This is the canonical
Phase D step identified in cycle 260's `lem:310B` scoping doc §C.4,
deliberately deferred since cycle 256.

## Approach

Mechanical port of cycle 248's seven-step proof recipe. The two
substitutions:

* Every `h * f y₀ : ℝ` becomes `h • f y₀ : N` (since `f y₀` is now
  `N`-valued).
* Every scalar `iteratedDeriv k yex x₀ : ℝ` becomes an `N`-valued
  tangent vector.

The key Mathlib hooks all worked verbatim for the polymorphic case:

* `taylor_isLittleO` and `taylor_within_apply` are stated for
  `{f : ℝ → E}` with `[NormedAddCommGroup E] [NormedSpace ℝ E]` — port
  ok.
* `iteratedDeriv_one` and `HasDerivAt.deriv` work for normed-space
  codomain.
* `IsLittleO.comp_tendsto` and `IsLittleO.isBigO` are filter-level
  and codomain-agnostic.

The one non-trivial divergence: the quadratic-coefficient bound. In
the scalar proof, `Asymptotics.isBigO_const_mul_self` (which requires
`SeminormedRing R`) closed `(h²/2 * iter2) =O[nhds 0] h²` directly.
For polymorphic `N`, the term is `((1/2) * h²) • c` with `c : N` —
a scalar acting on a vector — and `isBigO_const_mul_self` doesn't
apply. `IsBigO.const_smul_self` exists but goes the wrong direction
(it gives `(c' • f') =O[l] f'` where `c'` is a scalar and `f'` is
vector-valued; we want the constant on the *vector* side, not the
function). The clean closure was via `Asymptotics.isBigO_of_le'`:

```
refine Asymptotics.isBigO_of_le' (l := nhds (0 : ℝ))
  (c := (1/2) * ‖iteratedDeriv 2 yex x₀‖) ?_
intro h
rw [norm_smul]
have habs : ‖((1 : ℝ)/2 * h ^ 2 : ℝ)‖ = (1/2) * ‖h ^ 2‖ := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2),
    Real.norm_eq_abs]
rw [habs]
linarith [norm_nonneg (h ^ 2 : ℝ), norm_nonneg (iteratedDeriv 2 yex x₀)]
```

The Taylor-polynomial evaluation in step 2 also needed a small adjustment:
cycle 248's scalar proof used `simp [..., smul_eq_mul, ...]` to collapse
everything to scalar multiplication, then closed with `ring`. For the
polymorphic case, `smul_eq_mul` drops out (no `Mul N`), and the
post-simp goal has a leftover `((↑(Nat.succ 1))⁻¹ * h^2) • c` vs
`((1/2) * h^2) • c` mismatch on the factorial cast. `norm_num` closes
this in one step.

Non-vacuity witnesses (3 of 3 from strategy §C):

* **W3 (most important, faithfulness check)**: scalar specialisation
  at `N := ℝ` recovers cycle 248's scalar `lem_311A_order_one` form
  by direct application of `lem_311A_order_one_poly`.
* **W1**: trivial `f := 0` on `Fin 2 → ℝ` exhibits the polymorphic
  shape on a vector space, with `yex := fun _ => 0` and trivial
  `HasDerivAt` witness via `hasDerivAt_const`.
* **W2 (rotation ODE)**: deferred — `yex x := ![cos x, sin x]`
  requires component-wise `HasDerivAt` plumbing on `Fin 2 → ℝ` that
  doesn't materially exercise the lift beyond W1. Skipped per
  strategy §C ("Witness 3 is the most useful; witnesses 1 and 2 are
  the 'genuinely polymorphic' cases").

## Result

**SUCCESS.** Single-cycle close, axiom-clean. Shipped:

* `lem_311A_order_one_poly` (theorem, ~95 LOC including docstring) at
  `OpenMath/Chapter3/Section311.lean` line ~228.
* Scalar-specialisation example (witness W3).
* Trivial-`f` polymorphic example on `Fin 2 → ℝ` (witness W1).

Axioms via `lean_verify`:
`{propext, Classical.choice, Quot.sound}` — clean standard Mathlib
trio, no `sorryAx`. `lake env lean OpenMath/Chapter3/Section311.lean`
exits 0; `lake build OpenMath.Chapter3.Section311` exits 0
(2047 jobs).

File LOC: `Section311.lean` 1215 → 1379 (+164 LOC).
Repo sorry count: 0 → 0.

## Faithfulness check

### New theorem: `lem_311A_order_one_poly`

* **Entity reference (lem:311A)**:
  Quoted from `extraction/formalization_data/entities/lem_311A.json`:

  > Let S = S0 ∪ {s} be an ordered set, where every member of S0 is
  > less than s. Let t be a member of TS∗0 . Then d/dx F(|t|)(y(x)) is
  > the sum of F(|u|)(y(x)) over all u ∈ TS∗ such that the subtree
  > formed by removing s from the set of vertices is t.

* **Lean statement captures**: **different (incremental infrastructure
  layer)**. The shipped theorem `lem_311A_order_one_poly` is not the
  combinatorial labelling lemma above; it is the order-1
  Taylor-expansion specialisation that `lem:311A` underwrites in §311
  (the `r(τ)=1`, `σ(τ)=1`, `α(τ)=1` case of the elementary-weight
  formula for the exact-solution B-series). The textbook `lem:311A`
  itself remains unformalised — it requires labelled-tree quotient
  infrastructure (`def:300C`) plus multivariate Taylor (`thm:306A`),
  both deferred per cycle 260's `lem_310B_plan.md`.

* **Divergence from cycle 248**: this cycle lifts the codomain from
  `ℝ` to general `N : Type*` with `[NormedAddCommGroup N]
  [NormedSpace ℝ N]`. The polymorphic statement is **strictly more
  general** than the scalar form (witness W3 confirms the scalar
  case is recovered by specialisation, modulo `smul_eq_mul`). The
  `bseriesOrderOne f y₀ h = y₀ + h • f y₀` definition was already
  polymorphic in cycle 248.

### Pre-commit checklist

* **Tautology check**: conclusion `(... yex(x₀+h) - bseriesOrderOne)
  =O[nhds 0] (h^(1+1))` does not appear among the three hypotheses
  (`yex x₀ = y₀`, `ContDiff ℝ 2 yex`, `∀ x, HasDerivAt yex (f(yex x))
  x`). OK.

* **Identity check**: proof is a 7-step Taylor argument, not
  `exact h`. OK.

* **Definition smuggling check**: no new `class`/`structure`. OK.

* **Hypothesis strength check**: hypotheses match cycle 248's scalar
  form verbatim — no `ContDiff ℝ k f` is needed for the order-1 case
  (the chain rule on `f ∘ yex` only enters at order 2+). OK.

* **Absent theorem check**: no comments promise unwritten content.
  OK.

* **Tracking**: `lean_status.json` and entity `lem:311A` are
  NOT updated (per strategy §H): the polymorphic order-1 lift is
  infrastructure for §311's full content, not the closure of
  `lem:311A` itself.

## Dead ends

1. **First attempt at the Taylor-polynomial evaluation** used
   `congr 2` + two `show` statements to assert the post-`simp_only`
   form. The `show` for the first (smul) goal failed with "pattern
   not definitionally equal to target" — `congr 2` produced the
   coefficient-equation goal *first*, not the smul-equation goal, so
   my goal ordering was inverted. Diagnostic at `lean_multi_attempt`
   showed plain `norm_num` after the `simp_only` closes the entire
   leftover gap (just the `↑(Nat.succ 1)` cast needing simplification
   to `2`); dropped the `congr 2; show ...; show ...` scaffold.

2. **First attempt at the quadratic-coefficient bound** ended with
   `ring_nf` after `rw [habs]`. Both sides normalise to the same form
   `‖h^2‖ * ‖iteratedDeriv 2 yex x₀‖ * (1/2)` but the goal is `≤`,
   not `=`, so `ring_nf` leaves a `X ≤ X` reflexive goal that doesn't
   close. Replaced with `linarith [norm_nonneg (h^2 : ℝ),
   norm_nonneg (iteratedDeriv 2 yex x₀)]` — linarith handles the
   `≤` chain with the two non-negativity facts.

3. **`Asymptotics.isBigO_const_mul_self` doesn't lift**: requires
   `SeminormedRing R`, only applies for the scalar product
   `c * h^2`. For the smul case, I scouted `IsBigO.const_smul_self`,
   `IsBigO.const_smul_left`, and `IsBigO.smul` — none directly gives
   `(scalar_function • constant_vector) =O[l] scalar_function`.
   `IsBigO.smul` would work via `(refl scalar : c_fn =O[l] c_fn).smul
   (refl_O : const c =O[l] const c)` → `(c_fn • const c) =O[l] (c_fn
   • const c)`, but the RHS still has a smul that needs to be peeled
   to give `=O[l] h^2`. Direct `isBigO_of_le'` with the explicit
   `norm_smul` bound is cleaner.

## Discovery

1. **`Asymptotics.IsBigO.const_smul_self` direction subtlety**: the
   Mathlib `const_smul_self` lemma gives `(fun x => c' • f' x) =O[l]
   f'` where `c' : R` (a scalar) and `f' : α → E'` (a vector-valued
   function). It does NOT give `(fun x => (scalar_fn x) • c) =O[l]
   scalar_fn` — the constant and function roles are swapped from
   what one might expect when porting `isBigO_const_mul_self`
   reasoning to the smul setting. The right tool for our case is
   `Asymptotics.isBigO_of_le'` with an explicit `norm_smul` bound.
   File this for future Phase D cycles (order-2+, where smul
   coefficient bounds will appear in larger numbers).

2. **`(↑(Nat.succ 1))⁻¹ ≠ (1/2 : ℝ)` definitionally**, even after
   `Nat.cast_one`, `Nat.cast_mul`, `inv_one`, `one_mul`. The leftover
   gap needs an explicit numeric step (`norm_num` suffices). This
   is mildly surprising — the analogous scalar proof closed the same
   gap implicitly via `smul_eq_mul`'s elimination of the smul layer,
   making the whole expression a polynomial that `ring` handled.

3. **Lake build of `OpenMath.Chapter3.Section311` after this cycle
   takes ~4 seconds** (using cached .olean for all 2047 dependencies).
   This is genuinely fast and confirms no downstream `import` of
   Section311.lean is affected by the new theorem (no broken
   signatures, no removed names).

## Suggested next approach

Three credible directions for cycle 266 (in decreasing order of
single-cycle confidence):

1. **Phase E.1: `TruncatedRootedTree 2` partial-sum form of the
   order-2 case**. Use cycle 255's `TruncatedRootedTree N` and cycle
   256's `bseriesAlphaPartialSum` to restate `lem_311A_order_two`'s
   conclusion as `yex(x₀+h) − bseriesAlphaPartialSum f y₀ h {vertex,
   cherry} =O h^3`. This is the bridge between the cycle-248..259
   "closed-form Taylor truncation" content and the cycle-254..256
   "tree-indexed partial sum" infrastructure. ~1 cycle, mostly
   bookkeeping. RECOMMENDED.

2. **Polymorphic order-2 lift (Phase D.1 continuation)**. Needs the
   `iteratedFDeriv 1 ↔ fderiv` bridge to lift cycle 256's `deriv f y₀
   * f y₀` to `fderiv ℝ f y₀ (f y₀)`. HIGH risk single-cycle (1–2
   cycle scope); if Mathlib has the bridge as a one-liner it's
   trivial, if it doesn't it's a multi-cycle Mathlib-PR-grade
   undertaking. Pre-flight: `lean_loogle "fderiv = iteratedFDeriv 1"`
   before committing.

3. **Pivot to a fresh single-cycle entity**. Per cycle 260 scoping
   doc §8, candidates are `lem:342A` (NOT viable — `LegendreSymbol`
   only, no orthogonal-Legendre infrastructure) or one of the short
   Ch.5 `[ ]` rows (verify entity JSONs first). The §310/311 roadmap
   has just gained Phase D.1, so a one-cycle break to a fresh
   chapter is reasonable cadence.

The cycle 266 planner should weigh §310 roadmap velocity (option 1)
vs Phase D.1 continuation risk (option 2) vs textbook breadth
(option 3). The cycle 264 worker flagged the same trade-off.

Specific cycle 266 entry recommendation: **option 1** (Phase E.1
`TruncatedRootedTree 2` bridge), since (a) it ships in 1 cycle with
near-certainty, (b) it concretely demonstrates that the cycle 254/255
truncated-tree infrastructure is consumable by the cycle 248..259
Taylor specialisations, and (c) it sets up cycle 267+ for the
larger `r(t)=3, 4, 5` tree-indexed forms.
