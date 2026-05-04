# Cycle 746 Results

## Worked on

- §0 housekeeping in `plan.md` (per strategy).
- New file `OpenMath/EulerAsymptoticError.lean` (Butcher §215 — sorry-first
  scaffold for the Euler asymptotic error formula).
- Step 3 closure: `variationalSolution_isSolution` proved sorry-free via
  Picard–Lindelöf.

## Approach

Housekeeping pass on `plan.md`:
- Split the §46 bullet so §463 is marked `[x]` with a pointer to
  `OpenMath/MilneDevice.lean` (`milneAB4AM3`, `milneFactor = -(19/270)`),
  while §460–§462 stay `[ ]`.
- Replaced the `## Current Target` body (Milne device) with the §215
  scaffold body specified by the strategy.
- Deleted backlog item #4 (Milne device), renumbered 5→4 … 9→8.
- Appended the cycle 744 frontier line summarising the §463 closure.

`OpenMath/EulerAsymptoticError.lean` lands:
1. `def variationalRHS` — the variational ODE RHS (no sorry).
2. `structure EulerAsymptoticInput` — bundles `f`, `fy`, `L`, `hL`,
   `f_lip`, `y`, `secondDeriv`, `M₂`, `secondDeriv_bound`, `y₀`, `y_init`,
   `x₀`, `X`, `hxX : x₀ < X`, plus the analytical hypotheses `fy_bound`
   (pointwise bound `|fy x (y x)| ≤ L` along the flow) and `varRHS_cont`
   (joint continuity of the variational RHS as a function of `(x, ψ)`).
   The strict ordering `x₀ < X` matches Picard–Lindelöf's signature.
3. `noncomputable def variationalSolution` and the bundled headline
   `variationalSolution_isSolution` proved sorry-free via
   `PicardLindelof.exists_solution`. The thin time-dependent wrapper is
   `variationalRHSFn` plus the Lipschitz-of-linear-RHS lemma
   `variationalRHSFn_isLipschitzInSecondVar`, which factors the difference
   `(fy x (y x) * u + ½ secondDeriv x) − (fy x (y x) * v + ½ secondDeriv x)`
   to `fy x (y x) * (u − v)` and bounds via `|fy x (y x)| ≤ L`.
4. `noncomputable def eulerIterate` (locally, since `OpenMath/Basic.lean`
   only formalises the abstract Gronwall recurrence — there is no
   pre-existing Euler iterate function in the codebase). The headline
   `theorem euler_asymptotic_error` is sorry-first as planned.

## Result

SUCCESS. `lake env lean OpenMath/EulerAsymptoticError.lean` reports only
the expected `declaration uses 'sorry'` warning at the deferred
`euler_asymptotic_error` headline. All four §1 deliverables landed; Step 5
(close at least one sorry) closed the variational existence sorry (Step 3),
which is the recommended choice in the strategy.

## Dead ends

- Strategy text said "Replace `<EulerIterate>` with the existing Euler
  iterate name from `OpenMath/Basic.lean` (the same one already used by
  `OpenMath/EulerConvergence.lean`)". No such function exists in either
  file — `OpenMath/Basic.lean` only contains the abstract Gronwall
  recurrence (`a(i+1) ≤ (1 + h(i)·L)·a(i) + h(i)·C`), not the Euler
  iterate itself. Defined `eulerIterate` locally inside the new file, per
  the strategy's "do not modify `OpenMath/Basic.lean`" directive.
- Strategy text used `HasDerivAt`; `PicardLindelof.exists_solution` returns
  `HasDerivWithinAt ψ _ (Icc x₀ X) x`. Followed the strategy's "use
  whatever HasDerivAt / deriv API matches the existing style of
  `OpenMath/PicardLindelof.lean`" override and used `HasDerivWithinAt` in
  the headline.
- Initially defined `variationalRHS` and `variationalRHSFn` as `def`s; the
  compiler rejected them because they depend on `(1 / 2 : ℝ)` which uses
  `instDivInvMonoid` (noncomputable). Marked both `noncomputable`.
- Strategy's `EulerAsymptoticInput` description has `x₀ ≤ X`, but
  `PicardLindelof.exists_solution` requires strict `<`. Tightened the
  structure field to `hxX : x₀ < X` rather than carrying both — at
  `x₀ = X` there is no integration to do anyway. Recorded as a deviation
  from the literal strategy signature.

## Discovery

- The variational ODE is the textbook example of a *time-dependent*
  Lipschitz RHS where Lipschitzness in the state variable comes from
  `|∂_y f| ≤ L`, not from `f` being a contraction. The
  `variationalRHSFn_isLipschitzInSecondVar` lemma is one line of `ring` +
  `abs_mul` after factoring out `fy x (y x) * (u − v)`. This is a useful
  template for any future linear-in-state ODE we hit.
- `PicardLindelof.exists_solution` accepts the joint continuity hypothesis
  `Continuous (fun p : ℝ × E => f p.1 p.2)` and a *single* Lipschitz
  constant for `f` in the second variable on the whole strip — exactly
  what the variational RHS needs. No new wrapper was required.

## Suggested next approach

Two reasonable next targets, both predicated on cycle 746's scaffold being
in tracked code:

1. **Close `euler_asymptotic_error`.** The remaining headline reduces to
   a discrete-Gronwall + second-order-LTE expansion combiner. The bulk of
   the analysis is:
   - LTE expansion: `y(x_{n+1}) − y(x_n) − h·f(x_n, y(x_n)) = ½ h² y''(ξ_n)`
     for some `ξ_n ∈ (x_n, x_{n+1})` (Taylor remainder).
   - Variational LTE: `ψ(x_{n+1}) − ψ(x_n) − h·(fy(x_n, y(x_n))·ψ(x_n) +
     ½ y''(x_n)) = O(h²)`.
   - Gronwall combiner: `Mathlib.Analysis.ODE.Gronwall` plus the
     `theorem_212A` discrete recurrence already in `OpenMath/Basic.lean`.
   - Identification of the `O(h²)` constant in terms of `L`, `M₂`,
     `X − x₀` plus a uniform bound on `‖ψ‖`.
   The likely missing Mathlib lemma is the Taylor remainder for `y` along
   the flow once `secondDeriv = y''` is asserted. If that gap is real,
   file `.prover-state/issues/cycle_<NNN>_eulerAsymptotic_taylor_seam.md`.
2. **Add the `variationalSolution` uniqueness corollary** to `OpenMath/
   EulerAsymptoticError.lean` (one-liner from `PicardLindelof.unique`).
   This is a free-byproduct of Step 3 and useful when proving that the
   `Classical.choose`-extracted solution is well-defined up to the
   Picard–Lindelöf hypotheses.

§4 stretch goal (close the second §1 sorry in the same cycle) was not
attempted: Step 4 is the genuine multi-step proof, Step 3 was the cheap
close.
