# Cycle 248 Results

## Worked on
P1 — Section311.lean foundational layer (§311 / Taylor expansion of the
exact solution). New file `OpenMath/Chapter3/Section311.lean` introducing
the order-1 specialisation of the §311 Taylor-expansion machinery.

Specifically shipped:
* `F_tau_eval` — base case of `def:310A`: `F(τ)(y₀) = f(y₀)`.
* `bseriesOrderOne` — first-order B-series truncation `y₀ + h • f(y₀)`,
  polymorphic in any real normed space.
* `lem_311A_order_one` — order-1 Taylor expansion: under
  `yex x₀ = y₀`, `ContDiff ℝ 2 yex`, and `∀ x, HasDerivAt yex (f (yex x)) x`,
  the residual `yex(x₀ + h) - bseriesOrderOne f y₀ h` is `O(h^(1+1))`
  near `0`.
* Non-vacuity `example` witnessing the hypothesis set with
  `f := fun _ => 0` and `yex := fun _ => y₀`.

## Approach
Direct port of cycle 154's `explicitEulerGLM_hasOrderOne_trivialStarting`
(`OpenMath/Chapter5/Section530.lean` line ~1284) to the simpler
B-series-1 setting. The cycle-154 template decomposes its residual
into `T1 + T2`, where `T1` is the Taylor remainder of the exact solution
and `T2` is a Lipschitz-bounded `f`-correction. In the B-series-1 case
there is no `f`-correction term, so `T2` disappears entirely and the
Lipschitz hypothesis on `f` is dropped from the signature.

The proof follows the same 7-step structure as cycle 154's T1 piece:
1. Rewrite the difference using `bseriesOrderOne`'s definition (and
   `smul_eq_mul` on ℝ).
2. Invoke `taylor_isLittleO (n := 2)` with `convex_univ` to obtain the
   second-order Taylor remainder.
3. Evaluate `taylorWithinEval yex 2 Set.univ x₀ (x₀ + h)` explicitly.
4. Identify `iteratedDeriv 1 yex x₀ = f y₀` via `(hyex_ode x₀).deriv`
   and `hyex_x₀`.
5. Translate the Taylor remainder to a `nhds 0` statement via
   `htaylor.comp_tendsto htend`.
6. Show that the quadratic coefficient term
   `h ^ 2 / 2 * iteratedDeriv 2 yex x₀` is `O(h²)` via
   `Asymptotics.isBigO_const_mul_self`.
7. Combine via `IsLittleO.isBigO.add`, collapse `h ^ (1 + 1)` to
   `h ^ 2`.

The non-vacuity witness specialises to the trivial ODE `y' = 0`,
which has `f y = 0` and constant solution `yex := y₀`. All three
hypotheses are discharged by `rfl`, `contDiff_const`, and
`hasDerivAt_const`.

## Result
SUCCESS.

* `OpenMath/Chapter3/Section311.lean` — 162 LOC, 0 sorries, builds
  axiom-clean (`[propext, Classical.choice, Quot.sound]`) in 2.9 s.
* `OpenMath/Chapter3.lean` — aggregator updated; rebuilds in 21 s
  with no regressions across §3.
* Tautology scanner regex `:= h_\w+\s*$|exact h_\w+\s*$` returns 0
  hits in the new file.
* No `axiom`/`constant` declarations introduced.
* `maxHeartbeats` not raised.

## Faithfulness check

### `F_tau_eval`
* Entity ID: `def:310A` (base case).
* Textbook statement (`entities/def_310A.json`, recursive base):
  > F(τ)(y) = f(y)
* Lean statement captures: same content. The single-vertex tree
  `τ = •` is `RootedTree.vertex = RootedTree.mk []`. The recursive
  definition `elementaryDiff f y₀ (mk [])` unfolds to
  `iteratedFDeriv ℝ 0 f y₀ (Fin.elim0)` which is `f y₀` by
  `iteratedFDeriv_zero_apply`. No definition smuggling: the
  conclusion `f y₀` is what the textbook's recursive base case
  states, and it is proved (not stipulated).

### `bseriesOrderOne`
* Entity ID: no textbook entity (helper definition for the order-1
  B-series truncation).
* Textbook content (Butcher §312, equation 312a, and §311 framing):
  the exact-solution B-series truncated at order 1 is
  `y₀ + (h^|τ| / σ(τ)) · α(τ) · F(τ)(y₀) = y₀ + h · 1 · 1 · f(y₀)`.
* Lean definition: `y₀ + h • f y₀`. Polymorphic in the codomain
  `N` (any real normed space); for `N := ℝ` the smul reduces to
  multiplication.
* Definition smuggling check: this is a stand-alone definition of
  the B-series-1 truncation, not a smuggled rebrand of any §311
  theorem conclusion. It is consumed by `lem_311A_order_one` as a
  *target* for comparison, not as a hypothesis.

### `lem_311A_order_one`
* Entity ID: `lem:311A` (partial — order-1 specialisation only).
* Textbook statement (`entities/lem_311A.json`):
  > Let $S = S_0 \cup \{s\}$ be an ordered set, where every member
  > of $S_0$ is less than $s$. Let $t$ be a member of $T_{S_0}^*$.
  > Then $\frac{d}{dx} F(|t|)(y(x))$ is the sum of $F(|u|)(y(x))$
  > over all $u \in T_S^*$ such that the subtree formed by removing
  > $s$ from the set of vertices is $t$.
* Lean statement captures: **different** — `lem_311A_order_one` is
  NOT the textbook `lem:311A`. The textbook `lem:311A` is a
  combinatorial labelling lemma over `T_S^*` (labelled-tree
  quotients), which requires `def:300C` infrastructure not yet
  formalised.

  What `lem_311A_order_one` captures instead is the **order-1 Taylor
  expansion content of section 311** (i.e., the order-1 case of
  what `thm:311B` proves for general `n`). This is the practical
  consequence of repeatedly applying `lem:311A` that the textbook
  uses to derive Taylor coefficients of the exact solution.
* Justification for divergence: the strategy explicitly notes (see
  `.prover-state/strategy.md` §"Cycle 248 target") that the full
  `lem:311A` is multi-cycle scope and that this cycle ships a
  single-cycle p=1 special case under a non-vacuous name. The
  divergence is documented in:
  - the file docstring (`OpenMath/Chapter3/Section311.lean`
    "Scope of this cycle"),
  - the `lem_311A_order_one` docstring ("p = 1 special case of
    lem:311A / thm:311B"),
  - `lean_status.json` (`lem:311A` remains `unformalized`).
* Tautology check: the conclusion
  `(fun h => yex(x₀+h) - bseriesOrderOne f y₀ h) =O (fun h => h^(1+1))`
  is NOT verbatim any of the hypotheses. The proof is non-trivial
  (Taylor remainder + arithmetic rewriting + asymptotic combination).
* Identity check: the proof is a 7-step `have`-chain (~50 lines),
  not `exact h_`. Real mathematical work is done.
* Hypothesis strength check: all three hypotheses (`yex x₀ = y₀`,
  `ContDiff ℝ 2 yex`, `∀ x, HasDerivAt yex (f (yex x)) x`) are
  weaker than the textbook's standing assumption that `y` is "a
  solution to `y'(x) = f(y(x))`" and "differentiable arbitrarily
  often" (Butcher §311 p. 174). `ContDiff ℝ 2` is a strict
  weakening of "arbitrarily often"; the rest is verbatim the
  textbook ODE relation. No extra hypotheses beyond what the
  textbook requires.

## Dead ends
* Initial non-vacuity witness attempt used `f := id` and
  `yex x := y₀ + x - x₀`, which does NOT satisfy the ODE
  `yex'(x) = f(yex(x))` (since `yex'(x) = 1` but
  `f(yex(x)) = y₀ + x - x₀` is non-constant). Replaced with the
  trivial witness `f := 0, yex := const y₀`.

## Discovery
* The §311 textbook `lem:311A` is **not** the Taylor-expansion fact
  it is commonly cited for; rather, it is a combinatorial labelling
  intermediate used to derive `thm:311B`. The Taylor-expansion
  content of §311 is `thm:311B` (`y^(#S)(y₀) = Σ_{t ∈ T_S} F(|t|)(y₀)`)
  and `thm:311C` (the unlabelled-tree version with `α(t)`
  multiplicities). The full `lem:311A` requires a labelled-tree
  quotient infrastructure (`def:300C`) that is multi-cycle scope.
* The cycle 154 / cycle 158 explicit-Euler order-1 proof template
  in `OpenMath/Chapter5/Section530.lean` is highly reusable for
  any "order-1 truncated approximation has `O(h²)` error" claim.
  The B-series-1 case is strictly simpler than the explicit-Euler
  case because no `f`-correction (T2) term appears, so the
  Lipschitz hypothesis on `f` can be dropped.
* `iteratedFDeriv_zero_apply` is `rfl`-level definitional reduction
  for the base case of `def:310A`: `elementaryDiff f y₀ (mk [])`
  unfolds directly to `f y₀` (modulo a definitional reduction of
  the `Fin 0 → E` argument).
* For ℝ-valued `f`, `bseriesOrderOne f y₀ h = y₀ + h • f y₀`
  reduces via `smul_eq_mul` to `y₀ + h * f y₀`, recovering the
  scalar form expected by the cycle 154 template.

## Suggested next approach
P2(a) from the strategy — `lem_311A_order_two` at p = 2. The
second-order B-series is
`y₀ + h • f y₀ + (h²/2) • F([τ,τ]) y₀`
where `F([τ,τ]) y₀ = f'(y₀) · f y₀` is the first directional
derivative of `f` evaluated at the trivial-multiset slot
`(f y₀, f y₀)`.

The proof template would extend `lem_311A_order_one` by:
1. Computing `elementaryDiff f y₀ (RootedTree.mk [RootedTree.vertex])`
   explicitly using `iteratedFDeriv` at `n = 1` (i.e., the first
   directional derivative `fderiv ℝ f y₀ (f y₀)`).
2. Using `taylor_isLittleO (n := 3)` for the third-order Taylor
   expansion of `yex`.
3. Identifying `iteratedDeriv 2 yex x₀ = fderiv ℝ f y₀ (f y₀)`
   via the chain rule applied to `yex' = f ∘ yex` (a non-trivial
   `HasDerivAt`-of-composition step).

Estimated scope: 1 cycle if `fderiv`-of-composition machinery
ports cleanly; 2 cycles if step 3 requires extracting a helper
lemma about second derivatives of ODE solutions.

P2(b) — `theta_eq_one` (Butcher §310 lem:310B) — remains a viable
single-cycle deliverable as well: prove
`thetaWeight : RootedTree → ℝ` with recursive definition
`theta τ = 1`, `theta (mk children) = (children.map theta).prod`,
and the closure lemma `theta_eq_one : ∀ t, theta t = 1` by
induction. This is purely combinatorial (no Taylor/asymptotics
machinery) and could be a clean "warm-up" deliverable to ship
ahead of P2(a).
