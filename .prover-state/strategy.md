# Cycle 266 strategy — Phase E.1 with corrected `bseriesExactTerm` definition

## TL;DR

Ship a **new** B-series term definition `bseriesExactTerm` (the
textbook *exact-solution* B-series coefficient `(h^r/(σ·γ)) • F`)
plus a partial-sum API, then bridge it to cycle 256's
`lem_311A_order_two`. Axiom-clean, single cycle, ~100 LOC.

**Do NOT** attempt the cycle 265 worker's "Option 1 Phase E.1" as
literally stated — it has a hidden definitional mismatch that makes
the bridge mathematically false. See §A below.

## A. Why cycle 265's Option 1 (as stated) is wrong

The cycle 265 worker recommended:

> Phase E.1: restate `lem_311A_order_two`'s conclusion as
> `yex(x₀+h) − bseriesAlphaPartialSum f y₀ h {vertex, cherry} =O h^3`.
> ~1 cycle, mostly bookkeeping.

This is provably wrong. Compute on scalar `ℝ → ℝ`:

* `bseriesAlphaTerm vertex` = `α(τ) • bseriesTerm τ` =
  `1 • (h¹/σ(τ)) • F(τ)(y₀)` = `h • f y₀`. ✓
* `bseriesAlphaTerm cherry` = `α(cherry) • bseriesTerm cherry` =
  `1 • (h²/σ(cherry)) • F(cherry)(y₀)` =
  `1 • (h²/1) • (deriv f y₀ * f y₀)` = `h² · (f'·f)`. **NOT**
  `(h²/2) · (f'·f)`.

So `bseriesAlphaPartialSum {vertex, cherry} = h·f + h² · (f'·f)`,
but `lem_311A_order_two`'s Taylor truncation is
`h·f + (h²/2) · (f'·f)`. The two **differ by a factor of 2 on the
cherry term** — the missing `1/r! = 1/2` factor. Any direct bridge
would compile to a false statement.

The root cause: `bseriesAlphaTerm := α • bseriesTerm` is the
Butcher-§310-(310i) RK-method form, NOT the exact-solution Taylor
form. The exact-solution B-series term is

  `(h^r(t)/(σ(t) · γ(t))) • F(t)(y₀)`

(per Butcher §312 — equivalently `α(t)/r(t)! • bseriesTerm`, with
the factorial denominator that's invisible at `r = 1` but bites at
`r ≥ 2`). Note `γ(cherry) = 2`, `γ(broom₃) = 6` — these factorials
come naturally from `density (mk children) = (order · ∏ density)`
(cycle 017's `γ`-recursion, Butcher (301a)).

## B. Primary target — Phase E.1 with `bseriesExactTerm`

### P1 — Definitions and basic API (in `OpenMath/Chapter3/Section301.lean`)

Place immediately after cycle 256's `bseriesAlphaPartialSum` block
(currently lines 716–820 of `Section301.lean`), inside the existing
`namespace RootedTree` / `namespace OpenMath.Chapter3.Section310`.

Add the following (polymorphic in `E : Type*` with
`[NormedAddCommGroup E]` `[NormedSpace ℝ E]`):

1. **`bseriesExactTerm`** — the exact-solution B-series per-tree
   summand:
   ```lean
   noncomputable def bseriesExactTerm
       {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
       (f : E → E) (y₀ : E) (h : ℝ) (t : RootedTree) : E :=
     (h ^ order t / ((symmetry t : ℝ) * (density t : ℝ))) •
       elementaryDiff f y₀ t
   ```
   Docstring must cite Butcher §312 (the exact-solution B-series
   convention), note the *factorial denominator* via `γ(t)` per
   Butcher (301a), and distinguish from cycle 256's
   `bseriesAlphaTerm` (Butcher-(310i) form *without* the `1/γ`
   factor; both forms are valid textbook objects but for different
   purposes — `bseriesAlphaTerm` for the RK-numerical B-series,
   `bseriesExactTerm` for the exact-solution Taylor B-series).

2. **`bseriesExactTerm_vertex`**: at `vertex`, σ·γ = 1·1 = 1, so
   the coefficient is `h¹` and the term is `h • f y₀`. Closure:
   ```lean
   theorem bseriesExactTerm_vertex
       {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
       (f : E → E) (y₀ : E) (h : ℝ) :
       bseriesExactTerm f y₀ h vertex = h • f y₀ := by
     unfold bseriesExactTerm vertex elementaryDiff
     simp [iteratedFDeriv_zero_apply,
           show order (mk []) = 1 from rfl,
           show symmetry (mk []) = 1 from rfl,
           show density (mk []) = 1 from rfl]
   ```

3. **`bseriesExactPartialSum`** + `_empty` (`@[simp]`), `_insert`,
   `_singleton`, `_union` — exact ports of cycle 256's
   `bseriesAlphaPartialSum_*` shape with `bseriesAlphaTerm` →
   `bseriesExactTerm`.

### P2 — Scalar closed-form witness at cherry (faithfulness test)

This is the load-bearing sanity check that the new definition
matches the textbook Taylor coefficient. Add (scalar
specialisation, since cycle 256's `lem_311A_order_two` is scalar):

```lean
theorem bseriesExactTerm_cherry_scalar
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesExactTerm f y₀ h cherry = h^2 / 2 * (deriv f y₀ * f y₀) := by
  ...
```

Recipe: unfold `bseriesExactTerm`, compute `order cherry = 2`,
`symmetry cherry = 1`, `density cherry = 2` (all `rfl`-reducible
from the cycle 017 cherry instance); the smul collapses to scalar
multiplication via `smul_eq_mul`; identify
`elementaryDiff f y₀ cherry` with `deriv f y₀ * f y₀` (needs an
`iteratedFDeriv ℝ 1` → `deriv` bridge, or unfold
`elementaryDiff (mk [vertex])` directly and use
`iteratedFDeriv ℝ 1 f y₀` = `fderiv ℝ f y₀` modulo the
`ContinuousMultilinearMap` coercion, which on scalar reduces to
multiplication by `deriv f y₀`). If the `iteratedFDeriv`-to-scalar
collapse needs more than ~10 LOC, ship it as a small private
helper `_cherry_elementaryDiff_eq` first.

**Risk note**: the `iteratedFDeriv ℝ 1` vs `fderiv ℝ` bridge is
exactly the kind of multilinear-map plumbing the cycle 265 worker
flagged as HIGH risk in the polymorphic order-2 lift. **Here it
fires at a single concrete tree (`cherry`)** rather than over
abstract `N`, which should be much easier. If it still stalls, use
Backup B (§E below) and ship `bseriesExactTerm` + `_vertex` +
partial-sum API without the cherry closed form.

### P3 — Bridge to `lem_311A_order_two` (in `OpenMath/Chapter3/Section311.lean`)

Place immediately after cycle 256's
`bseriesAlphaPartialSum_singleton_vertex_eq` (currently around
line 1353 of `Section311.lean`). Add:

```lean
/-- §310/§311 Phase E.1 (cycle 266) — restate cycle 256's
`lem_311A_order_two` using the cycle-266 exact-solution partial
sum `bseriesExactPartialSum f y₀ h {vertex, cherry}`. ... -/
theorem lem_311A_order_two_partialSum
    {f : ℝ → ℝ} (hf_C1 : ContDiff ℝ 1 f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C3 : ContDiff ℝ 3 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    (fun h : ℝ => yex (x₀ + h) -
        (y₀ + bseriesExactPartialSum f y₀ h
          ({vertex, cherry} : Finset RootedTree)))
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (2 + 1)) := by
  -- Expand bseriesExactPartialSum {vertex, cherry} via _insert + _singleton,
  -- then bseriesExactTerm_vertex + bseriesExactTerm_cherry_scalar.
  -- Algebraic rewrite reduces the residual to cycle 256's
  -- lem_311A_order_two's residual; apply lem_311A_order_two directly.
  ...
```

Recipe:
1. Rewrite `bseriesExactPartialSum f y₀ h {vertex, cherry}` to
   `bseriesExactTerm f y₀ h vertex + bseriesExactTerm f y₀ h cherry`
   via `_insert` (using `vertex ∉ {cherry}` from `vertex ≠ cherry`,
   `rfl`-disprovable) + `_singleton`.
2. Rewrite the two terms via `bseriesExactTerm_vertex` and the new
   scalar `bseriesExactTerm_cherry_scalar`. `smul_eq_mul` collapses
   `h • f y₀` to `h * f y₀`.
3. The residual matches cycle 256's `lem_311A_order_two` conclusion
   verbatim. Discharge by
   `exact lem_311A_order_two hf_C1 hyex_x₀ hyex_C3 hyex_ode` (or
   by `Asymptotics.IsBigO.congr_left` + `funext + ring` if the
   algebraic form differs only by associativity/commutativity).

### P4 — Non-vacuity witnesses

Three `example` statements at the end of Section301.lean's
`bseriesExact*` block (mirror cycle 256's pattern):

* `bseriesExactPartialSum {vertex} = h • f y₀`
* `bseriesExactPartialSum {vertex, cherry} = h • f y₀ + (h²/2) * (deriv f y₀ * f y₀)`
  [only if P2 ships; otherwise omit]
* `bseriesExactPartialSum (id : ℝ → ℝ) y₀ h {vertex} = h • y₀`

And one in Section311.lean exercising the new bridge on
`f := fun _ => 0`, `yex := fun _ => y₀` (trivial case, residual
identically zero, discharged by `Asymptotics.isBigO_zero` after
the partial-sum unfolding).

### P5 — Documentation hygiene

* Update `.prover-state/issues/lem_310B_plan.md`:
  - Append a "Cycle 266 update" subsection under §5 Phase E.1
    marking Phase E.1 closed with `bseriesExactTerm`
    infrastructure.
  - Add a brief note in §4.4 (multilinear lift) flagging
    `bseriesExactTerm_cherry_scalar` as a stepping stone toward
    polymorphic-N order-2 form (cycle 267+).

* Update `plan.md` `lem:310B` row annotation with cycle 266 Phase
  E.1 closure note.

* **Do NOT** update `lean_status.json` for `lem:310B` or
  `lem:311A` — Phase E.1 is one stepping stone of a multi-cycle
  roadmap; both entities stay `unformalized`.

## C. What NOT to do

These have been ruled out by cycle 265's task results, cycle 260's
scoping doc, and my pre-flight analysis (§A above).

1. **Do NOT** literally implement cycle 265's "Option 1" using
   `bseriesAlphaPartialSum` — the factorial mismatch makes any
   direct bridge a false statement. The correct path uses the
   **new** `bseriesExactTerm`.

2. **Do NOT** refactor or remove cycle 256's `bseriesAlphaTerm` /
   `bseriesAlphaPartialSum`. They are a valid textbook object
   (the Butcher-(310i) form *before* invoking `lem:310B`'s
   `1/r!`-rescaling). Let them coexist with the new
   `bseriesExactTerm`. The two forms differ in semantic role:
   `bseriesAlphaTerm` for the RK-method's B-series,
   `bseriesExactTerm` for the exact-solution Taylor B-series.
   `lem:310B`'s eventual formalisation will bridge them.

3. **Do NOT** attempt the polymorphic order-2 lift (Phase D.1
   continuation from cycle 265). The cycle 265 worker correctly
   flagged this as HIGH risk: it requires the full
   `HasFDerivAt.comp_hasDerivAt` chain rule plumbing with
   multilinear-map bookkeeping over arbitrary normed space `N`.
   Multi-cycle scope. Defer to cycle 267+ with explicit scoping.

4. **Do NOT** attempt the full `lem:310B` — that requires
   labelled trees (`def:300C`, Phase A.3 of `lem_310B_plan.md`)
   plus the multinomial Taylor theorem (`thm:306A`, Phase B).
   Both are multi-cycle. Per `lem_310B_plan.md` §F.

5. **Do NOT** introduce sorries. Cycle 200/201 (thm:381H scaffold)
   and cycle 149/150 (def:530B scaffold) precedent: sorry-first
   scaffolds without single-cycle closure paths get rolled back.
   If P2's `bseriesExactTerm_cherry_scalar` stalls on the
   `iteratedFDeriv ℝ 1` → `deriv` bridge, use Backup B (§E) and
   ship without the cherry closed form.

6. **Do NOT** raise `maxHeartbeats` above 200000.

7. **Do NOT** add `axiom`/`constant` declarations.

8. **Do NOT** edit `scripts/autonomous_loop.py`. Tautology-scanner
   false positives and prompt-builder phantom issues are
   loop-maintainer territory; see
   `.prover-state/issues/tautology_scanner_false_positives.md` and
   `.prover-state/issues/phantom_commit_verdict_pattern.md`.

9. **Do NOT** attempt to compile `OpenMath/Chapter4/Section441.lean`
   on GPFS. The cycle 182–239+ track has 43+ consecutive 5-min
   timeouts and the file is GPFS-blocked. Skip per
   `.prover-state/issues/cycle_182_gpfs_slowness.md`.

10. **Do NOT** redefine `bseriesAlphaTerm` to include a `1/r!`
    factor "to fix" the cycle 256 issue. The cycle 256 form
    matches Butcher's (310i) verbatim; it's just not the
    *Taylor-truncated* form. Don't break working infrastructure.

## D. Mathlib hooks (verify before consuming)

These should be available at HEAD; check each via
`lean_local_search` or `lean_hover_info` early in the cycle if any
proof shape feels unfamiliar:

| Goal | Likely lemma name |
|---|---|
| `Finset.sum_insert` for `{vertex, cherry}` | std |
| `Finset.sum_singleton` | std |
| `Finset.sum_union` (disjoint) | std |
| `iteratedFDeriv ℝ 0 f y₀ ![] = f y₀` | `iteratedFDeriv_zero_apply` (cycle 250 uses) |
| `iteratedFDeriv ℝ 1 f y₀ vec` → `fderiv ℝ f y₀ vec` | `iteratedFDeriv_one_apply` (verify via `lean_loogle "iteratedFDeriv 1 = fderiv"`) |
| `(fderiv ℝ f y₀ : ℝ →L[ℝ] ℝ) 1 = deriv f y₀` (scalar) | `fderiv_eq_smul_deriv` or via `ContinuousLinearMap.smulRight` |
| `Asymptotics.IsBigO.congr_left` / `IsBigO.congr_right` | std |
| `smul_eq_mul` (scalar smul) | std |
| `vertex ≠ cherry` (`mk [] ≠ mk [vertex]`) | by `decide` via cycle 017's `DecidableEq RootedTree` |

If the `iteratedFDeriv ℝ 1` → `deriv` bridge is awkward, an
alternative approach for P2: prove
`bseriesExactTerm_cherry_scalar` by direct unfolding of
`elementaryDiff` at `mk [vertex]` and explicit computation. Cite
the cycle 256 `lem_311A_order_two` proof's `iteratedDeriv_two_via_ode`
helper as a template — it does the same `iteratedFDeriv 1` →
`fderiv` → `deriv` collapse for scalar functions.

## E. Backup plan (Backup B — if P2 cherry closed form stalls)

If P2's `bseriesExactTerm_cherry_scalar` requires more than ~30
LOC of `iteratedFDeriv`-to-`deriv` plumbing, ship a smaller
deliverable that still meets the cycle's minimum bar:

**Backup B**:
1. P1 in full (`bseriesExactTerm`, `_vertex`, partial-sum API
   `_empty`/`_insert`/`_singleton`/`_union`). ~60 LOC.
2. P4 non-vacuity *only for vertex* (the cherry pair example
   requires P2). ~15 LOC.
3. Drop P3 (the bridge to `lem_311A_order_two`). File a follow-up
   note in `.prover-state/issues/lem_310B_plan.md` Phase E.1
   noting that the closed form for `bseriesExactTerm cherry` is
   single-cycle work pending the `iteratedFDeriv ℝ 1` → `deriv`
   plumbing.

Backup B still ships:
* The corrected definitional infrastructure (`bseriesExactTerm`)
* Non-vacuity at vertex (matching cycle 256's bridge to
  `bseriesOrderOne`)
* Compiles axiom-clean, sorry count 0

The next cycle then takes P2+P3 as a clean 1-cycle target with
the definition already in place.

**Abort threshold**: if even Backup B's `bseriesExactTerm` and
`_vertex` don't compile cleanly within the first 60 minutes,
abandon Phase E.1 entirely and pivot to fresh entity (`lem:342A`
per `lem_310B_plan.md` §8.2 — single-cycle Legendre-orthogonality
target). Do NOT leave sorries.

## F. Verification protocol

Standard verification (per CLAUDE.md and §F of recent cycles):

1. **Compile**: `lake env lean OpenMath/Chapter3/Section301.lean`
   and `lake env lean OpenMath/Chapter3/Section311.lean` must
   both exit 0.
2. **Sorry count**:
   `grep -c sorry OpenMath/Chapter3/Section{301,311}.lean` must
   each return 0.
3. **Tautology scanner clean**:
   `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'` on the two
   files returns no matches (or matches only on defensible
   `:= by` `h_<name>` closers — but ideally zero new hits).
4. **Axiom-clean**: `lean_verify` on each new public theorem
   (`bseriesExactTerm_vertex`, `bseriesExactTerm_cherry_scalar`
   if shipped, `bseriesExactPartialSum_empty/insert/singleton/union`,
   `lem_311A_order_two_partialSum` if shipped). Expected output:
   `[propext, Classical.choice, Quot.sound]` only.
5. **Aggregator**: `lake env lean OpenMath/Chapter3.lean` exits 0.
6. **Faithfulness check** (per CLAUDE.md pre-commit checklist):
   - Quote textbook (Butcher §312 for `bseriesExactTerm`,
     Butcher §311 for `lem_311A_order_two_partialSum`).
   - Tautology check: conclusion ≠ hypothesis literally.
   - Identity check: proof is not `exact h`.
   - Documentation: cite the cycle 256 / cycle 265 lineage and
     the definitional fix.

## G. Faithfulness — what to document in cycle 266 task results

Mandatory documentation per CLAUDE.md:

* **`bseriesExactTerm`** (new def): cite Butcher §312
  (exact-solution B-series). State that the coefficient
  `h^r/(σ·γ)` is the textbook convention (cf. Butcher (301a) and
  the Taylor expansion `y(x₀+h) = Σ (h^n/n!) y^(n)(x₀)` combined
  with `lem:311A`'s `y^(n)(x₀) = Σ_{r(t)=n} α(t) F(t)(y₀)`, which
  gives per-tree coefficient `h^r · α(t)/r! = h^r/(σ·γ)`).

* **Faithfulness divergence from cycle 256**: explicitly note
  that cycle 256's `bseriesAlphaTerm := α • bseriesTerm` is the
  Butcher-(310i)-form *RK-method* B-series term (no `1/r!`
  factor), while cycle 266's `bseriesExactTerm := bseriesTerm/γ`
  is the *exact-solution* Taylor B-series term (with `1/r!` =
  `1/γ` factor, since `γ(t) = r(t) · ∏ γ(tᵢ)` collects the
  factorial from the recursive multiplicities). Both forms are
  valid textbook objects and `lem:310B`'s eventual formalisation
  will bridge them.

* **`lem_311A_order_two_partialSum`** (new bridge theorem, if
  shipped): captures the same content as cycle 256's
  `lem_311A_order_two`, restated using
  `bseriesExactPartialSum {vertex, cherry}` instead of the
  closed-form scalar polynomial. This is *equivalent* to
  `lem_311A_order_two` modulo the definitional unfolding of
  `bseriesExactPartialSum`; no new mathematical content beyond
  the partial-sum re-packaging.

## H. Suggested next steps for cycle 267+

After Phase E.1 lands, the natural next moves are:

1. **`bseriesExactTerm_broom₃_scalar`** and
   `_mk_vertex_vertex_scalar` (the two order-3 trees) — extend
   Phase E.1 to order 3.
2. **`lem_311A_order_three_partialSum`** — bridge cycle 257's
   order-3 closed form to a `bseriesExactPartialSum` over the
   four trees of order ≤ 3. Single cycle.
3. **Polymorphic order-2 (Phase D.1 continuation)** — now with
   the `bseriesExactTerm` machinery in place, the polymorphic
   order-2 lift becomes a more natural target since the cherry
   contribution factors through `bseriesExactTerm cherry`
   (polymorphic in `E`).
4. **Phase E.2 / E.3** — partial-sum forms at order 4 and 5,
   consuming cycles 258 and 259 respectively. ~1 cycle each.

If the cycle 267 planner sees this strategy as still on track,
the remaining roadmap (`lem_310B_plan.md` §5) is a clear 8–14
cycle multi-phase effort. If §310 momentum is no longer
compounding well, pivot to `lem:342A` (Legendre orthogonality on
`[0,1]`) per `lem_310B_plan.md` §8.2 — single-cycle, independent
of `lem:310B`.

## I. Risks (pre-flagged)

* **R1** (medium, P2 only): `iteratedFDeriv ℝ 1` vs `fderiv` API
  drift in Mathlib. Mitigation: try `lean_loogle "iteratedFDeriv 1"`
  and `lean_local_search "iteratedFDeriv_one"` early; fall back
  to Backup B if more than 30 LOC of plumbing needed.

* **R2** (low, P3 only): `lem_311A_order_two`'s residual algebraic
  form may differ from the `bseriesExactPartialSum`-expansion
  form by an `add`/`smul` associativity issue. Mitigation: use
  `Asymptotics.IsBigO.congr_left` (or `congr_right`) with a
  pointwise rewrite via `funext + ring`.

* **R3** (low): `density (mk [])` and `symmetry (mk [])` should
  both unfold to `1` by `rfl`; if not (unlikely given cycle 017's
  definitions), use the named lemma `tau_values` (cycle 017,
  `Section301.lean` line 267–269).

* **R4** (verify before proceeding): the cycle 250 worker shipped
  `alphaWeight = order!/(σ·γ)` — confirm that `density` (= γ) is
  publicly accessible from `Section301.lean` without import
  issues. Mitigation: `Grep` for `def density` early.

* **R5** (low): polymorphic vs scalar `smul`. Mitigation: in P2,
  state `bseriesExactTerm_cherry_scalar` for `ℝ → ℝ` only
  (matching cycle 256's scalar `lem_311A_order_two`). The
  polymorphic cherry closed form is cycle 267+ scope.

* **R6** (low): `vertex ∉ {cherry}` decidability in P3 step 1.
  Mitigation: `simp [Finset.mem_singleton]` plus `decide` (vertex
  and cherry are constructor-distinct `RootedTree` values, so
  `decide` should fire via `DecidableEq RootedTree` from
  `Section301.lean` line 92).

## J. Aristotle batch (optional)

If P2's `bseriesExactTerm_cherry_scalar` stalls on the
`iteratedFDeriv ℝ 1` → `deriv` bridge, an Aristotle batch is
appropriate:

* **Job target**: `bseriesExactTerm_cherry_scalar` only (the
  scalar cherry closed form).
* **In-context**: cycle 017's `cherry` definition, cycle 250's
  `alphaWeight_cherry` example, cycle 256's `bseriesAlphaTerm_vertex`
  (template for the simp recipe), and the elementaryDiff
  Section310 block. Submit with the prompt "compute the closed
  form for `bseriesExactTerm f y₀ h cherry` on `ℝ → ℝ` using
  `iteratedFDeriv` and `deriv`".
* **Single poll** discipline: do NOT re-poll within the cycle.

Otherwise, skip Aristotle — the deliverable is structural enough
that manual proof should close in 1 cycle.

## K. Bottom line

Cycle 266 is a single-cycle deliverable that:

1. Fixes a definitional gap in cycle 256's `bseriesAlphaTerm`
   infrastructure by introducing the corrected `bseriesExactTerm`
   (the textbook *exact-solution* B-series term with `1/γ` factor).
2. Ships the Phase E.1 bridge between cycle 256's closed-form
   `lem_311A_order_two` and the tree-indexed partial-sum form,
   which the cycle 265 worker correctly identified as the
   highest-value next step — just with the right definitional
   foundation.
3. Compounds the §310/§311 investment without committing to the
   multi-cycle Phase A/B/C/D infrastructure deferred by
   `lem_310B_plan.md`.

Expected: ~100 LOC across two files, axiom-clean, sorry count 0,
single cycle. Backup B drops P3 if P2 stalls. Hard abort
threshold: if even Backup B doesn't compile in 60 minutes, pivot
to `lem:342A` per `lem_310B_plan.md` §8.2.
