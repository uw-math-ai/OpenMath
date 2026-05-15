# Cycle 254 Results

## Worked on
`lem:310B` Phase A.0 — the B-series term scaffold (per cycle 254 strategy).
Shipped P1+P2+P3+P4 from the strategy: `bseriesTerm` definition, the
trivial-tree (`t = τ`) case of `lem:310B`, the θ-rewriting pointwise
scaffold, and three non-vacuity witnesses across `vertex`, `cherry`,
`broom₃`. Stretch P5 (`bseriesTerm_smul_h` homogeneity) skipped.

## Approach

### Placement correction (strategy adaptation)

The cycle 254 strategy directed me to add `bseriesTerm` to
`OpenMath/Chapter3/Section310.lean`. This is **not possible** as
written: `bseriesTerm`'s denominator uses `RootedTree.symmetry`, which
is defined in `Section301.lean` — and `Section301.lean` `import`s
`Section310.lean` (i.e. Section301 is downstream of Section310 in the
build graph despite its lower Butcher section number, because cycle 017
placed `RootedTree`/`order`/`theta`/`elementaryDiff` in Section310 and
then extended with `symmetry`/`density` in Section301). Placing
`bseriesTerm` in Section310 would create a circular import.

Resolution: added the four new declarations at the end of
`Section301.lean`, inside the same `OpenMath.Chapter3.Section310.RootedTree`
namespace block, immediately before `end RootedTree`. Name resolution
is identical to what the strategy intended (`bseriesTerm` is exported
as `OpenMath.Chapter3.Section310.RootedTree.bseriesTerm`). Documented
the placement decision in the inline section comment so future cycles
don't relitigate it.

### Definition (P1)

```lean
noncomputable def bseriesTerm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) (t : RootedTree) : E :=
  (h ^ order t / (symmetry t : ℝ)) • elementaryDiff f y₀ t
```

Convention mirrors `alphaWeight` (Section301.lean:305). `symmetry_pos`
(cycle 017) gives `0 < σ(t)` so the cast denominator is non-zero.

### Trivial-tree case (P2)

```lean
theorem bseriesTerm_vertex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) :
    bseriesTerm f y₀ h vertex = h • f y₀ := by
  unfold bseriesTerm vertex elementaryDiff
  simp [iteratedFDeriv_zero_apply,
        show order (mk []) = 1 from rfl,
        show symmetry (mk []) = 1 from rfl]
```

Required one iteration: my first draft (`simp [iteratedFDeriv_zero_apply]`
alone) left the goal
`(h ^ (mk []).order / ↑(mk []).symmetry) • f y₀ = h • f y₀` because
`simp` did not propagate `.order` / `.symmetry` reductions on its own.
Added the two `rfl` reductions as simp lemmas; closes cleanly.

### θ-rewriting scaffold (P3)

```lean
theorem bseriesTerm_eq_theta_smul_bseriesTerm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) (t : RootedTree) :
    bseriesTerm f y₀ h t = theta t • bseriesTerm f y₀ h t := by
  rw [theta_eq_one t, one_smul]
```

Closed in two rewrites: `theta_eq_one` (cycle 249) collapses `θ(t)` to
`1`, then `one_smul` collapses the scalar action.

### Witnesses (P4)

Three `example` blocks: `vertex` via `bseriesTerm_vertex`; `cherry`
and `broom₃` via `bseriesTerm_eq_theta_smul_bseriesTerm`. All
specialised to `f : ℝ → ℝ` so the ambient `NormedAddCommGroup`/
`NormedSpace ℝ` instances are inferred from Mathlib.

## Result
SUCCESS — P1+P2+P3+P4 land axiom-clean, sorry-clean, in a single
compile pass after one iteration on P2's `simp` set.

### Verification

* `lake env lean OpenMath/Chapter3/Section301.lean` — clean exit, 1m29s
  (cold; cache freshly-populated by Chapter3.lean prior build).
* `lake env lean OpenMath/Chapter3/Section310.lean` — clean exit, 22s
  (regression check; unchanged file).
* `lake env lean OpenMath/Chapter3.lean` — clean exit, 1m04s.
* `grep -c sorry` on Section301/Section310: both `0`.
* Tautology scanner (`:= h_\w+\s*$` etc): no matches in Section301.
* `lean_verify` on the three new declarations
  (`bseriesTerm`, `bseriesTerm_vertex`,
  `bseriesTerm_eq_theta_smul_bseriesTerm`): all report
  `["propext", "Classical.choice", "Quot.sound"]` — Mathlib baseline,
  no `sorryAx`.

## Faithfulness check

### `RootedTree.bseriesTerm` (def)

Entity context: this is the summand of Butcher's series (310i),
`(h^r(t) / σ(t)) • F(t)(y₀)`. The page-176 (310i) reads:

> y(x₀ + h) − y₀ = Σ_{t ∈ T*} (h^{|t|} / σ(t)) · α(|t|) · F(|t|)(y₀)

(modulo Butcher's `α(|t|)` notation and the labelled-tree quotient).
The `bseriesTerm f y₀ h t` Lean expression is the **`α`-stripped
summand**: `(h^r(t) / σ(t)) • F(t)(y₀)`. The factor `α(t)` is NOT
included — `alphaWeight` is a separate definition in Section301
(cycle 250) and downstream consumers will multiply when needed.

Lean statement captures: SAME content as the (310i) `α`-stripped
summand. The σ-faithfulness divergence (Section301's stipulative
recursive `symmetry` vs Butcher §300's automorphism-group definition,
issue `symmetry_group_equivalence.md`) is inherited; no new divergence
is introduced by `bseriesTerm`.

### `RootedTree.bseriesTerm_vertex` (theorem)

Entity `lem:310B` (`extraction/formalization_data/entities/lem_310B.json`)
states the Elementary Differential Weight Formula:

> ∂_{x₀}^k y_n(x₀, h) / k! evaluated at h = 0 = Σ_{|t| ∈ T_k^* / R}
>   F(|t|)(y₀) · α(|t|) (Butcher (310j), p. 176)

The `t = τ` case is the order-1 contribution: at the single-vertex
tree `τ`, `F(τ)(y₀) = f(y₀)`, `σ(τ) = 1`, `r(τ) = 1`, so the summand
collapses to `h • f(y₀)`. Butcher's proof of Lemma 310B (p. 176)
explicitly calls this case "obvious" — the order-1 Taylor expansion
of `y(x₀+h)` around `y₀` reduces to `y₀ + h·f(y₀) + O(h²)`.

Lean statement captures: SAME content as the `t = τ` half of
Butcher's `lem:310B` proof obligation. The full `lem:310B`
re-summation identity is **not** claimed by this theorem (cycle 254
ships only the trivial-tree special case).

### `RootedTree.bseriesTerm_eq_theta_smul_bseriesTerm` (theorem)

This is the **pointwise** algebraic identity Butcher's `lem:310B`
proof goes through after applying `thm:306A` (Taylor's theorem):
each B-series summand is invariant under multiplication by `θ(t)`
(the exact-solution operator weight). In our formalisation,
`theta_eq_one` (cycle 249) gives `θ ≡ 1`, so this scaffold is the
trivial identity `bseriesTerm = 1 • bseriesTerm = θ(t) • bseriesTerm`.

**Critical faithfulness disclaimer (in the docstring)**: this is
**NOT** the full statement of `lem:310B`. The full lemma asserts a
re-summation identity between a labeled-tree-orbit sum (LHS, requires
labeled-tree machinery not yet built) and the θ-weighted unlabeled
sum (RHS). The pointwise scaffold is one of several prerequisites;
full closure of `lem:310B` requires:

  (a) `thm:306A` (Taylor's theorem — multinomial expansion, multi-cycle);
  (b) labeled rooted tree quotient infrastructure (`def:300C`,
      currently absent);
  (c) the orbit-counting combinatorial bridge per Butcher's proof.

Lean statement captures: WEAKER than `lem:310B` (intentionally —
single-cycle scope). Documented explicitly. **`lean_status.json`
row for `lem:310B` stays `unformalized`**; the `plan.md` row for
`lem:310B` stays `[ ]`.

## Dead ends

### Attempted: place in Section310.lean (per strategy)

The strategy directed Section310 placement; this is infeasible because
`bseriesTerm` consumes `symmetry`, defined downstream in Section301
(which imports Section310). A circular import would result. Detected
during pre-flight by reading both files' `import` declarations and
namespace structures. Resolution: place in Section301.lean inside the
same namespace block (functionally equivalent).

### Attempted: `simp [iteratedFDeriv_zero_apply]` alone (P2 first draft)

Left an unsolved goal
`(h ^ (mk []).order / ↑(mk []).symmetry) • f y₀ = h • f y₀`.
`simp` did not propagate the `(mk []).order = 1` and
`(mk []).symmetry = 1` rfl-reductions on its own. Fix: add both as
explicit simp lemmas via `show ... from rfl`.

## Discovery

### Section301 ⊃ Section310 dependency inversion

Butcher's textbook numbering puts §301 before §310, but cycle 017's
file layout placed `RootedTree`, `order`, `elementaryDiff`,
`theta` in `Section310.lean`. Section301.lean then `import`s
Section310 and extends with `symmetry`, `density`, `alphaWeight`.
This inversion is structurally fine but causes the obvious placement
heuristic ("Section §310 content goes in Section310.lean") to fail
for any §310 content that depends on `symmetry`/`density`. The
cycle 254 strategy hit this; future cycles working on §310 content
(B-series partial sums, truncated trees, etc.) should default to
**Section301.lean** as the target file unless the new content is
purely a function of order/theta/elementaryDiff (which all live in
Section310).

### `iteratedFDeriv_zero_apply` is the right collapse lemma

Confirmed via `lean_loogle "iteratedFDeriv _ 0"`: the lemma
`iteratedFDeriv_zero_apply : (iteratedFDeriv 𝕜 0 f x) m = f x` for
any `m : Fin 0 → E` exists in
`Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries`. Already
transitively imported by Section310's `Mathlib.Analysis.Calculus.ContDiff.Basic`.
The `_eq_comp` variant (`continuousMultilinearCurryFin0`) is also
available but heavier; the `_apply` form is the right tool when
applying to an explicit empty-tuple argument.

### `vertex.order` and `vertex.symmetry` reduce by `rfl` but `simp` won't push them

A direct `show vertex = mk [] from rfl` followed by `show (mk []).order = 1 from rfl`
works, but `simp` alone does not derive the chain. Providing both
identities as simp lemmas in the call site is the cleanest path.

## Suggested next approach (cycle 255)

Per the strategy's §F outlook (highest-leverage first):

1. **TruncatedRootedTree scaffold (P1 for cycle 255)**: define
   `TruncatedRootedTree N := { t : RootedTree // order t ≤ N }` plus
   minimal API (val coercion, monotone embedding to higher `N`).
   Defer the `Fintype` instance (multi-cycle — the
   subtype-of-nested-inductive `Fintype` instance is the actual
   hard problem). Without `Fintype`, sums over `TruncatedRootedTree N`
   must be hand-enumerated via explicit `Finset` literals — but that
   is sufficient for small-`N` partial B-series proofs.

2. **B-series partial sum (P2 for cycle 255)**: define
   `bseriesPartialSum f y₀ h (S : Finset RootedTree) : E :=
     ∑ t ∈ S, bseriesTerm f y₀ h t`. Then ship the four-tree partial
   sum for `r ≤ 3` (vertex, cherry, broom₃, mk [cherry]) and prove
   it expands to the order-3 Taylor polynomial in `h`. This gives
   the cycle 248 P1 order-2 result `lem_311A_order_two` for free
   (or a close analogue), and is the foundation for the small-r
   `lem:310B` cases.

3. **Aristotle batch for the iteratedFDeriv ℝ 1 ↔ fderiv bridge**
   (cycle 248 P2(a) blocker). Single-poll after 30 min. This unlocks
   the order-2 step of `lem:311A` once `bseriesPartialSum` is in
   place.

Cycle 254 ships ~80 LOC; cycle 255 P1+P2 would add another ~60-80 LOC.
The `Fintype`-blocked path stays deferred for at least 3-5 cycles
beyond.

## Strategy adherence audit

* P1 (REQUIRED) — `bseriesTerm` definition: SHIPPED (in Section301,
  not Section310, see "Placement correction" above).
* P2 (REQUIRED) — `bseriesTerm_vertex`: SHIPPED.
* P3 (REQUIRED) — `bseriesTerm_eq_theta_smul_bseriesTerm`: SHIPPED.
* P4 (REQUIRED) — three witnesses (vertex/cherry/broom₃): SHIPPED.
* P5 (STRETCH) — `bseriesTerm_smul_h`: SKIPPED (P1-P4 took longer
  than ~75% of the cycle due to the GPFS-cold initial compile of
  Section301.lean; deferred to cycle 255 if useful).
* All §B prohibitions honoured: no full `lem:310B`, no sorry-first
  scaffold, no r=6 witnesses, no `TruncatedRootedTree`, no
  Section441 attempt, no `lem_311A_order_two`, no `thm:306A`,
  no `def:381F`/`thm:381H`, no maxHeartbeats raise, no `axiom`,
  no `scripts/autonomous_loop.py` edit, no Aristotle polling.
