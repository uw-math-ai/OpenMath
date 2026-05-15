# Cycle 256 Results

## Worked on

Per the cycle 256 strategy:

- **P1 (mandatory)**: α-weighted B-series partial sum companion in
  `OpenMath/Chapter3/Section301.lean`. Four new declarations:
  `bseriesAlphaTerm`, `bseriesAlphaTerm_vertex`,
  `bseriesAlphaPartialSum`, `bseriesAlphaPartialSum_empty` (with
  `@[simp]`), `bseriesAlphaPartialSum_insert`, plus two non-vacuity
  examples (singleton and two-element).
- **P2 (stretch — SHIPPED)**: `lem_311A_order_two` plus the
  chain-rule sub-lemma `iteratedDeriv_two_via_ode` in
  `OpenMath/Chapter3/Section311.lean`.
- **P3 (bonus — SHIPPED)**: cross-section bridge
  `bseriesAlphaPartialSum_singleton_vertex_eq` in Section311.

## Approach

### P1 (Section301)

Direct port of cycle 255's `bseriesPartialSum_*` declarations:
- `bseriesAlphaTerm f y₀ h t := alphaWeight t • bseriesTerm f y₀ h t`
- `bseriesAlphaTerm_vertex`: unfold + `rw [alphaWeight_vertex, one_smul,
  bseriesTerm_vertex]` (the strategy's defensive `show ... from` bridge
  was not needed — `vertex = mk []` resolved by definitional equality).
- `bseriesAlphaPartialSum S := ∑ t ∈ S, bseriesAlphaTerm f y₀ h t`.
- `_empty`, `_insert`: `simp [bseriesAlphaPartialSum]` and `simp
  [bseriesAlphaPartialSum, Finset.sum_insert ht]`.
- Two examples mirror cycle 255's pattern.

### P2 (Section311)

The chain-rule sub-lemma `iteratedDeriv_two_via_ode` follows the
recipe from the strategy §B P2:
1. `iteratedDeriv_succ` + `iteratedDeriv_one` unrolls to `deriv (deriv yex) x₀`.
2. `funext` shows `deriv yex = fun x => f (yex x)` (pointwise via
   `(hyex_ode x).deriv`).
3. `deriv_comp x₀ hf_diff.differentiableAt hyex_diff.differentiableAt`
   provides the chain rule.
4. `rw [(hyex_ode x₀).deriv, hyex_x₀]` collapses to `deriv f y₀ * f y₀`.

`lem_311A_order_two` extends cycle 248's `lem_311A_order_one`:
1. `taylor_isLittleO (n := 3)` produces the 3rd-order Taylor residual.
2. Evaluation of the Taylor polynomial at `x₀ + h` is unfolded with
   `simp only [Finset.sum_range_succ, ..., Nat.factorial, ...]` then
   closed by `ring`.
3. `hderiv1_x0` (cycle 248 pattern) identifies `iteratedDeriv 1 yex x₀ = f y₀`.
4. `hderiv2_x0 := iteratedDeriv_two_via_ode ...` identifies the
   second derivative.
5. `hcomp_tendsto` + congruence translates the Taylor residual from
   `nhds x₀` to `nhds 0`.
6. Residual + `(h³/6) • iteratedDeriv 3 yex x₀` as a separate
   `O(h³)` piece via `Asymptotics.isBigO_const_mul_self`.
7. Sum via `hres.isBigO.add hcubic`; `h ^ (2 + 1) = h ^ 3` via
   `funext`/`ring`.

### P3 (Section311)

One-line bridge: `rw [bseriesAlphaPartialSum, Finset.sum_singleton,
bseriesAlphaTerm_vertex]`. Required adding `import
OpenMath.Chapter3.Section301` to Section311 (was previously only
importing Section310).

## Result

**SUCCESS — P1 + P2 + P3 all SHIPPED.**

- `lake env lean OpenMath/Chapter3/Section301.lean` → exit 0.
- `lake env lean OpenMath/Chapter3/Section311.lean` → exit 0.
- `lake env lean OpenMath/Chapter3.lean` → exit 0.
- `lake build OpenMath.Chapter3.Section301` → success (3.4s).
- `lake build OpenMath.Chapter3.Section311` → success (83s — full
  rebuild of downstream from new Section301 import).
- `grep -c sorry OpenMath/Chapter3/Section301.lean` → 0.
- `grep -c sorry OpenMath/Chapter3/Section311.lean` → 0.
- Tautology scanner regex `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$`
  on modified files → 0 hits.

### Axiom-cleanliness verification (all new public symbols)

```
OpenMath.Chapter3.Section310.RootedTree.bseriesAlphaTerm
  → [propext, Classical.choice, Quot.sound]
OpenMath.Chapter3.Section310.RootedTree.bseriesAlphaTerm_vertex
  → [propext, Classical.choice, Quot.sound]
OpenMath.Chapter3.Section310.RootedTree.bseriesAlphaPartialSum
  → [propext, Classical.choice, Quot.sound]
OpenMath.Chapter3.Section310.RootedTree.bseriesAlphaPartialSum_empty
  → [propext, Classical.choice, Quot.sound]
OpenMath.Chapter3.Section310.RootedTree.bseriesAlphaPartialSum_insert
  → [propext, Classical.choice, Quot.sound]
OpenMath.Chapter3.Section311.lem_311A_order_two
  → [propext, Classical.choice, Quot.sound]
OpenMath.Chapter3.Section311.bseriesAlphaPartialSum_singleton_vertex_eq
  → [propext, Classical.choice, Quot.sound]
```

All axiom-clean (subset of `[propext, Classical.choice, Quot.sound]`).

### LOC delta

- `OpenMath/Chapter3/Section301.lean`: +73 lines.
- `OpenMath/Chapter3/Section311.lean`: +141 lines (sub-lemma +
  full theorem + P3 bridge + extra import).
- Total: +214 lines.

## Faithfulness check

### `bseriesAlphaTerm` (new `def`)

- Entity ID: `lem:310B` and (implicitly) the (310i) reference equation.
  No standalone entity exists for the α-weighted summand alone (this
  is an internal piece of (310i)).
- Butcher (310i) (cited via `lem:310B`'s reference equation):
  > `Σ_{t ∈ T} α(t) · (h^r(t) / σ(t)) · F(t)(y₀)`
- Lean: `alphaWeight t • bseriesTerm f y₀ h t`
  = `alphaWeight t • ((h^order t / σ(t)) • elementaryDiff f y₀ t)`.
- Captures: **same content**.

### `bseriesAlphaTerm_vertex` (new `theorem`)

- Butcher Table 310(II) row r=1 + cycle 254's `bseriesTerm_vertex`:
  `α(τ) · (h¹/σ(τ)) · F(τ)(y₀) = 1 · h · 1 · f(y₀) = h • f(y₀)`.
- Lean: `bseriesAlphaTerm f y₀ h vertex = h • f y₀`.
- Captures: **same content**.

### `bseriesAlphaPartialSum` (new `def`)

- Butcher (310i):
  > `Σ_{t ∈ T} α(t) · (h^r(t) / σ(t)) · F(t)(y₀)`.
- Lean: `∑ t ∈ S, bseriesAlphaTerm f y₀ h t`.
- Captures: **same content for `S = T`** (truncated to a hand-supplied
  finset to avoid summing over the full infinite `T`; cycle 257+ can
  ship a `T = Fintype` instance or a residual-bound version that
  recovers Butcher's full series). Faithful as a partial-sum
  approximant — Butcher's textbook also operates on truncated sums in
  practice (Table 310(II) is order-bounded).

### `bseriesAlphaPartialSum_empty` / `_insert` (new theorems)

- Trivial finset algebra: `Σ over ∅ = 0`, `Σ over insert = head + rest`.
  No textbook claim; pure Lean engineering scaffolding.

### `iteratedDeriv_two_via_ode` (new private `theorem`)

- Not a textbook statement; standard Mathlib idiom: under ODE `y' =
  f∘y`, the chain rule gives `y''(x₀) = f'(y(x₀)) · f(y(x₀))`. Used
  internally by `lem_311A_order_two`.
- No `entity_id` (helper sub-lemma).

### `lem_311A_order_two` (new `theorem`)

- Entity ID: `lem:311A` (Butcher §311, p. 174 — Taylor expansion of
  the exact solution).
- Butcher `lem:311A` is the combinatorial labelling statement (sum
  over labelled trees `u ∈ T_S^*`). Like cycle 248's
  `lem_311A_order_one`, the cycle-256 deliverable is the
  **order-2 Taylor specialization** that `lem:311A` underwrites in
  the §311 narrative, NOT the full combinatorial lemma.
- Lean: `(fun h => yex(x₀+h) - (y₀ + h·f(y₀) + (h²/2)·f'(y₀)·f(y₀))) =O[nhds 0]
  (fun h => h^(2+1))`.
- Captures: **same content as the order-2 specialization Butcher
  uses to derive (311a) — the second derivative of `F(τ)(y(x))` for
  the singleton tree case**. Strictly weaker than the full
  `lem:311A` (which the file docstring explicitly defers). The
  `lean_status.json` row for `lem:311A` remains `unformalized`
  consistent with cycle 248's convention.
- Extra hypothesis vs. cycle 248: `hf_C1 : ContDiff ℝ 1 f` is new
  here (needed for `Differentiable ℝ f` to apply the chain rule).
  Cycle 248's order-1 case did not need this because the chain rule
  is not invoked. Documented in the docstring; no Butcher hypothesis
  is being silently strengthened.

### `bseriesAlphaPartialSum_singleton_vertex_eq` (new `theorem`)

- NOT a textbook lemma — convenience bridge between cycle 256's
  α-weighted partial sum and cycle 248's `bseriesOrderOne`'s
  `h • f y₀` term. Per the strategy §C.9, no `entity_id` label.

## Dead ends

None substantive. The strategy's defensive `show alphaWeight (mk []) = 1
from alphaWeight_vertex` in `bseriesAlphaTerm_vertex` turned out to be
unneeded — `vertex` and `mk []` unify by definitional equality, so a
plain `rw [show alphaWeight vertex = 1 from alphaWeight_vertex]`
(kept for documentation clarity) works directly.

The first compile of P3 (the cross-section bridge) failed because
Section311 only imported Section310, not Section301; adding `import
OpenMath.Chapter3.Section301` fixed it. The downstream rebuild took
83s (full Chapter3 re-elaboration); cheap one-time cost.

The Taylor polynomial unfolding at order 3 needed only the standard
simp arguments that cycle 248 used at order 2 (`Finset.sum_range_succ`,
`Finset.sum_range_zero`, `Nat.factorial`, etc.), plus a `Nat.cast_ofNat`
that proved to be an unused simp argument (removed; warning fixed).

## Discovery

- The chain-rule sub-lemma `iteratedDeriv_two_via_ode` is a clean
  4-step proof (unroll iteratedDeriv → identify deriv yex pointwise
  → chain rule → collapse via hyex_x₀). It serves as a template for
  cycle 257's `iteratedDeriv_three_via_ode` (if needed): unroll one
  more layer with `iteratedDeriv_succ`, identify `deriv (deriv yex)`
  pointwise via cycle 256's identification, then chain rule once
  more (this time requiring `ContDiff ℝ 2 f` rather than `ContDiff ℝ 1 f`).
- The 3rd-order Taylor polynomial unfolding via `simp only
  [Finset.sum_range_succ, ..., Nat.factorial]` closes by `ring`
  without needing `Nat.cast_ofNat` (Lean computes `3! = 6` via the
  `Nat.factorial` definitional reduction).
- `taylor_isLittleO (n := 3)` works identically to `(n := 2)` — no
  Mathlib API drift at higher Taylor orders.
- Cycle 255 had documented `bseriesPartialSum` as not requiring
  Section301-internal helpers (it can live entirely in Section310);
  the P3 bridge confirms that cross-section consumers of cycle 256
  α-weighted infrastructure pay only an import-edge cost.

## Suggested next approach

Cycle 257 has three viable paths in increasing scope:

1. **`lem_311A_order_three`** (~150-200 LOC, 1 cycle): extend the
   order-2 chain-rule cascade by one layer. Requires
   `iteratedDeriv_three_via_ode` (one more chain-rule step,
   ~60-80 LOC). Yields `O(h⁴)` residual. Useful if §311 narrative
   needs deeper Taylor truncation; not strictly needed for §311's
   `thm:311B` if order-2 suffices.

2. **Aristotle: pivot to a small `lem:310B` case for r=2 or r=3**
   (multi-cycle): combine cycle 254's `bseriesTerm_eq_theta_smul_bseriesTerm`,
   cycle 256's `bseriesAlphaPartialSum`, and a small labelled-tree
   enumeration. Could yield a partial `lem:310B` win for trees of
   bounded order. Worth scoping in cycle 257; likely needs
   `Fintype (TruncatedRootedTree N)` for small N first.

3. **Polymorphic order-2** (~80 LOC, 1 cycle): generalize
   `lem_311A_order_two` from `ℝ → ℝ` to general `N : Type*` with
   `[NormedAddCommGroup N] [NormedSpace ℝ N]`, replacing
   `deriv f y₀ * f y₀` with `fderiv ℝ f y₀ (f y₀)`. This is the
   form `thm:311B` actually needs. The order-1 case in cycle 248
   already commits to `ℝ → ℝ`, so cycle 257 should align both
   `lem_311A_order_one` and `_two` polymorphically as a coordinated
   pair.

**Recommendation**: path 3 (polymorphic order-2 + retrofit order-1)
gives the highest leverage on §311's downstream `thm:311B` /
`thm:311C` while preserving cycle 256's progress. Path 1 is a quick
win if §311 needs more Taylor depth before §312's E-operator
infrastructure. Path 2 is the §310/§311 cascade endgame — high
value but multi-cycle.
