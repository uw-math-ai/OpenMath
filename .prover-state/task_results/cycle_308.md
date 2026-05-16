# Cycle 308 Results

## Worked on

Phase 1 of 3 of the §342 ↔ §321 Gauss–Legendre `RKTableau` lift
(strategy: P1 mandatory, P2 recommended, P3 optional):

* **P1 (def + n=1 witness)**: `butcherShiftedLegendre_collocationA`
  (the canonical collocation A-matrix at the shifted Legendre zeros)
  + `butcherShiftedLegendre_collocationA_one_apply` (the unique
  entry at `n = 1` evaluates to `1/2`).
* **P2 (RKTableau struct + coincidence)**:
  `butcherGaussLegendreRK_one : RKTableau 1` (the assembled
  1-stage Gauss–Legendre tableau) and
  `butcherGaussLegendreRK_one_eq_gaussLegendre1Stage` (it equals
  §321's hand-defined implicit-midpoint tableau from cycle 306).
  Plus a non-vacuity `example : butcherGaussLegendreRK_one.SatisfiesB 2`
  lifting the cycle 307 algebraic B(2) bridge onto the `RKTableau`.
* **Supporting** (per strategy): promoted cycle 302's
  `butcherShiftedLegendre_zeros 1 ⟨0, _⟩ = 1/2` and cycle 303's
  `butcherShiftedLegendre_quadratureWeights 1 ⟨0, _⟩ = 1` from
  anonymous `example`s to named public theorems
  `butcherShiftedLegendre_zeros_one_apply` and
  `butcherShiftedLegendre_quadratureWeights_one_apply` so P2's
  coincidence proof can cite them.
* **P3 (general-n)**: NOT attempted this cycle — deferred per the
  strategy's scoping (Phase 2/3 of the multi-cycle lift).

## Approach

1. Read `OpenMath/Chapter3/Section342.lean` lines 6140–6806 (cycle
   302 `_zeros`, cycle 303 `_quadratureWeights`, cycle 307 bridge)
   and `OpenMath/Chapter3/Section321.lean` (RKTableau, predicates,
   `gaussLegendre1Stage` from cycle 306).
2. Added `import OpenMath.Chapter3.Section321` to Section342.lean
   so the coincidence theorem can reference §321's hand-defined
   `gaussLegendre1Stage` and the §312 `RKTableau` struct (cycle
   check: no import cycle, since Section321 imports Section312 →
   Section310 only; neither references §342).
3. Promoted the two anonymous `example`s at Section342.lean:6184
   (zeros) and Section342.lean:6284 (quadratureWeights) to named
   `theorem`s with the same proofs verbatim, prefixed with a note
   recording the cycle-308 promotion rationale.
4. Inserted the P1 definition `butcherShiftedLegendre_collocationA`
   immediately before the namespace `end`, copying the integrand
   from cycle 303's `_quadratureWeights` and changing the upper
   limit from `1` to `butcherShiftedLegendre_zeros n i`.
5. Closed the P1 `_one_apply` named theorem via the strategy's
   recipe: `unfold` the def, `rw` the zero to `1/2`, then `simp
   [Lagrange.basis_singleton, Polynomial.eval_one]`. The
   intervalIntegral simp lemma fires automatically once the
   Lagrange basis is recognised as the constant `1` polynomial —
   the residual goal `1/2 - 0 = 1/2` is discharged by `simp`'s
   `sub_zero` step (no manual `ring`/`norm_num` needed).
6. Built `butcherGaussLegendreRK_one` as a `RKTableau 1` literal
   with the three §342 canonical fields (A, b, c).
7. Closed the coincidence theorem via
   `RKTableau.mk.injEq.mpr ⟨?_, ?_, ?_⟩`, dispatching each
   per-field equality by `funext + fin_cases` and citing the
   matching `_one_apply` named theorem.
8. Closed the B(2) `example` by rewriting through the coincidence
   theorem and re-using §321's `gaussLegendre1Stage`-based
   `interval_cases k; simp` pattern verbatim.
9. Compile-checked via `lake env lean OpenMath/Chapter3/Section342.lean`
   — 35s on a warm cache; no errors, only pre-existing linter
   warnings.
10. Verified axiom profile via `mcp__lean-lsp__lean_verify` on all
    five new public symbols.
11. Updated `plan.md` to record cycle 308's Phase 1/3 deliverable
    on the existing `lem:342B` line.

## Result

SUCCESS — P1 and P2 both ship axiom-clean (modulo the pre-existing
upstream `sorryAx` leak from cycle 301's `_rootsInIoo_card_ge`,
documented below).

### Deliverables shipped (5 new public symbols + 1 example)

1. `butcherShiftedLegendre_zeros_one_apply : zeros 1 ⟨0, _⟩ = 1/2`
   (promoted from cycle 302 `example`, body unchanged).
2. `butcherShiftedLegendre_quadratureWeights_one_apply : ... = 1`
   (promoted from cycle 303 `example`, body unchanged).
3. `butcherShiftedLegendre_collocationA (n : ℕ) (i j : Fin n) : ℝ`
   — the collocation A-matrix definition.
4. `butcherShiftedLegendre_collocationA_one_apply :
   collocationA 1 ⟨0, _⟩ ⟨0, _⟩ = 1/2`.
5. `butcherGaussLegendreRK_one : RKTableau 1` — assembled tableau.
6. `butcherGaussLegendreRK_one_eq_gaussLegendre1Stage` — coincidence
   with §321's hand-defined witness.
7. `example : butcherGaussLegendreRK_one.SatisfiesB 2` — non-vacuity
   anchor for the lifted B(2) bridge.

### Axiom check

`mcp__lean-lsp__lean_verify` reports the following profile for all
five new public theorems and for the cycle 307 bridge as well:

```
[propext, sorryAx, Classical.choice, Quot.sound]
```

The `sorryAx` is **pre-existing**: it traces to
`butcherShiftedLegendre_rootsInIoo_card_ge` (cycle 301 Phase A.1).
Confirmed by querying axioms on intermediate lemmas:

* `butcherShiftedLegendre_rootsInIoo_are_roots` (cycle 294): clean
  `[propext, Classical.choice, Quot.sound]`.
* `butcherShiftedLegendre_rootsInIoo_card_le` (cycle 301): clean.
* `butcherShiftedLegendre_rootsInIoo_card_ge` (cycle 301): leaks
  `sorryAx`.
* All downstream lemmas (`_zeros_one_apply`, `_quadratureWeights`,
  `_quadrature_exact_lt_n`, `_quadrature_exact_lt_two_n`,
  `_quadratureWeights_satisfiesB`) inherit the leak.

No new `sorry` keyword was introduced this cycle (`grep "sorry" OpenMath/Chapter3/Section342.lean` returns no matches). Cycle
307's task results note the same leak; resolving it (closing the
upstream `_rootsInIoo_card_ge` cleanly) is a separate cleanup cycle.

### Compile timings

`lake env lean OpenMath/Chapter3/Section342.lean` (warm cache):
35.5s real, 184s user. Well within budget. No `maxHeartbeats` bumps.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `butcherShiftedLegendre_collocationA`

* Entity ID: no dedicated entity (collocation A-matrix is the
  Butcher §342 p. 237 collocation method *construction*; the
  textbook entity covering "Gauss-Legendre RK method has order 2s
  iff (i)+(ii)+(iii)" is `cor:342D`, where item (iii) demands
  `C(s)`-satisfying `aᵢⱼ` — the §342 canonical choice is the
  collocation formula `Aᵢⱼ = ∫₀^{cᵢ} Lⱼ`).
* Textbook statement (Butcher §342 p. 237, paraphrasing the
  collocation derivation):
  > The collocation polynomial `u(x)` interpolating
  > `(cⱼ, f(Yⱼ))` integrates to `Yᵢ − y₀` over `[0, cᵢ]`. Hence
  > `Yᵢ − y₀ = h Σⱼ Aᵢⱼ f(Yⱼ)` where `Aᵢⱼ := ∫₀^{cᵢ} Lⱼ(x) dx`.
* Lean statement captures: **same content** — the integrand is
  exactly `Lⱼ` (the Lagrange basis at the canonical zeros), the
  interval is `[0, cᵢ]`, and the result type is `ℝ`.
* **Definition smuggling check**: ✓ this is the *primary*
  mathematical meaning of the collocation A-matrix. The `B(s)`,
  `C(s)`, `D(s)`, `E(s,s)` order conditions on the resulting
  tableau will be theorems (cycle 307 bridge for B at n=1 in cycle
  308; cycle 309+ for the rest), not part of the definition.

### `butcherShiftedLegendre_collocationA_one_apply`

* Entity: anchor / non-vacuity for `_collocationA` at `n = 1`.
* Textbook content (§342 p. 237 implicit midpoint): `A₁₁ = 1/2`.
* Lean statement: same content (`= 1/2`).
* **Tautology check**: NO — the conclusion `1/2` does not appear
  as a hypothesis; the proof routes through
  `Lagrange.basis_singleton`, `Polynomial.eval_one`, and
  `butcherShiftedLegendre_zeros_one_apply` (three separate
  rewrites). Genuine work.
* **Identity check**: NO — not a single `exact h`.

### `butcherGaussLegendreRK_one`

* Entity ID: no dedicated entity (component of `cor:342D` recipe
  applied at `s = 1`). The 1-stage Gauss method is named in §342
  p. 240's `cor:342D` examples table and is the implicit midpoint
  method (textbook `c = 1/2`, `b = 1`, `A = 1/2`).
* Textbook statement (§321 introductory tableau + §342 p. 240):
  > The 1-stage Gauss–Legendre method is the implicit midpoint
  > method with `c = 1/2`, `b = 1`, `A = 1/2`.
* Lean statement captures: **same content** — A, b, c fields are
  `_collocationA 1`, `_quadratureWeights 1`, `_zeros 1`
  respectively, which by the three `_one_apply` lemmas evaluate
  to the textbook constants. The coincidence theorem proves this.

### `butcherGaussLegendreRK_one_eq_gaussLegendre1Stage`

* Entity: bridge theorem (no separate textbook entity).
* **Tautology check**: NO — neither side is literally the other.
  LHS unfolds through three non-trivial integrals; RHS is a
  hand-defined constant tableau. Closing the equality requires
  evaluating each of the three at `n = 1`, none of which is `rfl`.
* **Identity check**: NO — proof routes through `RKTableau.mk.injEq`
  + `funext + fin_cases` + three named `_one_apply` lemmas.
  Genuine work.

### `butcherShiftedLegendre_zeros_one_apply` (promoted from cycle 302 example)

* Statement and proof unchanged from cycle 302; only the keyword
  `example` → `theorem` was changed and a name was added.
* No faithfulness divergence from the prior cycle.

### `butcherShiftedLegendre_quadratureWeights_one_apply` (promoted from cycle 303 example)

* Statement and proof unchanged from cycle 303; only `example` →
  `theorem` + name.
* No faithfulness divergence from the prior cycle.

### Hypothesis strength check

None of the new theorems introduce extra hypotheses beyond what
the textbook statement implies. `butcherGaussLegendreRK_one_eq_gaussLegendre1Stage`
has no hypotheses; the `_one_apply` lemmas are pure equalities at
a fixed concrete index.

### Class/structure faithfulness

No new `class` or `structure` introduced this cycle (the new
`RKTableau 1` value is a *witness*, not a new structure type).

## Dead ends

None — the strategy's recipe closed cleanly on first compile. One
brief detour: the strategy's draft proof of
`_collocationA_one_apply` ended with `ring`, but with the chosen
`rw [butcherShiftedLegendre_zeros_one_apply]` happening *before*
the `simp`, the `simp` step alone discharges the residual
`(1/2 - 0) * 1 = 1/2` arithmetic — no trailing `ring`/`norm_num`
needed. The proof shipped with just `simp [Lagrange.basis_singleton,
Polynomial.eval_one]`. Confirmed compile-clean and axiom-aligned
with the cycle 307 baseline.

## Discovery

1. **`RKTableau.mk.injEq` exists and works for per-field
   reduction.** The strategy hedged ("`RKTableau.ext` if available;
   otherwise manual `cases`/`rfl`"). In fact `mk.injEq` is the
   auto-generated structure injectivity lemma — invoking it with
   `.mpr ⟨?_, ?_, ?_⟩` cleanly opens three per-field subgoals, no
   `ext` lemma needed.
2. **The pre-existing upstream `sorryAx` leak from cycle 301**
   propagates through *every* `butcherShiftedLegendre_zeros`-using
   theorem, including the cycle 307 bridge that was committed last
   cycle. The leak source is `_rootsInIoo_card_ge` (cycle 301);
   `_rootsInIoo_card_le` is clean. A targeted cleanup of that one
   lemma would axiomatically clean the entire §342 collocation /
   quadrature stack. Worth a dedicated audit cycle in the near
   future.
3. **`Lagrange.basis_singleton + Polynomial.eval_one` is the
   canonical `n = 1` collapse pattern**: this same pair fires
   inside cycle 303's `_quadratureWeights_one_apply` and now
   cycle 308's `_collocationA_one_apply`. Any future
   `_Foo_one_apply`-style lemma for a Lagrange-basis integrand
   should use this pattern.
4. **Section342 ↔ Section321 dependency direction**: adding
   `import OpenMath.Chapter3.Section321` to Section342.lean is
   safe (no cycle) and is the natural location for the
   §342-canonical `RKTableau` constructions, since they consume
   both the §342 polynomial infrastructure and the §312
   `RKTableau` struct.

## Suggested next approach

The natural cycle 309 deliverable, per the strategy's Phase 2/3
scoping, is the general-`n` lift:

```lean
noncomputable def butcherGaussLegendreRK (n : ℕ) :
    OpenMath.Chapter3.Section312.RKTableau n where
  A := butcherShiftedLegendre_collocationA n
  b := butcherShiftedLegendre_quadratureWeights n
  c := butcherShiftedLegendre_zeros n

theorem butcherGaussLegendreRK_satisfiesB (n : ℕ) (hn : 0 < n) :
    (butcherGaussLegendreRK n).SatisfiesB (2 * n) := by
  intro k h1 hk
  show (∑ j : Fin n, butcherShiftedLegendre_quadratureWeights n j *
            butcherShiftedLegendre_zeros n j ^ (k - 1)) = 1 / (k : ℝ)
  exact butcherShiftedLegendre_quadratureWeights_satisfiesB n hn k h1 hk
```

This is a ~10-LOC cycle (one def + one short theorem) that closes
the B(2n) half of the §342 ↔ §321 lift in full. The remaining
halves (C(n), D(n), E(n,n)) require an upper-limit-parametrised
version of cycle 304's `_quadrature_exact_lt_two_n` (integrating
over `[0, cᵢ]` instead of `[0, 1]`), which is itself a multi-cycle
infrastructure step — that's the natural cycle 310+ target.

Secondarily, a one-off cleanup cycle on
`butcherShiftedLegendre_rootsInIoo_card_ge` to close the upstream
`sorryAx` leak would clean the entire §342 collocation stack.
Worth scheduling once the immediate §342 ↔ §321 bridge work
stabilises.

A third option: tackle `cor:342D` directly. The textbook proof
chains B(2s) ⟹ E(s,s) ⟹ D(s) ⟹ (342l) ⟹ order 2s, so this is a
multi-cycle composite that needs C(n), D(n), E(n,n) infrastructure
in place first. Cycle 309–311 is the realistic horizon.
