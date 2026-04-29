# Cycle 030 Strategy

## Status snapshot

* Cycle 029 landed `def:356B` (DJ-reducibility) and the DJ-irreducibility
  component of `def:356A`, with full `lake build` clean and 0 sorries.
* AN-stability component of `def:356A` is **deferred** (issue:
  `AN_stability_deferred.md`) — it needs complex matrix resolvent
  infrastructure (`(I − A Z)⁻¹`, left-half-plane condition,
  `R(Z)` magnitude bound). Cost estimate from the issue file: a
  dedicated cycle (or two) just for the resolvent + `R(Z)` machinery
  before the predicate itself can be stated faithfully.
* Progress: 30 / 175 entities.
* No pending Aristotle results, no open sorries.

## Cycle 030 target: `def:381A` — *equivalent* Runge–Kutta methods

**Why this and not AN-stability or `def:323A`.**

* `def:381A` is the natural §380/§381 leaf. Cycles 020, 021, 022, 029
  have built up the §381 reducibility cluster
  (`def:381B/C/D/E`, `def:356A` DJ-component, `def:356B`). Continuing
  the §381 momentum lets us reach `def:381F` (P-equivalent),
  `thm:381G/H` (the equivalence-conditions theorem), and the entire
  §382–§388 Runge–Kutta-group cluster.
* `def:381A` has 7 downstream consumers (`lem:383A`, `lem:389A`,
  `thm:382A`, `thm:382B`, `thm:384A`, `thm:388B`, plus `def:370A`
  which only references it). All are blocked behind it.
* AN-stability for `def:356A` remains the right *eventual* next major
  infrastructure investment, but it is multi-cycle (resolvent +
  `R(Z)` + predicate + witness, per the issue file). Tackle it after
  the §381 leaves are cleared so that we land at most one
  infrastructure-only cycle at a time.
* `def:323A` (internal order `q`) is the named fallback if `def:381A`
  blows scope (see §"Fallback" below).

## Textbook statement (verbatim from `extraction/formalization_data/entities/def_381A.json`)

> Two Runge–Kutta methods are 'equivalent' if, for any initial value
> problem defined by an autonomous function `f` satisfying a Lipschitz
> condition, and an initial value `y0`, there exists `h0 > 0` such that
> the result computed by the first method is identical with the result
> computed by the second method, if `h ≤ h0`.

This is a **semantic** equivalence: same numerical one-step output for
every Lipschitz autonomous problem, for sufficiently small step. It is
strictly weaker than Φ-equivalence (`def:381B`, already formalised),
because it allows the methods to differ on non-Lipschitz or implicit
ill-defined cases.

## Concrete Lean plan

**Place the new content in `OpenMath/Chapter3/Section381.lean`** (the
existing §380/§381 file). Do NOT create a new file — `def:381A` is
section 381, the same section as the existing P/0/Φ-reducibility
definitions, and `def:381F` will land in the same file next cycle.

### Step 1 — `IsRKOneStep` predicate

A relational ("predicate-style") encoding lets us handle implicit
methods without committing to a fixed-point existence theorem:

```lean
/-- `M` produces output `y₁` after one step of size `h` from `y₀` on
the autonomous ODE `y' = f(y)`. Captures the implicit stage system
`Y_i = y₀ + h • Σⱼ aᵢⱼ • f(Y_j)` and the update
`y₁ = y₀ + h • Σᵢ bᵢ • f(Yᵢ)`. -/
def IsRKOneStep {s : ℕ} (M : RKTableau s) {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : N → N) (y₀ : N) (h : ℝ) (y₁ : N) : Prop :=
  ∃ Y : Fin s → N,
    (∀ i, Y i = y₀ + h • ∑ j, M.A i j • f (Y j)) ∧
    y₁ = y₀ + h • ∑ i, M.b i • f (Y i)
```

Note this is a `Prop`, not a function — it is *true* for any `(y₁, Y)`
that satisfies the stage equations, and may admit zero, one, or
multiple solutions depending on `M`, `f`, and `h`. This is honest:
implicit methods may have no solution at large `h`, the unique
small-`h` solution at moderate `h`, etc.

### Step 2 — `Equivalent` predicate

```lean
/-- Butcher def:381A — two Runge–Kutta methods are 'equivalent' if,
for every Lipschitz autonomous problem and every initial value, there
exists a step-size threshold `h₀` below which any output of the first
method coincides with any output of the second method. -/
def Equivalent {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') : Prop :=
  ∀ {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : N → N) (L : ℝ≥0) (_hL : LipschitzWith L f) (y₀ : N),
    ∃ h₀ > (0 : ℝ), ∀ h, 0 < h → h ≤ h₀ →
      ∀ y₁ y₁', M.IsRKOneStep f y₀ h y₁ → M'.IsRKOneStep f y₀ h y₁' →
        y₁ = y₁'
```

Faithfulness check: this is exactly Butcher's "result computed by the
first ... is identical with the result computed by the second". The
`∀ y₁ y₁'` quantifier handles the (rare, implicit-method) case where
the stage equations have multiple solutions — we require *all* outputs
of `M` to agree with *all* outputs of `M'`. The `LipschitzWith L f`
hypothesis matches Butcher's "Lipschitz condition" verbatim (Mathlib's
`LipschitzWith` is the standard global-Lipschitz predicate over ℝ≥0).

Type-class plumbing note: Mathlib's `LipschitzWith` is in
`Mathlib.Topology.MetricSpace.Lipschitz`; `NNReal` is `ℝ≥0`. Use the
fully qualified name on first reference.

### Step 3 — Reflexivity witness on `explicitEuler`

Target `Equivalent explicitEuler explicitEuler` specifically, where
the stage system has a *unique* trivial solution `Y 0 = y₀` (since
`A = 0`):

```lean
theorem equivalent_explicitEuler_self :
    Equivalent explicitEuler explicitEuler := by
  intros N _ _ f L _hL y₀
  refine ⟨1, one_pos, ?_⟩
  intros h _hh_pos _hh_le y₁ y₁' h₁ h₁'
  obtain ⟨Y, hY_stage, hy₁⟩ := h₁
  obtain ⟨Y', hY'_stage, hy₁'⟩ := h₁'
  -- For explicit Euler (s = 1, A = 0), the stage equation is
  --   Y 0 = y₀ + h • ∑ j, 0 • f (Y j) = y₀
  -- So Y 0 = y₀ uniquely, and y₁ = y₀ + h • (1 • f y₀) = y₀ + h • f y₀.
  have hY0 : Y 0 = y₀ := by
    have hs := hY_stage 0
    simp [explicitEuler] at hs
    exact hs
  have hY'0 : Y' 0 = y₀ := by
    have hs := hY'_stage 0
    simp [explicitEuler] at hs
    exact hs
  rw [hy₁, hy₁']
  simp [explicitEuler, hY0, hY'0]
```

The general `equivalent_self M : ∀ M, Equivalent M M` for arbitrary
`M` is **out of scope this cycle** — it requires picking `h₀` small
enough that the implicit map is a contraction (Banach fixed-point), so
that any two stage solutions coincide. That is genuine Mathlib work
(deferred — see Step 5). For cycle 030, deliver only the
`explicitEuler` witness.

### Step 4 — Mark `def:381A` as formalised

Update `extraction/formalization_data/lean_status.json`:

```json
"def:381A": {
  "status": "formalized",
  "lean_file": "OpenMath/Chapter3/Section381.lean",
  "lean_symbol": "OpenMath.Chapter3.Section381.RKTableau.Equivalent",
  "notes": "Predicate over arbitrary normed spaces; non-vacuity witness on explicitEuler. General reflexivity equivalent_self M deferred — needs implicit-stage uniqueness via Banach fixed-point at small h."
}
```

Update `plan.md`:

* `def:381A` row: `[ ]` → `[x]` and add file pointer.
* Bump the progress counter `30 / 175` → `31 / 175` in the header.

### Step 5 — Issue file for the deferred general `equivalent_self`

Write `.prover-state/issues/equivalent_self_general_deferred.md`:

* Explain that `equivalent_self M` for arbitrary `M` is mathematically
  trivial in the textbook (the same algorithm gives the same answer)
  but in our predicate-style encoding requires implicit-stage
  uniqueness, which needs Banach contraction at small `h`.
* Cross-reference the AN-stability deferred issue: both share a
  family of "implicit-method well-definedness" gaps that may best be
  addressed in a single dedicated cycle building the Banach
  contraction infrastructure.
* Document that `equivalent_explicitEuler_self` is a sufficient
  non-vacuity witness for the cycle's deliverable.

## Pre-commit faithfulness checklist (mandatory)

For `def:381A` → `Equivalent`:

* [ ] Quote Butcher's statement in the file docstring (already
  required by project rules).
* [ ] Confirm the `IsRKOneStep` predicate captures Butcher's stage
  equations exactly. The textbook writes
  `Y_i = y_0 + h Σⱼ a_{ij} f(Y_j)` and
  `y_1 = y_0 + h Σᵢ bᵢ f(Yᵢ)`; the Lean encoding must match.
* [ ] **Definition smuggling check**: `Equivalent` must NOT be
  defined as Φ-equivalence (`PhiEquivalent`, the algebraic condition
  `∀ t, M.elementaryWeight t = M'.elementaryWeight t`). The textbook
  introduces `def:381A` (semantic equivalence) and `def:381B`
  (Φ-equivalence) as **distinct** notions; `thm:381H` later proves
  them equivalent (modulo the reduced method). Defining one in terms
  of the other smuggles the theorem.
* [ ] **Tautology check**: the witness `equivalent_explicitEuler_self`
  must do real work (unfold `IsRKOneStep`, derive `Y 0 = y₀` from
  the stage equation, apply `simp [explicitEuler]` to close). It
  should NOT be `exact rfl` or a one-liner.
* [ ] **Hypothesis strength check**: `LipschitzWith L f` for `L : ℝ≥0`
  is the cleanest match for Butcher's "satisfying a Lipschitz
  condition". Do NOT strengthen to `Continuous f` or
  `ContDiff ℝ ⊤ f` — Butcher specifies Lipschitz alone.

## Aristotle batch suggestion (optional)

`equivalent_explicitEuler_self` is small enough (≤ 20 lines) that
manual proving will be faster than an Aristotle round-trip. Skip
Aristotle for this cycle unless `equivalent_explicitEuler_self` blocks
on a `simp` rewrite that resists `lean_multi_attempt` exploration.

## What NOT to try

* **Do NOT** define `Equivalent` as `PhiEquivalent` or as
  "P-equivalent". These are theorems (`thm:381H`), not definitions —
  smuggling them as defs is a faithfulness failure.
* **Do NOT** define a function `oneStep : RKTableau s → ... → N` that
  picks a single output. For implicit methods, multiple outputs may
  exist; using a function silently drops the ambiguity. Use the
  predicate `IsRKOneStep` instead.
* **Do NOT** restrict `Equivalent` to explicit methods only. The
  textbook quantifies over all RK methods; the predicate-style
  encoding handles implicit methods correctly.
* **Do NOT** claim a general `equivalent_self M` proof. Defer to an
  issue file (see Step 5). The §381 cluster's proper closure of this
  is `thm:381H`, not Step 3 reflexivity.
* **Do NOT** introduce `axiom` or `constant` for the implicit-stage
  uniqueness gap. CLAUDE.md is explicit; build the Banach contraction
  helper later in a dedicated cycle, or live with the
  `explicitEuler`-only witness.
* **Do NOT** raise `maxHeartbeats` above 200000.
* **Do NOT** start AN-stability infrastructure as a side task. It is
  3+ cycles of complex-resolvent work and the cycle 029 issue file
  is explicit that it deserves dedicated cycles. Park it for after
  `def:381F` lands.
* **Do NOT** edit `scripts/autonomous_loop.py` (worker rule, per
  cycle 015 strategy and `tautology_scanner_false_positives.md`).
* **Do NOT** rename or reorganise the existing `Section381.lean`
  reducibility cluster. Append `IsRKOneStep`, `Equivalent`, and
  `equivalent_explicitEuler_self` at the end of the file, before
  `end RKTableau` / `end OpenMath.Chapter3.Section381`.
* **Do NOT** repeat the cycles 005–014 phantom debugging patterns
  ("commits not reaching repo", "scanner false positive"). Both are
  resolved; ignore any stale `attempts.md` carry-overs.
* **Do NOT** commit a half-finished `Equivalent` definition. Either
  the predicate + witness lands fully or the work reverts cleanly
  (see Fallback).

## Fallback (only if `def:381A` blows scope)

If by mid-cycle the `IsRKOneStep` / `Equivalent` predicate or the
`explicitEuler` witness proves harder than expected (e.g.
`LipschitzWith` typeclass plumbing won't unify, or `Fin 1` summation
unfolding is unworkable), pivot to **`def:323A` (internal order `q`)**:

* `extraction/formalization_data/entities/def_323A.json` — pure scalar
  definition over the existing `RKTableau` and `internalWeight`
  infrastructure from `Section312.lean`. Likely a single-file
  definition + a witness on `explicitEuler`.
* Place in a new file `OpenMath/Chapter3/Section323.lean` (registered
  in `OpenMath/Chapter3.lean` imports).
* Treat the partial `def:381A` work as deferred: revert any partial
  edits to `Section381.lean` and ship `def:323A` cleanly. No
  half-finished definitions in the codebase.

Note the fallback target — do not freelance to a different leaf
without writing why in `task_results/cycle_030.md`.

## Build commands

```bash
# Compile the file in isolation (preferred — fast)
lake env lean OpenMath/Chapter3/Section381.lean

# Full build (slow; only after the file compiles)
lake build

# Axiom check on the new declarations (after build is clean)
echo '#print axioms OpenMath.Chapter3.Section381.RKTableau.Equivalent
#print axioms OpenMath.Chapter3.Section381.RKTableau.equivalent_explicitEuler_self' \
  | lake env lean --stdin OpenMath/Chapter3/Section381.lean
```

Expect `[propext, Classical.choice, Quot.sound]` only.

## Deliverables checklist

* [ ] `IsRKOneStep` predicate in `Section381.lean`
* [ ] `Equivalent` predicate in `Section381.lean`
* [ ] `equivalent_explicitEuler_self` non-vacuity witness, fully proved
* [ ] File docstring updated to quote Butcher's `def:381A` statement
* [ ] `lean_status.json` row for `def:381A` flipped to `formalized`
* [ ] `plan.md` row for `def:381A` flipped to `[x]` with file pointer;
      progress counter bumped 30 → 31
* [ ] `.prover-state/issues/equivalent_self_general_deferred.md`
      created
* [ ] `lake env lean OpenMath/Chapter3/Section381.lean` clean
* [ ] `lake build` clean
* [ ] `#print axioms` returns the standard trio for both new declarations
* [ ] No new sorries (`rg --pcre2 '(?<!--\s)sorry' OpenMath/` returns nothing)
* [ ] Tautology scanner clean (rename any `h_<word>` closer to
      `h<word>` if it triggers — see
      `.prover-state/issues/tautology_scanner_false_positives.md`)
* [ ] `task_results/cycle_030.md` written per CLAUDE.md template
* [ ] Commit + push
