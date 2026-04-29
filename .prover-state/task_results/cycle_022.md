# Cycle 022 Results

## Worked on

Per cycle 022 strategy §1: formalising the first sentence of
`def:381E` ("irreducible" Runge–Kutta method) and providing a
non-vacuous witness on `RKTableau.explicitEuler`. The second
sentence ("reduced method" construction) was deferred per the
strategy via an issue file.

Specifically:

* Added `OpenMath.Chapter3.Section312.RKTableau.IsIrreducible` —
  a `Prop`-valued definition equal to the literal conjunction
  `¬ M.IsZeroReducible ∧ ¬ M.IsPReducible`.
* Added the witness theorem
  `OpenMath.Chapter3.Section381.explicitEuler_isIrreducible :
   RKTableau.explicitEuler.IsIrreducible`.
* Wrote `.prover-state/issues/reduced_method_deferred.md`
  documenting the deferral of construction (2).
* Updated `extraction/formalization_data/lean_status.json` and
  `plan.md` (counter 22 → 23, `def:381E` flipped to `[x]`).

## Approach

The predicate is a one-line Boolean composite of existing cycle 020
(`IsZeroReducible`) and cycle 021 (`IsPReducible`) definitions, so
no new infrastructure was needed.

For the witness:

* `¬ IsZeroReducible`: destructure the existential to `inP1`, the
  non-emptiness witness `i : Fin 1` with `hi : inP1 i = false`, and
  the row-zero hypothesis `hbZero`. `fin_cases i` collapses
  `i` to `0`, giving `hi : inP1 0 = false`. Then
  `hbZero 0 hi : RKTableau.explicitEuler.b 0 = 0`. Definitionally
  `explicitEuler.b 0 = 1`, so `one_ne_zero` discharges the goal.

* `¬ IsPReducible`: destructure to `sBar : ℕ`, `hLt : sBar < 1`,
  `P : PPartition 1 sBar`. `Nat.lt_one_iff.mp hLt` substitutes
  `sBar = 0`, leaving `P : PPartition 1 0`. Apply `P.block 0` to
  obtain `Fin 0`, then `Fin.elim0`.

The strategy suggested `interval_cases sBar` for the substitution;
that tactic was not available (the `Mathlib.Tactic.IntervalCases`
import would need to be pulled in transitively, which is not the
case in this file). Substituted with `obtain rfl : sBar = 0 :=
Nat.lt_one_iff.mp hLt` instead — simpler and avoids extra imports.

No Aristotle submission this cycle (per strategy §1.5: proof is
~5 tactic lines, well below the batching threshold).

## Result

**SUCCESS** — `def:381E` formalised in full as `IsIrreducible`,
with non-vacuous witness on `RKTableau.explicitEuler`, no `sorry`,
no `axiom` declarations beyond the standard three.

### Pre-commit checklist output

```bash
# 1. Sorry scanner — must report 0
$ rg '\bsorry\b' OpenMath/
# (no matches — clean)

# 2. Tautology scanner — must report 0
$ rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/
# (no matches — clean)

# 3. Section381 builds standalone
$ lake env lean OpenMath/Chapter3/Section381.lean
# (clean exit, no diagnostics)

# 4. Full project builds
$ lake build
# ✔ [2822/2825] Built OpenMath.Chapter3.Section381 (2.7s)
# ✔ [2823/2825] Built OpenMath.Chapter3 (2.6s)
# ✔ [2824/2825] Built OpenMath (4.0s)
# Build completed successfully (2825 jobs).

# 5. Axiom check
$ # (#print axioms appended temporarily, output captured, lines removed before commit)
'OpenMath.Chapter3.Section312.RKTableau.IsIrreducible' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter3.Section381.explicitEuler_isIrreducible' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

## Faithfulness check

### `def IsIrreducible`

* **Entity ID and textbook statement** (quoted from
  `extraction/formalization_data/entities/def_381E.json`,
  first sentence):
  > A Runge–Kutta method is 'irreducible' if it is neither
  > 0-reducible nor P-reducible.

* **Lean statement captures**: same content. The Lean type is
  exactly the conjunction `¬ M.IsZeroReducible ∧ ¬ M.IsPReducible`,
  literally Butcher's "neither 0-reducible nor P-reducible".

* **Tautology check**: `IsIrreducible` is a fresh predicate; its
  body involves only `IsZeroReducible` and `IsPReducible` (cycle
  020 / 021 definitions, independently verified). No conclusion
  appears as hypothesis (closed term). **Pass.**

* **Identity check**: not relevant for a `def`.

* **Hypothesis-strength check**: no hypotheses, just `M : RKTableau s`
  as input. **Pass.**

* **Definition-smuggling check**: `IsIrreducible` is the *literal*
  Boolean composite of two existing predicates, not a stronger
  characterisation. **Pass.**

* **Absent-theorem check**: docstring mentions "see
  reduced_method_deferred.md" — that issue file exists and contains
  the deferred construction. **Pass.**

### `theorem explicitEuler_isIrreducible`

* **Statement**: `RKTableau.explicitEuler.IsIrreducible` — i.e. the
  1-stage explicit Euler tableau is irreducible. Used to demonstrate
  non-vacuity of `IsIrreducible` per CLAUDE.md "concrete witness"
  rule.

* **Tautology check**: conclusion is `IsIrreducible explicitEuler`;
  there are no hypotheses (closed term). The conclusion does **not**
  appear as a hypothesis. **Pass.**

* **Identity check**: proof is `refine ⟨?_, ?_⟩` followed by two
  genuine `rintro`-`obtain`-`exact` arguments, not `exact h` for
  some `h`. **Pass.**

* **Hypothesis-strength check**: no hypotheses. **Pass.**

* **Definition-smuggling check**: not applicable (theorem, not
  definition).

* **Absent-theorem check**: no comments promise unwritten content.
  **Pass.**

## Dead ends

* `interval_cases sBar` (suggested by strategy §1) failed with
  `unknown tactic` because `Mathlib.Tactic.IntervalCases` is not
  transitively imported by `Section381.lean`. Substituted with
  `obtain rfl : sBar = 0 := Nat.lt_one_iff.mp hLt`. Both achieve
  the same case-split but the `obtain rfl` form has fewer
  dependencies. Lesson: lookup `Nat.lt_one_iff` is cheap and
  preferable when the bound is already strict.

* No Aristotle submissions, no other dead ends.

## Discovery

* `rintro` destructures through nested `And` and `Exists` even when
  one of the layers is a `def` (here `IsZeroReducibleVia`). The
  pattern `⟨inP1, ⟨i, hi⟩, hbZero, _⟩` correctly destructures
  `∃ inP1, (∃ i, _) ∧ (∀ i, _ → _) ∧ (∀ i j, _ → _ → _)` in one
  call. Useful idiom for future negation-of-existential proofs.

* `RKTableau.explicitEuler.b 0` reduces to `(1 : ℝ)` by `rfl`
  (the structure literal's `b := fun _ => 1` field beta-reduces
  on application). This means `one_ne_zero` directly closes
  `(b 0 = 0) → False` without any unfold/simp step. Useful when
  proving negative facts about `explicitEuler` and similar
  structure-literal tableaux.

* `def:381F`'s textbook statement ("each of them reduces to the
  same reduced method") **does** require the construction (2)
  half of `def:381E`, not just `IsIrreducible`. The dependents
  audit is recorded in `reduced_method_deferred.md`. This makes
  resolving Q1/Q2 of that issue a hard prerequisite for `def:381F`.

## Suggested next approach

**Recommend `thm:381G` for cycle 023.**

Justification:

1. **Topological order**: `thm:381G` and `def:381F` are both
   immediate downstream of `def:381E`. Among them, `thm:381G`
   ("Irreducible Runge–Kutta Stage Distinguishability" — for any
   irreducible method, distinct stages produce distinct trajectories
   on some Lipschitz ODE; furthermore there exists a tree on which
   their elementary weights differ) depends *only* on
   `IsIrreducible` (the predicate-half of `def:381E` formalised
   this cycle) and on the existing `elementaryWeight` /
   `derivativeWeight` infrastructure from cycle 017.

2. **Avoids the `reducedMethod` blocker**: `def:381F` ("two methods
   are P-equivalent iff they reduce to the same reduced method")
   requires the construction-half of `def:381E`, which is deferred
   pending Q1/Q2 resolution. Tackling `thm:381G` first lets us
   make §380 progress while the `reducedMethod` design questions
   stay open.

3. **High strategic value**: `thm:381G` is the first §380 theorem
   *using* `IsIrreducible` and validates that the predicate is
   correctly stated. If the proof of `thm:381G` requires
   strengthening `IsIrreducible` (e.g. block-wise non-equivalence),
   we want to discover that *before* building `reducedMethod` on
   top of it.

A reasonable alternative would be `def:381F` with `reducedMethod`
worked out in the same cycle, but the strategy explicitly defers
that and the cycle 022 strategy (§3) lists `def:381F` as a stretch
goal *not* to attempt now. Stick with `thm:381G`.

(Concrete cycle 023 reading list:
`extraction/formalization_data/entities/thm_381G.json`,
`extraction/raw_text/ch03.txt` around §381 page 303–304 for the
proof sketch, and the `Lipschitz` / `LipschitzWith` namespace in
Mathlib for the trajectory-distinguishability witness.)
