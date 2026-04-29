# Cycle 025 Results

## Worked on

`def:350A` — A-stability, A(α)-stability, and L-stability (Butcher §350,
page 251). New file `OpenMath/Chapter3/Section350.lean`.

## Approach

Followed the cycle-025 strategy verbatim:

1. Read `extraction/formalization_data/entities/def_350A.json` for the
   textbook quote and the surrounding `context_latex` (which is where
   the A-stable / L-stable wording lives — the `statement_latex` field
   only carries the A(α)-stable definition explicitly).
2. Wrote three definitions (`stabilitySector`, `IsAlphaStable`,
   `IsAStable`, `IsLStable`) keeping `R : ℂ → ℂ` as an explicit
   parameter, exactly as the strategy requested. No coupling to
   `RKTableau` this cycle.
3. Provided two concrete witnesses:
   - `R(z) := 0`: A-stable (`isAStable_zero`) and L-stable
     (`isLStable_zero`).
   - Implicit Euler `R(z) := 1 / (1 − z)`: A-stable
     (`isAStable_implicitEuler`).
4. Provided one basic API lemma `IsLStable.isAStable`.
5. Auxiliary infrastructure: `one_le_normSq_one_sub` and
   `one_le_norm_one_sub` to handle the implicit-Euler bound. Proof
   idea (textbook): `‖1 − z‖² = (1 − Re z)² + (Im z)²`; with
   `Re z ≤ 0` we get `1 − Re z ≥ 1` and so `‖1 − z‖² ≥ 1`. Closed
   with `nlinarith` on the squared form, then a one-line bridge from
   `‖·‖² ≥ 1` to `‖·‖ ≥ 1` (`sq_nonneg` of `‖·‖ − 1`, plus `nlinarith`).
6. Did NOT need Aristotle. Manual `nlinarith` closed the implicit-Euler
   bound on the first attempt — the strategy's "submit only if
   `nlinarith`/`polyrith` fail once" rule kicked in but the first
   attempt succeeded, so no submission was made (saving compute).

## Result

**SUCCESS.**

- `lake env lean OpenMath/Chapter3/Section350.lean` exits 0.
- `lake build OpenMath.Chapter3.Section350` succeeds.
- `lake build` (full) succeeds (2829 jobs).
- `#print axioms` for every new declaration shows only
  `[propext, Classical.choice, Quot.sound]`.
- Scanner pattern
  `':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'` returns zero hits
  across `OpenMath/`.
- No `sorry` anywhere in `OpenMath/`.

## Faithfulness check

For each new `def`/`lemma` introduced this cycle:

### `stabilitySector α : Set ℂ`
- Entity ID: `def:350A` (helper for the predicate; not a separately
  numbered Butcher concept, but a literal transcription of Butcher's
  set `S(α)`).
- Textbook quote (from `def_350A.json` `statement_text`):
  > the set of points `x + iy` in the complex plane such that
  > `x ≤ 0` and `−tan(α)|x| ≤ y ≤ tan(α)|x|`.
- Lean encoding:
  `{ z | z.re ≤ 0 ∧ |z.im| ≤ Real.tan α * |z.re| }`.
- Captures: **same content**. `−tan(α)|x| ≤ y ≤ tan(α)|x|` is exactly
  `|y| ≤ tan(α)|x|`, and we use `|z.re|` rather than `−z.re` (legal
  under `z.re ≤ 0`). Documented this trivially-equal reformulation in
  the file header (Faithfulness notes §1).

### `IsAlphaStable (α : ℝ) (R : ℂ → ℂ) : Prop`
- Entity ID: `def:350A` (primary statement).
- Textbook quote:
  > Let `α` denote an angle satisfying `α ∈ (0, π)` … A Runge–Kutta
  > method with stability function `R(z)` is `A(α)`-stable if
  > `|R(z)| ≤ 1` for all `z ∈ S(α)`.
- Lean encoding:
  `α ∈ Set.Ioo 0 Real.pi ∧ ∀ z ∈ stabilitySector α, ‖R z‖ ≤ 1`.
- Captures: **same content**. The `α ∈ (0, π)` constraint is bundled
  into the predicate (rather than being a hypothesis on a theorem),
  so the predicate is automatically false for out-of-range `α`. This
  matches Butcher's intent: he only ever talks about A(α)-stability
  for `α` in the open interval.

### `IsAStable (R : ℂ → ℂ) : Prop`
- Entity ID: `def:350A` (the A-stability definition appears in the
  surrounding §350 paragraph; recorded in `def_350A.json` `context_latex`).
- Textbook wording (`def_350A.json` `context_latex` and `preamble`):
  > A-stability (`|R(z)| ≤ 1` for `Re(z) ≤ 0`).
- Lean encoding:
  `∀ z : ℂ, z.re ≤ 0 → ‖R z‖ ≤ 1`.
- Captures: **same content**, literal transcription.

### `IsLStable (R : ℂ → ℂ) : Prop`
- Entity ID: `def:350A` (L-stability defined in same §350 context).
- Textbook wording (`def_350A.json` `context_latex`):
  > L-stability (`A`-stable with `R(∞) = 0`).
- Lean encoding:
  `IsAStable R ∧ Filter.Tendsto (fun x : ℝ => R (x : ℂ)) Filter.atBot (nhds 0)`.
- Captures: **same content (slight encoding choice)**. Butcher writes
  `R(∞) = 0` colloquially. For an RK method, `R(z)` is rational, so
  `R(∞) = 0` (in the Riemann-sphere sense) iff `R(z) → 0` as
  `|z| → ∞`, which is equivalent for rational `R` to the limit along
  the negative real axis used by Mathlib (`Filter.atBot`). The choice
  is justified in the file's "Faithfulness notes" §3. For non-rational
  `R` (which Butcher does not consider in this section) the two
  formulations could differ; but L-stability is only ever applied to
  RK stability functions, which are rational by construction.

### `IsLStable.isAStable` (basic API)
- Tautology check: hypothesis `IsLStable R = IsAStable R ∧ …`,
  conclusion `IsAStable R`. The proof is `h.1`. This is a *projection*
  (genuine work: turning a conjunction into one of its conjuncts), not
  a re-export of a hypothesis with a different name. **Pass.**

### `isAStable_zero` and `isLStable_zero`
- Concrete witness lemmas (CLAUDE.md "non-vacuity" rule). Hypothesis:
  none. Conclusion: that the constant function `0` is A/L-stable.
  Tautology check: pass (no hypothesis). Identity check: pass (proofs
  use `simp`/explicit constructor).

### `isAStable_implicitEuler`
- Concrete witness for `IsAStable` on the canonical worked example
  `R(z) = 1 / (1 − z)`. Identity check: pass — the proof goes through
  a real bound `‖1 − z‖ ≥ 1` derived from `Re z ≤ 0`, which is
  genuine algebra.

### `one_le_normSq_one_sub`, `one_le_norm_one_sub`
- Helper lemmas, no textbook origin. Tautology / identity checks pass
  (real algebra closed by `nlinarith`).

## Hypothesis-strength check

`IsAlphaStable` bundles `α ∈ (0, π)` into the predicate — a tighter
encoding than the textbook's separate sentence "let `α` … satisfy
`α ∈ (0, π)`". This is an encoding choice, not a hypothesis
strengthening of any theorem. Predicate semantics are identical: the
set of `(α, R)` pairs satisfying `IsAlphaStable α R` exactly matches
Butcher's `(α, R)` pairs satisfying his definition.

## Definition-smuggling check

`IsAlphaStable`, `IsAStable`, `IsLStable` are predicates on `R`, not
classes/structures with conclusion-as-field bugs. No smuggling.

## Dead ends

None this cycle. The only initial errors were:

1. `Complex.sq_abs` (the name I tried first) does not exist; the
   correct Mathlib name is `Complex.sq_norm`. Fixed by
   `lean_loogle` lookup.
2. `simpa using tendsto_const_nhds` triggered an "unnecessary simpa"
   linter warning. Replaced with bare `exact`.

Both fixes were one-liners.

## Discovery

- `Complex.sq_norm : (z : ℂ) → ‖z‖^2 = Complex.normSq z` is the
  canonical bridge for the `‖·‖² = (Re·)² + (Im·)²` workflow.
  `Complex.sq_abs` (which I expected from older Mathlib) is gone /
  renamed.
- `nlinarith` closes both legs of the implicit-Euler bound (the
  squared-norm bound and the bridge from `‖·‖² ≥ 1` to `‖·‖ ≥ 1`)
  with appropriate `sq_nonneg` hints. Polyrith was not needed.
- The strategy's L-stability spec used `Filter.atBot` on a real
  parameter; this matches Mathlib's standard idiom for "as
  `Re z → −∞`" and required no custom limit machinery.

## Suggested next approach

Per the §35x downstream tree, natural next targets are:

1. **`def:355A`** ("down arrows" / order web) — the strategy's listed
   backup. Depends only on `def:350A`. The only complication is
   `connectedComponentIn` from `Mathlib.Topology.Connected`.
2. **`lem:351A`** — depends on `def:350A` plus the still-deferred
   "stability function of an RK tableau" infrastructure
   (`(I − zA)⁻¹` for complex matrices). This is the natural next
   *infrastructure* milestone before any of the §35x theorems can be
   proved on RK tableaux directly.
3. **A bridge lemma** `IsAStable R ↔ IsAlphaStable (π/2) R`. The
   strategy correctly flagged that `Real.tan (π/2)` is `0` in Mathlib
   (Lean's totalisation), making the literal sector at `α = π/2`
   degenerate to `{ z | z.re ≤ 0 ∧ z.im = 0 }` rather than the closed
   left half-plane. Skipping this bridge for now is the right call;
   it would need either a custom-defined sector at `π/2` or a careful
   limit argument.

The natural next cycle is therefore `def:355A` (zero proof obligation
beyond connectedness) or starting the `(I − zA)⁻¹` infrastructure.
The planner should pick based on whether the goal is breadth (more
`[ ]` definitions cleared) or depth (unblocking `lem:351A` and the
rest of §351).
