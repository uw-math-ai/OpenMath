# Cycle 025 Strategy

## State summary

- Cycle 024 closed cleanly: `lem:322A` formalized in
  `OpenMath/Chapter3/Section322.lean`, `lake build` succeeds, axiom
  check clean (`propext, Classical.choice, Quot.sound`).
- 25 / 175 entities done (Chapter 3 progress: 9 entities).
- No pending Aristotle results.
- No `sorry` anywhere in `OpenMath/`.
- Open issues: all are documented carry-overs (Jordan/Schur,
  Picard–Lindelof bound, σ vs symmetry-group, deferred reduced-method
  construction, scanner false positives). **None of them block a new
  Chapter 3 cycle.**

## Phantom alerts to ignore

If the prompt's "stuck on" / "Suspected vacuous proofs" framing names
`Section112.lean:74` or any §212 line, **ignore it**. The cycle-014
and cycle-015 consultant notes diagnosed both as scanner / prompt-
builder false positives propagated by `attempts.md`. Current scanner
status verified clean (zero hits). Do not re-touch
`OpenMath/Chapter1/Section112.lean` or any Section212 file this cycle.

---

## Primary target: `def:350A` — A-stability, A(α)-stability, L-stability

**Why this and not something else.** Top of the Chapter 3 topo order
among `[ ]` rows, fully unblocked, pure definition (no proof
obligation), and foundational for the entire §35x stability cluster
(`thm:351B`, `lem:351A`, `thm:353A`, `def:355A`, `thm:355B`–`G`,
`def:356A`–`B`, `cor:356D`, `def:357A`–`B`, `thm:357C`–`D`,
`thm:358A`, `def:359C`). Closing this definition unblocks dozens of
downstream entities at zero proof cost.

**File location.** Create `OpenMath/Chapter3/Section350.lean`. Add an
import line in `OpenMath/Chapter3.lean`.

### Read first (MANDATORY)

1. `extraction/formalization_data/entities/def_350A.json` — note the
   textbook quote:
   > Let `α` denote an angle satisfying `α ∈ (0, π)` and let `S(α)`
   > denote the set of points `x + iy` in the complex plane such that
   > `x ≤ 0` and `-tan(α)|x| ≤ y ≤ tan(α)|x|`. A Runge–Kutta method
   > with stability function `R(z)` is `A(α)`-stable if `|R(z)| ≤ 1`
   > for all `z ∈ S(α)`.
   The textbook also defines (read further into the JSON):
   * **A-stable**: `|R(z)| ≤ 1` for all `z` with `Re z ≤ 0`.
   * **L-stable**: A-stable, and additionally `R(z) → 0` as
     `Re z → -∞` (Butcher §350 wording — verify against the JSON
     before encoding).
2. `extraction/raw_text/ch03.txt` for surrounding paragraphs of §350
   if the JSON is incomplete on L-stability — quote the actual
   wording in your faithfulness check.

### Encoding plan

Keep `R : ℂ → ℂ` an explicit parameter. **Do NOT** try to bind these
predicates to `RKTableau` via a "stability function" definition this
cycle — that requires `(I - zA)⁻¹` machinery we have not built. The
later "RK method M is A-stable iff `stabilityFunction M` is A-stable"
bridge is a separate, smaller cycle.

```lean
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace OpenMath.Chapter3.Section350

open Complex

/-- The closed sector `S(α) ⊂ ℂ` of Butcher §350: points `x + iy`
    with `x ≤ 0` and `|y| ≤ tan(α) · |x|`. -/
def stabilitySector (α : ℝ) : Set ℂ :=
  { z | z.re ≤ 0 ∧ |z.im| ≤ Real.tan α * |z.re| }

/-- Butcher def:350A — `A(α)`-stability of a stability function. -/
def IsAlphaStable (α : ℝ) (R : ℂ → ℂ) : Prop :=
  α ∈ Set.Ioo 0 Real.pi ∧ ∀ z ∈ stabilitySector α, ‖R z‖ ≤ 1

/-- Butcher def:350A — `A`-stability is the closed left half-plane case. -/
def IsAStable (R : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, z.re ≤ 0 → ‖R z‖ ≤ 1

/-- Butcher def:350A — L-stability strengthens A-stability with
    decay at -∞. (Verify Butcher's exact wording against the JSON
    before committing.) -/
def IsLStable (R : ℂ → ℂ) : Prop :=
  IsAStable R ∧ Filter.Tendsto (fun x : ℝ => R (x : ℂ))
    Filter.atBot (nhds 0)
```

(If Butcher uses `R(z) → 0` as `z → ∞` along the negative real axis,
the `Filter.atBot` form above is the standard Mathlib spelling.
Verify exact predicate against the textbook quote.)

### Required deliverables for this cycle

1. **Three definitions** as above (or with names of your choice that
   match Butcher's "A-stable", "A(α)-stable", "L-stable").
2. **Two non-vacuous witnesses** (CLAUDE.md "concrete witness" rule):
   * The constant function `R(z) := 0` is A-stable and L-stable
     (trivial: `‖0‖ = 0 ≤ 1`).
   * The function `R(z) := 1 / (1 - z)` (the implicit Euler stability
     function) is A-stable. Proof sketch:
     `‖1 - z‖² = (1 - Re z)² + (Im z)²`. Under `Re z ≤ 0` we have
     `1 - Re z ≥ 1`, so `‖1 - z‖² ≥ 1`, hence `‖1/(1-z)‖ ≤ 1`. Use
     `Complex.norm_div`, `Complex.norm_one`, and a manual
     `‖1 - z‖² ≥ 1` lemma. If the latter is annoying, try
     `nlinarith` or `polyrith` on the real-and-imaginary expansion.
3. **One basic API lemma**: `IsLStable R → IsAStable R` (immediate
   from the conjunction). Also document (by an `example` or short
   lemma) that `IsAStable R ↔ IsAlphaStable (π/2) R` modulo the
   sector-degeneracy at `α = π/2` (`tan(π/2)` is undefined / large,
   so this may need slight care — if it's awkward, just note in a
   comment that the equivalence holds in spirit and skip the
   formalization).
4. **Bookkeeping**: add `import OpenMath.Chapter3.Section350` to
   `OpenMath/Chapter3.lean`; flip `[ ]` → `[x]` for `def:350A` in
   `plan.md` and bump progress `25/175` → `26/175`; update the row
   in `extraction/formalization_data/lean_status.json`.

### Mathlib lemma names to expect

(Verify each via `lean_local_search` or `lean_loogle` before
committing.)

* `Complex.norm_div` — `‖a / b‖ = ‖a‖ / ‖b‖`.
* `Complex.normSq_eq_abs` / `Complex.sq_abs` — bridges to
  `(Re z)² + (Im z)²`.
* `Complex.normSq_sub` — `normSq (a - b) = …` (for `‖1 - z‖²`).
* `Real.tan` — note `Real.tan (π/2)` is `0` in Mathlib (Lean's
  total-function convention), which is the wrong value mathematically.
  This is the reason for the "α = π/2 corner case" caveat above.
* `Filter.Tendsto`, `Filter.atBot`, `nhds 0` — standard.
* `mul_self_nonneg`, `sq_nonneg` — for `‖1 - z‖² ≥ 1` proof.

### Faithfulness check items

For each of the three new `def`s:

* Quote Butcher's wording from the JSON in your task-results file.
* Confirm the Lean predicate matches the textbook quote literally.
  The slight reformulation
  `S(α) := { z | z.re ≤ 0 ∧ |z.im| ≤ tan(α) · |z.re| }`
  is exactly Butcher's `S(α)` rewritten with `|x|` in place of `-x`
  (legal since `x ≤ 0`); document this trivially-equal reformulation.
* If you encode `IsLStable` with a different limit form than the
  textbook (e.g. `Tendsto.atTop` along the real axis vs Butcher's
  prose), document why the encodings are equivalent.

---

## Aristotle plan

This cycle is mostly definition + light algebra. The only proof
obligation that benefits from Aristotle is the implicit-Euler witness
`‖1/(1-z)‖ ≤ 1` under `Re z ≤ 0`. **If your manual attempt with
`nlinarith` / `polyrith` fails after one attempt**, batch-submit
exactly that sub-lemma to Aristotle:

```lean
lemma implicit_euler_norm_le_one {z : ℂ} (hz : z.re ≤ 0) :
    ‖(1 : ℂ) / (1 - z)‖ ≤ 1
```

Submit, sleep 30 min per CLAUDE.md, then incorporate. Do not over-
submit; this cycle's payload is small.

---

## Things NOT to try

* **Do NOT** define a "stability function of an RK tableau" this
  cycle. That requires `(I - zA)⁻¹` for a complex matrix, which is
  bigger infrastructure than `def:350A` warrants. Defer to a
  later cycle that explicitly takes it as a target (likely between
  `def:350A` and `lem:351A`).
* **Do NOT** state `def:350A` as a property of `RKTableau s` directly.
  Keep `R : ℂ → ℂ` as a parameter.
* **Do NOT** modify `OpenMath/Chapter1/Section112.lean`,
  `OpenMath/Chapter2/Section212.lean`, or any §213 file. The
  "stuck on" verdict naming those files is a scanner phantom
  (cycle-014 and cycle-015 consultant notes confirmed).
* **Do NOT** edit `scripts/autonomous_loop.py`. Scanner bug fixes are
  the loop maintainer's job (already documented in
  `tautology_scanner_false_positives.md`).
* **Do NOT** attempt §142 Jordan/Schur infrastructure. Per
  `jordan_canonical_form_missing.md` and the cycle-009 / cycle-015
  consultant guidance, §142 is not on the critical path; Chapter 3
  takes priority.
* **Do NOT** chase the `def:381E` "reduced method" construction. It
  is deferred until `def:381F` is queued (per
  `reduced_method_deferred.md`).
* **Do NOT** raise `maxHeartbeats` above 200000. Decompose instead.
* **Do NOT** introduce `axiom` or `constant` for any gap.

---

## Backup target (only if `def:350A` finishes very fast)

If `def:350A` lands with substantial cycle time remaining and
Aristotle is not in flight, attempt **`def:355A`** ("down arrows")
in a new file `OpenMath/Chapter3/Section355.lean`. It depends only on
`def:350A` and an arbitrary rational function `R : ℂ → ℂ`; it defines
the "order web" as
`{ z | (R z * Complex.exp (-z)).im = 0 ∧ 0 < (R z * Complex.exp (-z)).re }`
and the "principal order web" as the connected component of `0`.

Caveat: "connected component" requires `Mathlib.Topology.Connected`
and `connectedComponentIn`, and may be more work than expected. If it
looks heavier than 30 minutes of work, write the textbook quote into
a new entry of `.prover-state/issues/` documenting the Mathlib-
connectedness scope and stop. Do not push half-finished `def:355A`
into the commit.

---

## Pre-commit checklist (per CLAUDE.md)

* `lake env lean OpenMath/Chapter3/Section350.lean` exits 0.
* `lake build OpenMath.Chapter3.Section350` succeeds.
* `#print axioms` for each new `def` and lemma shows only
  `[propext, Classical.choice, Quot.sound]`.
* Scanner clean: `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`
  returns zero hits.
* `plan.md` updated, `lean_status.json` updated,
  `OpenMath/Chapter3.lean` updated.
* `task_results/cycle_025.md` written with the faithfulness checklist
  populated.
* All new definitions have at least one concrete witness `example`.
