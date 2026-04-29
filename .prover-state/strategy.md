# Cycle 026 Strategy

## State at planning time

- Branch tip: `ed02095 Formalize def:350A — A-stability, A(α)-stability, L-stability`.
- Codebase: zero `sorry`, scanner zero hits, axiom-clean. `lake build`
  succeeds (2829 jobs).
- Progress: 26 / 175 entities. No pending Aristotle results.
- Cycle 025 task results explicitly ranked candidates:
  1. `def:355A` — pure definition, depends only on the just-finished
     `def:350A`, "zero proof obligation beyond connectedness".
  2. `lem:351A` — depends on RK-stability-function infrastructure
     `(I − zA)⁻¹` that does NOT exist yet.
  3. `IsAStable R ↔ IsAlphaStable (π/2) R` bridge — blocked by
     Mathlib's totalisation `Real.tan (π/2) = 0` making the literal
     `α = π/2` sector degenerate.

## Why not the strict topo-order entry `lem:383C`

`plan.md`'s next `[ ]` row in topo order is `lem:383C` ("Existence of
Left and Right Inverses" in §383, the Runge–Kutta group section).
Inspection shows `lem:383A` ("The Runge–Kutta group") and
`lem:383B` ("Associativity of multiplicative forest mappings") are
both still `[ ]`. `lem:383C` proves a property of the group whose
construction does not yet exist, so attempting it would be a 3+ cycle
infrastructure cascade. **Skip for this cycle.** Continuing the §35x
cluster (where `def:350A` just landed) is the right move.

## Phantom alerts to ignore

If the prompt's "stuck on" / "Suspected vacuous proofs" framing names
`Section112.lean:74`, any §212 line, or any cycle ≤ 25 entry, ignore
it. Cycle-014 and cycle-015 consultant notes diagnosed all of these
as scanner / prompt-builder false positives propagated by
`attempts.md`. Verify with
`rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/` — zero
hits at `HEAD`. Do not re-touch any flagged file.

---

## Primary target: `def:355A` (down arrows)

**Why this and not something else.** Cycle 025's #1 recommendation.
Pure definition, dependency on `def:350A` only, builds out the §35x
order-arrow geometry that powers `thm:355B`–`G` (six theorems of
§35x). Closing it at zero proof cost is high-leverage.

### File location

Create `OpenMath/Chapter3/Section355.lean` and add an
`import OpenMath.Chapter3.Section355` line to `OpenMath/Chapter3.lean`.

### Read first (MANDATORY)

1. `extraction/formalization_data/entities/def_355A.json` — quote the
   `statement_latex` and `statement_text` verbatim in the file's
   docstring and in the cycle-026 task results.
2. Surrounding §355 paragraphs in `extraction/raw_text/ch03.txt` if
   the JSON does not include them (Butcher's "down arrow" notion is
   geometric: a direction at a stability-boundary point along which
   `R(z)` agrees with `exp(z)` to a stated order).
3. The recently-shipped `OpenMath/Chapter3/Section350.lean` for the
   `IsAStable` / `IsAlphaStable` / `stabilitySector` API you can
   build on.

If `def_355A.json` reveals dependencies on entities that are NOT yet
formalised (e.g. it transitively requires order-tree weights from
`thm:317A`), **stop and pivot** to the fallback target below — file a
short note in `.prover-state/issues/def_355A_missing_dependencies.md`
explaining what is missing.

### Encoding plan

Keep the stability function `R : ℂ → ℂ` an explicit parameter. Do NOT
attempt to bind to `RKTableau` this cycle (same reason as `def:350A`:
no `(I − zA)⁻¹` machinery yet).

The textbook informal idea (verify against the JSON before encoding):
a *down arrow of order p at z₀* is a unit vector `v` such that the
boundary `{ z | |R(z)| = 1 }` has a tangency to the curve
`{ z | R(z) = exp(z) }` of order `p` at `z₀`, with the arrow pointing
"into" the stability region `{ z | |R(z)| < 1 }`.

Likely Lean shape (subject to JSON wording):

```lean
namespace OpenMath.Chapter3.Section355

open Complex

/-- Butcher def:355A — down arrow of order p at z₀ along direction v. -/
def IsDownArrow (R : ℂ → ℂ) (z₀ : ℂ) (p : ℕ) (v : ℂ) : Prop := …
```

Or it may be stated as a *set* of arrows / a *predicate over a tuple*
— follow the JSON.

### Required deliverables

1. **The definition** as in `def_355A.json`.
2. **One concrete witness** (CLAUDE.md non-vacuity rule). Three
   candidates ordered by hope:
   - **`R(z) := Complex.exp z`** — the exact-flow stability
     function; agrees with `exp(z)` at every order at every point.
     If `def:355A` is `∃ z₀ v p, …`, this should witness it
     trivially.
   - **`R(z) := 0`** — boundary `{|R|=1}` is empty, so any
     `∀ z₀ ∈ boundary, …` clause is vacuously true.
   - **`R(z) := 1`** — boundary is all of ℂ; whatever the predicate
     reduces to may be checkable directly.
   Pick the witness whose proof obligation is shortest. If none of
   the three trivialises, write the witness with `sorry`, batch the
   sorry to Aristotle, and continue.
3. **Optional** one-line API lemma (e.g. unfolding `IsDownArrow` of a
   constant function). Skip if the definition is already trivial.
4. **Bookkeeping**: `OpenMath/Chapter3.lean` import line; flip
   `[ ]` → `[x]` for `def:355A` in `plan.md`; bump
   `Progress: 26/175` → `Progress: 27/175`; update the row in
   `extraction/formalization_data/lean_status.json` to `formalized`.

### Faithfulness check (run before committing)

For the new `def`:

- Quote Butcher's `statement_latex` / `statement_text` in the
  cycle-026 task results.
- Confirm the Lean predicate matches the textbook wording. Document
  any reformulation (e.g. `|x| ≤ −x` under `x ≤ 0`).
- **Real.tan trap.** If the definition mentions `tan(α)` for a
  specific angle, beware Mathlib's `Real.tan (π/2) = 0` totalisation.
  Same trap as `def:350A`'s `α = π/2` corner case. Bundle a
  non-degeneracy hypothesis into the predicate or document the
  divergence.
- **No smuggling.** If you introduce a `class` or `structure` with
  `Prop` fields, every field must be hypothesis-shaped.
- The witness lemma's `#print axioms` must be
  `[propext, Classical.choice, Quot.sound]` only.

### Mathlib hints

- `Mathlib.Analysis.Complex.Basic` for `Complex.norm`,
  `Complex.normSq`, `Complex.norm_div`.
- `Complex.sq_norm` (NOT `Complex.sq_abs` — renamed; cycle 025 hit
  this).
- `Complex.exp` for the exact-flow witness candidate.
- `Mathlib.Topology.Connected.Basic` for `connectedComponentIn` *if*
  the definition needs the principal order web (a connected component
  of a set in ℂ). If `def:355A` itself needs no connectedness, do not
  pull this in.
- `Filter.Tendsto`, `Filter.atBot`, `nhds 0` — already used in
  `Section350.lean`.
- `nlinarith` / `polyrith` — closed every algebraic obligation in
  cycle 025; try them first on any `‖·‖² ≥ c` style goal.

---

## Workflow (follow strictly)

1. **Read** `extraction/formalization_data/entities/def_355A.json` and
   the surrounding §355 paragraphs. Quote the textbook in the file
   docstring and your task-results file.
2. **If dependencies are missing** (transitive `[ ]` entities the
   definition syntactically requires), pivot to the fallback target.
3. **Sorry-first.** Write the file structure (imports, namespace,
   definition, witness with `sorry`). Verify with
   `lake env lean OpenMath/Chapter3/Section355.lean`.
4. **Try `lean_multi_attempt`** at the witness goal:
   `["simp", "decide", "aesop", "tauto", "trivial", "exact rfl", "intro _ _; trivial"]`.
5. **Only if step 4 fails on every snippet**, batch a single Aristotle
   submission for the witness. Sleep 30 min once. Single check. No
   polling.
6. **Pre-commit checks** (all four must pass):
   - `lake env lean OpenMath/Chapter3/Section355.lean` (clean exit).
   - `lake build` (full build clean).
   - Scanner: `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`
     returns zero hits.
   - `#print axioms` on every new declaration shows only
     `[propext, Classical.choice, Quot.sound]`.
7. **Update** `extraction/formalization_data/lean_status.json` row
   for `def:355A` to `formalized` with the file path.
8. **Update** `plan.md`: tick the `def:355A` box and bump
   `Progress: 26/175` to `Progress: 27/175`.
9. **Write** `.prover-state/task_results/cycle_026.md` per the
   CLAUDE.md template (Worked on / Approach / Result / Faithfulness
   check / Dead ends / Discovery / Suggested next approach).
10. **Commit** all modified files. Verify the commit landed via
    `git log -1 --format='%H %s'` and
    `git log -1 origin/Main/Experiments --format='%H %s'`.

---

## Explicit DO-NOT list

- **Do NOT** start `lem:383C`, `lem:383A`, or `lem:383B`. The §383
  group infrastructure is a multi-cycle investment; out of scope.
- **Do NOT** start `lem:351A`, `thm:351B`, `thm:353A`, or any §351–§353
  theorem. They require `(I − zA)⁻¹` for complex matrices that does
  not exist yet. If you have time after `def:355A`, file an issue
  scoping the `(I − zA)⁻¹` infrastructure rather than starting it.
- **Do NOT** define a "stability function of an RK tableau" this
  cycle. Same reason as the `(I − zA)⁻¹` ban.
- **Do NOT** attempt the deferred `IsAStable R ↔ IsAlphaStable (π/2) R`
  bridge. Blocked by `Real.tan (π/2) = 0`.
- **Do NOT** chase the `def:381E` reduced-method construction
  (deferred per `reduced_method_deferred.md`).
- **Do NOT** attempt §142 Jordan/Schur infrastructure (non-blocking
  per `jordan_canonical_form_missing.md`).
- **Do NOT** modify `OpenMath/Chapter1/Section112.lean`,
  `OpenMath/Chapter2/Section212.lean`, or any §213 file. The "stuck
  on" framing naming those files is a scanner phantom.
- **Do NOT** edit `scripts/autonomous_loop.py`. Scanner / prompt-
  builder fixes are loop-maintainer territory; bug already filed at
  `tautology_scanner_false_positives.md`.
- **Do NOT** rename any `h_<name>` hypothesis unless the scanner
  flags it against `HEAD`.
- **Do NOT** raise `maxHeartbeats` above 200000.
- **Do NOT** introduce `axiom` or `constant` for any gap.
- **Do NOT** try `Complex.sq_abs` (renamed to `Complex.sq_norm`).

---

## Aristotle policy

Probably not needed (target is a definition with a likely-trivial
witness). Submit ONLY if step 4 of the workflow exhausts the
`lean_multi_attempt` snippet list. If submitted: batch (one job, the
witness lemma), sleep 30 min once, single check, no polling.

---

## Fallback target (only if `def:355A` is dependency-blocked or finishes very fast)

`thm:302C` ("Rooted Tree Enumeration Formulas", §302). Purely
combinatorial, builds directly on `thm:301A`'s `α`/`β`/`γ`/`σ`
recursions in `OpenMath/Chapter3/Section301.lean`. Likely shape:
order-`n` count identities provable by induction on `RootedTree` plus
`simp`/`ring`/`Nat.factorial` arithmetic.

If pivoting to this fallback:

- File `OpenMath/Chapter3/Section302.lean`.
- Read `extraction/formalization_data/entities/thm_302C.json`.
- Sorry-first; one theorem per induction step; concrete witness on
  `singleton` and one branching tree.
- Same pre-commit / status / plan / task-results / commit workflow as
  above.

---

## Minimum acceptable cycle output

- One new entity formalised (`def:355A` or fallback `thm:302C`),
  axiom-clean, scanner-clean, `lake build` clean, with at least one
  concrete witness.
- `lean_status.json` and `plan.md` updated; `OpenMath/Chapter3.lean`
  imports the new module.
- `cycle_026.md` task result written.
- Commit pushed to `origin/Main/Experiments`.

If even this minimum is unachievable due to a discovered
infrastructure gap, write a structured issue file in
`.prover-state/issues/` describing the blocker (per CLAUDE.md "A
cycle with zero changes is unacceptable"), then commit and push the
issue file alone.
