# Cycle 132 Results

## Worked on
Registered `thm:142D` (clauses (i) ⇔ (ii)) as a partial formalization
by adding a textbook-numbered alias `OpenMath.Chapter1.Section142.thm_142D`
that delegates to the existing `convergent_iff_minpoly_roots_lt_one`
(cycle 005). Updated `lean_status.json` to point at the new alias and
added a `notes` field documenting the deferred (iii)/(iv) clauses.
Updated `plan.md` to mark `thm:142D` as `[~]` (partial) and bumped the
progress counter from 68 / 175 to 69 / 175.

## Approach
Per the cycle 132 strategy:

1. Read `extraction/formalization_data/entities/thm_142D.json` to confirm
   the textbook statement and that the existing
   `convergent_iff_minpoly_roots_lt_one` body matches clauses (i)⇔(ii).
2. Inserted a thin alias `theorem thm_142D` at the bottom of the
   `ConvergenceCharacterizations` section in
   `OpenMath/Chapter1/Section142.lean`, with a docstring that:
   - States the partial nature explicitly (clauses (i) ⇔ (ii) only),
   - Lists clauses (iii) Jordan and (iv) Schur as deferred with a
     pointer to `.prover-state/issues/jordan_canonical_form_missing.md`,
   - Notes that this is a textbook-numbered alias of cycle 005's
     `convergent_iff_minpoly_roots_lt_one`.
3. Verified `lake env lean OpenMath/Chapter1/Section142.lean` compiles
   clean.
4. Rebuilt the `.olean` (`lake build OpenMath.Chapter1.Section142`)
   and confirmed
   `#print axioms OpenMath.Chapter1.Section142.thm_142D` shows
   `[propext, Classical.choice, Quot.sound]` only — axiom-clean.
5. Updated `extraction/formalization_data/lean_status.json`:
   - `lean_symbol` now points at `thm_142D` (was
     `convergent_iff_minpoly_roots_lt_one`).
   - Added a `notes` field describing the deferral.
6. Updated `plan.md`:
   - Progress header: 68 / 175 → 69 / 175 (with note `thm:142D` partial).
   - Row for `thm:142D` flipped from `[ ]` to `[~]` with status note.

Stretch goal (substantive r=2 IRK-stability witness) **not attempted**
this cycle — primary deliverable consumed the time budget and the
strategy explicitly says to defer if not all primary steps fit.

## Result
SUCCESS — all primary checklist items pass:

- [x] `lake env lean OpenMath/Chapter1/Section142.lean` exits 0.
- [x] `lake build OpenMath.Chapter1.Section142` succeeds.
- [x] `#print axioms OpenMath.Chapter1.Section142.thm_142D` shows
      `[propext, Classical.choice, Quot.sound]` only.
- [x] `lean_status.json` updated with new symbol and notes field.
- [x] `plan.md` shows `[~]` row and 69 / 175 progress.
- [x] No new sorry's; no axioms introduced; no maxHeartbeats raised.

## Faithfulness check

### `theorem thm_142D` (alias)

**Entity ID**: `thm:142D` *Convergence Equivalence for Matrix Powers*.

**Textbook statement (quoted from `entities/thm_142D.json`)**:
> Let \(A\) denote an \(m \times m\) matrix. The following statements are
> equivalent:
> (i) \(A\) is convergent.
> (ii) The minimal polynomial of \(A\) has all its zeros in the open
>      unit disc.
> (iii) The Jordan canonical form of \(A\) has all its diagonal
>       elements in the open unit disc.
> (iv) There exists a non-singular matrix \(S\) such that
>      \(\| S^{-1} A S \|_{\infty} < 1\).

**Lean statement captures**: WEAKER (partial) — only the (i) ⇔ (ii)
fragment of the 4-way TFAE. The Lean type is
`Convergent A ↔ ∀ μ : ℂ, μ ∈ (minpoly ℂ A).roots → ‖μ‖ < 1`, which is
exactly clauses (i) and (ii) and their bidirectional equivalence. Clauses
(iii) (Jordan canonical form) and (iv) (Schur similarity to a contraction)
are **absent** from the Lean statement — not stubbed, not encoded as
`True ↔ True` placeholders, not `sorry`'d.

**Justification for divergence**: Mathlib (as of v4.28.0) does not provide
Jordan canonical form or a rescaled Schur upper-triangular decomposition.
Both (iii) and (iv) require non-trivial Mathlib infrastructure that is
out of scope for a single cycle. The deferral is documented at
`.prover-state/issues/jordan_canonical_form_missing.md` and explicitly
called out in:
- The `thm_142D` docstring in `OpenMath/Chapter1/Section142.lean`.
- The `notes` field in `lean_status.json`.
- The `plan.md` row for `thm:142D`.

**Tautology check**: The conclusion `Convergent A ↔ …` does not appear
verbatim as a hypothesis (no hypotheses besides the matrix). ✓

**Identity check**: The proof is `convergent_iff_minpoly_roots_lt_one A`
— a direct application of the cycle 005 theorem. This is *not* a vacuous
re-export: the underlying theorem has substantive proofs in both
directions (cycle 005's eigenvector growth argument for (i) ⇒ (ii) and
cycle 005's spectral-radius / Gelfand bridge for (ii) ⇒ (i)). The
`thm_142D` alias serves the entity-graph cross-reference role, not as a
vehicle for new proof content. This pattern matches the previously
accepted `def:356A` partial (DJ-irreducibility component only) and
`def:381E` partial (IsIrreducible only).

**Definition smuggling check**: N/A — this is a `theorem`, not a `def` of
a named concept. The convergence and minimal-polynomial concepts come
from Mathlib (`Convergent` from cycle 005 in this file; `minpoly` from
Mathlib core).

**Hypothesis strength check**: No extra hypotheses beyond the textbook
statement. The Lean statement requires `[Fintype m] [DecidableEq m]` on
the index type, which are Mathlib's standard instance requirements for
matrix algebra over `ℂ` and don't represent mathematical strengthening.

## Dead ends
None this cycle — primary deliverable went straight through. The first
`#print axioms` check failed because the cached `.olean` was stale (mtime
predated the source edit); fixed by running `lake build` to regenerate
it. Not a real dead end, just a build-system gotcha worth noting.

## Discovery
- **Cached `.olean` invalidation**: `lake env lean <file>` does *not*
  refresh the package olean used by other files (or by ad-hoc scripts
  that `import OpenMath.Foo`). To run a verification script that imports
  the edited file, follow up with `lake build OpenMath.<...>` so the
  olean reflects the current source. Symptom: `unknownIdentifier` for
  the freshly-added declaration.
- **Existing `lean_status.json` schema**: the partial-formalization
  pattern uses `status: "in_progress"` (not `formalization_status:
  "partial"` as the strategy phrased it) plus an optional `notes` field.
  Verified by inspecting `def:356A`'s row before editing.

## Suggested next approach
Per the cycle 132 strategy's "next-cycle direction" guidance:

1. **Substantive r=2 IRK-stability witness** — the cycle 131 implicit
   midpoint witness is vacuous on the row-0 clauses for `r = 1`. A
   genuine substantive witness needs `r ≥ 2`. Construct a small dummy
   GLM with `s = 1, r = 2` (sketch in cycle 132 strategy §"Stretch
   goal"). Budget ~80 LOC.
2. **`thm:551B` Single Non-Zero Eigenvalue Stability** — uses the
   cycle 131 `IsIRKStable` predicate; closes a downstream consumer.
   Requires the §550 doubly-companion-matrix infrastructure (small,
   ~50 LOC). Could be bundled with item 1.
3. **`thm:431A` Schur criterion** — Mathlib has Rouché's theorem;
   medium-effort, unblocks §43 Chapter-4 stability work. Defer until a
   future cycle dedicated to §43.

Avoid in cycle 133:
- §142 (iii)/(iv) — still blocked on Jordan/Schur in Mathlib.
- `def:530A` / `thm:535A` / `thm:541A` / `def:451A` — all require
  substantial new infrastructure beyond a single cycle.
