# Cycle 002 Results

## Worked on

Both planner priorities landed:

- **Priority 1**: `def:142A` *power-boundedness* (Butcher §142, p. 67) →
  `OpenMath.Chapter1.Section142.PowerBounded` in
  `OpenMath/Chapter1/Section142.lean`.
- **Priority 2 (stretch)**: `def:112A` *one-sided Lipschitz condition*
  (Butcher §112, p. 47) →
  `OpenMath.Chapter1.Section112.OneSidedLipschitzInSecond` in
  `OpenMath/Chapter1/Section112.lean`.

Updated `OpenMath/Chapter1.lean` to import both new files, and
`extraction/formalization_data/lean_status.json` for both entities.

## Approach

### `def:142A` (PowerBounded)

1. Read `extraction/formalization_data/entities/def_142A.json` for the
   verbatim textbook statement. Confirmed `dependencies = []`.
2. Searched Mathlib for prior art:
   - `lean_leansearch "matrix power bounded uniformly"` returned
     `Matrix.linftyOpSemiNormedRing`, `isBounded_pow`, etc., but **no**
     named predicate for power-boundedness.
   - `lean_loogle PowerBounded` returned no results.
   - `lean_leansearch "norm A pow n NormedRing matrix"` returned the
     Mathlib matrix-norm `def`s (`linftyOpNormedRing`, `frobeniusNormedRing`,
     `l2OpNormedRingAux`, `instL2OpNormedRing`) — all **definitions**, not
     instances. Mathlib offers competing matrix norms and makes you opt in.
   - Conclusion: no Mathlib predicate to reuse; build a thin wrapper.
3. **Discovery (deviation from strategy)**: the strategy's recommended
   form `(A : Matrix n n R)` with `[NormedRing R]` does **not** typecheck
   under `Mathlib.Analysis.Matrix.Normed`, because `Norm (Matrix n n R)`
   is not synthesized — it requires opting into a specific matrix norm
   (`Matrix.linftyOpNormedRing` etc., none of which are global instances).
   The strategy's "or `Matrix.normedAddCommGroup`" hint reflects this same
   issue; the author flagged "any submultiplicative matrix norm is fine —
   the predicate is norm-equivalence-invariant up to changing `M`" but did
   not resolve where to make the choice.
   Two ways forward: (a) bake a specific norm choice (e.g. linftyOp) into
   the definition via `attribute [local instance]` — but that smuggles a
   norm choice invisibly into the predicate; (b) generalise the carrier
   from "matrix" to "element of a `SeminormedRing`" — the same pattern
   Cycle 001 used to generalise `ℝ^N` to `PseudoEMetricSpace`. Picked (b)
   as faithful and norm-choice-neutral. The Butcher textbook instance is
   recovered by choosing the carrier `A := Matrix n n ℝ` with any
   submultiplicative matrix norm, e.g. `let _ := Matrix.linftyOpNormedRing`.
   This decision and the rationale are documented in the Lean doc-comment.
4. Wrote the definition:

   ```lean
   def PowerBounded {A : Type*} [SeminormedRing A] (M : ℝ) (a : A) : Prop :=
     ∀ k : ℕ, ‖a ^ k‖ ≤ M
   ```

5. Compiled cleanly (`lake env lean OpenMath/Chapter1/Section142.lean`,
   then `lake build OpenMath` → "Build completed successfully (1887 jobs)").
6. Updated `lean_status.json`.

### `def:112A` (OneSidedLipschitzInSecond)

1. Read `extraction/formalization_data/entities/def_112A.json` for the
   verbatim textbook statement.
2. Searched Mathlib:
   - `lean_leansearch "one-sided Lipschitz"` returned only `LipschitzWith`
     variants — no match.
   - `lean_leansearch "monotone inner product norm squared bound"` returned
     Cauchy-Schwarz machinery and `real_inner_self_eq_norm_sq`, but no
     predicate matching Butcher's form.
   - Conclusion: no Mathlib predicate to reuse; build a thin wrapper.
3. **Discovery**: the scoped notation `⟪x, y⟫_ℝ` (from
   `RealInnerProductSpace`) failed to parse cleanly inside the universal
   quantifier — the parser interpreted `⟫_ℝ` as a type ascription on the
   whole bracketed expression. Worked around by using `inner ℝ x y`
   directly, which is the underlying definition the notation desugars to.
4. Wrote the definition:

   ```lean
   def OneSidedLipschitzInSecond {E : Type*}
       [NormedAddCommGroup E] [InnerProductSpace ℝ E]
       (s : Set ℝ) (ℓ : ℝ) (f : ℝ → E → E) : Prop :=
     ∀ x ∈ s, ∀ Y Z : E, inner ℝ (f x Y - f x Z) (Y - Z) ≤ ℓ * ‖Y - Z‖ ^ 2
   ```

5. Used `ℓ : ℝ` (not `ℝ≥0`) deliberately, per the strategy: one-sided
   Lipschitz constants can be negative, and that is precisely when the
   condition gives contractivity rather than mere boundedness of growth —
   a genuine difference from `def:110A`.
6. Compiled cleanly. Updated `lean_status.json`.

### Aristotle

Per strategy: skipped this cycle. Both targets are pure definitions with
no proof obligation. First Aristotle batch begins Cycle 003.

## Result

**SUCCESS.** Both definitions land cleanly.

- `lake build OpenMath` → "Build completed successfully (1887 jobs)."
- Zero errors, zero warnings.
- One commit covering both entities (see commit message).

## Faithfulness check

### `def:142A` *power-boundedness* (`def`)

- **Entity ID**: `def:142A`. Textbook statement, verbatim from
  `statement_latex` in `entities/def_142A.json`:

  > A square matrix $A$ is *stable* if there exists a constant $C$ such
  > that for all $n = 0, 1, 2, \dots$, $\|A^{n}\| \leq C$.
  > This property is often referred to as *power-boundedness*.

- **Lean statement captures**: same content, with one intentional
  generalization (carrier abstracted from "square matrix" to
  "element of a `SeminormedRing`"). The Butcher instance is recovered by
  `A := Matrix n n ℝ` with any submultiplicative matrix norm, as
  documented in the doc-comment.
- **Definition-smuggling check (PASS)**: I do **not** define
  power-boundedness via `Matrix.spectralRadius A ≤ 1`,
  `IsBounded (Set.range fun k => A ^ k)`, the minimal polynomial, or
  Jordan normal form. The Lean definition unfolds to `∀ k, ‖a^k‖ ≤ M`,
  which is verbatim Butcher's `‖A^n‖ ≤ C ∀ n`. Characterizations are
  reserved for `thm:142C`/`thm:142D`/`thm:142E`.
- **Existential-baking check (PASS)**: `M` is a parameter, not baked
  into an existential, exactly as `def:110A` exposes `L : ℝ≥0` as a
  parameter. Existential variant `∃ M, PowerBounded M a` is recoverable
  downstream when needed.
- **Hypothesis strength check**: N/A (definition, no hypotheses).

### `def:112A` *one-sided Lipschitz condition* (`def`)

- **Entity ID**: `def:112A`. Textbook statement, verbatim from
  `statement_latex` in `entities/def_112A.json`:

  > The function $f$ satisfies a `one-sided Lipschitz condition',
  > with `one-sided Lipschitz constant' $l$ if for all $x \in [a, b]$ and
  > all $u, v \in \mathbb{R}^N$,
  > $\langle f(x, u) - f(x, v), u - v \rangle \leq l \| u - v \|^2$.

- **Lean statement captures**: same content, with two intentional
  generalizations (mirroring `def:110A`):
  1. `[a, b]` → `s : Set ℝ` (Butcher recovered by `s = Set.Icc a b`).
  2. `ℝ^N` → arbitrary real inner-product space `E` with
     `[NormedAddCommGroup E] [InnerProductSpace ℝ E]` (Butcher recovered
     by `E = EuclideanSpace ℝ (Fin N)`).
- **Definition-smuggling check (PASS)**: I do **not** define one-sided
  Lipschitz via monotonicity, dissipativity in operator-theoretic form,
  or any other characterization. The predicate `inner ℝ (f x Y - f x Z)
  (Y - Z) ≤ ℓ * ‖Y - Z‖^2` is verbatim Butcher's bound.
- **Constant type (PASS — ℝ, not ℝ≥0)**: per the strategy,
  one-sided Lipschitz constants can be negative — this is exactly when
  the condition is strictly stronger than two-sided Lipschitz, giving
  contractivity. Using `ℓ : ℝ` rather than `ℓ : ℝ≥0` preserves this.
  The doc-comment flags this as a genuine difference from `def:110A`.
- **Hypothesis strength check**: N/A (definition, no hypotheses).

## Dead ends

- **Strategy-recommended Lean form for `def:142A`** (`A : Matrix n n R`
  with `[NormedRing R]`) failed to typecheck because Mathlib's matrix
  norms are `def`s, not instances. Resolved by generalising the carrier
  to a `SeminormedRing`. Documented above and in the Lean doc-comment.
- **Real inner-product notation `⟪x, y⟫_ℝ`** failed to parse inside the
  universal quantifier under `open scoped RealInnerProductSpace`.
  Sidestepped by using `inner ℝ x y` directly, which the notation
  desugars to anyway.

## Discovery

- **Mathlib matrix norms are `def`s, not instances.** `Matrix.linftyOpNormedRing`,
  `Matrix.frobeniusNormedRing`, `Matrix.l2OpNormedRingAux`, and
  `Matrix.normedAddCommGroup` (entrywise) are all `def`s in
  `Mathlib.Analysis.Matrix.Normed` (or `Mathlib.Analysis.CStarAlgebra.Matrix`).
  This is intentional — the norms are inequivalent on infinite-dimensional
  carriers, so Mathlib does not pick one globally. To use any of them you
  must `attribute [local instance]` or `let _ := ...`. Future §142
  theorems that need a specific matrix norm can opt in locally; this
  matches Mathlib's convention.
- **`Mathlib.Analysis.Matrix` is deprecated** — the new name is
  `Mathlib.Analysis.Matrix.Normed`. The compiler emits a warning if you
  use the old import. (Section142 ended up not needing matrix imports
  at all because `PowerBounded` is now `SeminormedRing`-typed.)
- **`inner ℝ` is the canonical raw form of the real inner product** —
  the `⟪_, _⟫_ℝ` scoped notation is sugar with subtle precedence
  interactions inside binders. For definition statements involving
  inner products, `inner ℝ` is more robust.
- **`NormedRing ⇒ SeminormedRing`** in Mathlib's hierarchy, so any
  carrier that's a `NormedRing` (e.g. `Matrix n n ℝ` with linftyOp norm)
  automatically satisfies the `[SeminormedRing A]` requirement of
  `PowerBounded`.

## Suggested next approach

The strategy's "Cycle 003 follow-up" remains valid:

1. **`lem:110B` investigation phase** — decide wrap-vs-restate for
   `ContractingWith.fixedPoint`. Read `entities/thm_110C.json` first to
   see what shape Picard wants. Then write `lem:110B` sorry-first.
2. **First Aristotle batch (~5 entities)**: candidates per strategy are
   `lem:110B`, `thm:101A` (Kepler — likely a worked example with explicit
   computation, possibly auto-closable), `thm:123B` (Hamiltonian area
   invariance), and one or two of `thm:142C/D/E` *only after* `def:142B`
   (`convergent` matrix) lands first. Per topo order, Cycle 003 should
   pick up `thm:101A` (next plan-order entity) plus `lem:110B` plus
   `def:142B`.
3. **Existential helper lemmas**: now that both `def:110A`,
   `def:142A`, and `def:112A` are stated with the constant as a
   parameter, downstream code may want
   `IsLipschitzInSecond` / `IsPowerBounded` / `IsOneSidedLipschitzInSecond`
   variants packaged as the existential. Defer until a downstream theorem
   actually needs them — premature.
4. **Matrix-norm choice for §142**: when `def:142B` and `thm:142C/D/E`
   land, the planner should pick a specific matrix norm (probably
   `Matrix.linftyOpNormedRing` or operator/spectral norm) and document
   the choice in `Section142.lean`. The current `PowerBounded` predicate
   is norm-choice-neutral, so the choice can be deferred to the theorem
   statements that need it.
