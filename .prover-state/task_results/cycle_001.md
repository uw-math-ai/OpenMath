# Cycle 001 Results

## Worked on

Bootstrap of the Lean library layout and formalization of `def:110A` —
"Lipschitz condition in its second variable" (Butcher §110, p. 43).

Created:
- `OpenMath.lean` (root) — `import OpenMath.Chapter1`
- `OpenMath/Chapter1.lean` — `import OpenMath.Chapter1.Section110`
- `OpenMath/Chapter1/Section110.lean` — namespace
  `OpenMath.Chapter1.Section110`, holds `def:110A` (and will hold `lem:110B`,
  `thm:110C` in subsequent cycles).

Updated `extraction/formalization_data/lean_status.json` for `def:110A`.

## Approach

1. Read `extraction/formalization_data/entities/def_110A.json` for the
   verbatim textbook statement.
2. Searched Mathlib for prior art:
   - `LipschitzWith` is defined in
     `Mathlib/Topology/EMetricSpace/Lipschitz.lean:58` as
     `def LipschitzWith (K : ℝ≥0) (f : α → β) := ∀ x y, edist (f x) (f y) ≤ K * edist x y`
     for `[PseudoEMetricSpace α] [PseudoEMetricSpace β]`.
   - `LipschitzOnWith` exists at line 62 of the same file.
   - No predicate for "Lipschitz in the second variable only" was found —
     consistent with the planner's expectation. Built the wrapper.
3. Wrote `LipschitzInSecond` as a thin wrapper over `LipschitzWith`:

   ```lean
   def LipschitzInSecond {E F : Type*}
       [PseudoEMetricSpace E] [PseudoEMetricSpace F]
       (s : Set ℝ) (L : ℝ≥0) (f : ℝ → E → F) : Prop :=
     ∀ x ∈ s, LipschitzWith L (f x)
   ```

   `L : ℝ≥0` is exposed as a parameter (matching Butcher's "there exists a
   constant `L`") rather than baked in existentially, per the planner's
   guidance (downstream Picard-style proofs need to extract `L`).
4. Ran `lake build OpenMath`. All three new files compile cleanly with zero
   errors and zero warnings (1230 jobs total — 1227 from Mathlib's transitive
   import closure of `Mathlib.Topology.MetricSpace.Lipschitz`, plus the 3
   new files).
5. Updated `extraction/formalization_data/lean_status.json` for `def:110A` to
   `formalized` with `lean_symbol = OpenMath.Chapter1.Section110.LipschitzInSecond`.

Note: `.lake` was a real directory (not a symlink to NVMe) and Mathlib oleans
were absent. Ran `lake exe cache get` from the project root to fetch the
8010-file Mathlib cache before `lake build` could succeed. This is a one-time
bootstrap cost; subsequent cycles will use the existing `.lake/`.

## Result

SUCCESS.

- `lake build OpenMath` → "Build completed successfully (1230 jobs)."
- No errors, no warnings.
- Definition reuses `LipschitzWith` (Mathlib primitive) and so inherits all
  Mathlib lemmas about Lipschitz functions for free.

## Faithfulness check

`def:110A` is a `def`. Per CLAUDE.md, only the **For every new `def`**
checklist applies; the structure-field, tautology, and identity checks do
not (no `class`, `structure`, `theorem`, or `lemma` introduced this cycle).

- **Entity ID**: `def:110A` — *Lipschitz condition in its second variable*.
  Textbook statement (verbatim from `statement_latex` in
  `entities/def_110A.json`):

  > The function $f : [a, b] \times \mathbb{R}^N \to \mathbb{R}^N$ is said to
  > satisfy a *Lipschitz condition in its second variable* if there exists a
  > constant $L$, known as a *Lipschitz constant*, such that for any
  > $x \in [a, b]$ and $Y, Z \in \mathbb{R}^N$,
  > $\| f(x, Y) - f(x, Z) \| \le L \| Y - Z \|.$

- **Lean statement captures**: same content, with two intentional generalizations
  required by the strategy:
  1. Codomain `F` and second-variable domain `E` are abstracted to
     `PseudoEMetricSpace` (textbook concretizes to `ℝ^N`). The Butcher
     instance is recovered by `E = F = EuclideanSpace ℝ (Fin N)`.
  2. The closed interval `[a, b]` is generalized to `s : Set ℝ`. The Butcher
     instance is recovered by `s = Set.Icc a b`.

  Both generalizations are explicit in the `LipschitzInSecond` doc-comment.
  Modulo these, the predicate `∀ x ∈ s, LipschitzWith L (f x)` unfolds (for
  fixed `x`) to `∀ Y Z, edist (f x Y) (f x Z) ≤ L * edist Y Z`, which on a
  metric (not pseudo-EMetric) space and for finite `L`, is equivalent to the
  textbook bound `‖f(x, Y) - f(x, Z)‖ ≤ L ‖Y - Z‖`.

- **Definition-smuggling check**: not applicable. The textbook itself states
  the definition as the Lipschitz bound; we are not encoding a
  characterization theorem as a definition. The constant `L` is a parameter
  (matching Butcher's "there exists a constant `L`"), not the predicate
  itself — the existential variant `∃ L, LipschitzInSecond s L f` is
  available downstream when needed.

- **Hypothesis strength check**: N/A (no hypotheses — this is a `def`, not a
  theorem).

No `class`/`structure` introduced, so the structure-field checklist is moot.
No `theorem`/`lemma` introduced, so the tautology/identity/hypothesis-strength
checklists are moot.

## Dead ends

None. Compilation succeeded on the first build (after fetching the Mathlib
cache). The only "dead end" was the initial `lake env lean` failure —
expected, since `.lake/build` had no Mathlib oleans yet; resolved by
`lake exe cache get`.

## Discovery

- **Build-cache bootstrap**: `lake exe cache get` is required before any
  `lake build` / `lake env lean` will succeed if `.lake/build/lib/lean/Mathlib`
  is empty. Took ~3 minutes to download 8010 files. Subsequent cycles can
  skip this step.
- **`LipschitzWith` is over `PseudoEMetricSpace`, not `PseudoMetricSpace`.**
  Using the EMetric form keeps the wrapper maximally general; the metric-space
  instance follows automatically via Mathlib's instance hierarchy when
  Butcher's downstream theorems specialize to `ℝ^N` (which is a
  `MetricSpace ⇒ PseudoMetricSpace ⇒ PseudoEMetricSpace`). No explicit
  conversion needed.
- **`Mathlib.Topology.MetricSpace.Lipschitz` re-exports**
  `Mathlib.Topology.EMetricSpace.Lipschitz` via `public import`, so importing
  the metric-space file is sufficient to bring `LipschitzWith` into scope.
- **`L : ℝ≥0` not `L : ℝ`**: Mathlib's convention. `ℝ≥0` (i.e. `NNReal`)
  embeds into both `ℝ` and `ℝ≥0∞`, so coercions to `‖·‖`-style real bounds are
  automatic. Future formalizations of §110 should follow this convention.

## Suggested next approach

Per the strategy's "Suggested next approach" line: pick **`def:142A`
power-boundedness** (zero-dependency, Ch.1 §142 stability prerequisite,
isolated from §110 so no coupling risk).

`def:112A` (initial value problem) is also zero-dependency and would be a
valid alternative — but `def:142A` is more isolated and lets the planner
grow §142 in parallel with §110 / §111. Either works; the planner has the
full Ch.1 dependency graph in `topo_order.json`.

For Cycle 002, the planner should also begin enabling the Aristotle-first
workflow: `lem:110B` (contraction mapping principle) is the first lemma
with a non-trivial proof obligation, and per CLAUDE.md should be batched
with ~4 other proof-bearing entities at the start of the cycle to maximize
free Aristotle compute. However, since `lem:110B` has Banach-fixed-point as
a candidate Mathlib reuse (`ContractingWith.fixedPoint` exists), the
planner should first decide whether to wrap the Mathlib version or restate
Butcher's specific framing.
