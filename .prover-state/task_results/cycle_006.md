# Cycle 006 Results

## Worked on
- `thm:142D` direction (ii) ⇒ (i) via the spectral-radius / Gelfand-formula API.
- Public packaging `convergent_iff_minpoly_roots_lt_one` combining cycle 005's
  (i) ⇒ (ii) with the new (ii) ⇒ (i) direction.

## Approach

### Step 2 — Mathlib search round (results)

Confirmed bridges in Mathlib `v4.28.0`:

1. **Eigenvalue ↔ spectrum membership** (finite-dim end):
   `Module.End.hasEigenvalue_iff_mem_spectrum`
   `: ∀ {K V} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {f : Module.End K V} {μ : K}, f.HasEigenvalue μ ↔ μ ∈ spectrum K f`
2. **Eigenvalue ↔ minpoly root** (any commutative torsion-free domain):
   `Module.End.hasEigenvalue_iff_isRoot`
3. **Matrix vs End identification**: `Matrix.minpoly_toLin'`,
   `Matrix.toLinAlgEquiv'`, `AlgEquiv.spectrum_eq` (transfers spectrum across an
   algebra equivalence — used to bring `μ ∈ spectrum ℂ A` to
   `μ ∈ spectrum ℂ (Matrix.toLinAlgEquiv' A)`).
4. **Spectral-radius from spectrum bound**:
   `spectrum.spectralRadius_lt_of_forall_lt`
   `: [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (a : A) {r : NNReal}, (∀ z ∈ spectrum ℂ a, ‖z‖₊ < r) → spectralRadius ℂ a < ↑r`
5. **Gelfand's formula** (NNReal flavour):
   `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`
   `: [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (a : A), Tendsto (fun n => ↑‖a ^ n‖₊ ^ (1 / ↑n)) atTop (nhds (spectralRadius ℂ a))`
6. **Power tendsto-zero**:
   `tendsto_pow_atTop_nhds_zero_of_lt_one`,
   `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`,
   plus `squeeze_zero_norm'` for the squeeze.
7. **Roots-membership**: `Polynomial.mem_roots`, `minpoly.ne_zero`,
   `Matrix.isIntegral` (gives `IsIntegral ℂ A`).

`Matrix m m ℂ` carries `NormedRing`/`NormedAlgebra ℂ`/`CompleteSpace` under
`open scoped Matrix.Norms.Operator` (already in cycle 005's file). It is
`Nontrivial` exactly when `[Nonempty m]`.

### Step 3 — Sorry-first scaffold

Decomposed (ii) ⇒ (i) into three private helpers and one public theorem,
all initially `sorry`:
- `matrix_mem_spectrum_imp_isRoot_minpoly`
- `matrix_spectralRadius_lt_one_of_minpoly_roots` (`[Nonempty m]`)
- `matrix_convergent_of_spectralRadius_lt_one` (`[Nonempty m]`)
- `minpoly_roots_lt_one_imp_convergent` (handles `IsEmpty m` separately)

The public Iff `convergent_iff_minpoly_roots_lt_one` was written term-mode
once the (ii) ⇒ (i) direction existed.

Sorry-first file compiled with exactly four expected `sorry` warnings.

### Step 4 — Aristotle batch

One submission, project ID `bcf39793-94a0-498d-a11f-8fbb8c8a4da9`.
Slept 1800s, refreshed status once: `COMPLETE_WITH_ERRORS` (the cycle 005
status-vs-build false-alarm pattern). Extracted result.

### Step 5 — Post-Aristotle handling

- **Diff**: Aristotle filled all four sorry's correctly but downgraded three
  `/-- ... -/` docstrings to plain `/- ... -/` comments
  (`matrix_spectralRadius_lt_one_of_minpoly_roots`,
  `matrix_convergent_of_spectralRadius_lt_one`,
  `minpoly_roots_lt_one_imp_convergent`). Restored the docstrings verbatim
  while keeping Aristotle's proof bodies.
- **Build**: `lake env lean OpenMath/Chapter1/Section142.lean` exits 0 with
  no warnings; `lake build OpenMath` exits 0 (full project builds). The
  `COMPLETE_WITH_ERRORS` label was indeed a false alarm.

## Result
SUCCESS.

- `minpoly_roots_lt_one_imp_convergent` and the public Iff
  `convergent_iff_minpoly_roots_lt_one` are formalised, no `sorry`s.
- Cycle 005's declarations (`convergent_imp_minpoly_roots_lt_one`,
  `similar_norm_lt_one_imp_convergent`, helpers) are unchanged.
- `lake build OpenMath` exits 0.

## Faithfulness check

### `matrix_mem_spectrum_imp_isRoot_minpoly` (private helper)
- **Tautology check**: conclusion `(minpoly ℂ A).IsRoot μ` ≠ hypothesis
  `μ ∈ spectrum ℂ A`. ✓
- **Identity check**: proof routes through `AlgEquiv.spectrum_eq`,
  `Module.End.hasEigenvalue_iff_mem_spectrum`,
  `Module.End.hasEigenvalue_iff_isRoot`, `Matrix.minpoly_toLin'`. Real
  mathematical content. ✓
- **Hypothesis-strength check**: only the standard `[Fintype m]
  [DecidableEq m]` (Mathlib-mandated for `Matrix.toLinAlgEquiv'`). ✓

### `matrix_spectralRadius_lt_one_of_minpoly_roots` (private helper)
- Tautology / identity / strength: ✓.
- Carries `[Nonempty m]` because Mathlib's
  `spectrum.spectralRadius_lt_of_forall_lt` requires `[Nontrivial A]`,
  equivalent to `[Nonempty m]` for `Matrix m m ℂ`. The public theorem
  re-introduces the empty case explicitly (see below).

### `matrix_convergent_of_spectralRadius_lt_one` (private helper)
- Tautology / identity / strength: ✓.
- `[Nonempty m]` (same reason as above).

### `minpoly_roots_lt_one_imp_convergent` (public theorem, Butcher 142D (ii) ⇒ (i))
- **Entity ID and textbook statement** (from `formalization_data/entities/thm_142D.json`):
  > "Let A denote an m × m matrix. The following statements are equivalent:
  > (i) A is convergent.
  > (ii) The minimal polynomial of A has all its zeros in the open unit disc.
  > (iii) ... (iv) ..."
- **Lean statement captures**: same content as the (ii) ⇒ (i) direction.
- **Tautology check**: hypothesis is a bound on minpoly roots; conclusion is
  the ODE-style limit `Tendsto (· ^ ·) atTop (𝓝 0)`. Distinct. ✓
- **Identity check**: proof case-splits on emptiness of `m` and chains the
  two private helpers. Real content. ✓
- **Hypothesis-strength check**: only `[Fintype m] [DecidableEq m]` (no
  spurious `[Nonempty m]` on the public statement). The empty case is
  handled in-proof. ✓

### `convergent_iff_minpoly_roots_lt_one` (public theorem, Butcher 142D (i) ⇔ (ii))
- **Entity ID and textbook statement**: same as above; this is the (i) ⇔ (ii)
  fragment of the 4-way TFAE.
- **Lean statement captures**: same content for clauses (i)↔(ii); clauses
  (iii) and (iv) are *not* claimed (full TFAE remains blocked on Jordan
  canonical form — see `.prover-state/issues/jordan_canonical_form_missing.md`).
- **Tautology check**: LHS is `Tendsto (fun n => A^n) atTop (𝓝 0)`; RHS is a
  norm bound on roots of a polynomial. Distinct. ✓
- **Identity check**: not a single `exact h`; combines two real theorems
  going opposite directions. ✓
- **Hypothesis-strength check**: only `[Fintype m] [DecidableEq m]`. ✓
- **Definition-smuggling check**: `Convergent` is unchanged from `def:142B`
  (`Tendsto (fun n => a^n) atTop (𝓝 0)`). The Iff is a theorem, not a
  redefinition. ✓
- **Absent-theorem check**: docstring references
  `.prover-state/issues/jordan_canonical_form_missing.md`; that file exists. ✓

## Dead ends
None this cycle — Aristotle's first batch closed all four sub-goals on the
first try.

## Discovery
1. **`AlgEquiv.spectrum_eq` is the clean bridge** between `spectrum ℂ A`
   for a matrix and `spectrum ℂ (Matrix.toLinAlgEquiv' A)` for the
   corresponding endomorphism. Cycle 005's `matrix_minpoly_root_is_eigenvalue`
   used `Matrix.toLin'` (a linear-equiv view); switching to
   `Matrix.toLinAlgEquiv'` for the algebra-equivalence view is what makes
   `spectrum` interchangeable.
2. **`COMPLETE_WITH_ERRORS` was a false alarm again** — the file built
   cleanly with no errors after a docstring fix-up. The cycle 005 lesson
   "always re-build before trusting Aristotle's status label" continues to
   pay off; no manual fallback was needed.
3. **Docstring downgrade pattern recurs** — Aristotle silently rewrote
   `/-- ... -/` to `/- ... -/` for three of the four docstrings in this
   submission. The diff-before-commit step caught it; this remains a
   non-trivial faithfulness risk for any future submission and the diff
   step should be considered mandatory, not "cheap insurance."
4. **Empty-`m` edge case is non-trivial in Lean** — the `Subsingleton`
   approach is via `tendsto_const_nhds.congr` after rewriting using
   `isEmptyElim`. Worth keeping in mind for future matrix theorems with
   `[Nonempty m]`-required Mathlib bridges (e.g. operator-norm one-class).

## Suggested next approach

Short-term:
- **Pivot to `thm:123A`** ("Further Hamiltonian problems", §123). It is the
  next not-done item in plan order after the in-progress `thm:142D`.
  Cycle 004's `thm:123B` Hamiltonian-area-invariance proof gives reusable
  symplectic-area infrastructure.

Long-term:
- The full 4-way TFAE of `thm:142D` (clauses (iii), and the (iv) link
  through Jordan/Schur) remains blocked on Schur upper-triangular
  decomposition / Jordan canonical form in Mathlib. The blocker file
  `.prover-state/issues/jordan_canonical_form_missing.md` already documents
  the gap; building a minimal Schur block in `OpenMath/` is a 3–5 cycle
  project — defer until it becomes load-bearing.
- `thm:142E` and `thm:142F` (perturbation bounds for stable / convergent
  matrices) chain off a *fuller* 142D and a Schur-style decomposition.
  They are better attacked after the Schur infrastructure cycle, not
  before.
