# Cycle 005 Results

## Worked on

`thm:142D` — Convergence Equivalence for Matrix Powers (Butcher §142).

Extended `OpenMath/Chapter1/Section142.lean` with the **two directions of
142D that are reachable in current Mathlib** (Mathlib v4.28.0 has neither
Jordan canonical form nor a Schur upper-triangular decomposition, so the
remaining clauses are infrastructure-blocked — see issue file below).

New theorems shipped:

- `convergent_imp_minpoly_roots_lt_one` — Butcher 142D direction (i) ⇒ (ii).
- `similar_norm_lt_one_imp_convergent` — Butcher 142D direction (iv) ⇒ (i).
- Three supporting helpers (private to the cycle's proof flow):
  - `matrix_minpoly_root_is_eigenvalue`
  - `matrix_pow_mulVec_of_eigenvector`
  - `mul_pow_conj_eq_pow`

New issue file: `.prover-state/issues/jordan_canonical_form_missing.md`,
documenting the Mathlib infrastructure gap blocking the (ii) ⇒ (iii),
(iii) ⇒ (iv), (i) ⇒ (iv), and (ii) ⇒ (iv) directions, and recommending
a future cycle close (i) ↔ (ii) via Mathlib's Gelfand-formula API.

`extraction/formalization_data/lean_status.json` updated: `thm:142D`
moved from `"unformalized"` to `"in_progress"`, with `lean_file` and
`lean_symbol` pointing to the (i) ⇒ (ii) theorem (the canonical entry
point into the Section 142 fragment of 142D).

## Approach

1. **Step 1 — entity load.** Read
   `extraction/formalization_data/entities/thm_142D.json`. Quoted
   `statement_latex` confirms the four clauses (i)–(iv); quoted
   `proof_latex` confirms Butcher's chain
   `(i) ⇒ (ii) ⇒ (iii) ⇒ (iv) ⇒ (i)`. `dependencies: []`,
   `transitive_dependencies: []` — no Butcher prerequisites.

2. **Step 2 — Mathlib search round** (findings captured in this file
   and reused in the issue file).

   Searched paths and verdicts:

   - `find Mathlib -iname '*jordan*'` → 5 hits; only
     `LinearAlgebra/JordanChevalley.lean` is matrix-relevant, and it
     gives only **Jordan-Chevalley** decomposition (`f = s + n` with
     `s` semisimple and `n` nilpotent commuting), **not** Jordan
     canonical form.  No `JordanForm.lean`.
   - `grep -rn 'Schur' Mathlib/LinearAlgebra/` → only `SchurComplement`
     (a 2×2 block lemma, unrelated to spectral triangularization).
     No upper-triangular similarity result.
   - `grep -rn 'Triangularizable'` → returns `IsTriangularizable` for
     Lie modules and `Module.End.iSup_genEigenspace_eq_top` (over
     algebraically closed fields with finite dimension); neither
     gives an explicit upper-triangular basis for a matrix.
   - `grep -rn 'tendsto_pow_atTop_nhds_zero'` →
     `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` lives in
     `Mathlib/Analysis/SpecificLimits/Normed.lean` and works for any
     `SeminormedRing` (so directly applicable to
     `Matrix m m ℂ` once we open `Matrix.Norms.Operator`).
   - `grep -rn 'hasEigenvalue_iff_isRoot'` → bridge from minpoly
     roots to eigenvalues, available for `Module.End` in
     `LinearAlgebra/Eigenspace/Minpoly.lean`. The matrix bridge runs
     via `Matrix.minpoly_toLin'` (`LinearAlgebra/Matrix/Charpoly/
     Minpoly.lean`).
   - `grep -rn 'spectralRadius'` → Gelfand's formula
     (`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`)
     is available for complex Banach algebras, but Mathlib has no
     direct `spectralRadius < 1 → Tendsto pow zero` wrapper, and no
     direct minpoly-root → spectrum bridge for matrices. Closing
     (ii) ⇒ (i) via Gelfand is feasible (next cycle's stretch goal)
     but not in scope this cycle.
   - `grep -rn 'Units.conj_pow'` →
     `Algebra/Group/Semiconj/Units.lean` provides
     `Units.conj_pow' : (↑u⁻¹ * x * ↑u)^n = ↑u⁻¹ * x^n * ↑u`,
     exactly what (iv) ⇒ (i) needs.
   - `grep -rn 'linfty_opNorm_mulVec'` →
     `Analysis/Matrix/Normed.lean` provides
     `‖A *ᵥ v‖ ≤ ‖A‖ * ‖v‖`, the submultiplicativity bound the
     (i) ⇒ (ii) eigenvector argument relies on.

   **Branch decision.** With no Jordan / Schur infrastructure, the
   directions `(ii) ⇒ (iii)`, `(iii) ⇒ (iv)`, and the standalone
   `(i) ⇒ (iv)` and `(ii) ⇒ (iv)` are out of reach without
   multi-cycle infrastructure work. The strategy's "ship 3-way TFAE
   `(i) ↔ (ii) ↔ (iv)`" goal is **not mathematically reachable
   without Jordan/Schur**, because closing the cycle requires at
   least one of `(i) ⇒ (iv)`, `(ii) ⇒ (iv)`, or `(ii) ⇒ (i)`, and
   only the third is conceivably reachable via Gelfand (still
   substantial work).  The **directionally honest** deliverable is
   the two named theorems
   `convergent_imp_minpoly_roots_lt_one` (i) ⇒ (ii) and
   `similar_norm_lt_one_imp_convergent` (iv) ⇒ (i), plus an issue
   file documenting the gap. No TFAE / Iff packaging, since none is
   mathematically warranted at this scope. The cycle-005 strategy's
   TFAE goal is **not met**, and that is the right call — shipping a
   `True ↔ True` placeholder for clause (iii) (or a fake Iff that
   only goes one way) would fail the faithfulness checklist.

3. **Step 3 — sorry-first scaffolding.** Wrote
   `OpenMath/Chapter1/Section142.lean` with five labeled `sorry`s
   (the two main directions plus three supporting helpers). Carrier
   chosen: `Matrix m m ℂ` (complex matrices, `[Fintype m]`,
   `[DecidableEq m]`).  Norm chosen:
   `Matrix.linftyOpNormedRing` via
   `open scoped Matrix.Norms.Operator` — Butcher cites
   `‖·‖_∞ = max_i ∑_j |a_{ij}|`, which is exactly Mathlib's
   `linftyOpNorm`. Verified the sorry-first file compiles cleanly
   (`lake env lean OpenMath/Chapter1/Section142.lean`, 5 `sorry`
   warnings, no errors).

4. **Step 4 — Aristotle batch (single submission).** Submitted the
   sorry-first file via `mcp__aristotle__submit_file` with a prompt
   pointing Aristotle at the specific Mathlib lemma names found in
   Step 2 (`Matrix.minpoly_toLin'`, `Module.End.hasEigenvalue_of_isRoot`,
   `Units.conj_pow'`, `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`,
   `linfty_opNorm_mulVec`).  Project ID
   `67ca4f6a-86b3-42dc-bf35-3e66e1861564`. Slept 30 minutes,
   refreshed status once, extracted result once.

5. **Step 5 — Aristotle results.** Status returned
   `COMPLETE_WITH_ERRORS`, but on inspection that label is
   **misleading on this run**: the extracted file compiles cleanly
   (`lake env lean … → exit 0`) and `lake build OpenMath` finishes
   with 2554/2554 jobs and zero errors / warnings.  Aristotle's
   `ARISTOTLE_SUMMARY.md` claimed "all 5 sorries filled with verified
   proofs", and the build agrees.  No manual fallback was needed.

6. **Step 6 — verification.**
   - `lake env lean OpenMath/Chapter1/Section142.lean` → exit 0.
   - `lake build OpenMath` → "Build completed successfully (2554 jobs)".
   - Diffed Aristotle's file against the sorry-first file: docstrings
     are preserved verbatim (cycle-004's "Aristotle silently
     downgraded `/-- … -/`" papercut did **not** recur this run —
     all five docstrings are intact).

## Result

**SUCCESS — partial 142D shipped.**

- `(iv) ⇒ (i)` and `(i) ⇒ (ii)` closed with full proofs, no
  `sorry`. Build clean.
- `(ii) ⇒ (iii)`, `(iii) ⇒ (iv)`, `(i) ⇒ (iv)`, `(ii) ⇒ (iv)` are
  **not in scope** this cycle (infrastructure-blocked); issue file
  written.
- No TFAE / Iff packaging is shipped, by design — see "Branch
  decision" above. Adding one would either be mathematically
  unjustified (no proven cycle) or smuggle a Jordan-form clause as
  `True` (faithfulness failure).

Aristotle's per-sub-lemma verdict (all five filled in one batch):

| sub-lemma | Aristotle outcome |
|---|---|
| `matrix_minpoly_root_is_eigenvalue` | ✓ `convert + minpoly_toLin' + hasEigenvalue_of_isRoot + exists_hasEigenvector` |
| `matrix_pow_mulVec_of_eigenvector` | ✓ induction + `mulVec_mulVec` + `mulVec_smul` + `smul_smul` |
| `convergent_imp_minpoly_roots_lt_one` | ✓ contrapositive via `Metric.tendsto_nhds`; ‖μ‖^n · ‖v‖ ≥ ‖v‖ > 0 contradicts `A^n *ᵥ v → 0` |
| `mul_pow_conj_eq_pow` | ✓ induction + `pow_succ` + `mul_assoc` |
| `similar_norm_lt_one_imp_convergent` | ✓ `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` + `Tendsto.const_mul` + `mul_const` + the helper |

## Faithfulness check

For each new declaration introduced this cycle:

### `matrix_minpoly_root_is_eigenvalue` (helper theorem)

- This is an **internal helper**, not a Butcher entity — it bridges
  `Polynomial.IsRoot (minpoly ℂ A) μ` to the matrix-vector equation
  `A *ᵥ v = μ • v`.  No Butcher statement to quote.
- Tautology check: hypothesis is a polynomial root statement,
  conclusion is an existential about eigenvectors — distinct content. ✓
- Identity check: proof is genuine (uses `Matrix.minpoly_toLin'`,
  `hasEigenvalue_of_isRoot`, `exists_hasEigenvector`,
  `Matrix.toLin'_apply` — not `exact h`). ✓
- Hypothesis-strength check: only `(minpoly ℂ A).IsRoot μ` is
  required; `[Fintype m]`, `[DecidableEq m]` are needed for
  `Matrix.minpoly_toLin'` and the algebra equivalence
  (Mathlib-mandated). ✓

### `matrix_pow_mulVec_of_eigenvector` (helper theorem)

- Internal helper; matrix analogue of
  `Module.End.HasEigenvector.pow_apply`.  No Butcher statement.
- Tautology check: hypothesis `A *ᵥ v = μ • v`, conclusion
  `A^n *ᵥ v = μ^n • v`. At `n = 0` the conclusion is `1 *ᵥ v = v`,
  which Mathlib's `one_mulVec` discharges; for `n ≥ 1` the
  conclusion is non-trivial and uses the hypothesis genuinely. ✓
- Identity check: proof is induction with
  `mulVec_mulVec`, `mulVec_smul`, `smul_smul`, `mul_comm` — real
  algebra. ✓
- Hypothesis-strength check: minimal. ✓

### `convergent_imp_minpoly_roots_lt_one` (Butcher 142D direction (i) ⇒ (ii))

- Entity ID: `thm:142D`, direction (i) ⇒ (ii).
- Quoted `statement_latex` (clauses (i) and (ii) only):
  > Let `A` denote an `m × m` matrix. […]
  > (i)  `A` is convergent.
  > (ii) The minimal polynomial of `A` has all its zeros in the open
  >      unit disc.
- Lean statement: `∀ μ : ℂ, μ ∈ (minpoly ℂ A).roots → ‖μ‖ < 1` under
  `Convergent A`. **Same content** — Butcher's "open unit disc"
  becomes `‖μ‖ < 1`, "zeros of the minimal polynomial" becomes
  `μ ∈ (minpoly ℂ A).roots`.
- Tautology check: hypothesis `Convergent A`
  (= `Tendsto (fun n => A^n) atTop (𝓝 0)`), conclusion is a
  norm-bound on minpoly roots — entirely distinct content. ✓
- Identity check: proof is contrapositive via `Metric.tendsto_nhds`
  + `linfty_opNorm_mulVec` + `norm_smul` + `one_le_pow₀` — real
  reasoning. ✓
- Hypothesis-strength check: only `Convergent A` plus `[Fintype m]`,
  `[DecidableEq m]` (Mathlib-mandated for the matrix-norm
  instance). No spurious nontriviality. ✓
- Carrier choice: `Matrix m m ℂ`. **Documented** — Butcher's eigenvalue
  argument needs an algebraically closed field, and the
  minpoly-root → eigenvalue bridge in Mathlib is also formulated over
  ℂ (or any algebraically closed field). The real case is recovered
  by complexification at downstream call sites.

### `mul_pow_conj_eq_pow` (helper theorem)

- Internal helper; conjugation identity.  No Butcher statement.
- Tautology check: equation between two distinct algebraic
  expressions; non-trivial at every `n ≥ 0` (`n = 0` reduces to
  `S * S⁻¹ = 1` which is `Units.mul_inv`). ✓

### `similar_norm_lt_one_imp_convergent` (Butcher 142D direction (iv) ⇒ (i))

- Entity ID: `thm:142D`, direction (iv) ⇒ (i).
- Quoted `statement_latex` (clauses (iv) and (i) only):
  > (iv) There exists a non-singular matrix `S` such that
  >      `‖S⁻¹ A S‖_∞ < 1`.
  > (i)  `A` is convergent.
- Lean statement: `(∃ S : (Matrix m m ℂ)ˣ, ‖↑S⁻¹ * A * ↑S‖ < 1) →
  Convergent A`.  **Same content** — Butcher's "non-singular `S`"
  becomes `S : (Matrix m m ℂ)ˣ` (the units of the matrix ring,
  i.e. invertible matrices); the existential matches the
  textbook's "there exists".
- Tautology check: hypothesis is a similarity-norm bound,
  conclusion is convergence of `A^n` — distinct content. ✓
- Identity check: proof uses
  `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` + `Tendsto.const_mul`
  + `mul_const` + `mul_pow_conj_eq_pow` — real reasoning, not a
  trivial re-export. ✓
- Hypothesis-strength check: only the textbook hypothesis (existence
  of `S`) plus the standing `[Fintype m]`, `[DecidableEq m]`. No
  extra `[Nontrivial m]`. ✓

### Carrier and norm choices (cycle-wide)

- Carrier: `Matrix m m ℂ` with `[Fintype m]`, `[DecidableEq m]`.
- Norm: `Matrix.linftyOpNorm` via
  `open scoped Matrix.Norms.Operator` — Butcher's `‖·‖_∞ = max_i
  ∑_j |a_{ij}|`. This matches the textbook's notation `‖·‖_∞`
  exactly. The `Convergent` predicate from `def:142B` is
  `SeminormedRing`-generic; it specialises to
  `Matrix m m ℂ` via `Matrix.linftyOpNormedRing`, and the result is
  norm-equivalence-invariant on the finite-dimensional space (so
  any submultiplicative matrix norm gives the same `Convergent`
  predicate up to picking a different witness in the (iv) clause).

## Dead ends

None — Aristotle one-shot all five sorries on the first batch, exactly
as the strategy predicted for `(iv) ⇒ (i)` and (with a question mark) for
`(i) ⇒ (ii)`. No manual fallback was needed.

The "dead end" for the cycle as a whole is the `(ii) ⇒ (iv)` /
Jordan-form direction, but that was correctly identified during the
Step-2 search round, **before** any sorry was written, and routed to
an issue file rather than wasted Aristotle quota.

## Discovery

- **Aristotle's `COMPLETE_WITH_ERRORS` status was a false alarm on
  this run.**  The extracted file compiled cleanly and `lake build
  OpenMath` succeeded with zero errors / warnings.  In future
  cycles, do **not** treat `COMPLETE_WITH_ERRORS` as definitive
  failure — always run the file through `lake env lean` before
  starting manual fallback.  The status reflects Aristotle's
  internal verifier output, which seems to disagree with the
  pinned `v4.28.0` build sometimes.

- **Docstring-preservation was clean this run** (cycle-004 caught
  Aristotle silently downgrading `/-- … -/` to `/- … -/`; that did
  not recur). Diffed Aristotle's output against the sorry-first
  file before committing — recommended habit.

- **`Module.End.hasEigenvalue_of_isRoot` requires `[IsTorsionFree R M]`
  in addition to the documented `[IsDomain R] [Module.Finite R M]`.**
  For `R = ℂ, M = m → ℂ`, all three hold automatically (ℂ is a
  field, `m → ℂ` is a finite-dimensional torsion-free module).
  Aristotle handled the instance synthesis silently via two
  `infer_instance` calls inside `convert`.

- **The strategy's "ship 3-way TFAE" goal was mathematically
  unreachable without Jordan/Schur**, contrary to its own
  acknowledgement of the gap. The right call this cycle was to ship
  the two directionally honest theorems and document the gap, rather
  than fabricate an Iff that does not hold.  Future planners
  proposing a TFAE on §14x convergence theorems should first verify
  that all four directions are reachable, not just two.

- **`lake env lean` is much faster than `lake build` on a single
  edited file** (~12s for `Section142.lean` alone vs ~40s+ for
  `lake build OpenMath` end-to-end). Use the per-file form during
  iteration and reserve `lake build OpenMath` for the final
  pre-commit check.

## Suggested next approach

For cycle 006, in descending order of attractiveness:

1. **Close `(ii) ⇒ (i)` via Gelfand's formula** (the issue file's
   recommendation (c)). This converts the cycle-005 partial
   `(iv) ⇒ (i) ⇒ (ii)` chain into a full `(i) ↔ (ii)` Iff plus the
   `(iv) ⇒ (i)` direction, without touching Jordan form. Estimated
   1 cycle. Bridges needed:
   - `μ ∈ (minpoly ℂ A).roots → μ ∈ spectrum ℂ A` for matrices (via
     `hasEigenvalue_of_isRoot` + `HasEigenvalue.mem_spectrum`).
   - `spectralRadius ℂ A ≤ 1 ⊔ sup_{μ ∈ minpoly.roots} ‖μ‖`
     (probably routine from `spectrum.elem_le_spectralRadius`).
   - `spectralRadius ℂ A < 1 → Tendsto (A^·) atTop (𝓝 0)` via
     Gelfand's `pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`
     plus a small ε-argument.

   This strictly extends cycle-005's deliverable and remains
   plan-order-faithful (still in `thm:142D`).

2. **`thm:112B`** (one-sided Lipschitz solution-difference bound)
   if cycle-006 wants to pivot away from §142 to §11x.  Deps
   `def:112A` (✓ from cycle 002).  Needs Grönwall +
   `norm_inner_le_norm` from Mathlib + a `HasDerivAt` computation
   on `‖y₁ - y₂‖²`.  Mathlib's Grönwall lives in
   `Mathlib.Analysis.ODE.Gronwall`.

3. **`thm:142E`** (Stable-matrix perturbation power bound) — depends
   on `def:142A` (✓) and on having the partial 142D shipped this
   cycle. Worth scoping only after option (1) is taken (so 142D is
   stronger than just two directional theorems).

4. **Build a minimal Schur decomposition in `OpenMath/`** to unblock
   the full 142D TFAE — the issue file's option (b). Multi-cycle.
   Defer until §142 becomes blocking for downstream chapters.

The plan-order rule prefers (1) over (2): cycle-005 left `thm:142D`
in `"in_progress"`, and option (1) finishes a strict superset of it.
Option (2) is the right pivot only if a planner judges that the
Gelfand bridges are themselves an infrastructure detour.
