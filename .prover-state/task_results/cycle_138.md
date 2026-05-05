# Cycle 138 Results

## Worked on

- New file `OpenMath/Chapter5/Section550.lean` opening §550.
- Definitions: `doublyCompanionMatrix` (Butcher equation 550a), `alphaPoly`,
  `betaPoly`.
- Theorem statement `doublyCompanionMatrix_det_factorization` for general n,
  sorry-first.
- **Closed** specialization `doublyCompanionMatrix_det_factorization_n_one`
  axiom-clean.
- Plumbing: `OpenMath/Chapter5.lean` import, `lean_status.json`, `plan.md`.
- Issue `.prover-state/issues/thm_550A_general_n.md` documenting deferral
  for general n.
- Aristotle batch (2 jobs): general-n + n=2 specialization, project IDs
  recorded in `.prover-state/aristotle_submissions/cycle_138/README.md`.

## Approach

### Step 1 — `doublyCompanionMatrix` definition

Encoded the matrix from (550a) entry-by-entry over ℂ via dependent-if
guards:

```lean
def doublyCompanionMatrix {n : ℕ} (α β : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j =>
  if h0 : i.val = 0 then
    if hj : j.val + 1 = n then
      -α ⟨n - 1, by omega⟩ - β ⟨n - 1, by omega⟩
    else
      -α j
  else if hj : j.val + 1 = n then
    -β ⟨n - i.val - 1, by omega⟩
  else if i.val = j.val + 1 then 1 else 0
```

The strategy's draft used `j.val = n - 1` directly which fails when
`n = 0` (`n - 1` underflows in ℕ subtraction). Switching to
`j.val + 1 = n` makes the guard well-typed at `n = 0` (vacuously) and
allows safe `Fin` constructions via `omega`.

### Step 2 — `n = 1` reduction sanity helper

```lean
@[simp]
lemma doublyCompanionMatrix_one_eq (α β : Fin 1 → ℂ) :
    doublyCompanionMatrix α β = !![-α 0 - β 0] := by
  ext i j; fin_cases i; fin_cases j; simp [doublyCompanionMatrix]
```

This closes by `simp` evaluating the dependent-if at `n = 1`,
`i.val = j.val = 0`, producing the corner entry `-α (n-1) - β (n-1)`.

### Step 3 — `n = 1` IsBigO closure

The proof shape:

1. Prove the residue equals `-(α 0 * β 0) * z^2` *as a function*:
   - rewrite via `doublyCompanionMatrix_one_eq`
   - reduce `(1 - z • !![-α 0 - β 0])` to `!![1 + z * (α 0 + β 0)]` by
     `Matrix.ext`/`fin_cases` + `simp; ring`
   - close determinant via `Matrix.det_fin_one`
   - simplify `alphaPoly`, `betaPoly` (each becomes `1 + α 0 * z`,
     `1 + β 0 * z`) and finish with `ring`.
2. Conclude `IsBigO _ ((-α 0 * β 0) * z^2) (z^2)` via
   `(isBigO_refl _ _).const_mul_left _`.

Final proof is ~25 LOC including a `funext` and the matrix lemma
glue.

### Step 4 — Plumbing

* Added `import OpenMath.Chapter5.Section550` to
  `OpenMath/Chapter5.lean` (in the alphabetical/numeric order).
* `lean_status.json` for `thm:550A`: status → `partial`,
  `lean_file` set, `lean_symbol` set to the general-n statement,
  cycle 138, notes pointing to the n=1 witness and the deferral issue.
* `plan.md` Chapter 5 row updated to `[~]` with full provenance.

### Step 5 — Issue file

`.prover-state/issues/thm_550A_general_n.md` documents:
- file/line reference
- textbook proof outline (eigenvalue density)
- why deferred (multi-cycle Mathlib assembly)
- 4 possible solution paths (cofactor expansion, eigenvalue density,
  induction, Aristotle)
- cross-references to dependents `thm:550B`, `thm:551B`, `thm:553A`.

### Step 6 — Aristotle batch

Two jobs submitted (file content adapted from Section550.lean,
self-contained):
- Job A — general n: project `7062c2a2-4a8b-4fae-b694-9355e06427a9`
- Job B — n = 2:    project `70f26d67-b37e-4eda-b946-64c9f4616612`

Per project policy, jobs left to run; cycle 139 will check.

## Result

SUCCESS.

* `lake env lean OpenMath/Chapter5/Section550.lean` exits 0 (only the
  expected `sorry` warning on the general-n statement).
* `lake env lean OpenMath/Chapter5.lean` exits 0 after the import
  addition.
* `#print axioms OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization_n_one`
  returns `[propext, Classical.choice, Quot.sound]` (axiom-clean).
* Tautology scanner: 0 *new* hits from cycle 138 (1 pre-existing hit
  in `Section514.lean:469` is unrelated to this cycle).

Success criteria from strategy (≥3 of 8 → cycle ≥ +1):
- [x] `Section550.lean` exists, builds clean.
- [x] `doublyCompanionMatrix` defined with correct entries (verified
      via the `_one_eq` lemma).
- [x] `_n_one` closed axiom-clean.
- [x] General-n stated sorry-first with the correct IsBigO conclusion.
- [x] `Chapter5.lean` imports `Section550`.
- [x] `lean_status.json` and `plan.md` updated.
- [x] `thm_550A_general_n.md` issue written.
- [x] Aristotle batch submitted with project IDs recorded.

8/8 success criteria met.

## Faithfulness check

### `def` `doublyCompanionMatrix`

- Entity ID `thm:550A` (the matrix is the central object of the
  theorem).
- Textbook statement (quoted from `entities/thm_550A.json`):
  > X = [[-α₁, -α₂, ..., -α_{n-1}, -αₙ - βₙ],
  >      [1, 0, ..., 0, -β_{n-1}],
  >      [0, 1, ..., 0, -β_{n-2}],
  >      ..., [0, 0, ..., 1, -β₁]]
- Lean statement captures: **same content** (with the documented
  0-indexed convention `α 0 ↔ α₁`). Each entry verified by case
  analysis: row 0 column 0..n-2 = `-α j`, row 0 column n-1 =
  `-α (n-1) - β (n-1)`, row i ≥ 1 column n-1 = `-β (n-i-1)`,
  sub-diagonal = 1, else 0. The `n = 1` reduction
  `!![-α 0 - β 0]` matches the textbook (550a) at n=1.

### `def` `alphaPoly`, `betaPoly`

- Textbook statements:
  > α(z) = 1 + α₁z + ··· + αₙzⁿ
  > β(z) = 1 + β₁z + ··· + βₙzⁿ
- Lean statements capture: **same content** under `α 0 ↔ α₁` indexing,
  encoded as `1 + ∑ i : Fin n, α i * z^(i.val + 1)`.

### `theorem` `doublyCompanionMatrix_det_factorization` (sorry-first)

- Entity ID `thm:550A`.
- Textbook statement:
  > 1 + γ₁z + γ₂z² + ⋯ + γₙzⁿ = det(I − zX) = α(z)β(z) + O(z^{n+1})
- Lean statement captures: **the second equality**, which is the
  substantive content of the theorem (the first equality is a generic
  matrix fact about charpoly coefficients vs `det(I - zX)`, not specific
  to doubly companion matrices, as noted in the strategy). The IsBigO
  formulation `IsBigO (𝓝 0) residue (z^{n+1})` matches the standard
  Lean idiom for `O(z^{n+1}) as z → 0`.
- Justification for not encoding the γ_i = charpoly coefficients
  identity: it is a generic fact unrelated to the doubly-companion
  structure. Adding it would expand scope; the strategy explicitly
  flagged this as out-of-scope.

### `theorem` `doublyCompanionMatrix_det_factorization_n_one`

- Entity ID `thm:550A` (specialised to n=1).
- Textbook statement at n=1: with X = [[-α₁ - β₁]],
  det(I - zX) = 1 + (α₁ + β₁)z, α(z)β(z) = 1 + (α₁+β₁)z + α₁β₁z²,
  so residue = -α₁β₁ z² ∈ O(z²).
- Lean statement captures: **same content**. The proof reduces the
  residue to `-(α 0 * β 0) * z^2` pointwise and concludes IsBigO via
  `isBigO_refl.const_mul_left`.
- Hypothesis strength check: zero hypotheses beyond `α β : Fin 1 → ℂ`,
  matching the textbook.
- Tautology check: conclusion is an asymptotic bound on the residue,
  not a hypothesis. No tautology.
- Identity check: proof body is non-trivial (matrix algebra +
  determinant computation + asymptotic bookkeeping).

## Dead ends

- **Initial imports**: `Mathlib.Data.Complex.Basic` brings ℂ as a ring
  but not as a normed/topological space. Switched to
  `Mathlib.Analysis.SpecialFunctions.Complex.Analytic` which transitively
  pulls in `NormedField ℂ` and the topology.
- **Computability**: `alphaPoly` and `betaPoly` involve `Complex.add`
  / `Complex.mul` which are noncomputable in their `NormedField`
  registration. Marked both definitions `noncomputable`.
- **Strategy guard `j.val = n - 1`**: would have failed at `n = 0`
  (ℕ subtraction underflow gives `0 - 1 = 0`, but the matrix is empty
  there anyway — yet `omega` could not discharge `n - 1 < n` without
  `n ≥ 1` hypothesis). Changed to `j.val + 1 = n`, which is always
  well-typed and allows `omega` to prove `Fin n` index bounds.
- **`simp [Fin.sum_univ_one]`**: linter flagged it as unused in the
  `n = 1` case (the sum reduction was already triggered by upstream
  `simp` lemmas). Removed.

## Discovery

- The `_one_eq` reduction lemma using `@[simp]` makes the `n = 1`
  proof essentially fall out: a single `simp` after the rewrite
  reduces the polynomial product to a `ring`-friendly form.
- For matrix `IsBigO` against `z^k` near 0, the cleanest endgame is to
  rewrite the LHS as a constant multiple of `z^k` *as a function*
  (via `funext`) then apply `(isBigO_refl _ _).const_mul_left _`.
  The `IsBigO.of_bound` route requires building a normed-bound
  filter-eventually, which is heavier here.
- Strategy's suggested `Mathlib.Analysis.Asymptotics.AsymptoticEquivalent`
  + `Mathlib.Analysis.Asymptotics.Defs` are not enough alone for the ℂ
  topology; need an `Analysis.SpecialFunctions.Complex.*` import to
  bring in the topological structure of ℂ. Same gotcha will apply to
  any future §550 work.
- The dependent-if guard pattern (`if h : <prop> then ... else ...`)
  with bound hypothesis name is essential for `omega`-discharged `Fin`
  constructions inside the body — without binding the proof, `omega`
  cannot see the case-distinction.

## Suggested next approach

For **cycle 139**:

1. **Check Aristotle returns first** (project IDs recorded in
   `aristotle_submissions/cycle_138/README.md`). If Job B (n=2)
   returns clean, incorporate as
   `doublyCompanionMatrix_det_factorization_n_two` directly into
   Section550.lean — this would give a second concrete witness.

2. **Fallback if Aristotle fails**: manually close `n = 2` using
   `Matrix.det_fin_two`, paralleling the n=1 proof. ~80 LOC. The
   determinant expands to
   `(1 + α 0 z)(1 + β 0 z) - z² · (-α 1 - β 1)`,
   and `α(z) · β(z) = 1 + (α 0 + β 0) z + (α 0 β 0 + α 1 + β 1) z² +
   (α 0 β 1 + α 1 β 0) z³ + α 1 β 1 z⁴`,
   so the residue is
   `-(α 0 β 1 + α 1 β 0) z³ - α 1 β 1 z⁴ = z³ · [-(α 0 β 1 + α 1 β 0) − α 1 β 1 z]`,
   a `z³ · g(z)` form with `g` continuous near 0, hence `IsBigO _ _ z³`.

3. **For the general-n attack**: the cleanest path appears to be the
   **induction on n via row-reduction**. The bottom-right (n-1)×(n-1)
   block of `X` is itself a doubly companion matrix with shifted
   coefficients. The Laplace expansion along the first column gives
   `det(I - zX) = (1 + α 0 z) · det(M_{n-1}) - z · det(...)`
   where `M_{n-1}` is the companion-shape recursive case. Sketching
   this out is the right cycle 139 deliverable.

4. **Do NOT pivot**: the explicit cycle 138 mandate was to land the
   §550 scaffold. Cycle 139 should continue this work, not start
   another section.
