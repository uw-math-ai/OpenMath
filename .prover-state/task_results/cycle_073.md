# Cycle 073 Results

## Worked on

* **Priority 0**: Landed the staged cycle 071+072 work
  (`runningMaxAbs` infrastructure + `thm:405A` closure) as commit
  `7c69187`, advancing `HEAD` past `9c209da` and breaking the
  cycle 008/035/071/072 commit-failure chain. Updated
  `attempts.md` Cycle 72 entry to reflect that the cycle 072
  commit failure was real (fourth occurrence) and resolved by
  cycle 073.
* **Priority 1**: Created `OpenMath/Chapter4/Section410.lean` with
  the §410 generating-function infrastructure (`αPoly`, `βPoly`,
  `C`, `expNegPS`) and a sorry-first scaffold for `thm:410A`.
  Added `import OpenMath.Chapter4.Section410` to
  `OpenMath/Chapter4.lean`.
* **Priority 2**: Submitted Aristotle batch (5 sub-lemmas in one
  project) at 15:43 UTC (project ID
  `503ca4f4-87fe-421a-803d-20db5b4ab1aa`).
* **Priority 3**: Manually closed 7 sub-lemmas in
  `Section410.lean` with clean axioms.

## Approach

### §410 sign convention (the design decision)

Butcher's §410 polynomial α(z) satisfies (410c):
`α(exp(-z)) - z β(exp(-z)) = C₀ + C₁ z + C₂ z² + ⋯`. With our
def:404B normalisation `α 0 = -1`, matching this identity required
some care — direct verification with explicit Euler showed that
the polynomial in (410c) corresponds to

```
α(z) = 1 - Σ_{i=1}^k M.α_i · z^i,    β(z) = Σ_{i=0}^k M.β_i · z^i.
```

(Constant term `α(1) = 1 - Σ M.α_i.succ = C M 0`.) This matches
the planner's suggested encoding. Verified by hand that the j-th
coefficient of `α(exp(-z)) - z β(exp(-z))` exactly equals the
proof-formula `C_j = -Σ_{i=1}^k α_i (-i)^j / j! - Σ_{i=0}^k β_i (-i)^{j-1} / (j-1)!`
for every `j ≥ 1`, and `C_0 = 1 - Σ α_i.succ` for the constant.
The β-sum's `i = 0` contribution at `j = 1` correctly produces
`-β_0` (from `(-(0 : ℝ))^0 = 1`) and `0` for `j ≥ 2`.

### Faithfulness — `C` defined directly from LMM coefficients

`C M j` is defined via the closed form Butcher derives in the
proof of (410A), NOT via the power-series coefficients of the
RHS of (410c). This makes `thm_410A` a substantive identity
asserting equality between two independently-defined quantities,
not a tautology.

### Sub-lemmas closed manually

* `C_zero` — definitional unfold `C M 0 = 1 - Σ M.α i.succ` (rfl).
* `C_zero_eq_zero_iff_isPreconsistent` — connects §410 to def:404A
  preconsistency (linarith).
* `αPoly_explicitEuler` — `αPoly explicitEulerLMM = 1 - X` (simp
  + explicitEulerLMM unfold).
* `βPoly_explicitEuler` — `βPoly explicitEulerLMM = X`.
* `αPoly_eval_one` — `(αPoly M).eval 1 = 1 - Σ M.α i.succ`
  (`simp [eval_finset_sum]`).
* `αPoly_eval_one_eq_C_zero` — bridge between polynomial-evaluation
  and Taylor-coefficient forms.
* `C_zero_explicitEuler` — explicit Euler is preconsistent ⇒
  `C explicitEulerLMM 0 = 0` (mpr of the iff).

### Aristotle batch

Submitted one self-contained file with 5 sub-lemmas:

1. `αPoly_natDegree_le` — degree bound, useful for §410B/C/D.
2. `βPoly_natDegree_le` — analogous degree bound.
3. `expNegPS_coeff` — `coeff n expNegPS = (-1)^n / n!`.
4. `coeff_aeval_C_X_pow` — closed form for the j-th coefficient
   of `aeval expNegPS (C c * X^m)` — the *key* helper for
   thm:410A.
5. `thm_410A_zero` — the j=0 case of thm:410A.

## Result

**SUCCESS** (Priority 0–3).

* Priority 0: `git log -1` now shows `7c69187` (cycle 071+072
  commit).
* Priority 1: `Section410.lean` compiles cleanly under both
  `lake env lean` and `lake build OpenMath.Chapter4.Section410`
  (with the expected single `sorry` warning on `thm_410A`).
  Aristotle submission file also compiles standalone.
* Priority 2: Aristotle project queued/in_progress; results
  to be incorporated below if returned.
* Priority 3: 7 manually-closed sub-lemmas all have clean axiom
  set `[propext, Classical.choice, Quot.sound]` (verified via
  `#print axioms` after `lake build` — required since cycle 072
  noted `lake env lean` does NOT refresh the .olean cache for
  `#print axioms`).

`lean_status.json::thm:410A` now points at
`OpenMath.Chapter4.Section410.thm_410A` with status `in_progress`.
`plan.md::thm:410A` switched from `[ ]` to `[~]` with the
cycle-073 cross-reference.

## Faithfulness check

For each new `def`/`theorem` introduced this cycle:

### `def αPoly`

* Entity context: Butcher §410, equation (410a)/(410c) —
  `α(z) = α_k z^k + α_{k-1} z^{k-1} + ⋯ + α_0` (per
  `entities/thm_410C.json::variables`), with the §410 polynomial
  satisfying (410c) `α(exp(-z)) - z β(exp(-z)) = Σ Cⱼ zʲ`.
* Lean statement captures: same content as Butcher's §410 α,
  modulo the LMM `α 0 = -1` normalisation: our `αPoly = 1 - Σ`
  matches Butcher's polynomial that satisfies (410c). Verified by
  explicit-Euler hand computation (`αPoly explicitEulerLMM = 1 - X`
  is consistent with C₂ = 1/2, C₃ = -1/3 for explicit Euler).
* Sign convention documented in the file header.

### `def βPoly`

* Entity context: Butcher §410 — `β(z) = β_k z^k + ⋯ + β_0`.
* Lean statement captures: same content (no sign flip — β indexing
  matches our LMM convention directly).

### `def C`

* Entity context: Butcher (410b)/(410A proof) — Cⱼ are the Taylor
  coefficients of the residual L(y, x_n, h).
* Lean statement captures: same content. Defined faithfully via
  Butcher's closed-form expression in the proof, NOT via the
  generating-function coefficients (which would make `thm_410A`
  vacuous).
* Definition smuggling check: ✓ — Cⱼ depends only on `M.α` and
  `M.β`, not on `αPoly` / `βPoly` / `expNegPS`.

### `def expNegPS`

* A direct PowerSeries definition `Σ (-1)^n z^n / n!`. Not in
  Butcher per se — a Lean-side helper. Documented as a helper
  (avoids threading `Algebra ℚ ℝ` for `PowerSeries.exp`).

### `theorem thm_410A`

* Entity ID `thm:410A`, textbook statement (entities/thm_410A.json):
  > The constants C₀, C₁, C₂, … in (410b) are given by
  > α(exp(−z)) − zβ(exp(−z)) = C₀ + C₁ z + C₂ z² + ⋯.
* Lean statement captures: same content. The Lean theorem asserts
  that the j-th `PowerSeries.coeff` of `aeval expNegPS αPoly M
  - X * aeval expNegPS βPoly M` equals `C M j`, for every `j`.
* Tautology check: ✓ — LHS is a generating-function coefficient,
  RHS is the closed-form Cⱼ via LMM coefficients. They are
  independently defined.
* Hypothesis strength: ✓ — Butcher takes only an LMM, no
  preconsistency / consistency hypothesis. Our Lean statement
  matches.
* Currently has `sorry`; flagged in the file header.

### Sub-lemmas

All 7 manually-closed sub-lemmas pass tautology / identity / hypothesis
checks. `C_zero_eq_zero_iff_isPreconsistent` does real work
(connecting the `1 - Σ`-form and the `1 = Σ`-form).
`αPoly_explicitEuler` and friends are sanity / non-vacuity witnesses.

## Dead ends

None this cycle. The §410 sign convention took some hand
verification (explicit Euler with various conventions) but
converged once I matched the planner's encoding to the textbook
proof's `Cⱼ` formula via direct Taylor expansion.

## Discovery

* **§410 sign convention.** With our `α 0 = -1` normalisation,
  Butcher's §410 polynomial encoding is
  `αPoly(M) = 1 - Σᵢ M.α (i.succ) z^(i+1)`. The sign is dictated
  by (410c): `α(1) = 1 - Σ M.α i.succ` matches `C M 0` in the
  preconsistency identity. Future §410B/C/D cycles must keep
  this convention.
* **PowerSeries.coeff API.** Modern Mathlib uses
  `(PowerSeries.coeff (R := ℝ) j) f` (R implicit), not
  `PowerSeries.coeff ℝ j f`. The earlier-form syntax produces an
  application-type-mismatch error at parse time.
* **`Polynomial.aeval` over `PowerSeries ℝ`.** Works directly
  via the `Algebra ℝ (PowerSeries ℝ)` instance. To "substitute
  exp(-z) into a polynomial" we just write
  `(Polynomial.aeval expNegPS) (αPoly M)`. This avoids needing
  `PowerSeries.evalNegHom` / `PowerSeries.exp` separately — and
  sidesteps the `Algebra ℚ ℝ` requirement of `PowerSeries.exp ℝ`
  by defining `expNegPS` from scratch.
* **Generating-function approach validated**. By hand-verification
  with explicit Euler, the j-th coefficient of
  `αPoly(M)(exp(-z)) - z βPoly(M)(exp(-z))` is exactly the
  Butcher closed-form Cⱼ. This means thm:410A is mechanical
  (no Taylor's theorem needed in Ch.3 — it's a pure formal
  power-series identity).

## Suggested next approach

For cycle 074 (or whichever cycle picks up §410 next):

1. **Close `thm_410A`** by reducing to per-monomial coefficient
   computations. Steps:
   * Push `Polynomial.aeval expNegPS` through `αPoly M = 1 - Σ`
     via `map_sub` / `map_sum` (algebra-hom properties).
   * Push `PowerSeries.coeff j` through the resulting sum via
     `LinearMap.map_sub` / `LinearMap.map_sum`.
   * For each monomial `Polynomial.C c * X^m`, use
     `Polynomial.aeval_C` and `Polynomial.aeval_X_pow` (or
     similar Mathlib lemmas) to reduce
     `aeval expNegPS (C c * X^m)` to `c • expNegPS^m`.
   * Compute `coeff j (expNegPS^m) = (-m)^j / j!` — this is the
     key non-trivial step, which would require either
     a direct induction on `m` (since `expNegPS^0 = 1`,
     `expNegPS^(m+1) = expNegPS * expNegPS^m`) or a
     `PowerSeries.rescale` correspondence.
   * Match the result to `C M j` via the case split on `j = 0`
     vs `j ≥ 1`.
2. **Open `thm:410B`** (the order condition: `α(exp(z)) +
   z β(exp(z)) = O(z^{p+1}) ↔ method has order p`). This needs:
   * Re-expressing `α(exp(z))` (note: `+z` instead of `-z`) —
     can use `evalNegHom` to swap `exp(-z) ↔ exp(z)`.
   * A definition of "order p" — likely `∀ j ≤ p, C M j = 0`
     (matches Butcher (410b) interpretation).
   * The `O(z^{p+1})` ↔ `∀ j ≤ p, coeff j = 0` correspondence —
     standard formal-power-series fact.
3. **Connect §410 to existing §404 infrastructure**. We already
   have `C_zero_eq_zero_iff_isPreconsistent`. Add
   `C_one_eq_zero_iff_isConsistent` (using def:404B
   `IsConsistent`) — the `j = 1` case relates to (404b)
   `Σ i α_i = Σ β_i` (after sign reconciliation).
4. **Backup**: if §410B/C/D stall, pivot to **`thm:431A`**
   (Schur stability criterion, §431) — zero transitive dependencies,
   self-contained, needs Rouché's theorem.

If Aristotle returns proofs for the helpers, incorporate them
directly into `Section410.lean` (or into a new
`Section410Helpers.lean` if the file becomes too large).

## Aristotle results (pending — to be filled after 30-min check)

Project ID: `503ca4f4-87fe-421a-803d-20db5b4ab1aa`
Submitted: 2026-05-02 15:43:28 UTC
File: `.prover-state/aristotle_submissions/cycle_073/section410_helpers.lean`

5 sub-lemmas: `αPoly_natDegree_le`, `βPoly_natDegree_le`,
`expNegPS_coeff`, `coeff_aeval_C_X_pow`, `thm_410A_zero`.

(Updated below after the 30-minute check.)
