# Cycle 138 Strategy — Open §550 with `thm:550A` infrastructure + n=1 verification

## Context (don't repeat)

- Cycle 137 closed `def:520F` non-vacuity with two negative L-stability witnesses.
- The non-vacuity strengthening cadence (cycles 128–137) has run its course
  for `def:520E`/`def:520F`/`def:525A`/`def:542A`/`def:551A`. **Pivot to a
  real theorem this cycle.**
- No pending Aristotle results.
- The cycle 137 worker explicitly suggested three options. After audit:
  - `thm:551B` — depends on `thm:550A` AND `thm:550B`. Don't try yet.
  - `thm:521B` — requires polynomial complexity-sequence representation
    of `stabilityFunction` and contour-integral arguments. Per the
    `def:521A` docstring (`Section520.lean:658-670`), this representation
    is **deferred** as multi-cycle infrastructure. Don't try.
  - `thm:550A` — pure linear algebra, foundation for both §551 and §553.
    **This is the cycle 138 target.**

## Primary target: `thm:550A` (Doubly companion matrices)

Textbook statement (`entities/thm_550A.json`, Butcher p. 457): for the
**doubly companion matrix** `X` built from coefficients
`α₁,…,αₙ, β₁,…,βₙ` per equation (550a),

```
X = [[-α₁, -α₂, ..., -α_{n-1}, -αₙ - βₙ],
     [1, 0, ..., 0, -β_{n-1}],
     [0, 1, ..., 0, -β_{n-2}],
     ...,
     [0, 0, ..., 1, -β₁]]
```

with `α(z) := 1 + α₁z + … + αₙ zⁿ` and `β(z) := 1 + β₁z + … + βₙ zⁿ`,
the characteristic polynomial of `X` and `det(I − zX)` satisfy

```
det(I − zX) = α(z)·β(z) + O(z^{n+1})        as z → 0  in ℂ.
```

(The "reciprocal" identity `1 + γ₁z + γ₂z² + … + γₙ zⁿ = det(I − zX)`
where `γᵢ` are the charpoly coefficients is a generic matrix fact —
not specific to doubly companion matrices.)

## Cycle 138 deliverable

A new file `OpenMath/Chapter5/Section550.lean` with:

1. **The doubly companion matrix definition.**
2. **Verification at `n = 1`.**
3. **Sorry-first scaffold for general `n`.**
4. **Issue file documenting the general-`n` deferral.**
5. **`OpenMath/Chapter5.lean` updated** to `import OpenMath.Chapter5.Section550`.

This is a "structure + 1 closure" cycle. The `n = 1` closure is a
**genuine** witness (textbook identity discharged for the smallest
case), not vacuous.

### Step 1 — Create the file (~30 min)

Create `OpenMath/Chapter5/Section550.lean` with this header skeleton.
Open under namespace `OpenMath.Chapter5.Section550` (new namespace —
do NOT reuse `Section510` here; §550 is its own narrative thread).

```lean
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Butcher §550 — Doubly companion matrices (Theorem 550A)
…
-/

namespace OpenMath.Chapter5.Section550

open Complex Asymptotics
```

### Step 2 — Define `doublyCompanionMatrix` (~50 LOC)

Define over `ℂ` directly (the textbook works over ℂ via eigenvalue
analysis; using `ℂ` from the start avoids a later complexification
detour). The cleanest formulation uses index-by-index entries — do
NOT try to use `Matrix.companion` from Mathlib (it's the standard
companion matrix, not the doubly version).

```lean
/-- **Doubly companion matrix** (550a). Indexed by `Fin n × Fin n`,
where `n ≥ 1`. The entries follow the textbook layout:
* row 0 holds `−α_{j+1}` for j < n−1, and `−αₙ − βₙ` at column n−1
* rows 1..n−1 hold a sub-diagonal `1` (i.e., `X[i, i−1] = 1`) and a
  last-column entry `−β_{n−i}`.
* All other entries are `0`.

We encode the coefficients `α, β : Fin n → ℂ` as the vectors
`(α₁,…,αₙ)` and `(β₁,…,βₙ)` (Fin-indexed, so `α k` means `α_{k+1}`
in textbook indexing). -/
def doublyCompanionMatrix {n : ℕ} (α β : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j =>
  if i.val = 0 then
    if j.val = n - 1 then
      -α ⟨n-1, by omega⟩ - β ⟨n-1, by omega⟩
    else
      -α j  -- row 0, columns 0..n-2: `-α_{j+1}` (textbook 1-indexed)
  else if i.val = j.val + 1 then
    1  -- sub-diagonal
  else if j.val = n - 1 then
    -β ⟨n - i.val, by omega⟩  -- last column entries
  else
    0
```

**Faithfulness check**: the textbook indexes α and β starting at 1;
our `Fin n` indexes start at 0, so `α 0` corresponds to textbook
`α₁`, `α (n−1)` corresponds to textbook `αₙ`. Document this in the
docstring prominently.

**Edge cases**: at `n = 0`, `Fin 0 → ℂ` is the empty function and
the matrix is the empty (0×0) matrix; the theorem becomes vacuous
(`O(z^1)` is just `IsBigO _ id`, true of the constant function 0).
At `n = 1`, `i.val = 0 = j.val` and `j.val = n - 1 = 0`, so the
single entry is `-α 0 - β 0` (which matches the textbook (550a)
specialised at n=1: `[[-α₁ - β₁]]`).

**Sanity helper**: prove
`doublyCompanionMatrix_one_eq : doublyCompanionMatrix α β = !![-α 0 - β 0]`
for `n = 1`. Use `Matrix.ext` + `fin_cases` + `decide` or `simp`.

### Step 3 — State `thm:550A` and prove the n=1 case (~80 LOC)

```lean
/-- The polynomial `α(z) = 1 + α₁z + … + αₙ zⁿ` (textbook indexing). -/
def alphaPoly {n : ℕ} (α : Fin n → ℂ) (z : ℂ) : ℂ :=
  1 + ∑ i : Fin n, α i * z ^ (i.val + 1)

/-- The polynomial `β(z) = 1 + β₁z + … + βₙ zⁿ`. -/
def betaPoly {n : ℕ} (β : Fin n → ℂ) (z : ℂ) : ℂ :=
  1 + ∑ i : Fin n, β i * z ^ (i.val + 1)

/-- **Theorem 550A** — for the doubly companion matrix `X` with
coefficient vectors `α, β`,
`det(I − zX) = α(z)·β(z) + O(z^{n+1})` as `z → 0`.

Butcher §550 Theorem 550A, p. 457. -/
theorem doublyCompanionMatrix_det_factorization
    {n : ℕ} (α β : Fin n → ℂ) :
    Asymptotics.IsBigO (nhds (0 : ℂ))
      (fun z : ℂ =>
        (1 - z • doublyCompanionMatrix α β).det
          - alphaPoly α z * betaPoly β z)
      (fun z : ℂ => z ^ (n + 1)) := by
  sorry  -- see issue thm_550A_general_n.md
```

Then prove the **n = 1 specialization** as a witness:

```lean
/-- `thm:550A` at `n = 1`: with single coefficients α₁, β₁,
`det(I − zX) = 1 + (α₁ + β₁)z`, while `α(z)·β(z) = 1 + (α₁+β₁)z + α₁β₁z²`,
so the difference is `−α₁β₁ z²`, which is `O(z²) = O(z^{1+1})`. -/
theorem doublyCompanionMatrix_det_factorization_n_one
    (α β : Fin 1 → ℂ) :
    Asymptotics.IsBigO (nhds (0 : ℂ))
      (fun z : ℂ =>
        (1 - z • doublyCompanionMatrix α β).det
          - alphaPoly α z * betaPoly β z)
      (fun z : ℂ => z ^ 2) := by
  -- (1 - zX).det = 1 - z · (-α 0 - β 0) = 1 + (α 0 + β 0) z
  -- α(z)·β(z) = (1 + α 0 · z)(1 + β 0 · z) = 1 + (α 0 + β 0) z + (α 0)(β 0) z²
  -- difference = -(α 0)(β 0) z²
  have h_diff : ∀ z : ℂ,
      (1 - z • doublyCompanionMatrix α β).det
        - alphaPoly α z * betaPoly β z
        = -(α 0 * β 0) * z ^ 2 := by
    intro z
    rw [doublyCompanionMatrix_one_eq]
    simp only [alphaPoly, betaPoly, Fin.sum_univ_one]
    -- Reduce 1 - z • !![-α 0 - β 0] to !![1 + z * (α 0 + β 0)] then
    -- use Matrix.det_fin_one.
    have : (1 - z • !![-α 0 - β 0] : Matrix (Fin 1) (Fin 1) ℂ)
            = !![1 + z * (α 0 + β 0)] := by
      ext i j; fin_cases i; fin_cases j
      simp [Matrix.smul_apply, sub_eq_add_neg]; ring
    rw [this, Matrix.det_fin_one]
    simp; ring
  -- Use h_diff to bound the LHS by `‖α 0 * β 0‖ · ‖z^2‖`.
  refine Asymptotics.IsBigO.of_bound ‖α 0 * β 0‖ ?_
  filter_upwards with z
  rw [h_diff]
  rw [Complex.norm_neg, Complex.norm_mul, Complex.norm_pow]
  ring_nf
  rfl  -- or `simp` if ring_nf leaves a trivial residue
```

**Verify with `lean_multi_attempt`** at every `simp`/`ring`/`refine`
boundary before stitching the proof. The endgame can be sensitive
to elaboration order. Three viable backup endgames if the
`IsBigO.of_bound` route doesn't fire cleanly:

1. `simp only [h_diff]; exact (isBigO_const_mul_self _ _ _).neg_left`-style.
2. Build `IsBigO` from `Filter.eventually_le` directly via
   `‖f z‖ ≤ ‖α 0 * β 0‖ * ‖z^2‖`.
3. Prove the function `equals` `fun z => -(α 0 * β 0) * z^2`
   (which is automatic from `h_diff`), then close via
   `Asymptotics.isBigO_const_mul_self` followed by `congr`.

If `lean_multi_attempt` shows none of these close, **decompose
further** into a sub-lemma `f z = g z * z^2` for an appropriate
constant `g z`, and feed that to `Asymptotics.IsBigO.const_mul_left`
plus `Asymptotics.isBigO_refl`.

### Step 4 — Update plumbing (~15 min)

* Add `import OpenMath.Chapter5.Section550` to `OpenMath/Chapter5.lean`.
  (Note: `OpenMath/Chapter5.lean` is currently missing imports for
  `Section514`, `Section515`, `Section525` — DO NOT add those; they
  may be intentionally deferred from the chapter's hub. Only add
  `Section550`. If lake build complains about a missing transitive
  dep, leave the new file out of the hub and import it directly
  wherever needed; document in the cycle results.)
* Update `extraction/formalization_data/lean_status.json` for
  `thm:550A`: status `partial`, `lean_file` =
  `OpenMath/Chapter5/Section550.lean`, `lean_symbol` =
  `OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization`,
  `cycle` = 138, plus a new annotation pointing to the
  `_n_one` witness theorem.
* Update `plan.md` Chapter 5 row for `thm:550A`: `[ ]` → `[~]` with
  a note "n=1 closed; general n deferred (issue
  `thm_550A_general_n.md`)".

### Step 5 — Document the general-n deferral

Write `.prover-state/issues/thm_550A_general_n.md` documenting:

* The textbook proof (eigenvalue density argument): distinct,
  non-zero eigenvalues form a dense set in coefficient space;
  charpoly coefficients are continuous; reduce to the dense case
  via direct eigenvalue calculation, then extend by continuity.
* Why the general case is deferred: density-based argument requires
  several Mathlib pieces in concert (continuity of charpoly
  coefficients in matrix entries, density of "distinct eigenvalues"
  in coefficient space, identity-of-analytic-functions extension by
  continuity). Each is available in Mathlib, but the assembly is
  multi-cycle.
* Possible solutions:
  (i) Direct cofactor-expansion of `det(I − zX)` for general `n` —
      compute the determinant entry-by-entry by exploiting the
      sparse structure of `X`. Tedious (~150 LOC) but plausible
      single-cycle work for cycle 139 if Aristotle batch is
      inconclusive.
  (ii) Eigenvalue-density argument (the textbook's path). ~300 LOC
       across 2–3 cycles.
  (iii) An induction on `n` via row-reduction. The doubly companion
        matrix has a recursive structure (the `(n−1) × (n−1)`
        bottom-right block of `X` is itself a doubly companion
        matrix shifted down). This may be the cleanest; sketch it
        out in cycle 139.
* Cross-reference: blocks `thm:551B` (which uses `thm:550A` for the
  M(z) eigenvalue analysis).

### Step 6 — Aristotle batch (parallel to manual work)

Submit two jobs at the START of the cycle (so they run in the
background while you work on Steps 1–5):

* **Job A**: the general-`n` `doublyCompanionMatrix_det_factorization`
  theorem with the full `n = 1` proof shown as guidance, plus a
  reference to the textbook's eigenvalue-density argument in the
  prompt.
* **Job B**: a focused sub-lemma stating the polynomial identity
  *exactly* (not asymptotically):
  `(1 - z • doublyCompanionMatrix α β).det = alphaPoly α z * betaPoly β z + ∑ i ∈ Finset.Ioc n (2*n), (γ i) * z^i`
  for some coefficients `γ i` derivable from α and β. The asymptotic
  `IsBigO` then follows directly. This may be more amenable than
  Job A's full asymptotic form.

Don't poll Aristotle this cycle. Submit and proceed with manual work.

## What NOT to try

1. **Do NOT attempt `thm:551B` or `thm:550B`.** Both depend on `thm:550A`
   PLUS additional infrastructure (similarity transformation, Jordan
   block computations). One step at a time.

2. **Do NOT attempt general-`n` `thm:550A` manually this cycle.**
   The eigenvalue density argument is multi-cycle work. Sorry-first
   it and document. If by some chance Aristotle returns a clean proof
   in time (unlikely — typical IN_PROGRESS at 30 min poll is < 5%),
   incorporate it next cycle.

3. **Do NOT use `Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs`'s eigenvalue
   results to close the `n = 1` case.** They require the matrix to be
   over an algebraically closed field with extra structure. For `n = 1`,
   stick to direct `Matrix.det_fin_one` calculation.

4. **Do NOT introduce a `class` for "doubly companion structure".**
   A plain `def` returning a `Matrix` is sufficient. Adding a
   typeclass/predicate would be over-engineering.

5. **Do NOT pick a different target.** The worker may be tempted by
   "easier" non-vacuity strengthenings (e.g.
   `implicitMidpointGLM_hasStabilityOrder_two` for `def:521A`). The
   cadence has run its course — pivoting to a real theorem is the
   explicit cycle 138 mandate. If you hit a deadlock on `thm:550A`,
   write an issue file and commit a partial scaffold rather than
   pivoting away.

6. **Do NOT raise `maxHeartbeats`** above 200000. The `n = 1`
   determinant computation should not need any heartbeat tweaks.

7. **Do NOT touch Section520/Section525 work.** Cycle 137's commit
   `dd5e986` is the clean baseline.

8. **Do NOT reuse the `OpenMath.Chapter5.Section510` namespace** for
   the new §550 work. Each section deserves its own namespace; the
   `Section510` namespace was reused historically for §512–§520
   deliverables only because they all rest on the same
   `GeneralLinearMethod` structure. §550 is a new, distinct narrative
   (matrix-theoretic, not GLM-specific). Use `OpenMath.Chapter5.Section550`.

9. **Do NOT add `import` of `Section515`, `Section514`, or `Section525`
   to `OpenMath/Chapter5.lean`** as part of cycle 138 plumbing. Those
   are missing from the hub (verified — see `Grep` output) but the
   reason is unclear; touching them is out of scope.

## Success criteria

The cycle counts as a substantive forward step (score ≥ +1) if at
least three of the following are true:

- [ ] `OpenMath/Chapter5/Section550.lean` exists, builds clean
      (`lake env lean OpenMath/Chapter5/Section550.lean` exits 0).
- [ ] `doublyCompanionMatrix` is defined with correct entries
      (verify with `n = 1` and `n = 2` instances via `decide` or
      explicit `Matrix.ext`).
- [ ] `doublyCompanionMatrix_det_factorization_n_one` is closed
      axiom-clean (`#print axioms` returns
      `[propext, Classical.choice, Quot.sound]`).
- [ ] `doublyCompanionMatrix_det_factorization` is stated (sorry-first
      OK) with the IsBigO conclusion matching the textbook.
- [ ] `OpenMath/Chapter5.lean` imports `Section550`.
- [ ] `lean_status.json` and `plan.md` reflect `thm:550A` partial.
- [ ] `.prover-state/issues/thm_550A_general_n.md` documents the
      deferral.
- [ ] Aristotle batch submitted (project IDs recorded in
      `.prover-state/aristotle_submissions/cycle_138/README.md`).

A bonus closure of `n = 2`
`doublyCompanionMatrix_det_factorization_n_two` (specifically, the
textbook claim at `n = 2` with explicit α₁, α₂, β₁, β₂) would push
the cycle to score +2. The `n = 2` computation is ~80 LOC of direct
`det_fin_two` calculation; not required but feasible if Steps 1–5
finish under-budget.

## Pre-commit checklist

- `lake env lean OpenMath/Chapter5/Section550.lean` exits 0 (no errors,
  warnings only on the sorry'd general-n theorem).
- `lake env lean OpenMath/Chapter5.lean` exits 0 (after the import is
  added).
- `#print axioms OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization_n_one`
  returns `[propext, Classical.choice, Quot.sound]`.
- Tautology scanner returns 0 hits across `OpenMath/`.
- `extraction/formalization_data/lean_status.json` validates against
  the JSON schema (status is `partial`, `cycle` set to 138).
- `plan.md` row for `thm:550A` is `[~]` and references the new file +
  issue.
- Faithfulness check: cite `entities/thm_550A.json` in the docstring;
  confirm the Lean statement matches Butcher's (550a) layout exactly
  (NOT a paraphrase). Document the 0-vs-1 indexing convention
  prominently in the `doublyCompanionMatrix` docstring.

## Suggested cycle 139 plan (preview)

If cycle 138 lands the structure as described, cycle 139's options are:

1. **Close `n = 2` of `thm:550A`** as a stepping stone toward general
   `n` (still concrete computation; ~80 LOC).
2. **Incorporate Aristotle returns** for general `n` (if any).
3. **Manual general-`n` proof via cofactor expansion or induction**
   (~150 LOC over 1–2 cycles).
4. **Pivot to `thm:550B`** (similarity transformation) once `thm:550A`
   is fully closed — but `thm:550B` itself depends on (550d), the
   single-`n`-fold-eigenvalue case, so its formalisation has its own
   complexity.

Don't decide cycle 139 in cycle 138. Land the cycle 138 deliverables
and let the planner re-evaluate.
