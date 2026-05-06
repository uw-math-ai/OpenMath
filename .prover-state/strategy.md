# Cycle 167 Strategy

## Context (carry-over from cycle 166)

Cycle 166 shipped Path 3 fallback for thm:454A:
* `LinearMultistepMethod.IsAStable` predicate (boundary-locus form,
  axiom-clean).
* `aeval_αPoly_eq` / `aeval_βPoly_eq` bridging lemmas (§410 polynomial
  form ↔ §451 vector form, axiom-clean).
* `vanW`, `vanW₁` Vandermonde test vectors.
* `explicitEulerLMM_not_isAStable` refutability witness (axiom-clean).

What stalled: `algebraic_identity_454A` (the §451e quadratic-form
identity). Direct proof unfolded `M.gMatrix`, `gTopLeft`,
`gBottomRight` simultaneously and manipulated nested dependent
if-then-else under `Fin.sum_univ_castSucc` / `Fin.sum_univ_succ`.
Lean elaboration hung 10+ min without output across two retries.
Root cause: `simp` blows up on the unfolded matrix entries inside a
single proof body.

Aristotle batch (project `89e8a962-b3eb-4f7d-b397-c77bf18773d4`) was at
11% when cycle 166 ended.

Sorry count: **0**. Path A from
`.prover-state/issues/thm_454A_stage_2_3_stall.md` is the recommended
closure path.

## Priority order (descending)

### Priority 1 — Aristotle single-poll

Run `mcp__aristotle__get_status` ONCE on
`89e8a962-b3eb-4f7d-b397-c77bf18773d4`. **DO NOT re-poll.** Three
outcomes:

* **COMPLETE with proofs**: extract via `mcp__aristotle__extract_result`.
  If a clean proof of `algebraic_identity_454A` or
  `gStable_isAStable` arrives, paste it into `Section454.lean` and
  validate with `lake env lean OpenMath/Chapter4/Section454.lean`.
  If accepted, also pull the dependent witnesses
  (`bdf2LMM_isAStable`) — but only if the dependency chain is
  self-consistent. **Verify axioms** on every accepted theorem with
  `lean_verify` (target `[propext, Classical.choice, Quot.sound]`
  exactly). Do NOT accept proofs that introduce other axioms.
* **IN_PROGRESS / FAILED**: cancel via
  `mcp__aristotle__cancel_project` (free the slot — cycle 166's
  retrospective shows the prover unlikely to land at 11% after 35+
  min) and proceed to Priority 2 manually.
* **Returned only partial proofs** (e.g. `gTopLeft_quadForm_eq` but
  not the others): incorporate the partial(s), then proceed to
  Priority 2 with the remaining sub-goals.

After incorporating Aristotle output, if the cycle's deliverable bar
is met (see Priority 4), STOP and write task results. Otherwise
continue.

### Priority 2 — Factor quadratic-form lemmas as standalone named theorems

This is the cycle 166 stall remediation per
`thm_454A_stage_2_3_stall.md` Path A. **The key insight is to give
each quadratic-form computation its own proof obligation in its own
top-level theorem, so Lean elaborates them independently.** Inline
proofs in cycle 166 hung because the two computations interact
through nested if-then-else expansion in a single proof body.

Add these as standalone theorems **directly in `Section454.lean`**
(not in `Section451.lean` — keeping new bridging-only material in
the §454 file simplifies imports and per-file `lake env lean`
validation).

Place them after `aeval_βPoly_eq` and before any A-stability
witness, in the existing `OpenMath.Chapter4.Section454` namespace.

#### Step 2a — `gTopLeft_quadForm_eq`

Recommended signature (polymorphic `R`):

```lean
theorem gTopLeft_quadForm_eq {R : Type*} [CommRing R] [StarRing R]
    {k : ℕ} (G : Matrix (Fin k) (Fin k) R) (W : Fin (k + 1) → R) :
    star W ⬝ᵥ (gTopLeft G *ᵥ W) =
      star (fun i : Fin k => W i.castSucc) ⬝ᵥ
        (G *ᵥ (fun i : Fin k => W i.castSucc)) := by
  ...
```

This requires `gTopLeft` to be polymorphic in `R` (it currently
specialises to `ℝ` in `Section451.lean:68`). **Refactor**
`gTopLeft` and `gBottomRight` to take a `Matrix (Fin k) (Fin k) R`
for any `R` with zero. Same for `gMatrix` if needed (likely yes,
since cycle 168 will instantiate `gMatrix` over ℂ).

The refactor is ~5 line edits each (replace `ℝ` with `R`, add
`[Zero R]`). Verify the existing §451 BDF2 witnesses still typecheck
(they instantiate at `R := ℝ` definitionally — should be `rfl`-clean).

**Proof body** (the actual stall point):

Strategy: `Matrix.dotProduct` unfolds to
`Σ i, star (W i) * (gTopLeft G *ᵥ W) i`. For `i = Fin.last k`, the
`gTopLeft` row is identically zero, so the term vanishes. For
`i = i'.castSucc` with `i' : Fin k`, the row matches `G i'`'s
mulVec of the truncated `W`.

Write the proof in *small named sub-lemmas* in `private` scope to
avoid the cycle 166 elaboration blowup:

1. `gTopLeft_apply_castSucc` — show
   `gTopLeft G i.castSucc j.castSucc = G i j` for `i j : Fin k`.
   Proof: unfold `gTopLeft, Matrix.of_apply`, `dif_pos` on
   `i.castSucc.val < k ∧ j.castSucc.val < k` (which holds via
   `Fin.castSucc_lt_last` + `Fin.is_lt`-style facts).
2. `gTopLeft_apply_last_row` — show
   `gTopLeft G (Fin.last k) j = 0` for any `j : Fin (k+1)`.
   Proof: `dif_neg` on `(Fin.last k).val = k`, contradicting
   `< k`.
3. `gTopLeft_apply_last_col` — show
   `gTopLeft G i (Fin.last k) = 0` for any `i : Fin (k+1)`.
   Symmetric to step 2.
4. `gTopLeft_mulVec_castSucc` — show
   `(gTopLeft G *ᵥ W) i.castSucc = G *ᵥ (fun j => W j.castSucc) i`.
   Proof: unfold `mulVec`, sum over `Fin (k+1)` using
   `Fin.sum_univ_castSucc`, the last term vanishes via
   `gTopLeft_apply_last_col`, the rest matches via
   `gTopLeft_apply_castSucc`.
5. `gTopLeft_mulVec_last` — show
   `(gTopLeft G *ᵥ W) (Fin.last k) = 0`. Proof: unfold `mulVec`,
   each row entry vanishes via `gTopLeft_apply_last_row`,
   `Finset.sum_const_zero`.
6. **Main theorem** `gTopLeft_quadForm_eq`: unfold `dotProduct` on
   LHS, split sum via `Fin.sum_univ_castSucc`, apply
   `gTopLeft_mulVec_castSucc` and `gTopLeft_mulVec_last`, simplify
   `star _ * 0 = 0`, conclude by `dotProduct` reverse-unfold on RHS.

Each sub-lemma should be ≤ 5 lines. **Validate each one
individually** with `lake env lean` (or `lean_verify`) before
proceeding to the next. If a sub-lemma takes > 60 s to elaborate,
something is wrong — pause and decompose further.

#### Step 2b — `gBottomRight_quadForm_eq`

Symmetric to Step 2a, but the boundary case is `i = 0`
(`Fin.castSucc` becomes `Fin.succ`, `Fin.last` becomes `0`).

```lean
theorem gBottomRight_quadForm_eq {R : Type*} [CommRing R] [StarRing R]
    {k : ℕ} (G : Matrix (Fin k) (Fin k) R) (W : Fin (k + 1) → R) :
    star W ⬝ᵥ (gBottomRight G *ᵥ W) =
      star (fun i : Fin k => W i.succ) ⬝ᵥ
        (G *ᵥ (fun i : Fin k => W i.succ)) := by
  ...
```

Six private sub-lemmas mirroring Step 2a:
1. `gBottomRight_apply_succ` — `gBottomRight G i.succ j.succ = G i j`.
2. `gBottomRight_apply_zero_row` — `gBottomRight G 0 j = 0`.
3. `gBottomRight_apply_zero_col` — `gBottomRight G i 0 = 0`.
4. `gBottomRight_mulVec_succ` — analogous.
5. `gBottomRight_mulVec_zero` — analogous.
6. Main theorem using `Fin.sum_univ_succ` (head-split, opposite of
   `Fin.sum_univ_castSucc`).

#### Step 2c — Validate

After Steps 2a + 2b land, run:
* `lake env lean OpenMath/Chapter4/Section454.lean` — confirm exit 0
  within 3 min.
* `lake env lean OpenMath/Chapter4/Section451.lean` — regression
  guard for the polymorphism refactor (BDF2 witnesses must still
  build).
* `lake build OpenMath.Chapter4.Section451 OpenMath.Chapter4.Section454`
  — full elaboration + .olean caching before `#print axioms`.
* `lean_verify
  OpenMath.Chapter4.Section454.gTopLeft_quadForm_eq` and
  `OpenMath.Chapter4.Section454.gBottomRight_quadForm_eq` —
  confirm axioms are exactly `[propext, Classical.choice, Quot.sound]`.

**Deliverable bar for Priority 2**: Steps 2a + 2b axiom-clean in
`Section454.lean`, all six private sub-lemmas + two main theorems.

### Priority 3 — Stretch: `algebraic_identity_454A` (only if > 30 min spare)

If Priority 2 lands cleanly with > 30 min remaining, attempt the
identity. Statement (over ℂ, using `gMatrix` polymorphised over R):

```lean
theorem algebraic_identity_454A {k : ℕ}
    (M : LinearMultistepMethod k) (G : Matrix (Fin k) (Fin k) ℂ)
    (w : ℂ) :
    star (vanW w) ⬝ᵥ
        ((M.gMatrix (R := ℂ) G * 0 + ...) *ᵥ vanW w) -- (placeholder; finalise to use Complex-lifted alphaVec/betaVec)
      = ...
```

(Exact statement: see Butcher §454 proof p. 387 around equation
(454a). The identity says `star W · M(G) · W = 2 α(w) β(w) - (1 - |w|²) star W₁ · G · W₁`.)

**Proof recipe:**
1. Unfold `gMatrix = vecMulVec α β + vecMulVec β α - gTopLeft G + gBottomRight G`.
2. Distribute `*ᵥ W` over the four-term sum, then `star W ⬝ᵥ` over
   the four-term sum.
3. The two `vecMulVec` terms each become a product of dot products
   (use `Matrix.dotProduct_vecMulVec` or unfold). Apply
   `aeval_αPoly_eq` and `aeval_βPoly_eq` (cycle 166) to identify
   these with `aeval w (αPoly M)` and `aeval w (βPoly M)`. (Note
   that `vanW i = w^i.val` exactly, so the dot product
   `α-vec ⬝ᵥ vanW = Σ alphaVec j · w^j` matches.)
4. The `gTopLeft G` term collapses via `gTopLeft_quadForm_eq` to a
   quadratic form on the truncated Vandermonde
   `(fun i => vanW (i.castSucc)) = (fun i : Fin k => w^i.val) = vanW₁ w`.
5. The `gBottomRight G` term collapses via
   `gBottomRight_quadForm_eq` to a quadratic form on the *shifted*
   Vandermonde `(fun i => vanW (i.succ)) = (fun i : Fin k => w^(i+1))
   = w • vanW₁ w` (since `w^(i+1) = w * w^i`).
6. Pull `w` out of the `gBottomRight` quadratic form via
   `Matrix.dotProduct_smul` / linearity in both arguments — the
   `star (w • _) ⬝ᵥ (G *ᵥ (w • _)) = (star w) * w * (star _ ⬝ᵥ (G *ᵥ _))
   = ‖w‖² * star W₁ ⬝ᵥ (G *ᵥ W₁)`.
7. Combine: `gBottomRight - gTopLeft` quadratic forms give
   `(‖w‖² - 1) * (G-quadratic-form on W₁)`, i.e.
   `−(1 − ‖w‖²) * (G-quadratic-form on W₁)`, matching the textbook
   RHS.

**If this stretch step times out**: revert it cleanly (delete the
theorem statement and its proof body; do NOT leave a sorry). Ship
Priority 2 only. Do NOT block on this.

### Priority 4 — Cycle deliverable bar

Minimum bar (positive score): Priority 1 incorporated + Priority 2
shipped (six sub-lemmas + two main theorems axiom-clean). This
unblocks cycle 168 to assemble `algebraic_identity_454A` and
`gStable_isAStable` from named pieces.

Do NOT attempt Priority 3 unless Priority 2 has > 30 min spare. The
cycle 166 retrospective is clear: monolithic proofs of the §454e
identity stall Lean elaboration. Build incrementally.

## What NOT to try

* **Do NOT inline `algebraic_identity_454A` in `Section454.lean`
  with a single `simp [...] ; ring` or
  `simp only [...] ; Fin.sum_univ_castSucc ; dif_neg` body.** This
  is exactly what stalled cycle 166 — Lean's elaboration of nested
  dependent if-then-else over `Fin (k+1) × Fin (k+1)` blows up. Use
  the named sub-lemma decomposition in Priority 2.
* **Do NOT use `decide` or `fin_cases` at general `k`.** They only
  fire at concrete `k`. The identities are universally quantified
  over `k : ℕ`.
* **Do NOT raise `maxHeartbeats`** above 200000 (CLAUDE.md). If a
  sub-lemma exceeds default heartbeats, decompose further.
* **Do NOT skip the polymorphism refactor.** Trying to state
  `gTopLeft_quadForm_eq` over ℝ first and lift to ℂ later via
  `.map (algebraMap ℝ ℂ)` introduces type-coercion churn that will
  recreate the elaboration blowup downstream. Polymorphic `R` from
  the start is cleaner. (Backup B1 below addresses what to do if
  the refactor stalls.)
* **Do NOT touch `Section451.lean`'s BDF2 witness or
  `bdf2_gMatrix_eq_smul_vecMulVec` proof.** They are axiom-clean
  and their § 451 namespace proof structure is independent. Only
  refactor the `gTopLeft`/`gBottomRight`/`gMatrix` *definitions* to
  be polymorphic; the BDF2 lemmas instantiate at `R := ℝ` and
  should rebuild automatically.
* **Do NOT re-poll Aristotle.** Single-poll discipline per CLAUDE.md.
  If cycle 166's project is still IN_PROGRESS at < 30%, cancel it.
* **Do NOT re-attempt cycle 166's stalled monolithic proof** verbatim.
  The approach is dead.
* **Do NOT introduce `axiom` or `constant`** to bypass the stall.
* **Do NOT pivot to a different entity.** thm:454A is the active
  multi-cycle target; cycles 166–169 are the planned arc per the
  issue file.
* **Do NOT add `[Star R]` or `[StarRing R]` instances to the
  refactored `gTopLeft`/`gBottomRight` definitions** — they only
  need `[Zero R]` to be defined. The star structure enters in the
  *quadratic-form lemmas* (where `star W` is taken). Keep the
  definition typeclass-light to maximise generality.

## Faithfulness checks

For every new `theorem` introduced this cycle, run the checklist in
CLAUDE.md §"Pre-Commit Faithfulness Checklist":

* For each of the six private sub-lemmas + two quadratic-form
  identities: tautology check, identity check, hypothesis-strength
  check, absent-theorem check.
* For the polymorphism refactor of `gTopLeft`/`gBottomRight`
  (and possibly `gMatrix`): no semantic change. Ensure
  `gTopLeft (R := ℝ)` is *definitionally* equal to the old
  `gTopLeft`. The BDF2 witness in `Section451.lean` must still
  typecheck without alteration. Run
  `lake env lean OpenMath/Chapter4/Section451.lean` after the
  refactor to confirm zero regression.

The two main theorems are bridging lemmas, not entities. They are
mathematically content-bearing (`gTopLeft G`'s quadratic form
factoring through `Fin k → R`'s truncation is the genuine §454e
algebraic content) but do not need a `lean_status.json` row update.

## Build & verification commands

* `lake env lean OpenMath/Chapter4/Section454.lean` — primary
  validation. Should exit 0 within 3 min.
* `lake env lean OpenMath/Chapter4/Section451.lean` — regression
  guard for the polymorphism refactor.
* `lake build OpenMath.Chapter4.Section454` (after first
  `lake env lean` succeeds) — full elaboration + .olean caching
  before running `#print axioms`.
* `lean_verify` on each new theorem — confirm axioms are exactly
  `[propext, Classical.choice, Quot.sound]`.

PATH note (from CLAUDE.md): if `lake` hangs, check that
`/tmp/lake-bin:/tmp/lean4-toolchain/bin` is first in PATH. The
GPFS-hosted toolchain causes multi-minute hangs.

## Task results expectations

Write `.prover-state/task_results/cycle_167.md` with:
* What landed (which sub-lemmas closed, axiom-clean).
* If Aristotle returned anything, document the proofs that were
  incorporated.
* If Priority 3 was attempted, document whether it landed or was
  reverted.
* Faithfulness check entries for each new theorem.
* Suggested next approach for cycle 168 (the final assembly into
  `algebraic_identity_454A` and `gStable_isAStable`).

Update `.prover-state/issues/thm_454A_stage_2_3_stall.md` with a
"Cycle 167 update" section noting which Stage 2 sub-lemmas landed
and whether the original "Path A" plan needs revision based on what
Lean actually did this cycle.

Do NOT flip the `plan.md` row for thm:454A. Status remains
unformalized; cycle 167 builds the stepping stones.

## Backup plan (Priority 2 stalls)

If the polymorphism refactor of `gTopLeft`/`gBottomRight` causes
breakage in `Section451.lean` that takes > 30 min to fix:

* **Backup B1**: keep `gTopLeft`/`gBottomRight` ℝ-only. Define
  parallel ℂ-valued versions inline in `Section454.lean`:
  ```lean
  private def gTopLeftC {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
    Matrix.of fun i j =>
      if h : i.val < k ∧ j.val < k then
        G ⟨i.val, h.1⟩ ⟨j.val, h.2⟩
      else 0
  ```
  State the quadratic-form lemmas over ℂ directly. Acceptable but
  introduces redundancy. Cycle 168 can revisit the polymorphism
  question separately.
* **Backup B2**: ship only `gTopLeft_quadForm_eq` Step 2a and its
  five private sub-lemmas this cycle. Defer
  `gBottomRight_quadForm_eq` to cycle 168. Still positive forward
  motion; one quadratic-form lemma + sub-lemmas is half the work
  cycle 168 would need to do.
* **Backup B3**: if a sub-lemma proof itself stalls (the named
  decomposition is *supposed* to avoid this, but if `simp` still
  blows up on the dependent-`if` unfolding), Aristotle-batch the
  stalled sub-lemma in a fresh project. Use cycle 167 to land
  whichever sub-lemmas didn't stall; rely on Aristotle return for
  cycle 168.

In all backup paths, the cycle is positive-score if **at least one**
of {`gTopLeft_quadForm_eq`, `gBottomRight_quadForm_eq`} lands
axiom-clean, OR Aristotle's batch returned a usable contribution.
