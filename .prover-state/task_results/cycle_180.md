# Cycle 180 Results

## Worked on

- **Priority 0** (mandatory): independently verify the supervisor's
  cycle 176–179 "commit-not-reaching-repo" verdicts against actual git
  state.
- **Priority 1**: scope Phase C of `lem:441A` (`aᵢ ≥ 0` for `i ∈ [2, k]`)
  into a multi-cycle implementation plan.
- **Priority 2** (stretch): close the long-deferred BDF2 closed-form
  identity `bdf2LMM.aPoly = C(4/3) X + C(8/3) X²` via the
  `Polynomial.funext + ring` recipe suggested by the consultant in
  cycle 174.

## Approach

### Priority 0 — Phantom-verdict verification

Ran the four `git show --stat` commands from the strategy file:

```
$ git show --stat 0b171c9 -- OpenMath/Chapter4/Section441.lean
1 file changed, 209 insertions(+), 1 deletion(-)
$ git show --stat 1f0b21c -- OpenMath/Chapter4/Section441.lean
1 file changed, 143 insertions(+)
$ git show --stat 80a5865 -- OpenMath/Chapter4/Section441.lean
1 file changed, 62 insertions(+)
$ git show --stat 572f058 -- OpenMath/Chapter4/Section441.lean
1 file changed, 32 insertions(+)
```

All four return non-empty diffstats, contradicting the supervisor's
verdicts. Cumulative: +446 insertions to `OpenMath/Chapter4/Section441.lean`
across cycles 176–179.

Ran the landmark grep:

```
$ grep -n "ρPoly_no_real_root_gt_one|ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent|ρPoly_pos_on_Ioi_one|ρPoly_deriv_eval_one_pos_of_stable_preconsistent|aPoly_coeff_one_pos_of_stable_preconsistent" OpenMath/Chapter4/Section441.lean
504:theorem LinearMultistepMethod.ρPoly_no_real_root_gt_one
599:theorem LinearMultistepMethod.ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent
707:theorem LinearMultistepMethod.ρPoly_pos_on_Ioi_one
767:theorem LinearMultistepMethod.ρPoly_deriv_eval_one_pos_of_stable_preconsistent
913:theorem LinearMultistepMethod.aPoly_coeff_one_pos_of_stable_preconsistent
```

All five Phase B landmark theorems present. `Section441.lean` is 932
LOC at the cycle 180 start, 0 sorries, axiom-clean. Phase B of
`lem:441A` IS COMPLETE.

Recorded the diagnosis as a "Cycle 180 confirmation" entry in
`.prover-state/attempts.md` and a fresh issue file
`.prover-state/issues/phantom_commit_verdict_pattern.md`. The new
issue file:

- Documents the pattern across cycles 176–179.
- Quantifies the cumulative impact: 4 consecutive cycles unfixed.
- Cross-references prior occurrences (cycles 008/014/015/035/073/170)
  and the canonical diagnoses in `consultant_advice_cycle_009.md` §A
  and `consultant_advice_cycle_015.md` §B.
- Recommends concrete loop-maintainer follow-ups (diff-extraction
  audit, path-matching audit, prompt-builder propagation, hash
  collision check) with a one-liner reproducer command.
- Explicitly carves the worker-side action (verify, document,
  escalate; do NOT fix) from the loop-maintainer-side action (audit
  the supervisor prompt-builder).

### Priority 1 — Phase C scoping

Wrote `.prover-state/issues/lem_441A_phase_C_scoping.md` with all 5
sections required by the strategy:

- **§1** quotes Butcher's textbook proof (verbatim from
  `extraction/raw_text/ch04.txt:1998–2008`) and decomposes it into 5
  steps (Möbius bridge → left-half-plane root location → real
  factorisation → non-negative-coefficient closure → sign-consistency
  closure).
- **§2** lists the Mathlib hooks per step. Verifications partial
  (Lean MCP rate-limited mid-cycle); annotated each hook as
  `[CONFIRMED present]`, `[LIKELY present, verify]`, or
  `[LIKELY MISSING, build helper]`. Genuine gap candidates flagged:
  `Polynomial.roots_map_conj`-style real-coefficient-implies-conjugate-
  closed-roots and the conjugate-pair quadratic factor identity.
- **§3** phases the work into C.1 (Möbius bridge, 1–2 cycles, ~150
  LOC), C.2 (stability ⇒ left-half-plane, 1 cycle, ~80 LOC), C.3
  (real factorisation, 1–2 cycles, ~300 LOC, **highest risk**), C.4
  (closure, 1 cycle, ~50 LOC). Best-case 4 cycles, worst-case 6.
- **§4** assigns LOC, Mathlib risk (Phase C.3 highest), Aristotle
  suitability (Phase C.4 highest, Phase C.3 lowest), and alternative
  routes per phase (Möbius pointwise bypass for C.1; Schur-style
  detour for C.3 — itself blocked by `jordan_canonical_form_missing.md`;
  BDF2 direct evaluation as a Phase C.bypass for the canonical example).
- **§5** cross-references all sibling issues, the parent
  `lem_441A_alpha_prime_negative.md`, and the relevant Section441
  landmarks.

Concluded with a recommendation to the cycle 181 planner to start
with Phase C.1 (medium risk, bounded cycle count).

### Priority 2 — `bdf2LMM_aPoly_eq` closed form

Followed the consultant's suggested `Polynomial.funext + ring` recipe
from cycle 174:

1. Verified `Polynomial.funext` exists in Mathlib via `loogle` —
   signature `{R : Type u} [CommRing R] [IsDomain R] [Infinite R]
   {p q : Polynomial R} (ext : ∀ r, p.eval r = q.eval r) : p = q`.
   ℝ satisfies all instances.
2. First attempt: the strategy's verbatim recipe
   ```lean
   apply Polynomial.funext; intro x; unfold LinearMultistepMethod.aPoly
   simp only [bdf2LMM, Fin.sum_univ_two, Polynomial.eval_*, ...]; ring
   ```
   — failed: `simp only [bdf2LMM, ...]` exposed the `α` field as a
   raw `match Fin.succ 0 with ...` / `match Fin.succ 1 with ...`
   pattern that did not reduce, leaving the `Fin` match in `ring`'s
   target.
3. Fix: rewrite via `have h1 : bdf2LMM.α (Fin.succ 0) = 4/3 := rfl`
   and `have h2 : bdf2LMM.α (Fin.succ 1) = -1/3 := rfl` — `rfl`
   forces Lean to reduce the match to a numeric value at the type
   level. After `rw [h1, h2]`, the residue is purely arithmetic in
   `ℝ`, which `ring` closes.
4. Added two corollaries: `bdf2LMM_aPoly_coeff_two_eq = 8/3` and
   `bdf2LMM_aPoly_coeff_two_pos`. Both single-line via
   `rw [bdf2LMM_aPoly_eq]; simp` and `rw [bdf2LMM_aPoly_coeff_two_eq];
   norm_num`.

## Result

**SUCCESS** on all three priorities.

- **Priority 0**: independently verified that cycles 176–179 supervisor
  verdicts are false alarms; documented in `attempts.md` and the new
  `phantom_commit_verdict_pattern.md` issue file.
- **Priority 1**: shipped `lem_441A_phase_C_scoping.md` with all 5
  sections; cycle 181 planner has a complete blueprint for Phase C.
- **Priority 2**: shipped `bdf2LMM_aPoly_eq`, `bdf2LMM_aPoly_coeff_two_eq`,
  and `bdf2LMM_aPoly_coeff_two_pos` to `Section441.lean`, all
  axiom-clean (`[propext, Classical.choice, Quot.sound]`).

`Section441.lean` is now 974 LOC (was 932), 0 sorries, axiom-clean.

`#print axioms` output (verified at cycle end):

```
'OpenMath.Chapter4.Section441.bdf2LMM_aPoly_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter4.Section441.bdf2LMM_aPoly_coeff_two_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter4.Section441.bdf2LMM_aPoly_coeff_two_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake build OpenMath.Chapter4.Section441` succeeded after 271s.

## Faithfulness check

For each new theorem introduced this cycle:

### `bdf2LMM_aPoly_eq`

- **Source**: `extraction/formalization_data/entities/lem_441A.json`
  + Butcher §441 p. 375 (the textbook formula
  `a(z) = (1+z)^k − Σᵢ αᵢ(1+z)^{k-i}(1-z)^i` instantiated at
  `k = 2, α₁ = 4/3, α₂ = −1/3`).
- **Textbook verification**: the explicit closed form `a(z) = (4/3)z +
  (8/3)z²` follows from
  `(1+z)² − (4/3)(1+z)(1−z) − (−1/3)(1−z)² = 0 + (4/3)z + (8/3)z²`.
- **Lean statement captures**: same content. Direct equality of
  `bdf2LMM.aPoly` with the explicit polynomial; no hypothesis,
  no quantifier weakening.

### `bdf2LMM_aPoly_coeff_two_eq` and `bdf2LMM_aPoly_coeff_two_pos`

- **Source**: `lem_441A.json` (the `aᵢ ≥ 0` clause for `i = 2`
  instantiated at BDF2). These are numerical witnesses for the
  Phase C target on the canonical example.
- **Textbook verification**: from `bdf2LMM_aPoly_eq`, `coeff 2 = 8/3 > 0`.
- **Lean statement captures**: same content. No hypothesis, no
  weakening.

### Tautology / identity / definition-smuggling / strength checks

- Tautology check: pass — none of the three theorems' conclusions
  appear as their own hypotheses (none have hypotheses).
- Identity check: pass — proofs are not bare `exact h_*` or `:= h_*`;
  `bdf2LMM_aPoly_eq` is a multi-step proof, the two coefficient
  lemmas are short `rw + simp/norm_num`.
- Definition-smuggling check: pass — no new `def` or `structure`
  introduced this cycle.
- Hypothesis-strength check: N/A — none of the three have hypotheses.

### Issue file faithfulness

- `phantom_commit_verdict_pattern.md`: the diagnosis quotes the actual
  `git show --stat` output (which I verified inline in the strategy's
  Priority 0 verification) — no fabrication, no extrapolation beyond
  the cited evidence.
- `lem_441A_phase_C_scoping.md`: the textbook quote in §1 is verbatim
  from `extraction/raw_text/ch04.txt:1998–2008`, preserving the OCR
  glitches in the source. The Mathlib hooks are annotated with
  verification status — partially verified due to MCP rate-limiting,
  with explicit instruction to cycle 181 to re-verify before
  committing to a phase plan. No phase target asserts a specific
  Mathlib lemma exists when I have not verified it.

## Dead ends

- **Verbatim recipe from the strategy**: the strategy's suggested
  proof
  ```lean
  apply Polynomial.funext; intro x; unfold LinearMultistepMethod.aPoly
  simp only [bdf2LMM, Fin.sum_univ_two, Polynomial.eval_*, ...]; ring
  ```
  did NOT close the goal as-is. The simp set `[bdf2LMM, Fin.sum_univ_two,
  ...]` left the `bdf2LMM.α` evaluations as raw `match Fin.succ 0 with
  ...` patterns that `ring` could not consume. The fix was to
  pre-evaluate `bdf2LMM.α (Fin.succ 0)` and `bdf2LMM.α (Fin.succ 1)`
  to numeric literals via `have h1 : ... := rfl` (which forces the
  match to reduce at type-level), then `rw [h1, h2]`. The `bdf2LMM`
  was removed from the simp set entirely — the `Fin.val_zero,
  Fin.val_one` simp lemmas were enough to clean up the natural-number
  exponent arithmetic.
- **Polynomial.ext + per-coefficient `simp + norm_num`**: not
  attempted (cycle 172/173 dead end pattern, explicitly forbidden by
  the cycle 180 strategy's "What NOT to do").
- **Lean MCP `lean_local_search`**: failed with a ripgrep PATH error
  ("ripgrep (rg) was not found on your PATH"). Fell back to
  `lean_loogle` for `Polynomial.funext` verification; further hook
  verifications for the Phase C scoping doc were rate-limited and
  partial. Documented as such in `lem_441A_phase_C_scoping.md` §2.

## Discovery

- **`bdf2LMM` `match` reduction trick**: the `bdf2LMM.α` field
  uses a `match` expression on `Fin 3`, which does NOT reduce under
  `simp only [bdf2LMM]` when the index is `Fin.succ 0` or
  `Fin.succ 1` (it stays as a stuck match). The fix is to introduce
  `have h : bdf2LMM.α (Fin.succ i) = numeric := rfl` before the
  simp + ring step — `rfl` forces the match to evaluate at the
  type-level, after which `rw` replaces the symbolic α with a
  literal. This pattern is reusable for any future BDF2-side closed-
  form proofs that touch `bdf2LMM.α`.
- **`Polynomial.funext` is the right tool** for proving polynomial
  identity over `ℝ` when the polynomials are explicit Σ / product
  expressions. It sidesteps `Polynomial.ext`-style per-coefficient
  case analysis (the cycle 172/173 stall pattern) by lifting to
  pointwise evaluation, where `ring` handles `Polynomial.C` /
  `Polynomial.X` arithmetic transparently.
- **Phantom-verdict pattern is propagating four cycles deep**: the
  cycle 180 worker confirmed via direct `git show --stat` that
  cycles 176–179 all shipped real Lean diffs, despite the supervisor
  reporting otherwise four times in a row. This is materially worse
  than the prior 1-cycle false positives in cycles 008/035/073/170;
  it indicates the supervisor's diff-detection logic is reliably
  broken on `Section441.lean` specifically. The new issue file
  escalates this for loop-maintainer attention.
- **`extraction/raw_text/ch04.txt:1998–2008`** contains Butcher's
  Phase C argument in clean prose; the conjugate-pair quadratic
  factorisation step is the highest-risk step but is mathematically
  straightforward (it's just real-side polynomial factorisation,
  which Mathlib has — but the descent from ℂ-side to ℝ-side may need
  custom helper lemmas).

## Suggested next approach

**For cycle 181** (planner):

1. **Loop-maintainer escalation**: ensure the supervisor prompt-builder
   audit triggered by `phantom_commit_verdict_pattern.md` is on the
   loop-maintainer's queue. Without it, cycle 181's worker may face
   the same false-positive verdict, and the propagated `attempts.md`
   row will keep poisoning subsequent prompts. Strongly consider
   dropping the cycle 180 row from `attempts.md` once the loop-
   maintainer has audited and patched the supervisor logic.

2. **Phase C.1**: target the Möbius polynomial-identity bridge
   between `aPoly` and `αPoly` (or `ρPoly`). The cleanest definition
   is the explicit
   ```lean
   noncomputable def mobiusTransform (p : Polynomial ℝ) : Polynomial ℝ :=
     ∑ i ∈ Finset.range (p.natDegree + 1),
       Polynomial.C (p.coeff i) *
       (1 - Polynomial.X) ^ i * (1 + Polynomial.X) ^ (p.natDegree - i)
   ```
   followed by the identity `aPoly = mobiusTransform αPoly_or_ρPoly`
   (sign/normalisation TBD via the cycle 174 bridge). 1–2 cycles,
   ~150 LOC.

3. **Re-verify Mathlib hooks** in `lem_441A_phase_C_scoping.md` §2.
   Cycle 180's verification was incomplete due to MCP rate-limiting.
   Specifically validate: `Polynomial.eq_prod_roots_of_splits`,
   `Polynomial.roots_map_conj` (or equivalent), `Complex.add_conj`,
   `Polynomial.lifts`. If any are missing, file a sub-issue before
   starting Phase C.3.

4. **BDF2 sanity discipline continues**: cycle 180 added
   `bdf2LMM_aPoly_coeff_two_pos`, witnessing Phase C's headline on
   the canonical `k = 2` example. Each Phase C phase deliverable
   should similarly ship a BDF2 numerical witness alongside the
   generic theorem.

5. **Do NOT** attempt Phase C.3 (the high-risk real factorisation)
   before C.1 and C.2 are landed — it depends structurally on both
   upstream phases, and the Mathlib infrastructure risk is highest
   there. If C.3 blocks, the Phase C.bypass for BDF2 is already
   shipped (cycle 180), so the cycle's deliverable bar is at least
   met by the BDF2 witness.
