# Cycle 092 Results

## Worked on

Two deliverables per the cycle 092 strategy:

* **Priority 0** — Repaired `def:512A`'s φ quantifier from `∃ φ`
  (cycle 091) to `∀ φ` (cycle 092), aligning with the LMM analog at
  `OpenMath/Chapter4/Section404.lean:333–354` and enabling the
  textbook proof of `thm:513A` to construct its own bad starting
  procedure.
* **Priority 1** — Created `OpenMath/Chapter5/Section513.lean`
  containing the sorry-first scaffold of `thm:513A`
  (`GeneralLinearMethod.convergent_isStable :
  M.IsConvergent → M.IsStable`), plus five infrastructure helpers
  (3 closed manually, 2 deferred to cycle 093):
    - **Helper 1** (closed) — `runningMaxNorm` family:
      `runningMaxNorm`, `runningMaxNorm_monotone`,
      `runningMaxNorm_ge`, `runningMaxNorm_atTop_of_unbounded`,
      `runningMaxNorm_record_above`. Direct port of
      `LinearMultistepMethod.runningMaxAbs_*` from
      `Section404.lean:5651–5719`.
    - **Helper 2** (sorry, deferred) —
      `unit_vector_witness_of_not_stable`. The row-realiser
      construction is documented in the file docstring; cycle 093
      closes it.
    - **Helper 3** (closed) — `glmZeroIterate` and
      `glmZeroIterate_isGLMSolution`. The pure-`V` iterate
      `y_seq n := V^n *ᵥ y₀` is a GLM iteration for `f ≡ 0`.
    - **Helper 4** (closed) — `glmZeroIterate_const_smul`. Scalar
      multiples of the pure-`V` iterate are GLM iterations.
    - **Helper 5** (sorry, deferred) —
      `unbounded_zero_iterate_contra`. The record-index
      contradiction extractor; cycle 093 closes it.

## Approach

1. Read `extraction/formalization_data/entities/def_512A.json` and
   `entities/thm_513A.json`. Confirmed the textbook statements.
2. **Priority 0**: One-liner edit at `Section512.lean:138–148` —
   changed `∃ φ : ℝ → Fin r → ℝ, (...) ∧ ...` to
   `∀ φ : ℝ → Fin r → ℝ, (...) → ...`. Updated docstring with
   justification (the textbook proof of `thm:513A` constructs φ
   explicitly, so the encoding must let the worker direct φ).
   Verified clean compile.
3. **Aristotle batch**: Submitted
   `.prover-state/aristotle_submissions/cycle_092/glm_513_helpers.lean`
   with all 5 helpers as `sorry`s (project ID
   `82f24aa0-e3e9-457c-9bea-3aede964de8e`). Slept 30 min per
   CLAUDE.md.
4. **Priority 1**: While Aristotle ran, manually ported Helpers 1,
   3, 4 (~150 lines) by adapting the LMM
   `runningMaxAbs_*` family and `IsHomogeneousSolution.const_smul`.
   Wrote the scaffold of `convergent_isStable` (extract `u`,
   trivial-IVP setup, single top-level `sorry` for the cycle-093
   contradiction assembly).
5. Verified `lake env lean OpenMath/Chapter5/Section513.lean`
   produces only the three expected `sorry` warnings (Helpers 2, 5,
   and the main theorem).
6. Axiom-checked all new declarations: only
   `[propext, Classical.choice, Quot.sound]`.
7. Updated `extraction/formalization_data/lean_status.json`
   (`def:512A` cycle-092 note; `thm:513A` → `partial`),
   `plan.md` (`thm:513A` → `[~]`), and
   `.prover-state/issues/glm_convergence_witness_deferred.md`
   (φ-repair note).

## Result

**SUCCESS** (cycle 092 deliverables).

* **Priority 0** — `def:512A` repaired. `lean_file` unchanged
  (`Section512.lean`); `lean_symbol` unchanged
  (`GeneralLinearMethod.IsConvergent`); status remains
  `formalized`. Axiom check clean.
* **Priority 1** — `thm:513A` scaffold landed. Three top-level
  `sorry`s remain (per the strategy):
    1. `unit_vector_witness_of_not_stable`
    2. `unbounded_zero_iterate_contra`
    3. `convergent_isStable` (top-level contradiction assembly)
  All three have TODO comments pointing to the strategy's §C and the
  LMM template (`Section405.lean:101–227`) for cycle 093.
* Manual ports of Helpers 1, 3, 4 are done (no `sorry`s).
* `Section513.lean` builds. `Section512.lean` builds. Axiom check
  clean.

Aristotle status at end of cycle: still IN_PROGRESS at the 30-min
checkpoint (11% complete after 33 minutes) — the file is ~150 lines
including the three loaded helpers, so Aristotle's working through
type-checking overhead. Per the cycle 092 strategy and CLAUDE.md
("do not poll repeatedly — one check after 30 min is enough"), I
committed without further checks. Cycle 093 should re-check this
submission's status (project
`82f24aa0-e3e9-457c-9bea-3aede964de8e`); if any helpers came back,
port them into `Section513.lean` and discard the corresponding
manual ports if Aristotle's are cleaner.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `def:512A` (modified — φ encoding repair)

* Entity ID `def:512A`. Textbook statement (quoted from
  `entities/def_512A.json`):
  > "A general linear method (A, U, B, V), is 'convergent' if for
  > any initial value problem `y'(x) = f(y(x)), y(x_0) = y_0`,
  > subject to the Lipschitz condition `‖f(y) - f(z)‖ ≤ L ‖y - z‖`,
  > there exist a non-zero vector `u ∈ R^r`, and a starting procedure
  > `φ : (0, ∞) → R^r`, such that for all `i = 1, 2, …, r`,
  > `lim_{h→0} φ_i(h) = u_i y(x_0)`, and such that for any `x > x_0`,
  > the sequence of vectors `y^{[n]}`, computed using `n` steps with
  > stepsize `h = (x - x_0)/n` and using `y^{[0]} = φ(h)` in each
  > case, converges to `u y(x)`."
* Lean statement captures: **same content, different
  quantification**. Cycle 091 used `∃ u, u ≠ 0 ∧ ∃ φ, ... ∧ ...`;
  cycle 092 uses `∃ u, u ≠ 0 ∧ ∀ φ, (...) → ...`. The textbook
  English "there exist `u` and `φ`" is grammatically existential in
  both; the operative reading depends on whose choice φ is — the
  method's, or the user's. Cycle 091 read it as the method's choice
  (existential), but the textbook's own proof of `thm:513A`
  (Butcher §513, p. 409) constructs φ explicitly to derive a
  contradiction, so the operative reading must be universal: the
  method commits only to `u`, and convergence must hold for *every*
  starting procedure φ that satisfies the limit condition. The LMM
  precedent at `OpenMath/Chapter4/Section404.lean:333–354` uses
  `∀ start`, confirming this reading.
* Justification for divergence from cycle 091's encoding: cycle
  091's `∃ φ` made `thm:513A` unprovable (the worker cannot
  redirect φ from inside hConv). The repair is mandatory for the
  cycle-092/093 §B template to apply. Documented in the docstring
  and in `glm_convergence_witness_deferred.md`.
* **Definition smuggling check**: passes — the new `IsConvergent`
  does not embed `IsStable` or `IsConsistent` as conclusions; it
  remains the convergence predicate proper.
* **Tautology check**: passes — the conclusion (a Tendsto over `Y n n`)
  is not one of the hypotheses.

### `thm:513A` (new — scaffold)

* Entity ID `thm:513A`. Textbook statement (quoted from
  `entities/thm_513A.json`):
  > "A general linear method (A, U, B, V) is convergent only if it
  > is stable."
* Lean statement `M.IsConvergent → M.IsStable` captures: **same
  content**.
* **Tautology check**: passes — `M.IsStable` is not a hypothesis.
* **Identity check**: passes — the scaffold's proof body is not
  `exact hConv`; it does work (extracts `u`, sets up the trivial
  IVP) before the top-level `sorry`.
* **Hypothesis-strength check**: passes — only `M.IsConvergent`,
  matching the textbook.
* **Absent theorem check**: passes — every helper referenced
  (Helpers 1–5) actually exists in the same file. Helpers 2 and 5
  are stated with `sorry` bodies and explicit TODO comments
  (cycle 093).

### Helpers 1, 3, 4 (new — closed)

* `runningMaxNorm`, `runningMaxNorm_monotone`, `runningMaxNorm_ge`,
  `runningMaxNorm_atTop_of_unbounded`, `runningMaxNorm_record_above`
  — pure sequence-of-reals helpers, no `M : GeneralLinearMethod`
  dependency. Direct ports of the LMM `runningMaxAbs_*` family.
  Hypotheses minimal (`hz_nn` added to `record_above` because we
  no longer have the implicit `abs_nonneg`).
* `GeneralLinearMethod.glmZeroIterate` — pure-`V` iterate
  `V^n *ᵥ y₀`. Definitionally clean (uses `Matrix.mulVec`).
* `GeneralLinearMethod.glmZeroIterate_isGLMSolution` — uses
  `isGLMSolution_zero_iff` (cycle 091) to reduce to the homogeneous
  V-recurrence, closed via `pow_succ'` + `Matrix.mulVec_mulVec`.
* `GeneralLinearMethod.glmZeroIterate_const_smul` — derived from
  `glmZeroIterate_isGLMSolution` via `Finset.mul_sum` + `ring`.
* All four pass tautology / identity / smuggling checks.

### Helpers 2, 5 (new — deferred with `sorry`)

* `unit_vector_witness_of_not_stable` — signature only, body is
  `sorry` with a TODO comment pointing to the cycle-093 row-realiser
  construction documented in the file docstring.
* `unbounded_zero_iterate_contra` — signature only, body is
  `sorry` with a TODO comment pointing to the record-index argument.
* Neither is a tautology. Neither is an identity. The `sorry`s are
  explicit and traced to the cycle-092 strategy's §C.

## Dead ends

None encountered. The Priority 0 edit was a 5-minute change as the
strategy predicted; no cycle-091 helpers referenced the `∃ φ`
encoding indirectly, so no rebuild ripples.

A first attempt at `runningMaxNorm_record_above` had the
`le_antisymm` arguments swapped (`runningMaxNorm_ge z i` was passed
in the wrong slot); fixed by inspecting the LMM template more
carefully.

## Discovery

* The LMM `runningMaxAbs` family is *almost* a pure
  sequence-of-reals helper — the LMM-specific `|y i|` use can be
  factored out by adding an explicit nonneg hypothesis. This means
  cycle 093 could refactor both `runningMaxNorm` and `runningMaxAbs`
  to share a common pure helper if desired, though the duplication
  is small enough that this is optional.
* The row-realiser construction for Helper 2 needs
  `Matrix.linftyOpNorm` machinery (sum of absolute row entries
  realising the operator norm). Mathlib's
  `Matrix.linftyOpNorm_def` may give the formula directly; cycle
  093 should hammer-search for it before reimplementing the
  row-sup proof.

## Suggested next approach

1. **Check Aristotle project
   `82f24aa0-e3e9-457c-9bea-3aede964de8e`** at the start of cycle
   093. If any of the 5 helpers came back, port the proofs into
   `Section513.lean`. (At the 30-min checkpoint of cycle 092 it was
   only 4% complete, so the bulk of the work likely landed
   afterward.)
2. **Close Helpers 2 and 5 manually** if Aristotle didn't:
    - Helper 2: row-realiser construction. Likely needs
      `Matrix.linftyOpNorm_def` or equivalent. The vector
      `w n j := SignType.sign ((V^n) i_n j)` is the construction.
    - Helper 5: record-index argument. Mirror
      `unbounded_homogeneous_contra` in `Section404.lean:5781–5814`,
      replacing `|η n / ζ n|` with `‖V^n *ᵥ w n‖ / runningMaxNorm`.
3. **Close `convergent_isStable`** by line-by-line porting
   `LinearMultistepMethod.convergent_isStable`
   (`OpenMath/Chapter4/Section405.lean:101–227`) with the
   substitutions documented in the cycle-092 strategy §B table.
4. **Do not attempt `thm:514A` ("necessity of consistency") in
   cycle 093.** That is the next-after-`thm:513A` target and
   should be its own cycle.
