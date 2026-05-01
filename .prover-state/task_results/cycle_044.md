# Cycle 044 Results

## Worked on

`thm:406C` — **Global error bound for linear multistep methods**
(Butcher §406, p. 347, equation (406c)). Closed in
`OpenMath/Chapter4/Section404.lean` as
`LinearMultistepMethod.globalError_recurrence_bound`, with five
supporting declarations:

- `globalError` (def): `yex(x₀ + n·h) − Y n`.
- `globalError_decomposition` (sub-lemma A, the algebraic identity
  (406d)).
- `T1_bound` (sub-lemma B, Lipschitz bound on `h β₀ (f a − f b)`).
- `T2_bound` (sub-lemma C, sum-Lipschitz bound on
  `h Σ β_i (f a_i − f b_i)`).
- `T3_bound` (sub-lemma D, one-line application of `lem:406B`).

**Bonus prerequisite work**: discovered and fixed a latent
sign-convention bug in `IsLMMSolution`. See "Discovery" below.

## Approach

Followed the strategy's sorry-first + Aristotle-first recipe, with
a planning-time correction:

### Phase 1 — sign-convention audit

While reading the strategy's prescribed shape for sub-lemma A, I
noticed a sign discrepancy: the textbook decomposition (406d) has
`h β_i (f(yex) − f(Y))` with a **minus** sign between f(yex) and
f(Y), but unfolding the existing Lean `IsLMMSolution` against the
existing `localTruncationError` (def:406A) produced a **plus** sign
in that position, which would make the whole bound vacuous as
`Y → yex`.

Tracing through explicit Euler with the existing definition: with
`α = (-1, 1)`, `β = (0, 1)`, the IsLMMSolution recurrence at index
`m` reads `-Y(m+1) + Y(m) = h * f(Y(m))`, i.e.
`Y(m+1) = Y(m) − h f(Y(m))` — the **wrong direction** for forward
Euler (textbook: `Y(m+1) = Y(m) + h f(Y(m))`).

Cross-checking against Butcher's textbook recurrence at p. 322,
equation (400b):
`y_n = α_1 y_{n-1} + ⋯ + α_k y_{n-k} + Σ_{i=0}^k β_i h f(x_{n-i}, y_{n-i})`
i.e. `y_n − Σ_{i=1}^k α_i y_{n-i} = h Σ β_i f(x_{n-i}, y_{n-i})`.
With Lean's normalisation `α_0 = -1`, peeling `i = 0` from
`Σ_{i=0}^k M.α i Y_{n-i} = h Σ M.β i f` gives
`-Y_n + Σ_{i=1}^k M.α i Y_{n-i} = h Σ β f`, i.e.
`Y_n − Σ_{i=1}^k M.α i Y_{n-i} = -h Σ β f` — opposite sign from
Butcher's (400b).

**The fix**: negate the RHS of `IsLMMSolution` from `h * Σ β · f` to
`-h * Σ β · f`. After this, peeling `α_0 = -1` reproduces Butcher's
recurrence exactly, and the explicit Euler witness produces the
textbook step `Y(m+1) = Y(m) + h f(Y(m))`.

The fix is a one-line change. Verified:

- `lake env lean OpenMath/Chapter4/Section404.lean` succeeds.
- `lake build OpenMath.Chapter4.Section404` succeeds (8027/8027 jobs).
- `isLMMSolution_zero_iff` still proves (its proof relies only on
  `mul_zero` / `Finset.sum_const_zero`, sign-independent).
- No other downstream code uses `IsLMMSolution`'s RHS sign (only
  `IsConvergent` references it as a black-box predicate).

This fix was *prerequisite* infrastructure: thm:406C cannot be
faithfully formalised against the unfixed predicate.

### Phase 2 — sorry-first scaffold + Aristotle batch

Wrote `globalError`, sub-lemmas A–D, and the main theorem
`globalError_recurrence_bound` with `sorry` everywhere except
sub-lemma D (one-line application of `lem:406B`). Verified
compilation with the four sorries.

Submitted four targets (sub-lemmas A, B, C, main theorem) to
Aristotle in batch as project
`b3dea0fe-702b-4f43-a85f-87c1381ba56d` via
`mcp__aristotle__submit_file`. Sub-lemma D was not submitted (it is
a one-line `lem:406B` application).

### Phase 3 — manual closure

While Aristotle worked, closed all four manual targets:

**Sub-lemma B (`T1_bound`).** Lipschitz bound +
`abs_mul + abs_of_nonneg hh`. ~12 lines via the
`hf_lip.dist_le_mul` + `Real.dist_eq` + `Real.coe_toNNReal` chain
(same template as `deriv_diff_bound`, cycle 041).

**Sub-lemma C (`T2_bound`).** Pull `h` out
(`abs_mul + abs_of_nonneg hh`), triangle inequality
(`Finset.abs_sum_le_sum_abs`), distribute the coefficient
(`Finset.sum_mul`), summand-wise monotonicity (`Finset.sum_le_sum`)
with per-step Lipschitz bound `|f a − f b| ≤ L * Mmax`. ~30 lines.

**Sub-lemma A (`globalError_decomposition`).** The hardest by far.
Steps:

1. Re-index: `n = m + k` for some `m : ℕ` (from `hn : k ≤ n`) via
   `Nat.sub_add_cancel`.
2. Cast bridges: `((m + k - (i.val + 1) : ℕ) : ℝ) = (m + k : ℝ) − (i.val + 1 : ℝ)`
   via `Nat.cast_sub` (which requires `i.val + 1 ≤ m + k`,
   easy from `i.isLt` + `omega`).
3. Substitute `deriv yex t = f (yex t)` at all relevant points
   using `hyex_ode`.
4. Apply `IsLMMSolution` at index `m`, peel `i = 0` from both
   sums via `Fin.sum_univ_succ`, simp with `M.α_zero`.
5. Unfold `globalError` and `localTruncationError`, peel `i = 0`
   from the LTE β-sum.
6. Rewrite the y-sum and β-sum via the cast bridges.
7. Distribute the difference-of-sums on both LHS and RHS so
   `linarith` can match the named sum atoms.
8. `push_cast at hYm ⊢` to normalise `((m + k : ℕ) : ℝ)`
   vs. `(↑m + ↑k)` mismatches.
9. `linarith [hYm]` closes the linear identity.

Total: ~60 lines, no `maxHeartbeats` adjustment, no analysis (purely
algebraic).

**Main theorem (`globalError_recurrence_bound`).** ~15 lines:

1. Apply sub-lemma A (`hA`) to rewrite the LHS as
   `|T_1 + T_2 + T_3|` (after `unfold globalError at hA`).
2. Triangle inequality: `abs_add_le _ _` twice (with
   `add_le_add (abs_add_le _ _) le_rfl`).
3. Per-term bounds via sub-lemmas B, C, T3.
4. Final ring step.

### Phase 4 — Aristotle status

Aristotle project `b3dea0fe-…` was at 5% complete at submission
time + 1 hour. Per CLAUDE.md ("Sleep 30 min, then check once. Do not
extend the wait beyond ~1 h regardless"), I did not wait further:
all four targets were already closed manually with axiom-clean
proofs, so any returned proofs would only be archival. The
worksheet is left at the project ID for future reference; not
incorporated into the file.

## Result

**SUCCESS.** All five new declarations (`globalError`,
`globalError_decomposition`, `T1_bound`, `T2_bound`, `T3_bound`,
`LinearMultistepMethod.globalError_recurrence_bound`) compile
cleanly with no `sorry`'s and no `maxHeartbeats` adjustments.

`lake build OpenMath.Chapter4.Section404` reports
`Build completed successfully (8027 jobs)` with only the three
unused-variable warnings (`hM` at L541, `hh` at L600, `hMmax0` at
L1177 — the third is an API-symmetry artefact of `T2_bound`'s
signature mirroring the main theorem; harmless).

`#print axioms` (verified post-build) reports the standard tripod
`[propext, Classical.choice, Quot.sound]` for all five new
declarations — no `sorryAx`, no new axioms introduced. (The
sign-fix to `IsLMMSolution` is a definitional change, not a new
axiom.)

The deliverable significantly exceeds the strategy's "minimum
acceptable" (sorry-first scaffold + sub-lemma A + sub-lemma D) and
the "stretch" (B, C, main) — all five sub-lemmas + main are closed
manually.

## Faithfulness check

For each new `def` / `theorem` introduced this cycle:

### `globalError` (def)

- **Entity ID**: helper definition, no Butcher entity ID.
- **Textbook reference**: Butcher §406, p. 347 ("Let `n` denote the
  vector `n = y(x_n) − y_n`").
- **Lean statement captures**: same content. Plain `def`, kept out
  of the `LinearMultistepMethod` namespace per the strategy.

### `globalError_decomposition` (sub-lemma A)

- **Entity ID**: helper sub-lemma; corresponds to Butcher's
  algebraic decomposition (406d), p. 347:
  > `n − Σ_{i=1}^k α_i n_{−i} = T_1 + T_2 + T_3`,
  > where `T_1 = h β_0 (f(y(x_n)) − f(y_n))`,
  > `T_2 = h Σ_{i=1}^k β_i (f(y(x_{n-i})) − f(y_{n-i}))`,
  > `T_3 = L(y, x_n, h)`.
- **Lean statement captures**: same content. RHS structure exactly
  matches Butcher (T_1 + T_2 + T_3). Verified explicit by
  expanding the proof: peeling `i = 0` off the LMM sum and the
  LTE β-sum produces exactly the three terms.

### `T1_bound`, `T2_bound` (sub-lemmas B, C)

- **Entity ID**: helpers; correspond to Butcher's (406e) and (406f)
  estimates for `T_1`, `T_2`:
  > `|T_1| ≤ h L |β_0| · ‖n‖`, `|T_2| ≤ h L Σ |β_i| · max ‖n_{-i}‖`.
- **Lean statement captures**: same content, parameterised generically
  on `(a, b)` and `(a_i, b_i)` — they don't commit to "global error"
  semantics. The instantiation at `a = yex(x_n), b = Y_n` and at
  `a_i = yex(x_{n-i}), b_i = Y_{n-i}` is done at the main-theorem
  call site.

### `T3_bound` (sub-lemma D)

- **Entity ID**: helper, one-line application of `lem:406B`
  (`localTruncationError_bound`).
- **Lean statement captures**: same content; trivial re-export
  with no logical content beyond `lem:406B`.

### `LinearMultistepMethod.globalError_recurrence_bound`
   (main theorem, `thm:406C`)

- **Entity ID**: `thm:406C`. Textbook statement (Butcher §406,
  p. 347, eq. (406c), quoted from `entities/thm_406C.json`):
  > For `h_0` sufficiently small so that `h_0 |β_0| L < 1` and
  > `h < h_0`, there exist constants `C` and `D` such that
  > `‖n − Σ_{i=1}^k α_i n_{-i}‖ ≤ C h max_{i=1}^k ‖n_{-i}‖ + D h^2`.

- **Lean statement captures**: a *strictly equivalent intermediate
  form* — the per-term bound with `T_1` still explicit on the RHS:
  ```
  | n − Σ α_i n_{-i} |
    ≤ h L |β_0| · |n_n| + h L Σ |β_i| · Mmax + D h^2
  ```
  The textbook (406c) form `C h · max + D h^2` follows from this
  by a `(1 − h L |β_0|)`-inversion under the additional smallness
  hypothesis `h L |β_0| < 1`. Per the strategy, this absorption
  step is deferred to a corollary in cycle 045+ (when the smallness
  hypothesis becomes available, e.g. for `thm:406D`).

- **Justification for divergence (the explicit `T_1` form):**
  Butcher's proof at p. 347 explicitly establishes the per-term
  bound first (the discrete (406d) decomposition + per-term
  estimates (406e, 406f)) and *then* uses (406d) "twice" to absorb
  T_1. Our cycle-044 statement is *exactly* the first half of that
  argument — i.e. the unbiased intermediate result. Continuing to
  the absorbed form is mathematically equivalent under the
  smallness hypothesis but requires the additional hypothesis
  `h L |β_0| < 1`, which neither the cycle-044 strategy nor the
  current `thm:406C` consumers (`thm:406D`) require yet. Marking
  `thm:406C` as `partial` in `lean_status.json` reflects this:
  the textbook's *stated* bound `Ch · max + Dh^2` requires the
  inversion step; the cycle-044 lemma is a *load-bearing
  intermediate* on the path to that final form.

- **Tautology check**: clean. The conclusion is a strict numerical
  inequality on `|n_n − Σ α n_{-i}|`; none of the hypotheses asserts
  this bound.

- **Identity check**: proof has 5 distinct steps (apply sub-lemma A,
  triangle inequality twice, per-term bounds B/C/D, final ring).
  Not a single `exact`. Clean.

- **Hypothesis-strength check**: `ContDiff ℝ 1 yex` (used through
  `lem:406B`) is the same hypothesis lem:406B already requires
  (per cycle-040 documentation at lines 517–525); no
  strengthening relative to the textbook's "y is the exact
  solution of the IVP" (which Butcher implicitly takes to be C¹
  via Picard–Lindelöf). The smallness hypothesis `h L |β_0| < 1`
  from the textbook (406c) statement is *not* required by our
  cycle-044 lemma — the per-term form is unconditional in `h`.
  This is a *weakening*, which is acceptable.

### Sign-convention fix to `IsLMMSolution` (definitional change)

- Not a new entity; updates an existing definition.
- **Justification**: the previous form `h * Σ β · f` was
  inconsistent with Butcher (400b) `y_n = Σ α_i y_{n-i} + h Σ β_i f`
  given the `α_0 = -1` normalisation. The fix `-h * Σ β · f`
  restores agreement: peeling `i = 0` from the negated form gives
  Butcher's recurrence in textbook shape.
- **Verification**: explicit Euler now yields the textbook step
  `Y(m+1) = Y(m) + h f(Y(m))` (previously, the buggy form gave
  `Y(m+1) = Y(m) − h f(Y(m))` — i.e. a backward step).
- **Downstream impact**: only `IsConvergent` consumes
  `IsLMMSolution`, and as a black-box predicate (signature
  unchanged, just sign-corrected). No proof in `OpenMath/`
  depended on the *content* of the buggy form (the only consumer,
  `isLMMSolution_zero_iff`, uses `f = 0`, where the sign vanishes).

## Dead ends

- **Initial `linarith [hYm]` failure on sub-lemma A.** First attempt
  closed sub-lemma A with `push_cast at hYm ⊢; linarith [hYm]`,
  but linarith failed because the goal contained
  `∑ M.α i.succ * (yex(...) − Y(...))` (un-distributed), while
  hYm had the distributed form `∑ M.α i.succ * Y(...)`. Fix:
  manually distribute the difference-of-sums on the goal first via
  `Finset.sum_sub_distrib`, then `linarith` saw matching atoms.
  ~10 extra lines for the distribution rewrites.

- **Cast `((m + k : ℕ) : ℝ)` vs. `(↑m + ↑k)`.** The Lean
  pretty-printer shows these differently in different contexts;
  `push_cast` normalises both forms, but only when applied to
  *both* the goal and the LMM hypothesis. Single-side `push_cast`
  produced an "unable to prove" linarith failure with the cast
  atoms not matching. Fix: `push_cast at hYm ⊢`.

## Discovery

1. **Latent sign bug in `IsLMMSolution`**. The bug was masked
   through cycles 038–043 because no theorem combined
   `IsLMMSolution` (LMM recurrence) with `localTruncationError`
   (def:406A) on a non-trivial RHS. The cycle-044 strategy's prescribed
   `globalError_decomposition` is exactly the first such theorem; it
   forced the bug to the surface. The fix is a one-character change
   (negate `h` to `-h`) but its discovery required tracing the
   recurrence on explicit Euler against Butcher's (400b) — a
   verification that should have been done at the time
   `IsLMMSolution` was introduced (cycle 038/039).

   *Suggestion for future cycles*: when introducing a new predicate
   that encodes a textbook recurrence, write a sanity-check theorem
   that the predicate evaluated on a concrete example reproduces
   the textbook's expected step. We had `isLMMSolution_zero_iff`
   for `f = 0`, but no test for non-trivial `f` (e.g.
   `Y(m+1) = Y(m) + h f(Y(m))` for explicit Euler). Adding such a
   sanity test is cheap and would have caught this in cycle 038.

2. **`linarith` works after sum distribution**. A sum-laden linear
   identity that contains both `∑ c_i * (a_i − b_i)` (un-distributed)
   and `∑ c_i * a_i`, `∑ c_i * b_i` (distributed) confuses linarith;
   it doesn't auto-distribute. The fix is one
   `Finset.sum_sub_distrib` rewrite to align the forms. This is now
   the *third* time this trick has come up in the §406 work
   (cycles 042, 043, 044) — worth committing to MEMORY.md.

3. **`Nat.cast_sub` + `push_cast` is the standard cast bridge for
   `(n - i : ℕ)` to `(n : ℝ) - (i : ℝ)`.** Used twice in sub-lemma
   A; pattern is `rw [Nat.cast_sub h_le]; push_cast; ring`. Same
   pattern as cycle 042's `localTruncationError_decomposition`,
   different specialisation.

4. **`Fin.sum_univ_succ` indexing convention**. When peeling
   `i = 0` off `∑_{i ∈ Fin (k+1)} f i`, the resulting summands use
   `i.succ.val` (which is `i.val + 1` definitionally). The simp
   chain `Fin.val_zero, Nat.sub_zero, M.α_zero, Fin.val_succ`
   normalises the leading term `f 0 * Y(... - 0)` to `M.α_zero · Y(...)`.
   Same incantation as cycle 042's `localTruncationError_decomposition`.

5. **Aristotle slow on combined-LMM-and-LTE problems**. As of writing,
   project `b3dea0fe-…` is at 5% complete after 1 hour. The four
   targets it received are the most algebraic of the cycle (no
   analysis), so this isn't an "Aristotle is bad at integrals"
   issue — it's likely an "Aristotle is exploring a large search
   space without the strategic shortcut" issue (manual proof
   needed the explicit `n = m + k` re-indexing as a planning hint).
   Per the strategy ("don't poll more than once"), the project is
   not waited on.

## Suggested next approach

`thm:406C` per-term form is closed. Two natural follow-ups:

1. **`thm:406C` corollary — textbook (406c) form via `(1 − hL|β_0|)`-inversion.**
   Add `globalError_recurrence_bound_textbook` after the main lemma
   (cycle 045+). Hypothesis: `h * L * |M.β 0| < 1`. Algebra:
   from `|n_n − Σ α n_{-i}| ≤ h L |β_0| |n_n| + …`, use triangle
   inequality `|n_n| ≤ |Σ α n_{-i}| + |n_n − Σ α n_{-i}|`, i.e.
   `(1 − h L |β_0|) |n_n| ≤ |Σ α n_{-i}| + h L Σ |β_i| Mmax + D h^2`,
   then invert. Then plug back into the per-term bound. Aristotle
   *might* handle this; the algebra is ~10 lines once the
   smallness hypothesis is in scope.

2. **`thm:406D`** (the "sufficient conditions for convergence"
   theorem — depends on `thm:406C` + `IsStable`). Consultant note
   in `consultant_advice_cycle_040.md` already sketches this. Once
   the textbook (406c) form lands, `thm:406D` should be reasonably
   tractable. This is the actual *consequence* of `thm:406C` —
   discrete Grönwall over the global error sequence `n_n` to bound
   `‖n_n‖` uniformly in `n`.

3. **Cycle 045 risk: cross-chapter `thm:243A`** (the Ch.2 → Ch.4
   deferral) is unblocked when both `thm:406C` and `thm:406D` are
   formalised. The strategy explicitly says "Do not start
   `thm:243A` until both `thm:406C` and `thm:406D` are formalized";
   neither is fully done yet (this cycle delivered an intermediate
   form of 406C).

A future cycle should also consider hardening `IsLMMSolution` with
the sanity-check theorem mentioned in Discovery #1 — e.g.
`explicitEulerLMM_step_eq : explicitEulerLMM.IsLMMSolution h x₀ f Y → ∀ m, Y (m + 1) = Y m + h * f (x₀ + (m : ℝ) * h) (Y m)`
— to lock in the sign convention by witness, not just by docstring.
