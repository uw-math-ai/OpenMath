# Cycle 045 Results

## Worked on

- **Primary**: closed the textbook (406c) form of `thm:406C` as
  `LinearMultistepMethod.globalError_recurrence_bound_textbook`
  (`OpenMath/Chapter4/Section404.lean:1330`). This is the
  `(1 − h L |β_0|)`-inversion / "use (406d) twice" absorption of the
  cycle-044 per-term bound.
- **Stretch**: added `explicitEulerLMM_step_eq`
  (`OpenMath/Chapter4/Section404.lean:364`) as a regression witness
  for the cycle-044 `IsLMMSolution` sign fix.
- **Tertiary** (`thm:406D` scaffold): not started — primary +
  stretch consumed the cycle.

## Approach

### Primary — `globalError_recurrence_bound_textbook`

Followed the planner's sketch verbatim (5-step decomposition, no
`nlinarith` on the closing step):

1. Apply cycle-044 per-term bound `hA : A ≤ c·N + T2coef·Mmax + Dh2`
   where `A = LHS abs`, `N = |yex(x_n) − Y_n|`, `c = h L |β_0|`.
2. Reverse triangle: `N ≤ B + A` where `B = |Σ α_i (yex − Y)|`.
3. Bound `B ≤ (Σ |α_i|) · Mmax` via `Finset.abs_sum_le_sum_abs`.
4. Combine via `nlinarith` to get
   `(1−c) · A ≤ c · Sα · Mmax + T2coef · Mmax + Dh2`.
5. Divide by `(1−c) > 0` using `le_div_iff₀` (Mathlib renamed
   `le_div_iff` to `le_div_iff₀`); finish with `linarith`.

Used `set` declarations for `A`, `B`, `N`, `c`, `Sα`, `T2coef`, `Dh2`
to keep `linarith`/`nlinarith` chains tractable. Final `rw` step
re-expresses the divided-form RHS in terms of the named shorthands
via a `simp only [...]; ring` block, then applies `le_div_iff₀`.

### Stretch — `explicitEulerLMM_step_eq`

Initial attempt used `Fin.sum_univ_succ` + `Fin.sum_univ_zero`, but
this only fired once on each side (only the outermost sum gets
rewritten, leaving the second sum). Switched to `Fin.sum_univ_two`
(direct unfolding for `Fin 2`, since `k = 1` ⇒ sums are over
`Fin (k+1) = Fin 2`), which expanded both sides cleanly. After
substituting the known coefficient values
(`α 0 = -1, α 1 = 1, β 0 = 0, β 1 = 1`), `linarith` closes the goal.

## Result

**SUCCESS** — both deliverables landed; `Section404.lean` compiles
cleanly via `lake env lean OpenMath/Chapter4/Section404.lean`
(only pre-existing unused-variable warnings on lines 567, 626, 1203;
no new warnings introduced this cycle). `lake env lean
OpenMath/Chapter4.lean` (which re-imports Section404) also compiles
clean.

`thm:406C` is now `formalized` in `lean_status.json` (was
`partial`); `lean_symbol` updated from `globalError_recurrence_bound`
to `globalError_recurrence_bound_textbook`. The cycle-044 per-term
form remains in the file as a load-bearing intermediate lemma.

## Faithfulness check

### `globalError_recurrence_bound_textbook` (`thm:406C`)

- Entity ID: `thm:406C`. Quote from `entities/thm_406C.json`:
  > "Then for h_0 sufficiently small so that h_0 |β_0| L < 1 and
  > h < h_0, there exist constants C and D such that
  > ‖n − Σ α_i n_{−i}‖ ≤ C h max ‖n_{−i}‖ + D h² (406c)."
- Lean statement captures: **same content**, with `C, D` as
  *explicit h-dependent rationals*. The Lean form is strictly
  tighter than the textbook (which abstracts `C`, `D` as unspecified
  constants depending on `h_0`); the textbook constants form follows
  trivially from the explicit form by taking `h ≤ h_0` and
  evaluating constants at `h_0`.
- Justification for divergence: explicit constants are tighter,
  reusable downstream (e.g. for `thm:406D` Lax-equivalence), and
  composable. Universal-quantification over `h_0` can be a one-line
  corollary in a future cycle if needed.
- Tautology check: clean. Conclusion is a numerical inequality with
  `(1 − h L |β_0|)` in the denominator; no hypothesis matches it
  verbatim.
- Identity check: proof has 5 named intermediate inequalities + a
  closing `linarith`; not a single `exact`.
- Hypothesis-strength check: `hsmall : h L |β_0| < 1` is the only
  new hypothesis vs. the per-term form; matches the textbook's
  smallness condition `h_0 |β_0| L < 1` exactly. Other hypotheses
  inherited verbatim from the per-term form.
- Absent-theorem check: `globalError_recurrence_bound` (cycle 044)
  exists at `Section404.lean:1241`. No promised content missing.

### `explicitEulerLMM_step_eq` (sanity-check witness)

- Helper lemma, not a Butcher entity. Documents and locks in the
  cycle-044 sign fix.
- Tautology check: conclusion `Y(m+1) = Y m + h · f(...)` does NOT
  match any hypothesis verbatim — the hypothesis is the abstract
  `IsLMMSolution` predicate, not the explicit Euler step.
- Identity check: proof unfolds the predicate via
  `Fin.sum_univ_two`, substitutes coefficient values, and finishes
  with `linarith`. Real work, not a re-export.
- Hypothesis-strength check: the only hypothesis is
  `explicitEulerLMM.IsLMMSolution h x₀ f Y`; this is the minimal
  hypothesis needed to derive the explicit Euler step.

## Dead ends

1. Initial `abs_add _ _` reference for the reverse-triangle step
   failed — Mathlib's name for `|a + b| ≤ |a| + |b|` is
   `abs_add_le`, not `abs_add` (the latter is the *equational*
   identity for absolute values in some specific monoid, not the
   triangle inequality used here). Fixed by switching to
   `abs_add_le`.
2. `le_div_iff` reference failed — Mathlib has renamed it to
   `le_div_iff₀`. Same content, new suffix for the `0 < c` divisor
   condition.
3. For `explicitEulerLMM_step_eq`, the obvious approach
   `rw [Fin.sum_univ_succ, Fin.sum_univ_zero,
       Fin.sum_univ_succ, Fin.sum_univ_zero]` only fired the first
   `Fin.sum_univ_succ` — the rewriter matches the outermost
   `∑ i, ?f i` pattern, which after one fire is the inner sum only
   on the LHS; the RHS sum's second-rewrite invocation found no
   match. Fixed by using `Fin.sum_univ_two` (atomic
   two-element-sum unfolding), which fires once per side.

## Discovery

1. **Mathlib renames detected this cycle**: `abs_add` →
   `abs_add_le`, `le_div_iff` → `le_div_iff₀`. Both already used
   elsewhere in the file (existing cycle-044 code uses `abs_add_le`
   directly). The strategy's tactic plan referenced the old names;
   future strategies should sanity-check Mathlib lemma names against
   what's already used in the file.
2. **`Fin.sum_univ_two` is the right tool for fixed-arity sums**.
   For `k = 1` (so sums over `Fin 2`), unfolding via
   `Fin.sum_univ_two` is one-shot and cleaner than chained
   `Fin.sum_univ_succ` + `Fin.sum_univ_zero`. (`Fin.sum_univ_three`
   etc. presumably exist for higher arities — useful for future
   k=2 sanity checks like a 2-step LMM witness.)
3. **`set` declarations + `nlinarith` is the workhorse pattern**
   for absorption-style algebra. Naming `A, B, N, c, Sα` etc.
   makes both the proof readable AND keeps `nlinarith`'s search
   space tractable. A single closing `nlinarith` would have been
   too ambitious; the named 4-step decomposition (h_step1..h_step4)
   followed by a final `linarith` after `le_div_iff₀` is robust.

## Suggested next approach

The natural next target is `thm:406D` (Convergence from Stability
and Consistency — the Lax-equivalence direction for LMMs). Its
proof depends on:

1. The textbook form of `thm:406C` (now closed).
2. A discrete Grönwall-type bound on the global-error sequence
   `{n_m}_m`, derived from the absorbed (406c) recurrence by
   iteration. **This is likely the bulk of the work.**
3. Bound on the homogeneous-recurrence solution under `IsStable`
   (already partly captured by `const_sequence_isHomogeneousSolution`
   in `Section404.lean` — but a stronger uniform bound is needed).
4. Consistency ⇒ LTE = O(h²) packaging (already in
   `localTruncationError_bound`).

Recommended cycle 046:

- Read `extraction/formalization_data/entities/thm_406D.json`
  carefully and write a sorry-first scaffold.
- Identify the discrete Grönwall sub-lemma — it is *not* present in
  Mathlib in the form needed (Mathlib's Grönwall is for continuous
  functions). It will need to be built as a helper lemma in
  `OpenMath.Chapter4.Section404` (or a new helper file).
- Submit the discrete Grönwall scaffold to Aristotle in batch
  (CLAUDE.md's free-compute rule: this is exactly the kind of
  pure-real-analysis lemma where Aristotle has the highest hit
  rate).

Aristotle hit-rate observation from prior cycles: ~5% on
absorption-style algebraic targets (cycle 044 evidence), but
plausibly higher on discrete-Grönwall (a single-pass induction
argument with one Mathlib-flavoured estimate). Worth one
submission.

If `thm:406D` is too ambitious for one cycle: split it into
- (a) discrete Grönwall as a standalone helper, then
- (b) the stability+consistency ⇒ convergence wrapper.

Both should fit comfortably within the existing `Section404.lean`.
