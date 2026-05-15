# Cycle 246 Results

## Worked on

**`thm:319B` Phase 1 — accumulation recurrence** (Butcher §319 p. 190),
the structural inductive step underlying the global truncation error
bound. Three deliverables in `OpenMath/Chapter3/Section319.lean`:

* D1 `RKTableau.IsRKTrajectory f h traj` — iterated-step trajectory
  predicate.
* D2 `RKTableau.HasLocalTruncationErrorBound f h yex δ` — local
  truncation error bound predicate (Butcher's Figure 319(ii)),
  encoded existentially.
* D3 `RKTableau.accumulation_recurrence` — the headline accumulation
  inequality.

Plus a private helper `lem_319A_extract` re-stating cycle 245's
`lem_319A` with universal `(y₀, z₀)` quantifier (Option (b) from §E.1
of the strategy), and D6 a non-vacuity witness on `paddedEuler`.

## Approach

Followed the planner's recipe (§E of strategy). Implementation plan:

1. **Helper `lem_319A_extract`** — verbatim port of cycle 245's
   `lem_319A` body with the `(y₀, z₀)` quantifier moved inside the
   existential conclusion. Necessary because the accumulation
   induction needs the *same* `L_dag` applied at multiple `(y₀, z₀)`
   pairs (one per step), and `Classical.choose`-style extraction
   from `lem_319A` does not provide definitional equality of `L_dag`
   across calls with different implicit `(y₀, z₀)` binders. ~135 LOC
   body (mechanical copy).

2. **D3 induction** — extract `L_dag` once at the top via
   `lem_319A_extract`, then induct on `n`:

   * **Base case** (`n = 0`): `Fin.last 0 = 0` collapses LHS to
     `‖yex 0 − traj 0‖`; RHS empty sum + `(1 + h L)^0 = 1` gives the
     same. Closes via `simp [Fin.last]`.

   * **Inductive step** (`n = m + 1`): restrict the prefix
     `traj' k := traj k.castSucc`, `yex' k := yex k.castSucc`,
     `δ' k := δ k.castSucc`; verify the restricted predicates by
     unfolding via `Fin.succ_castSucc : k.castSucc.succ = k.succ.castSucc`;
     apply `ih` to get a bound at `Fin.castSucc (Fin.last m)`. Then
     extract the last step's local-truncation-error witness via
     `h_lte (Fin.last m)`; bound the last-step difference via the
     triangle inequality plus `h_contract` applied to
     `(yex (Fin.last m).castSucc, traj (Fin.last m).castSucc)` and
     using `Fin.succ_last : (Fin.last m).succ = Fin.last (m + 1)`.
     Combine `ih_app` (amplified by `(1 + h L_dag)`) with the
     local-error contribution; arithmetically rearrange to match the
     goal at `n = m + 1` via `Fin.sum_univ_castSucc` and
     `pow_succ'`.

3. **D6 witness** — `paddedEuler.A = 0` makes Frobenius smallness
   automatic (`‖0‖ = 0 < 1`); applies `accumulation_recurrence`
   directly with `f := id`, reusing the cycle 245 D5 smallness
   plumbing pattern.

## Result

**SUCCESS — axiom-clean.**

* `lake env lean OpenMath/Chapter3/Section319.lean` exits 0.
* `grep -c sorry OpenMath/Chapter3/Section319.lean` = 0.
* All four new symbols
  (`IsRKTrajectory`, `HasLocalTruncationErrorBound`,
  `accumulation_recurrence`, `lem_319A_extract`) and the cycle 244/245
  carryover symbols
  (`stage_diff_recurrence`, `output_diff_recurrence`,
  `lem_319A_recurrences`, `lem_319A`) regression-clean at
  `[propext, Classical.choice, Quot.sound]`.

Section319.lean: 474 LOC → 871 LOC, +397 LOC (135 for
`lem_319A_extract`, 175 for `accumulation_recurrence`, 40 for D1+D2
definitions and docstrings, 35 for D6 example, ~10 for new docstrings
and section delimiters).

## Faithfulness check

For each new definition/theorem introduced this cycle:

### `IsRKTrajectory`

- **Entity ID**: not a textbook-named concept. Encodes Butcher's
  `(y_k)_{k=0}^{n}` numerical-trajectory sequence as a `Prop`
  predicate `∀ k : Fin n, M.IsRKOneStep f (traj k.castSucc) h (traj k.succ)`.
- **Lean statement captures**: same content, in predicate form.
- **Faithfulness**: documented in the definition's docstring.

### `HasLocalTruncationErrorBound`

- **Entity ID**: not a textbook-named concept directly, but
  corresponds to Butcher's Figure 319(ii) local-truncation-error
  bound. Statement form: for each step `k`, there exists an
  intermediate value `y_step` produced by `M` from `yex k.castSucc`,
  and `‖yex k.succ − y_step‖ ≤ δ k`.
- **Lean statement captures**: weaker than the textbook (textbook
  defines `δ_k` as an *equality* `δ_k = ‖y(x_k) − ŷ_k‖`; we use an
  *inequality*).
- **Justification for divergence**: the inequality form is the right
  interface for accumulation — it is the *bound* on `δ_k`, not its
  exact value, that propagates through the accumulation recurrence.
  Documented in the definition's docstring.

### `accumulation_recurrence`

- **Entity ID**: `thm:319B` (Phase 1). Textbook intermediate
  inequality (quoted from
  `extraction/formalization_data/entities/thm_319B.json`, Butcher §319
  p. 190 proof, paraphrased):
  > "Use Figure 319(ii) and obtain the estimate
  > `‖y(x_n) − y_n‖ ≤ C h^{p+1} ∑_{k=1}^{n} (1 + h L)^k`."
- **Lean statement captures**: more general than the textbook
  intermediate inequality. Ours:
  `‖yex_n − traj_n‖ ≤ (1 + h L^†)^n · ‖yex_0 − traj_0‖`
  ` + ∑_{k=0}^{n-1} (1 + h L^†)^{n-1-k} · δ_k`.
  The textbook pre-specializes `δ_k = C h^{p+1}` (a uniform bound);
  ours leaves `δ_k` as an arbitrary `Fin n → ℝ` sequence. Phase 2
  (cycle 247) will specialize and bound the geometric sum.
- **Faithfulness divergence (smallness)**: inherited from cycle 245
  — Frobenius operator norm `‖(h₀ L) • |A|‖_F < 1` instead of
  spectral-radius `h₀ L ρ(|A|) < 1`. Documented in docstring.
- **Tautology check**: conclusion does not appear as a hypothesis. ✓
- **Identity check**: proof is non-trivial (~175 LOC, composes
  `lem_319A_extract` with `Fin`-induction, triangle inequality,
  and arithmetic rearrangement). ✓
- **Hypothesis strength check**: hypotheses match cycle 245's
  `lem_319A` plus standard Lipschitz/smallness; no extra hypotheses
  beyond what the textbook proof needs. ✓

### `lem_319A_extract` (private helper)

- **Status**: not a textbook-named theorem; an internal repackaging
  of cycle 245's `lem_319A` with the `(y₀, z₀)` quantifier moved
  inside the existential conclusion.
- **Mathematically equivalent** to `lem_319A` (same proof body, only
  the position of the universal quantifier differs).
- **Tautology/identity checks**: same as `lem_319A`.

## Dead ends

**Initial namespace lookup confusion (resolved)**: an initial
`#print axioms` call from a fresh test file failed with
`Unknown constant` for all symbols, despite the file compiling
cleanly. Root cause: the file had compiled successfully but its
`.olean` was not loaded into the test harness's environment because
`lake env lean` does not run the dependent module's build on each
invocation when iterating in the same shell. Resolved by running
`lake build OpenMath.Chapter3.Section319` once explicitly; subsequent
`#print axioms` checks worked. Cost: ~5 minutes.

**Initial proof errors that needed correction**:

1. `Fin.castSucc_castSucc` — does not exist in Mathlib (the
   composition `k.castSucc.castSucc` is not a named simp lemma).
   Replaced with explicit `Fin.succ_castSucc` rewrites to bridge
   `k.castSucc.succ = k.succ.castSucc` between consecutive prefix
   restrictions.

2. `add_le_add_left ih_amplified _` — Lean's `add_le_add_left` in
   the elaboration context expected a form `_ + c ≤ _ + c` rather
   than the documented `c + _ ≤ c + _`, producing a type mismatch.
   Replaced with `linarith [ih_amplified]`, which doesn't depend on
   argument order.

3. `← pow_succ` — the pattern `a^n * a` did not match the goal's
   `a * a^m * b`; the correct lemma is `pow_succ'` which gives
   `a^(n+1) = a * a^n`. Replaced; opened the multiplication
   associativity explicitly with `← mul_assoc`.

4. `congr 2` on `(1 + h L)^(m + 1 - 1 - k.val) * δ k`
   ≟ `(1 + h L)^(m - k.val) * δ k`: `m + 1 - 1 - k.val = m - k.val`
   is definitionally true (Nat subtraction simplifies), so `congr 2`
   already closed the goal; the subsequent `omega` failed with "no
   goals to be solved." Replaced `congr 2; omega` with `rfl`.

5. `congr 1` after `rw [Fin.sum_univ_castSucc]` was too aggressive
   (split the sum-equation into two non-matching sub-goals).
   Replaced with two explicit `have` blocks (`h_last`, `h_sum_eq`)
   that prove the last-term and sum-restriction identities
   separately, then `rw [h_last, h_sum_eq]`.

## Discovery

* **`Fin.succ_castSucc`** is the key Mathlib lemma for bridging
  prefix restrictions through `Fin (m+1) ↪ Fin (m+2)`. Statement:
  `k.castSucc.succ = k.succ.castSucc` for `k : Fin m`. Use it to
  push restricted-predicate-witness hypotheses into the unrestricted
  form when needed (or vice versa).
* **`Fin.succ_last`** is real (referenced in Mathlib's JordanHolder
  and SuccPred files): `(Fin.last m).succ = Fin.last (m + 1)`.
* **`pow_succ'` vs `pow_succ`**: `pow_succ` gives `a^(n+1) = a^n * a`
  (right-associative); `pow_succ'` gives `a^(n+1) = a * a^n`
  (left-associative). The latter is needed when amplifying an
  inductive hypothesis by a contraction factor on the left.
* **`congr 1` / `congr 2` are slippery on Nat-subtraction
  exponents**: when the subtraction `m + 1 - 1 - k.val` can
  definitionally reduce, `congr` may close some sub-goals
  spontaneously, breaking subsequent fixed-position tactics. Prefer
  explicit `Finset.sum_congr` with a per-term `have` block.
* **`Classical.choose` definitional-equality concern (refuted in
  practice)**: not tested directly this cycle — Option (b) was
  chosen up-front per the strategy's recommendation. The
  `lem_319A_extract` repackaging adds ~135 LOC but is mechanical and
  guarantees `L_dag` is uniform across applications.

## Suggested next approach

**Cycle 247 — Phase 2 of `thm:319B`**: specialise `δ_k ≤ C h^{p+1}`
and bound the geometric sum to recover the headline:

```
‖y(x_n) − y_n‖ ≤  (exp(L^†(x_n − x_0)) − 1) / L^†  · C h^p   if L^† > 0
‖y(x_n) − y_n‖ ≤  (x_n − x_0) · C h^p                       if L^† = 0
```

Key ingredients:

1. Use `Real.add_one_le_exp` (or equivalent) to bound
   `(1 + h L^†)^n ≤ exp(L^† h n)`.
2. Compute the geometric sum
   `∑_{k=0}^{n-1} (1 + h L^†)^{n-1-k} = ((1 + h L^†)^n − 1)/(h L^†)`
   when `L^† > 0`; when `L^† = 0` the sum is just `n`.
3. Case-split on `L^† > 0` vs `L^† = 0`, since the closed-form
   denominator vanishes in the limiting case.
4. Pull `C h^{p+1}` out of the sum and use `n h ≤ x_n − x_0`.

Estimated LOC: ~150–200 (split into two helper lemmas for the
geometric-sum and the `(1 + x)^n ≤ exp(nx)` bound, then the
case-split combine).
