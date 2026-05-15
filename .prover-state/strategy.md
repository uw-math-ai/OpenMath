# Strategy — Cycle 292

## §A. State recap

* Repo HEAD: `a7b59bb Cycle 291 — §342 (342f) Phase A.2 starter lemmas
  (F.1, F.2, easy combination)`.
* Sorry count: **0** across `OpenMath/`.
* `OpenMath/Chapter3/Section342.lean`: ~2123 LOC, axiom-clean. Phase A.1
  (cycles 289+290) and Phase A.2 easy starter lemmas (cycle 291) shipped.
* `lem:342A` (342f) general three-term recurrence: Phase A.1 closed; Phase
  A.2 partially closed (F.1, F.2, easy combination); Phase A.2 F.3 cross-term
  and Phase A.3 basis-span conclusion remaining.
* No Aristotle projects pending. `c8b8f138` (cycle 282) and `efe4940e`
  (cycle 285) both cancelled per the three-stall protocol (cycles 283/284/285
  and 287/288/289 respectively). **Do NOT resubmit (342f) to Aristotle.**
* Recent supervisor scores (encouraging trend):
  cycle 287 = +1, 288 = +2, 289 = +1, 290 = +2, 291 = +2.

## §B. §441 GPFS skip

44th consecutive timeout expected on `OpenMath/Chapter4/Section441.lean`
smoke test (see `.prover-state/issues/cycle_182_gpfs_slowness.md`). **Do
not run the smoke test this cycle.** Section441-side work (Phase C.2+ of
`lem:441A`) remains GPFS-blocked.

## §C. Cycle 292 deliverables (Phase A.2 F.3 cross-term)

### §C.0 Read the issue file first

Before writing any Lean, re-read these three locations:
1. `.prover-state/issues/lem_342A_342f_manual_closure_plan.md` §5
   "Phase A.2" and §10 "Cycle 291 update".
2. Cycle 291's `recurrence_residual_orthogonal_first_term`,
   `_third_term`, `_easy` in `OpenMath/Chapter3/Section342.lean` (the
   tail end of the file, last ~80 LOC). These are the template for F.3.
3. Cycle 273's `butcherShiftedLegendre_one` (also in Section342.lean,
   the n=1 explicit form). It is the bridge `P_1^* = C 2 · X - C 1`
   that the F.3 proof routes through.

### §C.1 P1 — Basis-span helper (~50–80 LOC)

Ship the **reusable** orthogonality lemma needed for both F.3 and Phase
A.3:

```lean
theorem butcherShiftedLegendre_orthogonal_to_lower_degree
    (m : ℕ) (q : Polynomial ℝ) (hq : q.natDegree < m) :
    ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre m).eval x * q.eval x = 0
```

**Approach (induction on `q.natDegree`)**:

1. Strong induction on `d := q.natDegree`. Use `Nat.strong_induction_on
   d` or pattern-match by cases on `Nat.lt_or_eq_of_le`.
2. **Base case `d = 0`**: `q` is a constant, so
   `q = Polynomial.C (q.coeff 0)`. Then the integrand becomes
   `(P_m^*).eval x * q.coeff 0` and pulls the constant out:
   ```lean
   simp only [Polynomial.eq_C_of_natDegree_eq_zero hq_eq_zero,
              Polynomial.eval_C]
   simp_rw [mul_comm _ (q.coeff 0)]
   rw [intervalIntegral.integral_const_mul]
   -- Goal: q.coeff 0 * (∫ ... P_m^*.eval x * 1) = 0
   -- Note ∫ P_m^* = ∫ P_m^* · P_0^* (since P_0^* = 1) which = 0 for m ≥ 1.
   ```
   Use `butcherShiftedLegendre_zero` (cycle 273, `P_0^* = C 1`) to
   express `1` as `(P_0^*).eval x`, then apply
   `butcherShiftedLegendre_orthogonal` with `hm.ne'` (where `hm : 0 < m`
   follows from `q.natDegree = 0 < m`).
3. **Inductive step `d > 0`**: Express
   `q = (q - C c · P_d^*) + C c · P_d^*` where `c` is chosen so the
   leading-`X^d` coefficient cancels. Specifically
   `c := q.coeff d / (butcherShiftedLegendre d).leadingCoeff` (cycle 281
   gives `leadingCoeff = C(2d, d) > 0` so the division is well-defined).
   Then `(q - C c · P_d^*).natDegree < d`, IH applies. The second summand
   `∫ P_m^* · C c · P_d^*.eval x = c · ∫ P_m^* · P_d^* = 0` directly
   via `butcherShiftedLegendre_orthogonal` (since `d < m` ⇒ `d ≠ m`).

**Mathlib hooks to verify with `lean_local_search` first**:
- `Polynomial.eq_C_of_natDegree_eq_zero` (or similar — verify name).
- `Polynomial.natDegree_sub_lt` / `Polynomial.degree_sub_lt` (the
  latter already used in cycle 290).
- `butcherShiftedLegendre_zero` and `butcherShiftedLegendre_one`
  (cycle 273) and `butcherShiftedLegendre_leadingCoeff` (cycle 281).
- `intervalIntegral.integral_add` (cycle 291 recipe) for splitting
  the residual sum; integrability via `Polynomial.continuous.mul`.

**Fallback if leading-coefficient subtraction proves fiddly**:
Expand `q` directly in the monomial basis via `Polynomial.as_sum_range`,
then use linearity of `intervalIntegral` to split into a finite sum of
`∫ P_m^* · X^k * (q.coeff k)` for `k = 0..d`. Reduce to showing
`∫ P_m^* · X^k = 0` for each `k < m` (inner basis-span helper on
monomials only, which has the same recursion structure but with
simpler polynomial arithmetic). ~80 LOC instead of ~50.

### §C.2 P2 — F.3 cross-term (~30–50 LOC, given P1)

```lean
theorem recurrence_residual_orthogonal_cross_term (n : ℕ) (hn : 3 ≤ n)
    {k : ℕ} (hk : k ≤ n - 3) :
    ∫ x in (0 : ℝ)..1,
      (Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
       (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
       butcherShiftedLegendre (n - 1)).eval x *
      (butcherShiftedLegendre k).eval x = 0
```

**Approach** (uses P1):

1. **Constant pull-out** of `((2 * n - 1 : ℕ) : ℝ)` using the cycle 291
   F.2 pattern (`Polynomial.eval_mul, Polynomial.eval_C` + `simp_rw
   [mul_assoc]` + `intervalIntegral.integral_const_mul`).
2. **Commute the integrand** so `P_{n-1}^*` is on the left and the
   "lower-degree" polynomial `(C 2 · X - C 1) · P_k^*` is on the right.
3. **Apply P1** with `m := n - 1` and
   `q := (C 2 · X - C 1) * butcherShiftedLegendre k`. Need
   `q.natDegree < n - 1`:
   - `(C 2 · X - C 1).natDegree = 1` via `compute_degree!` or direct.
   - `(butcherShiftedLegendre k).natDegree = k` (cycle 273).
   - `(P_1-form * P_k^*).natDegree ≤ 1 + k ≤ 1 + (n - 3) = n - 2 <
     n - 1`, discharged by `Polynomial.natDegree_mul_le` + `omega`.
4. The integrand `(P_{n-1}^*).eval x * (q.eval x)` matches P1's
   conclusion modulo the `Polynomial.eval_mul` expansion of `q.eval x`.
   Use the lemma reversed: `Polynomial.eval_mul.symm` to fold the
   commuted scalar product back to `q.eval x`.

**Pitfall to watch**: `Polynomial.eval_mul` only applies to polynomial
products, not to `ℝ`-products. Keep the integrand in
`(polynomial).eval x * (polynomial).eval x` form for as long as
possible, only expanding to scalar multiplication when invoking
`integral_const_mul`. The cycle 291 F.2 proof has the right template
(`Polynomial.eval_mul, Polynomial.eval_C` simp set).

**Bridge `2X - 1 ↔ P_1^*` (optional cleaner route)**: cycle 273's
`butcherShiftedLegendre_one : butcherShiftedLegendre 1 = C 2 · X - C 1`
lets you rewrite `(C 2 · X - C 1)` as `butcherShiftedLegendre 1`, then
P1's hypothesis `q.natDegree < n - 1` becomes
`(butcherShiftedLegendre 1 * butcherShiftedLegendre k).natDegree
≤ 1 + k < n - 1`. This makes the connection to Butcher's argument
("substitute 2X - 1 = P_1^*") explicit; cosmetic but recommended.

### §C.3 P3 stretch — Full residual orthogonality (~15–25 LOC)

If P1 + P2 both close in budget, ship the combined orthogonality of the
**full** residual (F.1 + F.2 + F.3) against `P_k^*` for `k ≤ n - 3`:

```lean
theorem recurrence_residual_orthogonal (n : ℕ) (hn : 3 ≤ n)
    {k : ℕ} (hk : k ≤ n - 3) :
    ∫ x in (0 : ℝ)..1,
      (((n : ℝ) • butcherShiftedLegendre n
        - Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
          (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
          butcherShiftedLegendre (n - 1)
        + Polynomial.C ((n - 1 : ℕ) : ℝ) *
          butcherShiftedLegendre (n - 2)).eval x) *
      (butcherShiftedLegendre k).eval x = 0
```

This is the exact `Q` polynomial from cycle 290's
`recurrence_residual_natDegree_lt`. Closure: split via
`intervalIntegral.integral_sub` and `intervalIntegral.integral_add`
(integrability witnesses per the cycle 291 P3 pattern), then apply
F.1, F.2 (cycle 291), and F.3 (P2 above) summand-by-summand. The
`-` in front of the F.3 cross-term contributes `-0 = 0`.

If P3 lands, Phase A.2 of the manual closure plan is **fully closed**,
and cycle 293 can move to Phase A.3 (basis-span conclusion: combine
`natDegree Q < n` from cycle 290 with the full orthogonality from P3
to conclude `Q = 0`).

### §C.4 Order of operations

1. P0 hygiene: re-read cycle 291's three theorems, the issue file §5,
   cycle 273's `butcherShiftedLegendre_one`/`_zero`, and cycle 281's
   `butcherShiftedLegendre_leadingCoeff`. ~5–10 min.
2. Verify Mathlib hook names with `lean_local_search`:
   `Polynomial.eq_C_of_natDegree_eq_zero`, `Polynomial.natDegree_sub_lt`,
   `Polynomial.as_sum_range` (or the fallback variant). ~5 min.
3. Ship P1 (basis-span helper). ~50–80 LOC.
4. Ship P2 (F.3). ~30–50 LOC, depending heavily on whether the
   commute-then-apply-P1 pattern fires cleanly.
5. Verify both axiom-clean via `lean_verify`.
6. If budget remains, ship P3 (full residual orthogonality). ~15–25 LOC.
7. `lake env lean OpenMath/Chapter3/Section342.lean` and
   `lake env lean OpenMath/Chapter3.lean` to confirm aggregator builds.
8. Tautology-scanner sanity:
   `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section342.lean`
   should return zero hits.

## §D. What NOT to do this cycle

* **Do NOT resubmit (342f) to Aristotle.** Three consecutive 20% stalls
  in cycles 287/288/289 closed off the search-based path; the cycle 289
  three-stall protocol explicitly forbids further submissions for this
  target.
* **Do NOT pursue Möbius / Pascal-identity manual closures.** Cycle
  273 documented those paths as infeasible without (342a) infrastructure
  (which cycle 277 supplied) and Pascal-style binomial identities
  outside `ring`'s normal form. Path A (degree-bound + orthogonality
  basis, already in progress) is the clean route.
* **Do NOT extend the empirical recurrence ladder past `n = 11`.** Cycle
  288's `_recurrence_eleven` is the documented stopping point. Further
  rungs provide no new information beyond what's already established
  (cycle 285 onwards).
* **Do NOT touch `Section441.lean` or attempt its smoke test.** GPFS
  remains pathologically slow on §441's transitive Mathlib closure;
  43+ consecutive timeouts. Continue skipping per
  `.prover-state/issues/cycle_182_gpfs_slowness.md`.
* **Do NOT introduce `sorry` / `axiom` / `constant`.** Phase A.2 F.3 +
  basis-span helper are within reach axiom-clean; the cycle 200/201
  rollback precedent (sorry-first scaffolds without a credible
  single-cycle close) and cycle 149/150 rollback both forbid sorry
  scaffolds. If P1 stalls (basis-span helper proves too costly), ship
  the cycle clean with whatever fragment compiled, rather than
  introducing a sorry.
* **Do NOT raise `maxHeartbeats` above 200000.** If P1's induction blows
  up, decompose into a `pow_orthogonal_helper : ∀ d, d < m →
  ∫ P_m^*.eval x * x^d = 0` as a private intermediate lemma, and
  consume it via `Polynomial.as_sum_range`. Cycle 273's `_zero`/`_one`
  + cycle 281's `_leadingCoeff` give the inductive ingredients.
* **Do NOT modify `scripts/autonomous_loop.py`.** Per CLAUDE.md and the
  standing `phantom_commit_verdict_pattern.md` /
  `tautology_scanner_false_positives.md` issues, scanner / prompt-builder
  bugs are loop-maintainer territory.
* **Do NOT use `:= h_<name>` or `exact h_<name>`** style closers that
  start with `h_` (the underscore-after-h pattern). The tautology
  scanner false-positives on these (cycle 014/015 documented). Use
  `hname` (no underscore after `h`) for any new hypothesis names.
* **Do NOT generalise the basis-span helper to abstract `R : Type*`
  rings.** Keep it specialised to `Polynomial ℝ` matching cycle 277's
  `butcherShiftedLegendre_orthogonal`. Abstraction is out of scope.

## §E. Failed approaches (do NOT repeat)

From cycle history and prior attempts:

* **`Polynomial.ext` skeleton for closed-form polynomial identities**
  (cycles 172/173): produces unmanageable goals when `Polynomial.C`
  arithmetic is involved. Use `Polynomial.funext` + `ring` (cycle 180
  recipe) for polynomial identities, NOT `Polynomial.ext`.
* **`simp [...]; ring` one-shot for matrix-determinant + polynomial
  expansion** (cycle 148/150 stepping stones): blows past
  `maxHeartbeats` on n ≥ 6. Decompose into named private helpers.
* **`Finset.sum_le_sum_nbij'`** (cycle 050): does not exist in Mathlib.
  Use `← Finset.sum_image` + `Finset.sum_le_sum_of_subset_of_nonneg`.
* **`rw [hsymm]` where `hsymm` is universally-quantified at the wrong
  binder level** (cycle 169): metavariable instantiation rewrites
  multiple occurrences in opposite directions. Instantiate the lemma
  at the specific arguments first via `have := lemma α β` then `rw [...]`.
* **Aristotle on (342f)** (cycles 282–289): three consecutive 20%
  stalls. Manual closure only.
* **Direct (342f) via `Polynomial.ext` or `Polynomial.funext` + `ring`**
  (cycle 273): requires Pascal-style binomial identities that `ring`
  cannot fold. Path A (degree-bound + orthogonality basis) sidesteps
  this entirely.

## §F. Backup plan — if P1 stalls

If `butcherShiftedLegendre_orthogonal_to_lower_degree` proves harder
than expected (e.g. `Polynomial.eq_C_of_natDegree_eq_zero`'s exact
name doesn't match Mathlib's API, or the leading-coefficient
subtraction step requires non-trivial side conditions):

* **Cycle 292 minimal ship**: stop after P1 reaches a stuck point,
  revert the half-baked attempt, and instead ship a **direct monomial
  basis-span helper**:
  ```lean
  theorem butcherShiftedLegendre_orthogonal_pow
      (m k : ℕ) (hk : k < m) :
      ∫ x in (0 : ℝ)..1,
        (butcherShiftedLegendre m).eval x * x ^ k = 0
  ```
  This is structurally simpler (induction on `k` using cycle 273's
  small-`n` explicit forms — but `X^k` as a polynomial is also
  a sum of `P_j^*` for `j ≤ k`, so the same reasoning underlies it).
  The saving is mostly in framing. Defer the general `q : Polynomial ℝ`
  form to cycle 293.

* **Cycle 292 alternative ship**: pivot to a different §342 deliverable
  entirely. (342g) `n` distinct real zeros has a scoping doc at
  `.prover-state/issues/lem_342A_g_zeros_scoping.md`. The argument:
  form `Q := ∏ᵢ (X − xᵢ)` over the sign-change zeros (count `k < n`),
  then `∫₀¹ P_n^* · Q = 0` by (342a) but ≠ 0 by sign-constancy of
  the integrand. LOC budget ~150 per the scoping doc; some Mathlib
  hooks (`Polynomial.roots.toFinset`, sign-change extraction) are
  non-trivial. Lower-priority than F.3 but a viable cycle 292 pivot
  if P1 fails entirely.

## §G. Cycle 293+ outlook

* If cycle 292 ships P1 + P2 (Phase A.2 F.3): cycle 293 closes Phase A.2
  via P3-equivalent and Phase A.3 (combine `Q.natDegree < n` from
  cycle 290 with full orthogonality to conclude `Q = 0`). ~60–100 LOC.
* If cycle 292 ships P1 + P2 + P3: cycle 293 ships Phase A.3 directly.
  ~60–100 LOC.
* Cycle 294: extract the headline (342f) `n • P_n^* = (2n-1)(2X-1) ·
  P_{n-1}^* - (n-1) · P_{n-2}^*` from `Q = 0` via one `linear_combination`
  step. Bump `lean_status.json` row for `lem:342A` once (342g) also
  closes (per `lem_342A_g_zeros_scoping.md`); until then status remains
  `partial`.
* Cycle 295+: (342g) closure per the scoping doc. Multi-cycle.

## §H. Files the cycle 292 worker will touch

* `OpenMath/Chapter3/Section342.lean` — append the new theorems
  (basis-span helper + F.3, plus P3 stretch). Do NOT modify cycles
  271–291's theorems; only append.
* `.prover-state/issues/lem_342A_342f_manual_closure_plan.md` — append
  a "Cycle 292 update" subsection summarising deliverables.
* `.prover-state/task_results/cycle_292.md` — write per CLAUDE.md
  template.
* `plan.md` — update the `lem:342A` row's recurrence-progress narrative
  (the long status text under `[~] lem:342A`). Do NOT bump status to
  `[x]` yet; still partial until (342f) general theorem AND (342g)
  close.

## §I. Pre-flight checklist (do before writing Lean)

1. `git log -1 --format='%H %s'` — confirm HEAD is `a7b59bb`.
2. `wc -l OpenMath/Chapter3/Section342.lean` — confirm baseline ~2123
   LOC.
3. `grep -c sorry OpenMath/Chapter3/Section342.lean` — confirm `0`.
4. `lean_local_search "Polynomial.eq_C_of_natDegree_eq_zero"` — verify
   exact Mathlib name; if absent, search for
   `"Polynomial.C_eq_natCast"` or `"natDegree_eq_zero_iff_degree_le_zero"`
   and adjust the base-case approach.
5. `lean_local_search "Polynomial.natDegree_sub_lt"` — verify name for
   the inductive subtraction step.
6. `lean_hover_info` on `butcherShiftedLegendre_one` and `_zero` —
   confirm the exact statements before consuming them.

## §J. End-of-cycle reminders

* Run `lake env lean OpenMath/Chapter3/Section342.lean` AND
  `lake env lean OpenMath/Chapter3.lean` before commit.
* Run `lean_verify` on each new theorem; axioms should be
  `[propext, Classical.choice, Quot.sound]` only.
* Confirm `grep -c sorry OpenMath/Chapter3/Section342.lean` = 0.
* `task_results/cycle_292.md` must explicitly list each new theorem
  with its faithfulness-check entry (matching cycle 291's template).
* Commit message format (matching recent cycles):
  `Cycle 292 — §342 (342f) Phase A.2 F.3 cross-term + basis-span helper.`
  (Adjust if only P1 ships, or if P3 stretch also ships.)
