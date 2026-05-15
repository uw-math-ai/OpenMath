# Cycle 291 Results

## Worked on

`lem:342A` Butcher §342 (342f) general three-term recurrence — **Phase
A.2 starter lemmas** (F.1, F.2, and the optional combined statement
P3) per cycle 290's strategy and the manual closure plan at
`.prover-state/issues/lem_342A_342f_manual_closure_plan.md` §5.

Specifically, shipped three new axiom-clean theorems at the end of
`OpenMath/Chapter3/Section342.lean`:

- `recurrence_residual_orthogonal_first_term` (F.1): the first
  summand `(n : ℝ) • P_n^*` of the cycle 290 residual is orthogonal
  to `P_k^*` for every `k < n`.
- `recurrence_residual_orthogonal_third_term` (F.2): the third
  summand `C((n - 1 : ℕ) : ℝ) · P_{n-2}^*` is orthogonal to `P_k^*`
  for every `k ≤ n - 3`.
- `recurrence_residual_orthogonal_easy` (P3): the sum of the first
  and third summands is orthogonal to `P_k^*` for every `k ≤ n - 3`.

## Approach

Manual closure path only — no Aristotle submissions this cycle (the
cycle 289 three-stall protocol closed the door on `(342f)`-direct
search-based closure).

### Step 0 (preflight)

Re-read `butcherShiftedLegendre_orthogonal` (cycle 277,
`Section342.lean:1314`). Confirmed:

- Argument order: `{m n : ℕ} (hmn : m ≠ n)`.
- Integrand: `P_m.eval x * P_n.eval x` (in that order).
- Integration variable / endpoints: `(0 : ℝ)..1`.

This means:

- F.1 with `∫ (P_n.eval x) * (P_k.eval x) = 0` for `k < n` needs
  `m = n, n = k`, hypothesis `n ≠ k` i.e. `hk.ne'`.
- F.2 with `∫ (P_{n-2}.eval x) * (P_k.eval x) = 0` for `k ≤ n - 3`
  needs `m = n - 2, n = k`, hypothesis `n - 2 ≠ k`. Given
  `hn : 3 ≤ n` and `hk : k ≤ n - 3`, `omega` discharges this
  directly.

### Step 1 — F.1 (`recurrence_residual_orthogonal_first_term`)

5-line tactic body:

1. `simp only [Polynomial.eval_smul, smul_eq_mul]` rewrites
   `((n : ℝ) • P_n).eval x` to `(n : ℝ) * P_n.eval x`.
2. `simp_rw [mul_assoc]` re-associates the integrand from
   `(n * P_n.eval x) * P_k.eval x` to
   `n * (P_n.eval x * P_k.eval x)`.
3. `rw [intervalIntegral.integral_const_mul]` pulls the `(n : ℝ)`
   constant out of the integral.
4. `rw [butcherShiftedLegendre_orthogonal hk.ne']` substitutes the
   inner integral with `0`.
5. `mul_zero` closes the remaining `(n : ℝ) * 0 = 0` (folded into
   the same `rw` chain).

### Step 2 — F.2 (`recurrence_residual_orthogonal_third_term`)

Mirror of step 1, with `Polynomial.eval_C` in place of
`Polynomial.eval_smul`/`smul_eq_mul`:

1. `simp only [Polynomial.eval_mul, Polynomial.eval_C]` rewrites
   `(C ((n - 1 : ℕ) : ℝ) * P_{n-2}).eval x` to
   `((n - 1 : ℕ) : ℝ) * P_{n-2}.eval x`.
2. `simp_rw [mul_assoc]` re-associates as above.
3. `rw [intervalIntegral.integral_const_mul]` pulls the constant.
4. `have h_ne : n - 2 ≠ k := by omega` discharges the
   orthogonality hypothesis using `hn : 3 ≤ n` + `hk : k ≤ n - 3`.
5. `rw [butcherShiftedLegendre_orthogonal h_ne, mul_zero]` closes.

### Step 3 — P3 (`recurrence_residual_orthogonal_easy`)

Combined statement via `intervalIntegral.integral_add`. The
integrability witnesses are derived from `Polynomial.continuous` +
`Continuous.mul` + `.intervalIntegrable`:

```lean
have hf_int : IntervalIntegrable
    (fun x : ℝ => ((n : ℝ) • butcherShiftedLegendre n).eval x *
                  (butcherShiftedLegendre k).eval x)
    MeasureTheory.volume 0 1 :=
  (((((n : ℝ) • butcherShiftedLegendre n)).continuous.mul
    (butcherShiftedLegendre k).continuous).intervalIntegrable _ _)
```

After `simp only [Polynomial.eval_add, add_mul]` to split the
integrand and `rw [intervalIntegral.integral_add hf_int hg_int]` to
split the integral, apply F.1 (with `hk_lt : k < n := by omega` from
`hn + hk`) and F.2 directly. Closes with `add_zero`.

## Result

**SUCCESS** — All three theorems shipped axiom-clean.

Verifications:

- `lake env lean OpenMath/Chapter3/Section342.lean` → exit 0.
- `lake env lean OpenMath/Chapter3.lean` → exit 0.
- `grep -c sorry OpenMath/Chapter3/Section342.lean` → `0`.
- `lean_verify` MCP on each new theorem:
  - `recurrence_residual_orthogonal_first_term`:
    `[propext, Classical.choice, Quot.sound]`.
  - `recurrence_residual_orthogonal_third_term`:
    `[propext, Classical.choice, Quot.sound]`.
  - `recurrence_residual_orthogonal_easy`:
    `[propext, Classical.choice, Quot.sound]`.

LOC tally: ~50 LOC including docstrings (target was ~35–50 LOC, so
inside budget). The optional P3 deliverable shipped because P1+P2
closed in one pass with no decomposition needed.

## Faithfulness check

### `recurrence_residual_orthogonal_first_term`

- **Entity ID**: not a textbook entity; helper lemma toward
  `lem:342A` (342f) per the cycle 289 manual closure plan
  (`.prover-state/issues/lem_342A_342f_manual_closure_plan.md` §5
  Phase A.2 component F.1).
- **Textbook statement** (Butcher §342, p. 236, paraphrased — this
  is a helper, not a textbook entity):
  > A simple calculation shows that `Q` is orthogonal to `P_k^*` for
  > `k < n − 2`.
  The F.1 component is the first summand-by-summand check:
  `⟨n · P_n^*, P_k^*⟩ = n · ⟨P_n^*, P_k^*⟩ = 0` for any `k < n`,
  since `P_n^*` is orthogonal to all lower-degree `P_k^*`.
- **Lean statement captures**: same content. The proof uses cycle
  277's `butcherShiftedLegendre_orthogonal hk.ne'` directly; no
  smuggling, no weakening, no strengthening.
- **Hypotheses match**: only `hk : k < n` is required. The strategy
  suggested `(hn : 1 ≤ n)`, but on reflection that hypothesis is
  superfluous — `hk : k < n` already implies `0 < n` if needed,
  and the proof never uses `hn` at all. Dropped to keep the
  statement minimal.
- **No definition smuggling, no tautology, no identity proof**.

### `recurrence_residual_orthogonal_third_term`

- **Entity ID**: not a textbook entity; helper lemma toward
  `lem:342A` (342f), component F.2.
- **Textbook statement** (paraphrased from Butcher §342, p. 236):
  > `Q := n P_n^* − (2n − 1)(2x − 1) P_{n-1}^* + (n − 1) P_{n-2}^*`
  > is orthogonal to `P_k^*` for `k < n − 2`.
  The F.2 component handles `⟨(n − 1) · P_{n-2}^*, P_k^*⟩ = 0` when
  `k ≤ n - 3` (i.e., strictly less than `n - 2`).
- **Lean statement captures**: same content. The Lean statement
  carries the scalar as `C ((n - 1 : ℕ) : ℝ) *
  butcherShiftedLegendre (n - 2)` (a `Polynomial ℝ` multiplication
  by a constant polynomial), which matches the residual structure
  set up in cycle 290's `recurrence_residual_natDegree_lt`.
- **Hypotheses match**: `hn : 3 ≤ n` + `hk : k ≤ n - 3` are exactly
  what the textbook needs to ensure `n - 2 ≠ k`. Without `hn`,
  nat-truncation collapse at `n < 3` (e.g. `n = 2, k = 0, n - 3 = 0,
  n - 2 = 0 = k`) would break orthogonality. Documented hypothesis.
- **No definition smuggling, no tautology, no identity proof**.

### `recurrence_residual_orthogonal_easy`

- **Entity ID**: not a textbook entity; combined helper lemma
  toward `lem:342A` (342f), Phase A.2 (easy two summands).
- **Textbook statement** (paraphrased): same Butcher §342 quote as
  F.2 above, restricted to the partial sum
  `A + C := (n · P_n^*) + (n − 1) · P_{n-2}^*` (without the F.3
  cross-term).
- **Lean statement captures**: a strict consequence of F.1 + F.2
  via `intervalIntegral.integral_add`. The integrand is
  `((n : ℝ) • P_n + C (n - 1) · P_{n - 2}).eval x · P_k.eval x`,
  which is exactly the first plus third summand of the cycle 290
  residual (the middle term — the F.3 cross-term — is **not**
  included). No smuggling.
- **Hypotheses match**: `hn : 3 ≤ n` + `hk : k ≤ n - 3` (same as
  F.2). F.1's `hk_lt : k < n` is derived from these via `omega`.
- **No tautology, no identity proof, no excess hypothesis**.

## Dead ends

### None this cycle

P1 closed in 5 lines on the first attempt; P2 closed in 5 lines on
the first attempt; P3 closed in ~15 lines on the first attempt
(integrability witnesses + `integral_add` + the two component
applications). The strategy's tactic recipe was exactly correct
modulo a minor adjustment: instead of `rw [show ... from by funext x;
ring]` to re-associate the integrand, I used `simp_rw [mul_assoc]`,
which is cleaner and avoids the explicit lambda. The strategy
itself noted this as an option ("If the `show ... from by funext`
rewrite is awkward, try `simp_rw [mul_assoc]` first") so this was
not a dead end but a planned alternative.

## Discovery

### `simp_rw [mul_assoc]` is the cleanest re-association for
constant pull-out inside an integral

When the goal is `∫ x, r * f x * g x = 0`, `simp_rw [mul_assoc]`
turns the integrand into `r * (f x * g x)` so that
`intervalIntegral.integral_const_mul` fires directly. This is
cleaner than the `show ... = ... from by funext x; ring` pattern
since it avoids spelling out the integrand as a lambda — the
re-association happens at every multiplication site inside the
integral automatically.

### `Polynomial.continuous _ |>.mul _ |>.intervalIntegrable _ _`
is the canonical integrability incantation for `eval`-product
integrands

For an integrand of the form `(P.eval x) * (Q.eval x)`, the
canonical Mathlib chain is:

```lean
(P.continuous.mul Q.continuous).intervalIntegrable _ _
```

where `P.continuous : Continuous (fun x => P.eval x)` via dot
notation on `Polynomial.continuous`. This pattern is reusable for
Phase A.2 F.3 and Phase A.3 integrability witnesses.

### `hk.ne'` vs `hk.ne` for `<`-to-`≠` upgrade

For `hk : k < n`, `hk.ne` gives `k ≠ n` and `hk.ne'` gives `n ≠ k`.
The strategy correctly identified `hk.ne'` for the F.1 case
(needing `n ≠ k` since the cycle 277 lemma's argument order is
`m ≠ n` with `m = n` in our application). For F.2 the orientation
is different (`n - 2 ≠ k`, not coming from a `<`-hypothesis), so I
introduced `h_ne : n - 2 ≠ k := by omega` directly.

### Strategy's `(hn : 1 ≤ n)` hypothesis on F.1 is unnecessary

The strategy's signature for F.1 included `(hn : 1 ≤ n)`, but the
proof doesn't use this hypothesis — `hk : k < n` alone suffices
(`k = 0` is even allowed when `n ≥ 1` since `hk` rules out `n = 0`
via `k < n`). Dropped the hypothesis to keep the statement minimal.
This is a minor strengthening of the deliverable.

## Suggested next approach

### Cycle 292: Phase A.2 F.3 cross-term

The remaining Phase A.2 deliverable is the cross-term orthogonality

```lean
theorem recurrence_residual_orthogonal_cross_term (n : ℕ) (hn : 3 ≤ n)
    {k : ℕ} (hk : k ≤ n - 3) :
    ∫ x in (0 : ℝ)..1,
      (Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
       (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
       butcherShiftedLegendre (n - 1)).eval x *
      (butcherShiftedLegendre k).eval x = 0
```

Per the issue file §5 and cycle 290 task results §"Suggested next
approach", the route is:

1. **Bridge `2X - 1 = butcherShiftedLegendre 1`**. Via cycle 273's
   `butcherShiftedLegendre_one` (one-line lemma; verify sign
   convention since Butcher's `P_1^* = 2x - 1` matches).
2. **Constant pull-out** of `((2 * n - 1 : ℕ) : ℝ)` via the same
   `intervalIntegral.integral_const_mul` pattern.
3. **Symmetry of the inner product**: `∫ (P_1 · P_{n-1}).eval x ·
   P_k.eval x = ∫ P_{n-1}.eval x · (P_1 · P_k).eval x` via
   commutativity of `*` in the integrand. Note
   `(P_1 * P_k).natDegree ≤ 1 + k ≤ n - 2`.
4. **Basis-span lemma** (reusable for Phase A.3): for any polynomial
   `q : Polynomial ℝ` with `q.natDegree < n - 1`,
   `∫ P_{n-1}^*.eval x · q.eval x = 0`. This requires expressing
   `q` as a linear combination of `{P_0^*, …, P_{n-2}^*}` and
   applying `butcherShiftedLegendre_orthogonal` summand-by-summand.
   `Polynomial.degreeLT ℝ n` is the right Mathlib structure to
   leverage; basis-of-orthogonal-polynomials results may already
   exist in Mathlib (worth a `lean_leansearch` upfront).

LOC budget: 100–150 LOC for F.3 + the basis-span helper. The
helper is also load-bearing for Phase A.3 so the budget pays
double.

### Cycle 293+: Phase A.3 basis-span conclusion

Combine cycle 290's `recurrence_residual_natDegree_lt` + cycles
291–292's orthogonality of the residual `Q` against `P_k^*` for
`k ≤ n - 2` (or `k ≤ n - 3` if the parity strengthening is
deferred) + the basis-span lemma to conclude `Q = 0`, i.e. (342f)
in its general form. ~60–100 LOC per the issue file §6.

### Cycle 294: final closure of (342f) + `lean_status.json` bump

Once `Q = 0` is in hand, extract the textbook statement
`n · P_n^*(x) = (2x − 1)(2n − 1) P_{n-1}^*(x) − (n − 1) P_{n-2}^*(x)`
from `Q = 0` (one `rw` chain). Bump `extraction/formalization_data/
lean_status.json` row for `lem:342A` once all of (342a)…(342g)
close. (342g) — distinct real zeros — is the only remaining
sub-property after (342f); cycle 282's scoping doc
`.prover-state/issues/lem_342A_g_zeros_scoping.md` is ready for
the planner to schedule.

### LOC ladder

Cycle 289 ~80 LOC (binomial helper) + Cycle 290 ~140 LOC (residual
degree theorem) + Cycle 291 ~50 LOC (Phase A.2 easy starter
lemmas) = ~270 LOC toward (342f) so far. Phase A.2 F.3 + Phase A.3
+ final = ~200–300 LOC remaining. Total budget tracking matches the
issue file §6 estimate of 370–570 LOC.
