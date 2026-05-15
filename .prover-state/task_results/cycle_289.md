# Cycle 289 Results

## Worked on

`lem:342A` Butcher §342 (342f) general three-term recurrence — Branch D
manual closure pivot per cycle 285 three-stall protocol.

Specifically:
1. Single-poll Aristotle project `efe4940e-0931-4fb2-8549-7eafab20d7f7`
   (general (342f) resubmission from cycle 285).
2. Cancel project if at exactly 20% (3rd consecutive stall).
3. Open manual closure plan issue file.
4. Ship Phase A.1 (a) binomial helper lemma `n_mul_choose_two_n_n_eq`
   in `OpenMath/Chapter3/Section342.lean`.

## Approach

### Priority 0: Aristotle single-poll

Polled `efe4940e` at cycle start (19:10 UTC 2026-05-15):
- `status`: `IN_PROGRESS`
- `percent_complete`: `20`
- `last_updated_at`: `2026-05-15T19:10:25Z`

This matches cycle 288's observation (20% at 18:51 UTC) and cycle
287's (20% at 18:35 UTC) — observation #3 of 3 in the cycle 285
three-stall protocol. Flat across ~35 min of compute, with no advance
beyond the cycle 287 jump from 11% → 20%.

### Branch D execution

1. **Cancelled** `efe4940e` via `mcp__aristotle__cancel_project`. Final
   status: `CANCELED`, last_updated_at 19:10:43Z.

2. **Opened** `.prover-state/issues/lem_342A_342f_manual_closure_plan.md`
   (~220 lines, mirroring cycle 180's `lem_441A_phase_C_scoping.md`
   template):
   - §1 Textbook statement
   - §2 Distilled proof (3-step: residual degree, orthogonality, basis)
   - §3 Project-hook inventory (11 shipped lemmas + Mathlib hooks)
   - §4 Gap inventory (no new Mathlib gap expected)
   - §5 Phase decomposition (A.1 → A.2 → A.3 over 3 cycles)
   - §6 Risk assessment (370–570 LOC, 3–5 cycles total)
   - §7 Cycle 290 entry point
   - §8 What NOT to do
   - §9 Cross-references
   - §10 Closes (cycle 289 update with deferral note)

3. **Shipped** Phase A.1 (a) — binomial helper. Located in
   `OpenMath/Chapter3/Section342.lean` immediately after
   `butcherShiftedLegendre_recurrence_eleven`:

   ```lean
   private lemma n_mul_choose_two_n_n_eq (n : ℕ) (hn : 2 ≤ n) :
       (n : ℝ) * (Nat.choose (2 * n) n : ℝ)
         = 2 * ((2 * n - 1 : ℕ) : ℝ)
             * (Nat.choose (2 * n - 2) (n - 1) : ℝ)
   ```

   Proof route (~80 LOC including docstring):
   - **step1** (ℕ): `Nat.choose_mul_right` with `m = 2`, `n = n` gives
     `(2*n).choose n = 2 * (2*n - 1).choose (n - 1)`. Cast to ℝ.
   - **step3** (Pascal, ℕ): `Nat.choose_eq_choose_pred_add` at
     `n' = 2*n - 1`, `k = n - 1` gives
     `(2n-1).choose (n-1) = (2n-2).choose (n-2) + (2n-2).choose (n-1)
       = C2 + C1`. Cast to ℝ.
   - **step2** (ℕ): `Nat.choose_succ_right_eq` at `(2*n - 2, n - 2)`
     gives `(2n-2).choose (n-1) * (n-1) = (2n-2).choose (n-2) * n`,
     i.e. `C1 * (n - 1) = C2 * n`. Cast to ℝ with `h_n_minus_1_real`.
   - **Bridge nat-sub to real-sub**: `h_2n_minus_1_real :
     ((2*n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1` via `Nat.cast_sub` +
     `push_cast` + `ring`.
   - **Close** via `linear_combination (-2 : ℝ) * step2` after
     rewriting the chain `step1 → step3 → h_2n_minus_1_real`. The
     coefficient `-2` is paper-derived: LHS - RHS of the goal equals
     `2 * n * C2 - 2 * (n - 1) * C1`, which differs from
     `step2_lhs - step2_rhs = C1 * (n - 1) - C2 * n` by a factor of
     `-2` (via commutativity, ring-closable).

### Phase A.1 (b) deferred

The main residual-degree theorem `recurrence_residual_natDegree_lt`
requires non-trivial degree arithmetic on
`B = C ((2n-1 : ℕ) : ℝ) * (C 2 * X - C 1) * P_{n-1}`:
1. `(C 2 * X - C 1).natDegree = 1` and `.leadingCoeff = 2`.
2. `((C 2 * X - C 1) * P_{n-1}).natDegree = n` and
   `.leadingCoeff = 2 * C(2(n-1), n-1)`.
3. `(C β * (C 2 * X - C 1) * P_{n-1}).natDegree = n` and
   `.leadingCoeff = β * 2 * C(2n - 2, n - 1)`.
4. `(n • P_n).natDegree = n` and `.leadingCoeff = n * C(2n, n)`.
5. Equality of (3)'s and (4)'s leading coefficients (cycle 289 helper).
6. `Polynomial.degree_sub_lt` ⇒ `(A - B).degree < n`.
7. `(C (n - 1)) * P_{n-2}.natDegree ≤ n - 2 < n`.
8. `natDegree_add_le` + `Nat.max_lt` ⇒ residual `natDegree < n`.

Estimated 100–150 LOC. Per the strategy's "If the LOC budget for
(a)+(b) exceeds 150, ship only (a) in cycle 289 + the issue file +
cancellation, and defer (b) to cycle 290" directive, deferred (b) to
cycle 290. Cycle 290 should open with this as the sole deliverable.

## Result

**SUCCESS** — Branch D protocol executed cleanly:

1. ✅ Aristotle `efe4940e` cancelled at 3rd stall (20% three times).
2. ✅ Manual closure plan opened
   (`.prover-state/issues/lem_342A_342f_manual_closure_plan.md`).
3. ✅ Phase A.1 (a) helper lemma shipped axiom-clean
   (`[propext, Classical.choice, Quot.sound]`) and verified via
   `mcp__lean-lsp__lean_verify`.
4. ⏭️ Phase A.1 (b) main theorem deferred to cycle 290 per LOC
   budget — issue file §10 records the deferral and revised cycle
   290 entry point.

`lake env lean OpenMath/Chapter3/Section342.lean` succeeds.
`lake env lean OpenMath/Chapter3.lean` succeeds.
`grep -c "sorry" OpenMath/Chapter3/Section342.lean` = 0.

## Faithfulness check

### `n_mul_choose_two_n_n_eq` (private helper)

- **Entity ID**: subsidiary to `lem:342A` (342f) recurrence. No
  textbook entity directly assigned; this is an arithmetic identity
  needed for the residual-degree argument in the manual closure of
  (342f).

- **Textbook claim**: For `n ≥ 2`,
  `n · C(2n, n) = 2 · (2n − 1) · C(2n − 2, n − 1)`.

  Derivation from Butcher's textbook proof (Butcher §342, p. 236):

  > The highest degree coefficients in `P_n^*` and `P_{n-1}^*` can be
  > compared so that `n P_n^*(x) − (2x − 1)(2n − 1) P_{n-1}^*(x)` is a
  > polynomial, `Q` say, of degree less than `n`.

  The leading coefficient of `P_n^*` is `C(2n, n)` (cycle 281's
  `butcherShiftedLegendre_leadingCoeff`). The leading coefficient of
  `(2X − 1)(2n − 1) P_{n−1}^*` is `2 · (2n − 1) · C(2(n − 1), n − 1)
  = 2 · (2n − 1) · C(2n − 2, n − 1)`. For the difference to drop
  below degree `n`, these must be equal, giving the binomial
  identity. (Both reduce algebraically to `(2n)! / (n! · (n − 1)!)`.)

- **Lean statement captures**: same content.
  - Hypothesis `2 ≤ n` is necessary to make `2n − 1` and `n − 1`
    correspond to the textbook quantities (and avoid `ℕ`-truncation
    artifacts at `n ≤ 1`). For `n < 2`, the recurrence is vacuous
    (Butcher restricts to `n = 2, 3, …`).
  - Real-cast formulation (both sides over `ℝ`) is needed because
    the consuming theorem (cycle 290's `recurrence_residual_natDegree_lt`)
    operates on `Polynomial ℝ` leading coefficients.

- **Justification**: This is a routine binomial coefficient identity,
  not a textbook-named theorem; classification is "helper lemma for
  (342f)". The Lean statement matches the mathematical content
  needed for the (342f) leading-coefficient cancellation.

## Dead ends

- **Aristotle (342f) project `efe4940e`**: failed to advance beyond
  20% for three consecutive cycle-polls (287, 288, 289). Per the
  cycle 285 three-stall protocol, cancellation was the correct
  action. The cycle 285 strengthened resubmission had cited all
  necessary helpers as axioms (Rodrigues, orthogonality, parity,
  eval_one, eval_zero, natDegree, norm_sq, leadingCoeff = C(2n,n),
  the iterated-IBP machinery, explicit n=0..8 forms, and the
  recurrence at n=2..8 as base cases) — yet still stalled at 20%.
  This is the second consecutive Aristotle attempt at (342f)
  (cycle 282's `c8b8f138` also stalled at 12% over 3 cycles).
  Strong signal that (342f) is genuinely outside Aristotle's
  current capacity. Manual closure per Path A is the correct path.

- **Phase A.1 (b) in same cycle**: attempted to scope the main
  residual-degree theorem proof. Found that the degree arithmetic
  on `B = C β * (C 2 * X - C 1) * P_{n-1}` requires careful piecewise
  computation (8 sub-steps, est. 100-150 LOC). Adding this to the
  helper (~80 LOC) plus the issue file plus bookkeeping would push
  the cycle well past target LOC budget. Strategy explicitly permits
  deferral; deferred per §10 of issue file.

## Discovery

- **`linear_combination` with `Nat.cast`-bridged identities**: when
  proving a real-cast identity that decomposes into ℕ-arithmetic
  pieces, the cleanest pattern is:
  1. Prove each ℕ piece as a `have ... : ... = ... := by ...` block.
  2. `congrArg (Nat.cast (R := ℝ))` + `push_cast at this` to cast each
     piece to ℝ (note: the parameter is `(R := ...)` not `(α := ...)`).
  3. Bridge any nat-sub appearing in the goal to real-sub via
     `Nat.cast_sub` + `push_cast` + `ring`.
  4. `rw` the cast pieces into the goal.
  5. Close with `linear_combination c * step_h` where `c` is the
     paper-derived coefficient (verify by computing
     `LHS_goal - RHS_goal` and comparing to
     `c * (LHS_step - RHS_step)`).

  This avoids the dance of converting back and forth between ℕ and ℝ
  arithmetic in a single `linarith`/`nlinarith` call (which often
  fails on non-linear products).

- **`Nat.choose_mul_right`** (Mathlib): the under-utilised identity
  `(m * n).choose n = m * (m * n - 1).choose (n - 1)` for `n ≠ 0`.
  Specializes at `m = 2` to give the half-binomial identity
  `C(2n, n) = 2 · C(2n − 1, n − 1)`, which is the entry point to
  the (342f) leading-coefficient analysis.

- **Cycle 285 protocol observability**: the 20% stall plateau
  reproduced exactly across three consecutive cycle-polls (287, 288,
  289), suggesting Aristotle hits a planning checkpoint at 20% and
  cannot proceed past the leading-coefficient algebraic identity.
  The cycle 285 protocol's 3-stall threshold turned out to be exactly
  right — earlier cancellation would have left the door open for
  late-stage progress; later cancellation would have wasted compute.

## Suggested next approach

**Cycle 290 priority 0 (≥80% of cycle)**: ship Phase A.1 (b)
`recurrence_residual_natDegree_lt`. Reference the cycle 289 helper
`n_mul_choose_two_n_n_eq`. Decompose into private lemmas as needed:

- `linearFactor_natDegree : (C 2 * X - C 1).natDegree = 1`
- `linearFactor_leadingCoeff : (C 2 * X - C 1).leadingCoeff = 2`
- Helper for `B.natDegree = n` and `B.leadingCoeff`.
- Helper for `A.natDegree = n` and `A.leadingCoeff`.
- Apply `Polynomial.degree_sub_lt` + bridge to `natDegree`.
- Bound `C.natDegree ≤ n - 2` and combine via `natDegree_add_le`.

Target axiom-clean, ~100-150 LOC. After (b) lands, cycle 291 opens
Phase A.2.

**Stretch goal**: if (b) ships in under 100 LOC, also begin Phase A.2
setup — at minimum, write `recurrence_residual_orthogonal_first_term`
(`⟨n · P_n^*, P_k^*⟩ = 0` for `k < n`, direct from (342a)).

**Do NOT**: re-submit (342f) to Aristotle; extend the empirical ladder
past n = 11; attempt Möbius/Pascal-style alternative closures (per
issue file §8).
