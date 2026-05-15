# Cycle 293 Results

## Worked on

§342 (342f) Phase A.3 — **fully closed**. Six new theorems in
`OpenMath/Chapter3/Section342.lean` shipping the parity-aided closure
of the general three-term recurrence:

1. `recurrence_residual_eval_at_one` (P1) — `Q.eval 1 = 0`.
2. `recurrence_residual_parity` (P2) — `Q(1 - x) = (-1)^n · Q(x)`.
3. `recurrence_residual_natDegree_le` (P3) — `Q.natDegree ≤ n - 2`.
4. `polynomial_eq_smul_butcherShiftedLegendre_of_natDegree_le_of_orthogonal`
   (P4) — basis-span converse helper.
5. `recurrence_residual_eq_zero` (P5) — `Q = 0` for `n ≥ 3`.
6. `butcherShiftedLegendre_recurrence` (P6) — **the (342f) headline**:
   `n · P_n^* = C(2n - 1) · (2X - 1) · P_{n-1}^* − C(n - 1) · P_{n-2}^*`
   for every `n ≥ 2`.

## Approach

Followed the cycle 293 strategy verbatim through all six stretch
deliverables. Phase A.3 closure path:

1. **P1 (`Q.eval 1 = 0`)**: distributed eval through the residual,
   substituted (342b) `P_k^*(1) = 1` for each summand, bridged
   `Nat`-subtraction casts (`((2n - 1 : ℕ) : ℝ) = 2n - 1`,
   `((n - 1 : ℕ) : ℝ) = n - 1` via `Nat.cast_sub` + `push_cast`),
   closed via `ring`.

2. **P2 (parity)**: distributed eval, applied cycle 272's
   `butcherShiftedLegendre_eval_one_sub` to each of the three
   summands, then reduced the powers `(-1)^{n-1} = -((-1)^n)` and
   `(-1)^{n-2} = (-1)^n` (the latter via `pow_add` + `norm_num`,
   relying on `(-1 : ℝ)^2 = 1`), closed via `ring`.

3. **P3 (degree drop)**: lifted P2 to the polynomial-level identity
   `Q.comp (C 1 - X) = C ((-1)^n) · Q` via `Polynomial.funext`. Took
   leading coefficients of both sides:
   - LHS: `Polynomial.leadingCoeff_comp` on `q := (C 1 - X)`
     (`natDegree = 1`, `leadingCoeff = -1`) gives
     `Q.leadingCoeff · (-1)^Q.natDegree`.
   - RHS: `Polynomial.leadingCoeff_C_mul_of_isUnit` (since
     `(-1)^n` is a unit) gives `(-1)^n · Q.leadingCoeff`.

   Equated, cancelled `Q.leadingCoeff ≠ 0` via `mul_left_cancel₀` to
   obtain `(-1)^Q.natDegree = (-1)^n`. Then by_contra'd
   `Q.natDegree > n - 2`: with cycle 290's `Q.natDegree < n`, this
   forces `Q.natDegree = n - 1`. Substituting gives
   `(-1)^(n-1) = (-1)^n`, but `(-1)^n = (-1)^(n-1) · (-1)`, so
   `(-1)^(n-1) = 0`, contradicting `pow_ne_zero`.

4. **P4 (basis-span converse)**: induction on `m` via the suffices
   pattern that cycle 292's `butcherShiftedLegendre_orthogonal_to_lower_degree`
   established (worked cleanly here too).
   - Base `m = 0`: `q.natDegree = 0` ⇒ `q = C (q.coeff 0) = C (q.coeff 0)
     · P_0^*` (using cycle 273's `butcherShiftedLegendre_zero = C 1`).
   - Step `m + 1`: define
     `c_top := q.coeff (m+1) / P_{m+1}^*.leadingCoeff` (denominator
     non-zero by cycle 281's `butcherShiftedLegendre_leadingCoeff =
     C(2(m+1), m+1) > 0`). Set `q' := q - C c_top · P_{m+1}^*`. Showed
     `q'.natDegree ≤ m` via `Polynomial.natDegree_le_iff_coeff_eq_zero`
     + casework on `N = m + 1` (closed by `div_mul_cancel₀ + sub_self`)
     vs `N > m + 1` (cycle 290 pattern via `Polynomial.coeff_eq_zero_of_natDegree_lt`).
     Showed `q'` orthogonal to `P_k^*` for `k < m` by linearity of
     `intervalIntegral.integral_sub` + integral pull-out of `c_top` +
     cycle 277's `butcherShiftedLegendre_orthogonal` (since
     `m + 1 ≠ k`). Applied IH to `q'`, obtaining
     `q' = C c' · P_m^*`. Forced `c' = 0` by combining cycle 281's
     `butcherShiftedLegendre_norm_sq m' = 1/(2m'+1) ≠ 0` with
     `∫ q · P_m^* = 0` (the `m < m + 1` case of `h_orth`) — after
     expanding `q = C c' · P_m^* + C c_top · P_{m+1}^*`, the
     `P_{m+1}^*` term vanishes by orthogonality, leaving
     `c' · (1/(2m'+1)) = 0`, hence `c' = 0`. Conclude `q = C c_top
     · P_{m+1}^*` via `sub_eq_zero.mp`.

5. **P5 (`Q = 0` for `n ≥ 3`)**: applied P4 at `m := n - 2` with
   `h_deg := recurrence_residual_natDegree_le n hn2` (P3) and
   `h_orth k hk := recurrence_residual_orthogonal n hn (by omega : k ≤ n - 3)`
   (cycle 292). Got `⟨c, Q = C c · P_{n-2}^*⟩`. Combined with P1's
   `Q.eval 1 = 0` and (342b)'s `P_{n-2}^*(1) = 1` to force `c = 0`.

6. **P6 ((342f) headline)**: case split on `n` vs 3 via
   `Nat.lt_or_ge`. For `n = 2`, `interval_cases n`, then `convert
   butcherShiftedLegendre_recurrence_two using 2 <;> norm_num` to
   bridge the Nat-subtraction-cast presentation
   (`Polynomial.C ((2 * 2 - 1 : ℕ) : ℝ)` vs cycle 282's
   `Polynomial.C 3`). For `n ≥ 3`, `linear_combination` on P5's
   `Q = 0`.

## Result

**SUCCESS — full Phase A.3 closure shipped**, all axiom-clean
(`[propext, Classical.choice, Quot.sound]`). Zero sorries in
`OpenMath/Chapter3/Section342.lean`. The file grew from 3116 → 3539
LOC (~423 new LOC).

**`butcherShiftedLegendre_recurrence`** closes Butcher (342f) at every
`n ≥ 2` — the planner's headline goal for Phase A.

## Faithfulness check

### `recurrence_residual_eval_at_one` (P1)

- **Entity**: `lem:342A` (342f). Quoting `extraction/formalization_data/entities/lem_342A.json`:
  > $nP_n^*(x) - (2x - 1)(2n - 1)P_{n-1}^*(x) - (n - 1)P_{n-2}^*(x)$
  > is a polynomial, $Q$ say, of degree less than $n$.

  P1 verifies `Q.eval 1 = 0` directly using (342b). This is the
  textbook's "resolved by substituting `x = 1`" trick that fixes the
  `P_{n-2}^*` coefficient. PASS.
- **Tautology**: conclusion is an `.eval 1 = 0` claim; no hypothesis
  matches. PASS.
- **Identity**: proof is non-trivial (cast bridging + ring). PASS.
- **Hypothesis strength**: `hn : 2 ≤ n` matches the textbook range.
  PASS.

### `recurrence_residual_parity` (P2)

- **Entity**: `lem:342A` (342f). Captures the textbook step
  > Because $Q$ has the same parity as $n$, it is of degree less than
  > $n - 1$.

  P2 ships the parity assertion `Q(1 - x) = (-1)^n · Q(x)`. P3
  consumes it to extract the degree bound. PASS.
- **Tautology**: conclusion is an `.eval (1 - x) = ...` equation; no
  hypothesis matches. PASS.
- **Identity**: proof composes three (342c) parity facts. PASS.
- **Hypothesis strength**: `hn : 2 ≤ n` matches textbook. PASS.

### `recurrence_residual_natDegree_le` (P3)

- **Entity**: `lem:342A` (342f). Captures the textbook
  > Because $Q$ has the same parity as $n$, it is of degree less than
  > $n - 1$.

  Translating "less than `n - 1`" to Lean: `Q.natDegree ≤ n - 2`
  (since `Q.natDegree ∈ ℕ` and `Q.natDegree < n - 1` is the same as
  `Q.natDegree ≤ n - 2`). PASS.
- **Tautology**: conclusion is `Q.natDegree ≤ n - 2`; no hypothesis
  matches. PASS.
- **Identity**: proof is the leadingCoeff parity argument. PASS.
- **Hypothesis strength**: `hn : 2 ≤ n` matches textbook. PASS.

### `polynomial_eq_smul_butcherShiftedLegendre_of_natDegree_le_of_orthogonal` (P4)

- **Entity**: not a direct textbook entity — a reusable Lean-side
  basis-span converse helper. Implicit in the textbook's argument
  combining "Q is orthogonal to P_k^* for k < n - 2" with
  "degree(Q) < n - 1" to conclude `Q = c · P_{n-2}^*`. PASS.
- **Lean statement captures**: same content as the standard
  Gram-Schmidt-style converse: any polynomial of natDegree ≤ m
  orthogonal to `P_0^*, ..., P_{m-1}^*` lies in the span of `P_m^*`.
  PASS.
- **Tautology**: conclusion `∃ c, q = C c · P_m^*` is an existence
  claim; no hypothesis matches. PASS.
- **Identity**: induction with degree manipulation + orthogonality
  dispatch. PASS.
- **Hypothesis strength**: minimal — `q.natDegree ≤ m` and `h_orth`
  for `k < m`. PASS.

### `recurrence_residual_eq_zero` (P5)

- **Entity**: `lem:342A` (342f). This is the combined
  conclusion-step of Butcher's proof:
  > Hence, (342f) follows except for the value of the $P_{n-2}^*$
  > coefficient, which is resolved by substituting $x = 1$.

  P5 derives `Q = 0` — the precise content of (342f) up to algebraic
  rearrangement. PASS.
- **Tautology**: conclusion is `Q = 0`; no hypothesis matches. PASS.
- **Identity**: proof composes P3 + cycle 292 + P4 + P1. PASS.
- **Hypothesis strength**: `hn : 3 ≤ n` is the minimum required for
  cycle 292's orthogonality bound `k ≤ n - 3` to be non-vacuous.
  The `n = 2` case is handled separately in P6 via cycle 282. PASS.

### `butcherShiftedLegendre_recurrence` (P6)

- **Entity**: `lem:342A` (342f). The textbook statement, quoted from
  `lem_342A.json`:
  > $n P_n^*(x) = (2x - 1)(2n - 1) P_{n-1}^*(x) - (n - 1) P_{n-2}^*(x)$,
  > for $n = 2, 3, 4, \ldots$.

  Lean form: `(n : ℝ) • P_n^* = C ((2n - 1 : ℕ) : ℝ) · (C 2 · X - C 1)
  · P_{n-1}^* - C ((n - 1 : ℕ) : ℝ) · P_{n-2}^*`. Exact textbook
  content; the Nat-subtraction casts arise from Lean's preference for
  ℕ-typed indices. PASS.
- **Tautology**: conclusion is the (342f) equation; no hypothesis
  matches. PASS.
- **Identity**: proof composes the `n = 2` base case (cycle 282) with
  P5 (`n ≥ 3`) via `linear_combination`. PASS.
- **Hypothesis strength**: `hn : 2 ≤ n` matches the textbook range
  exactly. PASS.

## Dead ends

None this cycle. P3 went through the cleaner leadingCoeff-parity
argument (Route 3a) rather than the more pedestrian coefficient
calculation (Route 3b). P4 closed on the first attempt after one
minor fix: replaced a failed `field_simp` closing step in Step 1
with the more direct `rw [div_mul_cancel₀ _ hPmp1_lc_ne, sub_self]`.

## Discovery

The leadingCoeff parity trick (P3) is cleaner than the cycle 292
strategy alternative (manual `coeff_comp` computation). Pattern: lift
the eval-level parity to polynomial level via `Polynomial.funext`, then
`congrArg Polynomial.leadingCoeff` on the polynomial identity reduces
to an algebraic fact about `(-1)^{natDegree}` vs `(-1)^n`. This avoids
all `coeff_comp` plumbing. Worth remembering for future degree-
constraint extractions from polynomial identities of the form
`p.comp q = c · p`.

The basis-span converse helper (P4) is general — independent of (342f).
It states: any polynomial of natDegree `≤ m` orthogonal to
`P_0^*, ..., P_{m-1}^*` is a scalar multiple of `P_m^*`. This is the
unique-decomposition direction of the `{P_0^*, ..., P_m^*}` orthogonal
basis of `Polynomial.degreeLT ℝ (m + 1)`. Reusable for (342g) or any
future projection arguments.

## Suggested next approach

Phase A is now **fully closed**. The remaining open piece of `lem:342A`
is (342g) — `P_n^*` has `n` distinct real zeros in `(0, 1)`. See
`.prover-state/issues/lem_342A_g_zeros_scoping.md` for the scoping
plan. With (342f) now in hand, the standard argument routes through
the recurrence + sign analysis at the endpoints. Cycle 294 may either:

1. **Open (342g)**: use the recurrence to derive zero-interleaving via
   Sturm-style arguments. ~200-300 LOC estimated.
2. **Move to Section 343 (Gaussian-quadrature methods)**: now that
   (342f) is available, `lem:342B` (`Gaussian quadrature exactness
   degree`) becomes directly tractable. ~150 LOC estimated.

Either is appropriate. Recommend (1) to fully close §342, then (2)
to move down the dependency chain.

Also: update `lean_status.json` for `lem:342A` — the (342f) clause is
now closed via `butcherShiftedLegendre_recurrence`. The (342g) clause
is still open, so the entity-level status stays `partial` until (342g)
ships.
