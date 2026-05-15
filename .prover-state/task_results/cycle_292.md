# Cycle 292 Results

## Worked on

§342 (342f) Phase A.2 F.3 cross-term + basis-span helper + full residual
orthogonality (Phase A.2 closed). Three new theorems in
`OpenMath/Chapter3/Section342.lean`:

1. `butcherShiftedLegendre_orthogonal_to_lower_degree` (basis-span P1).
2. `recurrence_residual_orthogonal_cross_term` (F.3).
3. `recurrence_residual_orthogonal` (full residual; P3 stretch landed).

## Approach

Followed the cycle 292 strategy §C verbatim:

1. **P1 (basis-span helper).** Induction on a bound `d` with
   `q.natDegree ≤ d < m`. Base case `d = 0`: `q` is constant via
   `Polynomial.eq_C_of_natDegree_eq_zero`, pull the scalar out with
   `intervalIntegral.integral_const_mul`, then `∫ P_m^* = ∫ P_m^* · P_0^*
   = 0` via cycle 277's `butcherShiftedLegendre_orthogonal` (using
   `butcherShiftedLegendre_zero` to rewrite `P_0^* = C 1`). Inductive
   step `d → d + 1`: if `q.natDegree ≤ d`, apply IH; otherwise
   `q.natDegree = d + 1`, set `c := q.coeff (d+1) /
   (P_{d+1}^*).leadingCoeff` (well-defined since cycle 281's
   `butcherShiftedLegendre_leadingCoeff` gives a positive
   `C(2(d+1), d+1)` denominator), subtract `C c · P_{d+1}^*` to drop
   the residual's degree via `Polynomial.degree_sub_lt`, apply IH to the
   residual, and handle the subtracted scalar multiple of `P_{d+1}^*`
   via (342a) since `d + 1 < m`.

2. **P2 (F.3 cross-term).** Rewrote the integrand as
   `(2n - 1) * (P_{n-1}^*.eval x * ((C 2 · X - C 1) * P_k^*).eval x)`
   via `Polynomial.eval_mul / eval_sub / eval_C / eval_X` + `ring`.
   Pulled the constant out via `intervalIntegral.integral_const_mul`.
   Applied P1 with `m := n - 1` and `q := (C 2 · X - C 1) * P_k^*`.
   The natDegree side condition `q.natDegree < n - 1` reduces to
   `1 + k ≤ n - 2 < n - 1` via `Polynomial.natDegree_mul_le` plus
   cycle 273's `butcherShiftedLegendre_one` (which identifies
   `C 2 · X - C 1` with `butcherShiftedLegendre 1`, immediately giving
   `.natDegree = 1` via `butcherShiftedLegendre_natDegree 1`).

3. **P3 (full residual orthogonality).** Distributed
   `eval_add`/`eval_sub`/`sub_mul`/`add_mul`, split via
   `intervalIntegral.integral_sub` and `intervalIntegral.integral_add`
   (integrability witnesses from `Polynomial.continuous.mul`), then
   dispatched the three summands via cycle 291's
   `recurrence_residual_orthogonal_first_term` (F.1, with `k < n`),
   cycle 292's `recurrence_residual_orthogonal_cross_term` (F.3), and
   cycle 291's `recurrence_residual_orthogonal_third_term` (F.2).

## Result

SUCCESS — all three theorems compile and are axiom-clean
(`[propext, Classical.choice, Quot.sound]`) per `lean_verify`. Zero
sorries in `OpenMath/Chapter3/Section342.lean`. `OpenMath/Chapter3.lean`
aggregator builds. Total new LOC: ~244 (file went 2872 → 3116).

Phase A.2 of the (342f) manual closure plan is now **fully closed**.
Cycle 293 can move directly to Phase A.3 (combine cycle 290's
`recurrence_residual_natDegree_lt` with cycle 292's
`recurrence_residual_orthogonal` to conclude `Q = 0`, which yields the
general (342f) recurrence).

## Faithfulness check

### `butcherShiftedLegendre_orthogonal_to_lower_degree` (P1)

- **Entity ID**: not a direct textbook entity — a reusable Lean-side
  helper. The basis-span argument is implicit in Butcher §342 proof
  step "A simple calculation shows that `Q` is orthogonal to `P_k^*`
  for `k < n - 2`"; the helper isolates the underlying basis-span
  fact for reuse in Phase A.3.
- **Lean statement captures**: same content as the standard fact
  "shifted Legendre `P_m^*` is orthogonal to every polynomial of
  natDegree `< m`", an immediate corollary of (342a) on the basis
  `{P_0^*, ..., P_{m-1}^*}`.
- **Tautology check**: conclusion is the integral equality; no
  hypothesis matches. PASS.
- **Identity check**: proof is a nontrivial induction with degree
  arithmetic and orthogonality dispatch. PASS.
- **Hypothesis strength**: `q.natDegree < m` is the standard / minimal
  hypothesis. PASS.

### `recurrence_residual_orthogonal_cross_term` (F.3)

- **Entity ID**: `lem:342A` (342f) — the cross-term orthogonality is
  step 2 of Butcher's proof outline, quoted from
  `extraction/formalization_data/entities/lem_342A.json`:
  > A simple calculation shows that `Q` is orthogonal to `P_k^*` for
  > `k < n - 2`.

  This theorem ships the cross-term `⟨(2n - 1)(2X - 1) P_{n-1}^*, P_k^*⟩
  = 0` summand of that result. The full `Q` orthogonality is the
  combined theorem `recurrence_residual_orthogonal` (P3 below).
- **Lean statement captures**: same content, slightly stronger range
  `k ≤ n - 3` (textbook says `k < n - 2`, which is equivalent to
  `k ≤ n - 3` over `ℕ`). The textbook's later remark uses parity to
  weaken to `k < n - 2`, but Phase A.2 omits parity. PASS.
- **Tautology check**: conclusion is the integral; no hypothesis
  matches. PASS.
- **Identity check**: proof uses P1 + degree arithmetic, not vacuous.
  PASS.
- **Hypothesis strength**: `hn : 3 ≤ n` ensures `n - 3 ≥ 0` is sensible
  (otherwise `k ≤ n - 3` collapses to `k = 0` and the theorem is
  trivial). `hk : k ≤ n - 3` matches the textbook. PASS.

### `recurrence_residual_orthogonal` (P3)

- **Entity ID**: `lem:342A` (342f). This is the combined orthogonality
  step of Butcher's proof:
  > A simple calculation shows that `Q` is orthogonal to `P_k^*` for
  > `k < n - 2`.

  with `Q := n P_n^* - (2n - 1)(2X - 1) P_{n-1}^* + (n - 1) P_{n-2}^*`
  exactly as in cycle 290's `recurrence_residual_natDegree_lt`.
- **Lean statement captures**: same content. The combined integrand is
  the *full* residual `Q` from cycle 290; the orthogonality holds for
  every `k ≤ n - 3`. PASS.
- **Tautology check**: conclusion is the integral of the full residual
  against `P_k^*`. PASS.
- **Identity check**: proof composes F.1 + F.2 + F.3 by integral
  linearity; not vacuous. PASS.
- **Hypothesis strength**: `hn : 3 ≤ n` matches Phase A.2's required
  range. PASS.

## Dead ends

None this cycle — the strategy's planned route closed cleanly. One
small Lean-side wrinkle: in the natDegree calc step for the F.3
cross-term, the expression `Polynomial.C 2 * Polynomial.X - Polynomial.C 1`
in isolation defaulted to `ℕ[X]` (via natural-number literals); the fix
was an explicit `: Polynomial ℝ` annotation on the calc step (also
present in the initial `have h_2X_1_nd` definition, which Lean did
parse correctly due to its `: Polynomial ℝ` annotation).

## Discovery

The `Polynomial.degree_sub_lt` API plays cleanly with
`Polynomial.degree_eq_natDegree` for converting natDegree assertions to
degree-side assertions, even though `degree` is `WithBot ℕ`. Pattern
used in P1:

```lean
rw [Polynomial.degree_eq_natDegree h_zero,
    Polynomial.degree_eq_natDegree hq_ne, heq] at h_sub_deg
exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast h_sub_deg)
```

This `exact_mod_cast` double-step (first to peel a `WithBot ℕ` to `ℕ`,
then to convert `<` to `≤`) is a useful template for future
`Polynomial.degree_sub_lt`-based reductions.

The basis-span helper (P1) is general — it does not depend on the (342f)
recurrence structure. It directly proves that `P_m^*` is orthogonal to
every polynomial of natDegree `< m`, i.e. to all of `Polynomial.degreeLT
ℝ m`. This is the standard Gram-Schmidt / spanning-set fact for
orthogonal polynomial sequences. Future cycles working on (342g)
distinct-roots or any orthogonal-projection argument can consume P1
directly.

## Suggested next approach

Cycle 293: Phase A.3 — combine cycle 290's
`recurrence_residual_natDegree_lt` (which gives `Q.natDegree < n`) with
cycle 292's `recurrence_residual_orthogonal` (which gives `⟨Q, P_k^*⟩ =
0` for every `k ≤ n - 3`) to conclude `Q = 0`. Plan:

1. Use cycle 292's basis-span helper `butcherShiftedLegendre_orthogonal_to_lower_degree`
   in reverse: any polynomial with `natDegree < n` is uniquely determined
   by its inner products against `P_0^*, ..., P_{n-1}^*`. So if all such
   inner products vanish, the polynomial is `0`.
2. Cycle 292's `recurrence_residual_orthogonal` gives the inner products
   vanish for `k ≤ n - 3`; the remaining cases `k = n - 2` and `k = n - 1`
   need separate treatment. For these:
   - `k = n - 1`: `⟨Q, P_{n-1}^*⟩` — F.1 contributes 0 (since `n - 1 < n`,
     `n ≠ n - 1`), F.2 contributes 0 (since `n - 2 ≠ n - 1` for `n ≥ 3`).
     F.3's cross-term `(2n - 1)(2X - 1) P_{n-1}^*` against `P_{n-1}^*`
     does **not** vanish; it equals `(2n - 1) · ⟨(2X - 1) P_{n-1}^*,
     P_{n-1}^*⟩`. By parity (342c), `(2X - 1) P_{n-1}^*` has the same
     parity as `(P_1^* · P_{n-1}^*)`, which is `(-1)^1 · (-1)^{n-1} =
     (-1)^n`. So `⟨(2X - 1) P_{n-1}^*, P_{n-1}^*⟩ = 0` by parity
     argument (or by direct expansion). This needs care.
   - `k = n - 2`: `⟨Q, P_{n-2}^*⟩` — similar parity argument.

   Cycle 293 may need an additional parity-driven orthogonality result.
   Alternatively, use a different basis-span argument: combine
   `natDegree Q < n` with orthogonality to `P_0^*, ..., P_{n-1}^*` to
   force `Q = 0`. The cleanest route is probably:

   **Direct claim**: If `q : Polynomial ℝ` has `q.natDegree < n` and
   `∫ q · P_k^* = 0` for every `k < n`, then `q = 0`. This follows from
   P1 + induction / Gram-Schmidt.

   Then for the cycle 290 residual, we already have `Q.natDegree < n`
   (cycle 290). We need `⟨Q, P_k^*⟩ = 0` for every `k < n`, not just
   `k ≤ n - 3`. The cases `k = n - 2` and `k = n - 1` require
   additional argument:
   - For `k = n - 1`: as above, parity.
   - For `k = n - 2`: parity, OR the textbook's "x = 1 substitution"
     to fix the `P_{n-2}^*` coefficient.

3. Once Phase A.3 closes, cycle 294 extracts the (342f) headline via
   `linear_combination` on `Q = 0`.

Budget estimate: ~80-120 LOC for cycle 293 Phase A.3.

Alternative cycle 293 plan: skip directly to a Gram-Schmidt
spanning-set argument using P1 inductively. This avoids the parity
analysis but may require a separate lemma about
`Polynomial.degreeLT ℝ n` being spanned by `{P_0^*, ..., P_{n-1}^*}`.
