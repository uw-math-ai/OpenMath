# Cycle 290 Strategy — Phase A.1 (b) for lem:342A (342f) manual closure

## A. Target

**Phase A.1 (b)** of the lem:342A (342f) manual closure plan:
`recurrence_residual_natDegree_lt`. Cycle 289 shipped the binomial
helper `n_mul_choose_two_n_n_eq` (axiom-clean, 80 LOC) and explicitly
deferred (b) per LOC budget. Cycle 290's job is to ship (b) and
consume the cycle 289 helper.

Reference: `.prover-state/issues/lem_342A_342f_manual_closure_plan.md`
§5 Phase A.1, and the cycle 289 task results' "Suggested next
approach" section (verbatim deliverable spec).

## B. Statement to ship

In `OpenMath/Chapter3/Section342.lean`, immediately after the cycle
289 `n_mul_choose_two_n_n_eq` helper:

```lean
theorem recurrence_residual_natDegree_lt (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℝ) • butcherShiftedLegendre n
      - Polynomial.C ((2 * n - 1 : ℕ) : ℝ)
        * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre (n - 1)
      + Polynomial.C ((n - 1 : ℕ) : ℝ)
        * butcherShiftedLegendre (n - 2)).natDegree < n
```

This is the textbook statement that `Q := n·P_n^* − (2n-1)·(2X-1)·
P_{n-1}^* + (n-1)·P_{n-2}^*` has `natDegree < n` (Butcher §342 p. 236).

## C. Decomposition plan (8 sub-steps, ~100-150 LOC)

Per the cycle 289 task results, the proof decomposes into:

1. **`linearFactor_natDegree`** (private): `(C 2 * X - C 1).natDegree = 1`.
   `Polynomial.natDegree_X_sub_C` doesn't fire directly because of
   the leading `C 2`. Approach: compute via
   `Polynomial.natDegree_sub_eq_left_of_natDegree_lt` after noting
   `(C 1).natDegree = 0 < (C 2 * X).natDegree = 1`. Alternatively
   `compute_degree!` tactic.

2. **`linearFactor_leadingCoeff`** (private): `(C 2 * X - C 1).leadingCoeff = 2`.
   Via `Polynomial.leadingCoeff_X_pow_add_C` family, or direct
   computation: `leadingCoeff_sub_of_natDegree_lt` plus
   `Polynomial.leadingCoeff_C_mul_X`.

3. **B-side natDegree and leadingCoeff** (private): for
   `B := C β * (C 2 * X - C 1) * P_{n-1}` where
   `β := ((2*n - 1 : ℕ) : ℝ)`:
   - `B.natDegree = n`: via `Polynomial.natDegree_mul` (needs
     non-zero factors over `NoZeroDivisors ℝ`). Use
     `Polynomial.natDegree_C_mul_of_isUnit` for the `C β *` peel
     (need `β ≠ 0`, i.e. `(2*n - 1 : ℝ) ≠ 0` from `hn`).
   - `B.leadingCoeff = β * 2 * C(2(n-1), n-1)`: via
     `Polynomial.leadingCoeff_mul` (`R = ℝ` is integral domain).

4. **A-side natDegree and leadingCoeff** (private): for
   `A := (n : ℝ) • P_n`:
   - `A.natDegree = n` via `Polynomial.natDegree_smul` (need
     `(n : ℝ) ≠ 0` from `hn`).
   - `A.leadingCoeff = n * C(2n, n)` via `Polynomial.leadingCoeff_smul`
     + cycle 281's `butcherShiftedLegendre_leadingCoeff`.

5. **Leading-coefficient equality** (key step): use cycle 289's
   `n_mul_choose_two_n_n_eq` to show `A.leadingCoeff = B.leadingCoeff`.
   The identity from cycle 289:
   `n · C(2n, n) = 2 · (2n − 1) · C(2n − 2, n − 1)`.

6. **Apply `Polynomial.degree_sub_lt`**: with `A.degree = B.degree = n`,
   `A.leadingCoeff = B.leadingCoeff`, and `A ≠ 0` (since leading
   coefficient `n * C(2n, n) > 0`), conclude `(A - B).degree < n`.
   Bridge `degree` → `natDegree` via
   `Polynomial.natDegree_lt_iff_degree_lt` plus `(A - B) ≠ 0` handling.

7. **C-side bound** (private): for
   `Cterm := Polynomial.C ((n - 1 : ℕ) : ℝ) * P_{n-2}`:
   `Cterm.natDegree ≤ n - 2 < n`. Use `Polynomial.natDegree_C_mul_le`
   + `butcherShiftedLegendre_natDegree (n - 2) = n - 2`.

8. **Combine via `Polynomial.natDegree_add_le`**: `(A - B + Cterm).natDegree
   ≤ max ((A - B).natDegree) (Cterm.natDegree) < n` via `Nat.max_lt`
   on (6)'s `< n` and (7)'s `< n`.

## D. Tactical guidance

### D.1 Nat-subtraction handling

The hypotheses mix `Nat.sub` (`2*n - 1`, `n - 1`, `n - 2`) with real
arithmetic. Bridges already used in cycle 289's helper:
```
h_2n_minus_1_real : ((2*n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1
h_n_minus_1_real  : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1
```
proved via `Nat.cast_sub` + `push_cast` + `ring` (requires `1 ≤ n`
and `1 ≤ 2*n` from `hn : 2 ≤ n`).

Reuse the same pattern. For `n - 2`, you'll need `2 ≤ n` for
`Nat.cast_sub` (already from `hn`).

### D.2 Use `compute_degree!` aggressively

The piecewise degree-computation steps (1, 2, 3, 4) are exactly what
`compute_degree!` was designed for. Try it first on each before
falling back to manual `natDegree_*_le`/`natDegree_mul` rewriting.

### D.3 `Polynomial.degree_sub_lt` signature

Mathlib's signature (verify with `lean_hover_info` early):
```
theorem Polynomial.degree_sub_lt {p q : Polynomial R}
    (hd : p.degree = q.degree)
    (hp0 : p ≠ 0)
    (hlc : p.leadingCoeff = q.leadingCoeff) :
    (p - q).degree < p.degree
```

Apply with `p = (n : ℝ) • P_n` and `q = β * (2X - 1) * P_{n-1}`.
Bridge `degree = n` to `natDegree = n` (since neither is zero) via
`Polynomial.degree_eq_natDegree` after establishing non-zeroness.

### D.4 Non-zero leading coefficient

`butcherShiftedLegendre_leadingCoeff` gives `C(2n, n)` as the leading
coefficient. Use `Nat.choose_pos` (lower bound `2n choose n ≥ 1`
when `n ≤ 2n`, true from `hn`) to conclude `> 0`, hence `≠ 0`. Cast
to `ℝ` via `Nat.cast_pos`.

### D.5 LOC budget

Target ~100-150 LOC total. If approaching 200 LOC, split the proof
further: ship the per-step lemmas (1)-(7) as `private` declarations
and let cycle 291 assemble (8). But ideally land all 8 steps in
cycle 290.

## E. What NOT to do

### E.1 Do NOT re-submit (342f) to Aristotle.

Cycles 282 (`c8b8f138`, stalled 12% over 3 cycles → cancelled) and
285/287/288/289 (`efe4940e`, stalled 20% over 3 cycles → cancelled
cycle 289) are dispositive. Two consecutive Aristotle attempts at
(342f) at progressively-stronger axiomatizations have both failed.
**Manual closure only.**

### E.2 Do NOT extend the empirical ladder past `n = 11`.

Cycles 282-288's ladder rungs at `n = 2..11` are sufficient evidence.
Per cycle 285's protocol, further extension is not informative.

### E.3 Do NOT attempt Möbius/Pascal alternatives.

Cycle 273 documented those paths as too complex without (342a) in
hand. With (342a)/(342d)/Rodrigues now all shipped, Path A
(degree-bound + orthogonality basis) is the clean route.

### E.4 Do NOT use `sorry`, `axiom`, or `constant`.

Cycle 290's deliverable must be axiom-clean. The cycle 200/201
rollback precedent applies.

### E.5 Do NOT increase `maxHeartbeats` above 200000.

If a sub-step blows past the default heartbeat count, decompose
further into smaller private lemmas (cycle 150's `n=7` Section550
precedent: factor matrix expansion into its own lemma if simp
normalization is slow).

### E.6 Do NOT touch §441.

GPFS slowness persists (43+ consecutive timeouts since cycle 182).
Skip per `.prover-state/issues/cycle_182_gpfs_slowness.md`.

### E.7 Do NOT inline-prove the helper from cycle 289.

`n_mul_choose_two_n_n_eq` is already shipped axiom-clean. Reference
it directly via name; do not duplicate its proof.

### E.8 Do NOT pivot to a fresh entity.

The §342 (342f) closure is multi-cycle infrastructure work; cycle
290 is committed to Phase A.1 (b). Cycle 291+ can decide whether
to continue Phase A.2 immediately or pivot.

## F. Stretch goal (only if A.1 (b) closes in under 100 LOC)

Begin **Phase A.2** setup by shipping the easy orthogonality
components:

**(F.1)** `recurrence_residual_orthogonal_first_term`:
```lean
theorem recurrence_residual_orthogonal_first_term
    (n : ℕ) (hn : 2 ≤ n) {k : ℕ} (hk : k < n) :
    ∫ x in (0 : ℝ)..1, ((n : ℝ) • butcherShiftedLegendre n).eval x
        * (butcherShiftedLegendre k).eval x = 0
```
Direct from cycle 277's `butcherShiftedLegendre_orthogonal` + scalar
factor. ~10-20 LOC.

**(F.2)** `recurrence_residual_orthogonal_third_term`:
```lean
theorem recurrence_residual_orthogonal_third_term
    (n : ℕ) (hn : 2 ≤ n) {k : ℕ} (hk_le : k ≤ n - 3) :
    ∫ x in (0 : ℝ)..1,
        (Polynomial.C ((n - 1 : ℕ) : ℝ) * butcherShiftedLegendre (n - 2)).eval x
        * (butcherShiftedLegendre k).eval x = 0
```
Direct from `butcherShiftedLegendre_orthogonal` (since `k ≠ n - 2`
for `k ≤ n - 3`). ~15-25 LOC.

Save the cross-term `⟨(2n-1)·(2X-1)·P_{n-1}^*, P_k^*⟩ = 0` for cycle
291 — that requires the `2X - 1 = -P_1^*` substitution plus a basis
expansion argument.

**Do NOT attempt (F.1) and (F.2) if A.1 (b) is at all difficult.**
The Priority 0 deliverable is A.1 (b); stretch is genuinely
optional.

## G. Verification checklist

Before commit:

1. `lake env lean OpenMath/Chapter3/Section342.lean` exits 0.
2. `lake env lean OpenMath/Chapter3.lean` exits 0.
3. `grep -c sorry OpenMath/Chapter3/Section342.lean` → 0.
4. `#print axioms OpenMath.Chapter3.Section342.recurrence_residual_natDegree_lt`
   returns `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
5. (If F.1/F.2 shipped) same axiom check on each.

## H. Faithfulness

`recurrence_residual_natDegree_lt` is a *helper lemma* toward the
(342f) closure, not a textbook entity in itself. Butcher §342 p. 236
implicitly states this fact in the prose:

> The highest degree coefficients in `P_n^*` and `P_{n-1}^*` can be
> compared so that `n P_n^*(x) − (2x − 1)(2n − 1) P_{n-1}^*(x)` is a
> polynomial, `Q` say, of degree less than `n`.

The Lean statement captures the same content via the explicit
residual polynomial `Q`. The `(n - 1) · P_{n-2}^*` summand is added
because we work with the full residual (LHS − RHS of the (342f)
recurrence), not just the textbook's stated subtraction; this is a
strict generalization (adding a known-low-degree polynomial cannot
raise the bound above `n - 1`). The added `+ (n - 1) · P_{n-2}^*`
term has `natDegree ≤ n - 2 < n`, so it does not affect the
conclusion `< n`.

No faithfulness divergence from the textbook; this is helper
infrastructure.

## I. Cycle 291+ outlook

If cycle 290 ships A.1 (b) cleanly:
- **Cycle 291**: Phase A.2 (orthogonality components). Start with
  F.1/F.2 if not already shipped, then tackle the cross-term
  `⟨(2X-1)·P_{n-1}^*, P_k^*⟩ = 0` for `k ≤ n - 3`.
- **Cycle 292**: Phase A.3 (basis-span conclusion `Q = 0`).
- **Cycle 293**: Final closure of (342f) general theorem + status
  bump in `lean_status.json`.

Total ~4 cycles to close lem:342A (342f), bringing §342 to fully
formalized except possibly (342g) `n` distinct real zeros (separate
scoping in `lem_342A_g_zeros_scoping.md`).
