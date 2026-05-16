# Cycle 311 — §342 Phase 3.2: `D(n)` for the Gauss–Legendre `RKTableau`

## §A — Target

Ship `butcherGaussLegendreRK_satisfiesD` (third prong of `cor:342D`)
in `OpenMath/Chapter3/Section342.lean`, immediately after cycle 310's
`butcherGaussLegendreRK_satisfiesC` and its non-vacuity witnesses.

**The headline theorem** (write the signature first, then bottom-up
to it):

```lean
theorem butcherGaussLegendreRK_satisfiesD (n : ℕ) (hn : 0 < n) :
    (butcherGaussLegendreRK n).SatisfiesD n
```

Recall the `SatisfiesD` definition (Section321:111-114):

```
∀ j : Fin s, ∀ k : ℕ, 1 ≤ k → k ≤ ζ →
  (∑ i : Fin s, M.b i * M.c i ^ (k - 1) * M.A i j)
    = (M.b j / (k : ℝ)) * (1 - M.c j ^ k)
```

For the Gauss–Legendre tableau (`b = _quadratureWeights`,
`c = _zeros`, `A = _collocationA`) this becomes Butcher's

    ∑ᵢ bᵢ · cᵢ^(k-1) · ∫₀^{cᵢ} Lⱼ = (bⱼ/k) · (1 − cⱼ^k)    (★)

for every `j : Fin n` and every `k ∈ [1, n]`.

## §B — Why D(n) is feasible in one cycle

The textbook proof (Butcher §342 p. 240) is short. Translated to the
Lean infrastructure shipped through cycle 310, it has three moves:

1. **Express the L.H.S. as `∫₀¹ X^(k-1) · F_j(X) dx`** where `F_j` is
   a polynomial antiderivative of `Lⱼ := Lagrange.basis _ _ j` with
   `F_j(0) = 0`. The bridge is cycle 304's `2n`-degree quadrature
   exactness (`butcherShiftedLegendre_quadrature_exact_lt_two_n`):
   the polynomial `X^(k-1) · F_j` has `natDegree ≤ (k-1) + n ≤ 2n − 1
   < 2n`, so its quadrature sum equals its integral.

2. **Apply IBP to `∫₀¹ X^(k-1) · F_j`** with `u := F_j`,
   `dv := X^(k-1) dx`. The integrated term is `[F_j(x) · x^k/k]₀¹
   = F_j(1)/k = bⱼ/k`; the remainder is `−(1/k) · ∫₀¹ X^k · Lⱼ`.

3. **Reduce `∫₀¹ X^k · Lⱼ` to `bⱼ · cⱼ^k`** via cycle 304's
   `2n`-degree exactness on the polynomial `X^k · Lⱼ` (degree
   `k + (n−1) ≤ 2n − 1 < 2n`) plus the Kronecker-delta property
   `Lⱼ(cᵢ) = δᵢⱼ` (Mathlib's `Lagrange.eval_basis_self` and
   `Lagrange.eval_basis_of_ne`, already used in cycle 305 — see
   `Section342.lean` around line 6716).

The only genuinely new infrastructure is the polynomial antiderivative
of `Lⱼ` (Phase A). Phases B and C compose existing infrastructure.

## §C — Phased decomposition

Ship in this exact order. Each phase is independently axiom-checkable.

### Phase A — Polynomial antiderivative of `Lⱼ` (~80 LOC, must ship)

Mathlib does NOT have `Polynomial.integral` (verified at HEAD).
Build it manually for the specific case we need:

```lean
private noncomputable def butcherShiftedLegendre_lagrangeAntideriv
    (n : ℕ) (j : Fin n) : Polynomial ℝ :=
  let L : Polynomial ℝ :=
    Lagrange.basis Finset.univ (butcherShiftedLegendre_zeros n) j
  ∑ k ∈ Finset.range (L.natDegree + 1),
    Polynomial.C (L.coeff k / ((k : ℝ) + 1)) * Polynomial.X ^ (k + 1)
```

Then ship four named lemmas (each ~10–25 LOC):

**A.1** `butcherShiftedLegendre_lagrangeAntideriv_derivative`:
   `(lagrangeAntideriv n j).derivative = Lagrange.basis _ _ j`.

   Recipe: `Polynomial.derivative_sum` over the `Finset.range`,
   per-term `Polynomial.derivative_C_mul_X_pow` gives
   `C (c_k / (k+1)) · (k+1) · X^k = C c_k · X^k`, then
   `Finset.sum_congr` + the fact that `L = ∑_{k ≤ deg L} C (L.coeff k) · X^k`
   via `Polynomial.as_sum_range` (verify name with
   `lean_local_search "as_sum_range"`; alternative is
   `Polynomial.sum_C_mul_X_pow_eq` or `Polynomial.sum_range_eq`).
   Pitfall: division by `(k + 1 : ℝ)` is fine since `k + 1 ≠ 0` for
   `k : ℕ`, but rewriting `(k + 1) · (c_k / (k+1)) = c_k` needs
   `field_simp` with `Nat.cast_add_one_pos` or
   `(by positivity : (0 : ℝ) < (k : ℝ) + 1).ne'`.

**A.2** `butcherShiftedLegendre_lagrangeAntideriv_eval_zero`:
   `(lagrangeAntideriv n j).eval 0 = 0`.

   Each term `C (c_k / (k+1)) · X^(k+1)` evaluates to
   `(c_k / (k+1)) · 0^(k+1) = 0` since `k + 1 ≥ 1` and
   `0^(k+1) = 0`. Close with `Polynomial.eval_finset_sum` +
   `Polynomial.eval_mul` + `Polynomial.eval_C` + `Polynomial.eval_X`
   + `zero_pow (Nat.succ_ne_zero k)` + `Finset.sum_const_zero`.

**A.3** `butcherShiftedLegendre_lagrangeAntideriv_natDegree_le`:
   `(lagrangeAntideriv n j).natDegree ≤ n`.

   Bound each summand's `natDegree`:
   `(C (c_k / (k+1)) · X^(k+1)).natDegree ≤ k + 1` via
   `Polynomial.natDegree_C_mul_X_pow_le` or
   `Polynomial.natDegree_mul_le`. Then
   `Finset.sum.natDegree_le` (Mathlib: `Polynomial.natDegree_sum_le_of_forall_le`
   or `Polynomial.natDegree_finset_sum_le`) bounds the whole sum by
   `max_{k < L.natDegree + 1} (k + 1) ≤ L.natDegree + 1 ≤ n`
   (the last step uses `Lagrange.basis`'s degree bound — see
   `Lagrange.natDegree_basis_le` or just
   `Polynomial.natDegree_lt_iff_degree_lt`; for our case
   `(Lagrange.basis Finset.univ v j).natDegree ≤ n - 1` should be
   accessible).

   **Risk (LOW)**: if `Lagrange.natDegree_basis_le` is missing,
   use the looser bound `lagrangeAntideriv.natDegree ≤ L.natDegree + 1`
   and accept that we use it through `n - 1 + 1 = n` (with
   `omega` or `Nat.sub_add_cancel`).

**A.4** `butcherShiftedLegendre_lagrangeAntideriv_eval_integral`:
   `∀ c : ℝ, (lagrangeAntideriv n j).eval c = ∫ x in (0:ℝ)..c, (Lagrange.basis _ _ j).eval x`.

   FTC bridge. Recipe: apply `intervalIntegral.integral_eq_sub_of_hasDerivAt`
   with derivative from A.1. Specifically, for any `c : ℝ`:

   ```
   ∫ x in 0..c, L.eval x
     = (lagrangeAntideriv n j).eval c − (lagrangeAntideriv n j).eval 0
                                    ‖ via FTC + A.1
     = (lagrangeAntideriv n j).eval c                   -- via A.2
   ```

   The `HasDerivAt` hypothesis for `intervalIntegral.integral_eq_sub_of_hasDerivAt`
   is supplied by `Polynomial.hasDerivAt` + A.1 (the polynomial
   derivative equals the Lagrange basis). Integrability is
   `(Polynomial.continuous _).intervalIntegrable _ _`.

### Phase B — `∫₀¹ X^k · Lⱼ = bⱼ · cⱼ^k` for `k ≤ n` (~40 LOC, must ship)

```lean
private theorem butcherShiftedLegendre_integral_X_pow_lagrange_basis
    (n : ℕ) (hn : 0 < n) (j : Fin n) (k : ℕ) (hk : k ≤ n) :
    (∫ x in (0:ℝ)..1,
        x ^ k *
        (Lagrange.basis Finset.univ (butcherShiftedLegendre_zeros n) j).eval x)
      = butcherShiftedLegendre_quadratureWeights n j *
        butcherShiftedLegendre_zeros n j ^ k
```

Recipe:
1. Define `φ : Polynomial ℝ := Polynomial.X^k * Lagrange.basis _ _ j`.
   This has `natDegree ≤ k + (n - 1) ≤ 2n − 1 < 2n` via
   `Polynomial.natDegree_mul_le` + `Polynomial.natDegree_X_pow` +
   `Lagrange.basis`'s degree bound.
2. Apply cycle 304's `butcherShiftedLegendre_quadrature_exact_lt_two_n`
   on `φ` to convert `∫₀¹ φ.eval x` to `∑ᵢ bᵢ · φ(cᵢ)`.
3. Rewrite `φ.eval c = c^k · Lⱼ(c)` via `Polynomial.eval_mul`,
   `Polynomial.eval_pow`, `Polynomial.eval_X`.
4. Collapse the sum via the Kronecker-delta property:
   `Lⱼ(cᵢ) = δᵢⱼ` (= 1 if i = j, 0 otherwise) → only the `i = j`
   term survives → `bⱼ · cⱼ^k · 1`. Use `Finset.sum_eq_single (j)`
   with `Lagrange.eval_basis_self` (i = j case) and
   `Lagrange.eval_basis_of_ne` (i ≠ j case), exactly as
   `butcherShiftedLegendre_quadratureWeights_unique` does (see
   `Section342.lean:6700–6725` for the precedent).

**Pitfall (cycle 305 precedent)**: the `Finset.sum_eq_single` API
takes the bound function as `j ∈ s, j ≠ a → f j = 0`, NOT
`a → ∀ j ∈ s \ {a}, ...`. Match the cycle 305 invocation pattern
verbatim.

### Phase C — Full D(n) capstone (~100 LOC, stretch but achievable)

```lean
theorem butcherGaussLegendreRK_satisfiesD (n : ℕ) (hn : 0 < n) :
    (butcherGaussLegendreRK n).SatisfiesD n := by
  intro j k h1 hk
  -- Unfold to the concrete `∑ᵢ bᵢ · cᵢ^(k-1) · Aᵢⱼ = (bⱼ/k)(1 - cⱼ^k)`.
  show (∑ i : Fin n,
          butcherShiftedLegendre_quadratureWeights n i *
            butcherShiftedLegendre_zeros n i ^ (k - 1) *
            butcherShiftedLegendre_collocationA n i j)
        = butcherShiftedLegendre_quadratureWeights n j / (k : ℝ) *
          (1 - butcherShiftedLegendre_zeros n j ^ k)
  ...
```

Recipe:

1. **Substitute `Aᵢⱼ` by Phase A.4**:
   `butcherShiftedLegendre_collocationA n i j = (lagrangeAntideriv n j).eval (cᵢ)`.
   This uses cycle 308's `butcherShiftedLegendre_collocationA` definition
   plus Phase A.4 at `c := cᵢ`.

2. **Recognise LHS as a quadrature sum**: define the polynomial
   `φ := Polynomial.X^(k-1) * lagrangeAntideriv n j`. Then LHS =
   `∑ᵢ bᵢ · φ(cᵢ)`.

3. **Apply B(2n) exactness** (cycle 304) to `φ`: need
   `φ.natDegree ≤ (k − 1) + n ≤ 2n − 1 < 2n` (use Phase A.3).
   Gives LHS = `∫₀¹ φ(x) dx = ∫₀¹ x^(k-1) · (lagrangeAntideriv).eval x dx`.

4. **IBP**: use `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`
   with `u(x) := (lagrangeAntideriv n j).eval x` and
   `v(x) := x^k / k`. Then `u'(x) = Lⱼ.eval x` (Phase A.1 lifted via
   `Polynomial.hasDerivAt`) and `v'(x) = x^(k-1)` (chain rule;
   `hasDerivAt_pow` divided by `k > 0`).

   The IBP identity gives:
   ```
   ∫₀¹ u(x) · v'(x) dx
     = [u(x) · v(x)]₀¹ − ∫₀¹ u'(x) · v(x) dx
     = (1/k) · (lagrangeAntideriv).eval 1 − (1/k) · ∫₀¹ Lⱼ(x) · x^k dx
   ```

5. **Identify the boundary term** `(lagrangeAntideriv).eval 1`:
   - via Phase A.4: `(lagrangeAntideriv).eval 1 = ∫₀¹ Lⱼ.eval x dx`
   - which by definition (Section342:6233) equals
     `butcherShiftedLegendre_quadratureWeights n j`.
   So boundary term = `bⱼ`.

6. **Substitute Phase B** for the remainder:
   `∫₀¹ Lⱼ(x) · x^k dx = ∫₀¹ x^k · Lⱼ(x) dx = bⱼ · cⱼ^k`.

7. **Close with `field_simp` + `ring`**:
   LHS = `bⱼ/k − (1/k) · bⱼ · cⱼ^k = (bⱼ/k) · (1 − cⱼ^k)` = RHS. ✓

**LOC budget** for Phase C: ~100 LOC (the IBP setup is the heaviest
single step; Phase A and B reduce the remaining algebra to
straightforward `ring`/`field_simp`).

### Phase D — Non-vacuity witnesses (~15 LOC, must ship if any of A/B/C ships)

After D(n) lands:

```lean
/-- Non-vacuity at n = 2: 2-stage Gauss–Legendre satisfies D(2). -/
example : (butcherGaussLegendreRK 2).SatisfiesD 2 :=
  butcherGaussLegendreRK_satisfiesD 2 (by norm_num)

/-- Round-trip through §321's hand-built gaussLegendre1Stage. -/
example : (OpenMath.Chapter3.Section321.gaussLegendre1Stage).SatisfiesD 1 := by
  rw [← butcherGaussLegendreRK_one_eq_gaussLegendre1Stage,
      ← butcherGaussLegendreRK_one_eq]
  exact butcherGaussLegendreRK_satisfiesD 1 (by norm_num)
```

Mirror cycle 310's non-vacuity examples (line 7080+).

## §D — Risk register and contingencies

| Risk | Severity | Mitigation |
|---|---|---|
| R1: `Polynomial.as_sum_range` name drift in Phase A.1 | LOW | Verify via `lean_local_search "as_sum_range"` before use; fallback `Polynomial.eq_sum_range_C_mul_X_pow` or build inline via `Polynomial.ext` |
| R2: Phase A.3 `Polynomial.natDegree_finset_sum_le` name drift | LOW | Verify name; alternative is per-summand bound + `Finset.le_sum` |
| R3: `Lagrange.natDegree_basis_le` may not exist | LOW | Use `Lagrange.basis`'s defining product (degree ≤ `Finset.univ.card - 1 = n - 1`) inline via `Polynomial.natDegree_prod_le` |
| R4: Mathlib's IBP signature picks wrong derivative side | MEDIUM | Two IBP variants exist; verify the right one with `lean_local_search "integral_mul_deriv"` — cycle 277's `iterated_ibp_XnOneSubXn` (Section342NormSqHelpers.lean) is a working template; copy its skeleton |
| R5: `field_simp` over `(k : ℝ)` for `k : ℕ` with `k ≥ 1` | LOW | Use `have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)` then `field_simp [hk_ne]` |
| R6: Phase C `show` re-statement of `SatisfiesD` body | LOW | Cycle 310's `show` recipe (line 7060–7063) is the template; only the b/c/A substitutions change |
| R7: Building polynomial antiderivative via `Finset.range` blows past 200000 heartbeats | LOW-MED | Decompose A.1–A.4 into independent named lemmas (which the plan already does) |

## §E — What NOT to do

* **Do NOT** attempt `cor:342D` end-to-end (the iff with order 2s).
  That requires §314A elementary-weight infrastructure plus the
  order-2s ↔ trees-up-to-2s equivalence, which is 3–4 cycles of
  separate work. C(n) + D(n) is the legitimate stopping point for
  the §342↔§321 lift in cycle 311.
* **Do NOT** try to derive D(n) "directly from B(2n) + C(n)" without
  the antiderivative-IBP route. The standard B+C ⟹ D derivation
  (Hairer–Wanner I.7) goes through E(n,n) and requires double-sum
  manipulation that is *less* tractable than the IBP route in our
  setup, because we lack a clean E(n,n) infrastructure.
* **Do NOT** introduce `axiom`, `constant`, or `sorry` placeholders.
  Any phase that doesn't close cleanly should be removed before
  commit, not left as a stub. See cycle 149/150 (`def:530B`),
  cycle 200/201 (`thm:381H`), and cycle 138/139 (`thm:550A`
  general-n) for the rollback precedent.
* **Do NOT** raise `maxHeartbeats` above 200000. If Phase A or
  Phase C blows past the default budget, decompose further into
  named sub-lemmas. Cycle 308's collocation-A-matrix definition is
  the template for splitting heavy `simp`-laden proofs.
* **Do NOT** submit to Aristotle this cycle. D(n) is a structural
  proof (IBP + algebraic substitution), not a search-heavy
  identity. Aristotle's strengths are premise selection on tight
  algebraic targets; here the proof structure is fully specified
  and the LOC budget is dominated by mechanical Lean encoding.
  Cycle 282's (342f) recurrence Aristotle attempt stalled twice
  for similar structural reasons.
* **Do NOT** redefine `butcherShiftedLegendre_collocationA` or
  `butcherShiftedLegendre_quadratureWeights`. Both definitions are
  load-bearing for cycles 303–310 and any change would invalidate
  the lift chain. The Phase A antiderivative is a *new* object,
  not a refactor.
* **Do NOT** try to use `Polynomial.integral` from Mathlib. It does
  not exist (verified). Use the explicit `Finset.sum` construction
  in Phase A.

## §F — Cycle 312+ outlook

After D(n) ships, the natural cycle-312 targets are (in priority order):

1. **`thm:342C`** (Gaussian quadrature order conditions equivalence,
   listed as `[ ]` in `plan.md`). The textbook statement
   (Butcher §342 p. 240) is the iff "a Runge–Kutta method has
   order 2s ⇔ B(2s), C(s), D(s)". With cycles 309/310/311 supplying
   B(2n), C(n), D(n), the forward direction (⟸) is the simplifying
   assumptions theorem from §321 (also currently unformalized);
   the reverse direction is a Vandermonde / interpolation argument.
   Likely a 1–2 cycle target after some §321 simplifying-assumptions
   infrastructure.

2. **§314A elementary-weight argument** (currently `[ ]` for
   `thm:314A`). This is the prerequisite for the full `cor:342D`
   capstone. Multi-cycle.

3. **`cor:342D` end-to-end**: once both `thm:342C` and `thm:314A`
   are available, `cor:342D` is a several-line corollary. Plan as
   a Phase 4 of the §342↔§321 lift after at least one of the above
   lands.

4. **Cleanup**: the `sorryAx` leak from cycle 301
   (`_rootsInIoo_card_ge` upstream) propagates through every §342
   theorem consuming `_zeros`. An audit cycle isolating and closing
   that sorry would clean up the axiom profile of every cycle
   308–311 deliverable.

## §G — Single-cycle ship gate

**Minimum acceptable cycle 311 ship**: Phase A + Phase B + at least
one non-vacuity example. Phase C deferred to cycle 312 if needed.

**Target ship**: Phase A + B + C + non-vacuity examples (the full
`butcherGaussLegendreRK_satisfiesD` headline).

**Abort threshold**: if Phase A.4 (FTC bridge) stalls past 90 minutes
of focused work, roll back to "Phase A.1–A.3 + Phase B + one
intermediate sanity example" and ship a partial-progress cycle.
Document the Phase A.4 stall in `.prover-state/task_results/cycle_311.md`
with a concrete recipe so cycle 312's worker can close it.

**Sorry count constraint**: file ships with sorry count 0. No
intermediate scaffolding allowed. If a phase doesn't close, remove
its skeleton before commit.

## §H — File placement and structure

All Phase A/B/C additions go in `OpenMath/Chapter3/Section342.lean`,
appended **after** cycle 310's `butcherGaussLegendreRK_satisfiesC`
non-vacuity witnesses (currently the file's last block, around line
7100+).

Add a new section header before Phase A:

```
/-! ### Phase 3.2 — `D(n)` lift via polynomial antiderivative + IBP (cycle 311)

Cycle 310 shipped the C(n) prong of `cor:342D`; cycle 311 ships the
D(n) prong via the textbook IBP argument (Butcher §342 p. 240).

The proof recipe ...
-/
```

Keep cycle 310's section ordering (collocation exactness → `SatisfiesC`)
as the architectural template; Phase A → B → C mirrors it (antideriv
infrastructure → quadrature-of-`X^k Lⱼ` → `SatisfiesD` capstone).

## §I — Verification before commit

1. `lake env lean OpenMath/Chapter3/Section342.lean` — exits 0.
2. `grep -c sorry OpenMath/Chapter3/Section342.lean` — returns 0.
3. `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section342.lean`
   — returns no matches (tautology scanner clean).
4. `lean_verify OpenMath.Chapter3.Section342.butcherGaussLegendreRK_satisfiesD`
   — returns `[propext, sorryAx, Classical.choice, Quot.sound]`
   (sorryAx leak is pre-existing from cycle 301 upstream, expected).
5. Spot-check the two non-vacuity examples (n=2 and gaussLegendre1Stage
   round-trip) compile.
6. `lake env lean OpenMath/Chapter3.lean` (aggregator) — exits 0,
   confirming no downstream regression.

Update `extraction/formalization_data/lean_status.json`: bump the
cycle reference on the §342 row but **do not** mark `cor:342D` as
formalized (it's still partial — only the C(n) and D(n) prongs ship,
not the full iff). The `lem:342B` row stays `formalized` (cycle 305).

Update `plan.md`: add a one-line cycle 311 closure paragraph to the
`cor:342D` row's existing Phase 3 progress notes (the cycle 310 line
already records C(n); cycle 311 line records D(n)).

Write `.prover-state/task_results/cycle_311.md` documenting the
deliverables, axiom profiles, LOC delta, and Phase C completion
status (full ship vs partial vs abort).

## §J — Commit message template

```
Cycle 311 — §342 D(n) lift: polynomial antiderivative + IBP capstone.

Phase A: butcherShiftedLegendre_lagrangeAntideriv + 4 lemmas (~80 LOC).
Phase B: ∫₀¹ X^k · Lⱼ = bⱼ · cⱼ^k via B(2n) + Kronecker δ (~40 LOC).
Phase C: butcherGaussLegendreRK_satisfiesD via IBP (~100 LOC).
P4: non-vacuity at n=2 + gaussLegendre1Stage round-trip.

All axiom-clean ([propext, sorryAx, Classical.choice, Quot.sound];
sorryAx pre-existing from cycle 301 upstream). Closes 2/3 prongs of
cor:342D (C(n) + D(n)); B(2n) shipped cycle 309. Full cor:342D
capstone deferred to thm:342C + thm:314A multi-cycle effort.
```
