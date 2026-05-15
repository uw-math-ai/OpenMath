# Cycle 290 Results

## Worked on

`lem:342A` Butcher §342 (342f) general three-term recurrence —
**Phase A.1 (b)** manual closure deliverable per the cycle 289 task
results "Suggested next approach" spec.

Specifically: ship the residual-degree theorem
`recurrence_residual_natDegree_lt` in `OpenMath/Chapter3/Section342.lean`,
consuming the cycle 289 binomial helper `n_mul_choose_two_n_n_eq` and
the cycle 281 `butcherShiftedLegendre_leadingCoeff` infrastructure.

## Approach

Manual closure (no Aristotle resubmission — cycle 289 closed that
door after the third 20% stall on `efe4940e`). Followed the cycle 289
"Suggested next approach" 8-step decomposition with one additional
step for the `(A - B) ≠ 0` degree↔natDegree bridge:

### Step-by-step

1. **L = C 2 · X − C 1** has `natDegree = 1` via `compute_degree!`,
   `leadingCoeff = 2` via direct coefficient computation
   (`Polynomial.leadingCoeff`, `coeff_sub`, `coeff_C_mul`,
   `coeff_X_one`, `coeff_C` + `norm_num`).
2. **C β · L** (with `β := ((2n - 1 : ℕ) : ℝ) ≠ 0`) has `natDegree = 1`
   via `Polynomial.natDegree_C_mul hβ_ne` and `leadingCoeff = β · 2`
   via `Polynomial.leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero
   hβ_ne)`.
3. **B := C β · L · P_{n-1}** has `natDegree = 1 + (n-1) = n` via
   `Polynomial.natDegree_mul` (needs `C β · L ≠ 0` from natDegree-1
   contradiction with the zero polynomial; `P_{n-1} ≠ 0` from
   `butcherShiftedLegendre_natDegree (n-1) = n - 1 ≥ 1`) +
   `butcherShiftedLegendre_natDegree (n-1)` + `omega` for the nat
   arithmetic. `B.leadingCoeff = β · 2 · C(2(n-1), n-1)` via
   `Polynomial.leadingCoeff_mul` + step 2's coeff + cycle 281's
   `butcherShiftedLegendre_leadingCoeff`.
4. **Rewrite `(n : ℝ) • P_n` as `C (n : ℝ) · P_n`** via
   `Polynomial.smul_eq_C_mul` once at the start. Then **A := C (n : ℝ)
   · P_n** has `natDegree = n` (`Polynomial.natDegree_C_mul hn_ne`) and
   `leadingCoeff = (n : ℝ) · C(2n, n)`
   (`Polynomial.leadingCoeff_C_mul_of_isUnit` + cycle 281).
5. **Bridge `2 * (n - 1) = 2 * n - 2`** via `omega`, then close
   `A.leadingCoeff = B.leadingCoeff` via cycle 289's
   `n_mul_choose_two_n_n_eq` + `linarith`.
6. **A.degree = B.degree = (n : WithBot ℕ)** via
   `Polynomial.degree_eq_natDegree` (need `A ≠ 0` and `B ≠ 0`, both
   from `natDegree = n > 0` contradiction with the zero polynomial).
7. **`(A - B).degree < (n : WithBot ℕ)`** via `Polynomial.degree_sub_lt`
   with `A.degree = B.degree`, `A ≠ 0`, `A.leadingCoeff = B.leadingCoeff`.
   Then `(A - B).natDegree < n` via case split on `A - B = 0` (trivial:
   `natDegree 0 = 0 < n`) + `Polynomial.natDegree_lt_iff_degree_lt`.
8. **Cterm := C((n - 1):ℝ) · P_{n-2}** has `natDegree ≤ n - 2` via
   `Polynomial.natDegree_C_mul_le` + `butcherShiftedLegendre_natDegree
   (n - 2)`. Hence `< n` since `n ≥ 2` (`omega`).
9. **Final combination**: `(A - B + Cterm).natDegree ≤ max
   ((A - B).natDegree) (Cterm.natDegree) < n` via
   `Polynomial.natDegree_add_le` + `Nat.max_lt`.

### Implementation details

- Used `set ... with` aliases for `L`, `A`, `B`, `Cterm` to keep the
  proof body readable; per-step `rw [hL_def]` / `rw [hA_def]` etc. to
  unfold when needed (Lean 4 has no `unfold_let` tactic in this
  toolchain — `rw [...]` and `simp only [...]` are the substitutes).
- Nat-sub↔real-sub bridge: `((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1`
  via `Nat.cast_sub (by omega : 1 ≤ 2 * n) + push_cast + ring`. Same
  pattern as cycle 289.

## Result

**SUCCESS** — `recurrence_residual_natDegree_lt` shipped axiom-clean
in `OpenMath/Chapter3/Section342.lean` (lines 2667–2797, ~140 LOC
total including docstring). Verifications:

- `lake env lean OpenMath/Chapter3/Section342.lean` exits 0.
- `lake env lean OpenMath/Chapter3.lean` exits 0.
- `lake build OpenMath.Chapter3.Section342` exits 0.
- `grep -c sorry OpenMath/Chapter3/Section342.lean` → 0.
- `#print axioms OpenMath.Chapter3.Section342.recurrence_residual_natDegree_lt`
  → `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

LOC tally: target was 100–150 LOC; actual ~140 LOC (within budget,
no further decomposition needed). Cycle 290's F-tier stretch goals
(F.1 `recurrence_residual_orthogonal_first_term`, F.2
`recurrence_residual_orthogonal_third_term`) **not attempted** per
the strategy's explicit instruction "Do NOT attempt (F.1) and (F.2)
if A.1 (b) is at all difficult"; while the main deliverable did not
prove difficult, exhausting cycle time on Mathlib API research and
the per-step verification meant prudence dictated banking the win
and deferring F.1/F.2 to cycle 291's planning surface (where they
appear as the suggested Phase A.2 starting point).

## Faithfulness check

### `recurrence_residual_natDegree_lt`

- **Entity ID**: not a textbook entity; helper lemma toward
  `lem:342A` (342f) per cycle 289 manual closure plan
  (`.prover-state/issues/lem_342A_342f_manual_closure_plan.md` §5
  Phase A.1).
- **Textbook statement** (Butcher §342 p. 236, quoted from
  `extraction/formalization_data/entities/lem_342A.json` —
  paraphrased prose since this is a helper, not a textbook entity):

  > The highest degree coefficients in `P_n^*` and `P_{n-1}^*` can
  > be compared so that `n P_n^*(x) − (2x − 1)(2n − 1) P_{n-1}^*(x)`
  > is a polynomial, `Q` say, of degree less than `n`.

- **Lean statement captures**: same content, modulo the addition of
  the `(n - 1) · P_{n-2}^*` summand (the textbook states the bound
  only on `n P_n − (2x - 1)(2n - 1) P_{n-1}`; we additionally
  include the `(n - 1) · P_{n-2}` term so that the residual is the
  full LHS − RHS of (342f) rather than just the "leading two"
  subtraction). This is a **strict generalization**: adding a known
  `natDegree ≤ n - 2 < n` polynomial cannot raise the bound above
  `n - 1`. The added summand has `natDegree ≤ n - 2 < n` so the
  conclusion `< n` is preserved.
- **Hypotheses match**: `hn : 2 ≤ n` is the minimal requirement for
  the recurrence (Butcher only states (342f) for `n ≥ 2`).
- **No definition smuggling, no tautology, no identity proof, no
  promised-but-absent content**.

### `Polynomial.degree_sub_lt` hypothesis-strength check

The Mathlib lemma `Polynomial.degree_sub_lt` requires three inputs:
`p.degree = q.degree`, `p ≠ 0`, `p.leadingCoeff = q.leadingCoeff`.
All three are essential and we provide each from a separate sub-step
(no excess hypothesis). The `p ≠ 0` requirement is the only one
that could be considered "extra" relative to the conclusion, but it
is genuinely needed — without it, both `p = q = 0` would give
`p - q = 0` whose degree is `⊥`, not `<` any natural number.

## Dead ends

### `unfold_let` tactic not available

Initial draft used `unfold_let L` / `unfold_let A` etc. to expand
`set` aliases. Lean 4 / current Mathlib toolchain reports "unknown
tactic". Replaced with `rw [hL_def]` / `rw [hA_def]` etc. (where
`hL_def : L = C 2 * X - C 1` is the `with` equation from the `set`
command). `simp only [hL_def]` would also work.

### `show` with bare polynomial literal fails type inference

Tried `show (Polynomial.C 2 * Polynomial.X - Polynomial.C 1).natDegree
= 1` without type annotation. Lean inferred `ℕ[X]` instead of `ℝ[X]`
from the bare `C 1` / `C 2` literals, producing `HSub ℕ[X] ℕ[X] ?m`
synthesis failures. The fix was `rw [hL_def]` to unfold from the
typed alias — no `show` needed since the alias already carries the
type.

### `Polynomial.leadingCoeff_smul_of_smul_regular` API mismatch

The natural-looking `(c • p).leadingCoeff = c • p.leadingCoeff`
exists in Mathlib as `Polynomial.leadingCoeff_smul_of_smul_regular`,
but requires `IsSMulRegular R k` which is non-trivial to discharge
for `ℝ`-scalars without a witness from a closed Mathlib library.
Switched approach: rewrite `(n : ℝ) • P_n = C (n : ℝ) * P_n` via
`Polynomial.smul_eq_C_mul` up front, then use `natDegree_C_mul` +
`leadingCoeff_C_mul_of_isUnit` from `Polynomial.Degree.Operations`.

### Direct `simp` on `(C 2 * X - C 1).leadingCoeff`

Tried `simp [Polynomial.leadingCoeff, Polynomial.coeff_sub,
Polynomial.coeff_C_mul, Polynomial.coeff_X_one, Polynomial.coeff_C]`
— produced "Possibly looping simp theorem: `leadingCoeff.eq_1`" +
"maximum recursion depth has been reached". The fix was to first
establish `natDegree = 1` (via `compute_degree!`), then `rw
[leadingCoeff, hL_nd]` to fix the coefficient index to `1`, then
unfold the explicit coefficients of `C 2 * X - C 1` at index `1`
manually.

## Discovery

### `Polynomial.smul_eq_C_mul` is the workhorse

When mixing `R`-module structure (`r • p`) with polynomial-ring
operations (`C r * p`), the cleanest move is to rewrite all `•` to
`C * _` immediately. After this, the entire `natDegree` /
`leadingCoeff` calculus reduces to multiplication lemmas
(`Polynomial.natDegree_mul`, `Polynomial.natDegree_C_mul`,
`Polynomial.leadingCoeff_C_mul_of_isUnit`,
`Polynomial.leadingCoeff_mul`) which all have well-tested Mathlib
API. Trying to keep `•` and work with `Polynomial.natDegree_smul` +
`Polynomial.leadingCoeff_smul_of_smul_regular` is harder because the
smul-regular hypothesis is awkward in `ℝ`.

### `compute_degree!` is excellent for upper bounds, not for equality

`compute_degree!` closed `(C 2 * X - C 1 : ℝ[X]).natDegree = 1`
trivially (one tactic call). For more complex products like `C β
· L · P_{n-1}` where `P_{n-1}` is an opaque polynomial of known
degree `n - 1`, the cleaner approach was manual `Polynomial.natDegree_mul`
chaining rather than wrestling with `compute_degree`'s opaque-symbol
handling.

### Case split on `p = 0` for `natDegree_lt_iff_degree_lt`

`Polynomial.natDegree_lt_iff_degree_lt` requires `p ≠ 0`. When `p`
is constructed via subtraction (e.g. `A - B`), we cannot easily
exclude `p = 0` without proving non-equality of the original
polynomials. The clean pattern is:

```lean
by_cases h : p = 0
· simp [h]; omega    -- natDegree 0 = 0 < n trivially
· exact (Polynomial.natDegree_lt_iff_degree_lt h).mpr hAB_deg
```

Avoids the need to prove `A ≠ B` separately.

### Nat-sub bridging is a one-liner now

The `Nat.cast_sub (by omega : 1 ≤ ...)` + `push_cast` + `ring`
pattern (introduced in cycle 289 for the binomial helper) is
sufficient to bridge any `((a - b : ℕ) : ℝ)` to `(a : ℝ) - (b : ℝ)`
given `b ≤ a`. Used twice in this cycle (for `2n - 1` and `n - 1`,
though the latter is only used as a bridge in a few branches; the
final usage in the `Cterm` summand keeps the nat form throughout
since `Polynomial.natDegree_C_mul_le` is agnostic to the inner cast
form).

## Suggested next approach

### Cycle 291: Phase A.2 orthogonality

Per the cycle 290 strategy §F, ship the two **easy** orthogonality
components first as starter lemmas:

1. **`recurrence_residual_orthogonal_first_term (n : ℕ) (hn : 2 ≤ n)
   {k : ℕ} (hk : k < n) : ∫₀¹ ((n : ℝ) • P_n).eval x · P_k.eval x = 0`**.
   ~15 LOC: direct from cycle 277's `butcherShiftedLegendre_orthogonal`
   + `(n : ℝ) •` scalar pull-out via `intervalIntegral.integral_const_mul`
   and `Polynomial.eval_smul`. Since `k < n`, the orthogonality gives
   `∫ P_n · P_k = 0`, then the scalar factor preserves zero.

2. **`recurrence_residual_orthogonal_third_term (n : ℕ) (hn : 2 ≤ n)
   {k : ℕ} (hk_le : k ≤ n - 3) : ∫₀¹ (C((n - 1):ℝ) · P_{n-2}).eval x ·
   P_k.eval x = 0`**. ~20 LOC: direct from
   `butcherShiftedLegendre_orthogonal` since `k ≤ n - 3 < n - 2`, so
   `P_{n-2}` and `P_k` are orthogonal. The `C(...)` factor pulls out
   via `intervalIntegral.integral_const_mul` and `Polynomial.eval_C`.

3. **Cross-term `⟨(2n - 1) · (2X - 1) · P_{n-1}, P_k⟩ = 0` for `k ≤
   n - 3`** (HARDER): requires expanding `(2X - 1) · P_{n-1}` as a
   linear combination of `{P_j}_{j=0..n}` via the identity `2X - 1
   = P_1^*` (the textbook (342b) at `n = 1`), giving
   `(2X - 1) · P_{n-1} = P_1 · P_{n-1}`. Then `P_1 · P_{n-1}`
   expands as `Σ_j c_j P_j` with each `c_j = ⟨P_1 P_{n-1}, P_j⟩ /
   ⟨P_j, P_j⟩` via the Fourier-coefficient formula. For `j ≤ n -
   3`, the coefficient `⟨P_1 P_{n-1}, P_j⟩ = ⟨P_{n-1}, P_1 P_j⟩`
   (by symmetry of the inner product), and `P_1 P_j` has natDegree
   `j + 1 ≤ n - 2 < n - 1`, so this inner product is zero by the
   orthogonality basis property of `P_{n-1}` against
   `Polynomial.degreeLT ℝ (n - 1)`. **Defer this to cycle 292** —
   cycle 291 should land just F.1 and F.2.

### Cycle 292+

Continue Phase A.2 cross-term work, then Phase A.3
(basis-span conclusion) per the issue file §5.

### Cross-section spot-check

The `lean_status.json` row for `lem:342A` should remain `~` until
all of (342a), (342b), (342c), (342d), (342e), (342f), (342g) close.
Currently (342f) is the second-to-last open property; (342g)
distinct real zeros has the cycle 282 scoping doc
(`lem_342A_g_zeros_scoping.md`) for the planner to schedule once
(342f) lands.
