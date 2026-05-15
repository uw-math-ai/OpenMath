# Scoping: lem:342A (342f) — manual closure of the general three-term recurrence

## Status

After three consecutive observations of Aristotle project
`efe4940e-0931-4fb2-8549-7eafab20d7f7` (general (342f) resubmission
from cycle 285) IN_PROGRESS at exactly **20%** — cycle 287
(2026-05-15T18:35Z), cycle 288 (2026-05-15T18:51Z), cycle 289
(2026-05-15T19:10Z) — cycle 289 cancelled the project under the cycle
285 three-stall protocol and pivots to manual closure.

The empirical evidence base for the recurrence spans `n ∈ {2..11}` as
of cycle 288 (`butcherShiftedLegendre_recurrence_two` through
`_recurrence_eleven`, lines 2340–2567 of `Section342.lean`). All are
axiom-clean. Further ladder extension provides no new information.

## §1 Textbook statement (Butcher §342, p. 236, equation 342f)

> `n P_n^*(x) = (2x - 1)(2n - 1) P_{n-1}^*(x) - (n - 1) P_{n-2}^*(x)`,
> for `n = 2, 3, 4, …`.

Quoted from `extraction/formalization_data/entities/lem_342A.json`.

## §2 Textbook proof distilled (Butcher §342, p. 236)

> The highest degree coefficients in `P_n^*` and `P_{n-1}^*` can be
> compared so that `n P_n^*(x) − (2x − 1)(2n − 1) P_{n-1}^*(x)` is a
> polynomial, `Q` say, of degree less than `n`. … A simple calculation
> shows that `Q` is orthogonal to `P_k^*` for `k < n − 2`. Hence,
> (342f) follows except for the value of the `P_{n-2}^*` coefficient,
> which is resolved by substituting `x = 1`.

Three steps:
1. Show `Q := n·P_n^* − (2n-1)·(2X-1)·P_{n-1}^* + (n-1)·P_{n-2}^*`
   has `natDegree < n` via leading-coefficient cancellation.
2. Show `⟨Q, P_k^*⟩ = 0` for `k ∈ {0, 1, …, n-2}` (orthogonality of
   each summand against `P_k^*`).
3. Conclude `Q = 0` since `Q ∈ degreeLT n` lies in the orthogonal
   complement of an `n`-dimensional spanning set of `degreeLT n`.

(The textbook also uses parity (342c) to get `natDegree Q < n − 1` and
needs orthogonality only for `k < n − 2`. We use the slightly stronger
formulation `k ≤ n − 2` to avoid threading parity into Phase A.1.)

## §3 Project-hook inventory (already shipped, axiom-clean)

| Need | Lean symbol | Source | Cycle |
|------|-------------|--------|-------|
| `P_n^*` definition | `butcherShiftedLegendre n` | `Section342.lean:65` | 271 |
| `(342a)` orthogonality | `butcherShiftedLegendre_orthogonal` | `Section342.lean:1314` | 277 |
| `(342b)` eval at 1 | `butcherShiftedLegendre_eval_one` | `Section342.lean:97` | 271 |
| `(342c)` parity | `butcherShiftedLegendre_eval_one_sub` | `Section342.lean:117` | 272 |
| `(342d)` norm-sq | `butcherShiftedLegendre_norm_sq` | `Section342.lean:2252` | 281 |
| `(342e)` Rodrigues | `butcherShiftedLegendre_rodrigues` | `Section342.lean:177` | 277 |
| `natDegree = n` | `butcherShiftedLegendre_natDegree` | `Section342.lean:241` | 273 |
| `leadingCoeff = C(2n,n)` | `butcherShiftedLegendre_leadingCoeff` | `Section342.lean:2213` | 281 |
| `eval at 0 = (-1)^n` | `butcherShiftedLegendre_eval_zero` | `Section342.lean:256` | 273 |
| Explicit `P_0..P_11` | `butcherShiftedLegendre_zero/.../eleven` | `Section342.lean:265–999` | 271–288 |
| `n=2..11` recurrence | `butcherShiftedLegendre_recurrence_two/.../eleven` | `Section342.lean:2340–2567` | 282–288 |

Mathlib hooks:
- `Polynomial.degree_sub_lt` (verified via leansearch cycle 289):
  ```
  p.degree = q.degree → p ≠ 0 → p.leadingCoeff = q.leadingCoeff
    → (p - q).degree < p.degree
  ```
- `Polynomial.natDegree_smul_le`, `Polynomial.natDegree_mul_le`,
  `Polynomial.natDegree_C_mul_le`, `Polynomial.natDegree_X_sub_C` —
  standard degree-bound API.
- `Polynomial.leadingCoeff_mul` (over `ℝ` no integral-domain trouble).
- `Nat.choose_eq_factorial_div_factorial`, `Nat.factorial_succ` for
  the binomial identity.

## §4 Gap inventory

Nothing fundamental. The proof routes through degree arithmetic and
existing orthogonality. No new Mathlib gap is anticipated. Risk is
purely LOC budget and decomposition discipline.

## §5 Phase decomposition (Path A: polynomial-degree closure)

### Phase A.1 — Residual has `natDegree < n` (cycle 289 + possibly 290)

Two sub-deliverables:

**(a) Binomial identity helper**
```lean
private lemma n_mul_choose_two_n_n_eq (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * (Nat.choose (2 * n) n : ℝ)
      = 2 * ((2 * n - 1 : ℕ) : ℝ) * (Nat.choose (2 * n - 2) (n - 1) : ℝ)
```
Paper-verified: both reduce to `(2n)! / ((n-1)! · n!)`. Closure via
`Nat.choose_eq_factorial_div_factorial` + `Nat.factorial_succ` ×2 +
`field_simp` + `ring`. Estimated 30–50 LOC.

**(b) Residual-degree main theorem**
```lean
theorem recurrence_residual_natDegree_lt (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℝ) • butcherShiftedLegendre n
      - Polynomial.C ((2 * n - 1 : ℕ) : ℝ)
        * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre (n - 1)
      + Polynomial.C ((n - 1 : ℕ) : ℝ)
        * butcherShiftedLegendre (n - 2)).natDegree < n
```
Proof via `Polynomial.degree_sub_lt` on `n·P_n^*` vs the `(2n-1)·(2X-1)·
P_{n-1}^*` term (both have `natDegree = n`, equal leading coefficients
by the helper above), bounded by `natDegree (n-1)·P_{n-2}^* ≤ n-2 < n`.
Estimated 80–120 LOC.

If (a)+(b) exceed 150 LOC, ship (a) in cycle 289 and defer (b) to
cycle 290. Phase A.1 must be axiom-clean — no sorries.

### Phase A.2 — Residual is orthogonal to `P_k^*` for `k ∈ {0, …, n-2}` (cycle 291)

Three orthogonality components:
- `⟨n·P_n^*, P_k^*⟩ = 0` for `k < n` — direct from (342a).
- `⟨(n-1)·P_{n-2}^*, P_k^*⟩ = 0` for `k ≠ n-2` — direct from (342a).
  For `k = n-2`, equals `(n-1) · ⟨P_{n-2}^*, P_{n-2}^*⟩` which is the
  (342d) norm-square at `n-2`. Cross-check: this matches the textbook's
  "Hence (342f) follows except for the value of the `P_{n-2}^*`
  coefficient" remark — Phase A.2 needs `k ≤ n − 3` strictly.
- `⟨(2n-1)·(2X-1)·P_{n-1}^*, P_k^*⟩ = 0` for `k < n-2`.
  Use `2X - 1 = -P_1^*` (cycle 273's `butcherShiftedLegendre_one`)
  to reduce to `-⟨P_1^* · P_{n-1}^*, P_k^*⟩`. Since `deg (P_1^* ·
  P_{n-1}^*) = n`, this is *not* immediate from (342a). The actual
  argument is: write `P_1^* · P_{n-1}^*` in the basis `{P_0^*, …,
  P_n^*}` and observe the only `P_k^*` components surviving against
  the `P_k^*` test function are at `k ∈ {n-2, n-1, n}`. For
  `k ≤ n-3`, the inner product vanishes. Estimated 100–150 LOC.

Refined formulation: actually, the textbook says `k < n - 2`, so the
constant resolves via `x = 1` substitution. The clean formulation may
be `⟨Q, P_k^*⟩ = 0 for k ≤ n - 3`, then `Q = c · P_{n-2}^*` is shown
to satisfy `c = 0` by evaluating both sides at `x = 1` using (342b).

### Phase A.3 — Conclude `Q = 0` (cycle 292)

Either:
- Combine `natDegree Q < n` + orthogonality to `P_k^*` for all
  `k ≤ n-2` via the basis spanning argument
  (`Polynomial.degreeLT ℝ n = LinearMap.span {P_0^*, …, P_{n-1}^*}`).
- Or do `Q ∈ degreeLT (n-1)` (use parity), spanned by `P_0^*, …,
  P_{n-2}^*`, and orthogonality to all of these forces `Q = 0` (then
  the `P_{n-2}^*` slot is constrained by both orthogonality and the
  `x = 1` evaluation, which fixes the coefficient).

Estimated 60–100 LOC.

## §6 Risk assessment

| Phase | LOC | Cycles | Risk |
|-------|-----|--------|------|
| A.1 | 110–170 | 1–2 | low — pure degree arithmetic |
| A.2 | 200–300 | 2 | medium — orthogonality basis reasoning |
| A.3 | 60–100 | 1 | low — Gram-Schmidt-style argument |
| Total | 370–570 | 3–4 | medium overall |

Best case 3 cycles (290–292), worst case 5 cycles. No new Mathlib gap
expected.

## §7 Cycle 290 entry point

If cycle 289 shipped Phase A.1 helper only: open cycle 290 with Phase
A.1 main theorem `recurrence_residual_natDegree_lt`.

If cycle 289 shipped both helper and main theorem: open cycle 290
with Phase A.2 setup — start with the easy components:
- `recurrence_residual_orthogonal_first_term` (`⟨n·P_n^*, P_k^*⟩ = 0`)
- `recurrence_residual_orthogonal_third_term` (`⟨(n-1)·P_{n-2}^*,
  P_k^*⟩ = 0`)
Save the cross-term `⟨(2n-1)·(2X-1)·P_{n-1}^*, P_k^*⟩` decomposition
for cycle 291.

## §8 What NOT to do

- **Do NOT resubmit (342f) to Aristotle.** Three consecutive 20%
  stalls is dispositive. Manual closure per this plan only.
- **Do NOT pursue Möbius / Pascal-identity manual closures.** Cycle
  273 documented those paths as too complex without (342a)
  infrastructure; Path A above (degree-bound + orthogonality basis)
  is the clean route with the now-shipped (342a)/(342d)/Rodrigues
  infrastructure.
- **Do NOT extend the empirical ladder past `n = 11`.** Per cycle
  285's protocol, the empirical base at `n ∈ {2..11}` is sufficient.
- **Do NOT introduce `sorry`/`axiom`/`constant`.** Phase A.1
  deliverables must be axiom-clean.

## §9 Cross-references

- `extraction/formalization_data/entities/lem_342A.json` — textbook
  statement and dependencies.
- `OpenMath/Chapter3/Section342.lean:2213–2225` —
  `butcherShiftedLegendre_leadingCoeff` (cycle 281).
- `OpenMath/Chapter3/Section342.lean:241–249` —
  `butcherShiftedLegendre_natDegree` (cycle 273).
- `OpenMath/Chapter3/Section342.lean:1314–1383` —
  `butcherShiftedLegendre_orthogonal` (cycle 277, full (342a)).
- `OpenMath/Chapter3/Section342.lean:2340–2567` — recurrence ladder
  `n ∈ {2..11}` (cycles 282–288).
- `OpenMath/Chapter3/Section342NormSqHelpers.lean` — reusable
  polynomial/integral lemmas (cycle 281's pattern for factored helpers).
- `.prover-state/issues/lem_342A_g_zeros_scoping.md` — sibling
  (342g) plan; depends on (342f) landing.
- `.prover-state/issues/lem_441A_phase_C_scoping.md` — template
  for this scoping doc's structure (cycle 180).

## §10 Closes

This is a scoping document for cycle 290+. Cycle 289 itself ships
the Phase A.1 helper lemma (binomial identity) and — if LOC budget
allows — the main residual-degree theorem.

### Cycle 289 update — Phase A.1 (a) SHIPPED, (b) deferred

Cycle 289 shipped Phase A.1 deliverable (a), the binomial identity
helper:

```lean
private lemma n_mul_choose_two_n_n_eq (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * (Nat.choose (2 * n) n : ℝ)
      = 2 * ((2 * n - 1 : ℕ) : ℝ) * (Nat.choose (2 * n - 2) (n - 1) : ℝ)
```

Located in `OpenMath/Chapter3/Section342.lean` immediately after
`butcherShiftedLegendre_recurrence_eleven`. ~80 LOC including
docstring. Proof route exactly as planned: `Nat.choose_mul_right` +
`Nat.choose_eq_choose_pred_add` (Pascal) + `Nat.choose_succ_right_eq`,
combined via `linear_combination (-2) * step2` on a real-cast
formulation. Verified axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

Phase A.1 (b) — `recurrence_residual_natDegree_lt` — deferred to
cycle 290. The degree arithmetic is non-trivial in scope:

1. `((C 2 * X - C 1) : Polynomial ℝ).natDegree = 1` and
   `.leadingCoeff = 2` — needs `natDegree_add_eq_left_of_natDegree_lt`
   + `leadingCoeff_add_of_degree_lt'` or `compute_degree!`.
2. `((C 2 * X - C 1) * P_{n-1}).natDegree = n` and
   `.leadingCoeff = 2 · C(2(n-1), n-1)` — needs `natDegree_mul`
   over `NoZeroDivisors`.
3. `(C β * (C 2 * X - C 1) * P_{n-1}).natDegree = n` and
   `.leadingCoeff = β · 2 · C(2n - 2, n - 1)` — needs
   `leadingCoeff_C_mul_of_isUnit`.
4. `(n • P_n).natDegree = n` and `.leadingCoeff = n · C(2n, n)` —
   needs `Polynomial.natDegree_smul` + `leadingCoeff_smul`.
5. Equality of (3)'s and (4)'s leading coefficients — the cycle 289
   helper provides this.
6. `Polynomial.degree_sub_lt` ⇒ `(A − B).degree < n`.
7. `(C (n - 1)) * P_{n-2}.natDegree ≤ n − 2 < n`.
8. `natDegree_add_le` + `Nat.max_lt` ⇒ residual `natDegree < n`.

Estimated 100–150 LOC. The piecewise degree arithmetic, while
mechanical, exceeds the cycle 289 LOC budget when added to (a) +
the issue file + the cycle 289 task results / lean_status / plan
updates. Cycle 290 should open with this as the entire deliverable.

### Cycle 290 entry point (revised)

Open cycle 290 with Phase A.1 (b): `recurrence_residual_natDegree_lt`
using the cycle 289 helper. Decompose into the 8 steps above, ship
each as a private lemma if it doesn't condense to one or two `simp`
lines. Target axiom-clean.

After (b) lands, Phase A.2 setup is the next priority.
