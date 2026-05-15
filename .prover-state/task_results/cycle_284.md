# Cycle 284 Results

## Worked on
- §342 (342f) recurrence ladder rung at `n = 8` (Branch B per strategy):
  - `butcherShiftedLegendre_eight` — explicit closed form for `P_8^*`.
  - `butcherShiftedLegendre_recurrence_eight` — concrete recurrence
    witness `8 · P_8^* = 15(2X − 1) · P_7^* − 7 · P_6^*`.

## Approach
1. P0 single-poll Aristotle project `c8b8f138-f875-4263-94ec-74533b5120d7`
   (general (342f) recurrence). Result: **IN_PROGRESS at 12%**
   (created 17:14 UTC, last update 17:45 UTC — stalled at the same %
   as the cycle 283 poll). Per strategy §A Branch B, pivoted
   immediately to manual ladder extension.
2. Cross-checked the recurrence coefficients at n=8 by hand via Python
   integer arithmetic before writing any Lean:
   - LHS `= 8·P_8^* = 102960x⁸ − 411840x⁷ + 672672x⁶ − 576576x⁵
     + 277200x⁴ − 73920x³ + 10080x² − 576x + 8`.
   - RHS `= 15·(2X − 1)·P_7^* − 7·P_6^*` evaluates to the same vector
     of nine coefficients. (Python `MATCH: True` printed.)
3. Computed the explicit-form coefficients for `P_8^*` from the
   `coeff_shiftedLegendre k = (-1)^k · C(n,k) · C(n+k,n)` identity at
   n=8: `(1, -72, 1260, -9240, 34650, -72072, 84084, -51480, 12870)`.
   Outer Butcher sign `(-1)^8 = 1` leaves them unflipped.
4. Wrote `butcherShiftedLegendre_eight` via cycle 276's peel-off
   pattern `unfold ; ext k ; simp only [coeff_C_mul, coeff_map,
   coeff_shiftedLegendre] ; match k with ...` and a per-`k` case-split
   `k ∈ {0..8, k+9}` with `decide`-helpers for the eight `Nat.choose`
   values from C(9,8)=9 up to C(16,8)=12870 (plus the secondary
   C(8,j) values for `j ∈ {2..7}`) and per-arm `norm_num`. Tail closed
   via `Nat.choose_eq_zero_of_lt`.
5. Wrote `butcherShiftedLegendre_recurrence_eight` via the cycle 283
   `Polynomial.funext + simp [eval_*] + ring` recipe (10 LOC body).
6. Ran the closure checklist:
   - `lake env lean OpenMath/Chapter3/Section342.lean` → exit 0,
     0 errors, 0 sorries.
   - `lake build OpenMath.Chapter3.Section342` → completed; aggregator
     `OpenMath/Chapter3.lean` clean.
   - `#print axioms butcherShiftedLegendre_eight` → `[propext,
     Classical.choice, Quot.sound]`.
   - `#print axioms butcherShiftedLegendre_recurrence_eight` →
     `[propext, Classical.choice, Quot.sound]`.

## Result
**SUCCESS** — Branch B shipped both deliverables axiom-clean.
`Section342.lean` LOC count 2020 → ~2123. Sorry count remains 0.
Aristotle `c8b8f138` left running (no poll beyond §A this cycle, per
CLAUDE.md rule).

## Faithfulness check

### `butcherShiftedLegendre_eight`
- Entity ID: `lem:342A` (helper / concrete witness for the family
  `P_n^*`, n=8 case).
- Textbook statement (from `formalization_data/entities/lem_342A.json`,
  property (342e) applied at n=8):
  > `P_n^*(x) = (1/n!) (d/dx)^n ((x²−x)^n)`, n = 0, 1, 2, ….
- Lean statement captures: **same content** specialised at n=8 via
  the equivalent coefficient-formula route. The polynomial
  `12870 X^8 − 51480 X^7 + 84084 X^6 − 72072 X^5 + 34650 X^4
  − 9240 X^3 + 1260 X^2 − 72 X + 1` is the unique degree-8 polynomial
  on [0, 1] that agrees with `(1/8!) · (d/dx)^8 ((x²−x)^8)` (via the
  cycle 272 Rodrigues bridge and Mathlib's
  `Polynomial.coeff_shiftedLegendre`). Sanity: `P_8^*(0) = 1 = (-1)^8`
  and `P_8^*(1) = 12870 − 51480 + 84084 − 72072 + 34650 − 9240 + 1260
  − 72 + 1 = 1` (matching (342b)).

### `butcherShiftedLegendre_recurrence_eight`
- Entity ID: `lem:342A` (clause (342f) concrete witness at n=8).
- Textbook statement (from `formalization_data/entities/lem_342A.json`):
  > `n P_n^*(x) = (2x − 1)(2n − 1) P_{n-1}^*(x) − (n − 1) P_{n-2}^*(x)`,
  > n = 2, 3, 4, ….
- Lean statement captures: **same content** specialised at n=8.
  At n=8: `(2n − 1, n − 1) = (15, 7)`, and the textbook factor
  `(2x − 1)(2n − 1)` is realized as `C 15 · (C 2 · X − C 1)`. The
  Lean LHS uses `(8 : ℝ) • butcherShiftedLegendre 8` rather than
  `C 8 · …` to match the cycle 282 ladder convention (the scalar
  factor `(8 : ℝ)` is provably `C 8` via `Polynomial.C_eq_natCast` +
  `smul_eq_C_mul`, but the `(•)` form is `ring`-friendly).
- No hypothesis strengthening (the statement is unconditional at n=8);
  no definition smuggling (the textbook (342f) is a polynomial-ring
  identity, and the Lean version proves the same identity over `ℝ[X]`).

## Dead ends
None — both recipes from the strategy worked on first compile.

## Discovery
- Aristotle `c8b8f138` has now logged two consecutive 12% readings
  (cycle 283 at 15 min, cycle 284 at 31 min). At the cycle 277/281
  precedent for `d4ce527b` (342d general), Aristotle showed a steady
  ~+5%/cycle climb; the present stall is the first time a §342
  submission has stagnated. Two readings are still within normal
  variance — cycle 285 should poll again before considering
  cancel-and-resubmit. If cycle 285 still reads 12%, the cycle 285
  planner should consider whether the cycle 282 submission prompt
  needs strengthening with explicit Mathlib hooks (e.g. the
  cycle 277 `integral_poly_mul_iterDeriv_vanish` helper, which gives
  the orthogonality machinery Aristotle would need for the
  `Q ⊥ P_k^*` step).
- The cycle 276 onward peel-off pattern continues to scale linearly:
  cycles 276 → 277 → 278 → 279 → 280 → 284 each added one degree to
  the explicit-form ladder at ~80 LOC per rung with no proof-engineering
  surprises. The bottleneck is now the `decide`-time of the
  `Nat.choose 16 8 = 12870` evaluations (still <1s at n=8).

## Suggested next approach
**For cycle 285 planner**:
1. **P0**: single-poll Aristotle `c8b8f138`. If still IN_PROGRESS at
   12% (three consecutive stalls), seriously consider cancelling and
   resubmitting with a stronger prompt:
   - Include the cycle 277 `integral_poly_mul_iterDeriv_vanish` lemma
     as an axiom (gives Aristotle the iterated-IBP orthogonality
     machinery without forcing it to redo cycle 277's work).
   - Cite the textbook proof sketch verbatim from the
     `formalization_data` entry: degree+parity reasoning on
     `Q := LHS − RHS`.
   - Add the cycle 281 `butcherShiftedLegendre_leadingCoeff` private
     bridging lemma (gives Aristotle the `(2n)!/(n!)²` leading-coefficient
     identity without forcing it to rederive Rodrigues differentiation).
2. **P1** (Branch B if Aristotle stalls): extend the ladder to `n = 9`.
   Coefficient computation:
   - Coefficients via `(-1)^k · C(9,k) · C(9+k,9)` at n=9 (odd parity):
     `(−1, 90, −1980, 18480, −90090, 252252, −420420, 411840, −218790, 48620)`.
     (Sign flips at every odd k; outer `(-1)^9 = -1` then flips the
     whole polynomial again. Net: highest-degree coefficient is
     `+48620` and constant term is `−1` matching `P_9^*(0) = (−1)^9`.)
   - Required `decide`-helpers: `Nat.choose {10..18} 9` and
     `Nat.choose 9 {2..8}`. Largest value: `Nat.choose 18 9 = 48620`.
   - Recurrence at n=9: `(9 : ℝ) • P_9^* = C 17 · (2X − 1) · P_8^*
     − C 8 · P_7^*`. Cross-check coefficients by Python before write.
3. **P2 (parallel pivot)**: if cycle 285 also stalls, consider
   pivoting to `lem:310B` Phase A.3 (TreeAutomorphism strengthening,
   per `lem_310B_plan.md`) — that work doesn't block (342f)/(342g) and
   provides momentum on a different chapter.
4. **P3 (long-term)**: Once (342f) general lands, fire Aristotle on
   (342g) `n` distinct real zeros per
   `.prover-state/issues/lem_342A_g_zeros_scoping.md`'s sign-change
   strategy.

## §342 ladder status (post-cycle 284)
| n | `butcherShiftedLegendre_n` | `_recurrence_n` | `_norm_sq_n` |
|---|---|---|---|
| 0 | `_zero` (cycle 273) | — | `_zero` (cycle 274) |
| 1 | `_one` (cycle 273) | — | `_one` (cycle 274) |
| 2 | `_two` (cycle 275) | `_two` (cycle 282) | `_two` (cycle 275) |
| 3 | `_three` (cycle 276) | `_three` (cycle 282) | `_three` (cycle 276) |
| 4 | `_four` (cycle 277) | `_four` (cycle 282) | `_four` (cycle 277) |
| 5 | `_five` (cycle 278) | `_five` (cycle 283) | `_five` (cycle 278) |
| 6 | `_six` (cycle 279) | `_six` (cycle 283) | `_six` (cycle 279) |
| 7 | `_seven` (cycle 280) | `_seven` (cycle 283) | `_seven` (cycle 280) |
| 8 | **`_eight` (cycle 284)** | **`_eight` (cycle 284)** | — (general `_norm_sq` covers all n; cycle 281) |

(342a) orthogonality: closed general (cycle 277, Aristotle 727396d5).
(342b) eval_one: closed general (cycle 271).
(342c) eval_one_sub: closed general (cycle 271).
(342d) norm_sq: closed general (cycle 281, Aristotle d4ce527b).
(342e) rodrigues: closed general (cycle 272).
(342f) recurrence: **open at general; n=2..8 witnesses shipped**.
(342g) n distinct real zeros: **open**.
