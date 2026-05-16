# Scoping: lem:342A (342g) — `P_n^*` has `n` distinct real zeros in (0, 1)

## Textbook statement (Butcher §342, p. 236)

> `P_n^*` has `n` distinct real zeros in the interval `(0, 1)`,
> `n = 0, 1, 2, …`.

Quoted from `extraction/formalization_data/entities/lem_342A.json`,
clause (342g).

## Textbook proof sketch (Butcher §342, p. 236)

> The final result (342g) is proved by supposing, on the contrary,
> that `P_n^*(x) = Q(x) R(x)`, where the polynomial factors `Q` and
> `R` have degrees `m < n` and `n - m`, respectively, and where `R`
> has no zeros in `(0, 1)`. We now find that
> `∫₀¹ P_n^*(x) Q(x) dx = 0`, even though the integrand is not zero
> and has a constant sign.

The standard contradiction: let `x_1, …, x_k` (with `k < n`) be the
distinct real zeros of `P_n^*` in `(0, 1)` *at which `P_n^*` changes
sign*. Form
`Q(x) := (x − x_1)(x − x_2)…(x − x_k)` (degree `k < n`).
Then `P_n^*(x) · Q(x)` has constant sign on `(0, 1)` (the sign-change
zeros are paired off), so the integral is nonzero. But by (342a)
applied to `Q ∈ Span{P_0^*, …, P_{k}^*}` (since `deg Q = k < n`),
the integral *is* zero. Contradiction.

## Why this is a candidate for Aristotle, not manual

Sign-change combinatorics in Lean is fiddly:
- Need to extract a finite sign-change set from `P_n^*` on `(0, 1)`.
- Need to argue `P_n^*(x) · ∏ᵢ (x − xᵢ)` has constant sign on the open
  interval, formalizing the "sign-change zeros are paired off"
  argument.
- Need the orthogonality conclusion `∫₀¹ P_n^* · Q = 0` from a
  polynomial `Q` of degree `k < n` — a corollary of (342a), via
  expansion of `Q` in the `P_j^*` basis.

The §342 (342a)/(342b)/(342d)/(342e)/(342f) layer is now in place
post-cycle 282 — Aristotle has access to all of orthogonality,
norm-square, Rodrigues, parity, and (once 342f lands) the three-term
recurrence. (342g) is the natural next batch submission once (342f)
ships.

## Mathlib hooks likely needed

| Need | Mathlib candidate |
|---|---|
| Polynomial roots in an interval | `Polynomial.roots`, `Polynomial.card_roots_le_degree` |
| Counted multiplicity of real roots | `Polynomial.roots_count_le_degree` |
| Sign change → root in interval (IVT) | `intermediate_value_Ioo`, `Polynomial.continuous` |
| Polynomial factorization over ℝ | `Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq` |
| Orthogonality vs polynomial of smaller degree | reduce via the basis `{P_0^*, …, P_k^*}` (cycle 282's `butcherShiftedLegendre_natDegree` provides the dim/degree match) |

## LOC budget estimate

~150 LOC. Structure:
- ~30 LOC infrastructure: extracting sign-change zeros of `P_n^*`
  in `(0, 1)` as a `Finset ℝ`.
- ~40 LOC: product polynomial `Q := ∏ᵢ (X − C xᵢ)` and its degree.
- ~40 LOC: sign-constancy of `P_n^* · Q` on `(0, 1)` (or "sign of
  the integrand is nonzero except at finitely many points").
- ~40 LOC: integral nonvanishing via positivity, contradiction with
  (342a)-derived `∫₀¹ P_n^* · Q = 0`.

## Risk assessment

| Risk | Mitigation |
|---|---|
| Sign-change formalization is fiddly in Lean | Submit to Aristotle once (342f) lands |
| Polynomial-basis expansion `Q ∈ Span{P_0^*, …, P_k^*}` requires a degree-induction lemma not in Mathlib | Provide as a helper axiom in the Aristotle submission |
| `card_roots` vs distinct real zeros in an open interval — Mathlib might count multiplicities | Use `Polynomial.roots.toFinset` to deduplicate |

## Cycle 283+ outlook

- Single-poll Aristotle (342f) project `c8b8f138-f875-4263-94ec-74533b5120d7`.
- If COMPLETE → integrate analogously to cycle 281's `d4ce527b`
  integration; then fire (342g) on Aristotle citing all of (342a)–(342f).
- If IN_PROGRESS at low % → continue ladder (n=5, 6, 7 recurrence
  witnesses) as Branch B fallback.

## Cycle 294 update

Cycle 294 executed the measured fire-and-forget pattern from this
scoping doc:

* **Aristotle submission**: project
  `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5` (file
  `.prover-state/aristotle_submissions/cycle_294/342g_zeros.lean`,
  status `QUEUED` at 2026-05-15 22:11:40 UTC). Cites (342a)–(342f)
  plus the cycle-292 `butcherShiftedLegendre_orthogonal_to_lower_degree`
  lemma — the load-bearing prerequisite for the contradiction
  argument. Single-poll cycle 295.
* **Empirical anchors shipped**: three theorems in
  `OpenMath/Chapter3/Section342.lean`, all axiom-clean:
  * `butcherShiftedLegendre_one_root` — `P_1^*(1/2) = 0 ∧ 1/2 ∈ (0,1)`.
  * `butcherShiftedLegendre_two_roots` — distinct roots
    `(3 ± √3)/6 ∈ (0,1)` of `P_2^*`.
  * `butcherShiftedLegendre_card_roots_le` — upper bound
    `(P_n^*).roots.toFinset.card ≤ n` via `Polynomial.card_roots'`
    + cycle 273's `butcherShiftedLegendre_natDegree`.
* **`n = 3` zeros**: explicitly deferred (closed-form involves
  cubic-formula nested radicals). The IVT path is viable but
  belongs to the full closure infrastructure.

## Closes

This is a scoping document, not a deliverable in itself. No file
changes proposed; the actual (342g) work is deferred to cycle 283+.

Cycle 294 anchored the work and dispatched to Aristotle. Cycle 295
single-polls. Closure (Branch A / B / C) depends on Aristotle's
return.

## Cycle 295 update

* **Aristotle single-poll**: `IN_PROGRESS`, `percent_complete = 16`
  at `2026-05-15T22:41:20Z` (≈30 min after cycle 294 submission).
  Growth from `QUEUED` (0%) ⇒ Branch B fired.
* **`n = 3` anchor shipped**: `butcherShiftedLegendre_three_roots`
  in `OpenMath/Chapter3/Section342.lean` — three distinct roots
  of `P_3^*` in `(0, 1)` via parity (middle, `r = 1/2`) plus IVT on
  `[0, 1/5]` (left, `r ∈ (0, 1/5)`) and `[4/5, 1]` (right,
  `r ∈ (4/5, 1)`), assembled with interval-disjointness `linarith`.
* **Reusable helper**: `butcherShiftedLegendre_eval_half_eq_zero_of_odd`
  generalises the parity-driven middle-root argument to every odd
  `n`. Reused immediately in cycle 296's `n = 5` anchor.
* All cycle 295 work axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## Cycle 296 update

* **Aristotle single-poll**: `IN_PROGRESS`, `percent_complete = 25`
  at `2026-05-15T23:01:44Z` (≈50 min after cycle 294 submission;
  +9 percentage points from cycle 295's 16%). Healthy growth ⇒
  Branch B fires; leave Aristotle running.
* **`n = 5` anchor shipped**: `butcherShiftedLegendre_five_roots`
  in `OpenMath/Chapter3/Section342.lean` — five distinct roots of
  `P_5^*` in `(0, 1)`. Recipe:
  - **Middle root** `r₃ = 1/2` via cycle 295's
    `butcherShiftedLegendre_eval_half_eq_zero_of_odd 5 ⟨2, rfl⟩`
    (one-line application of the new helper).
  - **Two left roots** via IVT on the closed form
    `P_5^* = 252X^5 - 630X^4 + 560X^3 - 210X^2 + 30X - 1`
    (cycle 278's `butcherShiftedLegendre_five`):
    * `P_5^*(0) = -1`, `P_5^*(1/10) = 2497/6250` ⇒ ascending
      `intermediate_value_Ioo` on `[0, 1/10]`.
    * `P_5^*(1/10) = 2497/6250`, `P_5^*(1/4) = -23/256` ⇒ descending
      `intermediate_value_Ioo'` on `[1/10, 1/4]`.
  - **Two right roots** (parity-symmetric to the left pair):
    * `P_5^*(3/4) = 23/256`, `P_5^*(9/10) = -2497/6250` ⇒ descending
      `intermediate_value_Ioo'` on `[3/4, 9/10]`.
    * `P_5^*(9/10) = -2497/6250`, `P_5^*(1) = 1` ⇒ ascending
      `intermediate_value_Ioo` on `[9/10, 1]`.
  - **Distinctness** (10 pairs) via `linarith` on the disjoint
    intervals
    `(0, 1/10) < (1/10, 1/4) < {1/2} < (3/4, 9/10) < (9/10, 1)`.
* Axiom-clean (`[propext, Classical.choice, Quot.sound]`); zero
  sorries; well within the strategy's 200-LOC budget.
* Aristotle still in flight; no stall observation appended.

## Cycle 297 update

* **Aristotle single-poll**: `IN_PROGRESS`, `percent_complete = 25`
  at `2026-05-15T23:19:53Z` (≈68 min after cycle 294 submission;
  flat from cycle 296's 25%). This is **observation #1** of the
  three-stall protocol (cycle 285 precedent: cancel only after three
  consecutive same-or-lower readings). Aristotle remains queued —
  do **NOT** cancel. Branch C fires (n=7 anchor); continue Aristotle
  through cycles 298 and 299.
* **`n = 7` anchor shipped**: `butcherShiftedLegendre_seven_roots`
  in `OpenMath/Chapter3/Section342.lean` — seven distinct roots of
  `P_7^*` in `(0, 1)`. Mechanical scaling of cycle 296's `n = 5`
  recipe:
  - **Middle root** `r₄ = 1/2` via cycle 295's
    `butcherShiftedLegendre_eval_half_eq_zero_of_odd 7 ⟨3, rfl⟩`.
  - **Three left roots** via IVT on cycle 280's closed form
    `P_7^* = 3432X^7 - 12012X^6 + 16632X^5 - 11550X^4 + 4200X^3 -
    756X^2 + 56X - 1`:
    * `(0, 1/20)` ascending; `(1/20, 1/5)` descending; `(1/5, 2/5)` ascending.
  - **Three right roots** (parity-symmetric):
    * `(3/5, 4/5)` ascending; `(4/5, 19/20)` descending; `(19/20, 1)` ascending.
  - **Distinctness** (21 pairs) via disjoint-interval `linarith`.
* Axiom-clean; zero sorries.

## Cycle 298 update

* **Aristotle single-poll**: `IN_PROGRESS`, `percent_complete = 28`
  at `2026-05-15T23:38:59Z` (≈87 min after cycle 294 submission;
  **+3 percentage points** from cycle 297's 25%). Per the strategy
  branch table, `> 25%` is healthy progress ⇒ **stall counter
  resets**; this is no longer observation #2. Branch B fires (n = 9
  anchor); Aristotle remains queued.
* **`n = 9` anchor shipped**: `butcherShiftedLegendre_nine_roots`
  in `OpenMath/Chapter3/Section342.lean` — nine distinct roots of
  `P_9^*` in `(0, 1)`. Mechanical extension of cycle 297's `n = 7`
  recipe using cycle 285's closed form `butcherShiftedLegendre_nine`
  and cycle 295's parity helper applied to `⟨4, rfl⟩` (since
  `9 = 2·4 + 1`):
  - **Middle root** `r₅ = 1/2` via
    `butcherShiftedLegendre_eval_half_eq_zero_of_odd 9 ⟨4, rfl⟩`.
  - **Four left roots** via IVT (signs pre-verified with Python
    `Fraction` against the closed form
    `P_9^* = 48620X^9 − 218790X^8 + 411840X^7 − 420420X^6
            + 252252X^5 − 90090X^4 + 18480X^3 − 1980X^2 + 90X − 1`):
    * `(0, 1/20)` ascending — `P(0) = -1`, `P(1/20) = 9459468441/25600000000`.
    * `(1/20, 1/8)` descending — `P(1/8) = -(10413009/33554432)`.
    * `(1/8, 1/4)` ascending — `P(1/4) = 17557/65536`.
    * `(1/4, 2/5)` descending — `P(2/5) = -(96077/390625)`.
  - **Four right roots** (parity-symmetric to the left tetrad):
    * `(3/5, 3/4)` descending; `(3/4, 7/8)` ascending;
      `(7/8, 19/20)` descending; `(19/20, 1)` ascending.
  - **Distinctness** (36 pairs) via disjoint-interval `linarith`.
* Axiom-clean (`[propext, Classical.choice, Quot.sound]`); zero
  sorries. The bracket-sign pre-verification step caught that the
  strategy table's "Direction" column on the right half was off-by-
  parity for `n = 9` (table claimed ascending; actual direction is
  determined by `P_9^*(1 − x) = -P_9^*(x)`). The Lean proof uses
  the verified directions, not the table directions.
* Aristotle still in flight; healthy growth ⇒ continue. Cycle 299
  polls again. If 28% holds flat, that becomes observation #1 of a
  fresh three-stall window. Cancellation precondition (three
  consecutive flat readings) not currently met.

## Cycle 299 update

* **Aristotle single-poll**: `IN_PROGRESS`, `percent_complete = 29`
  at `2026-05-15T23:56:34Z` (≈18 min after cycle 298's 28% reading;
  **+1 percentage point**). Per the strategy branch table, `> 28%`
  is healthy growth ⇒ **stall counter remains 0**; Branch B fires
  (n = 11 anchor). Aristotle stays queued.
* **`n = 11` anchor shipped**: `butcherShiftedLegendre_eleven_roots`
  in `OpenMath/Chapter3/Section342.lean` — eleven distinct roots
  of `P_11^*` in `(0, 1)`. Mechanical extension of cycle 298's
  `n = 9` recipe using cycle 287's closed form
  `butcherShiftedLegendre_eleven` and cycle 295's parity helper
  applied to `⟨5, rfl⟩` (since `11 = 2·5 + 1`):
  - **Middle root** `r₆ = 1/2` via
    `butcherShiftedLegendre_eval_half_eq_zero_of_odd 11 ⟨5, rfl⟩`.
  - **Five left roots** via IVT (signs pre-verified with Python
    `Fraction` against the closed form
    `P_11^* = 705432X^11 − 3879876X^10 + 9237800X^9
              − 12471030X^8 + 10501920X^7 − 5717712X^6
              + 2018016X^5 − 450450X^4 + 60060X^3
              − 4290X^2 + 132X − 1`):
    * `(0, 1/50)` ascending — `P(0) = -1`,
      `P(1/50) = 25826480523788463/76293945312500000`.
    * `(1/50, 1/10)` descending — `P(1/10) = -(900666979/3125000000)`.
    * `(1/10, 1/5)` ascending — `P(1/5) = 11581677/48828125`.
    * `(1/5, 3/10)` descending — `P(3/10) = -(1534706671/6250000000)`.
    * `(3/10, 9/20)` ascending —
      `P(9/20) = 5516425106321/25600000000000`.
  - **Five right roots** (parity-symmetric to the left pentad):
    * `(11/20, 7/10)` ascending; `(7/10, 4/5)` descending;
      `(4/5, 9/10)` ascending; `(9/10, 49/50)` descending;
      `(49/50, 1)` ascending.
  - **Distinctness** (55 pairs) via disjoint-interval `linarith`.
* **Pre-verification table** (actual signs observed; matches the
  expected odd-parity pattern `−, +, −, +, −, +, 0, −, +, −, +, −, +`):
  `P(0) -; P(1/50) +; P(1/10) -; P(1/5) +; P(3/10) -; P(9/20) +;
  P(1/2) 0; P(11/20) -; P(7/10) +; P(4/5) -; P(9/10) +;
  P(49/50) -; P(1) +`. Outer-bracket denominator 50 sufficed —
  escalation to denominator 100 not needed.
* **Linarith hypothesis-pollution mitigation** (new for cycle 299):
  The 12 large-rational `hf_*` polynomial evaluations
  (e.g. `25826480523788463 / 76293945312500000`) caused `linarith`
  to time out on `isDefEq` during the post-`refine` distinctness/
  membership block (66 goals). Mitigated by an explicit
  `clear hP11 hcont hf_0 hf_1 hf_one_fiftieth … hf_forty_nine_fiftieths`
  immediately before `refine`, retaining only `hf_half` (consumed
  by `refine` for the parity-forced `r₆` root) and the IVT-derived
  `hrᵢ_eval` / `hrᵢ_mem` hypotheses. **Worth importing into the
  cycle 300+ template** if the empirical ladder continues.
* Axiom-clean (`[propext, Classical.choice, Quot.sound]`); zero
  sorries. Build refreshes `OpenMath.Chapter3.Section342` oleans in
  ~28s on this cluster — cycle budget comfortably met.
* Aristotle still in flight; cycle 300 polls again. If `29%` holds
  flat that becomes observation #1 of a fresh three-stall window.
  Cancellation precondition (three consecutive flat readings) not
  currently met.

## Cycle 301 closure

**RESOLVED.** Aristotle project
`5939f28b-c890-4b7f-be4f-ed0f31f0d0b5` returned `COMPLETE` at 100%
on the cycle 301 single-poll (created 2026-05-15T22:11Z, completed
2026-05-16T00:37Z). The proof was integrated into
`OpenMath/Chapter3/Section342.lean` with:

* Generic polynomial-sign helpers extracted to a new file
  `OpenMath/Chapter3/Section342DistinctRootsHelpers.lean` (mirror of
  cycle 281's `Section342NormSqHelpers.lean` pattern):
  - `poly_nonneg_or_nonpos_near_even_mult_root`
  - `poly_constant_sign_of_even_mult_roots`
  - `prod_linear_factors_dvd_of_roots`

* New theorems in `Section342.lean` (`OpenMath.Chapter3.Section342`
  namespace):
  - `butcherShiftedLegendre_ne_zero (n : ℕ) : butcherShiftedLegendre n ≠ 0`
  - `butcherShiftedLegendre_rootsInIoo (n : ℕ) : Finset ℝ`
  - `butcherShiftedLegendre_rootsInIoo_subset`
  - `butcherShiftedLegendre_rootsInIoo_are_roots`
  - `butcherShiftedLegendre_rootsInIoo_card_le` (refines cycle 294's
    `butcherShiftedLegendre_card_roots_le` to the open-interval filter)
  - `butcherShiftedLegendre_rootsInIoo_card_ge` (sign-change
    contradiction, ~250 LOC, the load-bearing lemma)
  - `butcherShiftedLegendre_n_distinct_real_zeros (n : ℕ) : ∃ xs : Finset ℝ, xs.card = n ∧ (∀ x ∈ xs, x ∈ Set.Ioo 0 1) ∧ (∀ x ∈ xs, P_n^*.eval x = 0)`

* **All theorems axiom-clean** (`[propext, Classical.choice, Quot.sound]`
  only) under the CLAUDE.md default `maxHeartbeats := 200000`.
  Aristotle's `set_option maxHeartbeats 800000` defensive bumps on
  `poly_constant_sign_of_even_mult_roots` and `rootsInIoo_card_ge`
  were dropped without any proof decomposition — they were defensive
  and unneeded once two surgical fixes landed:

  1. **`IsBezout` synthesis fix**: Aristotle's
     `Irreducible.coprime_iff_not_dvd` path requires `IsBezout R[X]`,
     which the elaborator couldn't pin from the bare `_` placeholder
     metavariable. Swapped to the more direct
     `Polynomial.isCoprime_X_sub_C_of_isUnit_sub
       (sub_ne_zero_of_ne hrs).isUnit`
     (in `Mathlib.Algebra.Polynomial.RingDivision`), which does not
     require `IsBezout`.

  2. **`simp +zetaDelta at *` blow-up fix**: Aristotle's volume
     positivity argument
     `0 < volume (Set.Ioo (max 0 (x-ε)) (min 1 (x+ε)))`
     used `simp +zetaDelta at *` which timed out at 200000 heartbeats.
     Replaced with explicit `rcases le_or_gt (x - ε) 0` / `rcases
     le_or_gt 1 (x + ε)` case-splits on the `max` / `min` formulas,
     followed by `rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr ...`.

* Cycle 295–300 empirical anchors (`butcherShiftedLegendre_{one,three,
  five,seven,nine,eleven,thirteen}_roots`) are **retained as
  defensive regression witnesses** — they provide explicit closed-form
  sub-interval brackets that the existential headline does not. Per
  cycle 301 strategy §D.6.

* `extraction/formalization_data/lean_status.json`: `lem:342A` updated
  to `formalized`, `lean_symbol` updated to
  `butcherShiftedLegendre_n_distinct_real_zeros`.

* `plan.md`: `[~] lem:342A` → `[x] lem:342A` with cycle 301 closure
  paragraph documenting the Aristotle integration and the two
  surgical fixes.

**lem:342A complete**: all seven clauses (342a)–(342g) closed over
cycles 271–301.
