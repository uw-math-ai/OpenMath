# Cycle 279 Results

## Worked on

§342 (342d) `n = 6` ladder rung — Branch B fallback per Cycle 279
strategy after Aristotle `d4ce527b-b714-4e51-b0a6-e3d06302d7fa`
returned IN_PROGRESS (52%) on the single poll.

Targets shipped:
1. `butcherShiftedLegendre_six` — closed-form
   `P_6^*(X) = 924X⁶ − 2772X⁵ + 3150X⁴ − 1680X³ + 420X² − 42X + 1`.
2. `butcherShiftedLegendre_norm_sq_six` — concrete (342d) instance
   `∫₀¹ (P_6^*(x))² dx = 1/13`.
3. One non-vacuity `example` confirming `1/(2·6 + 1) = 1/13`.

## Approach

### Priority 0 — Aristotle poll

`mcp__aristotle__get_status` on `d4ce527b-b714-4e51-b0a6-e3d06302d7fa`
returned `IN_PROGRESS` at `percent_complete = 52` (up from 33% in
cycle 278 — `~+19pp` jump). Did not re-poll per CLAUDE.md.

### Priority 1 — Branch B `_six` + `_norm_sq_six`

#### 1.1 `butcherShiftedLegendre_six`

Mirrored cycle 278's `butcherShiftedLegendre_five` template (which
itself mirrors cycle 277's `_four` for the even-`n` case):

- `unfold butcherShiftedLegendre`; `ext k`;
- `simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
   Polynomial.coeff_shiftedLegendre]` (peel off `C ((-1)^6) * ·`
   BEFORE simp can collapse it to the polynomial `1`);
- `match k with` for `k ∈ {0, 1, 2, 3, 4, 5, 6}` plus `k+7` tail;
- Each `k ∈ {2..5}` arm gets two `decide`-helpers
  `Nat.choose (n+k) n = …`, `Nat.choose n k = …`; `k = 6` only
  needs `Nat.choose 12 6 = 924`.

Mathlib coefficient formula confirmed via
`mcp__lean-lsp__lean_hover_info`:
`Polynomial.coeff_shiftedLegendre (n k : ℕ) :
   (shiftedLegendre n).coeff k = (-1)^k * (n.choose k) * (n + k).choose n`.

For `n = 6`, the relevant values match the strategy:
| k | (-1)^k | C(6,k) | C(6+k,6) | product |
|---|--------|--------|-----------|---------|
| 0 |   1    |   1    |    1      |    1    |
| 1 |  -1    |   6    |    7      |  -42    |
| 2 |   1    |  15    |   28      |  420    |
| 3 |  -1    |  20    |   84      | -1680   |
| 4 |   1    |  15    |  210      | 3150    |
| 5 |  -1    |   6    |  462      | -2772   |
| 6 |   1    |   1    |  924      |  924    |

Outer `(-1)^6 = 1` leaves all signs as-is. Sanity: `924 - 2772 + 3150
- 1680 + 420 - 42 + 1 = 1` (matches `P_n^*(1) = 1` from (342b));
constant term `1` matches `P_6^*(0) = (-1)^6 = 1` from
`butcherShiftedLegendre_eval_zero`.

#### 1.2 `butcherShiftedLegendre_norm_sq_six`

Mirrored cycle 278's `butcherShiftedLegendre_norm_sq_five` recipe
with one extra layer (n=6 expansion has 13 terms vs 11 for n=5).

**Coefficient convolution of `(P_6^*)²`** — hand-verified before
writing Lean per cycle 278 Discovery #2:

With `a_0..a_6 = (1, -42, 420, -1680, 3150, -2772, 924)`,
`c_k = Σ_{i+j=k} a_i · a_j`:

- c_0 = 1                  (= 1²)
- c_1 = -84
- c_2 = 2604
- c_3 = -38640
- c_4 = 323820
- c_5 = -1681344
- c_6 = 5703096
- c_7 = -12990096
- c_8 = 20012580
- c_9 = -20568240
- c_10 = 13505184
- c_11 = -5122656
- c_12 = 853776            (= 924²)

Boundary cross-checks `c_0 = 1`, `c_12 = 924² = 853776` ✓.

Lean structure:
1. `hP` rewrites `(butcherShiftedLegendre 6).eval x ^ 2` to the
   13-term polynomial in `x` via `rw [butcherShiftedLegendre_six]`
   + `simp` (eval lemmas) + `ring`.
2. `simp_rw [hP]` substitutes the integrand.
3. 12 `IntervalIntegrable` witnesses `hi_x12` down to `hi_x` via
   `(continuous_pow k).intervalIntegrable 0 1`.
4. 12 `integral_pow` evaluations `h12 .. h1` (each `∫₀¹ x^k = 1/(k+1)`).
5. Outer-to-inner cascade of 12 nested
   `intervalIntegral.integral_add` / `intervalIntegral.integral_sub`
   (alternating `+` / `−` matching the 12 ops in the left-associative
   expression).
6. 12 `intervalIntegral.integral_const_mul` strip the coefficients.
7. `h12, h11, …, h1, integral_one` substitute.
8. `ring` collapses the 13 rational sum to `1/13`.

The opening-paren counts on each integrability witness go 12, 11, 10,
..., 1 (matching cycle 278 Discovery #3's formula `n+6` opening parens
for the outermost witness at the n=6 case).

### Verification

- `lake env lean OpenMath/Chapter3/Section342.lean` — exit 0,
  unused-simp-arg warnings only (pre-existing in cycle 271–278 code,
  not introduced by cycle 279).
- `lake build OpenMath.Chapter3.Section342` — 2708 jobs, exit 0.
- `lake env lean OpenMath/Chapter3.lean` (aggregator) — exit 0.
- `grep -c sorry OpenMath/Chapter3/Section342.lean` — 0.
- `#print axioms`:
  - `butcherShiftedLegendre_six` depends on
    `[propext, Classical.choice, Quot.sound]`.
  - `butcherShiftedLegendre_norm_sq_six` depends on
    `[propext, Classical.choice, Quot.sound]`.

Section342.lean grew from 1231 → 1466 LOC.

## Result

SUCCESS — Branch B delivered as planned. Three artefacts shipped
axiom-clean. Aristotle `d4ce527b` advanced 19 percentage points
(33% → 52%) over a single cycle, which is far faster than the prior
2pp/cycle pace; the general (342d) result may complete by cycle 280
or 281.

## Faithfulness check

### `butcherShiftedLegendre_six`

- Entity ID: `lem:342A` (this is a stepping-stone helper, not a
  named textbook entity itself).
- Lean statement: definitional explicit-form rewriting of the
  cycle-272 `butcherShiftedLegendre 6` (which itself faithfully
  encodes Butcher's `P_6^*` definition modulo the (342e) Rodrigues
  identity proven in cycle 272).
- Verification anchors:
  - `(butcherShiftedLegendre 6).eval 1 = 1` (sum of RHS coefficients
    on the closed form = `924 − 2772 + 3150 − 1680 + 420 − 42 + 1 = 1`,
    matching (342b) per `butcherShiftedLegendre_eval_one`).
  - `(butcherShiftedLegendre 6).eval 0 = 1` (constant term of RHS = 1,
    matching `butcherShiftedLegendre_eval_zero 6` which evaluates to
    `(-1)^6 = 1`).
- Captures: same content — verified by `Polynomial.ext` against
  Mathlib's `Polynomial.coeff_shiftedLegendre` formula combined with
  the Butcher `(-1)^n` prefactor.

### `butcherShiftedLegendre_norm_sq_six`

- Entity ID: `lem:342A` clause (342d) at `n = 6`.
- Textbook statement (from
  `extraction/formalization_data/entities/lem_342A.json`):
  > `∫₀¹ P_n^*(x)^2 dx = 1/(2n + 1)`, `n = 0, 1, 2, …`. (342d)
- Lean statement: same content at `n = 6`
  (`∫₀¹ (P_6^*(x))^2 dx = 1/13 = 1/(2·6 + 1)`); the non-vacuity
  witness `example : … = 1 / (2 * (6 : ℕ) + 1)` enforces the match
  to the closed form.
- Tautology check: PASSED — conclusion is an integral computation,
  not a hypothesis re-export. No hypotheses beyond ambient measure
  theory infrastructure on ℝ.
- Identity check: PASSED — proof body is 50+ tactic lines, not
  `exact h`.
- Hypothesis strength check: PASSED — no extra hypotheses beyond
  Mathlib's interval-integral framework.

### Lean coverage status for `lem:342A` (342a–342g)

| clause | status         | cycle   | witness                                                |
|--------|----------------|---------|--------------------------------------------------------|
| 342a   | DONE           | 277     | `butcherShiftedLegendre_orthogonal` (Aristotle)         |
| 342b   | DONE           | 271     | `butcherShiftedLegendre_eval_one`                       |
| 342c   | DONE           | 271     | `butcherShiftedLegendre_eval_one_sub`                   |
| 342d   | PARTIAL (n≤6)  | 274–279 | `butcherShiftedLegendre_norm_sq_{zero..six}` ladder;    |
|        |                |         | general case waiting on Aristotle `d4ce527b` (52%)      |
| 342e   | DONE           | 272     | `butcherShiftedLegendre_rodrigues`                      |
| 342f   | NOT DONE       | —       | three-term recurrence, deferred                         |
| 342g   | NOT DONE       | —       | `n` distinct real zeros, deferred                       |

`lem:342A` row remains `partial` in `lean_status.json` until (342d)
general, (342f), and (342g) all close.

## Dead ends

None this cycle. The strategy laid out by the planner mapped 1:1 to
the cycle 278 template; the only risk was arithmetic error in the
13 convolution coefficients `c_k`, but cross-checks on `c_0 = 1` and
`c_12 = 924² = 853776` plus `ring`-closing the 13-fraction sum to
`1/13` validated the computation.

## Discovery

1. **Aristotle `d4ce527b` accelerated**: the project gained 19
   percentage points in one cycle window (33% → 52%), the largest
   per-cycle jump observed for this project. Prior pace was ~2pp/cycle.
   The (342d) general theorem may complete by cycle 280 or 281.

2. **Even-`n` peel-off still required**: even though `(-1)^6 = 1`
   the `simp only [coeff_C_mul, coeff_map, coeff_shiftedLegendre]`
   peel-off (cycle 276 pattern) is still necessary; without it,
   `simp` collapses `C ((-1)^6)` to the polynomial `1` and breaks
   the subsequent `coeff_C_mul` lemma application.

3. **Paren-count formula confirmed**: for `n = 6`, the polynomial
   integrability witness in the outermost `integral_add` needs 12
   opening parens (matching the 11 binary ops on the polynomial
   part plus the outer enclosure). Cycle 278's Discovery #3 formula
   `n + 6` opening parens for the outermost witness extrapolates
   correctly: n=5 needed 11, n=6 needed 12.

4. **File size projection update**: cycle 278 noted "split worth
   considering at n=8". After cycle 279, Section342.lean is 1466 LOC.
   At ~170-200 LOC per ladder rung, n=7 would push it to ~1640-1680
   LOC and n=8 to ~1830-1880 LOC. Splitting at n=8 (or after the
   general result lands) remains the right time.

5. **Convolution arithmetic stable**: hand-computing the c_k values
   with explicit cross-checks (c_0 = a_0², c_2n = a_n²) caught no
   sign errors this cycle. The strategy's pre-flight values matched
   all 13 c_k exactly; `ring` closed the 13-fraction sum on first
   try.

## Suggested next approach

**Cycle 280 P0**: Poll Aristotle `d4ce527b` once more. At 52% with
~+19pp/cycle pace, completion by cycle 280 or 281 is plausible. If
COMPLETE → integrate the general (342d) result. If still IN_PROGRESS,
no harm done.

**Cycle 280 P1 (if Aristotle still IN_PROGRESS)**: Ship `n = 7`
ladder rung (`butcherShiftedLegendre_seven` + `_norm_sq_seven`).

For the n=7 closed form (odd-`n`), the same cycle-276 peel-off pattern
applies. Coefficients (verify against Lean!):
- `(-1)^7 = -1` outer; signs flip relative to n=6.
- `(P_7^*).coeff k = (-1)^k · C(7,k) · C(7+k,7)` for `k ∈ {0..7}`.
- Values:
  - k=0: 1·1·1 = 1; outer flip → -1
  - k=1: -1·7·8 = -56; outer flip → 56
  - k=2: 1·21·36 = 756; outer flip → -756
  - k=3: -1·35·120 = -4200; outer flip → 4200
  - k=4: 1·35·330 = 11550; outer flip → -11550
  - k=5: -1·21·792 = -16632; outer flip → 16632
  - k=6: 1·7·1716 = 12012; outer flip → -12012
  - k=7: -1·1·3432 = -3432; outer flip → 3432

Sanity: at x=1, `3432 − 12012 + 16632 − 11550 + 4200 − 756 + 56 − 1`
= `3432 − 12012 = −8580`; `−8580 + 16632 = 8052`; `8052 − 11550 = −3498`;
`−3498 + 4200 = 702`; `702 − 756 = −54`; `−54 + 56 = 2`; `2 − 1 = 1`.
Matches (342b) `P_7^*(1) = 1` ✓.

At x=0: constant term is -1, matching `P_7^*(0) = (-1)^7 = -1` ✓.

So `P_7^*(X) = 3432X^7 - 12012X^6 + 16632X^5 - 11550X^4 + 4200X^3
- 756X^2 + 56X - 1`. (The strategy's cycle 278 note about the leading
coefficient sign was a false alarm; the computation above confirms
`+3432X^7`.)

For `_norm_sq_seven`: target `∫₀¹ (P_7^*)² = 1/15`. Will need 14 c_k
convolution coefficients and 14 nested `integral_add`/`integral_sub`
ops. LOC budget ~200.

**Cycle 280 P2 (only if both A and P1 fail)**: (342f) recurrence
remains blocked by Mathlib's lack of standard-Legendre infrastructure;
defer further.

**Cycle 281+**: Once Aristotle `d4ce527b` completes and the general
(342d) lands, the focus can shift to (342f) recurrence and (342g)
zeros. (342f) might be approachable via orthogonality (cycle 277's
`butcherShiftedLegendre_orthogonal`) plus the now-extensive small-`n`
ladder rungs as test cases.

**Cycle 281+ alt**: Consider pivoting to a fresh entity (`lem:342B`
Gaussian-quadrature exactness degree, or `thm:344A` Radau/Lobatto)
if §342 momentum has saturated. The ladder is now well-anchored at
`n ∈ {0..6}` and adding more rungs has diminishing strategic value
relative to broader chapter coverage.

**File split**: Section342.lean is 1466 LOC. Splitting threshold
should be reset to "after Aristotle returns the general (342d)
result, OR after n=8 rung lands". The split candidates would be:
`Section342Basic.lean` (definition + (342b)/(342c)/(342e) infra),
`Section342Orthogonality.lean` (342a + Aristotle helpers),
`Section342NormSquare.lean` (342d ladder + eventually general).
