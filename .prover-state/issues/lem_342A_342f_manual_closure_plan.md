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

### Cycle 290 update — Phase A.1 (b) SHIPPED

Cycle 290 shipped `recurrence_residual_natDegree_lt` axiom-clean in
~140 LOC (`Section342.lean:2667–2797`). The full residual
`(n : ℝ) • P_n − C (2n - 1) (2X - 1) P_{n-1} + C (n - 1) P_{n-2}` has
`natDegree < n`. Phase A.1 is now complete.

### Cycle 291 update — Phase A.2 starter lemmas (F.1, F.2, easy
combination) SHIPPED

Cycle 291 shipped the two easy Phase A.2 orthogonality components
plus their additive combination, axiom-clean:

```lean
theorem recurrence_residual_orthogonal_first_term (n : ℕ)
    {k : ℕ} (hk : k < n) :
    ∫ x in (0 : ℝ)..1, ((n : ℝ) • butcherShiftedLegendre n).eval x *
                       (butcherShiftedLegendre k).eval x = 0

theorem recurrence_residual_orthogonal_third_term (n : ℕ) (hn : 3 ≤ n)
    {k : ℕ} (hk : k ≤ n - 3) :
    ∫ x in (0 : ℝ)..1, (Polynomial.C ((n - 1 : ℕ) : ℝ) *
                       butcherShiftedLegendre (n - 2)).eval x *
                       (butcherShiftedLegendre k).eval x = 0

theorem recurrence_residual_orthogonal_easy (n : ℕ) (hn : 3 ≤ n)
    {k : ℕ} (hk : k ≤ n - 3) :
    ∫ x in (0 : ℝ)..1, (((n : ℝ) • butcherShiftedLegendre n +
                         Polynomial.C ((n - 1 : ℕ) : ℝ) *
                         butcherShiftedLegendre (n - 2)).eval x) *
                       (butcherShiftedLegendre k).eval x = 0
```

All three live at `Section342.lean:2800–`. Proofs route through
`Polynomial.eval_smul` / `Polynomial.eval_mul` /
`Polynomial.eval_add` + `add_mul` + `mul_assoc` re-association +
`intervalIntegral.integral_const_mul` (constant pull-out) +
`butcherShiftedLegendre_orthogonal` (cycle 277). The combined
statement uses `intervalIntegral.integral_add` with integrability
witnesses from `Polynomial.continuous _ |>.mul (Polynomial.continuous _)
|>.intervalIntegrable`. ~50 LOC total (well under the F.1 + F.2 budget
estimate). The strategy's optional P3 deliverable was shipped because
P1 and P2 closed in one pass.

Total LOC ladder so far: cycle 289 ~80 LOC; cycle 290 ~140 LOC;
cycle 291 ~50 LOC. Combined Phase A.1 + Phase A.2 (easy) ~270 LOC.

F.3 (cross-term `⟨(2n - 1) · (2X - 1) · P_{n-1}^*, P_k^*⟩ = 0` for
`k ≤ n - 3`) remains open and is the next planner deliverable per
the cycle 292 entry point below.

### Cycle 292 entry point

Phase A.2 F.3: `(2n - 1) · (2X - 1) · P_{n-1}^*` orthogonal to
`P_k^*` for `k ≤ n - 3`. Concrete plan:

1. Establish `2X - 1 = butcherShiftedLegendre 1` (or `= -P_1^*`,
   depending on sign convention) — bridge via cycle 273's
   `butcherShiftedLegendre_one`. One-line lemma.
2. Reduce the integrand to `c · P_1^* · P_{n-1}^* · P_k^*` and use
   the inner-product symmetry: `⟨P_1 P_{n-1}, P_k⟩ = ⟨P_{n-1}, P_1
   P_k⟩` (commutativity of `*` in the integrand). Then
   `(P_1 · P_k).natDegree ≤ k + 1 ≤ n - 2 < n - 1`.
3. Show `P_{n-1}^*` is orthogonal to every polynomial of natDegree
   `< n - 1`. This is the **basis-span lemma** which also unlocks
   Phase A.3; ship it as a reusable helper.

Budget: ~100–150 LOC for F.3 + basis-span helper.

### Phase A.3 entry point (cycle 293+)

Once F.3 lands, Phase A.3 combines `natDegree Q < n` (cycle 290) +
orthogonality of `Q` to `P_k^*` for `k ≤ n - 2` (cycles 291–292) +
the basis-span lemma to conclude `Q = 0`, i.e. (342f) general.

### Cycle 292 update — Phase A.2 P1 + P2 + P3 SHIPPED (Phase A.2 fully closed)

Cycle 292 shipped all three planned deliverables axiom-clean
(`[propext, Classical.choice, Quot.sound]`):

```lean
theorem butcherShiftedLegendre_orthogonal_to_lower_degree
    (m : ℕ) (q : Polynomial ℝ) (hq : q.natDegree < m) :
    ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre m).eval x * q.eval x = 0

theorem recurrence_residual_orthogonal_cross_term (n : ℕ) (hn : 3 ≤ n)
    {k : ℕ} (hk : k ≤ n - 3) :
    ∫ x in (0 : ℝ)..1,
      (Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
       (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
       butcherShiftedLegendre (n - 1)).eval x *
      (butcherShiftedLegendre k).eval x = 0

theorem recurrence_residual_orthogonal (n : ℕ) (hn : 3 ≤ n)
    {k : ℕ} (hk : k ≤ n - 3) :
    ∫ x in (0 : ℝ)..1,
      (((n : ℝ) • butcherShiftedLegendre n
        - Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
          (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
          butcherShiftedLegendre (n - 1)
        + Polynomial.C ((n - 1 : ℕ) : ℝ) *
          butcherShiftedLegendre (n - 2)).eval x) *
      (butcherShiftedLegendre k).eval x = 0
```

All three live at `Section342.lean:2873–3115` (file is now ~3116 LOC).
Total cycle 292 LOC: ~244 (P1 ~140 LOC for the basis-span helper
inductive proof, P2 ~35 LOC for F.3, P3 ~50 LOC for the combined
residual orthogonality + integrability witnesses).

P1 (basis-span helper) is general: it asserts `P_m^*` is orthogonal to
every polynomial of natDegree `< m`. Independent of (342f) and reusable
for Phase A.3 / (342g).

P3 combines F.1 (cycle 291), F.3 (cycle 292), F.2 (cycle 291) into the
full orthogonality of the cycle 290 recurrence residual `Q` against
`P_k^*` for every `k ≤ n - 3`. Together with cycle 290's
`recurrence_residual_natDegree_lt` (`Q.natDegree < n`), this is exactly
the input Phase A.3 needs.

LOC ladder so far: cycle 289 ~80, cycle 290 ~140, cycle 291 ~50,
cycle 292 ~244. Combined Phase A.1 + A.2 ~510 LOC.

### Cycle 293 entry point — Phase A.3 (conclude `Q = 0`)

Phase A.3 needs to derive `Q = 0` from:
* `Q.natDegree < n` (cycle 290's `recurrence_residual_natDegree_lt`).
* `⟨Q, P_k^*⟩ = 0` for `k ≤ n - 3` (cycle 292's
  `recurrence_residual_orthogonal`).

The textbook's argument (Butcher §342, p. 236) routes through parity:
"Because `Q` has the same parity as `n`, it is of degree less than
`n - 1`. A simple calculation shows that `Q` is orthogonal to `P_k^*`
for `k < n - 2`. Hence, (342f) follows except for the value of the
`P_{n-2}^*` coefficient, which is resolved by substituting `x = 1`."

Two viable routes for cycle 293:

**Route A — Parity-aided** (closer to textbook):
1. Show `Q` has the same parity as `n` under `x ↦ 1 - x` (use (342c)
   on each summand): `Q(1 - x) = (-1)^n Q(x)`.
2. Combined with `natDegree Q < n` and parity, conclude
   `natDegree Q < n - 1`.
3. The orthogonality `⟨Q, P_k^*⟩ = 0` for `k ≤ n - 3` plus the
   spanning-set argument (P1 in reverse: any polynomial of natDegree
   `< n - 1` orthogonal to every `P_k^*` for `k < n - 1` is `0`)
   forces `Q ∈ span {P_{n-2}^*}` modulo orthogonality conditions.
4. The `P_{n-2}^*` coefficient is fixed by substituting `x = 1`
   (use (342b): `P_n^*(1) = 1`).

**Route B — Direct Gram-Schmidt**:
1. Show the orthogonality range extends to `k ≤ n - 1` (compute
   `⟨Q, P_{n-2}^*⟩` and `⟨Q, P_{n-1}^*⟩` separately).
   * For `⟨Q, P_{n-1}^*⟩`: F.1 contributes `0` (since `n - 1 < n`),
     F.2 contributes `0` (since `n - 2 ≠ n - 1` for `n ≥ 3`), F.3
     cross-term needs `⟨(2X - 1) P_{n-1}^*, P_{n-1}^*⟩` which is
     `0` by a parity argument on `2X - 1`.
   * For `⟨Q, P_{n-2}^*⟩`: this is **not** zero in general; the
     textbook fixes the `P_{n-2}^*` coefficient via `x = 1`. Use
     (342d) norm-square + (342b) eval-at-one to compute the
     `P_{n-2}^*` coefficient exactly.
2. Show that any polynomial with `natDegree < n` orthogonal to
   `P_0^*, ..., P_{n-1}^*` is zero. This is a standard Gram-Schmidt
   spanning-set fact, derivable from P1 + induction.

Cycle 293 should aim for ~80-120 LOC. Route A is closer to textbook but
needs parity setup; Route B is more direct but the `P_{n-2}^*` slot
needs eval-at-`x = 1` for the coefficient (which is also how the
textbook resolves it).

If Phase A.3 lands cleanly, cycle 294 extracts the (342f) headline via
a `linear_combination` step on `Q = 0`.

### Cycle 293 update — Phase A.3 SHIPPED + (342f) headline closed

Cycle 293 shipped **all six** Phase A.3 deliverables (P1 through P6) in
a single cycle, axiom-clean
(`[propext, Classical.choice, Quot.sound]`). Located at
`OpenMath/Chapter3/Section342.lean:3129–3539` (~423 new LOC).

```lean
theorem recurrence_residual_eval_at_one (n : ℕ) (hn : 2 ≤ n) :
    ((residual)).eval 1 = 0

theorem recurrence_residual_parity (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    ((residual)).eval (1 - x) = ((-1 : ℝ) ^ n) * ((residual)).eval x

theorem recurrence_residual_natDegree_le (n : ℕ) (hn : 2 ≤ n) :
    ((residual)).natDegree ≤ n - 2

theorem polynomial_eq_smul_butcherShiftedLegendre_of_natDegree_le_of_orthogonal
    (m : ℕ) (q : Polynomial ℝ) (hq_deg : q.natDegree ≤ m)
    (h_orth : ∀ k, k < m →
      ∫ x in (0 : ℝ)..1, q.eval x * (butcherShiftedLegendre k).eval x = 0) :
    ∃ c : ℝ, q = Polynomial.C c * butcherShiftedLegendre m

theorem recurrence_residual_eq_zero (n : ℕ) (hn : 3 ≤ n) :
    (residual) = 0

theorem butcherShiftedLegendre_recurrence (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) • butcherShiftedLegendre n =
      Polynomial.C ((2 * n - 1 : ℕ) : ℝ) *
        (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) *
        butcherShiftedLegendre (n - 1)
      - Polynomial.C ((n - 1 : ℕ) : ℝ) *
        butcherShiftedLegendre (n - 2)
```

`(residual)` denotes the cycle 290 residual
`(n : ℝ) • P_n - C ((2*n - 1 : ℕ) : ℝ) * (C 2 * X - C 1) * P_{n-1} +
C ((n - 1 : ℕ) : ℝ) * P_{n-2}`.

The path used was **Route A** (parity-aided), but with a cleaner
leadingCoeff-based degree-drop argument in P3:
* P1 and P2 went directly per the strategy's recipe.
* P3 lifted P2 to polynomial level via `Polynomial.funext`, then took
  `Polynomial.leadingCoeff` of both sides of
  `Q.comp (C 1 - X) = C ((-1)^n) * Q`. With `(C 1 - X).leadingCoeff =
  -1` and `(C 1 - X).natDegree = 1`, `Polynomial.leadingCoeff_comp`
  gave `Q.leadingCoeff * (-1)^Q.natDegree` on the LHS. Equating with
  the RHS `(-1)^n * Q.leadingCoeff` and cancelling `Q.leadingCoeff ≠ 0`
  produced `(-1)^Q.natDegree = (-1)^n`. Combined with `Q.natDegree < n`
  (cycle 290), this rules out `Q.natDegree = n - 1`, giving
  `Q.natDegree ≤ n - 2`. **Much cleaner than the `coeff_comp` route
  sketched in the strategy.**
* P4 induction followed cycle 292's `suffices ∀ m', ...` pattern. Each
  step closed cleanly; only fix was replacing `field_simp` with the
  more direct `div_mul_cancel₀ + sub_self` in the residual-natDegree
  step.
* P5 applied P4 at `m := n - 2` with cycle 292's
  `recurrence_residual_orthogonal` providing the orthogonality input.
  P1 then forced the resulting scalar to zero.
* P6 case-split on `n` vs 3: cycle 282's
  `butcherShiftedLegendre_recurrence_two` for `n = 2` (with
  `convert ... using 2 <;> norm_num` to bridge the Nat-cast forms),
  and `linear_combination` on P5's `Q = 0` for `n ≥ 3`.

Total LOC ladder over Phase A:
* Cycle 289: ~80 (binomial helper).
* Cycle 290: ~140 (residual.natDegree < n).
* Cycle 291: ~50 (F.1 + F.2 + easy combination).
* Cycle 292: ~244 (basis-span helper + F.3 + full residual orthogonality).
* Cycle 293: ~423 (parity infrastructure + degree drop + basis-span
  converse + Q = 0 + (342f) headline).

**Phase A total**: ~937 LOC across cycles 289–293 (5 cycles), closing
(342f) at all `n ≥ 2`. Was projected 3–5 cycles, 370–570 LOC. Came in
on cycle count, slightly over LOC due to P3's parity infrastructure
and P4's full induction proof (more substantive than the cycle 292
forward direction).

### Status

`lem:342A` properties shipped:
- (342a) orthogonality — cycle 277.
- (342b) eval at 1 — cycle 271.
- (342c) parity — cycle 272.
- (342d) norm square — cycle 281.
- (342e) Rodrigues — cycle 277.
- (342f) recurrence — **cycle 293**.
- (342g) `n` distinct real zeros — **open** (see
  `lem_342A_g_zeros_scoping.md`).

This issue file may be closed once (342g) lands. Until then, leave
open as Phase A reference.
