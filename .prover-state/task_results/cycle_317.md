# Cycle 317 Results

## Worked on

`thm:344A` Phase A — opening §344 (Radau and Lobatto quadrature). New
file `OpenMath/Chapter3/Section344.lean` (namespace
`OpenMath.Chapter3.Section344`) containing:

* **Deliverable A** — three polynomial-family definitions:
  * `butcherRadauI s   := butcherShiftedLegendre s + butcherShiftedLegendre (s - 1)`
  * `butcherRadauII s  := butcherShiftedLegendre s - butcherShiftedLegendre (s - 1)`
  * `butcherLobatto s  := butcherShiftedLegendre s - butcherShiftedLegendre (s - 2)`

* **Deliverable B** — four endpoint vanishing theorems:
  * `butcherRadauI_eval_zero (s : ℕ) (hs : 0 < s) : (butcherRadauI s).eval 0 = 0`
  * `butcherRadauII_eval_one (s : ℕ) : (butcherRadauII s).eval 1 = 0`
  * `butcherLobatto_eval_zero (s : ℕ) (hs : 2 ≤ s) : (butcherLobatto s).eval 0 = 0`
  * `butcherLobatto_eval_one (s : ℕ) : (butcherLobatto s).eval 1 = 0`

* **Deliverable C** — six small-`s` explicit forms:
  * `butcherRadauI_one : butcherRadauI 1 = C 2 * X`
  * `butcherRadauI_two : butcherRadauI 2 = C 6 * X^2 - C 4 * X`
  * `butcherRadauII_one : butcherRadauII 1 = C 2 * X - C 2`
  * `butcherRadauII_two : butcherRadauII 2 = C 6 * X^2 - C 8 * X + C 2`
  * `butcherLobatto_two : butcherLobatto 2 = C 6 * X^2 - C 6 * X`
  * `butcherLobatto_three : butcherLobatto 3 = C 20 * X^3 - C 30 * X^2 + C 10 * X`
  Plus four `example` non-vacuity witnesses confirming the endpoint
  theorems fire on the small-`s` closed forms.

* **Deliverable D** — three natural-degree bounds:
  * `butcherRadauI_natDegree (s : ℕ) (hs : 0 < s) : (butcherRadauI s).natDegree = s`
  * `butcherRadauII_natDegree (s : ℕ) (hs : 0 < s) : (butcherRadauII s).natDegree = s`
  * `butcherLobatto_natDegree (s : ℕ) (hs : 2 ≤ s) : (butcherLobatto s).natDegree = s`

Plus updates to `OpenMath/Chapter3.lean` (import the new file),
`extraction/formalization_data/lean_status.json` (`thm:344A` →
`partial`, symbol = `butcherRadauI_eval_zero`), and `plan.md`
(`[ ] thm:344A` → `[~] thm:344A` with cycle 317 closure note).

## Approach

Followed the planner strategy verbatim. Single-file ship under the LOC
budget (~280 LOC vs the 350-LOC abort threshold).

* **Endpoint vanishing**: the `_eval_zero` proofs use
  `butcherShiftedLegendre_eval_zero` (cycle 273) to produce
  `(-1)^s ± (-1)^(s-k)` and then collapse via the parity recipe from
  the strategy. For Radau I (`k = 1`), `obtain ⟨k, rfl⟩ :=
  Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hs)` rewrites
  `s = k + 1` so `s - 1 = k` reduces by `rfl`, and
  `pow_succ` + `ring` closes. For Lobatto (`k = 2`),
  `obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs` rewrites `s = 2 + k`
  but `(2 + k - 2 : ℕ) = k` does **not** reduce by `rfl` (Nat
  subtraction recurses on the subtrahend), so I used `by omega` for
  the explicit subtraction lemma followed by `pow_add` + `ring`.
* **`_eval_one` theorems**: `butcherShiftedLegendre_eval_one` (cycle
  271) gives `P_n^*(1) = 1` for all `n`, so the proofs reduce to
  `1 - 1 = 0` and close by `ring`. The textbook's `s ≥ 1` / `s ≥ 2`
  hypotheses are not needed for the pure polynomial-evaluation fact
  (the hypothesis only matters for `c_s` to refer to the `s`-th
  abscissa in the underlying quadrature formula); I dropped them per
  the faithfulness "hypothesis strength" rule and documented the
  reason in the docstrings.
* **Small-`s` explicit forms**: each form follows
  `unfold + rw [butcherShiftedLegendre_{zero,one,two,three}] + apply
  Polynomial.funext + simp only [Polynomial.eval_{add,sub,mul,pow,C,X}] + ring`.
  Direct `ring` on the polynomial-ring expression fails because `ring`
  treats `Polynomial.C n` as an opaque atom and cannot fold
  `C 6 - C 4 = C 2`; lifting to `eval` and back via
  `Polynomial.funext` collapses every `C n` to a literal `n : ℝ`
  where `ring` works. (This is the cycle 282 pattern documented in
  the strategy.)
* **Degree bounds**: each follows
  `Polynomial.natDegree_add_eq_left_of_natDegree_lt` (Radau I) or
  `Polynomial.natDegree_sub_eq_left_of_natDegree_lt` (Radau II,
  Lobatto) applied to the strict-degree-comparison
  `(P_{s-1}^*).natDegree = s - 1 < s = (P_s^*).natDegree` (or
  `s - 2 < s` for Lobatto). The strict inequality discharges by
  `omega` after rewriting both sides via cycle 273's
  `butcherShiftedLegendre_natDegree`.

## Result

**SUCCESS.** All 13 new public theorems plus the three new definitions
compile cleanly (zero errors, zero warnings after a single
unused-simp-arg fix). All 13 theorems axiom-clean
`[propext, Classical.choice, Quot.sound]`. Build time for the new
file: 3.3s. Repo sorry count remains 0.

`Polynomial.natDegree_sub_eq_left_of_natDegree_lt` (the `sub` variant
the strategy was unsure about) **does exist** in Mathlib at HEAD; no
`sub_eq_add_neg` + `natDegree_neg` workaround was needed.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

* **`butcherRadauI s`** —
  Entity ID and textbook statement (quoted from
  `extraction/formalization_data/entities/thm_344A.json`, proof_text):
  > "The fact that x = 0 is a zero of P_s^*(x) + P_{s−1}^*(x) … follows
  > from (342b) and (342c), with x = 1."
  Lean statement captures: **same content** (the polynomial
  `P_s^* + P_{s-1}^*` whose root at `x = 0` is the Radau I anchor).
  The definition is the literal sum, not a stipulative
  "polynomial whose roots are the Radau I abscissae" — no smuggling.

* **`butcherRadauII s`** —
  Textbook statement:
  > "The fact that x = 1 is a zero of P_s^*(x) − P_{s−1}^*(x) … follows
  > from (342b)."
  Lean statement captures: **same content** (literal difference).

* **`butcherLobatto s`** —
  Textbook statement:
  > "The fact that x = 1 is a zero of … P_s^*(x) − P_{s−2}^*(x) follows
  > from (342b). The fact that x = 0 is a zero of … P_s^*(x) − P_{s−2}^*(x)
  > follows from (342b) and (342c), with x = 1."
  Lean statement captures: **same content** (literal difference, no
  stipulation).

* **Endpoint theorems (`butcherRadauI_eval_zero`,
  `butcherRadauII_eval_one`, `butcherLobatto_eval_zero`,
  `butcherLobatto_eval_one`)** — all four state that the polynomial
  evaluates to `0` at the textbook-named endpoint; **same content** as
  the textbook claim. Tautology / identity-of-hypothesis checks:
  none of the endpoint conclusions appear as hypotheses; each closes
  by a genuine algebraic collapse `(-1)^s + (-1)^(s-1) = 0` or
  `1 - 1 = 0`. **Hypothesis strength**: the `s ≥ 1` hypothesis is
  required for `butcherRadauI_eval_zero` (without it, `s = 0` gives
  `(-1)^0 + (-1)^0 = 2 ≠ 0`); for `butcherRadauII_eval_one` and
  `butcherLobatto_eval_one` the hypothesis is *not* required and was
  dropped (`P_n^*(1) = 1` for all `n`, including `n = 0`). For
  `butcherLobatto_eval_zero` the `s ≥ 2` hypothesis is required
  (without it, e.g. `s = 1` gives `(-1)^1 + (-1)^{1-2=0} = -2 ≠ 0`
  due to truncated subtraction). Documented this in the docstrings.

* **Small-`s` explicit forms** — each cross-checks against textbook
  conventions per the strategy's checklist:
  * `butcherRadauI 1 = 2X` ✓ (single root at `0`, matches Radau I
    1-stage at `c_1 = 0`).
  * `butcherRadauII 1 = 2X - 2` ✓ (single root at `1`, matches
    Radau II 1-stage at `c_1 = 1`).
  * `butcherLobatto 2 = 6X^2 - 6X = 6X(X-1)` ✓ (roots at `0, 1`,
    matches Lobatto 2-stage at `c_1 = 0`, `c_2 = 1`).
  * Order-2 / order-3 forms verified by `ring`-discharged algebraic
    identities against the cycle 273+ closed forms for `P_n^*`.

* **Degree bounds** — captures the obvious fact that `P_s^*` is the
  leading term in each sum/difference. **Same content** as the
  textbook's implicit degree count (Butcher uses `2s − 2` /
  `2s − 3` polynomial-exactness statements, which presuppose
  `natDegree = s` for the underlying quadrature polynomial).
  Tautology check: each `natDegree` conclusion is a genuine
  consequence of the degree comparison, not a re-export of a
  hypothesis. **Hypothesis strength**: `0 < s` (Radau) and `2 ≤ s`
  (Lobatto) are minimal — for `s = 0` (Radau) the polynomial reduces
  to `P_0^* + P_0^* = 2` (degree 0, not `s = 0`-vacuous but
  degenerate); for `s < 2` (Lobatto) the polynomial vanishes
  identically (since `s - 2 = 0`) and `natDegree = 0` regardless
  (false claim for `s = 1`).

No new `class` / `structure` introduced this cycle; no `Prop`-field
escape hatches.

## Dead ends

* **`ring` directly on `Polynomial ℝ` expressions** (cycle 273+ known
  pitfall): rewriting `P_2^* + P_1^* = (C 6 * X^2 - C 6 * X + C 1) +
  (C 2 * X - C 1)` and trying to close `= C 6 * X^2 - C 4 * X` by
  `ring` fails — `ring` treats `Polynomial.C 6`, `Polynomial.C 4`,
  etc. as opaque atoms and cannot fold the constant arithmetic
  `-C 6 + C 2 = -C 4`. Workaround = the cycle 282 `Polynomial.funext`
  + `simp only [Polynomial.eval_*]` + `ring` recipe, which lifts to
  the evaluated polynomial where `C n` collapses to `n : ℝ` and
  `ring` handles the constant arithmetic. Documented in this file's
  proof comments and consistent with the existing memory entry on
  this Polynomial-`ring` failure mode.

* **`(2 + k - 2 : ℕ) = k` by `rfl`** (Nat truncated subtraction
  pitfall, anticipated by the strategy): the strategy speculated that
  `rfl` might fail and offered a backup. It does fail because Nat
  subtraction recurses on the second argument and never gets a chance
  to unfold `2 + k` to `Nat.succ (Nat.succ k)`. Used `by omega`
  instead. `(k + 1 - 1 : ℕ) = k` (Radau case) *does* reduce by `rfl`
  because subtraction unfolds `1 = Nat.succ 0` then `(k+1) - (0+1) =
  k - 0 = k`.

## Discovery

* **`Polynomial.natDegree_sub_eq_left_of_natDegree_lt` exists in
  Mathlib at HEAD.** The strategy hedged on this lemma's existence
  and proposed a `sub_eq_add_neg` + `natDegree_neg` fallback. The
  direct `sub` lemma works cleanly — no fallback needed. This is the
  natural companion to `Polynomial.natDegree_add_eq_left_of_natDegree_lt`
  and likely available since Mathlib added the comprehensive
  `Polynomial.Degree.Lemmas` module.

* **Endpoint-at-1 theorems are stronger than the textbook hypothesis
  requires.** Both `butcherRadauII_eval_one` and `butcherLobatto_eval_one`
  hold without the textbook's `s ≥ 1` / `s ≥ 2` hypothesis because
  `P_n^*(1) = 1` is unconditional. This is a faithfulness *strengthening*
  (weakening of hypotheses), and a useful general pattern: when the
  textbook hypothesis is about semantics ("`c_s` is the `s`-th
  abscissa") rather than the polynomial-arithmetic statement, the
  Lean statement can often drop the hypothesis.

* **The "P_s^* + P_{s-1}^*" / "P_s^* - P_{s-1}^*" / "P_s^* - P_{s-2}^*"
  trinity is the natural Radau-Lobatto polynomial scaffolding for
  the upcoming Phase B / Phase C cycles.** Future cycles can lift
  cycle 292's `butcherShiftedLegendre_orthogonal_to_lower_degree`
  basis-span lemma to a Radau/Lobatto-analogous orthogonality
  (cycle 318), then to a polynomial-exactness theorem on quotient +
  remainder decomposition (cycle 319), and finally to the homotopy
  argument for `c_i ∈ [0, 1]` and `b_i > 0` (cycles 320+, multi-cycle).

## Suggested next approach

For cycle 318 the planner should consider Phase B.1 of the
`thm:344A` plan: extend the Radau I polynomial's orthogonality
properties. Specifically:

* `butcherRadauI_orthogonal_to_lower_degree (s : ℕ) (hs : 0 < s) (q :
  Polynomial ℝ) (hq : q.natDegree < s - 1) :
  ∫ x in 0..1, (butcherRadauI s).eval x * q.eval x = 0` — analogous
  to cycle 292's `butcherShiftedLegendre_orthogonal_to_lower_degree`,
  but the Radau I polynomial is only orthogonal to polynomials of
  degree `< s - 1` (one less than `P_s^*`'s) because the
  `P_{s-1}^*` summand drags in a degree-`s - 1` non-orthogonality
  obstruction. Use `butcherShiftedLegendre_orthogonal` (cycle 291)
  on both `P_s^*` and `P_{s-1}^*` summands, with the index
  arithmetic checking that both `m = s` and `m = s - 1` exceed
  `q.natDegree < s - 1`.
* Analogous orthogonality lemmas for `butcherRadauII` (also degree
  `< s - 1`) and `butcherLobatto` (degree `< s - 2`).

These three lemmas plus cycle 317's degree bounds set up the
polynomial-exactness theorem of Phase B.2 (cycle 319) cleanly via
polynomial division: `φ = Q · butcherRadauI + R`, with `Q` of degree
`< s - 1` contributing zero by orthogonality and `R` of degree `< s`
exactly captured by `s` interpolation points (the Radau abscissae).
The exactness degree `2s - 2` follows from `s + (s - 2) = 2s - 2`.

Alternatively, the planner could ship the small-`s` explicit
quadrature *abscissae* of Radau I/II / Lobatto (analogous to cycle
295+'s `butcherShiftedLegendre_zeros_one_apply`), which would set up
a `butcherRadauI_RKTableau` / `butcherRadauII_RKTableau` /
`butcherLobatto_RKTableau` construction at small `s` mirroring
cycles 308–312 for Gauss-Legendre. That direction is later in the
plan (cycles 322+) but small-`s` `s = 1` cases might ship in a single
cycle as a useful anchor.

Either direction is viable; the orthogonality direction has higher
infrastructure value for the full `thm:344A` ship.
