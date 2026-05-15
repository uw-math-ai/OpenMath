# Cycle 273 Results

## Worked on

* **Track 1** (fire-and-forget): Aristotle submission for Butcher §342 (342a)
  shifted Legendre orthogonality on `[0, 1]`.
* **Track 2** (planned manual attempt): Butcher §342 (342f) three-term
  recurrence over `ℝ[X]`. Bailed early per strategy time-box.
* **Track 3** (fallback): Three small §342 helpers + non-vacuity witnesses
  on `butcherShiftedLegendre`.

## Approach

### Track 1 — Aristotle (342a) orthogonality

Built `.prover-state/aristotle_submissions/cycle_273/342a_orthogonality.lean`
containing:

* The `butcherShiftedLegendre` definition (copied from cycle 271).
* The four cycles 271–272 results restated as **axioms** so Aristotle could
  cite them directly:
  - `butcherShiftedLegendre_eval_one` (342b)
  - `butcherShiftedLegendre_eval_one_sub` (342c)
  - `butcherShiftedLegendre_rodrigues` (342e)
  - `butcherShiftedLegendre_natDegree` (degree)
* The target sorry'd theorem
  ```
  butcherShiftedLegendre_orthogonal {m n : ℕ} (hmn : m ≠ n) :
      ∫ x in (0 : ℝ)..1,
        (butcherShiftedLegendre m).eval x *
        (butcherShiftedLegendre n).eval x = 0
  ```
* Prompt hint walking Aristotle through the Rodrigues + integration-by-parts ×
  n strategy with boundary-term vanishing analysis.

Submitted via `mcp__aristotle__submit_file`. Project ID
`727396d5-14f9-4014-9aad-1f38238a1651`. Per CLAUDE.md single-poll
discipline, **not polled this cycle** — cycle 274 planner will check
status. Submission timestamp + prompt hint recorded at
`.prover-state/aristotle_submissions/cycle_273/README.md`.

### Track 2 — manual (342f) recurrence (BAILED at minute ~20)

Investigated the strategy's two proposed routes:

1. **`Polynomial.ext` + `coeff_shiftedLegendre` + `push_cast; ring`**. The
   per-coefficient identity reduces to a Pascal-style binomial identity:
   ```
   (m+2) C(m+2, k) C(m+2+k, m+2)
     − (2m+3) C(m+1, k) C(m+1+k, m+1)
     − 2(2m+3) C(m+1, k−1) C(m+k, m+1)
     + (m+1) C(m, k) C(m+k, m) = 0
   ```
   This is **not** a `ring`-closable identity — it requires Pascal-like
   manipulations of `Nat.choose` (`Nat.choose_succ_succ`, factorial cancellations).

2. **`Polynomial.funext` + eval-pointwise `ring`**. The eval of `shiftedLegendre n`
   at a real `x` is `∑ k (−1)^k C(n,k) C(n+k,n) x^k` — a polynomial in `x` over `ℝ`
   with binomial-coefficient constants. The recurrence as a polynomial identity in
   `x` *still* requires the same binomial identity coefficient-by-coefficient, so
   `ring` cannot close it directly.

The standard textbook derivation routes:

* **Bonnet-style**: differentiate Rodrigues' formula or apply Leibniz's rule to
  the second-order Legendre ODE seed `X(1-X)·u_n′ + n(2X-1)·u_n = 0`. This
  yields the ODE for `D^n u_n`, not the three-term recurrence directly.
* **Butcher's outline**: `n P_n^* − (2x−1)(2n−1) P_{n−1}^*` has degree < n and
  matching parity, hence equals `−(n−1) P_{n−2}^*` by orthogonality + endpoint
  evaluation. **Requires (342a) orthogonality as input** — circular if Aristotle
  hasn't returned yet.

Mathlib has no standalone Legendre polynomial type or 3-term recurrence
hook to bypass these. The strategy's 60-minute time-box gave no realistic
path to closure. Bailed to Track 3.

### Track 3 — three §342 helpers

Per strategy §C.3:

**Helper 1** — `butcherShiftedLegendre_eval_zero (n : ℕ) :
(butcherShiftedLegendre n).eval 0 = (-1)^n`. Proof: apply cycle 271's
`butcherShiftedLegendre_eval_one_sub n 1`, rewrite `(1 - 1 : ℝ) = 0` and
substitute `butcherShiftedLegendre_eval_one`; the residue `(-1)^n * 1 = (-1)^n`
is closed by `simpa`. 4 LOC.

**Helper 2** — `butcherShiftedLegendre_zero : butcherShiftedLegendre 0 = C 1`.
Proof: `Polynomial.ext`, case-split on `k`. For `k = 0`,
`coeff_shiftedLegendre 0 0 = 1` and `Polynomial.coeff_one 0 = 1` match; for
`k = succ _`, both sides are `0`. Closed by `simp` with
`coeff_shiftedLegendre` and `coeff_one`. 7 LOC.

**Helper 3** — `butcherShiftedLegendre_one : butcherShiftedLegendre 1 =
C 2 * X - C 1`. Proof: `Polynomial.ext` with `match k with | 0 | 1 | k+2`.
For `k = 0` and `k = 1`, simp closes via `coeff_shiftedLegendre`,
`coeff_sub`, `coeff_C`, `coeff_C_mul`, `coeff_one`. For `k+2 ≥ 2`,
auxiliary `Nat.choose 1 (k+2) = 0` (via `Nat.choose_eq_zero_of_lt`) kills
the `shiftedLegendre 1` side, leaving both sides zero. 11 LOC.

Plus 6 small non-vacuity `example` witnesses (`eval_zero` at `n ∈ {0,1,2}`,
explicit `P_0^* = C 1`, `P_1^*(0) = -1`, `P_1^*(1) = 1`).

## Result

**Track 1**: SUCCESS — Aristotle submission queued, awaiting cycle 274 poll.

**Track 2**: BAILED EARLY — strategy assessment confirmed the 60-min budget
is insufficient without standard Legendre infrastructure or (342a)
orthogonality. No regression (no changes committed).

**Track 3**: SUCCESS — three §342 helpers + non-vacuity witnesses shipped
axiom-clean. `Section342.lean` is 246 → 318 LOC, 0 sorries, 0 errors,
0 warnings (after simp-arg cleanup).

**Score**: +1 (per strategy §H: Track 3 ships ≥ 2 helpers + Track 1 submitted).

## Faithfulness check

The three new theorems are **internal helpers**, not entity-named Butcher
properties — they have no direct entry in `extraction/formalization_data/entities/`.
They are decompositions of the broader `lem:342A` goals:

* `butcherShiftedLegendre_eval_zero` corresponds to the `x = 0` evaluation
  implicit in Butcher's (342c) parity + (342b) normalization at `x = 1`.
  Captures the derived fact `P_n^*(0) = (-1)^n`. **Same content as the
  textbook** — no divergence.
* `butcherShiftedLegendre_zero` corresponds to Butcher's degree-0 case
  (implicit in the family definition with `n = 0`); the constant polynomial
  `1` is the unique degree-0 polynomial satisfying `P_0^*(1) = 1`. **Same content
  as textbook** — no divergence.
* `butcherShiftedLegendre_one` expands the degree-1 case `P_1^*(x) = 2x - 1`.
  Butcher does not state this explicitly but it follows from his (342b)/(342c)
  characterization (unique linear polynomial with `P_1^*(1) = 1` and parity
  `P_1^*(1-x) = -P_1^*(x)`). **Same content as textbook** — no divergence.

All three are genuine non-tautological mathematical content (no
identity proofs, no smuggled definitions, no spurious hypotheses).

## Dead ends

* **(342f) `Polynomial.funext` route** does *not* sidestep binomial-coefficient
  identities as the cycle 273 strategy §C.2 suggested. The eval at a real `x`
  is still a polynomial in `x` whose coefficients are explicit binomial sums;
  `ring` cannot close it. Strategy's "may be cleaner" hint was over-optimistic.

* **`shiftedLegendre n` simp-lemma scope**: `Polynomial.coeff_one` is needed
  for any expression involving `Polynomial.C 1` (which simp normalizes to the
  polynomial constant `1`); plain `coeff_C` doesn't fire on the `C 1` form
  after normalization.

## Discovery

* **Butcher's recurrence (342f) outlined-proof needs orthogonality (342a)**
  as a load-bearing input. The cleanest closure path for (342f) is therefore
  *after* Aristotle returns (342a), not in parallel. Cycle 274's planner
  should weight this: if Aristotle ships (342a), (342f) becomes a ~30-min
  derivation via Butcher's degree-and-difference argument; otherwise (342f)
  needs either binomial-identity grinding or a Mathlib enhancement (standard
  Legendre + Bonnet's recurrence).

* **Pascal-style identity for shifted Legendre** is *not* in Mathlib at HEAD.
  This is a genuine Mathlib gap (cf. CLAUDE.md "Mathlib gap is never a final
  answer" — would require contributing the standard Legendre recurrence
  upstream, multi-cycle scope).

* **`Polynomial.coeff_one`** + **`Polynomial.coeff_shiftedLegendre`** form
  the minimal simp set for any `butcherShiftedLegendre n` coefficient
  computation. `Polynomial.coeff_C_mul`, `Polynomial.coeff_X`, `Polynomial.coeff_sub`,
  `Polynomial.coeff_C` are needed only when comparing against a closed-form
  polynomial expression like `C 2 * X - C 1`.

## Suggested next approach

**Cycle 274 priority order (highest first):**

1. **Poll Aristotle `727396d5-14f9-4014-9aad-1f38238a1651`** (one
   `mcp__aristotle__get_status` call). If COMPLETE with a successful proof,
   integrate into `Section342.lean` (ship as `butcherShiftedLegendre_orthogonal`)
   and unlock (342d) `‖P_n^*‖² = 1/(2n+1)`.

2. **If Aristotle returned a partial / failed proof**: pivot to one of:
   * **Hand-finish Aristotle's partial** (re-run with extended budget or
     manually patch sorry's per Aristotle's progress).
   * **(342f) via Butcher's degree-and-difference outline** (assumes (342a),
     which Aristotle gave us) — ~30 LOC if Aristotle delivered.
   * **(342d) `∫₀¹ (P_n^*)² = 1/(2n+1)`** — also unlocked by (342a). Use
     Rodrigues + IBP × n + factorial book-keeping.

3. **If Aristotle failed cleanly with no salvageable partial**: pivot to
   `lem:310B` Phase A.1 (`RootedTree.Vertex` scaffold per `lem_310B_plan.md`),
   OR attempt a Mathlib upstream contribution of standard Legendre polynomials
   + Bonnet's recurrence (multi-cycle, ambitious).

4. **Do NOT** continue grinding (342f) via coefficient comparison this cycle
   — the path requires either (342a) as input (resolved next cycle) or
   Mathlib enhancements (multi-cycle).

**Faithfulness flag for cycle 274**: when Aristotle's (342a) proof is
integrated, **verify the integral formulation matches Butcher verbatim**
(`∫₀¹` over `[0, 1]`, not the symmetric `[-1, 1]` interval used for
standard Legendre). The submission file uses `intervalIntegral` over
`(0 : ℝ)..1`, which is correct.
