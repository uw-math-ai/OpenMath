# Cycle 271 strategy — open §342 by shipping `lem:342A` (342b) + (342c)

## A. Context

Cycle 270 closed §310/§311 Phase E.1 up to order 5 in the scalar
setting (the 17-tree partial-sum bridge `lem_311A_order_five_partialSum`
at `OpenMath/Chapter3/Section311.lean`). Phase E.1 is now fully closed
at cycle 259's deliberate order-5 cutoff. There is **no pending
Aristotle work** to incorporate. Sorry count is 0; tautology scanner
clean.

The cycle 270 worker's task-results §"Suggested next approach"
enumerated three follow-up directions and explicitly recommended
**Option 2: pivot to `lem:342A`** (Legendre orthogonality on `[0,1]`)
as a "single-cycle independent target per `lem_310B_plan.md` §8.2",
detaching from the §310/§311 Phase E ladder before diminishing
returns kick in. Cycle 271 adopts this pivot.

## B. Strategic scope correction

`lem_310B_plan.md` §8.2 (written cycle 260) optimistically estimated
that **each of `lem:342A`'s seven properties (342a)–(342g)** could
ship as a single-cycle deliverable. **Re-reading the textbook
(`extraction/formalization_data/entities/lem_342A.json`) plus a
Mathlib survey overrides this**:

* Mathlib has `Polynomial.shiftedLegendre n : ℤ[X]` at
  `.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean`
  (115 LOC, axiom-clean). Provides:
  - `Polynomial.shiftedLegendre n` — the polynomial.
  - `Polynomial.factorial_mul_shiftedLegendre_eq` — Rodrigues
    formula: `n! * shiftedLegendre n = D^n (X^n * (1-X)^n)`.
  - `Polynomial.coeff_shiftedLegendre` — explicit coefficient.
  - `Polynomial.degree_shiftedLegendre` / `natDegree_shiftedLegendre`.
  - `Polynomial.shiftedLegendre_eval_symm` —
    `aeval x (shiftedLegendre n) = (-1)^n * aeval (1 - x) (shiftedLegendre n)`.

* Mathlib does **NOT** prove orthogonality (`grep "orthog\|integral"`
  on the file returns only a docstring mention, no actual lemma).
  So **(342a) requires us to build the orthogonality proof
  ourselves** via integration by parts on Rodrigues — likely
  ~200–400 LOC and 2–3 cycles of work (not single-cycle).

* **Sign-convention divergence**: Mathlib's `shiftedLegendre n (0) = 1`
  and `shiftedLegendre n (1) = (-1)^n`. Butcher's `Pn*(0) = (-1)^n`
  and `Pn*(1) = 1` (see (342b)). The two are related by the mirror
  `x ↦ 1 − x` (or equivalently the parity factor `(-1)^n`):

  > Butcher's `P_n*(x) = (-1)^n * Polynomial.shiftedLegendre n.eval x
  >                    = Polynomial.shiftedLegendre n.eval (1 - x)`.

  Both equalities hold via `shiftedLegendre_eval_symm`.

**Cycle 271 commits to shipping (342b) + (342c) ONLY** as the §342
opening deliverable. (342a) and the remaining (342d–g) are deferred
to cycle 272+, each as a separate single-cycle effort.

## C. Deliverables (priority order)

### Priority 0 (mandatory): create `OpenMath/Chapter3/Section342.lean`

Define Butcher's shifted Legendre polynomial via the Mathlib bridge:

```lean
import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Algebra.Polynomial.AlgebraMap

namespace OpenMath.Chapter3.Section342

open Polynomial

/-- Butcher's shifted Legendre polynomial `P_n*` on `[0,1]`
(Butcher §342, p. 236). Defined as `(-1)^n` times Mathlib's
`Polynomial.shiftedLegendre n` (cast to `ℝ`), which gives
`P_n*(1) = 1` per Butcher's normalisation (342b). Equivalently
(via Mathlib's `shiftedLegendre_eval_symm`), evaluating the same
polynomial at `1 - x`. -/
noncomputable def butcherShiftedLegendre (n : ℕ) : Polynomial ℝ :=
  Polynomial.C ((-1 : ℝ) ^ n) *
    (Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)
```

### Priority 1 (mandatory): prove (342b)

```lean
/-- Butcher §342 (342b): `P_n^*(1) = 1` for all `n`. -/
theorem butcherShiftedLegendre_eval_one (n : ℕ) :
    (butcherShiftedLegendre n).eval 1 = 1 := by
  ...
```

**Tactic recipe** (verify the load-bearing lemma names via
`lean_local_search` and `lean_loogle` BEFORE committing):

1. Unfold `butcherShiftedLegendre`:
   ```
   unfold butcherShiftedLegendre
   simp only [Polynomial.eval_mul, Polynomial.eval_C]
   ```
   Goal becomes `(-1)^n * ((shiftedLegendre n).map (Int.castRingHom ℝ)).eval 1 = 1`.
2. Push `eval` through `map` (verify `Polynomial.eval_map` exists,
   else use `Polynomial.eval₂_at_apply` chain):
   ```
   rw [Polynomial.eval_map]
   -- Goal: (-1)^n * eval₂ (Int.castRingHom ℝ) 1 (shiftedLegendre n) = 1
   -- Equivalently: (-1)^n * ((shiftedLegendre n).eval (1 : ℤ) : ℝ) = 1.
   ```
3. Apply `Polynomial.shiftedLegendre_eval_symm` at `R := ℤ`, `x := 1`:
   ```
   have hsymm := Polynomial.shiftedLegendre_eval_symm n (R := ℤ) 1
   -- hsymm : aeval 1 (shiftedLegendre n) = (-1)^n * aeval 0 (shiftedLegendre n)
   ```
4. Simplify `aeval 0 (shiftedLegendre n) = (shiftedLegendre n).coeff 0`:
   ```
   have h0 : (shiftedLegendre n).eval (0 : ℤ) = (shiftedLegendre n).coeff 0 := by
     rw [Polynomial.eval_zero_eq_coeff_zero] -- or unfold eval₂ + sum collapse
   rw [Polynomial.coeff_shiftedLegendre n 0]
   -- Goal: (-1)^0 * C(n,0) * C(n,n) = 1 ⇒ 1 * 1 * 1 = 1 ⇒ trivial.
   ```
5. Push everything back to ℝ via `Int.cast` and close with `ring` or
   `norm_num`.

**Fallback recipe (if step 3 fails)**: direct coefficient-sum
evaluation:
```
rw [butcherShiftedLegendre, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_map_int]
-- After cast simplification:
-- Goal: (-1)^n * (∑ k ∈ Finset.range (n+1),
--                    (-1)^k * C(n,k) * C(n+k,n)) = 1
-- This sum is a known binomial identity:
-- ∑_{k=0}^n (-1)^k C(n,k) C(n+k,n) = (-1)^n.
-- Mathlib may have this; if not, prove via induction or via
-- Vandermonde / Chu-Vandermonde.
```

Expected LOC: 10–30. Aristotle suitability: HIGH (the coefficient
sum identity is a standard target).

### Priority 2 (stretch, ship if Priority 1 closes axiom-clean): prove (342c)

Butcher's (342c): `P_n*(1-x) = (-1)^n * P_n*(x)`.

```lean
/-- Butcher §342 (342c): `P_n^*(1 - x) = (-1)^n * P_n^*(x)`. -/
theorem butcherShiftedLegendre_eval_one_sub (n : ℕ) (x : ℝ) :
    (butcherShiftedLegendre n).eval (1 - x) =
      (-1 : ℝ)^n * (butcherShiftedLegendre n).eval x := by
  ...
```

**Tactic recipe**:

1. `unfold butcherShiftedLegendre`; `simp [Polynomial.eval_mul,
   Polynomial.eval_C, Polynomial.eval_map_int]` on both sides.
2. Goal reduces to:
   `(-1)^n * (shiftedLegendre n).eval (1-x) =
    (-1)^n * ((-1)^n * (shiftedLegendre n).eval x)`
   (where the inner `.eval` is over ℤ-cast-to-ℝ; the integer-eval
   via `Polynomial.eval_map_int` and `Int.cast` machinery).
3. Apply `Polynomial.shiftedLegendre_eval_symm` at `R := ℝ`,
   `x := x`:
   `(shiftedLegendre n).eval (1-x) = (-1)^n * (shiftedLegendre n).eval x`
   (modulo cast manipulations — verify the `R := ℝ` instantiation
   works against the `.map (Int.castRingHom ℝ)` substrate).
4. Close by `ring` after cancelling `(-1)^n * (-1)^n = 1`.

Expected LOC: 15–25.

### Priority 3 (mandatory if P1 closes): non-vacuity witnesses

```lean
example : (butcherShiftedLegendre 0).eval 1 = 1 :=
  butcherShiftedLegendre_eval_one 0

example : (butcherShiftedLegendre 1).eval 1 = 1 :=
  butcherShiftedLegendre_eval_one 1

example : (butcherShiftedLegendre 2).eval 1 = 1 :=
  butcherShiftedLegendre_eval_one 2
```

If P2 closes, add:

```lean
example (x : ℝ) :
    (butcherShiftedLegendre 1).eval (1 - x) =
      -(butcherShiftedLegendre 1).eval x := by
  simpa using butcherShiftedLegendre_eval_one_sub 1 x
```

If time permits, also add a witness exhibiting the polynomial's
*degree* matches Mathlib's:

```lean
example (n : ℕ) : (butcherShiftedLegendre n).natDegree = n := by
  unfold butcherShiftedLegendre
  -- C ((-1)^n) is nonzero (since (-1)^n ≠ 0), so natDegree
  -- distributes through the multiplication.
  rw [Polynomial.natDegree_C_mul, Polynomial.natDegree_map]
  · exact Polynomial.natDegree_shiftedLegendre n
  · -- (-1)^n ≠ 0
    exact pow_ne_zero n (by norm_num)
```

### Priority 4 (mandatory if P1 closes): bookkeeping

1. **Add import to `OpenMath/Chapter3.lean`**: insert
   `import OpenMath.Chapter3.Section342` between `Section323` and
   `Section343` (topo order).
2. **Update `extraction/formalization_data/lean_status.json`** for
   `lem:342A`: status `unformalized` → `partial`; `lean_file`
   → `OpenMath/Chapter3/Section342.lean`; `lean_symbol`
   → `butcherShiftedLegendre_eval_one`; `cycle` → 271.
3. **Update `plan.md`** for `lem:342A`: `[ ]` → `[~]` with one-line
   cycle 271 closure note describing the partial coverage and
   remaining (342a)/(342d-g) deferral.
4. **Write `.prover-state/task_results/cycle_271.md`** following the
   CLAUDE.md template, including the faithfulness check from §H
   below.

## D. What NOT to try

* Do **NOT** attempt (342a) orthogonality in cycle 271. The proof
  via integration by parts on Rodrigues is genuinely 200–400 LOC
  and requires `intervalIntegral.integral_eq_sub_of_hasDeriv*` +
  `Polynomial.iteratedDeriv_*` machinery. It is multi-cycle work;
  rushing it produces a stalled scaffold per the cycle 200/201,
  138/139, 149/150 rollback precedents. Sorry-first scaffolds are
  forbidden by the supervisor's "no sorry increase" policy.

* Do **NOT** attempt (342e) Rodrigues bridge in this cycle.
  Mathlib's `factorial_mul_shiftedLegendre_eq` gives the bridge
  in Mathlib's sign convention; transcribing to Butcher's
  `(d/dx)^n ((x^2 - x)^n)` form requires `((x^2-x)^n) = (-1)^n *
  (x^n * (1-x)^n)` expansion plus an interplay with the cycle 271
  `(-1)^n` definitional factor. Defer.

* Do **NOT** redefine `butcherShiftedLegendre` via Mathlib's
  `.comp (1 - X)` form. Although mathematically equivalent
  (via `shiftedLegendre_eval_symm` lifted to polynomial equality),
  the multiplicative `(-1)^n * shiftedLegendre n` form gives
  cleaner proofs for (342b) and (342c). The `.comp (1 - X)` form
  forces `Polynomial.eval_comp` expansions that complicate the
  (342b) closure.

* Do **NOT** introduce sorries. The cycle's deliverable bar is
  "ship axiom-clean (342b) + non-vacuity, or the cycle fails."
  Stretch P2 must also ship axiom-clean if attempted; do not leave
  a sorried `_eval_one_sub` for the supervisor to flag.

* Do **NOT** raise `maxHeartbeats` above 200000. If (342b) stalls
  on a `simp` blowup, decompose into a private helper that
  evaluates the polynomial at 1 via `coeff_shiftedLegendre`
  per-term in `Finset.sum_range_succ` form.

* Do **NOT** introduce `axiom`/`constant` declarations.

* Do **NOT** modify any other file beyond
  `OpenMath/Chapter3/Section342.lean`, `OpenMath/Chapter3.lean`,
  `extraction/formalization_data/lean_status.json`, and `plan.md`.
  In particular, do NOT touch cycle 270's `Section311` work or
  cycles 266–270's `Section301` closed forms.

* Do **NOT** attempt to compile `OpenMath/Chapter4/Section441.lean`
  on GPFS — 43+ consecutive timeouts since cycle 182. Skip per
  `.prover-state/issues/cycle_182_gpfs_slowness.md`.

* Do **NOT** edit `scripts/autonomous_loop.py` or any
  supervisor-side infrastructure. Tautology-scanner false
  positives and prompt-builder phantoms are loop-maintainer
  territory per
  `.prover-state/issues/tautology_scanner_false_positives.md` and
  `.prover-state/issues/phantom_commit_verdict_pattern.md`.

* Do **NOT** pursue the polymorphic-`E` lift of cycle 266's
  `bseriesExactTerm_cherry_scalar` this cycle. Cycle 265 flagged
  this as MEDIUM-HIGH risk due to `ContinuousMultilinearMap`
  curry/uncurry plumbing, and after Phase E.1 is fully closed in
  the scalar setting the marginal value of the polymorphic-`E`
  lift is low without `lem:310B`'s labelled-tree quotient
  infrastructure.

## E. Risk inventory

| Risk | Severity | Mitigation |
|------|----------|------------|
| (R1) `Polynomial.eval_map` name drift | low | If Mathlib renamed to `eval_map'` or `Polynomial.eval_map_int`, fall back via `lean_local_search "eval_map"` |
| (R2) `simp` blowup on `(shiftedLegendre n).eval 1` | medium | Use Approach B (coefficient sum unfolding) as fallback; cite `coeff_shiftedLegendre` per-coefficient |
| (R3) `shiftedLegendre_eval_symm` ring instance | low | Mathlib's signature takes `{R : Type*} [Ring R]`; instantiate at `R := ℝ` explicitly via `(R := ℝ)` or at `R := ℤ` with subsequent cast |
| (R4) `Int.castRingHom ℝ` namespace | low | Verify via `lean_local_search "Int.castRingHom"`; stable since Lean 4.0 |
| (R5) noncomputable cascade on examples | low | All `example`s reduce to numerical evaluations via the closed theorem; should not trigger `noncomputable` requirement |
| (R6) `Polynomial.eval_zero_eq_coeff_zero` doesn't exist | low | Use `simp [Polynomial.eval]` to unfold the polynomial evaluation at 0 manually; the result `eval 0 p = p.coeff 0` is a definitional consequence |

## F. Aristotle batch suggestion (optional, fire-and-forget for cycle 272)

If P1 closes cleanly in ~30 min, consider submitting **(342a)
orthogonality** to Aristotle as a fire-and-forget background job
for cycle 272+. Aristotle template:

> namespace `OpenMath.Chapter3.Section342` (with Mathlib's
> `Polynomial.shiftedLegendre` and the cycle 271 `butcherShiftedLegendre`
> definition + (342b)/(342c) in scope), prove:
>
> ```lean
> theorem butcherShiftedLegendre_orthogonal {m n : ℕ} (hmn : m ≠ n) :
>     ∫ x in (0)..(1), (butcherShiftedLegendre m).eval x *
>       (butcherShiftedLegendre n).eval x = 0
> ```
>
> Hint: use Mathlib's `factorial_mul_shiftedLegendre_eq` (Rodrigues
> formula) and integration by parts `n+1` times on the larger of
> `m`, `n` to reduce the integrand to a constant times the lower-
> degree polynomial, then apply the same lemma to halve the
> degree. The boundary terms vanish because `X^n * (1-X)^n` and
> its first `n−1` derivatives vanish at both endpoints.

Submit one Aristotle job (project_id to be assigned by the worker).
**Do NOT poll** in cycle 271 per CLAUDE.md single-poll discipline;
cycle 272 will check the result.

## G. Verification checklist (run before claiming success)

1. `lake env lean OpenMath/Chapter3/Section342.lean` → exit 0.
2. `lake env lean OpenMath/Chapter3.lean` → exit 0.
3. `grep -c sorry OpenMath/Chapter3/Section342.lean` → `0`.
4. `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'
   OpenMath/Chapter3/Section342.lean` → no hits.
5. `#print axioms
   OpenMath.Chapter3.Section342.butcherShiftedLegendre_eval_one`
   → `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
6. If P2 shipped, repeat (5) on
   `butcherShiftedLegendre_eval_one_sub`.
7. Three non-vacuity `example`s compile.
8. Aggregator `lake env lean OpenMath/Chapter3.lean` rebuild after
   the new Section342 import lands.

## H. Faithfulness check (mandatory in task_results/cycle_271.md)

For `butcherShiftedLegendre`:

* Anchor entity: `lem:342A`
  (`extraction/formalization_data/entities/lem_342A.json`).
* Textbook statement (verbatim quote from JSON `statement_text`):
  > "There exist polynomials Pn∗ : [0, 1] → R, of degrees n, for
  > n = 0, 1, 2, . . . with the properties that ∫₀¹ P_m^* P_n^* dx
  > = 0, m ≠ n (342a), P_n^*(1) = 1 (342b), …"
* Lean type: `ℕ → Polynomial ℝ`. Captures: same content
  (polynomial on `[0,1]` of degree `n`) with explicit closed-form
  definition.
* **Definition smuggling check**: `butcherShiftedLegendre` is
  defined as `(-1)^n * Polynomial.shiftedLegendre n` (with the
  int-to-real cast). The "smuggling" concern would be if we
  defined `P_n*` as "the polynomial satisfying (342a)+(342b)" (an
  *implicit* definition). We avoid this by using Mathlib's
  explicit closed form. (342b) becomes a theorem, not a
  definitional axiom. ✓

For `butcherShiftedLegendre_eval_one` (342b):

* Hypothesis strength: no hypotheses beyond `n : ℕ`. Matches
  textbook.
* Tautology check: conclusion `eval 1 = 1` does NOT appear as a
  hypothesis. Proof goes through `shiftedLegendre_eval_symm` + a
  closed-form coefficient identity (non-vacuous).
* Identity check: not a trivial `exact h` proof.

For `butcherShiftedLegendre_eval_one_sub` (342c, if shipped):

* Hypothesis strength: no hypotheses beyond `n : ℕ`, `x : ℝ`.
* Definition smuggling check: NO — the parity is proved as a
  theorem via Mathlib's `shiftedLegendre_eval_symm`, not assumed.

## I. Cycle 272+ outlook

* **Cycle 272**: (342a) orthogonality — substantive integration-by-
  parts on Rodrigues. Estimated 200–400 LOC, single cycle if
  Aristotle returns the §F job COMPLETE; otherwise multi-cycle.
* **Cycle 273**: (342d) norm `∫₀¹ P_n*² = 1/(2n+1)` — direct
  corollary of (342a) + Rodrigues evaluation. ~80 LOC.
* **Cycle 274**: (342e) Butcher's Rodrigues formula bridge —
  `P_n*(x) = (1/n!) (d/dx)^n ((x²-x)^n)` from Mathlib's
  `factorial_mul_shiftedLegendre_eq`. ~50 LOC.
* **Cycle 275**: (342f) three-term recurrence. ~150 LOC.
* **Cycle 276**: (342g) `n` distinct real zeros in `(0,1)`. ~100 LOC,
  uses (342a) for the contradiction argument.
* **Cycle 277+**: pivot back to `lem:310B` Phase A (multi-cycle)
  or fresh entity per planner decision.

## J. Why pivot to §342 over polymorphic-E lift

The cycle 270 worker also listed "polymorphic-E lift of cycle 266's
`bseriesExactTerm_cherry_scalar`" (Phase D.1 / E.2) as an
alternative. Rejected for cycle 271:

* Risk: cycle 265 flagged this as MEDIUM-HIGH due to
  `ContinuousMultilinearMap.curry`/`uncurry` plumbing for
  `iteratedFDeriv ℝ n f` viewed as an N-multilinear map.
* Compounding: even if order-2 polymorphic ships, the §311 thread
  is essentially complete (orders 1–5 scalar, order 1 polymorphic).
  Extending to order ≥ 2 polymorphic delivers limited new content
  without `lem:310B`'s labelled-tree quotient infrastructure
  (per `.prover-state/issues/lem_310B_plan.md` Phase D).
* §342 detaches cleanly: a fresh chapter section, new Mathlib
  hooks (`Polynomial.shiftedLegendre`), and unblocks 5 downstream
  entities (`lem:359A`, `thm:324C`, `thm:344A`, `thm:358A`,
  `thm:363A`) over the multi-cycle `lem:342A` cluster.

Cycle 271's pivot to §342 is the higher-value option.

## K. Bottom line for the cycle 271 worker

Ship `OpenMath/Chapter3/Section342.lean` with:
* `butcherShiftedLegendre (n : ℕ) : Polynomial ℝ` (def, ~3 LOC).
* `butcherShiftedLegendre_eval_one : ∀ n, ... = 1` (theorem, ~15
  LOC).
* `butcherShiftedLegendre_eval_one_sub` (theorem, ~20 LOC) **IF
  AND ONLY IF** Priority 1 closes axiom-clean.
* Three non-vacuity `example`s (mandatory if P1 closes).
* One optional `natDegree` example (stretch).

Total file: ~80 LOC.

All axiom-clean (`[propext, Classical.choice, Quot.sound]`).
Sorry count remains 0. Update `lean_status.json`, `plan.md`,
`Chapter3.lean` import. Write `task_results/cycle_271.md` with the
§H faithfulness check.

If the cycle 271 worker hits a hard wall on Priority 1 — e.g.
`shiftedLegendre_eval_symm` doesn't fire on the cast substrate
after 30 min of `lean_multi_attempt` exploration — fall back to
the coefficient-sum recipe (Approach B in §C Priority 1). If THAT
also stalls, abandon the cycle to a documentation-only deliverable:
ship just the definition with a `_eval_one` stub `sorry` and file
a fresh issue describing the Mathlib API drift. This is the
absolute floor; under no circumstances should the cycle ship 2+
sorries.
