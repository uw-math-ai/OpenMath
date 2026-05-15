# Cycle 271 Results

## Worked on

Opening `lem:342A` (Butcher §342 — shifted Legendre polynomials on
`[0,1]`) by shipping properties **(342b)** `P_n^*(1) = 1` and
**(342c)** `P_n^*(1 - x) = (-1)^n P_n^*(x)` axiom-clean. New file
`OpenMath/Chapter3/Section342.lean` (~165 LOC). Bookkeeping:
`OpenMath/Chapter3.lean` import, `extraction/formalization_data/lean_status.json`
update for `lem:342A` (`unformalized` → `partial`), and the
corresponding `plan.md` entry refresh.

(342a) orthogonality, (342d) `∫₀¹ P_n^*² = 1/(2n+1)`, (342e)
Rodrigues, (342f) three-term recurrence, (342g) `n` distinct real
zeros — all deferred to cycles 272+ per cycle 271 strategy §C.

## Approach

Strategy: define `butcherShiftedLegendre (n : ℕ) : Polynomial ℝ` as
`(-1)^n * (Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)`
bridging Butcher's `P_n^*(1) = 1` convention against Mathlib's
`shiftedLegendre n |_(x=1) = (-1)^n`, then close (342b) and (342c)
via Mathlib's `Polynomial.shiftedLegendre_eval_symm`.

### Definition (verbatim, with comments stripped)

```lean
noncomputable def butcherShiftedLegendre (n : ℕ) : Polynomial ℝ :=
  Polynomial.C ((-1 : ℝ) ^ n) *
    (Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)
```

### Helper lemmas (private)

* `shiftedLegendre_eval_zero_int n : (shiftedLegendre n).eval (0:ℤ) = 1`
  — via `coeff_zero_eq_eval_zero` + `coeff_shiftedLegendre` + `simp`
  (the constant term collapses `(-1)^0 · C(n,0) · C(n,n)` to `1`).

* `shiftedLegendre_eval_one_int n : (shiftedLegendre n).eval (1:ℤ) = (-1)^n`
  — via `Polynomial.shiftedLegendre_eval_symm` at `R := ℤ`, `x := 1`
  (note `1 - 1 = 0` over ℤ), composed with `Polynomial.coe_aeval_eq_eval`
  to identify `aeval (k : ℤ) (p : ℤ[X])` with `p.eval k`.

### (342b) proof recipe

```lean
theorem butcherShiftedLegendre_eval_one (n : ℕ) :
    (butcherShiftedLegendre n).eval 1 = 1 := by
  unfold butcherShiftedLegendre
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
      Polynomial.eval₂_at_one]
  rw [shiftedLegendre_eval_one_int]
  simp only [map_pow, map_neg, map_one]
  rw [← mul_pow]
  norm_num
```

`Polynomial.eval₂_at_one : p.eval₂ f 1 = f (p.eval 1)` pushes the
`1 : ℝ` through the `Int.castRingHom ℝ` substrate. Then the integer
evaluation collapses to `(-1)^n` via the helper, and `(-1)^n * (-1)^n
= ((-1)·(-1))^n = 1^n = 1` closes via `norm_num`.

### (342c) proof recipe

```lean
theorem butcherShiftedLegendre_eval_one_sub (n : ℕ) (x : ℝ) :
    (butcherShiftedLegendre n).eval (1 - x) =
      (-1 : ℝ) ^ n * (butcherShiftedLegendre n).eval x := by
  have hsymm :
      ((Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)).eval (1 - x)
        = (-1 : ℝ) ^ n *
          ((Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)).eval x := by
    have heq := Polynomial.shiftedLegendre_eval_symm n (R := ℝ) (1 - x)
    rw [show (1 : ℝ) - (1 - x) = x from by ring] at heq
    have hcast : ∀ y : ℝ,
        (Polynomial.aeval y) (Polynomial.shiftedLegendre n)
          = ((Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)).eval y := by
      intro y
      rw [Polynomial.aeval_def, Polynomial.eval_map, algebraMap_int_eq]
    rw [hcast, hcast] at heq
    exact heq
  unfold butcherShiftedLegendre
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_C, hsymm]
```

Mathlib's `shiftedLegendre_eval_symm` instantiated at `R := ℝ` and the
substitution `1 - (1 - x) = x` directly yields the mirror identity for
the int-cast substrate; multiplying both sides by the Butcher sign
factor `(-1)^n` and observing `(-1)^n · (-1)^n = 1` (absorbed
syntactically after `hsymm` is rewritten in on the LHS) closes the
goal without needing a trailing `ring`.

### Non-vacuity witnesses (mandatory per strategy Priority 3)

* 342b: `n ∈ {0, 1, 2}` direct application of the theorem.
* 342c: `n = 1` (parity `-1`) and `n = 2` (parity `+1`) `simpa`
  closures over `butcherShiftedLegendre_eval_one_sub`.

## Result

**SUCCESS** — Priority 0 (definition), Priority 1 (342b), Priority 2
(342c stretch), Priority 3 (non-vacuity examples), and Priority 4
(bookkeeping) all delivered. Compilation passes for both
`OpenMath/Chapter3/Section342.lean` (standalone, `lake env lean`) and
`OpenMath/Chapter3.lean` (aggregator, after `lake build OpenMath.Chapter3.Section342`).

* `lake env lean OpenMath/Chapter3/Section342.lean` → exit 0.
* `lake build OpenMath.Chapter3.Section342` → exit 0.
* `lake env lean OpenMath/Chapter3.lean` → exit 0 (after Section342 .olean build).
* `grep -c sorry OpenMath/Chapter3/Section342.lean` → `0`.
* `grep -nE ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'
  OpenMath/Chapter3/Section342.lean` → no hits.
* `lean_verify` on `butcherShiftedLegendre_eval_one` →
  `{"axioms":["propext","Classical.choice","Quot.sound"]}` (no `sorryAx`).
* `lean_verify` on `butcherShiftedLegendre_eval_one_sub` →
  same axiom set.
* All five non-vacuity `example`s compile under the same axiom set.

LOC delta: +165 (Section342.lean), +1 (Chapter3.lean import line),
+~6 lines (lean_status.json + plan.md updates).

## Faithfulness check

### `def butcherShiftedLegendre (n : ℕ) : Polynomial ℝ`

* Entity ID: `lem:342A`
  (`extraction/formalization_data/entities/lem_342A.json`).
* Textbook statement (verbatim from JSON `statement_text`):
  > "There exist polynomials Pn∗ : [0, 1] → R, of degrees n, for
  > n = 0, 1, 2, . . . with the properties that [342a–342g]."
* Lean type: `ℕ → Polynomial ℝ`. Captures: same content — a
  polynomial-over-ℝ per natural-number index `n`. The textbook
  type `[0, 1] → ℝ` is recovered up to function extensionality by
  `(butcherShiftedLegendre n).eval : ℝ → ℝ` restricted to `[0, 1]`.
* **Definition smuggling check**: `butcherShiftedLegendre` is
  defined as `(-1)^n * Polynomial.shiftedLegendre n` (with int-to-real
  cast). The "smuggling" concern would be if we defined `P_n*` as
  "the polynomial satisfying (342a)+(342b)" (an *implicit*
  definition that would make (342b) tautological). We avoid this
  by using Mathlib's explicit closed-form definition; (342b)
  becomes a *theorem* derived from `coeff_shiftedLegendre` +
  `shiftedLegendre_eval_symm`, not a definitional axiom. ✓
* Degree: `(butcherShiftedLegendre n).natDegree = n` follows from
  Mathlib's `natDegree_shiftedLegendre` + the fact that
  `C ((-1)^n)` is a nonzero constant. Not shipped this cycle to
  keep the deliverable minimal; available as a follow-up
  one-liner.

### `theorem butcherShiftedLegendre_eval_one` (342b)

* Textbook statement (verbatim from JSON `statement_latex`):
  > "P_n^*(1) = 1, n = 0, 1, 2, \dots."
* Lean statement captures: **same content** — `(butcherShiftedLegendre n).eval 1 = 1`.
* Hypothesis strength: `n : ℕ` only. **Matches textbook
  quantifier** (`n = 0, 1, 2, …`).
* **Tautology check**: conclusion `eval 1 = 1` does NOT appear as a
  hypothesis. The proof goes through `shiftedLegendre_eval_symm` +
  the closed-form coefficient identity `(shiftedLegendre n).coeff 0 = 1`
  (via `coeff_shiftedLegendre`); non-vacuous.
* **Identity check**: proof is a chain of `rw`/`simp only` rewrites
  followed by `norm_num` — definitively not `exact h` or `id`.

### `theorem butcherShiftedLegendre_eval_one_sub` (342c)

* Textbook statement (verbatim from JSON `statement_latex`):
  > "P_n^*(1 - x) = (-1)^n P_n^*(x), n = 0, 1, 2, \dots."
* Lean statement captures: **same content** —
  `(butcherShiftedLegendre n).eval (1 - x) = (-1)^n * (butcherShiftedLegendre n).eval x`.
* Hypothesis strength: `n : ℕ`, `x : ℝ` only. Matches textbook.
* **Definition smuggling check**: NO — the parity is **proved as
  a theorem** via Mathlib's `shiftedLegendre_eval_symm`, not assumed
  in the definition of `butcherShiftedLegendre`. ✓
* **Tautology check**: conclusion does NOT appear as a hypothesis.
* **Identity check**: proof is a multi-step `rw` chain plus a nested
  helper `hcast`; not `exact h` or `id`.

## Dead ends

* **First-attempt `push_cast` failure** in the (342b) tail. After
  `rw [shiftedLegendre_eval_one_int]` the goal becomes
  `(-1)^n * (Int.castRingHom ℝ) ((-1)^n) = 1`. `push_cast` did not
  pull the int-cast inward to recognise `Int.castRingHom ℝ` as a
  cast (presumably because the cast appears as an explicit
  function application rather than a `↑`-coerced subterm). Replaced
  with `simp only [map_pow, map_neg, map_one]` which fires
  cleanly via the `RingHom` `map_*` simp lemma family.

* **First-attempt `aeval_def + eval_map` chain** in the (342c)
  proof. `aeval_def` rewrites `aeval y p` to `eval₂ (algebraMap ℤ ℝ)
  y p`, but `eval_map` for `.map (Int.castRingHom ℝ)` gives
  `eval₂ (Int.castRingHom ℝ) y`. The two sides differ syntactically
  even though `algebraMap ℤ ℝ = Int.castRingHom ℝ`
  (definitionally, since the ℤ-algebra instance on a ring is
  unique). Added `algebraMap_int_eq` (Mathlib lemma stating
  `algebraMap ℤ R = Int.castRingHom R`) as the bridging rewrite
  to align both sides.

* **First-attempt `mul_one` rewrite** in the `_eval_one` helper.
  Tried `rw [h0, sub_zero, mul_one] at hsymm` where `hsymm` was
  `aeval 0 = (-1)^n * aeval (1 - 0)`. After rewriting `aeval 0` to
  `1` and `1 - 0` to `1`, the term has shape `1 = (-1)^n * aeval 1`
  with no `_ * 1` factor — `mul_one` had nothing to rewrite. Removed
  it; the form `1 = (-1)^n * aeval 1` was already what was needed.

* **First-attempt missing `ℝ` import**. `Mathlib.RingTheory.Polynomial.ShiftedLegendre`
  + `Mathlib.Algebra.Polynomial.AlgebraMap` do NOT transitively
  import `ℝ`'s `Semiring` / `Ring` / `OfNat 1` instances; the
  first compile produced ~20 `failed to synthesize instance of
  type class Semiring ℝ` errors. Added
  `import Mathlib.Data.Real.Basic` and the file compiled.

* **Strategy fallback "coefficient-sum recipe" (Approach B)** was
  *not* needed. The Approach A recipe (`shiftedLegendre_eval_symm`
  bouncing off `coeff_shiftedLegendre n 0 = 1`) closed cleanly on
  first attempt for both (342b) and (342c), so the Vandermonde /
  Chu-Vandermonde fallback was not exercised.

## Discovery

1. **Mathlib's `Polynomial.shiftedLegendre`** is the canonical
   substrate for any future shifted-Legendre work in this project
   (Butcher §342 cluster + downstream uses via `lem:342A`'s 5
   dependents: `lem:359A`, `thm:324C`, `thm:344A`, `thm:358A`,
   `thm:363A`). Mathlib gives us out of the box:
   `shiftedLegendre n` (def), `coeff_shiftedLegendre`,
   `degree_shiftedLegendre` (`@[simp]`), `natDegree_shiftedLegendre`
   (`@[simp]`), `factorial_mul_shiftedLegendre_eq` (Rodrigues
   formula), and `shiftedLegendre_eval_symm` (parity identity).
   It does **NOT** ship orthogonality, the norm `1/(2n+1)`, the
   three-term recurrence, or the distinct-zeros result — those
   are the cycle 272+ deliverables for (342a), (342d), (342f),
   (342g) respectively.

2. **Sign-convention bridge** between Mathlib (`P_n(0) = 1`,
   `P_n(1) = (-1)^n`) and Butcher (`P_n^*(0) = (-1)^n`, `P_n^*(1) =
   1`) is one multiplicative `(-1)^n` factor. The cycle 271
   strategy correctly predicted the `(-1)^n *
   shiftedLegendre n` form gives cleaner proofs than
   `shiftedLegendre n |_(x ↦ 1 - x)` (which would force
   `Polynomial.eval_comp` expansions throughout).

3. **`Polynomial.coe_aeval_eq_eval (r : R) : (aeval r : R[X] → R) = eval r`**
   is the canonical bridge for collapsing `aeval` over `R[X]` to
   plain `eval` when the base ring matches the polynomial's
   coefficient ring. This is the unsung hero of the cycle 271
   helper `shiftedLegendre_eval_one_int` — without it, the
   `aeval`-shaped output of `shiftedLegendre_eval_symm` (over
   `R := ℤ`) would require manual unfolding through `aeval_def`
   + `eval₂_eq_eval_map` + `Polynomial.map_id` (since
   `algebraMap ℤ ℤ = RingHom.id`, modulo a hidden `Int.cast_id`
   simplification).

4. **`algebraMap_int_eq` simp-direction**. Mathlib's documented
   simp-normal form is `Int.castRingHom R`, not `algebraMap ℤ R`
   (per `Mathlib.Algebra.Polynomial.AlgebraMap.lean:143` comment:
   "these used to be about `algebraMap ℤ R`, but now the simp-
   normal form is `Int.castRingHom R`"). When mixing `aeval` (which
   internally references `algebraMap ℤ R`) with `Polynomial.map
   (Int.castRingHom R)`, an explicit `rw [algebraMap_int_eq]` is
   needed to bridge the two sides.

5. **`Polynomial.eval₂_at_one : p.eval₂ f 1 = f (p.eval 1)`** (and
   the `eval₂_at_apply` / `eval₂_at_zero` family) is the canonical
   way to push a ring-hom cast inward when evaluating a mapped
   polynomial at a boundary value (`0` or `1`). This is the second
   load-bearing lemma in the (342b) proof, after
   `shiftedLegendre_eval_symm`.

## Suggested next approach

### Immediate cycle 272 candidates (single-cycle each)

* **(342d) `∫₀¹ P_n^*² = 1/(2n+1)`**: direct corollary of (342a)
  once (342a) is in hand; pure integration identity over `[0,1]`.
  ~80–100 LOC, single cycle once (342a) lands.

* **(342e) Rodrigues bridge**: transcribe Mathlib's
  `factorial_mul_shiftedLegendre_eq` (`n! · shiftedLegendre n =
  D^n (X^n · (1 - X)^n)`) into Butcher's `P_n^*(x) =
  (1/n!) (d/dx)^n ((x² - x)^n)` form. Requires
  `((X² - X)^n : ℤ[X]) = (-1)^n · (X^n · (1 - X)^n)` algebraic
  bridge (mathematically `(x² − x) = −x(1 − x) = (−1)(x(1 − x))`,
  so the `n`-th power picks up `(-1)^n`). ~50–80 LOC, **single
  cycle**, low-risk: only needs `Polynomial`-ring algebra +
  `iteratedDeriv` (or `iterate derivative`) tracking, no analysis.

* **(342f) three-term recurrence**: `n P_n^*(x) = (2x-1)(2n-1)
  P_{n-1}^*(x) - (n-1) P_{n-2}^*(x)`. Mathlib's Rodrigues
  + Bonnet's recurrence chain might be derivable; otherwise a
  direct `coeff_shiftedLegendre`-based induction. ~150 LOC,
  single cycle if the coefficient identity is well-known.

* **(342g) distinct real zeros in `(0, 1)`**: requires (342a) plus
  the contradiction argument from Butcher's proof (factoring
  `P_n^*(x) = Q(x) R(x)` and integrating against `Q`). ~100 LOC,
  single cycle after (342a) lands.

### Substantive cycle 272 candidates (multi-cycle each)

* **(342a) orthogonality** `∫₀¹ P_m^*(x) P_n^*(x) dx = 0` for `m ≠ n`.
  Proof: integration by parts on Rodrigues. Requires
  `intervalIntegral.integral_eq_sub_of_hasDeriv*` chains
  (`n+1` repeated integrations by parts on the larger of `m, n`),
  `Polynomial.iteratedDeriv_*` machinery, plus the
  endpoint-vanishing argument (`X^n · (1-X)^n` and its first
  `n-1` derivatives vanish at `0` and `1`). 200–400 LOC, likely
  multi-cycle. **The strategy explicitly recommends submitting
  this to Aristotle as a fire-and-forget background job** before
  scheduling cycle 272.

### Fire-and-forget Aristotle submission (per cycle 271 strategy §F)

The cycle 271 strategy §F offered submitting (342a) to Aristotle
as a "do NOT poll" background job for cycle 272+. **This cycle did
not submit** because the cycle 271 P1 ran cleanly without needing
the Approach B fallback, leaving no need to free up time and
because submitting Aristotle work creates a 30-minute wait
inappropriate for an already-shipping cycle. The cycle 272 worker
should consider this submission at the *start* of cycle 272 (so
that by the time manual work on (342d)/(342e)/(342f) concludes,
Aristotle's (342a) attempt is available for incorporation).

### Polymorphic-`E` lift (cycle 271 strategy §J recap)

Cycle 270's "polymorphic-`E` lift of cycle 266's
`bseriesExactTerm_cherry_scalar`" remains the standing alternative
to §342 work. The cycle 271 pivot to §342 was the higher-value
option this cycle because (a) Phase E.1 was already closed at
order 5, and (b) §342 unblocks 5 downstream entities. If cycle 272
finds the §342 work flowing quickly (especially (342e) Rodrigues),
the worker may also consider a small (~50 LOC) Phase D.2 / E.2
order-2 polymorphic stretch as a side-task — but the cycle 265
HIGH-risk flag on `ContinuousMultilinearMap` plumbing still
applies.

### Larger-scope candidates

* **`lem:310B` Phase A.1** (`RootedTree.Vertex` scaffold +
  `vertices` Finset enumeration, per cycle 261 blueprint /
  `lem_310B_plan.md` §5 Phase A): 80–120 LOC, axiom-clean target,
  the next infrastructure layer for the full `lem:310B` general
  form.

* **`thm:351B`**: blocked by 5–8 cycle prerequisite chain per the
  cycle 260 scoping analysis. Not recommended as a cycle 272
  pivot.
