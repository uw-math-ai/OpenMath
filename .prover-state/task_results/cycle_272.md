# Cycle 272 Results

## Worked on

Extending `lem:342A` coverage in
`OpenMath/Chapter3/Section342.lean` with two new axiom-clean results:

* **(342e) Rodrigues' formula** as the polynomial identity over
  `ℝ[X]`:
  ```
  C (n! : ℝ) * butcherShiftedLegendre n
    = C ((-1)^n) * derivative^[n] (X^n * (1 - X)^n)
  ```
* **(degree of `P_n^*`)** stretch lemma:
  `(butcherShiftedLegendre n).natDegree = n`.

Plus three non-vacuity `example`s for (342e) at `n ∈ {0, 1, 2}`.

(342a) orthogonality / (342d) norm / (342f) recurrence / (342g)
distinct zeros remain deferred per cycle 272 strategy §D. No
Aristotle submission was fired this cycle (decided to defer (342a)
manually for now — cycle 273+ may revisit).

File deltas:
* `OpenMath/Chapter3/Section342.lean`: 159 → 246 LOC
  (~87 LOC added: 1 import, 1 theorem + docstring, 3 non-vacuity
  `example`s, 1 stretch theorem + docstring).
* New import: `Mathlib.Algebra.Polynomial.Degree.Lemmas`
  (needed for `Polynomial.natDegree_map_eq_of_injective`).
* `extraction/formalization_data/lean_status.json`: no change
  (entity-level status stays `partial`).
* `plan.md`: refreshed `lem:342A` line to note (342e) closure.

## Approach

### (342e) `butcherShiftedLegendre_rodrigues`

Strategy §B.3 recipe (Shape A). Lifted Mathlib's
`Polynomial.factorial_mul_shiftedLegendre_eq` from `ℤ[X]` to `ℝ[X]`
along `Int.castRingHom ℝ`:

```lean
theorem butcherShiftedLegendre_rodrigues (n : ℕ) :
    Polynomial.C ((n.factorial : ℝ)) * butcherShiftedLegendre n
      = Polynomial.C ((-1 : ℝ) ^ n) *
        Polynomial.derivative^[n]
          ((Polynomial.X : Polynomial ℝ) ^ n *
            (1 - (Polynomial.X : Polynomial ℝ)) ^ n) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℝ))
    (Polynomial.factorial_mul_shiftedLegendre_eq n)
  rw [Polynomial.map_mul, Polynomial.map_natCast,
      ← Polynomial.iterate_derivative_map,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X] at h
  rw [← Polynomial.C_eq_natCast] at h
  unfold butcherShiftedLegendre
  rw [← mul_assoc,
      mul_comm (Polynomial.C ((n.factorial : ℝ)))
               (Polynomial.C ((-1 : ℝ) ^ n)),
      mul_assoc, h]
```

Key hooks:
* `Polynomial.factorial_mul_shiftedLegendre_eq` (Mathlib, ℤ[X]) —
  exact name + shape `(n ! : ℤ[X]) * shiftedLegendre n =
  derivative^[n] (X^n * (1 - X)^n)`.
* `Polynomial.iterate_derivative_map` —
  `derivative^[k] (p.map f) = (derivative^[k] p).map f` (@[simp];
  used reversed to push `map f` inside `derivative^[k]`).
* `Polynomial.map_natCast` to push `map ι` through `(n! : ℤ[X])`.
* `Polynomial.C_eq_natCast : C (n : R) = (n : R[X])` to bridge
  the natCast form of `n!` with `Polynomial.C (n!)` on the goal.

The proof closed first attempt on the first compile (no fallback
needed). 13 LOC of tactic body.

### Stretch: `butcherShiftedLegendre_natDegree`

```lean
theorem butcherShiftedLegendre_natDegree (n : ℕ) :
    (butcherShiftedLegendre n).natDegree = n := by
  have h_unit : IsUnit ((-1 : ℝ) ^ n) :=
    isUnit_iff_ne_zero.mpr (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0))
  have h_inj : Function.Injective (Int.castRingHom ℝ) :=
    Int.cast_injective
  unfold butcherShiftedLegendre
  rw [Polynomial.natDegree_C_mul_of_isUnit h_unit,
      Polynomial.natDegree_map_eq_of_injective h_inj,
      Polynomial.natDegree_shiftedLegendre]
```

Required new import:
`Mathlib.Algebra.Polynomial.Degree.Lemmas` for
`Polynomial.natDegree_map_eq_of_injective`. (First compile attempt
failed with `unknownIdentifier` because that lemma's module is not
transitively imported from `Mathlib.RingTheory.Polynomial.ShiftedLegendre`.)

Stretch theorem closed in 8 LOC.

## Result

**SUCCESS — both (342e) and the stretch `natDegree` lemma ship
axiom-clean** with `[propext, Classical.choice, Quot.sound]` only.

`lean_verify` results:
* `butcherShiftedLegendre_rodrigues`:
  `["propext", "Classical.choice", "Quot.sound"]`.
* `butcherShiftedLegendre_natDegree`:
  `["propext", "Classical.choice", "Quot.sound"]`.

File compiles `lake env lean OpenMath/Chapter3/Section342.lean` →
exit 0. `lake env lean OpenMath/Chapter3.lean` → exit 0 (no
downstream regressions). Cycle 271's deliverables
(`butcherShiftedLegendre_eval_one`,
`butcherShiftedLegendre_eval_one_sub`) re-verified axiom-clean —
nothing was modified there.

Sorry count: 0 → 0.

## Faithfulness check

### `butcherShiftedLegendre_rodrigues` — Butcher (342e), p. 236

Entity ID `lem:342A`, textbook statement (from
`extraction/formalization_data/entities/lem_342A.json`, quoting the
(342e) sub-property):
> `P_n^*(x) = (1/n!) (d/dx)^n ((x^2 - x)^n)`

Lean statement captures: **same content (equivalent reformulation)**.

Equivalence: `(x^2 - x)^n = (-(x - x^2))^n = (-1)^n (x - x^2)^n =
(-1)^n (x · (1 - x))^n = (-1)^n x^n (1 - x)^n`. Substituting into
Butcher's (342e):
```
P_n^*(x) = (1/n!) · (d/dx)^n ((x^2 - x)^n)
        = (1/n!) · (-1)^n · (d/dx)^n (x^n (1 - x)^n).
```
Multiplying both sides by `n!` (a nonzero `ℝ`) clears the division
and yields the polynomial-ring identity stated as
`butcherShiftedLegendre_rodrigues`:
```
n! · P_n^*(x) = (-1)^n · (d/dx)^n (x^n (1 - x)^n).
```
The Lean statement is the polynomial-ring identity rather than the
function-evaluation identity — strictly stronger (function identity
follows by `eval`), and avoids dividing by `n!`. No hidden hypotheses
beyond `n : ℕ`.

Tautology check: conclusion is `LHS = RHS` over `ℝ[X]`, with
`LHS = C (n! : ℝ) * butcherShiftedLegendre n` and
`RHS = C ((-1)^n) * derivative^[n] (X^n (1-X)^n)`. These are
structurally distinct expressions — no hypothesis-restating bug.

Identity check: proof is not `exact h`; it does genuine algebraic
work bridging Mathlib's `ℤ[X]` Rodrigues to the Butcher-convention
`ℝ[X]` statement.

Hypothesis strength: only `n : ℕ`. Butcher's (342e) is also stated
for all `n = 0, 1, 2, …` so no extra hypotheses.

### `butcherShiftedLegendre_natDegree` — Butcher (342A first
clause), p. 236

Entity ID `lem:342A`, textbook statement: "polynomials … of degrees
`n`, for `n = 0, 1, 2, …`".

Lean statement captures: **same content**. Butcher's claim "degree
`n`" matches `natDegree = n` exactly. Hypothesis strength: only
`n : ℕ`. Tautology check: passes (LHS is `natDegree (…)`, a
function call; RHS is the bound variable `n`).

### Non-vacuity `example`s (342e at `n ∈ {0, 1, 2}`)

Three `example` blocks instantiate `butcherShiftedLegendre_rodrigues`
at `n = 0, 1, 2`. Each compiles → confirms (342e) is non-vacuous
at the smallest finite cases. These witnesses also serve as a
sign-convention sanity check (if the `(-1)^n` factor were on the
wrong side, the `n = 1` example would diverge from Butcher's
`P_1^*(x) = 2x - 1`).

## Dead ends

None this cycle. The §B.3 recipe from the planner's strategy worked
on first compile.

The only friction point was the missing import for
`Polynomial.natDegree_map_eq_of_injective` (stretch lemma), resolved
in one edit by adding `import Mathlib.Algebra.Polynomial.Degree.Lemmas`.

## Discovery

### Mathlib hook shape confirmed at HEAD

`Polynomial.factorial_mul_shiftedLegendre_eq n` is *exactly*
`(n ! : ℤ[X]) * shiftedLegendre n = derivative^[n] (X^n * (1 - X)^n)`
in `ℤ[X]`. No `smul` form, no `Polynomial.C`-wrapped factorial —
the natural-number cast `Nat.cast (n!) : ℤ[X]` is used directly.
This matches strategy §B.3 expectation (`Polynomial.map_natCast`
suffices for push-down).

### `iterate_derivative_map` is `@[simp]`

`Polynomial.iterate_derivative_map` carries `@[simp]`, but the
direction is `derivative^[k] (p.map f) = (derivative^[k] p).map f`
(map outside `derivative^[k]`). We need the reverse direction to
push `map` inside, so `rw [← Polynomial.iterate_derivative_map]`
is required. `simp` will NOT close this for free.

### Module-level imports needed for degree lemmas

`Mathlib.RingTheory.Polynomial.ShiftedLegendre` does not
transitively import `Mathlib.Algebra.Polynomial.Degree.Lemmas`
(which houses `natDegree_map_eq_of_injective` and
`degree_map_eq_of_injective`). Future cycles touching `natDegree`
lemmas on `Polynomial`-valued constructions should add this import
proactively.

### `Int.cast_injective` is enough for `Int.castRingHom ℝ`

`Int.cast_injective : Function.Injective (Int.cast : ℤ → α)` (with
`[CharZero α]`) elaborates directly as
`Function.Injective ⇑(Int.castRingHom ℝ)` — no further unfolding
needed. Useful for any future ℤ→ℝ polynomial lift.

## Suggested next approach

Cycle 273 candidates (priority-ordered, each ~single-cycle):

1. **(342f) three-term recurrence** (~150 LOC, MEDIUM risk). Now
   that (342e) lands and `natDegree` is available, the recurrence
   `n P_n^* = (2x - 1)(2n - 1) P_{n-1}^* - (n - 1) P_{n-2}^*` is
   the next natural §342 deliverable. Need to check whether
   Mathlib's `shiftedLegendre` has a recurrence already; if not,
   prove directly via `coeff_shiftedLegendre` induction or via
   leading-coefficient comparison + Butcher's parity argument
   (orthogonality not required for (342f)).

2. **Fire-and-forget Aristotle (342a)**. Now that the §342
   infrastructure includes (342b), (342c), (342e), an Aristotle
   submission of (342a) orthogonality with Rodrigues as a provided
   hypothesis becomes much more tractable. Strategy §A's recipe
   stands; cycle 273 should fire the job at cycle-start and poll
   at cycle 274.

3. **Polymorphic-`E` lift** (Phase D.2/E.2 of `lem_310B_plan.md`).
   Still flagged HIGH risk from cycle 265 (`ContinuousMultilinearMap`
   plumbing). Defer further; §342 yields better textbook progress
   per cycle.

4. **`lem:310B` Phase A.1** (`RootedTree.Vertex` + `vertices`
   Finset). ~80–120 LOC, axiom-clean target — orthogonal to §342
   and good for a "break" cycle if needed.

Recommended cycle 273 sequence: option (1) (342f) if planner judges
the leading-coefficient approach tractable; otherwise option (2)
(fire Aristotle (342a)) + option (4) (lem:310B Phase A.1) in
parallel.
