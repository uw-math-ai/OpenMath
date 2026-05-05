# Cycle 133 Results

## Worked on

Priority 1 from the planner: strengthening `def:551A` non-vacuity by
adding a substantive `r = 2` witness `padded2DEulerGLM_isIRKStable`
to `OpenMath/Chapter5/Section520.lean`. The cycle 131 witness
`explicitEulerGLM_isIRKStable` (`r = 1`) discharged the `∀ i ≠ 0`
clauses *vacuously* over an empty index set; this cycle adds a
second witness in which those clauses range over the genuinely
non-empty index `i = 1` and are discharged by direct computation.

## Approach

1. Read `extraction/formalization_data/entities/def_551A.json` to
   re-confirm the textbook predicate (already encoded in cycle 131,
   not modified here).
2. Read `OpenMath/Chapter5/Section510.lean` to confirm
   `GeneralLinearMethod` has exactly the four fields `A, U, B, V`
   (no abscissae or auxiliary data).
3. Inserted, immediately after `explicitEulerGLM_isIRKStable` at
   `Section520.lean:619`, the new definition `padded2DEulerGLM`
   (s = 1, r = 2) with

   ```
   A := !![0]
   U := !![1, 0]
   B := !![1; 0]
   V := !![1, 0; 0, 0]
   ```

4. Proved `padded2DEulerGLM_isIRKStable` with `X := 0`. The proof
   structure is
   `refine ⟨?_, 0, ?_, ?_⟩`, then for each clause:
   - (551a) clause: `intro i; fin_cases i <;> simp [padded2DEulerGLM]`.
   - `B*A − X*B` clause: `intro i j hi; fin_cases i; · exact absurd
     rfl hi; · fin_cases j; simp [padded2DEulerGLM]`.
   - `B*U − X*V + V*X` clause: same shape with
     `<;> simp [padded2DEulerGLM]` over both `j` cases.

   The `simp [padded2DEulerGLM]` invocations close the row-1 entries
   by unfolding the matrix literals and reducing `0 * ... = 0`.

5. Cleaned up the initial proof: an earlier version explicitly
   listed `Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero`
   in the `simp` argument list. The unused-simp-arg linter flagged
   all three as redundant given `padded2DEulerGLM` (which provides
   the matrix literals); removing them keeps the file warning-free.

6. Verified `lake env lean OpenMath/Chapter5/Section520.lean` exits 0
   with no warnings, then `lake build OpenMath.Chapter5.Section520`
   exits 0, then ran a `#print axioms` check on both
   `padded2DEulerGLM_isIRKStable` and the cycle 131 witness
   `explicitEulerGLM_isIRKStable` to confirm both depend only on
   `[propext, Classical.choice, Quot.sound]`.

7. Updated `plan.md` for the `def:551A` row to reference the new
   substantive witness alongside the existing vacuous one. Did NOT
   touch `lean_status.json` — `def:551A` is already `formalized`
   (its `lean_symbol` is `…IsIRKStable`, the predicate, which is
   unchanged); adding a second witness is strengthening evidence,
   not a status change.

Per the strategy I did NOT use Aristotle (the proof is two ~5-line
entry-wise computations, well below Aristotle's round-trip overhead).

## Result

**SUCCESS.**

* `lake env lean OpenMath/Chapter5/Section520.lean` exits 0 (no
  warnings, no errors, no `sorry`).
* `lake build OpenMath.Chapter5.Section520` exits 0
  (`Build completed successfully (2772 jobs).`).
* `#print axioms OpenMath.Chapter5.Section510.padded2DEulerGLM_isIRKStable`
  → `[propext, Classical.choice, Quot.sound]` (axiom-clean).
* `#print axioms OpenMath.Chapter5.Section510.explicitEulerGLM_isIRKStable`
  → `[propext, Classical.choice, Quot.sound]` (no regression).
* No new `sorry` introduced. Total sorry count in `OpenMath/`
  remains 0.
* `plan.md` updated. `lean_status.json` left unchanged (correct,
  per strategy).

Progress count: 69 / 175 (unchanged — `def:551A` was already
counted; a second witness does not advance an entity).

## Faithfulness check

Two new declarations introduced this cycle.

### `def padded2DEulerGLM : GeneralLinearMethod 1 2`

* Entity ID: **none — this is a witness/instance**, not a named
  textbook concept. It is analogous to the existing `explicitEulerGLM`
  and `implicitMidpointGLM` in `Section510.lean`, which are also
  unnamed-in-textbook witnesses introduced solely to certify
  non-vacuity of nearby predicates.
* "Definition matches textbook" check: **N/A** (no textbook entity
  to compare against). The faithfulness question for a witness
  reduces to "does this object actually satisfy the predicate, with
  the predicate unchanged?" — addressed by the proof of
  `padded2DEulerGLM_isIRKStable` below.
* Definition smuggling check: N/A (no `Prop` fields, no class).
* Hypothesis strength check: N/A (a `def` of a concrete GLM has no
  hypotheses).

### `theorem padded2DEulerGLM_isIRKStable : padded2DEulerGLM.IsIRKStable`

* Entity ID: `def:551A`. Textbook statement (quoted from
  `extraction/formalization_data/entities/def_551A.json`):

  > A general linear method (A, U, B, V) is `inherently Runge–Kutta
  > stable' if V is of the form (551a) and the two matrices BA − XB
  > and BU − XV + VX are zero except for their first rows, where X
  > is some matrix.

* Lean statement captures: **same content** as cycle 131. The
  predicate `IsIRKStable` is unchanged this cycle; this theorem
  exhibits a second inhabitant `padded2DEulerGLM`. The `IsIRKStable`
  predicate (introduced cycle 131) encodes:
  - 551a: `∀ i : Fin r, M.V i 0 = if i = 0 then 1 else 0`
  - residual clauses: `∃ X, (∀ i ≠ 0, ∀ j, (B*A − X*B) i j = 0) ∧
    (∀ i ≠ 0, ∀ j, (B*U − X*V + V*X) i j = 0)`

  which directly transcribes the textbook clauses.
* Justification for divergence: **none — no divergence**. This is
  *strengthening evidence* of non-vacuity, not a definition change.
  The cycle 131 witness `explicitEulerGLM_isIRKStable` is preserved
  verbatim.
* Tautology check: conclusion `padded2DEulerGLM.IsIRKStable` is not
  a hypothesis (the theorem has no hypotheses).
* Identity check: the proof is not `exact h` — it is genuine
  entry-wise computation on a non-empty index. With `X = 0` the
  residual clauses still require concretely computing `(B*A) 1 0`
  and `(B*U) 1 j` for `j ∈ Fin 2` and verifying each equals zero;
  the `simp [padded2DEulerGLM]` closures unfold the matrix literals
  and reduce by `0 * x = 0` and the `Fin (succ 0) = Fin 2`
  enumeration.
* Hypothesis strength check: zero hypotheses — minimal.
* "Substantive vs vacuous" claim: **substantive**. Under `Fin 2`,
  the clauses `∀ i : Fin 2, i ≠ 0 → P i` apply concretely at
  `i = 1`. Contrast cycle 131's `Fin 1`, where `∀ i, i ≠ 0 → …`
  is vacuously closed by `absurd (Subsingleton.elim i 0) hi`. The
  proof here cannot reduce to such a vacuity argument because the
  index set is non-empty.

Method-class side conditions from the §551 `Context` block
(`p = q`, `s = r = p + 1`, `A` diagonally implicit, `λ ≥ 0`,
`ρ(V̇) = 0`) are *not* enforced on `padded2DEulerGLM`. Per the
cycle 131 docstring on `IsIRKStable`, those describe the family
of methods studied when IRK stability is discussed — they are not
part of the predicate. Including them inside the witness GLM
would be hypothesis smuggling on the witness side. (`padded2DEulerGLM`
trivially has `s = 1`, `r = 2`, so `s = r` fails — that is fine and
intentional: the predicate `IsIRKStable` does not require it.)

## Dead ends

None of substance. The first version of the proof passed
`simp [padded2DEulerGLM, Matrix.mul_apply, Fin.sum_univ_succ,
Fin.sum_univ_zero]`, but the unused-simp-arg linter reported all
three additional lemmas as unused — `simp [padded2DEulerGLM]` alone
suffices because the matrix-literal unfolders in
`Mathlib.Data.Matrix.Notation` already provide the entry-wise
reductions. No fallback to `decide`, `Fin.sum_univ_two`, or
separate `have` blocks (all listed in the strategy's "if harder
than expected" section) was needed.

## Discovery

* For witnesses on small `Fin r` matrices built from `!![…]`
  literals, `simp [<def_name>]` is typically enough to close
  entry-wise equalities — the matrix-notation simp lemmas already
  unfold both `Matrix.mul_apply` and the small-`Fin` summations.
  Manually listing `Matrix.mul_apply`, `Fin.sum_univ_succ`,
  `Fin.sum_univ_zero` produces redundant simp warnings.
* Pattern for "non-vacuous `i ≠ 0` clause on `Fin (succ n)`" with
  `n ≥ 1`: `intro i j hi; fin_cases i; · exact absurd rfl hi; ·
  fin_cases j; simp [<witness_def>]`. The first branch handles
  `i = 0` (where `hi : (0 : Fin _) ≠ 0` is `absurd rfl`); the
  later branches handle the genuinely-non-empty residue.
* The `IsIRKStable` predicate is `(... ∧ ∃ X, ...)`, so
  `refine ⟨?_, 0, ?_, ?_⟩` flattens directly to four obligations
  (first conjunct, `X` witness, then the two universally quantified
  residual clauses). No need for nested `refine ⟨_, ⟨X, _, _⟩⟩`.

## Suggested next approach

The cycle 132 → 133 chain has now closed the structural-vacuity gap
introduced by cycles 130 and 131 for `def:551A`. The next planning
step should choose between:

1. **Apply the same substantive-r=2-witness pattern to `def:542A`**
   (Runge–Kutta stability). Cycle 130's `explicitEulerGLM_isRKStable`
   uses `r = 1`; the `Φ(w, z) = w^{r-1} (w - R(z))` factorisation is
   non-trivial only for `r ≥ 2`. A `padded2DEulerGLM`-style witness
   with `r = 2` would similarly strengthen def:542A's non-vacuity
   from "true by `pow_zero`" to "true by genuine factorisation".
   The witness construction may share the same GLM (with stability
   matrix `M(z) = V + z B (I − zA)^{-1} U` computed at `s = 1, r = 2`
   reducing to a clean closed form).

2. **`thm:551B` *Single Non Zero Eigenvalue Stability*** —
   strategy's Priority 2. Cycle 133 did not attempt this since
   Priority 1 consumed the budget. The next planner should read
   `extraction/formalization_data/entities/thm_551B.json` first to
   classify whether it reduces to a short spectral argument on `V`
   alone (proceed) or requires §550 doubly-companion-matrix
   infrastructure (write a blocker issue).

3. **`thm:553A` *Derivation of methods with IRK stability*** —
   listed as a `def:551A` dependent in the entity record; now that
   `def:551A` has both vacuous and substantive witnesses, the
   prerequisite stack for `thm:553A` is in better shape, but it
   likely still requires §550 infrastructure.

Recommendation for the next planner: option 1 (def:542A substantive
r=2 witness) is the highest-leverage continuation of the current
arc. Option 2 is a clean classify-then-decide single cycle. Option 3
is multi-cycle and should wait on §550.
