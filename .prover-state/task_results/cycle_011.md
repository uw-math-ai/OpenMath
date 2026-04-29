# Cycle 011 Results

## Worked on
`thm:140A` — *Linear difference equations* (Butcher §140, p. 66),
formalized in a new file `OpenMath/Chapter1/Section140.lean` as

- `OpenMath.Chapter1.Section140.linDiffEqSolution` — recurrence (140a)
  `X_{k+1} = A_{k+1} • X_k + φ_{k+1}` with given `X_0`.
- `OpenMath.Chapter1.Section140.linDiffEqSolution_closed_form` — the
  closed-form solution
  `X_n = (A_n · ⋯ · A_1) • X_0 + Σ_{j=1}^n (A_n · ⋯ · A_{j+1}) • φ_j`.

Plus helper definition `transProd` (Butcher's right-to-left
transition product) and lemmas `transProd_zero`, `transProd_succ`,
`transProd_succ_of_le`, `transProd_self`, `transProd_of_lt`,
`linDiffEqSolution_zero`, `linDiffEqSolution_succ`.

## Approach
1. Read `entities/thm_140A.json` and `raw_text/ch01.txt` for §140 to
   pin down Butcher's product convention.
   The textbook explicitly defines
   `∏_{i=m}^n A_i = A_n A_{n-1} · · · A_{m+1} A_m`
   (right-to-left, non-commutative — see ch01.txt lines 2184–2188).
2. **Direction sanity check** by hand: from
   `X_2 = A_2 X_1 + φ_2 = A_2 (A_1 X_0 + φ_1) + φ_2
        = A_2 A_1 X_0 + A_2 φ_1 + φ_2`,
   confirmed the X₀ coefficient `A_n · ⋯ · A_1` is composed
   right-to-left and that this is **opposite** to Mathlib's default
   `Finset.prod` order (which would yield `A_1 · ⋯ · A_n`).
3. Defined our own `transProd A k n` recursive on the upper index, so
   the equation lemma `transProd_succ_of_le` gives the correct
   left-multiplication step
   `transProd A k (n+1) = A (n+1) * transProd A k n`
   needed by induction. Avoided `Finset.prod` over `Icc` entirely for
   the non-commutative product; used `Finset.sum_Icc_succ_top` for the
   commutative summation only.
4. Generic-module formulation `[Semiring R] [AddCommMonoid V] [Module R V]`
   per the strategy. Matrix-valued case is a corollary (deferred).
5. Proved the closed form by induction on `n`. Base case is `simp` on
   the recurrence and the empty `Icc 1 0`. Inductive step:
   - distribute `A (n+1) •` over the IH via `smul_add`, `Finset.smul_sum`,
   - rewrite each `A (n+1) • (transProd A k n • _)` to
     `transProd A k (n+1) • _` via `smul_smul` + `transProd_succ_of_le`,
   - split `Σ j ∈ Icc 1 (n+1), _` using `Finset.sum_Icc_succ_top`,
   - simplify the new top term with `transProd_self` (= 1) and
     `one_smul`,
   - finish with `abel`.

## Result
**SUCCESS.**

- `lake env lean OpenMath/Chapter1/Section140.lean` compiles silently
  (no warnings, no errors) on first clean run after fixing two import
  paths (`Mathlib.Algebra.BigOperators.Group.Finset.Basic` instead of
  `…Group.Finset`, and `…GroupWithZero.Action` for `Finset.smul_sum`).
- `lake build` succeeds (full project rebuild).
- `#print axioms OpenMath.Chapter1.Section140.linDiffEqSolution_closed_form`
  reports `[propext, Classical.choice, Quot.sound]` — no `sorryAx`,
  no custom axioms.

Aristotle was **not** used this cycle. The proof closed cleanly in the
first compile pass with only straightforward Mathlib lemmas, leaving
no `sorry`s to dispatch. The strategy explicitly bars submitting the
full theorem to Aristotle (the algebraic structure is non-trivial and
failure modes wouldn't help iteration); the suggested sub-lemmas
(empty product, product extension, sum split, etc.) were all closed
inline as one-liners (`rfl`, `simp`, `omega`-guarded `if_neg`),
making the batch step vacuous.

## Faithfulness check
For each new `def` / `theorem` introduced this cycle:

### `def linDiffEqSolution`
- Entity ID: `thm:140A`.
- Textbook recurrence (`entities/thm_140A.json` → equations[0]):
  > X_n = A_n X_{n-1} + φ_n   (140a)
- Lean recurrence (Section140.lean:103–105):
  > `linDiffEqSolution A φ X₀ (k+1) = A (k+1) • linDiffEqSolution A φ X₀ k + φ (k+1)`
- Captures: **same content**. With `n = k+1`, the Lean recurrence
  reads `X_n = A_n • X_{n-1} + φ_n`, matching (140a) verbatim.
- Definition smuggling check: `linDiffEqSolution` is the recurrence
  alone — no claim about uniqueness or closed form is built into the
  def. The closed-form claim is the separate `theorem linDiffEqSolution_closed_form`.

### `theorem linDiffEqSolution_closed_form`
- Entity ID: `thm:140A`.
- Textbook conclusion (`entities/thm_140A.json` → statement_latex,
  rendered):
  > y_n = (∏_{i=1}^n A_i) X_0 + (∏_{i=2}^n A_i) φ_1 + (∏_{i=3}^n A_i) φ_2 + ⋯ + A_n φ_{n-1} + φ_n
- Lean conclusion (Section140.lean:130–131):
  > `linDiffEqSolution A φ X₀ n = transProd A 0 n • X₀ + ∑ j ∈ Icc 1 n, transProd A j n • φ j`
- Captures: **same content**. Term-by-term:
  - `transProd A 0 n = A_n · ⋯ · A_1 = ∏_{i=1}^n A_i` (X₀ coefficient).
  - `transProd A 1 n = A_n · ⋯ · A_2 = ∏_{i=2}^n A_i` (φ₁ coefficient).
  - `transProd A j n = A_n · ⋯ · A_{j+1} = ∏_{i=j+1}^n A_i` (φⱼ coeff).
  - `transProd A (n-1) n = A_n` (φ_{n-1} coefficient).
  - `transProd A n n = 1` (φ_n coefficient — empty product, last term).
- **Tautology check**: PASS. The conclusion is an algebraic identity
  between the recurrence and a closed sum-product expression; no
  hypothesis equals the conclusion (there are no Prop hypotheses
  beyond the data).
- **Identity check**: PASS. Proof is `induction n with | zero => …
  | succ n ih => rw [...]; abel`, with five non-trivial rewrites in
  the `succ` case (`smul_add`, `Finset.smul_sum`, two
  `smul_smul`/`transProd_succ_of_le` rewrites, and `Finset.sum_Icc_succ_top`).
- **Hypothesis strength check**: PASS. Signature carries only the
  data (`A : ℕ → R`, `φ : ℕ → V`, `X₀ : V`, `n : ℕ`) and the
  ambient typeclasses (`Semiring R`, `AddCommMonoid V`, `Module R V`).
  No invertibility, boundedness, commutativity, or other constraints
  on `A` — matching Butcher's "no hypothesis" statement.
- **Direction check**: PASS. Verified by hand for n=2 (see Approach §2).
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.

### `def transProd` (helper)
- Not a Butcher entity; introduced as a Lean-side helper because
  Mathlib's `Finset.prod` orders factors left-to-right while Butcher's
  `∏` is right-to-left and would commute incorrectly under
  non-commutative multiplication.
- Documentation states the convention `transProd A k n = A_n · A_{n-1} · ⋯ · A_{k+1}`
  and the relation to Butcher's `∏_{i=m}^n A_i` via shift `k := m-1`.

## Dead ends
None this cycle. Two import-path mistakes were caught on the first
build attempt:

1. `Mathlib.Algebra.BigOperators.Group.Finset` — does not exist;
   the correct module is `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
   (the directory has been split since the strategy was drafted).
2. `Finset.smul_sum` lives in `Mathlib.Algebra.BigOperators.GroupWithZero.Action`,
   not in the generic `Group/Finset` tree.

Both fixed in <1 min; not worth a dead-end writeup.

The `norm_num` tactic was also tried in the base case but isn't
imported by the modules used here; replaced with a direct
`Nat.zero_lt_one` and ultimately removed entirely (since `simp` with
`linDiffEqSolution, transProd` already closes the base case).

## Discovery
- **`Module R V` works for non-commutative `Semiring R`.** Mathlib's
  `class Module (R : Type*) (M : Type*) [Semiring R] [AddCommMonoid M]
  extends DistribMulAction R M`. The `extends DistribMulAction` does
  not require `R` commutative, and `mul_smul` `(a * b) • x = a • (b • x)`
  holds for the left-action even when multiplication does not commute.
  This is the cleanest setting for matrix recurrences without picking
  a concrete `Matrix m m S` instance.
- **Butcher's right-to-left product is opposite to Mathlib's default
  `Finset.prod` order.** Anyone reusing `transProd` for §141A
  (constant coefficients) should keep this in mind: the constant case
  `A_i ≡ A` makes the order irrelevant (yielding `A^n`), so
  `Finset.prod` could be used there — but if extended back to §140-style
  variable coefficients, the right-to-left order is essential.
- **`Finset.sum_Icc_succ_top` requires `a ≤ b + 1` (always true here)**;
  this is the lemma name for the commutative side of the induction
  step, not the (separate) `prod_Icc_succ_top`.
- **`abel` works fine for the final `V`-valued combination** — it
  doesn't need ring structure, only `AddCommMonoid V`.

## Commit verification (per cycle 010 lesson)
- Local HEAD: `6d126274aa9bc559e7f47f3e16e8d0b2123ee548`
- `origin/Main/Experiments`: `6d126274aa9bc559e7f47f3e16e8d0b2123ee548`
- `git diff --stat HEAD~1 HEAD`: 4 files changed, 335 insertions(+), 3 deletions(-)
  — non-empty, cycle landed.

## Suggested next approach
Cycle 012 should target **`thm:141A`** (Constant coefficients, §141).
With `thm:140A` shipped:

- Specialize `linDiffEqSolution` to `A_n ≡ A_const` and prove
  `transProd A_const 0 n = A_const ^ n` (using
  `Mathlib.Algebra.GroupPower.Basic`).
- The closed form becomes
  `X_n = A^n • X_0 + Σ_{j=1}^n A^{n-j} • φ_j`.
- Mathlib's `Matrix.Pow` and `pow_succ` should let the reduction be
  ~10 lines.
- The §141 textbook proof additionally connects this to characteristic
  polynomial roots (the `λ_1, …, λ_k` discussion); that connection
  may be a separate corollary entity worth adding to the
  `extensions/helper_entities.json` file rather than crammed into one
  theorem.

Beyond §141, the next chunk of §142 entities (`thm:142C/D/E/F`) remain
Jordan-blocked per the open issue
`.prover-state/issues/jordan_canonical_form_missing.md`. Cycle 012
should not touch them.
