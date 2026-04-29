# Cycle 012 Results

## Worked on
`thm:141A` — *Constant coefficients* (Butcher §141, p. 67),
formalized in a new file `OpenMath/Chapter1/Section141.lean` as

- `OpenMath.Chapter1.Section141.linRec` — scalar order-`k`
  constant-coefficient inhomogeneous recurrence (141a)
  `y_n = α_1 y_{n-1} + ⋯ + α_k y_{n-k} + ψ_n` (with `y_0, …, y_{k-1}`
  the given initial values).
- `OpenMath.Chapter1.Section141.theta` — canonical impulse response
  `θ` (the homogeneous solution with `θ_0 = 1`, `θ_m = 0` for
  `m < 0` modeled by guarded sum).
- `OpenMath.Chapter1.Section141.yPrime` — transformed initial data
  `y'` from (141b), defined recursively as
  `y'_m = y_m - Σ_{i<m} θ_{m-i} y'_i`.
- `OpenMath.Chapter1.Section141.linRec_closed_form` — Butcher §141A:
  `linRec n = (Σ_{i ∈ range (min k (n+1))} θ_{n-i} y'_i) + (Σ_{i ∈ Icc k n} θ_{n-i} ψ_i)`.

Plus helper / equation lemmas (linRec_of_lt, linRec_of_ge, theta_zero,
theta_succ, yPrime_of_lt, yPrime_of_ge, yPrime_recover,
theta_inner_sum, theta_recurrence_at) and four private case lemmas
used in the main proof: linRec_closed_form_lt (n < k), theta_k_zero_eq
(k = 0), linRec_closed_form_k_zero (k = 0), sum_swap_yprime,
sum_swap_psi.

## Approach
1. Read `entities/thm_141A.json` and `raw_text/ch01.txt` lines
   2200–2275 to pin the exact statement of (141a, 141b, 141c) and
   the upper-triangular θ-matrix definition of `y'`.

2. **Definitions.** Used well-founded recursion (`termination_by` +
   `decreasing_by omega` / `i.isLt`) for `linRec`, `theta`, `yPrime`.
   For `yPrime`, used `Fin m`-indexed inner sum so the
   well-founded-recursion check is direct (`i.isLt`).

3. **ℕ-vs-ℤ index decision.** Adopted strategy option (a):
   restrict the first sum to `range (min k (n+1))` instead of
   `range k`. This is mathematically equivalent to Butcher's
   `Σ_{i=0}^{k-1}` with the convention `θ_m = 0` for `m < 0` (any
   term with `i > n` would have `θ_{n-i} = 0` in Butcher), and
   avoids modeling `θ` as ℤ-indexed. Documented in the file
   docstring.

4. **Sub-lemma decomposition.** Split the main theorem into:
   - `linRec_closed_form_lt` (case `n < k`): direct from
     `linRec_of_lt` + `yPrime_recover` + empty `Icc k n`.
   - `linRec_closed_form_k_zero` (case `k = 0`): direct using
     `theta_k_zero_eq` (`θ 0 _ m = δ_{m,0}`).
   - For the inductive step (`k ≥ 1`, `n ≥ k`): apply IH for each
     `j : Fin k`, distribute `α j *` over the IH-expanded sums,
     and use two sum-swap helpers `sum_swap_yprime` and `sum_swap_psi`
     to collapse the double sums via `theta_recurrence_at`.

5. **Sum-swap helpers.** The key technical content was proving
   - `sum_swap_yprime`: For `0 < k ≤ n`,
     `Σ j : Fin k, α j * Σ_{i ∈ range (min k (n - j))} θ_{m_j-i} y'_i
        = Σ_{i ∈ range k} θ_{n-i} y'_i`
   - `sum_swap_psi`: For `0 < k ≤ n`,
     `Σ j : Fin k, α j * Σ_{i ∈ Icc k m_j} θ_{m_j-i} ψ_i
        = Σ_{i ∈ Icc k (n-1)} θ_{n-i} ψ_i`.
   Both proofs follow the same five-step pattern:
   (i) `Finset.mul_sum` to distribute α j;
   (ii) replace each variable inner range/Icc with a fixed (independent
        of j) larger set, conditional `if i + j.val < n then … else 0`,
        via `Finset.sum_filter`;
   (iii) `Finset.sum_comm` to swap the two sums;
   (iv) for each fixed i, factor out `y'_i`/`ψ_i` to the right via
        `Finset.sum_mul`;
   (v) match `theta_recurrence_at`'s form (rewriting the condition
        `i + j < n ↔ j + i < n` and the argument `n - 1 - j - i = n - 1 - i - j`)
        and rewrite to `θ_{n-i}`.

6. **The `theta_recurrence_at` helper.** A small lemma:
   `Σ j : Fin k, (if j.val + i < n then α j * θ_{n-1-i-j.val} else 0)
      = θ_{n-i}`
   for `i < n`. Proof: rewrite `n - i = (n - i - 1) + 1` (using
   `i < n` so `n - i ≥ 1`), apply `theta_succ` at `n - i`, and
   verify the two sums match term-by-term (the predicate
   `j ≤ n - i - 1` is equivalent to `j + i < n`).

7. **Top-level structure.** Final main proof uses
   `Nat.strong_induction_on` on `n`, peels off the `k = 0` case
   first (via `Nat.eq_zero_or_pos k`), then within `k ≥ 1`,
   case-splits on `n < k` vs `n ≥ k`. The `n ≥ k` branch:
   - Apply `linRec_of_ge` then IH on each `n - 1 - j.val < n`.
   - `simp_rw [hIH]` then `simp_rw [mul_add, Finset.sum_add_distrib]`
     to split into the y'-part and ψ-part.
   - Apply `sum_swap_yprime` and `sum_swap_psi`.
   - Use `Finset.sum_Icc_succ_top` to pop the top term `i = n` off
     the Icc sum (where `θ_{n-n} = θ_0 = 1`), giving the missing
     `ψ_n` to combine with the swap-helpers' output.
   - Close with `abel`.

## Result
**SUCCESS.**

- `lake env lean OpenMath/Chapter1/Section141.lean` compiles silently
  (no warnings, no errors).
- `lake build` succeeds (full project rebuild).
- `#print axioms OpenMath.Chapter1.Section141.linRec_closed_form`
  reports `[propext, Classical.choice, Quot.sound]` — no `sorryAx`,
  no custom axioms.

### Aristotle usage
Per CLAUDE.md's Aristotle-first protocol, four sub-lemmas were
batch-submitted to Aristotle while I proceeded with manual proofs:
1. `inner_sum_eq_theta` (project `cd3fad3f`) — completed by Aristotle
   in ~7 min, but I had already proven it manually as
   `theta_inner_sum`.
2. `theta_recurrence_at` (project `068f3d6b`) — completed in ~10 min,
   already proven manually.
3. `sum_swap_yprime` (project `b284de16`) — still IN_PROGRESS at the
   time of commit; I proved it manually first.
4. `sum_swap_psi` (project `a4d70275`) — still IN_PROGRESS at the
   time of commit; I proved it manually first.

The strategy explicitly bars submitting the full main theorem to
Aristotle ("the algebraic structure is non-trivial and Aristotle's
failure modes will not help iteration"), so jobs were narrowed to
sub-lemmas. None of the Aristotle outputs were needed in the final
file — the manual proofs landed first.

## Faithfulness check
For each new `def` / `theorem` introduced this cycle:

### `def linRec` (Butcher §141, equation 141a)
- Entity ID: `thm:141A`.
- Textbook recurrence (raw_text/ch01.txt:2208):
  > `y_n = α_1 y_{n-1} + α_2 y_{n-2} + · · · + α_k y_{n-k} + ψ_n`
- Lean recurrence (Section141.lean):
  > `linRec k α y₀init ψ n =
     if h : n < k then y₀init ⟨n, h⟩
     else (∑ j : Fin k, α j * linRec k α y₀init ψ (n - 1 - j.val)) + ψ n`
- Captures: **same content**. With `α : Fin k → R` carrying
  `α_1, …, α_k` (i.e., `α ⟨j, _⟩ = α_{j+1}`), the recurrence at
  `n ≥ k` reads
  `linRec n = α_1 · linRec(n-1) + α_2 · linRec(n-2) + ⋯ + α_k · linRec(n-k) + ψ_n`,
  matching (141a) verbatim.
- Definition smuggling check: `linRec` is the recurrence alone — no
  closed-form claim is built into the def.

### `def theta` (Butcher §141, canonical solution θ_m)
- Textbook (raw_text/ch01.txt:2218):
  > "Denote the solution to this problem at step m by `y_m = θ_m`,
     `m = 0, 1, 2, …, n`, with `θ_m = 0` for `m < 0`."
- Lean: `theta k α 0 = 1`, `theta k α (n+1) = ∑ j : Fin k,
   if j.val ≤ n then α j * theta k α (n - j.val) else 0`.
- Captures: **same content**. Initial conditions `θ_0 = 1`,
  `θ_{-1} = ⋯ = θ_{1-k} = 0` are encoded by:
  - `θ_0 = 1` directly.
  - For `m ≥ 1`: the textbook recurrence reads `θ_m = α_1 θ_{m-1} + ⋯ + α_k θ_{m-k}`.
    For `j ≥ m` (i.e., `m - j < 0`), Butcher's `θ_{m-1-j}` would be
    `0`. With ℕ-indexed `θ`, we'd get `θ_{m-1-j} = θ 0 = 1`, which
    would corrupt the recurrence. The guard `if j.val ≤ n` (i.e.,
    `j ≤ m - 1`) zeros out exactly those terms that should be `0`
    by the textbook convention.
- Definition smuggling check: `theta` is the recursive data, not a
  property — fine.

### `def yPrime` (Butcher §141, equation 141b)
- Textbook (raw_text/ch01.txt:2230, the upper-triangular matrix
  equation):
  > `(y'_{k-1}, …, y'_1, y'_0)ᵀ = T^{-1} · (y_{k-1}, …, y_1, y_0)ᵀ`,
  > where T is the upper-triangular matrix with 1's on the diagonal
  > and `θ_1, θ_2, …` above.
- Equivalent recursive form (the textbook's `T^{-1}` formula
  unfolded — Butcher gives the matrix, we use the recursion):
  > `y'_m = y_m - θ_1 y'_{m-1} - ⋯ - θ_m y'_0`,
  > i.e. `y'_m = y_m - Σ_{i=0}^{m-1} θ_{m-i} y'_i`.
- Lean: `yPrime k α y₀init m = y₀init ⟨m, h⟩ - Σ i : Fin m, θ_{m-i} · y'_i`.
- Captures: **same content**. The `Fin m` sum gives `i = 0, …, m-1`,
  matching the textbook's index range.
- The `yPrime_recover` lemma proves the textbook's "this is equal to
  `y_m`" claim from the proof of 141A:
  `y₀init ⟨m, h⟩ = Σ i ∈ range (m+1), θ_{m-i} · y'_i`.

### `theorem linRec_closed_form` (Butcher §141, theorem 141A)
- Textbook conclusion (entities/thm_141A.json → statement_latex):
  > `y_n = Σ_{i=0}^{k-1} θ_{n-i} y'_i + Σ_{i=k}^{n} θ_{n-i} ψ_i`
- Lean conclusion:
  > `linRec k α y₀init ψ n
     = (∑ i ∈ Finset.range (min k (n + 1)),
            theta k α (n - i) * yPrime k α y₀init i)
       + ∑ i ∈ Finset.Icc k n, theta k α (n - i) * ψ i`
- Captures: **same content** with the documented index-range
  adjustment. The first sum's range
  `range (min k (n + 1)) = {0, 1, …, min(k - 1, n)}`. For `n ≥ k - 1`
  (in particular for any `n ≥ k`), this equals `range k = {0, …, k - 1}`,
  matching Butcher exactly. For `n < k - 1`, the truncation
  `range (n + 1)` is mathematically equivalent (the dropped terms
  `i = n + 1, …, k - 1` would have `n - i < 0` and thus
  `θ_{n-i} = 0` in the textbook). The file docstring documents
  this divergence.
- **Tautology check**: PASS. The conclusion is an algebraic identity
  between `linRec` (defined as a recursion) and a sum-product
  expression built from `theta` and `yPrime`. None of the four
  arguments (`α`, `y₀init`, `ψ`, `n`) are propositions, so no
  hypothesis equals the conclusion.
- **Identity check**: PASS. The proof is a strong induction on `n`
  with non-trivial case work (k = 0 split, n < k vs n ≥ k split,
  IH application, two sum-swap manipulations, sum-Icc-top
  manipulation, abel). It is not `exact h_something`.
- **Hypothesis strength**: PASS. The signature has only the data
  `(k : ℕ) (α y₀init : Fin k → R) (ψ : ℕ → R) (n : ℕ)` and ambient
  typeclasses `[Ring R]`. No invertibility, no positivity, no
  upper-triangularity assumption on `α`. Matches Butcher's
  hypothesis-free statement.
- **Absent theorem check**: PASS. Every comment promising a
  sub-lemma names a declaration that exists in the file:
  `linRec_of_lt`, `linRec_of_ge`, `theta_zero`, `theta_succ`,
  `yPrime_of_lt`, `yPrime_of_ge`, `yPrime_recover`,
  `theta_inner_sum`, `theta_recurrence_at`, `linRec_closed_form_lt`,
  `theta_k_zero_eq`, `linRec_closed_form_k_zero`,
  `sum_swap_yprime`, `sum_swap_psi`.
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.

## Dead ends
1. **`rfl` for theta equation lemmas.** Initial draft used `rfl` for
   `theta_zero` and `theta_succ`, exploiting the structural
   recursion of `Section140.lean`. This failed because well-founded
   recursion (forced by `termination_by` for the strong-recursion
   pattern `n + 1 ↦ n - j.val`) makes the equation lemmas
   non-definitional. Fixed by using `rw [theta]` (which uses the
   compiler-generated `theta.eq_def`).

2. **`yPrime` decreasing_by with `range m`.** Initial draft used
   `∑ i ∈ Finset.range m, …` with `decreasing_by exact
   Finset.mem_range.mp ‹_›`, but the `‹_›` couldn't find the
   membership hypothesis (it picked up the natural-number value
   `m` instead). Fixed by switching to `∑ i : Fin m, …` so the
   bound is intrinsic and `decreasing_by exact i.isLt` works
   directly.

3. **`ring` failed on `α j * (θ * y') = α j * θ * y'`.** This is
   just left-associativity, but `ring` requires commutativity (we're
   in `[Ring R]`, not `[CommRing R]`). Fixed by `rw [← mul_assoc]`
   in the positive branch and `rw [zero_mul]` in the negative branch
   of the `split_ifs`. (Could also have used `noncomm_ring` but
   `mul_assoc` is more transparent.)

4. **`split_ifs with h1 h2` on equivalent conditions.** Tried this
   for the rewrite `i + j < n ↔ j + i < n`, but Lean produces
   different numbers of cases / hypothesis names depending on the
   internal logic. Replaced with the cleaner explicit `by_cases h:
   i + j < n` followed by two `if_pos`/`if_neg` rewrites — easier to
   reason about and more robust.

5. **`Fin.sum_univ_eq_sum_range` location.** The lemma lives in
   `Mathlib.Data.Fintype.BigOperators`, not in
   `Mathlib.Algebra.BigOperators.*`. Required adding the import.

6. **`Finset.Icc_eq_empty` for `n < k`.** Worked first try; one-liner
   `Finset.Icc_eq_empty (by omega)`.

7. **`abel` works in the final algebraic combination, not `ring`.**
   The closing step `(A + B) + (C + D) + ψ_n = A + (D + ψ_n + C) + B`
   is purely additive — `abel` (for AddCommMonoid) handles it
   without needing ring structure.

## Discovery
- **Well-founded recursion on `Nat.strongRecOn` style, encoded via
  `termination_by` / `decreasing_by`, works fine for the recurrences
  in §141.** No need to manually invoke `Nat.strongRecOn`. The key
  is to pass enough into `decreasing_by` (i.e., `Fin k`'s `isLt` for
  `j : Fin k`) so omega can close the well-founded measure goal.
- **`Finset.sum_filter` is the right tool for "extending" a
  variable-bound sum to a fixed-bound sum with a conditional.**
  This is much cleaner than manually splitting and re-pasting
  Finsets.
- **The k = 0 case is genuinely degenerate** (Fin 0 is empty,
  recurrence reduces to `linRec = ψ`), and it's cleaner to handle
  it via a separate top-level case rather than weaving it into the
  main strong-induction argument with auxiliary hypotheses on `0 < k`.
- **The `hkpos : 0 < k` hypothesis in `sum_swap_psi` is implicitly
  used by omega** (to derive `False` from `0 < 0` in the boundary
  case `k = 0, n = 0`, even though the lemma is only invoked with
  `0 < k` true). The Lean unused-variable linter doesn't trace
  through omega; renaming to `_hkpos` suppresses the warning.
- **Butcher's "add the contribution from each step" line in the
  proof** corresponds in Lean to the combination
  `sum_swap_psi (over i ∈ Icc k (n-1)) + ψ_n = secondSum_n`, where
  the missing `ψ_n` is exactly the `i = n` term that
  `Finset.sum_Icc_succ_top` exposes via `θ_{n-n} = θ_0 = 1`.

## Commit verification
- Local HEAD before commit: `b10e1dbb9777aef35a0c2ccca575ac2fdf914e98`
- Local HEAD after commit: TBD (filled in below)
- `origin/Main/Experiments` after push: TBD (filled in below)

## Suggested next approach
With `thm:141A` shipped, **Chapter 1 has 13 of 17 entities formalized**.
The four remaining unformalized Ch. 1 entities are
`thm:142C`, `thm:142D` (in_progress), `thm:142E`, `thm:142F` — all of
the §142 cluster — which remain Jordan-blocked per
`.prover-state/issues/jordan_canonical_form_missing.md`.

Cycle 013 should pivot to **Chapter 2**, starting with `thm:212A`
(Global truncation error of Euler's method). Per the planner's
note in cycle 012's strategy, this depends only on §110 (Lipschitz,
existence/uniqueness) which is shipped.

The infrastructure built this cycle (`linRec`, `theta`, `yPrime`,
the sum-swap helpers) is reusable for any future §141-style
constant-coefficient-recurrence work, e.g., when LMM stability
analysis (Ch. 4) needs the characteristic-polynomial reduction
of (141a).
