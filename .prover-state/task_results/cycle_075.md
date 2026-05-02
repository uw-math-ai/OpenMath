# Cycle 075 Results

## Worked on

* **Priority 0**: Closed `thm_410B` — Butcher's §410 order
  condition theorem in generating-function form
  (`Section410.lean:436`).
* **Priority 1 (infrastructure)**:
  - `genFn` abbreviation packaging `α(exp(-z)) - z β(exp(-z))`
    (`Section410.lean:281`); refactored `thm_410A` and
    `thm_410A_zero` to use it.
  - `LinearMultistepMethod.HasOrderAtLeast` predicate
    `∀ j ≤ p, C M j = 0` (declared under
    `OpenMath.Chapter4.Section404` namespace so dot notation
    works on LMM, since LMM lives in §404).
* **Priority 2 (bridge)**:
  - `C_one_eq_zero_iff_isConsistent_aux`: `C M 1 = 0 ↔ M.SatisfiesEq404b`
    (the algebraic core).
  - `C_one_eq_zero_iff_isConsistent`: full §410↔§404 bridge under
    preconsistency.
* **Priority 3 (witnesses)**:
  - `explicitEulerLMM_hasOrderAtLeast_zero` — explicit Euler has
    order ≥ 0 (preconsistency).
  - `explicitEulerLMM_hasOrderAtLeast_one` — explicit Euler has
    order ≥ 1 (consistency, via the bridge).
  - `explicitEulerLMM_C_two_ne_zero` — explicit Euler does NOT
    have order ≥ 2; restrictiveness check (textbook says
    explicit Euler is exactly first-order).
* **Artefacts updated**:
  - `lean_status.json::thm:410B` → `formalized`.
  - `plan.md::thm:410B` from `[ ]` to `[x]`; progress
    `44 → 45 of 175`.

## Approach

Followed the cycle 075 strategy step by step:

1. Loaded formalization data for `thm:410B` (`thm_410B.json`).
2. Read existing Section410.lean (`thm_410A`, `genFn`-style
   open-coded subtraction).
3. Drafted skeleton with sorries for the bridge and the
   `C 2 ≠ 0` numerical check; rest of cycle's deliverables
   (definition, `thm_410B`, two witnesses) closed manually.
4. Submitted the bridge + `C 2 ≠ 0` to Aristotle as a
   self-contained file (`c_one_bridge.lean`); project
   `b40cf1e8-4c19-4b67-b387-dd6eceb94380` returned in ~42 min.
5. Closed the manual proofs (bridge with explicit
   `Finset.sum_neg_distrib + ring + linarith`; `thm_410B` via
   double `rw [thm_410A]`).
6. After Aristotle returned, replaced the bridge with
   Aristotle's cleaner one-liner
   `simp [C, ...]; constructor <;> norm_num [...] at * <;> linarith`.
7. Verified file compiles, axiom set is `[propext, Classical.choice, Quot.sound]`.

### Namespacing trick

`LinearMultistepMethod` lives in
`OpenMath.Chapter4.Section404`, so dot notation
`M.HasOrderAtLeast` looks for
`OpenMath.Chapter4.Section404.LinearMultistepMethod.HasOrderAtLeast`.
The strategy's plan put `HasOrderAtLeast` under §410's
namespace, which doesn't satisfy dot notation. Fixed by
ending the §410 namespace block, opening §404 just for the
def, then re-entering §410 — keeps Section404.lean
untouched (per the strategy "don't touch Section404") while
keeping dot notation.

### Bridge proof

After several iterations, Aristotle's cleaner version was
adopted (the explicit `Finset.sum_neg_distrib + ring`
rewriting works but is verbose):

```lean
simp [C, LinearMultistepMethod.SatisfiesEq404b]
constructor <;> intro h <;>
  norm_num [Finset.sum_add_distrib, add_mul, mul_add, mul_assoc,
    mul_comm, mul_left_comm] at * <;>
  linarith
```

The kitchen-sink `norm_num [...]` rearranges
`M.α x.succ * (-1 + -↑↑x)` into `-(↑↑x + 1) * M.α x.succ`,
matching `SatisfiesEq404b`'s normal form, after which
`linarith` closes both directions.

### `thm_410B` proof

Trivial after `genFn`/`thm_410A`:

```lean
unfold LinearMultistepMethod.HasOrderAtLeast
refine ⟨fun h j hj => ?_, fun h j hj => ?_⟩
· rw [thm_410A]; exact h j hj
· rw [← thm_410A]; exact h j hj
```

This is **not** a tautology — `thm_410A` (cycle 074) is the
substantive identity `coeff j (genFn M) = C M j`; `thm_410B`
just re-packages it under the `∀ j ≤ p, ... = 0` quantifier.

## Result

**SUCCESS.** All five deliverables from the strategy
(D1 `HasOrderAtLeast`, D2 `genFn`, D3 bridge, D4 `thm_410B`,
D5 three witnesses) landed. Section410.lean compiles cleanly
with 0 sorries and standard axioms only.

`#print axioms thm_410B` →
`[propext, Classical.choice, Quot.sound]`. Same for the bridge
and all witnesses.

Net diff: ~+170 LOC, +6 theorems, +1 def, +1 abbreviation.
Progress counter: 44 → 45 / 175.

## Faithfulness check

### `LinearMultistepMethod.HasOrderAtLeast` (def)

Entity: textbook §410, p. 330 (Butcher):

> "this will enable us to expand (410a) in a Taylor series
>   `C₀ y(xn) + C₁ h y'(xn) + … + Cp h^p y^(p)(xn) + …`
>   (410b) and **order p will mean that C₀ = C₁ = … = Cp = 0**."

Lean statement: `∀ j ≤ p, C M j = 0`. Captures: **same
content**. The textbook sentence is the definitional one.
The asymptotic interpretation `L(y, x, h) = O(h^{p+1})` is
captured implicitly via Butcher's Taylor expansion (410b);
for `p = 1` we already have it quantitatively as `lem:406B`
(§404 — `localTruncationError_bound`). The
`O(z^{p+1})`-style generating-function characterization is
`thm_410B`.

### `thm_410B` (theorem)

Entity `thm:410B`, Butcher p. 351:

> "A linear multistep method `[α, β]` has order `p` (or
> higher) if and only if `α(exp(z)) + zβ(exp(z)) = O(z^{p+1})`."

Lean statement:
`M.HasOrderAtLeast p ↔ ∀ j ≤ p, coeff j (genFn M) = 0`,
with `genFn M = α(exp(-z)) - z β(exp(-z))` (backward sign).

Captures: **same content** modulo two encoding choices.

1. **Sign convention.** Butcher writes
   `α(exp(z)) + z β(exp(z))` (forward); we use
   `α(exp(-z)) - z β(exp(-z))` (backward). The two are
   equivalent under `z ↦ -z`. The backward convention
   matches def:406A and all of §404, §405, §406, §410A.
   Documented in `genFn`'s and `thm_410B`'s docstrings.
   A literal forward-sign variant is deferred to thm:410C
   (which is "this result restated in (ρ, σ) notation" per
   Butcher's text immediately after 410B).
2. **`O(z^{p+1})` for formal power series.** Butcher uses
   asymptotic `O`-notation; for formal power series (no
   topology) this is operationally
   `∀ j ≤ p, coeff j = 0`. Mathlib lacks a `Filter.IsBigO`
   over PowerSeries at the generality we'd want; the
   per-coefficient form is the standard formalization.

### `genFn` (abbreviation, not a named-concept def)

Pure naming convenience for
`α(exp(-z)) - z β(exp(-z))` — directly Butcher's (410c)
LHS with our backward-sign convention. No
faithfulness concern.

### `C_one_eq_zero_iff_isConsistent_aux` and the full bridge

Not a textbook entity — bridges §410 (`C M 1 = 0`) to §404
((404b)). Provable algebraic identity; not a definition.
Tautology check: PASS — the conclusion is iff between two
syntactically distinct conditions.

### Witnesses

`explicitEulerLMM_hasOrderAtLeast_zero/one`,
`explicitEulerLMM_C_two_ne_zero`: non-vacuity / restrictiveness
witnesses. Match Butcher's first-order classification of
explicit Euler. No faithfulness concern.

### Tautology and identity checks

- **`thm_410B`** conclusion `M.HasOrderAtLeast p ↔ ∀ j ≤ p, coeff j (genFn M) = 0`
  vs hypothesis: no hypothesis matches. PASS.
  Identity check: proof is two `rw [thm_410A]` calls — `thm_410A`
  is the substantive identity (`coeff j (genFn M) = C M j`),
  so this is **not** a vacuous re-export. PASS.
- **`HasOrderAtLeast`** is a definition, not a theorem. No
  smuggling: the predicate IS the textbook definition (Butcher
  uses `C₀ = C₁ = ⋯ = Cp = 0` definitionally).
- **`C_one_eq_zero_iff_isConsistent`** uses
  `M.IsPreconsistent` as a hypothesis. The textbook makes
  `C 1 = 0` part of the consistency conditions, with
  preconsistency separate. Hypothesis matches Butcher. PASS.

### Hypothesis strength check

Butcher's thm:410B takes only an LMM. Our version is
parameterized only by `M : LinearMultistepMethod k` and
`p : ℕ`. PASS.

## Dead ends

* **First bridge attempt** used a manual
  `Finset.sum_neg_distrib + ring + linarith` rewrite chain
  (the cast-bridge memo `feedback_satisfieseq404b_cast.md`
  pattern). It worked, but Aristotle's
  `simp [C, ...]; norm_num [...] at * <;> linarith`
  is shorter, so I substituted Aristotle's version.
  Both are equivalent.
* **`HasOrderAtLeast` namespace mistake**: first attempt put
  the def under `OpenMath.Chapter4.Section410.LinearMultistepMethod.HasOrderAtLeast`,
  which broke dot notation (the type `LinearMultistepMethod`
  lives in `Section404`). Fix: declare under §404 namespace,
  re-enter §410. Documented in the file.
* **`(0 + 1)` exponent / factorial issue**: `simp only [pow_one, ...]`
  did not fire because `(0+1)` isn't *literally* `1` in the
  matched term. Fix: use `simp [Nat.factorial]` (or
  Aristotle's `simp [C, ...]`), which definitionally
  reduces both.

## Discovery

* **Cross-namespace dot notation**: when adding a predicate
  for a type defined in another file/namespace, declare the
  predicate inside the type's namespace via a temporary
  `end ... namespace ...` switch; this preserves dot notation
  without modifying the type's source file. Pattern:
  ```lean
  end MyNamespace
  namespace TypeNamespace
  def MyType.MyPredicate ...
  end TypeNamespace
  namespace MyNamespace
  open TypeNamespace
  ```
  Section410.lean now uses this pattern at lines 394–419.
* **Aristotle as a tactic-improver**: even when the user
  has a working manual proof, submitting the same lemma to
  Aristotle can return a shorter alternative. Worth
  considering for files with many similar algebraic finishers.
* **`thm_410A` payoff**: the cycle 074 generating-function
  identity (`coeff j (genFn M) = C M j`) was already
  substantive on its own; cycle 075's `thm_410B` is now
  proved in ~5 lines because the heavy lifting is upstream.
  Designing infrastructure as `coeff j (...) = ...` rather
  than predicate-form lets downstream packaging be trivial.

## Suggested next approach

* **Highest yield**: `thm:410D` (the order-`p` characterization
  via factorial conditions on α, β-coefficients —
  `Σᵢ i^j α_i = j Σᵢ i^{j-1} β_i` for `j = 1, …, p`). With
  thm:410B closed and `C M j` in closed form, thm:410D is
  another packaging cycle: state the factorial-condition
  predicate, prove it equivalent to `C M j = 0` for `1 ≤ j ≤ p`,
  combine with thm:410B. ~1 cycle.
* **Alternative**: `thm:410C` — restate thm:410B in `(ρ, σ)`
  notation (forward-sign convention). Adds a sign-conjugation
  bridge `genFn_forward` ↔ `genFn` and re-derives
  `thm_410B_forward`. ~1 cycle, mostly bookkeeping.
* **Heavier targets**: `thm:431A` (Schur stability for LMMs)
  needs Schur root-location infrastructure for polynomials;
  `thm:422A` (LMM as a one-step method on ℝ^k) needs
  vector-valued one-step infrastructure. Both are 2+ cycle
  efforts.

The natural next pick is `thm:410D` — it closes the §410
order-condition cluster with the textbook's Adams-style
factorial criterion, and the infrastructure is now in place.
