# Cycle 036 Results

## Worked on

- New `def`: `LinearMultistepMethod.SatisfiesEq404b` (Butcher equation
  (404b)).
- New `def`: `LinearMultistepMethod.IsConsistent` (Butcher Definition
  404B — preconsistency ∧ (404b)).
- Four new witness theorems exercising both predicates against
  `explicitEulerLMM` and `implicitEulerLMM`:
    - `explicitEulerLMM_satisfiesEq404b`
    - `explicitEulerLMM_isConsistent`
    - `implicitEulerLMM_satisfiesEq404b`
    - `implicitEulerLMM_isConsistent`

All added to `OpenMath/Chapter4/Section404.lean` (extending the
cycle-035 file rather than creating a new one — `def:404B` shares the
chapter §404 introduction with `def:404A`).

## Approach

Followed the cycle-036 strategy verbatim. Verified the cycle-035
deliverable is on the branch (commit `d3bb122`) before doing anything
else, confirming the supervisor's `score=0` verdict from cycle 035 is
a phantom and the prior work is real and committed (587 insertions
across 9 files, including 101 lines of `Section404.lean`).

For the Lean encoding of (404b):

  ∑ i : Fin k, ((i : ℕ) + 1 : ℝ) · M.α i.succ  =  ∑ i, M.β i

— `(i+1)` is the textbook subscript on α, `i.succ : Fin (k+1)` skips
the `α 0` slot. β indexing already starts at 0 so the right-hand sum
ranges over all of `Fin (k+1)`. Hand-verified for k=2:
`(0+1)·α₁ + (1+1)·α₂ = α₁ + 2α₂`.

`IsConsistent` is the conjunction `IsPreconsistent ∧ SatisfiesEq404b`
— this is a verbatim encoding of the textbook line "a linear
multistep method satisfying (404a) **and** (404b) is said to be
consistent". Reused `IsPreconsistent` rather than inlining (404a) so
downstream consumers can extract the preconsistency component
cleanly.

All four witness proofs close by single-tactic `simp` with the
predicate definition and the Euler witness unfolded — the same shape
as the cycle-035 preconsistency witnesses.

## Result

SUCCESS. `lake env lean OpenMath/Chapter4/Section404.lean` exits
clean (no warnings, no errors). The four new theorems compile and
the existing cycle-035 content is unaffected.

Per the strategy, Aristotle was **not** used this cycle: the four
new proofs are five-character `simp` closures, so a 30-minute
round-trip would dwarf the proof cost by orders of magnitude.

## Faithfulness check

### `def: LinearMultistepMethod.SatisfiesEq404b` (helper-style predicate for equation (404b))

- Entity ID: `def:404B`, equation tag `404b` from the entity JSON
  `equations` block.
- Textbook statement (quoted from `equations[1].content`):
  > α_1 + 2α_2 + ... + kα_k = β_0 + β_1 + ... + β_k
- Lean statement captures: same content. The α-sum runs over
  `Fin k` with coefficient `((i : ℕ) + 1)` selecting `M.α i.succ`
  (so `i = 0` corresponds to the textbook's `α_1` term with
  coefficient `1`, `i = 1` corresponds to `α_2` with coefficient
  `2`, etc.). The β-sum runs over all of `Fin (k+1)` exactly
  matching `β_0 + β_1 + ... + β_k`.
- Naming note: this predicate is *not* a named textbook concept; it
  is the equation underlying Definition 404B. The docstring labels
  it as such ("the equation `α₁ + 2α₂ + … + kα_k = β₀ + β₁ + … + β_k`")
  rather than treating it as a concept on its own.

### `def: LinearMultistepMethod.IsConsistent` (Definition 404B)

- Entity ID: `def:404B`.
- Textbook statement (quoted from `statement_text`):
  > A linear multistep method satisfying (404a) and (404b) is said
  > to be 'consistent'.
- Lean statement captures: same content. Encoded as
  `M.IsPreconsistent ∧ M.SatisfiesEq404b`, which is the textbook's
  conjunction verbatim.
- Definition smuggling check: `IsConsistent` is the conjunction of
  the two algebraic conditions (404a) and (404b) — these *are* the
  textbook's defining conditions, not a characterisation theorem
  masquerading as a definition. The textbook itself defines
  consistency as "satisfying (404a) and (404b)", so this Lean def
  is the textbook def transcribed.

### Witness theorems (`explicitEulerLMM_satisfiesEq404b`, `explicitEulerLMM_isConsistent`, `implicitEulerLMM_satisfiesEq404b`, `implicitEulerLMM_isConsistent`)

- These are non-vacuity witnesses; they have no hypotheses and
  prove a concrete `IsConsistent` / `SatisfiesEq404b` instance for
  a specific Euler `LinearMultistepMethod` record.
- Tautology check: each conclusion mentions a concrete LMM record
  (not a universally-quantified `M`), so there is no shared
  hypothesis-conclusion structure. Not a tautology.
- Identity check: the two `IsConsistent` witnesses use `⟨_, _⟩`
  constructors over already-proved component lemmas
  (`*_isPreconsistent` and `*_satisfiesEq404b`); they are *not*
  `:= h_xxx` or `:= id` closers. The two `SatisfiesEq404b`
  witnesses use `simp` with the predicate definition and Euler
  record unfolded — genuine proof work normalising the `Fin`
  sums.
- Hypothesis strength: zero hypotheses. Cannot be weakened.

## Dead ends

None. Bare `simp` closed each `SatisfiesEq404b` witness on the
first try — same as the cycle-035 `IsPreconsistent` witnesses.

## Discovery

The single-step `Fin` sum normalisation by `simp` is robust enough
to handle both the (404a) sum (length-`k` over `Fin k`) and the
(404b) sums (length-`k` weighted α-sum + length-`(k+1)` β-sum) for
the k=1 Euler witnesses without any explicit `Fin.sum_univ_*`
lemmas. The strategy's contingency for adding those lemmas
explicitly was not needed.

The chapter scaffolding from cycle 035 (chapter aggregator
`OpenMath/Chapter4.lean`, root re-export in `OpenMath.lean`) means
adding more entities to `Section404.lean` requires zero
infrastructure changes — only the file itself plus the
`lean_status.json` and `plan.md` bookkeeping.

## Suggested next approach

Per the planner's cycle-037 preview, the cheapest next §40-§41
target is `def:403A` (Dahlquist stability), which introduces the
characteristic polynomial `ρ(z) := ∑ α_i z^{k-i}`. It is pure
algebra, builds on the existing `LinearMultistepMethod` record, and
its infrastructure (the ρ polynomial) is reused throughout §43.

After `def:403A`, `def:402A` (convergent LMM) is the right next
target — it requires the LMM recurrence operator
(`LinearMultistepMethod.step` or similar) which will then be reused
by `def:406A` (LTE).

`def:404B` unblocks `def:406A`, `lem:406B`, `lem:441A`,
`thm:243A`, `thm:405C`, `thm:406D`, and `thm:410B` per the entity
JSON `dependents` field. The next planner can pick whichever has
the most-ready supporting infrastructure.
