# Cycle 037 Results

## Worked on
`def:403A` — Dahlquist stability / zero-stability of linear multistep
methods. Appended to `OpenMath/Chapter4/Section404.lean` per the
strategy (§40 introductory file, no rename).

Three new declarations:
- `LinearMultistepMethod.IsHomogeneousSolution` — predicate capturing
  Butcher equation (403a), the homogeneous recurrence
  `y_{m+k} = α_1 y_{m+k-1} + ⋯ + α_k y_m`.
- `LinearMultistepMethod.IsStable` — Definition 403A: every
  homogeneous solution is bounded.
- Two non-vacuity witnesses: `explicitEulerLMM_isStable` and
  `implicitEulerLMM_isStable`.

## Approach
1. Read `entities/def_403A.json` to confirm the textbook statement and
   equation (403a).
2. Wrote sorry-first scaffold (definition + two witness theorems with
   `:= by sorry`). LSP confirmed compilation with only the two
   expected sorry warnings; lake env confirmed exit code 0.
3. Submitted three jobs to Aristotle:
   - explicit Euler stability
   - implicit Euler stability
   - bonus `const_sequence_isHomogeneousSolution` lemma
4. While Aristotle worked, executed the strategy's §4 proof recipe
   manually. The proof shape:
   ```
   intro y hy
   induction n with
   | zero => rfl
   | succ n ih => simp [explicitEulerLMM] at (hy n); linarith
   refine ⟨|y 0|, fun n => ?_⟩; rw [hconst n]
   ```
   compiled on first try for both witnesses. (The strategy explicitly
   said “use whichever finishes first” — manual finished, so Aristotle
   results were not needed. Submissions remain queued/running but
   were not polled per the CLAUDE.md "do not poll" rule.)
5. Verified via `lean_diagnostic_messages`: zero diagnostics on the
   final file. Verified via `lean_verify` that
   `explicitEulerLMM_isStable` uses only
   `[propext, Classical.choice, Quot.sound]`.
6. Updated `lean_status.json`, `plan.md` counter (36→37) and
   `def:403A` row, and wrote this result file.

## Result
SUCCESS — `def:403A` formalized end-to-end in a single cycle. Both
Euler witness theorems prove without `sorry`, no `axiom`/`constant`
introduced, no `maxHeartbeats` raised, no unused-simp-arg or other
warnings.

## Faithfulness check
For each new `def` or `theorem` introduced this cycle:

### `LinearMultistepMethod.IsHomogeneousSolution`
- Entity ID: not a textbook concept on its own — it's the predicate
  encoding equation (403a).
- Textbook equation (from `entities/def_403A.json`):
  > `y_n = α_1 y_{n-1} + α_2 y_{n-2} + ⋯ + α_k y_{n-k}`
- Lean statement: `∀ m, y (m + k) = ∑ i : Fin k, M.α i.succ * y (m + k - (i.val + 1))`.
  Hand-traced for `k = 2`: at `i.val = 0`, term = `M.α 1 * y (m + 2 - 1) = α_1 · y_{m+1}`;
  at `i.val = 1`, term = `M.α 2 * y (m + 2 - 2) = α_2 · y_m`.
  Sum = `α_1 · y_{m+1} + α_2 · y_m`, matching the textbook exactly.
- Captures: same content.

### `LinearMultistepMethod.IsStable` (Definition 403A)
- Entity ID: `def:403A`.
- Textbook statement (from `entities/def_403A.json`):
  > "A linear multistep method [α, β] is 'stable' if the difference
  > equation (403a) has only bounded solutions."
- Lean statement:
  `∀ y, M.IsHomogeneousSolution y → ∃ C, ∀ n, |y n| ≤ C`.
- Captures: same content. The definition is the textbook condition
  verbatim — boundedness of every (403a) solution. No algebraic
  characterisation (root condition, companion matrix, Schur) is used;
  those are theorems for later cycles.
- Smuggling check: PASS — `IsStable` is not defined as any algebraic
  characterisation.
- Tautology check: PASS — universal quantifier in body, no
  `IsHomogeneousSolution` hypothesis.
- No characteristic polynomial introduced.

### `explicitEulerLMM_isStable`
- Entity ID: helper witness (non-vacuity, no textbook entity).
- Statement: `explicitEulerLMM.IsStable`.
- Captures: zero-hypothesis non-vacuity witness for `IsStable` against
  the concrete `explicitEulerLMM` record (k=1, α=(-1,1)).
- Identity check: PASS — proof uses `intro / induction / simp /
  refine / rw`, not `:= h_<name>`, `:= id`, or `exact h_<name>`.
- Hypothesis-strength check: zero hypotheses, so vacuously OK.

### `implicitEulerLMM_isStable`
- Same shape as `explicitEulerLMM_isStable` against
  `implicitEulerLMM` (k=1, α=(-1,1), only β differs).
- Captures: zero-hypothesis non-vacuity witness for `IsStable`.
- Identity check: PASS — same `intro / induction / simp` shape.

### Pre-commit checks (all PASS)
- TAUTOLOGY: no theorem conclusion equals a hypothesis.
- IDENTITY: no `:= h_<name>` / `:= id` / `exact h_<name>` closer.
- DEFINITION SMUGGLING: `IsStable` is the textbook boundedness
  condition, not an algebraic characterisation.
- HYPOTHESIS STRENGTH: witnesses have no hypotheses; the definition
  has none beyond `M`.
- ABSENT THEOREM: every promised theorem is present and closed.
- AXIOMS: `explicitEulerLMM_isStable` uses
  `[propext, Classical.choice, Quot.sound]` only.

## Dead ends
None. The strategy's §4 proof recipe worked verbatim on first
compile. The only minor cleanup was that `simp` flagged
`LinearMultistepMethod.IsHomogeneousSolution` and `Fin.sum_univ_one`
as unused simp arguments after the LMM definition was unfolded; I
trimmed the `simp` invocation to just `simp [explicitEulerLMM]` /
`simp [implicitEulerLMM]`, which resolved the recurrence directly.

## Discovery
- `simp [explicitEulerLMM]` is enough to collapse the homogeneous
  recurrence at `k = 1` — it unfolds the LMM record and the `if i = 0`
  branches, normalises `m + 1 - 1 = m`, and rewrites the sum
  automatically. No need for `Fin.sum_univ_one` explicitly.
- The strategy's §4 fallback (manual `Fin.sum_univ_succ` rewriting)
  was unnecessary; the proof finished in well under the 30-line
  threshold (the `succ` branch is two lines after `have hrec := hy n`).
- LSP `lean_diagnostic_messages` is dramatically faster than
  `lake env lean` for sorry-first verification — used to confirm the
  scaffold compiled while the lake build was still running.

## Suggested next approach
The strategy's §10 preview is correct: cycle 038 should formalize
`def:402A` (convergent LMM). Building blocks needed:
1. **LMM step operator** — predicate or function capturing the
   implicit recurrence
   `Σ_i α_i y_{n-i} = h Σ_i β_i f(x_{n-i}, y_{n-i})`. The simplest
   first form is a predicate
   `LinearMultistepMethod.SatisfiesStep M h f y` with no explicit
   functional form (works for both explicit and implicit methods).
2. **Starting-method abstraction** — Butcher §402 says the first `k`
   values `y_0, …, y_{k-1}` are externally supplied. Encode as a
   field on a "convergent setup" structure or as a parameter
   `start : ℝ → ℝ → Fin k → ℝ` taking the IVP data `(x₀, y₀)` and
   step size, returning the prescribed starting values.
3. **Tendsto statement** — Butcher's convergence is `Y_m - y(x) → 0`
   as the step size → 0 with `m·h → x - x₀` fixed. The cleanest
   Lean shape is a `Filter.Tendsto`-style limit; needs IVP solution
   from §110 (already formalized) and a uniform-in-grid quantifier.
4. **First witness**: explicit Euler convergent on a Lipschitz IVP —
   this needs the Picard–Lindelöf bound (already in §111) plus a
   straightforward induction. Likely a substantial sub-cycle on its
   own; consider splitting `def:402A` (the predicate) and
   `explicitEulerLMM_isConvergent` (the witness) across two cycles.

A bonus infrastructural cycle that could unblock both §402 and §405
(power-bounded characterisation of stability): introduce the
characteristic polynomial `ρ(z) = -1 + Σ α_i z^{i}` (note α_0 = -1
contributes the leading coefficient if we follow Butcher's convention
exactly) and the companion-matrix encoding. Both are needed by the
`thm:441A` / `thm:441C` characterisation theorems and would let later
stability witnesses use polynomial-root arguments rather than direct
sequence induction. **But**: this is purely infrastructural and the
strategy explicitly forbade it for §403 — only do it once a §405 or
§441 theorem is the active target.

## Aristotle batch follow-up
Three jobs were submitted:
- `d9d3e278-74b8-48da-ba37-260620d8a394` (explicit Euler stable)
- `4d95322a-4e04-4982-8098-264d63354e56` (implicit Euler stable)
- `5b4a34ed-7418-4675-b9e0-df92b80ec641` (const sequence is
  homogeneous solution)

All three were not needed (manual proofs finished first), but their
results may be informative for future cycles. The const-sequence
lemma in particular is reusable infrastructure for §405 (it
characterises when constant sequences are valid solutions of the
homogeneous recurrence — an important sanity check for any
preconsistent method). If the cycle-038 worker has time, it could
incorporate Aristotle's solution to that bonus lemma directly into
`Section404.lean` next to the §403 content.
