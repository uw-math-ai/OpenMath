# Cycle 037 strategy — formalize `def:403A` (Dahlquist stability / zero-stability)

## 0. Cycle 036 status: real success, do not redo

Cycle 036 successfully formalized `def:404B` (consistent LMM) with
four witness theorems. Commit hash `16b74c7`. Verify with:

```
git log -1 --format='%H %s'
```

Expected output: `16b74c7 Formalize def:404B — consistent linear multistep methods`.
The branch tip is current; nothing about §404 needs revisiting.

## 1. Top-line directive

**Pick exactly one entity this cycle: `def:403A`.** Extend the
existing `OpenMath/Chapter4/Section404.lean` file — do **not** create
a new `Section403.lean`. The §403 content sits naturally alongside
§404 in the same Chapter-4 introductory cluster, and reusing the file
avoids adding another import-graph entry for a single definition. Add
a new section comment `## §403 — Stability (def:403A)` inside the
existing namespace; everything else stays in
`OpenMath.Chapter4.Section404`.

> The **file** is named `Section404.lean` for cycle-035/036 reasons,
> but the contents already span §404. We will treat it as the §40
> introductory file. Do **not** rename the file; do **not** rename the
> namespace. Just append §403 content at the bottom.

If at the end of the cycle you have spare time, do **only**
housekeeping (update `lean_status.json`, update `plan.md` to bump the
progress counter and tick the `def:403A` row). Do **not** start
`def:402A` — it needs the LMM step operator and is a separate cycle.

---

## 2. What `def:403A` says (textbook, quoted verbatim)

From `extraction/formalization_data/entities/def_403A.json`:

> A linear multistep method [α, β] is 'stable' if the difference
> equation (403a) has only bounded solutions.

with the section-context equation

> (403a)  `y_n = α_1 y_{n-1} + α_2 y_{n-2} + ⋯ + α_k y_{n-k}`

and the textbook's note that "stability" here is also called
**zero-stability** or **stability in the sense of Dahlquist**.

The dependency hooks are `def:142A` (power-boundedness, formalized in
`OpenMath/Chapter1/Section142.lean`) and `thm:140A` (linear
difference equations, also formalized). You do **not** need to invoke
either — they are conceptual hooks for downstream characterisation
theorems (`thm:405A/B/C`, `thm:441A/C`), not for this definition.

---

## 3. Required Lean deliverables

Add to `OpenMath/Chapter4/Section404.lean`, inside the existing
`namespace OpenMath.Chapter4.Section404`, **after** the §404 content:

### (a) The homogeneous-recurrence predicate

```lean
/-- Butcher (403a): a sequence `y : ℕ → ℝ` is a *solution of the
homogeneous recurrence* of the linear multistep method `M` if for
every `m : ℕ`,

  `y (m + k) = α_1 · y_{m+k-1} + α_2 · y_{m+k-2} + ⋯ + α_k · y_m`.

This is equation (403a) — the difference equation that arises when
the method is applied to the trivial IVP `f ≡ 0`. The sum is indexed
by `i : Fin k`, with `i.succ : Fin (k+1)` selecting `α_{i.val + 1}`
and offset `i.val + 1` running from 1 to k. -/
def LinearMultistepMethod.IsHomogeneousSolution {k : ℕ}
    (M : LinearMultistepMethod k) (y : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, y (m + k) = ∑ i : Fin k, M.α i.succ * y (m + k - (i.val + 1))
```

### (b) The stability predicate (Definition 403A)

```lean
/-- Butcher Definition 403A: a linear multistep method is *stable*
(also called *zero-stable* or *Dahlquist-stable*) if every solution
of the homogeneous recurrence (403a) is bounded.

Boundedness is encoded as `∃ C, ∀ n, |y n| ≤ C`. -/
def LinearMultistepMethod.IsStable {k : ℕ}
    (M : LinearMultistepMethod k) : Prop :=
  ∀ y : ℕ → ℝ, M.IsHomogeneousSolution y → ∃ C, ∀ n, |y n| ≤ C
```

### (c) Two witness theorems

`explicitEulerLMM` and `implicitEulerLMM` (already defined in this
file) both have `k = 1`, `α 1 = 1`, so the homogeneous recurrence
collapses to `y (m + 1) = y m`, i.e. solutions are constant
sequences, trivially bounded by `|y 0|`.

```lean
theorem explicitEulerLMM_isStable : explicitEulerLMM.IsStable := by
  sorry
theorem implicitEulerLMM_isStable : implicitEulerLMM.IsStable := by
  sorry
```

Both proofs follow the same shape (see §4 below).

---

## 4. Proof recipe (apply identically to both witnesses)

For each Euler witness:

```lean
  intro y hy
  have hconst : ∀ n, y n = y 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        have hrec := hy n
        -- hrec : y (n + 1) = ∑ i : Fin 1, α i.succ * y (n + 1 - (i.val + 1))
        simp [LinearMultistepMethod.IsHomogeneousSolution,
              explicitEulerLMM,    -- or implicitEulerLMM
              Fin.sum_univ_one] at hrec
        -- After simp, hrec should read `y (n + 1) = y n` (or
        -- `y (n + 1) = 1 * y n`). Combine with ih.
        linarith
  refine ⟨|y 0|, fun n => ?_⟩
  rw [hconst n]
```

### Robustness fallbacks

* If `Fin.sum_univ_one` doesn't immediately collapse the sum, try
  `Fin.sum_univ_succ` or `Finset.sum_singleton`. Use
  `lean_multi_attempt` at that step — do **not** burn cycle time on
  manual sum-rewriting.
* If `m + 1 - (0 + 1) = m` doesn't normalize, add
  `Nat.add_sub_cancel` or unfold the subtraction by hand:
  `show y (n + 1) = M.α (Fin.succ 0) * y (n + 1 - 1)` and reduce.
* If `linarith` doesn't close the final step, replace with
  `rw [hrec, ih]` (after simplifying the `* 1` and the
  index-arithmetic).

The proof is short (≤ 15 lines) — if it stretches longer than 30
lines, stop and re-read the `IsHomogeneousSolution` definition: you
may have a mismatch in the `i.val + 1` offset.

---

## 5. Sorry-first checkpoint (CLAUDE.md absolute rule)

Before any closing tactic, write the full file (definition + two
witnesses, all closed with `sorry`) and run

```
lake env lean OpenMath/Chapter4/Section404.lean
```

It must compile cleanly. **Only then** start closing the two
sorries.

---

## 6. Aristotle batch — submit immediately after sorry-first compiles

Submit **all three** items below to Aristotle as separate jobs the
moment the sorry-first file compiles:

1. `explicitEulerLMM_isStable` — full theorem statement and sorry'd
   proof skeleton.
2. `implicitEulerLMM_isStable` — same shape; Aristotle may even
   solve it in one shot.
3. A bonus sub-lemma:
   ```lean
   theorem const_sequence_isHomogeneousSolution
       (c : ℝ) {k : ℕ} (M : LinearMultistepMethod k)
       (hM : M.IsPreconsistent) :
       M.IsHomogeneousSolution (fun _ => c) := by sorry
   ```
   This says "constant sequences solve the homogeneous recurrence
   iff the method is preconsistent" (use `hM` to discharge
   `1 = ∑ α_{i+1}` after pulling `c` out of the sum). It is bonus
   infrastructure — not required for the cycle to succeed.

After submitting, **sleep 30 minutes** (CLAUDE.md rule). While
Aristotle works, do the manual proof of `explicitEulerLMM_isStable`
using §4 above. If your manual proof finishes first, keep it; if
Aristotle returns a cleaner proof, use Aristotle's. Do **not** poll
Aristotle repeatedly — one check after 30 min is enough.

---

## 7. Pre-commit faithfulness checklist

For `IsHomogeneousSolution`:
- [ ] Quote (403a) verbatim in a docstring (already in §3a above).
- [ ] **Hand-trace `k = 2`**: the sum must produce
  `α_1 · y_{m+1} + α_2 · y_m`. If it produces
  `α_1 · y_m + α_2 · y_{m+1}` instead, the offset is reversed —
  flip to `y (m + k - 1 - i.val)` and re-trace.

For `IsStable`:
- [ ] **Definition smuggling check**: `IsStable` must be defined as
  "every homogeneous solution is bounded", **not** as any algebraic
  characterisation (root condition, power-bounded companion matrix,
  Schur condition). The textbook *defines* stability as "(403a) has
  only bounded solutions"; the equivalent characterisations are
  *theorems* (e.g. `thm:441C`), not the definition.
- [ ] **Tautology check**: `IsStable M` does not have hypothesis
  `IsHomogeneousSolution`; the universal quantifier is in the body.
- [ ] No characteristic polynomial in this cycle.

For the two witness theorems:
- [ ] Both are zero-hypothesis non-vacuity witnesses against
  concrete Euler records.
- [ ] **Identity check**: neither closes with `:= h_<name>`,
  `:= id`, or `exact h_<name>` — the proofs use
  `intro / induction / simp / refine`. This avoids the scanner
  false-positive issue documented in
  `tautology_scanner_false_positives.md`.
- [ ] `lake env lean OpenMath/Chapter4/Section404.lean` exits
  clean.
- [ ] `#print axioms OpenMath.Chapter4.Section404.explicitEulerLMM_isStable`
  shows only `[propext, Classical.choice, Quot.sound]`.

---

## 8. What NOT to do this cycle

These are **explicit prohibitions** with reasons. Do not deviate.

1. **Do NOT introduce a characteristic polynomial `ρ(z)`.** The
   cycle-036 task results suggested this, but `def:403A`'s
   `statement_text` does not mention `ρ` — only the homogeneous
   recurrence. Building `ρ` here would be infrastructure for §410's
   order-condition theorems, not for §403. Defer.

2. **Do NOT introduce a companion-matrix encoding.** The companion
   matrix bridges §403 stability to `def:142A` power-boundedness.
   That bridge is a *theorem* (essentially `thm:140A` plus a
   wrapper), not the definition. Defer.

3. **Do NOT formalize `def:402A` (convergent LMM) in this cycle.**
   `def:402A` requires the LMM step operator
   (`LinearMultistepMethod.step` or similar), which depends on `f`,
   `h`, and a chosen starting method. That is at least one full
   cycle of new infrastructure. Stay scoped.

4. **Do NOT rename `Section404.lean` to `Section403.lean` or split
   it.** Reusing the file is the cycle-035/036 convention; splitting
   adds an import-graph entry for one definition.

5. **Do NOT raise `maxHeartbeats`** above 200000 (CLAUDE.md absolute
   rule). The proofs here are short; you will not need to.

6. **Do NOT introduce any `axiom` or `constant` declaration**
   (CLAUDE.md absolute rule).

7. **Do NOT modify `scripts/autonomous_loop.py`** (worker rule per
   `tautology_scanner_false_positives.md`).

8. **Do NOT chase phantom verdicts.** Any "Section112.lean:74" or
   "Section212.lean:138/144" line in `attempts.md` is stale; both
   are diagnosed in `consultant_advice_cycle_009/014/015.md`. Cycle
   036 is committed at `16b74c7` — verify with
   `git log -1 --format='%H %s'` and move on.

9. **Do NOT use `:= h_<name>`, `:= id`, or `exact h_<name>` as the
   final closer of any new theorem or sub-proof.** Use plain
   `intro/refine/exact <full term>` shapes. The scanner has bugs
   and the workaround is to avoid the underscore-prefixed-
   hypothesis idiom. If you must build up a hypothesis with
   `rw … at hX; exact hX`, name it `hx` (no underscore).

10. **Do NOT redo any previously-formalized entity.** Do NOT touch
    `Section404.lean`'s existing `LinearMultistepMethod`,
    `IsPreconsistent`, `SatisfiesEq404b`, `IsConsistent`,
    `explicitEulerLMM`, `implicitEulerLMM`, or any of their witness
    theorems. **Append only.**

11. **Do NOT spend time on §142, AN-stability, Schur, or
    `picard_lindelof_bound_strengthening`.** All are documented
    blockers; none is on the critical path for §403. The current
    `def:403A` deliverable does not depend on any of them.

---

## 9. Bookkeeping (do all of these before committing)

1. Set `formalization_status` to `"formalized"` and populate
   `lean_file` / `lean_symbol` for `def:403A` in
   `extraction/formalization_data/lean_status.json`. Use:
   - `lean_file`: `OpenMath/Chapter4/Section404.lean`
   - `lean_symbol`: `OpenMath.Chapter4.Section404.LinearMultistepMethod.IsStable`
2. In `plan.md`, change the `[ ] def:403A` row to
   `[x] def:403A ... — OpenMath/Chapter4/Section404.lean` and bump
   the header counter from `36 / 175` to `37 / 175`.
3. Write `.prover-state/task_results/cycle_037.md` per the
   CLAUDE.md format. Faithfulness section must list:
   - `IsHomogeneousSolution` (helper predicate, not a textbook
     concept on its own — it captures equation (403a)).
   - `IsStable` (Definition 403A) with the textbook quote.
   - The two `_isStable` witnesses.
   Each with the textbook quote (or "not a named concept" note for
   `IsHomogeneousSolution`) and the "captures: same content" line.
4. Commit with a message of the form
   `Formalize def:403A — Dahlquist (zero-)stability of LMMs`.
   Verify the commit lands by running `git log -1 --format='%H %s'`
   *after* `git push`. Both must show the new commit hash.

---

## 10. Suggested cycle-038 preview (informational only)

After `def:403A` lands, the next §40 target is `def:402A`
(convergent LMM). It needs:

* The **LMM step operator**: a function or predicate capturing the
  implicit recurrence
  `Σ_i α_i y_{n-i} = h Σ_i β_i f(x_{n-i}, y_{n-i})`.
* A "starting method" abstraction (Butcher §402 mentions this is
  externally supplied) — likely a function `ℕ → ℝ → ℝ → ℕ → ℝ`
  returning the starting values `y_0, …, y_{k-1}` from the IVP and
  step size.
* A `Tendsto` statement `Y_m - y(x) → 0` as `m → ∞`.

That is a full cycle of infrastructure work. Do **not** start it
this cycle.
