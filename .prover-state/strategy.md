# Cycle 353 Strategy — BDF3 wire-up

## §A Context

Cycle 352 shipped clean (score=2): trapezoidal-rule wire-up — definition
+ preconsistency / (404b) / consistency in `Section404.lean`, plus
order-2 verification + the cycle 351 `coef_β`-identity instantiation
in `Section422.lean`. Sorry count: 0 across the repo. No pending
Aristotle results. The "What I'm stuck on" field in the prompt is
empty.

Cycle 352's task results recommend **Option 1 (BDF3 wire-up)** as the
lowest-risk single-cycle ship, matching cycle 352's cadence and
supplying the order-3 LMM witness currently absent from the project
(current witnesses cap at order 2: BDF2, trapezoidal).

**This cycle's deliverable: BDF3 wire-up.** Follow the trapezoidal /
BDF2 template verbatim, scaled to `k = 3`.

## §B What to ship

Six new public declarations (all axiom-clean target):

| # | Name | File | Source template |
|---|---|---|---|
| 1 | `bdf3LMM` | `Section451.lean` | `bdf2LMM` (line 140) |
| 2 | `bdf3LMM_isPreconsistent` | `Section451.lean` | trapezoidal_isPreconsistent (Section404:185) |
| 3 | `bdf3LMM_satisfiesEq404b` | `Section451.lean` | trapezoidal_satisfiesEq404b (Section404:191) |
| 4 | `bdf3LMM_isConsistent` | `Section451.lean` | trapezoidal_isConsistent (Section404:196) |
| 5 | `bdf3LMM_hasOrderAtLeast_three` | `Section422.lean` | `bdf2LMM_hasOrderAtLeast_two` (Section422:1284) |
| 6 | `bdf3LMM_coef_β_eq_half_sum_i_sq_alpha` | `Section422.lean` | `bdf2LMM_coef_β_eq_half_sum_i_sq_alpha` (Section422:1317) |

**Placement rationale:** `bdf2LMM` lives in `Section451.lean` (the
G-stability cluster), so `bdf3LMM` follows suit. The order-3 / coef_β
witnesses live in `Section422.lean` (the cycle 351/352 site) per the
trapezoidal precedent.

### Coefficients (verified on paper)

BDF3 in §404 normalisation (`α 0 = -1`):

```
α 0 = -1
α 1 = 18 / 11
α 2 = -9 / 11
α 3 = 2 / 11
β 0 = 6 / 11
β 1 = 0
β 2 = 0
β 3 = 0
```

Numerical checks (all on paper, all clean):

* Preconsistency: `Σᵢ₌₁..₃ αᵢ = 18/11 − 9/11 + 2/11 = 1` ✓
* (404b): `Σᵢ i·αᵢ = 18/11 − 18/11 + 6/11 = 6/11 = Σᵢ βᵢ` ✓
* `C M 0 = 1 − 1 = 0`, `C M 1 = 6/11 − 6/11 = 0`,
  `C M 2 = 0` (α-sum `[18/11 − 36/11 + 18/11]/2 = 0`; β-sum 0),
  `C M 3 = 0` (α-sum `[−18/11 + 72/11 − 54/11]/6 = 0`; β-sum 0).

### Identity instantiation (cycle 351 specialisation)

For BDF3:
* LHS `coef_β = Σᵢ:Fin 4 i·βᵢ = 0` (only `β 0 ≠ 0`)
* RHS `(1/2) · Σᵢ:Fin 3 (i+1)²·αᵢ.succ
     = (1/2) · [1·(18/11) + 4·(−9/11) + 9·(2/11)] = (1/2) · 0 = 0`

Both vanish — same trivial-witness shape as BDF2 (`0 = 0`). Worth
shipping anyway as a parity-with-trapezoidal sanity witness; the
non-trivial witness `1/2 = 1/2` was already shipped at trapezoidal
(cycle 352).

## §C Step-by-step recipe

### Step 1 — `bdf3LMM` definition (`Section451.lean`, after line 151)

Insert after `bdf2LMM`'s `α_zero := rfl` line, before
`bdf2GWitness`:

```lean
/-- The 3-step BDF method (BDF3) as a linear multistep method.
The textbook recurrence is
`y_n = (18/11) y_{n-1} − (9/11) y_{n-2} + (2/11) y_{n-3}
   + (6/11) h f(x_n, y_n)`.
Under the §404 normalisation `α 0 = -1`, the coefficient vectors are
`α = (-1, 18/11, -9/11, 2/11)`, `β = (6/11, 0, 0, 0)`. BDF3 is order 3
and stable, providing the order-3 LMM witness for §410/§422
non-vacuity. -/
noncomputable def bdf3LMM : LinearMultistepMethod 3 where
  α := fun i =>
    match i with
    | ⟨0, _⟩ => -1
    | ⟨1, _⟩ => 18 / 11
    | ⟨2, _⟩ => -9 / 11
    | ⟨3, _⟩ => 2 / 11
  β := fun i =>
    match i with
    | ⟨0, _⟩ => 6 / 11
    | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => 0
    | ⟨3, _⟩ => 0
  α_zero := rfl
```

The `noncomputable` keyword is required (`Real` division on `18/11`
etc. uses `Real.instDivInvMonoid`); cycle 352's `trapezoidalLMM`
needed the same treatment.

### Step 2 — Preconsistency / (404b) / consistency

Insert immediately after `bdf3LMM`, before `bdf2GWitness`:

```lean
/-- BDF3 is preconsistent: `Σᵢ αᵢ = 18/11 − 9/11 + 2/11 = 1`. -/
theorem bdf3LMM_isPreconsistent :
    bdf3LMM.IsPreconsistent := by
  simp [LinearMultistepMethod.IsPreconsistent, bdf3LMM,
    Fin.sum_univ_three]
  norm_num

/-- BDF3 satisfies (404b):
`Σᵢ i·αᵢ = 1·(18/11) + 2·(−9/11) + 3·(2/11) = 6/11 = β₀ = Σᵢ βᵢ`. -/
theorem bdf3LMM_satisfiesEq404b :
    bdf3LMM.SatisfiesEq404b := by
  simp [LinearMultistepMethod.SatisfiesEq404b, bdf3LMM,
    Fin.sum_univ_three, Fin.sum_univ_four]
  norm_num

/-- BDF3 is consistent (preconsistent + (404b)). -/
theorem bdf3LMM_isConsistent : bdf3LMM.IsConsistent :=
  ⟨bdf3LMM_isPreconsistent, bdf3LMM_satisfiesEq404b⟩
```

**Risk:** `bdf2LMM_isPreconsistent` uses a slightly different
incantation than `trapezoidalLMM_isPreconsistent`. The trapezoidal
case (Section404:185) closes by `simp` alone because the `α`/`β`
fields are `if-then-else` — `simp` unfolds the conditional. BDF
methods use `match` on `Fin`, which `simp` handles by needing the
`Fin.sum_univ_n` hint. **Add `Fin.sum_univ_three` (3-summand
α-sum) and `Fin.sum_univ_four` (4-summand β-sum)** to the simp
sets, then `norm_num` to close the rational arithmetic
`18/11 − 9/11 + 2/11 = 1` and `1·(18/11) + 2·(−9/11) + 3·(2/11) = 6/11`.

If the first attempt fails, inspect `Section451.lean:331+` for
`bdf2LMM_isConsistent`'s concrete recipe (already shipped axiom-clean
for k=2; this is the closest precedent and will likely show whether
`Fin.sum_univ_succ` / `Finset.sum_succ_above_eq` are needed instead).

### Step 3 — `bdf3LMM_hasOrderAtLeast_three` (`Section422.lean`, after line 1325)

Append after `bdf2LMM_coef_β_eq_half_sum_i_sq_alpha` (which is the
last existing Phase D′.2.2 BDF2 witness), keeping cycle 352's
trapezoidal block immediately following. Use the trapezoidal /
BDF2 four-arm template scaled to `j ∈ {0, 1, 2, 3}`:

```lean
/-- *Phase D′.2.2 BDF3 order-3 witness (cycle 353):* BDF3 satisfies
`HasOrderAtLeast 3`. Verified by checking `C bdf3LMM j = 0` for
`j ∈ {0, 1, 2, 3}` (preconsistency + (404b) + two further
cancellations from the α-side third- and fourth-power moments).
This is the project's first order-≥-3 LMM witness. -/
theorem bdf3LMM_hasOrderAtLeast_three :
    OpenMath.Chapter4.Section451.bdf3LMM.HasOrderAtLeast 3 := by
  intro j hj
  interval_cases j
  · show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section451.bdf3LMM 0 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section451.bdf3LMM, Fin.sum_univ_three]
    norm_num
  · show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section451.bdf3LMM 1 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section451.bdf3LMM,
      Fin.sum_univ_three, Fin.sum_univ_four, Nat.factorial]
    norm_num
  · show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section451.bdf3LMM 2 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section451.bdf3LMM,
      Fin.sum_univ_three, Fin.sum_univ_four, Nat.factorial]
    norm_num
  · show OpenMath.Chapter4.Section410.C
        OpenMath.Chapter4.Section451.bdf3LMM 3 = 0
    simp [OpenMath.Chapter4.Section410.C,
      OpenMath.Chapter4.Section451.bdf3LMM,
      Fin.sum_univ_three, Fin.sum_univ_four, Nat.factorial]
    norm_num
```

### Step 4 — Identity instantiation (`Section422.lean`, immediately after Step 3)

```lean
/-- *Phase D′.2.2 BDF3 sanity witness (cycle 353):* end-to-end
exercise of `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two`
on BDF3. Like BDF2 (cycle 351), both sides vanish at BDF3:
* LHS `coef_β(bdf3LMM) = 0·(6/11) + 1·0 + 2·0 + 3·0 = 0`;
* RHS `(1/2) · Σᵢ (i+1)²·αᵢ.succ = (1/2) · [1·(18/11) + 4·(−9/11) +
  9·(2/11)] = (1/2) · 0 = 0`.
A trivial-identity witness (parity with BDF2); the first non-trivial
witness was trapezoidal `1/2 = 1/2` (cycle 352). -/
theorem bdf3LMM_coef_β_eq_half_sum_i_sq_alpha :
    (∑ i : Fin 4, ((i.val : ℕ) : ℝ) *
        OpenMath.Chapter4.Section451.bdf3LMM.β i)
      = (1 / 2) *
        ∑ i : Fin 3, (((i.val + 1 : ℕ) : ℝ))^2 *
          OpenMath.Chapter4.Section451.bdf3LMM.α i.succ := by
  apply coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two
  intro j hj
  exact bdf3LMM_hasOrderAtLeast_three j (by omega)
```

**Note**: `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two`
requires `HasOrderAtLeast 2`, not `3`. The recipe above derives
the order-2 instance inline via `omega` (which handles `j ≤ 2 → j ≤ 3`)
— **safer than assuming a `.mono` lemma exists**. Do NOT search
for `HasOrderAtLeast.mono`; the inline route always works.

### Step 5 — Verification

```bash
lake build OpenMath.Chapter4.Section451
lake build OpenMath.Chapter4.Section422
```

Then `#print axioms` for each of the six new public symbols.
Expected: `[propext, Classical.choice, Quot.sound]` for all six.

**Critical**: per cycle 352's "Discovery" section, `lake env lean`
does NOT update `.olean`. **Use `lake build <Module>` between edits
to `Section451.lean` and consumer-file (`Section422.lean`) builds.**
Failing to do this caused cycle 352 to waste ~25 min on a stale
Section404 olean.

## §D What to update

* `extraction/formalization_data/lean_status.json` — **no change**.
  BDF3 is not a textbook-named entity; the wire-up is a non-vacuity
  ship for the existing `def:402A` / `def:403A` / `def:404B` / `def:404A`
  rows (and the §422 Phase D′.2.2 chain on top).
* `plan.md` — **no change**. Same rationale.
* `.prover-state/task_results/cycle_353.md` — standard cycle results
  doc (Worked on / Approach / Result / Faithfulness check / Dead ends /
  Discovery / Suggested next approach).

## §E Faithfulness checklist

Per CLAUDE.md "Pre-Commit Faithfulness Checklist":

1. **`bdf3LMM`** — not a textbook *entity*, but a standard
   universally-attested 3-step BDF method. Coefficients verified on
   paper above. **No textbook divergence**.
2. **`bdf3LMM_isPreconsistent` / `_satisfiesEq404b` / `_isConsistent`** —
   numerical specialisations of existing predicates (`def:404A`,
   `def:404B`). Direct arithmetic; no tautology, no identity-only
   proof. **Same content** as the textbook claim "BDF3 is
   consistent". Identity check: PASS (`simp` does real `18/11 −
   9/11 + 2/11 = 1` arithmetic, not a hypothesis re-export).
3. **`bdf3LMM_hasOrderAtLeast_three`** — numerical specialisation.
   The textbook claim that "BDF3 has order 3" is standard. Verified
   by direct computation of `C bdf3LMM j` for `j ∈ {0, 1, 2, 3}`.
   **Same content**.
4. **`bdf3LMM_coef_β_eq_half_sum_i_sq_alpha`** — specialisation of
   cycle 351's identity. Proof is a single
   `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two` application
   (downcast from order ≥ 3 to order ≥ 2 inline); the mathematical
   work is in the cycle 351 theorem. This is a non-vacuity witness
   (both sides vanish), exercising the identity at an order-3 method.
   **Same content**.

## §F What NOT to do this cycle

1. **Do NOT attempt Option 2 (`trapezoidalLMM_isStable`).** Per
   cycle 352's task results, this requires handling at-boundary roots
   of `ρ(z) = z - 1` (simple root at `z = 1` on the unit circle),
   which is NOT covered by cycle 346's `bdf2LMM_isStable` interior-
   roots recipe. Substantive separate cycle.
2. **Do NOT start Phase D′.2.2 Step 2 (`0 ≤ Σᵢ (i+1)²·αᵢ`).** The
   cycle 348 scoping doc covers Phase D′.2.0 / 2.1 / 2.2; Phase
   D′.2.2 Step 2 (closing the `coef_β ≥ 0` inequality) needs a
   dedicated multi-cycle scoping doc *before* any Lean code. Cycle
   352's task results explicitly defer this.
3. **Do NOT introduce sorries.** Cycles 149/150 (def:530B Path A)
   and 200/201 (thm:381H scaffold) both rolled back sorry-first
   scaffolds. Ship axiom-clean or don't ship.
4. **Do NOT add `bdf3LMM_isStable`.** That's the natural Phase B
   next step but it requires the cycle 346 stability infrastructure
   on a 3-step method — multi-cycle. Separate ship.
5. **Do NOT bump `bdf3LMM_hasOrderAtLeast_three` to
   `HasOrderAtLeast 4` "while we're at it"** — BDF3 has exact order
   3, not 4 (`C M 4 ≠ 0`). Stating order ≥ 4 would be **false** and
   the proof would fail. The textbook claim is order exactly 3.
6. **Do NOT include `Fin.sum_univ_two` in the BDF3 simp sets** — BDF3
   has `Fin 3` (α) and `Fin 4` (β) summations; `Fin.sum_univ_two` is
   the wrong hint and might cause `simp` to spin.
7. **Do NOT bypass the `lake build` cache discipline.** Per cycle
   352's "Discovery": `lake env lean` does not update `.olean`. Run
   `lake build OpenMath.Chapter4.Section451` after each edit to
   `Section451.lean`, **before** `lake build OpenMath.Chapter4.Section422`.
8. **Do NOT freelance to a fresh entity (Chapter 3 §342, §344, etc.)**.
   Cycle 352 closed a clean §404/§422 small-cycle ship; cycle 353
   matches that cadence with BDF3 to compound the witness surface
   (currently order ≤ 2; this brings order 3 online).

## §G Failure modes from past cycles (DO NOT repeat)

* **Cycle 352 v1: missing `noncomputable`** on `trapezoidalLMM`
  caused `error(lean.dependsOnNoncomputable)`. BDF2 already used
  `noncomputable`; BDF3 follows suit (Step 1 above includes it
  explicitly).
* **Cycle 352 v1: trailing `norm_num`** in `_isPreconsistent` /
  `_satisfiesEq404b` produced `error: No goals to be solved` for
  `trapezoidalLMM` because `simp` already closed the if-then-else
  form. BDF3 uses `match` on `Fin`, which `simp` does NOT fully
  reduce — `norm_num` IS needed for the rational arithmetic.
  **Do NOT remove `norm_num` from the BDF3 recipe.** (BDF2's
  `_isConsistent` proof at Section451:331 also keeps `norm_num`.)
* **Cycle 173 BDF2 closed-form attempt: `Polynomial.ext + simp +
  ring`** stalled on `Polynomial.C` arithmetic over ℝ. Not relevant
  this cycle — we are NOT shipping `bdf3LMM.aPoly` closed form.
* **Cycles 176–179 phantom commit verdicts** on Section441 were
  false alarms (per `phantom_commit_verdict_pattern.md`). Not
  relevant this cycle — Section441 is untouched.

## §H Optional stretch (only if Steps 1–5 close in < 60 minutes)

If BDF3 ships smoothly and time remains, add **two thin one-line
corollary witnesses** for cycle 344's `coef_α_pos_of_stable_preconsistent`
specialised to BDF3 — but **only if `bdf3LMM_isStable` already
exists**. Currently `bdf3LMM_isStable` does NOT exist
(cycle 346 shipped `bdf2LMM_isStable`, not BDF3), so this stretch
is **not available this cycle**. Stretch effectively disabled —
ship Steps 1–5 only.

## §I Cycle 354+ outlook

Per cycle 352 task results, three forward directions remain
plausible after BDF3 ships:

1. **`bdf3LMM_isStable`** (~50–80 LOC) — port cycle 346's `bdf2LMM_isStable`
   recipe to k=3. The §403 ρ-polynomial-roots argument generalises
   cleanly; substantive but tractable single cycle.
2. **`trapezoidalLMM_isStable`** (~50 LOC) — at-boundary stability,
   substantive single cycle. Pairs with cycle 346's `bdf2LMM_isStable`.
3. **Phase D′.2.2 Step 2 scoping** (Markdown only) — write the
   dedicated `eq422a_eta_phase_D_prime_step_2_step_2_scoping.md`
   covering the `0 ≤ Σᵢ (i+1)²·αᵢ` route options (`ρ''(1) ≥ 0`,
   §441 Möbius, etc.).
4. **`thm:535A` (underlying one-step method, GLM)** — Chapter 5
   §535 entry point; ~2–3 cycle definition + non-vacuity work,
   would break the §422 streak (cycles 336–353 = 18 consecutive on
   `def:422B`-adjacent work).

Cycle 354's planner decides based on cycle 353's outcome.
