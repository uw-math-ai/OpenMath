# Cycle 354 Strategy

## §A — State at cycle 354 start

* Last commit: `f4158b3` (cycle 353 — BDF3 wire-up: order-3 LMM witness).
* No pending Aristotle results.
* Sorry count: 0. No tracked blockers requiring infrastructure work.
* `Section441.lean` remains GPFS-blocked (43+ consecutive compile
  timeouts since cycle 182 — do **not** attempt to add to Section441).
  Section441's `.olean` cache is healthy, so downstream consumers
  (Section422 in particular) build fine.

The cycle 353 worker shipped 6 axiom-clean BDF3 declarations
(`bdf3LMM` + 4 §404/§422 witnesses + the cycle 351 identity at BDF3),
opening up the project's first **order-3 LMM territory**. The
worker's `## Suggested next approach` block offered three directions:

1. `bdf3LMM_isStable` — substantive, ports cycle 346's BDF2 closed-form
   recipe to k = 3 with complex conjugate roots (`(z − 1)(11z² − 7z + 2)`,
   discriminant `−39`, complex-pair magnitude `√(2/11)`).
2. `trapezoidalLMM_isStable` — trivial port of `explicitEulerLMM_isStable`
   (k = 1, α₁ = 1, constant solutions, ~15 LOC).
3. Phase D′.2.2 Step 2 scoping (Markdown only).

§B–§E below commit to a hybrid plan: **P1 ships trapezoidal stability
as a guaranteed-close warm-up**, **P2 attempts BDF3 stability with a
strict time-box and fallback ladder**.

## §B — P1 (PRIMARY, ~15 LOC, GUARANTEED): `trapezoidalLMM_isStable`

Trapezoidal rule (Crank–Nicolson) is `k = 1`, α₁ = 1 — the homogeneous
recurrence is `Y(m+1) = Y(m)`, identical in shape to the two Euler
methods. Port `explicitEulerLMM_isStable`
(`OpenMath/Chapter4/Section404.lean:248-259`) verbatim with one symbol
substitution.

### Concrete signature

In `OpenMath/Chapter4/Section404.lean`, immediately after
`implicitEulerLMM_isStable` (line 273), add:

```lean
/-- The trapezoidal rule is Dahlquist-stable. -/
theorem trapezoidalLMM_isStable : trapezoidalLMM.IsStable := by
  intro y hy
  have hconst : ∀ n, y n = y 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        have hrec := hy n
        simp [trapezoidalLMM] at hrec
        linarith
  refine ⟨|y 0|, fun n => ?_⟩
  rw [hconst n]
```

### Required imports

None new. `trapezoidalLMM` is already defined at Section404.lean:179
(cycle 352).

### Verification

```bash
lake build OpenMath.Chapter4.Section404
echo '#print axioms OpenMath.Chapter4.Section404.trapezoidalLMM_isStable' \
  | lake env lean --stdin OpenMath/Chapter4/Section404.lean
```

Expected output: `[propext, Classical.choice, Quot.sound]`.

### Faithfulness check

* Entity: `def:403A` (no separate entity — stability is a predicate,
  not a textbook theorem). Trapezoidal stability is folklore (Dahlquist
  §403 implicitly).
* Lean statement matches `LinearMultistepMethod.IsStable` verbatim
  (cycle 346 precedent: same shape as `bdf2LMM_isStable`).
* Tautology check: PASS (the proof does real work — induction on the
  recurrence is not a hypothesis re-export).
* Hypothesis-strength check: PASS (no hypotheses beyond the predicate).

**P1 ships definitively. Do this first.**

## §C — P2 (SUBSTANTIVE, ~100–200 LOC, MEDIUM-HIGH risk): `bdf3LMM_isStable`

The proof structure ports cycle 346's `bdf2LMM_isStable` recipe
(`Section451.lean:330-348`) to k = 3 with a real-form closed-form
decomposition that handles the complex conjugate root pair.

### Mathematical setup

BDF3 characteristic polynomial: `11z³ − 18z² + 9z − 2 = 0`. Factor as
`(z − 1)(11z² − 7z + 2)`.

* **Real root**: `z₁ = 1`, simple, on the unit circle.
* **Complex conjugate pair**: roots of `11z² − 7z + 2 = 0`. Discriminant
  `49 − 88 = −39 < 0`. Real part `7/22`, imaginary part `√39/22`.
  Magnitude `|z|² = 2/11 ≈ 0.182 < 1`. **Strictly inside the disc.**

### Recommended route — auxiliary-sequence + Lyapunov

The naive trig closed-form `Y(n) = A + (2/11)^(n/2)·(B·cos(nθ) +
C·sin(nθ))` is Lean-fiddly because of the trig identities required at
each induction step. The cleaner approach:

**Step 1 — auxiliary sequence is constant**. Define `Z(n) := Y(n+2)
− (7/11)·Y(n+1) + (2/11)·Y(n)`. Direct substitution of BDF3's
recurrence `Y(n+3) = (18/11)·Y(n+2) − (9/11)·Y(n+1) + (2/11)·Y(n)`
into `Z(n+1)` shows `Z(n+1) = Z(n)`. So `Z` is constant with
`Z(n) = C₀ := Y(2) − (7/11)·Y(1) + (2/11)·Y(0)`.

**Step 2 — `Y` satisfies an inhomogeneous 2-term recurrence**.
Equivalently:

  `Y(n+2) = (7/11)·Y(n+1) − (2/11)·Y(n) + C₀`.

The unique constant particular solution is `A := 11·C₀/6` (from
`(6/11)·A = C₀`). The homogeneous part `W(n) := Y(n) − A` satisfies

  `W(n+2) = (7/11)·W(n+1) − (2/11)·W(n)`,

whose characteristic polynomial has roots strictly inside the unit
disc.

**Step 3 — Lyapunov bound on `W`**. Find `α, β > 0` such that
`Q(W(n), W(n+1)) := α·W(n)² + β·W(n+1)²` is non-increasing in `n`.
Concretely: paper-verify

  `Q(W(n+1), W(n+2)) − Q(W(n), W(n+1))
     = β·W(n+2)² + (α − β)·W(n+1)² − α·W(n)² ≤ 0`

for some specific `(α, β)`. (A reasonable trial: `α = 2, β = 11`,
because `11·W(n+2)² ≈ 11·((7/11)W(n+1) − (2/11)W(n))² = (49/11)·W(n+1)²
+ (4/11)·W(n)² − (28/11)·W(n+1)·W(n)`; the negative-semidefiniteness
inequality with the trial pair may or may not hold — verify on paper
before committing.) If `(2, 11)` doesn't work, try `(1, 7)` or
`(4, 11)`. The general criterion is that the quadratic form
`-α·x² + 2·(−14β/121)·x·y + (β·49/121 + α − β)·y²` is negative
semidefinite as a form on `(x, y) = (W(n), W(n+1))`. **Verify on
paper first**; if no clean rational `(α, β)` works, fall back to the
trig route.

**Step 4 — boundedness**. `Q(W(0), W(1))` is a finite constant, so
`W(n)² ≤ Q(W(n), W(n+1))/min(α, β) ≤ Q(W(0), W(1))/min(α, β)`, i.e.
`|W(n)| ≤ √(Q(W(0), W(1))/min(α, β))`. Then `|Y(n)| ≤ |A| + |W(n)|`
is uniformly bounded.

### Concrete Lean shape

In `OpenMath/Chapter4/Section451.lean`, after `bdf2LMM_isStable` (line
348). Three private theorems + one public:

```lean
-- (1) Z is constant.
private theorem bdf3_auxiliary_const (Y : ℕ → ℝ)
    (hY : bdf3LMM.IsHomogeneousSolution Y) :
    ∀ n, Y (n+2) - (7/11)·Y (n+1) + (2/11)·Y n
       = Y 2 - (7/11)·Y 1 + (2/11)·Y 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hrec := hY n
      simp [bdf3LMM, Fin.sum_univ_three] at hrec
      linarith [ih]

-- (2) Y = A + W where W satisfies a 2-term recurrence.
-- Define A := 11·C₀/6 and W := Y - A. Prove W satisfies the
-- 2-term recurrence by direct substitution (uses (1)).

-- (3) Lyapunov: Q(W) := α·W² + β·W² is non-increasing.
-- (paper-verify the α, β values FIRST)

-- (4) bdf3LMM_isStable: combine (1) + (3) for boundedness.
```

### Time-box and fallback ladder

* **0–20 min**: paper-verify a clean `(α, β)` Lyapunov pair. If
  the inequality with rational `(α, β) ∈ {(2, 11), (1, 7), (4, 11),
  (5, 12)}` doesn't fire, pivot to the trig route or fall back
  immediately to P3.
* **20–90 min**: write the three private theorems + public
  theorem in Lean. Run `lake build OpenMath.Chapter4.Section451`
  after each non-trivial step.
* **90+ min, NOT CLOSED**: **STOP** and fall back to P3.

### Faithfulness check (when shipped)

* Entity: same as P1 (`def:403A` predicate, no separate textbook
  entity).
* Lean statement: `bdf3LMM.IsStable`, matches the predicate directly.
* Tautology check: PASS (decomposition + Lyapunov argument is real
  work).
* Hypothesis-strength check: PASS (no extra hypotheses).

## §D — P3 (FALLBACK and STRETCH, ~15–60 LOC each)

If P2 stalls past 90 min, ship one or more of these instead. Each is
guaranteed-close ~15–60 LOC.

### P3a (recommended first fallback) — `trapezoidalLMM_sum_β_pos`

Composition of P1's `trapezoidalLMM_isStable` with cycle 349's
`sum_β_pos_of_stable_consistent` (Section422.lean) and cycle 352's
`trapezoidalLMM_isConsistent`. One-liner:

```lean
/-- Cycle 349 `sum_β_pos_of_stable_consistent` exercised at the
trapezoidal rule. -/
theorem trapezoidalLMM_sum_β_pos :
    0 < ∑ i : Fin 2, trapezoidalLMM.β i :=
  sum_β_pos_of_stable_consistent trapezoidalLMM (by norm_num)
    trapezoidalLMM_isStable trapezoidalLMM_isConsistent
```

Add to `Section422.lean` after cycle 352's trapezoidal block. Verify
the exact name and signature of `sum_β_pos_of_stable_consistent`
against `Section422.lean` (cycle 349 added it, but the worker
should grep before consuming).

### P3b — `bdf3LMM_coef_α_plus_coef_β_ne_zero` numerical witness

Even without `bdf3LMM_isStable`, the algebraic identity
`coef_α + coef_β = Σᵢ (i+1)·βᵢ` (cycle 350) instantiated at BDF3
gives a one-liner non-vacuity:

```lean
/-- BDF3 satisfies the non-vanishing side hypothesis from cycle 350's
weakened (422a) corollary: `coef_α + coef_β = 6/11 ≠ 0`. -/
theorem bdf3LMM_coef_α_plus_coef_β_ne_zero :
    (∑ i : Fin 3, ((i.val + 1 : ℕ) : ℝ) * bdf3LMM.α i.succ)
      + (∑ i : Fin 4, ((i.val : ℕ) : ℝ) * bdf3LMM.β i) ≠ 0 := by
  simp [bdf3LMM, Fin.sum_univ_three, Fin.sum_univ_four]; norm_num
```

(Adapt the simp set to whatever cycle 350 used.)

### P3c — Scoping issue file for BDF3 stability

If P2 stalls AND there's time, write `.prover-state/issues/
bdf3_stability_path.md` (≥150 lines Markdown, no Lean code)
decomposing BDF3 stability into the auxiliary-sequence + Lyapunov
route as a multi-cycle plan, with paper-verified Lyapunov
coefficients and a 2-3 cycle decomposition. Template:
`.prover-state/issues/eq422a_eta_phase_D_prime_step_2_scoping.md`.

## §E — Explicitly DO NOT pursue

* **DO NOT add to `OpenMath/Chapter4/Section441.lean`.** It is
  GPFS-blocked (43+ consecutive compile timeouts since cycle 182).
  Adding even a 5-line lemma triggers the pathology. All `Section441`
  consumers work through cached `.olean`s — that's fine. See
  `.prover-state/issues/cycle_182_gpfs_slowness.md`.
* **DO NOT attempt Phase D′.2.2 Step 2 main theorem this cycle**
  (`0 ≤ Σᵢ (i+1)²·α(i.succ)` under stable + preconsistent + order ≥ 2).
  Substantive multi-cycle work requiring `ρ''(1) ≥ 0` infrastructure
  in Section441 (blocked) or §441 Möbius transform extension (also
  Section441). The cycle 351 algebraic identity reduces Step 2 to a
  polynomial-derivative positivity claim; closing that is genuinely
  multi-cycle.
* **DO NOT attempt BDF3 stability via "companion matrix
  power-boundedness"**. That route requires building the entire
  matrix-power-bounded-on-finite-dim infrastructure from scratch and
  is multi-cycle (see `cesaro_inverse_I_minus_V.md` for an analogous
  Section514 obstruction).
* **DO NOT attempt BDF3 stability via "all complex roots in closed
  unit disc ⇒ stable" general theorem**. That's the §441 root-condition
  ↔ Dahlquist-stability bridge and is multi-cycle infrastructure work
  (same family as `thm:441C`, the Dahlquist barrier).
* **DO NOT introduce `axiom` / `constant` declarations** for any
  step.
* **DO NOT raise `maxHeartbeats` above 200000**. If the BDF3
  Lyapunov inequality's `nlinarith` times out, decompose into
  intermediate lemmas first.
* **DO NOT attempt `bdf3LMM_isGStable`** (G-stability witness) as
  an alternative to Dahlquist stability. G-stability requires
  constructing a specific 3×3 positive-definite matrix `G` and
  verifying `gMatrix bdf3LMM G` is PSD — substantial work, multi-cycle.
  The cycle 346 BDF2 precedent (Section451.lean:280-283) used a
  hand-supplied `bdf2GWitness` matrix from Butcher's textbook; BDF3's
  textbook witness is not currently in our codebase.
* **DO NOT pivot to a fresh entity** before P1 ships. The
  trapezoidal stability witness is the floor deliverable.
* **DO NOT attempt the trig closed-form route as the primary
  approach.** The auxiliary-sequence + Lyapunov route (§C above) is
  simpler. Trig is the fallback if Lyapunov coefficients don't work.

## §F — Cycle 354 deliverable bar

* **Score = +2 floor**: P1 (`trapezoidalLMM_isStable`) shipped
  axiom-clean.
* **Score = +3 target**: P1 + P2 (`bdf3LMM_isStable`) both shipped
  axiom-clean.
* **Score = +2 fallback**: P1 + P3a (`trapezoidalLMM_sum_β_pos`)
  shipped axiom-clean; BDF3 stability deferred to a scoping doc
  (P3c) for cycle 355.

Sorry count must remain at **0** (cycle 200/201 rollback precedent —
sorry-first scaffolds for multi-cycle targets without single-cycle
closure get rolled back).

## §G — Task results format

Cycle 354 worker MUST write `.prover-state/task_results/cycle_354.md`
with:

* `## Worked on`: which of P1/P2/P3 attempted, in order.
* `## Approach`: which BDF3 route chosen (auxiliary-sequence Lyapunov
  vs trig closed-form), if P2 was attempted. If Lyapunov, record
  the `(α, β)` pair used.
* `## Result`: SUCCESS / FAILED with line counts and axiom report per
  theorem.
* `## Faithfulness check`: per-theorem entity citation + tautology /
  identity / hypothesis-strength checks. Note that `def:403A` is a
  predicate with no separate textbook theorem, so the stability
  witnesses are non-vacuity for that predicate, not citations of
  named textbook theorems.
* `## Dead ends`: any blind alleys hit during P2's BDF3 attempt
  (e.g., trig identity that didn't fire, Lyapunov coefficient that
  didn't bound). Be specific so cycle 355 can learn.
* `## Discovery`: any Mathlib hooks identified for future cycles
  (Lyapunov-style monotone-norm reasoning, complex-root closed forms,
  etc.).
* `## Suggested next approach`: cycle 355 priorities. Candidates:
  - If BDF3 stability shipped: pivot to `Phase D′.2.2 Step 2` proper
    (now that all four §404 stable methods — Euler×2, trapezoidal,
    BDF2, BDF3 — have stability + consistency witnesses, the
    motivation for unconditional Phase D′ corollaries is stronger).
  - If BDF3 stability deferred: continue with the auxiliary-sequence
    or trig closed-form route per the P3c scoping doc.
  - Pivot candidates: `def:451A` `IsGStable` for trapezoidal
    (Section451 extension); `def:422B` `underlyingOneStepMethod`
    Phase D.2/D.3 work (multi-cycle per `def_422B_path.md`); or
    `bdf3LMM_isGStable` as a separate Section451 ship (needs
    textbook G-matrix lookup).

## §H — Cycle 354 execution discipline

1. **First 10 min**: read §B above, write trapezoidal stability,
   build, verify, commit P1 alone. Do not block P1 on P2 progress.
2. **Next 20 min**: paper-verify the Lyapunov coefficients for §C
   Step 3. If none work cleanly with rationals, pivot to trig
   closed-form OR fall back to P3 directly.
3. **Next 70 min**: write P2 in Lean. Build after each private
   theorem.
4. **Last 30 min**: if P2 closed, write task results and commit
   together with P1. If P2 stalled, ship P3a (and optionally
   P3b / P3c) and commit.
5. **Final 10 min**: update `lean_status.json` (no row changes
   expected for stability witnesses — they support `def:402A` /
   `def:403A` non-vacuity rather than closing textbook entities)
   and `plan.md` (likewise no row changes expected).

If the cycle ends with ONLY P1 shipped (because P2 stalled and P3 was
not attempted), that is still a **+2 cycle** — sub-optimal but
acceptable. The supervisor explicitly tolerates cycles that ship one
clean unit of progress over cycles that attempt too much and regress.
