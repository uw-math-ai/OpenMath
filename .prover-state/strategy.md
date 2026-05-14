# Cycle 237 strategy

## §A — Pivot rationale

The §380 cluster has been the focus for **22 consecutive cycles
(215–236)**. Cycle 236 shipped the §383 `Group` instance on
`Quotient PhiEquivalent.setoidSigma` (axiom-clean). The natural next
step in §380 is `thm:384A` (Φ as `MonoidHom`/`GroupHom` from §382 to
§383), but this requires the `Equivalent → PhiEquivalent` direction
which is **multi-cycle B-series infrastructure** (needs `thm:311D`
output-as-B-series, `thm:314A` independence of elementary
differentials, and a smooth-IVP relaxation of `Equivalent`'s
Lipschitz hypothesis). See `.prover-state/issues/thm_381H_deferred.md`
deferred directions (1) and (3).

The cycle 236 worker explicitly recommended pivoting:

> A fresh entity entirely (e.g., `def:422B` underlying one-step LMM,
> or §535 GLM underlying one-step method). The §380 cluster has been
> the focus for many consecutive cycles (cycles 215–236, 22 in a row)
> — a planner pivot may be appropriate.

I scoped def:422B, def:442A, thm:343B, thm:534A, thm:541A, thm:551B,
and thm:323B; **all require B-series machinery** (`lem:310B`,
`lem:311A`, `lem:312B`, `lem:313A`, `thm:311D`, `thm:313B`) or
Riemann-surface infrastructure or `thm:550B`. None are single-cycle.

The exception: **`lem:441B`** (Butcher §441 p. 376) is a stand-alone
PowerSeries problem **with no LMM dependency**. The cycle 171
attempt was rolled back per `.prover-state/issues/lem_441B_misinterpretation.md`
because cycle 171 conflated `lem:441B`'s universal `c_{2i}` constants
with `aPoly` coefficients. The issue file scopes the **correct**
formalization as a "Phase B" cycle: define `cInverseLog : ℕ → ℝ`
via PowerSeries inversion, prove the textbook (441c) identity, and
establish base cases `c₀ = 1/2`, `c₂ = −1/6`.

This cycle: **lem:441B Phase B** — single-cycle PowerSeries cycle.

## §B — Primary target: `lem:441B` Phase B

### Background reading (mandatory)

1. `.prover-state/issues/lem_441B_misinterpretation.md` — full
   diagnosis of why cycle 171's `aPoly_even_coeff_neg` was wrong
   (it keyed off Sequence 1 `aᵢ`, but `lem:441B` is about the
   independent universal Sequence 2 `c_{2i}`).
2. `extraction/raw_text/ch04.txt:1947–2030` — verbatim Butcher §441
   text. **Do not edit `raw_text/`.**
3. `extraction/formalization_data/entities/lem_441B.json` —
   textbook statement.
4. Cycle 235 / cycle 236 task results — the §383 Group instance
   landed; this cycle is independent of it.

### Textbook statement

> Lemma 441B. The coefficients `c₂, c₄, …` are all negative.

> Proof. Using the series for `log((1+z)/(1−z))/z`, we see that
> `c₀, c₂, c₄, …` satisfy
> ```
> (2 + (2/3)z² + (2/5)z⁴ + ⋯) · (c₀ + c₂z² + c₄z⁴ + ⋯) = 1.   (441c)
> ```
> It follows that `c₀ = 1/2, c₂ = −1/6`. ...

The Sequence 2 `c_{2i}` are constants of a **universal power
series**. They have **no LMM dependence** — the `cInverseLog n`
function is a function `ℕ → ℝ`, NOT `LinearMultistepMethod k → ℕ → ℝ`.

### Phase B deliverables (this cycle)

Land all axiom-clean. See §C for the file-placement decision
(extend `Section441.lean` if GPFS smoke test passes, otherwise
create `Section441B.lean`).

1. **`cInverseLogSeries : PowerSeries ℝ`** — the LHS series of
   (441c), `2 + (2/3)X² + (2/5)X⁴ + ⋯`. Recommended definition:
   ```lean
   noncomputable def cInverseLogSeries : PowerSeries ℝ :=
     PowerSeries.mk fun n =>
       if Even n then 2 / (n + 1 : ℝ) else 0
   ```
   (i.e. coefficient of `X^(2i)` is `2 / (2i + 1)`, coefficient of
   `X^(2i+1)` is `0`.)

2. **`cInverseLogSeries_constantCoeff_eq_two`** — the constant
   coefficient is `2 ≠ 0`, so the series is invertible in
   `PowerSeries ℝ`. Proved by `simp [cInverseLogSeries]`. Required
   for invoking `PowerSeries.invOfUnit`.

3. **`cSeries : PowerSeries ℝ`** — define as the inverse, then
   normalize so the indexing matches the textbook's `c_{2i}`:
   ```lean
   noncomputable def cSeries : PowerSeries ℝ :=
     PowerSeries.invOfUnit cInverseLogSeries (Units.mk0 2 ...)
   ```
   (or hand-roll via `PowerSeries.mk` with an explicit recurrence —
   see R3 below for the encoding choice). The textbook (441c)
   identity becomes `cInverseLogSeries * cSeries = 1`.

4. **`cInverseLog : ℕ → ℝ`** — extract the textbook coefficients
   `c_{2n}`:
   ```lean
   noncomputable def cInverseLog (n : ℕ) : ℝ :=
     PowerSeries.coeff ℝ (2 * n) cSeries
   ```

5. **`cInverseLog_zero_eq_half : cInverseLog 0 = 1/2`** — base
   case from (441c) constant-coefficient evaluation.

6. **`cInverseLog_one_eq_neg_one_sixth : cInverseLog 1 = -1/6`** —
   second base case (`c₂ = −1/6`). Computed from the (441c) identity
   at `X²` coefficient: `0 = (2/3)·c₀ + 2·c₂`, hence
   `c₂ = -(2/3)/2 · c₀ = -1/3 · 1/2 = -1/6`.

7. **`cInverseLog_recurrence`** (Phase B headline): the (441c)-derived
   recurrence at `n ≥ 1`. Recommended cleanest form:
   ```
   ∀ n, n ≥ 1 → 2 * cInverseLog n =
     - ∑ i in Finset.range n, (2 / (2 * (i + 1) + 1 : ℝ)) * cInverseLog (n - 1 - i)
   ```
   (i.e. `2·c_{2n} = − ∑_{i=1}^{n} (2/(2i+1)) · c_{2(n-i)}`.)
   Proof: extract the `X^(2n)` coefficient from
   `cInverseLogSeries * cSeries = 1` via `PowerSeries.coeff_mul`,
   collapse odd-indexed contributions, rearrange.

### Phase C deferred (cycle 238+)

The strict-negativity claim `∀ n, 1 ≤ n → cInverseLog n < 0` is the
**Phase C** deliverable. The argument is strong induction on `n`
using the (441c) recurrence and the universal-fact
`d_{2i} = -8(n−i) / ((2i+1)(2i−1)) < 0` for `1 ≤ i ≤ n−1`,
`d_{2n} = 0`. **Do not attempt Phase C this cycle.** Phase C requires
proving sign properties of the dual `d` series, which is its own
~80–150 LOC deliverable.

### Aristotle suitability

**Medium**. The `cInverseLogSeries` definition + `cSeries`
construction + base-case computations are mechanical Mathlib API
calls. A 5-job batch is appropriate:
- Job 1: `cInverseLogSeries_constantCoeff_eq_two`
- Job 2: `cInverseLog_zero_eq_half`
- Job 3: `cInverseLog_one_eq_neg_one_sixth`
- Job 4: `cInverseLog_recurrence`
- Job 5 (stretch): `cInverseLog n < 0` for n = 1, 2 (Phase C base
  cases as numerical witnesses)

**Submit jobs at the START of the cycle**, then sleep ~30 min while
hand-writing the definitions (§B.1–§B.4) and base-case computations.
Single poll after sleep per CLAUDE.md.

## §C — File placement

**Recipe**:
1. At cycle start, run a one-shot GPFS smoke test:
   `time timeout 60 lake env lean OpenMath/Chapter4/Section441.lean`.
2. If it completes (unlikely — 41 consecutive failures spanning
   ~50 calendar days per `cycle_182_gpfs_slowness.md`), **extend
   `Section441.lean`** at the end of the existing namespace block.
3. If it times out (expected), **create
   `OpenMath/Chapter4/Section441B.lean`** as a new file with no
   imports from `Section441.lean` (since `cInverseLog` is pure
   ℝ-PowerSeries with no LMM dependency). Add
   `import OpenMath.Chapter4.Section441B` to `OpenMath/Chapter4.lean`.

The `cInverseLog` machinery has zero `LinearMultistepMethod`
references, so file split is technically clean either way.

## §D — Non-vacuity witnesses (P5)

After Phase B lands, ship at least these:

1. `cInverseLog 0 = 1/2` and `cInverseLog 1 = -1/6` (base cases —
   already in §B.5/§B.6).
2. `0 < cInverseLog 0` (the `c₀` base sign).
3. `cInverseLog 1 < 0` (the `c₂` base sign — this is the **first
   non-trivial Phase C instance**, derived directly from the base
   case computation, no induction needed).

These three witnesses confirm that Phase B's machinery delivers the
correct numerical values and that Phase C's negativity claim holds at
the smallest non-trivial index.

## §E — What NOT to attempt

### E.1 — Do NOT attempt Phase C

Phase C (`∀ n, 1 ≤ n → cInverseLog n < 0`) requires proving sign
properties of the dual `d` series and a strong-induction argument over
`n`. This is its own ~80–150 LOC deliverable. **Strict scope:** ship
Phase B (definition + identity + base cases), document Phase C as the
cycle 238+ entry point in `lem_441B_misinterpretation.md`.

### E.2 — Do NOT attempt Φ as a homomorphism (`thm:384A`)

`Equivalent → PhiEquivalent` is **multi-cycle** B-series
infrastructure. See `.prover-state/issues/thm_381H_deferred.md`
deferred directions (1) and (3). No single-cycle path exists. **Do
not** sorry-scaffold `thm:384A` either — sorry-first scaffolds for
multi-cycle blockers got rolled back in cycles 138, 149, 200; the
supervisor scores sorry increase at −2.

### E.3 — Do NOT pursue any B-series-dependent entity

Avoid: `thm:343B`, `thm:323B`, `thm:534A`, `thm:541A`, `thm:551B`,
`def:422B`, `def:442A`, `lem:310B`, `lem:311A`, `lem:312B`,
`lem:313A`, `thm:311D`, `thm:313B`, `thm:317A`, `thm:315A`. All
require B-series infrastructure that is genuinely multi-cycle.

### E.4 — Do NOT attempt §441 Phase C.2 (GPFS-blocked)

Per `.prover-state/issues/cycle_182_gpfs_slowness.md`, Section441.lean
has been GPFS-blocked for **41 consecutive cycles** spanning ~50
calendar days. The cycle 182 draft (with cycle 184 namespace fix) is
preserved at `.prover-state/cycle_182_draft_section441.lean` — do
not re-attempt local compilation. **Do** run the §C smoke test once at
cycle start (a single 60s `timeout` invocation), but if it fails (it
will), do not retry. Loop-maintainer escalation is in force.

### E.5 — Do NOT cherry-pick easy entities

Stick with `lem:441B` Phase B. Do not pivot to a smaller deliverable
mid-cycle unless §F.5 (Mathlib gap) genuinely fires.

### E.6 — Do NOT add an n=8 stepping stone for `thm:550A`

Per cycle 150 task results, "the seven-`n` data set is now strong
enough that further stepping stones (n = 8) provide marginal value;
effort should pivot." The general-`n` proof is multi-cycle Aristotle
or cofactor-induction work. Do not regress to n=8.

### E.7 — Do NOT modify `scripts/autonomous_loop.py`

Per CLAUDE.md, scanner / prompt-builder bugs are loop-maintainer
territory. The standing `tautology_scanner_false_positives.md` and
`phantom_commit_verdict_pattern.md` issues are escalation records;
do not patch the supervisor.

### E.8 — Do NOT introduce `axiom` or `constant`

Per CLAUDE.md. Phase B is genuinely formalisable in Mathlib's
`PowerSeries` ring; no axioms needed. If a specific Mathlib API is
missing, build it as a private helper lemma in the same file.

### E.9 — Do NOT raise `maxHeartbeats`

Per CLAUDE.md. Phase B's largest proof (the `cInverseLog_recurrence`)
should fit within default heartbeats; if it doesn't, decompose into
two narrower lemmas (the `X^(2n)`-coefficient extraction and the
recurrence rearrangement).

### E.10 — Do NOT redo cycle 171's mistake

Cycle 171 conflated Sequence 1 (`aᵢ`, the LMM-dependent `aPoly`
coefficients) with Sequence 2 (`c_{2i}`, the universal series
inversion). Per the issue file, Phase B's `cInverseLog : ℕ → ℝ`
function takes ONLY a `ℕ` argument; it must NOT take a
`LinearMultistepMethod k` parameter. If you find yourself writing
`M.cInverseLog n` or `LinearMultistepMethod.cInverseLog`, STOP and
re-read `lem_441B_misinterpretation.md`.

## §F — Risk register (R1–R7)

### R1 — `PowerSeries.invOfUnit` API surface

Mathlib has `PowerSeries.invOfUnit` (in
`Mathlib.RingTheory.PowerSeries.Inverse`) requiring the constant
coefficient to be a unit. Verify by `lean_local_search "PowerSeries.invOfUnit"`
or `lean_loogle "PowerSeries.inv"` at the start of the cycle. If the
exact API name has drifted (renamed to `PowerSeries.inv'` or similar),
adjust accordingly. **Mitigation**: an alternative is hand-rolling
`cSeries` as `PowerSeries.mk fun n => recurrence(n)` and proving
`cInverseLogSeries * cSeries = 1` separately via `PowerSeries.ext` +
strong induction.

### R2 — Even/odd indexing

The textbook `c_{2i}` indexing assumes only even-indexed coefficients
are nontrivial. Two encoding choices:
- (a) `cInverseLogSeries = PowerSeries.mk fun n => if Even n then 2/(n+1) else 0`
  and `cInverseLog n := PowerSeries.coeff ℝ (2*n) cSeries`.
- (b) Define a "compressed" series in even-indexed coefficients only
  via a substitution `X ↦ X²`. Mathlib has `PowerSeries.subst` or
  similar.

Recommendation: (a) — simpler, no substitution machinery. The odd
coefficients of `cSeries` will be zero by symmetry of the equation,
which is provable as a corollary if needed.

### R3 — Recurrence form for `cInverseLog_recurrence`

The cleanest form is the **explicit closed-form `c_{2n}` recurrence**:
```
2·c_{2n} = - ∑_{i=1}^{n} (2/(2i+1)) · c_{2(n-i)}.
```

But proving this *as a single statement* requires extracting the
coefficient of `X^(2n)` from `cInverseLogSeries * cSeries = 1`,
which involves a `Finset.range (2n+1)` sum that has zero contributions
at odd indices. **Mitigation**: factor out the odd-indexing collapse
as a private helper, then state the cleaner even-only form.

If even-indexing collapse proves nontrivial (likely), settle for the
**raw form**:
```
∀ n, 0 = ∑ i in Finset.range (2n+1),
  (cInverseLogSeries.coeff ℝ i) * cSeries.coeff ℝ (2n - i).
```
which is a direct application of `PowerSeries.coeff_mul`.

### R4 — Powers of `PowerSeries`

If the proof needs `cInverseLogSeries^k` (e.g. for cleaner
induction), Mathlib's `PowerSeries.pow` is in
`Mathlib.RingTheory.PowerSeries.Basic`. Should not be load-bearing
for Phase B.

### R5 — Mathlib gap (low risk)

If Mathlib's `PowerSeries` lacks `invOfUnit` (unlikely; this is a
classical construction), we can hand-roll the inverse via
`PowerSeries.mk` with an explicit recurrence and prove
`cInverseLogSeries * cSeries = 1` by `PowerSeries.ext` +
`PowerSeries.coeff_mul` + induction. This adds ~50 LOC but is
mechanical.

### R6 — `Even n` predicate timing

`Even n` vs `n.bodd` — Mathlib uses both. The cleaner form for
`if`-then-`else` in the series definition is `Even n` from
`Mathlib.Data.Nat.Parity`. Decidability is automatic.

### R7 — File placement (Section441.lean vs Section441B.lean)

Per §C: if §C's GPFS smoke test passes (against expectation), extend
Section441.lean. If it fails (the 42nd consecutive timeout — almost
certain), create `OpenMath/Chapter4/Section441B.lean` and add
`import OpenMath.Chapter4.Section441B` to `OpenMath/Chapter4.lean`.
The `cInverseLog` machinery is pure ℝ-PowerSeries — no Section441
dependencies — so file split is clean. Update
`OpenMath/Chapter4.lean` accordingly.

## §G — Scoping recipe (start of cycle)

1. **Read** `.prover-state/issues/lem_441B_misinterpretation.md`
   (full diagnosis).
2. **Read** `.prover-state/issues/cycle_182_gpfs_slowness.md`
   (status of the 41-cycle GPFS streak — informs §C decision).
3. **Read** `extraction/raw_text/ch04.txt:1947–2030` (textbook §441
   verbatim).
4. **Verify Mathlib API** for `PowerSeries.invOfUnit` /
   `PowerSeries.coeff_mul` / `PowerSeries.constantCoeff`. Use
   `lean_local_search` once for each (cheap rate-limited operations).
5. **GPFS smoke test** (one-shot): `time timeout 60 lake env lean
   OpenMath/Chapter4/Section441.lean`. If it completes, extend
   Section441.lean. If it times out (expected), use Section441B.lean.
6. **Submit Aristotle batch** (5 jobs per §B.Aristotle) at the start
   of the cycle — do NOT block on it; proceed with hand-written
   Phase B work.

## §H — Aristotle batch template

For each of the 5 jobs, submit a self-contained Lean snippet
including:
- `import Mathlib.RingTheory.PowerSeries.Inverse`
- `import Mathlib.Data.Nat.Parity`
- The `cInverseLogSeries`, `cSeries`, `cInverseLog` definitions
  (verbatim from §B.1–§B.4)
- The target lemma signature with `sorry` body
- A docstring naming the §441 (441c) identity it derives from

Aristotle SHOULD handle Job 1 (constant coefficient) and Jobs 2/3
(base-case computations) easily. Job 4 (recurrence) is the
substantial deliverable; if Aristotle struggles, the manual proof
recipe in §B.7 + R3 is the fallback.

## §I — Pre-commit checklist (CLAUDE.md mandatory)

For each new `def` / `theorem` introduced this cycle:

1. **Quote the textbook statement** for `lem:441B` (from
   `extraction/formalization_data/entities/lem_441B.json`):
   > "The coefficients c₂, c₄, … are all negative."
   And the (441c) identity:
   > "(2 + (2/3)z² + (2/5)z⁴ + ⋯)(c₀ + c₂z² + c₄z⁴ + ⋯) = 1."

2. **Match the Lean definition to the textbook**:
   - `cInverseLogSeries`: matches the LHS of (441c).
   - `cSeries`: defined as the inverse, satisfying (441c) by
     construction.
   - `cInverseLog`: extracts `c_{2n}` for n ≥ 0.

3. **Faithfulness divergence**: NONE for Phase B. The definitions
   and the (441c) identity match the textbook exactly. The
   negativity claim (Phase C) is deferred.

4. **Tautology check**: `cInverseLog_zero_eq_half`'s body should
   genuinely compute `1/2`, not be a circular `:= 1/2 := rfl`. Use
   `simp [cInverseLog, cSeries, ...]` plus `PowerSeries.constantCoeff`
   API to derive the value.

5. **Identity check**: the (441c) identity proof (`cSeries`
   construction) should NOT be `id` or a one-line `rfl` — it should
   genuinely invoke `PowerSeries.invOfUnit` or hand-rolled
   `PowerSeries.ext` + `PowerSeries.coeff_mul`.

6. **Hypothesis strength check**: `cInverseLog_recurrence` should
   take *only* `n ≥ 1` as a hypothesis (or `0 < n`), not extra
   assumptions like "the recurrence is well-founded" — those should
   be proved internally, not hypothesised.

7. **Absent theorem check**: the docstring should reference
   `lem:441B` and the (441c) equation, but should NOT claim Phase
   C results that aren't yet proved.

## §J — Task results template

Update `.prover-state/task_results/cycle_237.md`:
- **Worked on**: `lem:441B` Phase B (PowerSeries definition +
  identity + base cases).
- **Result**: SUCCESS / PARTIAL / FAILED — with itemised theorem
  list and axiom-cleanliness verification.
- **Faithfulness check**: per §I above.
- **Discovery**: any Mathlib API surface notes (R1, R3, R5).
- **Suggested next approach**: Phase C (negativity proof) for
  cycle 238 if Phase B lands cleanly. Otherwise: extend Phase B
  with whatever didn't fit.

## §K — `lean_status.json` and `plan.md` updates

If Phase B ships axiom-clean:
- `lean_status.json` row for `lem:441B`: `unformalized` → `partial`,
  `lean_symbol`: `cInverseLog_recurrence` (the headline), `cycle: 237`.
- `plan.md` `lem:441B` row: `[ ]` → `[~]` with cycle 237 note
  describing Phase B closure and Phase C deferral.

If Phase B partially ships (e.g. only definition + base cases, no
recurrence proof):
- `lean_status.json` and `plan.md`: still `partial` / `[~]`, cycle
  237, document the partial scope clearly.

If Phase B fails entirely:
- Do not change `lean_status.json` or `plan.md`. Document the
  failure mode in `cycle_237.md` and update
  `lem_441B_misinterpretation.md` with the new failure analysis.

## §L — Backup plans (in priority order)

If Phase B's PowerSeries inversion proves harder than expected and
~75% of the cycle has elapsed without progress:

### Backup B1 — Ship just the definition + base cases

Drop the (441c) identity proof and `cInverseLog_recurrence`. Ship:
- `cInverseLogSeries`
- `cInverseLogSeries_constantCoeff_eq_two`
- `cInverseLog 0 = 1/2` via direct computation (independent of
  `cSeries`'s inversion — use `PowerSeries.coeff_zero_eq_constantCoeff`
  on `cInverseLogSeries * cSeries = 1`).

This is ~30 LOC, axiom-clean. The (441c) recurrence comes in cycle
238 once the inversion API is well-understood.

### Backup B2 — Pivot to a documentation-only deliverable

Document the §441 cluster's status in
`lem_441A_phase_C_scoping.md`'s sibling location, summarising what
remains across `lem:441A` Phase C, `lem:441B`, `thm:441C`, `thm:443A`,
`thm:443B`. Open issues for any not yet documented. This is
zero-risk pivot territory if Phase B genuinely fails.

### Backup B3 — Definition-only Chapter 5 entity

If §441 entirely fails, look at small Chapter 5 stretch witnesses:
- An r=5 extension of the cycle 161 padded-Euler witness pattern
  (mechanical lift, ~150 LOC). NOT a substantive new entity, but
  satisfies the no-empty-cycle rule.
- Adding a referenced computation in
  `OpenMath/Chapter4/Section410.lean` consuming existing
  generating-polynomial infrastructure.

## §M — End-of-cycle deliverable summary

By the end of cycle 237:

1. **Section441.lean** (or Section441B.lean): +5 to +7 new public
   declarations, all axiom-clean. Sorry count: 0 (unchanged).
2. **`lean_status.json`**: `lem:441B` row updated.
3. **`plan.md`**: `lem:441B` row updated.
4. **`.prover-state/task_results/cycle_237.md`**: per §J template.
5. **`.prover-state/issues/lem_441B_misinterpretation.md`**: append
   "Cycle 237 update — Phase B SHIPPED" section.
6. **Aristotle**: 5-job batch submitted at cycle start, single poll
   at cycle end (per CLAUDE.md), incorporated where applicable.
7. **GPFS issue**: append the 42nd consecutive timeout to
   `cycle_182_gpfs_slowness.md` (single-line update).

The cycle satisfies CLAUDE.md's minimum-progress rule with margin
even if only Backup B1 ships (definition + base cases is non-trivial
Mathlib `PowerSeries` work).
