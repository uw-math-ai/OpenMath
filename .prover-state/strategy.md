# Cycle 275 Strategy — §342 Aristotle poll + (342d) n=2 manual fallback

## Status entering cycle 275

- **Section342.lean**: 386 LOC, 0 sorries, axiom-clean (cycle 274).
- **Shipped so far**: (342b) `P_n^*(1)=1`, (342c) parity, (342e)
  Rodrigues, (342d) at `n=0` and `n=1`, plus helpers
  (`butcherShiftedLegendre_zero` = `C 1`,
  `butcherShiftedLegendre_one` = `C 2 * X - C 1`,
  `butcherShiftedLegendre_eval_zero` = `(-1)^n`, `natDegree = n`).
- **Two Aristotle projects pending**:
  - `727396d5-14f9-4014-9aad-1f38238a1651` — (342a) orthogonality.
    Created 2026-05-15T12:59. Last poll (cycle 274): IN_PROGRESS 18%.
  - `d4ce527b-b714-4e51-b0a6-e3d06302d7fa` — general (342d)
    norm-square. Created 2026-05-15T13:24. Submitted in cycle 274;
    not yet polled.

## Priority 1 — Single-poll Aristotle (mandatory, ~5 min)

**Run exactly once** at the start of the cycle. Do NOT re-poll.

```
mcp__aristotle__get_status(project_id="727396d5-14f9-4014-9aad-1f38238a1651")
mcp__aristotle__get_status(project_id="d4ce527b-b714-4e51-b0a6-e3d06302d7fa")
```

### Branch decision tree

| Case | Action |
|---|---|
| Either project `COMPLETED` | Go to Priority 2 (incorporate). |
| Both `IN_PROGRESS` or `QUEUED` | Skip Priority 2. Go straight to Priority 3 (manual `n=2` ship). |
| Either `FAILED` / `COMPLETED_WITH_ERRORS` | Read `ARISTOTLE_SUMMARY.md` via `extract_result`; if a one-line namespace/import fix is identifiable (like cycle 184's pattern), apply it and re-submit; otherwise treat as IN_PROGRESS for branching. |

**Do not wait for Aristotle.** Per CLAUDE.md "one check after 30 min
is enough". Both projects have been running ≥18 h; if they haven't
completed by now, they may take several more cycles.

## Priority 2 — Incorporate any COMPLETED Aristotle result

### If (342a) project `727396d5` returned COMPLETED

The submission targeted `butcherShiftedLegendre_orthogonal` with the
cycle 271–273 prerequisites as named axioms. To integrate:

1. `mcp__aristotle__extract_result(project_id="727396d5...")` and
   read the returned proof file.
2. Replace any `axiom` lines in the returned proof with citations to
   real shipped theorems (`butcherShiftedLegendre_rodrigues`,
   `butcherShiftedLegendre_natDegree`,
   `butcherShiftedLegendre_eval_one`, etc.).
3. Open `OpenMath/Chapter3/Section342.lean` and add the theorem
   (preserve docstring; cite "Butcher (342a)"). Place after the
   cycle 274 norm-square instances.
4. Verify via `mcp__lean-lsp__lean_diagnostic_messages` on the
   updated file. Fix any namespace-resolution errors inline.
5. Verify axiom-cleanness via `lean_verify` on the new theorem name.
   Expected: `[propext, Classical.choice, Quot.sound]`.
6. Update `lean_status.json` row for `lem:342A`: cycle bumped to 275;
   the lemma remains `partial` (other clauses still incomplete) but
   note (342a) as shipped in the cycle-trace string.
7. Update `plan.md` `lem:342A` row similarly.

### If (342d) project `d4ce527b` returned COMPLETED

Same recipe with target `butcherShiftedLegendre_norm_square`. The
expected strategy is Rodrigues + iterated IBP + Beta integral
identity `∫₀¹ x^n (1-x)^n dx = (n!)² / (2n+1)!`.

**Sanity check the n=0 and n=1 special cases** against the new
general theorem — cycle 274's shipped `butcherShiftedLegendre_norm_sq_zero`
and `_one` should specialise from the general statement. Add a
non-vacuity witness exhibiting the specialisation.

### If both COMPLETED simultaneously

Integrate (342a) first (it's older and has the cleaner Rodrigues
template), then (342d). If only one fits in the cycle budget, defer
the second to cycle 276.

## Priority 3 — Manual ship of (342d) at `n=2` (target if Aristotle not ready)

If neither Aristotle job completed, ship `∫₀¹ (P_2^*(x))^2 dx = 1/5`
following the cycle 274 template. This continues the (342d) ladder
one rung further and provides a useful test case for whenever the
general Aristotle proof lands.

### Step 3a — Add expansion lemma `butcherShiftedLegendre_two`

Mirror cycle 273's `butcherShiftedLegendre_zero` and
`butcherShiftedLegendre_one` recipes.

`P_2^*(x) = 6x² - 6x + 1` (Butcher Table 312(I), p. 197, also
deducible from Rodrigues at n=2: `(1/2!)·D²((x²-x)²) = 6x² - 6x + 1`).

Verify the coefficient table via `lean_multi_attempt` before writing
the full proof.

```lean
theorem butcherShiftedLegendre_two :
    butcherShiftedLegendre 2 = Polynomial.C 6 * Polynomial.X ^ 2
      - Polynomial.C 6 * Polynomial.X + Polynomial.C 1 := by
  apply Polynomial.ext
  intro k
  unfold butcherShiftedLegendre
  match k with
  | 0 => simp [Polynomial.coeff_shiftedLegendre, ...]; ring
  | 1 => simp [...]; ring
  | 2 => simp [...]; ring
  | k + 3 =>
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · ...
    · simp [...]
```

If `Polynomial.ext` + per-coefficient `match` stalls (cycles 172/173
precedent), fallback to `Polynomial.funext` + `ring` (cycle 180 BDF2
recipe).

### Step 3b — Ship `butcherShiftedLegendre_norm_sq_two`

Mirror cycle 274's `butcherShiftedLegendre_norm_sq_one` structure
but with the cubic-expanded integrand `(6x² - 6x + 1)² = 36x⁴ - 72x³
+ 48x² - 12x + 1`:

```lean
theorem butcherShiftedLegendre_norm_sq_two :
    ∫ x in (0:ℝ)..1, (butcherShiftedLegendre 2).eval x ^ 2 = 1 / 5 := by
  have heq : ∀ x : ℝ, (butcherShiftedLegendre 2).eval x ^ 2
             = 36 * x^4 - 72 * x^3 + 48 * x^2 - 12 * x + 1 := by
    intro x
    rw [butcherShiftedLegendre_two]
    simp; ring
  rw [intervalIntegral.integral_congr (fun x _ => heq x)]
  -- Split via integral_add / integral_sub / integral_const_mul.
  -- Close with integral_pow for ∫₀¹ x^k at k = 1, 2, 3, 4.
  ...
  norm_num
```

The closed-form values:
- `∫₀¹ x⁴ dx = 1/5`
- `∫₀¹ x³ dx = 1/4`
- `∫₀¹ x² dx = 1/3`
- `∫₀¹ x  dx = 1/2`
- `∫₀¹ 1  dx = 1`

Then `36·(1/5) - 72·(1/4) + 48·(1/3) - 12·(1/2) + 1 = 7.2 - 18 + 16
- 6 + 1 = 0.2 = 1/5`. ✓

Confirm `1 / (2·2 + 1) = 1/5` matches the closed form.

### Step 3c — Non-vacuity witness

```lean
example : (1 : ℝ) / (2 * 2 + 1) = 1 / 5 := by norm_num

example : ∫ x in (0:ℝ)..1, (butcherShiftedLegendre 2).eval x ^ 2
          = 1 / (2 * 2 + 1) := by
  rw [butcherShiftedLegendre_norm_sq_two]; norm_num
```

### LOC budget for P3

- `butcherShiftedLegendre_two`: ~30 LOC.
- `butcherShiftedLegendre_norm_sq_two`: ~50–70 LOC (the quartic has
  5 monomials to integrate, slightly worse than cycle 274's
  quadratic).
- Non-vacuity witness: ~3 LOC.

Total: **~80–100 LOC**. Well within the cycle budget.

## Priority 4 — Stretch (only if P3 ships with margin)

If P3 closes cleanly with time remaining, attempt:

- **`butcherShiftedLegendre_three`**: `P_3^*(x) = 20x³ - 30x² + 12x - 1`.
  Just the expansion lemma, no integral. Continues the ladder one
  more rung. ~30 LOC.

Do NOT attempt:
- (342f) recurrence — Pascal-style binomial identities required;
  cycle 273 confirmed `ring` cannot close them.
- (342g) real-zeros-in-(0,1) — requires complex analysis machinery.
- (342d) `n=3` norm-square — the quintic expansion grows; better
  to let Aristotle's general proof handle higher n.

## What NOT to try

- **Do NOT re-poll Aristotle within the cycle.** Per CLAUDE.md, one
  check is enough.
- **Do NOT attempt the general (342d) manual proof.** Cycle 274
  determined the four-piece audit (iterated IBP × n, boundary
  vanishing, `(d/dx)^n P_n^*` constant extraction, real Beta integral)
  is over budget. Aristotle is the right path.
- **Do NOT attempt (342f) recurrence.** Per cycle 273 attempts.md:
  "Both `Polynomial.ext` (coefficient route) and `Polynomial.funext`
  (eval route) require Pascal-style binomial identities on
  `Nat.choose` that `ring` cannot close." Do not retry without
  (342a) in hand.
- **Do NOT attempt (342g)**. Requires complex analysis machinery
  not yet built.
- **Do NOT touch Section441.lean.** GPFS timeout pathology persists
  (43+ consecutive timeouts since cycle 182). Skip per the standing
  blocker in `cycle_182_gpfs_slowness.md`.
- **Do NOT introduce sorries.** Cycle 274's bar was 0 sorries
  axiom-clean. Cycle 275 must match.
- **Do NOT increase maxHeartbeats above 200000.** Decompose instead.
- **Do NOT pivot to a fresh entity.** The §342 path is showing steady
  progress; both Aristotle jobs are live; cycle 275's bar is one more
  rung on the (342d) ladder or successful integration of an Aristotle
  result. Pivoting now risks abandoning two Aristotle deliverables
  that may complete within 1–3 cycles.

## Build commands

```bash
# Single-file verify
lake env lean OpenMath/Chapter3/Section342.lean

# Axiom check (per new theorem)
echo '#print axioms OpenMath.Chapter3.Section342.butcherShiftedLegendre_norm_sq_two' \
  | lake env lean --stdin OpenMath/Chapter3/Section342.lean
# Expected: [propext, Classical.choice, Quot.sound]
```

## Cycle 275 task results file

Write `.prover-state/task_results/cycle_275.md` per CLAUDE.md format.
Include:
- Aristotle poll results (verbatim status snippets for both projects).
- For each new theorem: entity ID, textbook clause it captures,
  faithfulness check, axioms.
- Updated `lean_status.json` cycle reference.
- Suggested next approach for cycle 276 (likely: continue (342d)
  ladder OR re-poll Aristotle).

## Commit message template

If Aristotle landed:
```
Cycle 275 — §342 (342a)/(342d) Aristotle integration SHIPPED.
```

Otherwise:
```
Cycle 275 — §342 (342d) n=2 case + butcherShiftedLegendre_two SHIPPED.
```
