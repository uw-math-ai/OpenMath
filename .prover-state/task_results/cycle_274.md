# Cycle 274 Results

## Worked on

* **P1**: Single-poll of Aristotle project `727396d5-14f9-4014-9aad-1f38238a1651`
  (cycle 273's (342a) orthogonality submission).
* **P3 (modified)**: Manually shipped concrete `n = 0` and `n = 1`
  cases of Butcher §342 (342d) — the norm-square integral identity
  `∫₀¹ (P_n^*(x))^2 dx = 1/(2n+1)`. General `n` deferred to Aristotle.
* **P3 fallback**: Submitted general (342d) to Aristotle as project
  `d4ce527b-b714-4e51-b0a6-e3d06302d7fa`.

## Approach

### P1 — Aristotle poll for (342a)

Single `mcp__aristotle__get_status` call per CLAUDE.md discipline.
Result verbatim:

```
{
  "project_id": "727396d5-14f9-4014-9aad-1f38238a1651",
  "status": "IN_PROGRESS",
  "created_at": "2026-05-15T12:59:00.909286",
  "last_updated_at": "2026-05-15T13:16:35.923798",
  "percent_complete": 18,
  "file_name": "342a_orthogonality.lean"
}
```

Per strategy §B.P1 branching: `IN_PROGRESS` → skip P2a, proceed to P3
without integrating any Aristotle output. No re-polling within the
cycle.

### P3 modified — concrete (342d) cases at `n = 0` and `n = 1`

Reviewed Mathlib for the four heavy-lifting pieces required by general
(342d):

1. **Iterated IBP × n**: `intervalIntegral.integral_mul_deriv_eq_deriv_mul`
   exists for a single step, but iterating `n` times is a substantive
   induction (~40 LOC helper).
2. **Boundary-term vanishing** for `D^k (X^n (1-X)^n)` at endpoints
   for `k < n`: requires a separate lemma by induction on `k`
   (~30 LOC).
3. **`(d/dx)^n P_n^*` as a constant**: needs `Polynomial.coeff_shiftedLegendre`
   bookkeeping and the leading-coefficient extraction.
4. **Real Beta integral** `∫₀¹ x^n (1-x)^n dx = (n!)^2 / (2n+1)!`:
   Mathlib has `Complex.betaIntegral` (complex `cpow` form) but no
   direct real-coefficient version for natural-number exponents.
   Casting through `cpow` requires nontrivial type juggling.

Given the LOC budget (60–120 LOC per strategy §B.P3) and the four
load-bearing pieces, full manual ship is over budget. Instead, ship
concrete `n = 0` and `n = 1` cases (real mathematical content, not
just non-vacuity witnesses) and fall back to Aristotle for the
general statement per strategy §B.P3 risk plan.

The two cases:

* `butcherShiftedLegendre_norm_sq_zero : ∫₀¹ (P_0^*(x))^2 dx = 1`
  — direct, using `butcherShiftedLegendre_zero` (P_0^* = C 1) and
  `intervalIntegral.integral_const`. ~8 LOC.
* `butcherShiftedLegendre_norm_sq_one : ∫₀¹ (P_1^*(x))^2 dx = 1/3`
  — uses `butcherShiftedLegendre_one` (P_1^* = 2X - 1), reduces to
  `∫₀¹ (4x² - 4x + 1) dx` via pointwise rewrite, then splits via
  `intervalIntegral.integral_add` / `integral_sub` / `integral_const_mul`
  and closes with `integral_pow` + `integral_one`. ~30 LOC.

Both confirm Butcher's closed form: `1 / (2·0 + 1) = 1` and
`1 / (2·1 + 1) = 1/3`. Two non-vacuity witnesses added showing the
match.

### P3 fallback — Aristotle submission for general (342d)

Built `.prover-state/aristotle_submissions/cycle_274/342d_norm_square.lean`
exposing cycles 271–273's prerequisites as named axioms (Rodrigues,
parity, natDegree, eval-one, eval-zero, P_0/P_1 expansions) so
Aristotle can cite them directly. Verified the file compiles standalone
(only warning: declaration uses `sorry`).

Submitted to Aristotle. Returned project ID
`d4ce527b-b714-4e51-b0a6-e3d06302d7fa` (status QUEUED).

## Result

**SUCCESS** — Cycle 274 deliverables:

1. **(342d) `n = 0` case**: `butcherShiftedLegendre_norm_sq_zero`
   shipped axiom-clean (`[propext, Classical.choice, Quot.sound]`).
2. **(342d) `n = 1` case**: `butcherShiftedLegendre_norm_sq_one`
   shipped axiom-clean (`[propext, Classical.choice, Quot.sound]`).
3. **Two non-vacuity witnesses** confirming the closed-form RHS
   `1 / (2n + 1)` at `n = 0, 1`.
4. **One new import**: `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`
   (for `integral_pow`, `integral_one`, `intervalIntegral.integral_const`).
5. **Aristotle submission `d4ce527b`** for general (342d), running.
6. **Aristotle project `727396d5`** for (342a) still IN_PROGRESS at 18%.

Sorry count remains 0 in `OpenMath/Chapter3/Section342.lean`.
Verified via `lean_diagnostic_messages` and per-theorem
`lean_verify`.

## Faithfulness check

### `butcherShiftedLegendre_norm_sq_zero`

- Entity ID: `lem:342A`, clause (342d), instance at `n = 0`.
- Textbook statement (quoted from `lem_342A.json`):
  > `∫_0^1 P_n^*(x)^2 \, dx = \frac{1}{2n + 1}, \quad n = 0, 1, 2, \dots`
- Lean statement captures: **same content at `n = 0`** — Lean proves
  `∫ x in (0:ℝ)..1, (butcherShiftedLegendre 0).eval x ^ 2 = 1`,
  which is the `n = 0` instance of Butcher's (342d) since
  `1 / (2 · 0 + 1) = 1`. A separate non-vacuity witness confirms
  the match to the closed form `1 / (2n + 1)`.
- Hypotheses: none beyond the polynomial definition.
- Identity check: the proof is **not** `exact h` — it
  rewrites `P_0^* = C 1` (`butcherShiftedLegendre_zero`, cycle 273)
  and integrates the constant `1` via `intervalIntegral.integral_const`.

### `butcherShiftedLegendre_norm_sq_one`

- Entity ID: `lem:342A`, clause (342d), instance at `n = 1`.
- Textbook statement: same as above.
- Lean statement captures: **same content at `n = 1`** — Lean proves
  `∫ x in (0:ℝ)..1, (butcherShiftedLegendre 1).eval x ^ 2 = 1 / 3`,
  which is the `n = 1` instance of Butcher's (342d) since
  `1 / (2 · 1 + 1) = 1/3`. A separate non-vacuity witness confirms
  the match to the closed form.
- Hypotheses: none beyond the polynomial definition.
- Identity check: the proof is **not** `exact h` — it rewrites
  `P_1^* = 2X - 1` (`butcherShiftedLegendre_one`, cycle 273), expands
  `(2x-1)^2 = 4x^2 - 4x + 1` via `simp` + `ring`, splits the integral
  via `intervalIntegral.integral_add` / `integral_sub` /
  `integral_const_mul`, and closes via `integral_pow` (for `∫₀¹ x^2`)
  and explicit derivation of `∫₀¹ x = 1/2` from `integral_pow`.
- Tautology check: conclusion `= 1/3` is not equal to any hypothesis.

### `342d` Aristotle submission

Standalone file in `.prover-state/aristotle_submissions/cycle_274/`.
Axioms are explicit and reflect cycles 271–273's *real* shipped
theorems. Per cycle 273 precedent: when Aristotle's result is
integrated (cycle 275+), the axioms will be replaced by direct
citations to the proven theorems in `Section342.lean`.

## Dead ends

* **Full general (342d) manual ship**: declined after the four-piece
  Mathlib audit. The real Beta integral for natural exponents is
  not directly available (only `Complex.betaIntegral` with `cpow`),
  and the iterated-IBP + boundary-vanishing scaffold pushes total
  LOC well over the 120 LOC budget. Per strategy §B.P3 risk
  mitigation: bail to Aristotle.
* **Initial `linarith` closure** of the `∫₀¹ x` lemma: failed because
  `simp` had reduced the `integral_pow` output beyond `linarith`'s
  reach. Replaced with an explicit `simp only [pow_one, Nat.cast_one]`
  followed by `rw` + `norm_num`.

## Discovery

* **Mathlib's Beta integral is complex-only**: `Complex.betaIntegral u v`
  uses `cpow` and is typed in `ℂ`. There is no direct real-valued
  `∫₀¹ x^m (1-x)^n dx = m! n! / (m+n+1)!` lemma for natural exponents
  in Mathlib, which makes (342d)'s last step nontrivial. A future
  cycle could ship this as a reusable helper in `OpenMath/` (or
  upstream to Mathlib).
* **`integral_pow` `Nat.cast` artifact**: `integral_pow n` produces
  `(b^(n+1) - a^(n+1)) / (↑n + 1)` with a `Nat.cast` on the
  denominator. For `n = 1`, `↑1 + 1 = 2 : ℝ` reduces via
  `Nat.cast_one`, not directly via `simp` defaults. Recorded as a
  quirk for future polynomial-integral proofs.
* **`butcherShiftedLegendre_zero` and `butcherShiftedLegendre_one`
  are highly reusable**: cycle 273's expansion lemmas for
  `P_0^* = C 1` and `P_1^* = C 2 * X - C 1` made the `n = 0, 1`
  cases of (342d) immediate. The same template should work for
  any subsequent small-`n` instance check.

## Suggested next approach

### Cycle 275 P1 (likely)

Poll BOTH Aristotle projects:

* `727396d5-14f9-4014-9aad-1f38238a1651` — (342a) orthogonality
  (created 2026-05-15T12:59).
* `d4ce527b-b714-4e51-b0a6-e3d06302d7fa` — (342d) norm-square
  (created 2026-05-15T13:24).

Per Aristotle precedent (cycle 273 (342e) Rodrigues took ~24 h to
COMPLETE), both should be deliverable by cycle 275–277. Integrate
whichever completes first.

### Cycle 275 P2 (if no Aristotle hits)

The most tractable manual path remaining is **(342f)** the three-term
recurrence, but it is gated on **(342a)** orthogonality per Butcher's
proof sketch. So if neither Aristotle job has landed by cycle 275, the
next manual option is the **`n = 2`** instance of (342d):
`∫₀¹ (P_2^*(x))^2 dx = 1/5` — direct polynomial integration following
the cycle 274 template, requires a `butcherShiftedLegendre_two`
expansion lemma `P_2^*(x) = 6x^2 - 6x + 1`. This would extend the
(342d) ladder by one rung.

### Alternative pivot

§310/§311 Phase A.1 (`RootedTree.Vertex` scaffold per
`lem_310B_plan.md`) remains a viable alternative if both §342 Aristotle
jobs stall. The relevant data lives in `.prover-state/`.

## Cycle 274 closure summary

| Deliverable | Status |
|---|---|
| P1 (Aristotle poll) | ✓ DONE — IN_PROGRESS 18% |
| P2a (integrate (342a)) | SKIPPED — Aristotle not yet COMPLETE |
| P2b (salvage) | N/A — no errors to salvage |
| P3 (manual (342d)) | PARTIAL — `n = 0` and `n = 1` cases shipped |
| P3 fallback (Aristotle (342d)) | ✓ DONE — `d4ce527b` submitted |
| P4 (non-vacuity stretch) | ✓ DONE — 2 closed-form match witnesses |

Sorries: **0** in `OpenMath/Chapter3/Section342.lean`.
Axioms: only `[propext, Classical.choice, Quot.sound]`.
