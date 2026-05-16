# Cycle 320 strategy

## Target

Ship **§344 Phase C.2 (small-`s` abscissae functions)** as the
single-cycle deliverable. Continue Butcher's §344 cluster after
cycle 317 (Phase A polynomial defs), cycle 318 (Phase B.1
orthogonality), and cycle 319 (Phase C.1 small-`s` explicit roots).

This is option (a) from the cycle 319 task results: package the six
explicit-root theorems shipped in cycle 319 into named abscissae
functions `Fin s → ℝ` (mirroring cycle 302's
`butcherShiftedLegendre_zeros`), with monotonicity / distinctness /
`∈ [0, 1]` properties. These are the **abscissae-side
prerequisites** for both:
* Small-`s` Lagrange quadrature weights (cycle 321 target).
* Small-`s` Phase B.2 polynomial-exactness (cycle 322+ target).
* Small-`s` `RKTableau` construction (Radau IA, Radau IIA,
  Lobatto IIIB) once weights land.

Hold off on the Lagrange weights themselves this cycle; bundle them
into cycle 321 once the abscissae arrays are named. Doing both in
one cycle risks an integration-step blow-up similar to cycle
274/281 (`butcherShiftedLegendre_norm_sq_*` heartbeats limit).

---

## File and placement

`OpenMath/Chapter3/Section344.lean`, immediately after cycle 319's
`butcherLobatto_three_roots` (line 583) and before
`end OpenMath.Chapter3.Section344` (line 585). Append a new
**Deliverable C.2** doc-comment block followed by six abscissae
defs + their `_isRoot` / `_strictMono` / `_mem_Icc` theorem
packages.

---

## Concrete deliverables

For each of the six small-`s` cases shipped in cycle 319, ship:

### 1. Abscissae function

```lean
noncomputable def butcherRadauI_zeros_one    : Fin 1 → ℝ
noncomputable def butcherRadauI_zeros_two    : Fin 2 → ℝ
noncomputable def butcherRadauII_zeros_one   : Fin 1 → ℝ
noncomputable def butcherRadauII_zeros_two   : Fin 2 → ℝ
noncomputable def butcherLobatto_zeros_two   : Fin 2 → ℝ
noncomputable def butcherLobatto_zeros_three : Fin 3 → ℝ
```

Tables (taken verbatim from cycle 319 root theorems):

| Function                        | Body                              |
|---------------------------------|-----------------------------------|
| `butcherRadauI_zeros_one`       | `0`                               |
| `butcherRadauI_zeros_two`       | `(0, 2/3)`                        |
| `butcherRadauII_zeros_one`      | `1`                               |
| `butcherRadauII_zeros_two`      | `(1/3, 1)`                        |
| `butcherLobatto_zeros_two`      | `(0, 1)`                          |
| `butcherLobatto_zeros_three`    | `(0, 1/2, 1)`                     |

Use `noncomputable` for parity with cycle 302's
`butcherShiftedLegendre_zeros` (even though these defs *are*
computable; the noncomputable annotation costs nothing and keeps
the style uniform).

Recommended body shape: pattern-matched on the `Fin` indices.
Example:

```lean
noncomputable def butcherRadauI_zeros_two : Fin 2 → ℝ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2/3
```

### 2. Root theorems (`_isRoot`)

For each abscissa function, prove every entry is a root of the
corresponding §344 polynomial. Example shape:

```lean
theorem butcherRadauI_zeros_two_isRoot (i : Fin 2) :
    (butcherRadauI 2).eval (butcherRadauI_zeros_two i) = 0 := by
  fin_cases i
  · exact butcherRadauI_two_roots.1
  · exact butcherRadauI_two_roots.2.1
```

`fin_cases i` should unfold `butcherRadauI_zeros_two` definitionally
on each branch (since each branch is `rfl`). Each branch then cites
the appropriate conjunct from cycle 319's `_roots` theorem.

For the single-root cases (`_one` variants), no `fin_cases` needed:

```lean
theorem butcherRadauI_zeros_one_isRoot (i : Fin 1) :
    (butcherRadauI 1).eval (butcherRadauI_zeros_one i) = 0 := by
  fin_cases i; exact butcherRadauI_one_root
```

### 3. Strict-monotonicity theorems (`_strictMono`)

For the multi-root cases (the four `_two` and one `_three`
variants), prove the abscissa function is strictly monotone — this
packages the pairwise-distinctness clauses from cycle 319 into the
form downstream RKTableau construction expects.

```lean
theorem butcherRadauI_zeros_two_strictMono :
    StrictMono butcherRadauI_zeros_two := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> norm_num
```

For Lobatto's `_three`, after `fin_cases i <;> fin_cases j` there
are 9 sub-goals: 3 trivially-true `i < j` cases (`0 < 1/2`, `0 < 1`,
`1/2 < 1`) closed by `norm_num`, plus 6 false-`hij` cases closed by
`simp_all` (since `hij : (0 : Fin 3) < 0` etc. is decidable false).

The `_one` variants don't need `_strictMono` (single-element
domain) — skip them.

### 4. Containment theorems (`_mem_Icc`)

Each abscissa lies in `[0, 1]`:

```lean
theorem butcherRadauI_zeros_two_mem_Icc (i : Fin 2) :
    butcherRadauI_zeros_two i ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases i <;> simp [Set.mem_Icc] <;> norm_num
```

Needed for downstream `RKTableau` construction (the abscissae have
to live in the unit interval per Butcher §321 conventions).

---

## Total LOC estimate

~150 LOC total:
* 6 abscissa defs × ~5 LOC each ≈ 30 LOC.
* 6 `_isRoot` theorems × ~6 LOC each ≈ 36 LOC.
* 5 `_strictMono` theorems × ~7 LOC each ≈ 35 LOC.
  (Wait — there are 5 multi-element abscissae: the four `_two`
  variants plus `_three`. The two `_one` variants don't need it.)
* 6 `_mem_Icc` theorems × ~5 LOC each ≈ 30 LOC.
* Docstrings and inter-block comments ≈ 20 LOC.

Well within the ~200 LOC abort threshold. If the worker is ahead
of budget, optionally add P3 (see §"P3 stretch" below).

---

## Step-by-step plan

1. **Open the cycle 320 work** — open `Section344.lean` and locate
   line 583 (immediately after `butcherLobatto_three_roots`).

2. **Write the section header** — add a Deliverable C.2 doc-comment
   block (~10 LOC) describing the six abscissa functions and their
   use cases.

3. **Ship the six abscissa defs** — each as a `noncomputable def`
   with pattern-matched cases per the table above. No proof
   obligations; each branch closes by `rfl`.

4. **Ship the six `_isRoot` theorems** — each cites the
   corresponding cycle 319 `_roots` (or `_root` for single-element)
   theorem's appropriate conjunct via `fin_cases i` + `exact ...`.

5. **Ship the five `_strictMono` theorems** — `intro i j hij;
   fin_cases i <;> fin_cases j <;> simp_all <;> norm_num` should
   close all five. If `simp_all` leaves residue on some `_three`
   branches, fall back to explicit case unfolding (see Risk R3).

6. **Ship the six `_mem_Icc` theorems** — `fin_cases i +
   simp [Set.mem_Icc] + norm_num`. Mechanical.

7. **Build verify** — `lake env lean
   OpenMath/Chapter3/Section344.lean`. If clean, run `lake env
   lean OpenMath/Chapter3.lean` to confirm the aggregator builds.

8. **Axiom verify** — use `lean_verify` on at least one theorem
   per family (suggested:
   `butcherRadauI_zeros_two_isRoot`,
   `butcherRadauII_zeros_two_strictMono`,
   `butcherLobatto_zeros_three_strictMono`,
   `butcherLobatto_zeros_three_mem_Icc`) to confirm
   `[propext, Classical.choice, Quot.sound]` only.

9. **Update `plan.md`** — append a cycle 320 line to `thm:344A`'s
   row describing Phase C.2 (small-`s` abscissae functions) shipped
   axiom-clean.

10. **Update `extraction/formalization_data/lean_status.json`** —
    keep `thm:344A` as `partial` (Phase B.2 and general-`s` C.2 are
    still open); bump the `cycle` field to 320 and append a one-line
    note to the `notes` field about Phase C.2 shipping.

11. **Write `.prover-state/task_results/cycle_320.md`** documenting
    deliverables, faithfulness check, dead ends, and suggested
    cycle 321 entry point.

12. **Pre-commit faithfulness check** — see §"Faithfulness check"
    below.

13. **Commit** — single commit with message
    "Cycle 320 — §344 Phase C.2: small-`s` abscissae functions
    shipped axiom-clean."

---

## Faithfulness check

For each new `def` (six abscissae functions):

* **Definition smuggling check**: each abscissa function packages
  cycle 319's explicit-root values into `Fin s → ℝ` arrays. The
  textbook (Butcher §344 p. 244) does not name these arrays
  explicitly at small-`s`; they are derived from `thm:344A`'s
  abscissae conditions (`c_1 < c_2 < ... < c_s` with `c_i ∈ [0, 1]`
  and the §344 endpoint constraints). Each entry is the unique
  root of the corresponding §344 polynomial at the given position
  (matching `c_i`'s ordering). No equivalence lemma needed; the
  `_isRoot` theorems are the explicit bridge.

For each new theorem (six `_isRoot`, five `_strictMono`, six
`_mem_Icc`):

* **Tautology check**: none of the conclusions appear verbatim as
  hypotheses (no hypotheses on any of these theorems).
* **Identity check**: each `_isRoot` proof is `fin_cases i +
  exact <cycle 319 root>` — real work via abscissa unfolding plus
  cycle 319 citation. `_strictMono` and `_mem_Icc` delegate to
  cycle 319 distinctness clauses and `norm_num` arithmetic.
* **Hypothesis strength**: all 17 new theorems are universal
  numerical facts (no hypotheses); minimal-strength signatures.
* **Absent theorem check**: nothing promised but missing.

---

## Risk assessment and mitigations

### R1: `noncomputable def` pattern-matching issues

The pattern-matching shape `| ⟨0, _⟩ => 0` may fire warnings about
incomplete patterns or definitional reduction. Mitigations in
order of preference:

(a) The shape above. Should work — Lean accepts pattern-matching
    on `Fin n` via raw `⟨val, isLt⟩` deconstruction.

(b) Use `Fin.cases` recursor:
    `Fin.cases 0 (fun _ => 2/3 (Fin.elim0 ·))` — less readable
    but always works.

(c) If patterns are flagged incomplete, append a catch-all
    `| _ => 0` after the explicit cases (defensive; only fires
    on impossible indices since `Fin n` indices are exhausted by
    the explicit cases).

Recommended: try (a) first; if Lean complains, switch to (c).

### R2: `fin_cases i` does not unfold the abscissa function

If `fin_cases i` leaves the goal in the form
`(butcherRadauI 2).eval (butcherRadauI_zeros_two ⟨0, _⟩) = 0`
without unfolding `butcherRadauI_zeros_two`, prepend a `show`
tactic to force the unfold:

```lean
fin_cases i
· show (butcherRadauI 2).eval (0 : ℝ) = 0
  exact butcherRadauI_two_roots.1
```

Alternative: use `simp only [butcherRadauI_zeros_two]` after
`fin_cases` to force definitional unfolding. The cycle 263
`feedback_indexed_inductive_cases_disjoint.md` (memory) confirms
`fin_cases` does unfold patterns on `Fin n` defs cleanly when each
branch reduces by `rfl`.

### R3: `_strictMono` arithmetic residue on Lobatto `_three`

For Lobatto's `_three`, `fin_cases i <;> fin_cases j` produces 9
sub-goals. The 3 true ones (`hij : 0 < 1`, `0 < 2`, `1 < 2` on
`Fin 3` mapping to `0 < 1/2`, `0 < 1`, `1/2 < 1` on `ℝ`) close by
`norm_num`. The 6 false ones (e.g. `hij : 1 < 0`, `hij : 0 < 0`,
etc.) should close by `simp_all` (`Fin.lt_def` collapse plus
`Nat`-arithmetic).

If `simp_all` leaves stubborn `Fin.lt_def` residue, the recovery
is explicit case unfolding via a `rcases` pattern. Less elegant
but always works:

```lean
intro i j hij
rcases i with ⟨i, hi⟩
rcases j with ⟨j, hj⟩
interval_cases i <;> interval_cases j <;> simp_all <;> norm_num
```

`interval_cases` on `Nat`-valued `i, j` bounded by `Fin n`'s `isLt`
field should enumerate `i ∈ {0, 1, 2}` and `j ∈ {0, 1, 2}` cleanly.

### R4: Build heartbeats

Cycle 274–281's `butcherShiftedLegendre_norm_sq_*` blow-up risk
applies to integration-heavy proofs, NOT to abscissae arithmetic.
This cycle ships only `Polynomial.eval` + arithmetic; no
`intervalIntegral` invocations. The heartbeat risk is **low**.

### R5: Aristotle suitability

These deliverables are too small and mechanical to benefit from
Aristotle. Ship manually; do NOT submit to Aristotle.

---

## P3 stretch — small-`s` Lagrange quadrature weight stubs

If steps 1–13 close in well under the cycle budget (perhaps 60% of
LOC and time spent), optionally add P3:

```lean
noncomputable def butcherRadauI_quadratureWeights_one : Fin 1 → ℝ :=
  fun _ => 1

noncomputable def butcherRadauI_quadratureWeights_two : Fin 2 → ℝ
  | ⟨0, _⟩ => 1/4
  | ⟨1, _⟩ => 3/4

-- ... and four more analogously
```

Don't try to prove the integral identity `b_j = ∫₀¹ L_j(x) dx`
this cycle — that's a cycle 321 deliverable. Just define the
closed-form weights with numerical values and ship trivial
`_apply` `rfl` lemmas. This pre-commits to the numerical values
so cycle 321 has a clear target.

Closed-form values to use (verify by paper integration before
writing):

| Family       | Stages | Weights                      |
|--------------|--------|------------------------------|
| Radau I      | s=1    | `(1)`                        |
| Radau I      | s=2    | `(1/4, 3/4)`                 |
| Radau II     | s=1    | `(1)`                        |
| Radau II     | s=2    | `(3/4, 1/4)`                 |
| Lobatto      | s=2    | `(1/2, 1/2)` (trapezoidal)   |
| Lobatto      | s=3    | `(1/6, 2/3, 1/6)` (Simpson)  |

If P3 lands, cycle 321 ships the integral identities directly
linking these closed forms to `∫₀¹ L_j(x) dx`. Without P3, cycle
321 ships the weights as integrals first, then the closed-form
lemmas separately.

**Skip P3 if any of steps 1–13 take longer than estimated.** A
single-cycle deliverable that ships clean is worth more than a
two-cycle deliverable that risks a half-shipped state.

---

## What NOT to try

* **Do NOT attempt small-`s` Lagrange weights via integral
  computation in cycle 320.** The integration step has cycle
  274/281 precedent of blowing past heartbeats. Save for cycle
  321.

* **Do NOT attempt general-`s` Phase C.2** (`thm:344A` abscissae
  construction via sign-change argument). Per plan.md, this is
  multi-cycle and requires endpoint-zero factoring (`x` for
  Radau I, `(x − 1)` for Radau II, `x(x − 1)` for Lobatto) before
  the cycle 301 `butcherShiftedLegendre_n_distinct_real_zeros`
  recipe applies. Out of scope.

* **Do NOT attempt Phase B.2** (polynomial-exactness `2s − 2` /
  `2s − 3`) in cycle 320. Requires Lagrange-interpolation
  infrastructure at the §344 abscissae plus the
  polynomial-division step. Cycle 322+ work, after weights land.

* **Do NOT define abscissae for `s ≥ 3` Radau** or `s ≥ 4`
  Lobatto. Cycle 319 only provides explicit roots up to those
  sizes; going beyond requires cycle 301's sign-change machinery
  ported to the §344 polynomials, which is multi-cycle work.

* **Do NOT raise `maxHeartbeats`.** Per CLAUDE.md, decompose
  instead. Nothing this cycle should need > 200000 heartbeats.

* **Do NOT introduce `axiom` / `constant`.** Per CLAUDE.md.

* **Do NOT introduce sorries.** Cycle 320 must close axiom-clean
  or skip individual deliverables (e.g. ship only Radau I and
  Radau II, defer Lobatto to cycle 321) rather than scaffolding
  sorries. The cycle 138 → 139 and cycle 149 → 150 rollback
  precedents apply.

* **Do NOT submit anything to Aristotle this cycle.** These
  deliverables are too small and mechanical to benefit from
  prover assistance.

* **Do NOT touch `OpenMath/Chapter4/Section441.lean`.** It has
  been GPFS-blocked for 43+ consecutive cycles since cycle 182.
  Skip per `.prover-state/issues/cycle_182_gpfs_slowness.md`.

* **Do NOT respond to phantom "stuck on" framings** in subsequent
  consultant prompts. Multiple prior cycles (008, 014, 015, 040,
  174, 180, 196, 248, 263) document loop-maintainer-side
  prompt-builder false positives propagating stale `attempts.md`
  rows. If a future cycle's "What I'm stuck on" field is empty
  or cites cycle 320 deliverables that are at HEAD, treat it as
  a no-op and pivot directly to cycle 321 planning. See
  `.prover-state/issues/phantom_commit_verdict_pattern.md` and
  `.prover-state/issues/consultant_advice_cycle_263.md` §I.

* **Do NOT modify `scripts/autonomous_loop.py`** or the
  prompt-builder. Tautology-scanner / consultant-phase false
  positives are loop-maintainer territory per
  `.prover-state/issues/tautology_scanner_false_positives.md`.

---

## Cycle 321 entry point (recommended)

If cycle 320 ships P1 (abscissae) without P3 (weight stubs):

* **Cycle 321 target**: small-`s` Lagrange quadrature weights via
  integral definitions, mirroring cycle 303's
  `butcherShiftedLegendre_quadratureWeights` construction. For
  each of the six abscissae functions, define
  `_quadratureWeights : Fin s → ℝ` as
  `∫₀¹ (Lagrange.basis Finset.univ <abscissae> j).eval x`, then
  prove the closed-form numerical values via paper-verified
  integration. ~150 LOC estimate; will hit the cycle 274/281
  heartbeats territory, so plan carefully and split per-stage if
  needed.

If cycle 320 ships P1 + P3 (abscissae + weight stubs):

* **Cycle 321 target**: prove the integral identities linking
  the cycle 320 closed-form stubs to `∫₀¹ L_j(x) dx`. ~80 LOC
  per stub. After this, cycle 322 begins Phase B.2
  polynomial-exactness or pivots to RKTableau construction.

Either way, cycle 322+'s natural pivot is the small-`s`
`RKTableau` construction: Radau IA (Radau II abscissae +
collocation A-matrix) and Lobatto IIIB (Lobatto abscissae +
collocation A-matrix). Small-`s` cases are tractable individually
(Radau IA `s=1` is backward Euler; Lobatto IIIB `s=2` is the
trapezoidal rule); general-`s` requires the cycle 308–312 lift
recipe ported to §344.

---

## Summary

* **Target**: §344 Phase C.2 (small-`s` abscissae functions, six
  defs + 17 theorems).
* **LOC**: ~150.
* **Risk**: low (mechanical `fin_cases` + `norm_num`).
* **Sorry count**: 0 → 0.
* **Axiom-clean expected** (`[propext, Classical.choice, Quot.sound]`).
* **No Aristotle this cycle.**
* **No Section441 attempts.**
* **No sorries, no axioms, no maxHeartbeats bumps.**
