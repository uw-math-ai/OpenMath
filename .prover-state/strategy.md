# Cycle 284 strategy

**Cycle 283 outcome**: Shipped three (342f) recurrence ladder rungs at
`n = 5, 6, 7` axiom-clean (`Section342.lean` 1949 → 2020 LOC, sorry
count 0). Aristotle project `c8b8f138-f875-4263-94ec-74533b5120d7`
(general (342f) recurrence) single-polled and was **IN_PROGRESS at 12%**
(15 min after submission). Cycle 282–283 used the
`Polynomial.funext + simp [eval_*] + ring` recipe at scale; ring proves
remain fast.

**Current substantive target**: `lem:342A` (§342, Butcher §342 p. 236) —
the seven properties (342a)–(342g) of the Butcher-normalised shifted
Legendre polynomials `P_n^*`. Properties (342a)/(342b)/(342c)/(342d)/(342e)
are formalised; (342f) general and (342g) `n` distinct real zeros remain.

---

## §A — P0 Aristotle poll (5 min, mandatory)

**Single-poll** `mcp__aristotle__get_status` on
`c8b8f138-f875-4263-94ec-74533b5120d7`. **Do NOT poll any other project**
this cycle. Per CLAUDE.md, one poll only.

Three branches by status:

### Branch A — `COMPLETE` (preferred outcome)

Per Aristotle's `d4ce527b` (cycle 281) integration precedent:

1. **Download & inspect** the proof via
   `mcp__aristotle__download_result`. Read `ARISTOTLE_SUMMARY.md` and
   the main proof file.
2. **Decide on helper file**: if the proof introduces ≥2 reusable
   private helpers (mutual recursion, ring/coefficient identities,
   multi-step IBP, etc.), extract them into a new file
   `OpenMath/Chapter3/Section342RecurrenceHelpers.lean` (precedent:
   cycle 281's `Section342NormSqHelpers.lean`, ~210 LOC). If the proof
   is ≤80 LOC and self-contained, inline it directly into Section342.
3. **Integrate as** `butcherShiftedLegendre_recurrence` with signature
   matching the `c8b8f138` submission target (verify by reading the
   submission `.lean` file at
   `.prover-state/aristotle_submissions/cycle_282/`).
4. **Verify axiom-clean**: `#print axioms` on every new symbol must
   return `[propext, Classical.choice, Quot.sound]` only. If a `sorry`
   slips in, ROLL BACK the integration and proceed to Branch B.
5. **Cross-check** that the cycle 282–283 concrete witnesses
   `butcherShiftedLegendre_recurrence_{two..seven}` still build (their
   proofs do NOT route through the general theorem — they are
   independent `Polynomial.funext + ring` computations — so this should
   be automatic, but verify).
6. **Update**:
   - `extraction/formalization_data/lean_status.json` for `lem:342A`
     — the (342f) clause is now closed; leave `partial` because
     (342g) is still open.
   - `plan.md` `lem:342A` row — append a cycle 284 (342f) general
     closure note.
7. **P2 stretch (if Branch A succeeded with budget remaining)**: Fire
   Aristotle on (342g) `n` distinct real zeros per
   `.prover-state/issues/lem_342A_g_zeros_scoping.md`. Submit a
   self-contained `.lean` file at
   `.prover-state/aristotle_submissions/cycle_284/342g_zeros.lean`
   citing as axioms:
   - cycle 271–273's `butcherShiftedLegendre_{eval_one, eval_one_sub,
     eval_zero, natDegree, rodrigues, zero, one, two, three}`
   - cycle 275–280's `butcherShiftedLegendre_{four..seven}`
   - cycle 277's `butcherShiftedLegendre_orthogonal`
   - cycle 281's `butcherShiftedLegendre_norm_sq`
   - cycle 284's `butcherShiftedLegendre_recurrence`
   Use the sign-change-contradiction strategy from
   `lem_342A_g_zeros_scoping.md` §"Textbook proof sketch". Do NOT
   poll the new submission this cycle — just submit and move on.

### Branch B — `IN_PROGRESS` at ≤50% (most likely outcome)

Expected at the cycle 283 pace of ~+5–10%/cycle. Per strategy, **do not
wait** — pivot immediately to manual ladder extension.

**P1 deliverable: ship `butcherShiftedLegendre_eight` + `butcherShiftedLegendre_recurrence_eight`.**

#### B.1 Shape of `butcherShiftedLegendre_eight`

`n = 8` is **even** (like cycle 279's n=6), so `(-1)^8 = 1` and the
outer Butcher sign flip is trivial. The explicit form is:

```
butcherShiftedLegendre 8 =
    C 12870 · X^8 - C 51480 · X^7 + C 84084 · X^6 - C 72072 · X^5
  + C 34650 · X^4 - C 9240 · X^3 + C 1260 · X^2 - C 72 · X + C 1
```

Coefficient derivation (from `coeff_shiftedLegendre k = (-1)^k *
C(n+k, k) * C(n, k)` at n=8):

| k | (-1)^k · C(n+k,k) · C(n,k) | value |
|---|----------------------------|-------|
| 0 | +1 · 1 · 1 | 1 |
| 1 | -1 · 9 · 8 | -72 |
| 2 | +1 · 45 · 28 | 1260 |
| 3 | -1 · 165 · 56 | -9240 |
| 4 | +1 · 495 · 70 | 34650 |
| 5 | -1 · 1287 · 56 | -72072 |
| 6 | +1 · 3003 · 28 | 84084 |
| 7 | -1 · 6435 · 8 | -51480 |
| 8 | +1 · 12870 · 1 | 12870 |

Required `decide`-helpers (extending cycle 278/280's pattern):
```
Nat.choose 9 8 = 9,  Nat.choose 8 1 = 8
Nat.choose 10 8 = 45, Nat.choose 8 2 = 28
Nat.choose 11 8 = 165, Nat.choose 8 3 = 56
Nat.choose 12 8 = 495, Nat.choose 8 4 = 70
Nat.choose 13 8 = 1287, Nat.choose 8 5 = 56
Nat.choose 14 8 = 3003, Nat.choose 8 6 = 28
Nat.choose 15 8 = 6435, Nat.choose 8 7 = 8
Nat.choose 16 8 = 12870
```

**Recipe** (verbatim port of cycle 279's `_six` proof shape at
`Section342.lean` line ~455 — read it first as template):
```lean
theorem butcherShiftedLegendre_eight :
    butcherShiftedLegendre 8 = ... := by
  unfold butcherShiftedLegendre
  ext k
  -- Peel-off pattern (cycle 276 onward)
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
             Polynomial.coeff_shiftedLegendre]
  match k with
  | 0 => simp [...]; norm_num
  | 1 => simp [...]; norm_num
  | 2 => have hch1 : Nat.choose 10 8 = 45 := by decide
         have hch2 : Nat.choose 8 2 = 28 := by decide
         simp [..., hch1, hch2]; norm_num
  ... (case-split through k = 8)
  | k + 9 =>
      -- Tail: all coefficients 0 by Nat.choose_eq_zero_of_lt
      simp [Polynomial.coeff_sub, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_C, Polynomial.coeff_one,
            Nat.choose_eq_zero_of_lt]
```

LOC budget ~80 LOC. Faithfulness check: this is a numerical identity
for a textbook-named polynomial, no risk of definition smuggling.

#### B.2 Shape of `butcherShiftedLegendre_recurrence_eight`

At n=8: `(2n-1, n-1) = (15, 7)`. The recurrence is

```
(8 : ℝ) • P_8^* = C 15 · (C 2 · X - C 1) · P_7^* - C 7 · P_6^*
```

Recipe identical to cycle 283's `_recurrence_{five,six,seven}` (~10
LOC body):
```lean
theorem butcherShiftedLegendre_recurrence_eight :
    (8 : ℝ) • butcherShiftedLegendre 8 =
      Polynomial.C 15 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 7
      - Polynomial.C 7 * butcherShiftedLegendre 6 := by
  apply Polynomial.funext
  intro x
  rw [butcherShiftedLegendre_eight, butcherShiftedLegendre_seven,
      butcherShiftedLegendre_six]
  simp [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
  ring
```

LOC budget ~15 LOC.

#### B.3 Sanity-check the recurrence coefficients before writing

Before committing, verify by hand or `python -c`:
- LHS: `8 · P_8^* = 102960 X^8 - 411840 X^7 + 672672 X^6 - 576576 X^5
  + 277200 X^4 - 73920 X^3 + 10080 X^2 - 576 X + 8`.
- RHS: `15 · (2X - 1) · P_7^* - 7 · P_6^*`. Compute
  `(2X - 1) · P_7^*` first, multiply by 15, subtract `7 · P_6^*`,
  confirm coefficients match LHS. (Cross-checking is mandatory because
  `ring` will silently close a wrong recurrence as `0 = 0` if both
  sides match — but it will produce an error if mismatched.)

### Branch C — `COMPLETE_WITH_ERRORS` / `FAILED` / `CANCELLED`

Per cycle 184 precedent (Aristotle returned a one-line namespace fix):
1. Read the error report. If the fix is ≤10 LOC of mechanical edits
   (namespace qualifications, typo corrections), apply and integrate.
2. Otherwise treat as Branch B (ship n=8 ladder rung manually) and
   leave the failed Aristotle project as-is — do NOT cancel and
   resubmit this cycle (CLAUDE.md: one Aristotle poll per cycle).

---

## §B — DO NOT do this cycle

These are explicit fails or known bad patterns; do not repeat.

### B.1 — Do NOT attempt manual general-(342f) proof
Cycle 273 task results §"What was tried" documents that both
`Polynomial.ext` (coefficient route) and `Polynomial.funext` (eval
route) require **Pascal-style binomial identities on Nat.choose** that
`ring` cannot close. Butcher's textbook degree-and-difference outline
requires (342a) orthogonality + (342e) Rodrigues as inputs, but
synthesising these into a Lean recurrence proof was estimated
multi-cycle in cycle 273. Aristotle is in flight (`c8b8f138`); do not
race it manually.

### B.2 — Do NOT poll Aristotle more than once
Per CLAUDE.md "sleep 30 minutes, check once". The cycle 283 poll was
~15 min after submission and reached 12%; the cycle 284 poll will be
the second observation. Beyond that, the project is left running for
cycle 285+.

### B.3 — Do NOT modify Section441.lean
44+ consecutive GPFS timeouts since cycle 182 per
`.prover-state/issues/cycle_182_gpfs_slowness.md`. Section441 work is
loop-maintainer territory until GPFS recovers.

### B.4 — Do NOT use `Polynomial.ext` for the new explicit form
Cycle 273 §"Dead end" documents that `Polynomial.ext` requires
coefficient-by-coefficient identities that involve `Nat.choose` that
`ring` cannot close. **Use the cycle 276 onward peel-off pattern**:
`unfold ; ext k ; simp only [coeff_C_mul, coeff_map,
coeff_shiftedLegendre] ; match k with ...`.

### B.5 — Do NOT fire Aristotle on (342g) UNLESS Branch A succeeds
The (342g) sign-change argument depends on (342f) general (used for
the orthogonality contradiction in degree-`k` polynomial expansion).
Without (342f) in hand, Aristotle would have to reprove it as a
sub-lemma — wasteful. Fire (342g) only after (342f) integrates.

### B.6 — Do NOT raise `maxHeartbeats`
Per CLAUDE.md "Never increase `maxHeartbeats` above 200000. Decompose
the proof instead." The n=8 explicit-form proof should fit within
default heartbeats with proper case-split structure (cycles 278/280
hit no heartbeat issues).

### B.7 — Do NOT skip the case k=0 in the match
Even though `(-1)^8 * coeff_shiftedLegendre 8 0 = 1`, Lean does not
auto-simplify the `(-1)^n * ·` factor without explicit `norm_num`. All
case branches need full `simp [...] ; norm_num` closure (cf. cycle
279's `_six` proof at Section342.lean line ~455).

### B.8 — Do NOT introduce sorries
Sorry count is 0 and must remain 0 (supervisor policy from cycles
149/150 + 200/201 rollbacks). If a deliverable threatens to introduce
a sorry, ship a strictly weaker axiom-clean variant instead, or skip
the deliverable for this cycle.

---

## §C — Closure checklist (mandatory before commit)

1. **`lake env lean OpenMath/Chapter3/Section342.lean` exits 0**.
2. **`lake env lean OpenMath/Chapter3.lean` exits 0** (aggregator).
3. **`grep -c sorry OpenMath/Chapter3/Section342.lean` = 0**.
4. **Axiom-clean check**: `#print axioms` on every new symbol returns
   `[propext, Classical.choice, Quot.sound]` only. If `sorryAx` appears,
   the corresponding proof did not close — revert and re-plan.
5. **Pre-commit faithfulness checklist** (per CLAUDE.md): for each new
   `theorem`/`def`, write a short note in `task_results/cycle_284.md`
   §"Faithfulness check" quoting the textbook statement and confirming
   the Lean statement matches.
6. **Write `.prover-state/task_results/cycle_284.md`** documenting:
   - Worked on (which branch fired)
   - Approach (poll result + integration/extension recipe)
   - Result (SUCCESS / branch outcome)
   - Faithfulness check
   - Dead ends (none expected if recipes followed)
   - Discovery (any new Mathlib hooks or Aristotle behaviour notes)
   - Suggested next approach for cycle 285
7. **Update `plan.md`** `lem:342A` row with the cycle 284 closure note.
8. **Update `extraction/formalization_data/lean_status.json`**:
   - If Branch A succeeded: bump cycle to 284, append (342f) general
     closure to `lean_symbol` notes, leave status `partial`
     (still need (342g)).
   - If Branch B: bump cycle to 284, append "n=8 ladder rung" to the
     concrete witnesses list, status remains `partial`.
9. **Commit** with message starting `Cycle 284 — §342 (342f) ...`.
10. **Push** to `origin/butcher-experiments`.

---

## §D — Pre-flight risk register (Branch B specifically)

| Risk | Mitigation |
|---|---|
| `Nat.choose 16 8 = 12870` slow via `decide` | If `decide` exceeds 10s, fallback `by norm_num [Nat.choose]` (cycle 278/280 precedent shows `decide` worked at these sizes). |
| `match k with | k + 9 => ...` tail doesn't close via `Nat.choose_eq_zero_of_lt` | Inspect cycle 280's `k + 8 =>` tail (for n=7) at Section342.lean ~line 690 for the working simp set. |
| `Polynomial.funext` consumes ~5s per use | Acceptable; cycle 283 proofs at n=5,6,7 each closed in <10s warm. |
| Recurrence LHS≠RHS at n=8 (typo'd coefficient) | Cross-check by hand BEFORE running `ring` — `ring` will report a specific monomial mismatch but the LOC budget assumes first-try close. |

---

## §E — Cycle 285+ outlook (briefing for next planner)

- If cycle 284 ships Branch A (general (342f) integrated): cycle 285
  polls (342g) Aristotle (if P2 stretch fired) OR begins
  `lem:342B` (Gaussian quadrature exactness, depends on (342g)).
- If cycle 284 ships Branch B (n=8 ladder rung): cycle 285 polls
  Aristotle `c8b8f138` again; if still IN_PROGRESS, extend ladder to
  n=9 (mechanical port) OR pivot to `lem:310B` Phase A.3
  (TreeAutomorphism strengthening, per `lem_310B_plan.md`).
- Long-running parallel option: `lem:310B` Phase A.3 is the deferred
  multi-cycle item that does not block (342f)/(342g). A planner could
  in principle interleave Phase A.3 cycles with §342 polling cycles.
