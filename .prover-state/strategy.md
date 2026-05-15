# Cycle 294 strategy — open §342 (342g) (`P_n^*` has `n` distinct real zeros in `(0, 1)`)

## §A Context and decision

**Cycle 293 closed (342f) in full** — `butcherShiftedLegendre_recurrence`
ships axiom-clean at `OpenMath/Chapter3/Section342.lean:3522` for every
`n ≥ 2`. With (342a), (342b), (342c), (342d), (342e), (342f) all
closed, the **only remaining open clause of `lem:342A` is (342g)**:

> `P_n^*` has `n` distinct real zeros in `(0, 1)`, `n = 0, 1, 2, …`.

The cycle 293 worker explicitly suggested (342g) as the natural cycle
294 target (≈ 200–300 LOC estimated for the full closure). A scoping
document already exists at
`.prover-state/issues/lem_342A_g_zeros_scoping.md` with the textbook
proof sketch (Butcher §342 p. 236, contradiction via sign-change
pairing + (342a) orthogonality on `Q := ∏ᵢ (X − C xᵢ)`).

**Sign-change combinatorics is fiddly in Lean**, so cycle 294 follows
a **fire-and-forget Aristotle + concrete-witness ladder** pattern,
analogous to cycle 277 (Aristotle closure of (342a) + concrete `n=4`
norm-square witness in parallel). This is the strategy endorsed by
the scoping doc §29–44.

The cycle 294 plan is **measured, not capstone**: ship empirical
infrastructure (Aristotle submission + small-`n` zero witnesses +
upper-bound `card_roots ≤ n`) so cycle 295+ can either integrate
Aristotle's return or attempt manual closure with a strong empirical
base. **Do NOT attempt the full (342g) closure manually this cycle**
— sign-change pairing on `Polynomial.roots` over `ℝ` is multi-cycle
infrastructure not yet in place.

---

## §B Priority 1 (fire-and-forget) — Submit (342g) to Aristotle

**Action**: create `.prover-state/aristotle_submissions/cycle_294/342g_zeros.lean`
containing the (342g) target plus **all** of cycles 271–293's results
as cited axioms, and submit via `mcp__aristotle__submit_file`.
Aristotle gets a richer prerequisite base than for (342a) or (342d).

### Target statement (Lean):

```lean
theorem butcherShiftedLegendre_n_distinct_real_zeros (n : ℕ) :
    ∃ (xs : Finset ℝ), xs.card = n ∧
      (∀ x ∈ xs, x ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ x ∈ xs, (butcherShiftedLegendre n).eval x = 0)
```

### Cited axioms (all closed, axiom-clean at HEAD):

* `butcherShiftedLegendre_eval_one` (342b)
* `butcherShiftedLegendre_eval_one_sub` (342c, parity)
* `butcherShiftedLegendre_eval_zero` (cycle 273)
* `butcherShiftedLegendre_natDegree = n` (cycle 273)
* Explicit forms `_zero`, `_one`, `_two`, ..., `_eleven`
  (cycles 273–288) — useful for base cases.
* `butcherShiftedLegendre_rodrigues` (342e)
* `butcherShiftedLegendre_orthogonal {m n : ℕ} (hmn : m ≠ n) :
  ∫₀¹ P_m^* · P_n^* = 0` (342a, cycle 277) — load-bearing.
* `butcherShiftedLegendre_norm_sq n : ∫₀¹ (P_n^*)² = 1/(2n+1)` (342d
  general, cycle 281)
* `butcherShiftedLegendre_orthogonal_to_lower_degree (n : ℕ)
  (q : Polynomial ℝ) (hq : q.natDegree < n) : ∫₀¹ P_n^* · q = 0`
  (cycle 292) — **the key reusable lemma for the contradiction
  argument**.
* `butcherShiftedLegendre_recurrence n (hn : 2 ≤ n)` (342f, cycle
  293) — possibly useful for Sturm-style proofs.

### Proof-sketch hint to include in the Aristotle prompt:

> Proof by contradiction. Suppose `P_n^*` has fewer than `n`
> sign-change points in `(0, 1)`. Let `x_1, …, x_k` be the distinct
> sign-change points (`k < n`), and form
> `Q := ∏ᵢ (X − Polynomial.C xᵢ)` with `natDegree = k < n`. Then
> `P_n^*(x) · Q(x)` has constant non-zero sign on `(0, 1)` except at
> the finite root set (sign changes paired off), so
> `∫₀¹ P_n^* · Q ≠ 0`. But
> `butcherShiftedLegendre_orthogonal_to_lower_degree n Q (by simp [Q] : Q.natDegree < n)`
> gives `∫₀¹ P_n^* · Q = 0`. Contradiction. Hence `P_n^*` has at
> least `n` sign-change zeros in `(0, 1)`; combined with
> `natDegree = n` and `card_roots ≤ natDegree`, equality is forced.

**Submission specifics**: include cited-axiom statements verbatim
(not just signatures) so Aristotle sees the exact integral form
used by (342a) and the cycle-292 helper. Mention that integrals are
`intervalIntegral` form `∫ x in (0:ℝ)..1, ...`, NOT measure-theoretic
unbounded form.

**Logging**: record the project ID returned by submission in
`.prover-state/aristotle_submissions/cycle_294/README.md` and in the
cycle 294 task results.

**Do NOT poll Aristotle this cycle.** Single-poll discipline per
CLAUDE.md. Cycle 295 polls exactly once.

---

## §C Priority 2 (manual ship) — Concrete small-`n` zero witnesses

Ship two concrete numerical witnesses confirming `P_n^*` has `n`
real zeros in `(0, 1)` for `n ∈ {1, 2}`. These provide:
* Non-vacuity for the general (342g) statement.
* Empirical base for the closure (analogous to the cycles
  274–280 norm-square ladder).
* Sanity checks if Aristotle's general-`n` proof requires fix-up.

Locate these in `OpenMath/Chapter3/Section342.lean` after the
cycle 293 `butcherShiftedLegendre_recurrence` block (line 3522+).

### P2.1 — `n = 1`: explicit zero at `x = 1/2`

`P_1^*(x) = 2x − 1` (cycle 273) has single root `x = 1/2 ∈ (0, 1)`.

**Lean target**:
```lean
theorem butcherShiftedLegendre_one_root :
    (butcherShiftedLegendre 1).eval (1 / 2 : ℝ) = 0 ∧
      (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1
```

**Proof recipe**: `refine ⟨?_, ?_⟩`. First goal: `rw [butcherShiftedLegendre_one]`
then `simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
Polynomial.eval_X]; norm_num`. Second goal: `simp [Set.mem_Ioo];
norm_num`. ~10 LOC including docstring.

### P2.2 — `n = 2`: explicit zeros at `(3 ± √3) / 6`

`P_2^*(x) = 6x² − 6x + 1` (cycle 275). Quadratic formula:
roots `x = (6 ± √12) / 12 = (3 ± √3) / 6`. Both in `(0, 1)`:
`(3 − √3) / 6 ≈ 0.211` and `(3 + √3) / 6 ≈ 0.789`. Distinct since
`√3 > 0`.

**Lean target**:
```lean
theorem butcherShiftedLegendre_two_roots :
    ∃ x₁ x₂ : ℝ,
      x₁ ≠ x₂ ∧
      x₁ ∈ Set.Ioo (0 : ℝ) 1 ∧ x₂ ∈ Set.Ioo (0 : ℝ) 1 ∧
      (butcherShiftedLegendre 2).eval x₁ = 0 ∧
      (butcherShiftedLegendre 2).eval x₂ = 0
```

**Proof recipe**: `refine ⟨(3 - Real.sqrt 3) / 6, (3 + Real.sqrt 3) / 6, ?_, ?_, ?_, ?_, ?_⟩`.
* Set up `have hsqrt3_pos : (0 : ℝ) < Real.sqrt 3 :=
  Real.sqrt_pos.mpr (by norm_num)` and
  `have hsqrt3_sq : Real.sqrt 3 ^ 2 = 3 :=
  Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)` upfront.
* Distinctness: `intro h; linarith`.
* Membership in `(0, 1)`: each via `simp [Set.mem_Ioo]; constructor`,
  closed by `nlinarith [hsqrt3_sq, hsqrt3_pos]` using `√3 ≤ 2` derived
  from `Real.sqrt 3 ≤ Real.sqrt 4 = 2` (via `Real.sqrt_le_sqrt` +
  `Real.sqrt_four`), or directly from `(√3)² = 3 < 4`.
* Eval = 0 (both): `rw [butcherShiftedLegendre_two]`, then
  `simp only [Polynomial.eval_sub, Polynomial.eval_add,
   Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
   Polynomial.eval_X]`, then `nlinarith [hsqrt3_sq]` (the
  `(√3)² = 3` fact discharges the residue cleanly via
  `(3 ± √3)² = 12 ± 6√3` arithmetic).

The eval=0 step is the most delicate — if `nlinarith` stalls past
3 min, factor out a `have hroot_arith : ((3 - Real.sqrt 3) / 6)^2
* 6 - 6 * ((3 - Real.sqrt 3) / 6) + 1 = 0` lemma proved separately
with explicit `ring_nf` + `linear_combination` against `hsqrt3_sq`.

Estimated 30–50 LOC for the full P2.2 theorem.

### P2.3 — `n = 3` (DEFERRED, not in scope)

The three roots of `P_3^* = 20x³ - 30x² + 12x - 1` lie in `(0, 1)`
but their closed forms involve cubic-formula nested radicals.
Defer to a future cycle if needed; IVT-style sign analysis is the
viable route, requiring infrastructure that's part of the full
(342g) closure.

---

## §D Priority 3 (manual ship) — Upper bound `card_roots ≤ n`

The **upper-bound half** of (342g) is essentially free via Mathlib's
`Polynomial.card_roots'_le_natDegree` (or its alias) combined with
cycle 273's `butcherShiftedLegendre_natDegree = n`.

**Lean target**:
```lean
theorem butcherShiftedLegendre_card_roots_le (n : ℕ) :
    (butcherShiftedLegendre n).roots.toFinset.card ≤ n
```

**Proof recipe**:
```lean
calc (butcherShiftedLegendre n).roots.toFinset.card
    ≤ (butcherShiftedLegendre n).roots.card := Multiset.toFinset_card_le _
  _ ≤ (butcherShiftedLegendre n).natDegree := Polynomial.card_roots'_le_natDegree _
  _ = n := butcherShiftedLegendre_natDegree n
```

Verify the Mathlib name (`card_roots'_le_natDegree` vs
`card_roots_le_degree` vs an updated 2024+ alias) with
`lean_local_search "card_roots"` first. If `toFinset_card_le` does
not unify cleanly, ship the multi-set form
`(butcherShiftedLegendre n).roots.card ≤ n` instead — sufficient as
an upper bound, the `toFinset` version is a stretch.

~15 LOC including docstring.

---

## §E Priority 4 (housekeeping) — Update `lean_status.json` for `lem:342A`

Cycle 293 closed (342f). The `lem:342A` row's `status` stays
`partial` (since (342g) is open), but the cycle reference should
note (342f) is now in Lean as `butcherShiftedLegendre_recurrence`.
Recommended `lean_symbol` stays `butcherShiftedLegendre_norm_sq`
(cycle 281's general (342d)) since it's the most-cited downstream
clause, OR is updated to `butcherShiftedLegendre_recurrence` if the
planner prefers the latest milestone. Per
`extraction/CLAUDE.md`, `lean_status.json` is the only file under
`extraction/` that may be hand-edited.

Also extend `plan.md`'s `lem:342A` row cycle 293 closure note to
record that (342g) is the remaining open clause.

---

## §F What to AVOID this cycle

1. **Do NOT attempt the full (342g) closure manually.** Sign-change
   pairing on `Polynomial.roots` over `ℝ` is multi-cycle. Wait for
   Aristotle's return (cycle 295+ poll).

2. **Do NOT extend the explicit polynomial ladder past `n = 11`.**
   Cycle 288 closed `_eleven`; we have eleven concrete data points,
   well past the cycle 280 "seven sufficient" benchmark.

3. **Do NOT poll Aristotle this cycle.** Cycle 295 polls once.

4. **Do NOT re-attempt `Section441.lean` compile.** GPFS-blocked
   since cycle 182 (43+ consecutive timeouts). Skip per
   `cycle_182_gpfs_slowness.md`.

5. **Do NOT raise `maxHeartbeats` above 200000.** If P2.2's `nlinarith`
   stalls, decompose via a named `Real.sqrt_three_*` helper.

6. **Do NOT introduce `sorry`/`axiom`/`constant`.** All §C/§D
   deliverables must be axiom-clean (`[propext, Classical.choice,
   Quot.sound]`) or skipped entirely.

7. **Do NOT edit `scripts/autonomous_loop.py`.** Loop-maintainer
   territory per `tautology_scanner_false_positives.md`.

8. **Do NOT pursue P2.3 (`n = 3` zeros).** Out of scope; closed-form
   roots are cubic-formula nightmares.

9. **Do NOT introduce a new top-level file.** All §C/§D content goes
   into `OpenMath/Chapter3/Section342.lean` after line 3539.

---

## §G Pre-flight Mathlib hook verification

Before coding §C/§D, verify these names with `lean_local_search` or
`lean_loogle`:

| Goal | Candidate lemma | Risk |
|---|---|---|
| `(P_n^*).natDegree = n` | `butcherShiftedLegendre_natDegree` (cycle 273) | low — at HEAD |
| `Polynomial.eval` of explicit polynomial | `eval_sub`, `eval_mul`, `eval_C`, `eval_X`, `eval_pow` | low |
| `Real.sqrt 3 ^ 2 = 3` | `Real.sq_sqrt (h : 0 ≤ 3)` | low |
| `0 < Real.sqrt 3` | `Real.sqrt_pos.mpr` | low |
| `Real.sqrt 3 < 2` | derive via `(√3)² = 3 < 4` + `nlinarith [hsqrt3_sq]`, OR `Real.sqrt_lt_sqrt` + `Real.sqrt_four` | medium — verify path |
| `card_roots' ≤ natDegree` | `Polynomial.card_roots'_le_natDegree` (Mathlib 2024+) | medium — name drift possible |
| `Multiset.toFinset.card ≤ Multiset.card` | `Multiset.toFinset_card_le` | low |

If `Real.sqrt 3 < 2` resists, the cleanest backup is
`Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 3) (by norm_num : (3:ℝ) < 4)`
chained with `Real.sqrt_four : Real.sqrt 4 = 2` (verify name).

---

## §H Risk assessment and abort thresholds

| Risk | Probability | Mitigation |
|---|---|---|
| Aristotle submission file too large | low | trim cited-axiom bodies to statements only |
| P2.2 `nlinarith` on eval=0 stalls | medium | factor `have hroot_arith : <numerical identity> := by ring_nf; linear_combination hsqrt3_sq` first |
| `Real.sqrt 3 < 2` formulation resists | low | fall back to `Real.sqrt_lt_sqrt` + `Real.sqrt_four` |
| `card_roots'_le_natDegree` name drifted | medium | search alternatives; multi-set form `roots.card ≤ n` is fine |

**Abort threshold for §C P2.2**: if `nlinarith [hsqrt3_sq]` on the
eval=0 step doesn't close within 5 min wall, ship P2.1 only (and
defer P2.2 to cycle 295). Do NOT spend more than 30 min total on
the membership-in-`(0,1)` Real.sqrt bookkeeping for P2.2.

**Abort threshold for §D**: if `card_roots`-related names don't
resolve in 10 min, drop §D entirely; it's housekeeping, not
load-bearing.

**Abort threshold for §B**: if Aristotle CLI / MCP submission errors,
log the failure in the cycle 294 task results and pivot to ship §C
and §D only — Aristotle can be resubmitted in cycle 295. Do NOT
attempt to recover by hand-editing submission files.

---

## §I Total cycle scope estimate

* §B Aristotle submission: ~20 min (file prep + submit).
* §C P2.1 (`n = 1` root): ~10 min (~10 LOC).
* §C P2.2 (`n = 2` roots): ~45 min (~40 LOC).
* §D upper-bound `card_roots ≤ n`: ~20 min (~15 LOC).
* §E `lean_status.json` + `plan.md` update: ~5 min.
* §F write `task_results/cycle_294.md`, commit, push: ~15 min.

**Total**: ~2 hours target, ~70 LOC of Lean. Cycle 293 shipped 423
LOC; cycle 294 is intentionally ~6× smaller. **Measured cycle** —
the heavy lifting is the Aristotle submission, not local Lean code.

---

## §J Cycle 295+ outlook

**Branch A (Aristotle returns COMPLETE for (342g))**: integrate
the proof (likely 100–200 LOC of helper lemmas + main theorem)
following the cycle 277 / cycle 281 integration template. Update
`lean_status.json` for `lem:342A` → `formalized`. Cycle 296+ then
pivots to `lem:342B` (Gaussian quadrature exactness, now directly
tractable per cycle 293 task results) or `cor:342D` (Gaussian
quadrature RK order condition).

**Branch B (Aristotle IN_PROGRESS at low % at cycle 295 poll)**:
continue manual progress. Concrete next steps:
* Build sign-change extraction `signChangeSet : Polynomial ℝ →
  Finset ℝ` infrastructure (~50 LOC).
* Prove `(P_n^*).signChangeSet ⊆ Set.Ioo (0:ℝ) 1`.
* Build the product polynomial `Q := ∏ (X − C x)` and
  `Q.natDegree = card signChangeSet`.

**Branch C (Aristotle stalls multiple cycles)**: trigger manual
closure plan analogous to the cycle 289 Branch D protocol for
(342f). Open a `lem_342A_g_zeros_manual_closure_plan.md` issue file
with three phases (Phase A: sign-change extraction, Phase B:
orthogonality contradiction, Phase C: closure). Multi-cycle effort.

---

## §K Concrete file edits this cycle

1. **`OpenMath/Chapter3/Section342.lean`** (append after line 3539):
   * `butcherShiftedLegendre_one_root` (P2.1).
   * `butcherShiftedLegendre_two_roots` (P2.2).
   * `butcherShiftedLegendre_card_roots_le` (P3).
2. **`.prover-state/aristotle_submissions/cycle_294/342g_zeros.lean`**:
   new file with (342g) target + cited axioms (P1).
3. **`.prover-state/aristotle_submissions/cycle_294/README.md`**:
   new file recording the Aristotle project ID.
4. **`extraction/formalization_data/lean_status.json`** (P4):
   bump `lem:342A` cycle reference to 293 with (342f) closure
   note; status remains `partial`.
5. **`plan.md`**: extend `lem:342A` cycle 293 closure entry to
   note (342g) is the remaining open clause.
6. **`.prover-state/task_results/cycle_294.md`**: standard report.
7. **`.prover-state/issues/lem_342A_g_zeros_scoping.md`**:
   append "Cycle 294 update" section documenting Aristotle
   submission + the three concrete witnesses landed.

---

## §L Verification checklist before commit

* [ ] `lake env lean OpenMath/Chapter3/Section342.lean` exits 0.
* [ ] `lake env lean OpenMath/Chapter3.lean` exits 0.
* [ ] `grep -c sorry OpenMath/Chapter3/Section342.lean` returns 0.
* [ ] `lean_verify OpenMath.Chapter3.Section342.butcherShiftedLegendre_one_root` axiom-clean.
* [ ] `lean_verify OpenMath.Chapter3.Section342.butcherShiftedLegendre_two_roots` axiom-clean (if shipped).
* [ ] `lean_verify OpenMath.Chapter3.Section342.butcherShiftedLegendre_card_roots_le` axiom-clean (if shipped).
* [ ] Tautology-scanner regex (`:= h_\w+$ | exact h_\w+$ | := id$`) returns 0 hits in Section342.lean.
* [ ] Aristotle project ID logged in
      `.prover-state/aristotle_submissions/cycle_294/README.md`.
* [ ] `.prover-state/task_results/cycle_294.md` written with the
      "Worked on / Approach / Result / Faithfulness check / Dead
      ends / Discovery / Suggested next approach" template.

Ship the cycle.
