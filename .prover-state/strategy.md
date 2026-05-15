# Cycle 272 — strategy: ship (342e) Rodrigues bridge; fire-and-forget Aristotle on (342a)

## Context (one paragraph)

Cycle 271 opened §342 axiom-clean: `OpenMath/Chapter3/Section342.lean`
(165 LOC, 0 sorries) ships `butcherShiftedLegendre` (def) + (342b)
`P_n*(1) = 1` + (342c) `P_n*(1−x) = (−1)^n P_n*(x)`. The Approach A
recipe (`shiftedLegendre_eval_symm` + `coeff_shiftedLegendre`) closed
both on first attempt — no fallbacks fired. Cycle 271 explicitly
deferred (342a) orthogonality, (342d)–(342g) to cycles 272+ and
recommended (342e) **Rodrigues** as the highest-confidence
single-cycle (342*) deliverable (~50–80 LOC, low-risk, only
algebraic polynomial-ring machinery + `iteratedDeriv` tracking, no
analysis). The cycle 271 worker also flagged the option of
fire-and-forget Aristotle submission for (342a) at cycle-start.

Cycle 272 ships (342e) and optionally fires off (342a) to Aristotle.

---

## §A — Priority 0 (optional, ~5 min): fire-and-forget Aristotle submission for (342a) orthogonality

**Do this immediately if you intend to attempt (342a) manually in a
cycle ≥273.** Skip if you intend to leave (342a) deferred indefinitely.

If you decide to do it:

1. Verify the `aristotle` MCP is reachable
   (`mcp__aristotle__list_projects` returns recent projects).
2. Construct a self-contained snippet that
   - Imports `Mathlib.RingTheory.Polynomial.ShiftedLegendre`,
     `Mathlib.Analysis.SpecialFunctions.Integrals`,
     `Mathlib.Data.Real.Basic`,
     `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`.
   - States `butcherShiftedLegendre` exactly as cycle 271 defined it
     (line ~38 of `OpenMath/Chapter3/Section342.lean`).
   - States the orthogonality theorem with `m ≠ n` as a hypothesis:
     ```lean
     theorem butcherShiftedLegendre_orthogonal (m n : ℕ) (hmn : m ≠ n) :
         ∫ x in (0:ℝ)..1,
           (butcherShiftedLegendre m).eval x *
           (butcherShiftedLegendre n).eval x = 0 := sorry
     ```
   - **Includes** (342b) and (342c) as already-proven theorems in the
     snippet (Aristotle can use them as inputs). DO NOT include
     (342e) or other unproven properties.
3. Submit via `mcp__aristotle__submit_prompt` with prompt:
   "Fill in the sorry. The proof goes by integration by parts
   (n times) on Rodrigues' formula
   `n! · butcherShiftedLegendre n = (-1)^n · iteratedDeriv n
   (X^n · (1 - X)^n)` (lift the ℤ-polynomial to ℝ via
   `Polynomial.map (Int.castRingHom ℝ)`). After integration by parts,
   the boundary terms vanish because `X^n · (1 - X)^n` and its first
   `n-1` derivatives vanish at `0` and `1`; the remaining bulk term
   becomes `(-1)^n · ∫ (X^n · (1-X)^n) · derivative^[n] P_m*` which
   vanishes when `m < n` (since `derivative^[n] P_m*` has degree
   `m - n < 0`, i.e. is zero) and symmetrically when `m > n`."
4. **Record the project ID** in
   `.prover-state/aristotle_submissions/cycle_272/orthogonality.md`
   with submission timestamp.
5. **DO NOT POLL THIS CYCLE.** Per CLAUDE.md: one check after ~30
   min. Cycle 273+ can poll once.

If you do not want to submit (decision: leave deferred), skip this
priority entirely.

---

## §B — Priority 1 (main deliverable, ~60–90 min): ship (342e) Rodrigues bridge

**Target**: in `OpenMath/Chapter3/Section342.lean`, append

```lean
theorem butcherShiftedLegendre_rodrigues (n : ℕ) :
    Polynomial.C (n.factorial : ℝ) * butcherShiftedLegendre n
      = Polynomial.C ((-1 : ℝ) ^ n) *
        Polynomial.derivative^[n]
          ((Polynomial.X ^ n) * ((1 - Polynomial.X) ^ n)) := sorry
```

(see §B.2 for shape options; pick whichever yields the shortest proof
against the actual Mathlib hook).

### §B.1 — Verify the Mathlib hook ahead of writing the proof

Run `lean_local_search "factorial_mul_shiftedLegendre"` and confirm
at HEAD:

* `Polynomial.factorial_mul_shiftedLegendre_eq` exists. Expected
  shape (per cycle 271 task results §"Discovery"):
  ```
  (n.factorial : ℤ) • shiftedLegendre n
    = Polynomial.derivative^[n] ((X^n * (1 - X)^n : ℤ[X]))
  ```
  Variant possibilities: `derivative^[n]` may be written as
  `Polynomial.derivative^[n]` or as iterated composition; the LHS
  may use `•` (smul) or `*` with `C (n.factorial)`. Either form is
  fine — adapt the target statement to match.

* `Polynomial.map_pow`, `Polynomial.map_mul`, `Polynomial.map_sub`,
  `Polynomial.map_one`, `Polynomial.map_X` for the
  `Int.castRingHom ℝ` substrate push-down.

* `Polynomial.map_derivative` (single-step iterated-derivative
  commutation with `.map`). Then iterate by induction on `n` if no
  direct `Polynomial.map_iteratedDerivative` lemma exists — see §B.4
  for the 6-LOC backup.

### §B.2 — Statement shape options

There are three reasonable shapes; pick the one whose proof is
shortest against your verified Mathlib hook:

**Shape A (recommended; matches Mathlib's RHS most directly)**:
```lean
theorem butcherShiftedLegendre_rodrigues (n : ℕ) :
    Polynomial.C (n.factorial : ℝ) * butcherShiftedLegendre n
      = Polynomial.C ((-1 : ℝ) ^ n) *
        Polynomial.derivative^[n]
          ((Polynomial.X ^ n) * ((1 - Polynomial.X) ^ n)) := ...
```
Cycle 271's `(-1)^n * shiftedLegendre n` bookkeeping moves to the
RHS as `C ((-1)^n) * derivative^[n] (...)`, leaving `n! · P_n*` on
the LHS in Butcher's textbook form.

**Shape B (Butcher's textbook form)**:
```lean
theorem butcherShiftedLegendre_rodrigues (n : ℕ) :
    Polynomial.C (n.factorial : ℝ) * butcherShiftedLegendre n
      = Polynomial.derivative^[n]
          ((Polynomial.X * (1 - Polynomial.X)) ^ n) := ...
```
This requires absorbing the `(-1)^n` from cycle 271's definition
into the `(X · (1 - X))^n` substrate via `mul_pow`. Equivalent to
Shape A; pick by aesthetics.

**Shape C (with smul on ℝ)**:
```lean
theorem butcherShiftedLegendre_rodrigues (n : ℕ) :
    (n.factorial : ℝ) • butcherShiftedLegendre n
      = ((-1 : ℝ) ^ n) • Polynomial.derivative^[n]
          ((Polynomial.X ^ n) * ((1 - Polynomial.X) ^ n)) := ...
```
Mirrors the smul form Mathlib uses for
`factorial_mul_shiftedLegendre_eq`. Only choose this if Mathlib's
hook uses smul (verify in §B.1).

**Recommended: Shape A** (clean separation of cycle 271's sign
factor + matches Mathlib's hook RHS).

### §B.3 — Proof recipe (Shape A)

```lean
theorem butcherShiftedLegendre_rodrigues (n : ℕ) :
    Polynomial.C (n.factorial : ℝ) * butcherShiftedLegendre n
      = Polynomial.C ((-1 : ℝ) ^ n) *
        Polynomial.derivative^[n]
          ((Polynomial.X ^ n) * ((1 - Polynomial.X) ^ n)) := by
  -- Step 1: unfold butcherShiftedLegendre.
  unfold butcherShiftedLegendre
  -- LHS:
  --   C (n!) * (C ((-1)^n) * map ι (shiftedLegendre n))
  -- Step 2: regroup so that C ((-1)^n) is the outermost factor.
  -- (Both sides have C ((-1)^n) on the outside after this.)
  rw [← mul_assoc, mul_comm (Polynomial.C ((n.factorial : ℝ)))
        (Polynomial.C ((-1 : ℝ) ^ n)), mul_assoc]
  -- Now goal is:
  --   C ((-1)^n) * (C (n!) * map ι (shiftedLegendre n))
  --     = C ((-1)^n) * derivative^[n] (X^n · (1 - X)^n)
  -- Step 3: cancel C ((-1)^n) on both sides.
  congr 1
  -- Step 4: lift Mathlib's Rodrigues over ℤ to ℝ via map ι.
  have hMathlib := Polynomial.factorial_mul_shiftedLegendre_eq n
  -- hMathlib : (n.factorial : ℤ) • Polynomial.shiftedLegendre n
  --   = Polynomial.derivative^[n] (X^n * (1 - X)^n)   (over ℤ)
  -- (adapt the smul-vs-C-mul form based on actual Mathlib shape)
  have h := congrArg (Polynomial.map (Int.castRingHom ℝ)) hMathlib
  -- Step 5: push map through smul / C-mul on the LHS of h.
  -- (Pick the right hook: Polynomial.map_intCast_smul, or
  --  Polynomial.map_natCast_mul, or unfold smul to C-mul first.)
  -- Step 6: push map through derivative^[n] on the RHS of h.
  rw [map_iteratedDerivative_eq] at h        -- §B.4 helper
  -- Step 7: push map through the X^n · (1 - X)^n substrate.
  simp only [Polynomial.map_pow, Polynomial.map_mul,
             Polynomial.map_sub, Polynomial.map_one,
             Polynomial.map_X] at h
  exact h
```

The proof is mechanical once each step's exact Mathlib lemma name
is verified. The key Mathlib hooks to look up via §B.1:

1. `Polynomial.factorial_mul_shiftedLegendre_eq` — *exact name and
   shape* (smul vs C ·; over ℤ vs ℕ smul).
2. **`Polynomial.map_derivative`** (single-step iterated-derivative
   commutation with `.map`). Then build `map_iteratedDerivative_eq`
   by induction (§B.4) if Mathlib lacks the direct lemma.
3. **`Polynomial.map_intCast_smul`** or
   **`Polynomial.map_nsmul`** — pushing a `ℤ`/`ℕ` smul through `.map`.
   Search via `lean_loogle "Polynomial.map.*HSMul"` if needed.

### §B.4 — Backup recipe if `map_iteratedDerivative` is missing

Build the bridge by induction on `n`:

```lean
private lemma map_iteratedDerivative_eq
    (p : Polynomial ℤ) (n : ℕ) :
    Polynomial.map (Int.castRingHom ℝ) (Polynomial.derivative^[n] p)
      = Polynomial.derivative^[n]
          (Polynomial.map (Int.castRingHom ℝ) p) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Polynomial.map_derivative, ih]
```

~6 LOC private helper. `Polynomial.map_derivative` is the
single-step hook and is standard in Mathlib (confirmed present in
recent versions; verify name via `lean_local_search`).

### §B.5 — Mandatory non-vacuity witnesses

After the theorem closes, add at least three `example` blocks at
`n ∈ {0, 1, 2}` confirming the identity matches Butcher's small-`n`
values:

* `n = 0`: `1 · P_0*(x) = derivative^[0] (X^0 · (1−X)^0) = 1`. LHS
  is `C 1 · 1 = 1`. RHS reduces to `1`. (Possibly closes by `decide`
  or one-line `simp`.)
* `n = 1`: `1! · P_1*(x) = C ((-1)^1) · derivative (X · (1-X))
  = C (-1) · (1 - 2X) = 2X - 1`. Butcher's `P_1*(x) = 2x - 1`.
  Check via direct evaluation at a point (e.g. `eval 1/2 = 0`).
* `n = 2`: `2 · P_2*(x) = C 1 · derivative^[2] (X^2 · (1-X)^2)`.
  Butcher's `P_2*(x) = 6x² - 6x + 1`, so `2 · P_2* = 12x² - 12x + 2`.
  Verify via coefficient extraction or `eval 0 = 2`.

These witnesses ALSO serve as a sanity check on the sign convention:
if (342e) is stated with the wrong sign, `n = 1` will produce a
visible discrepancy (`-2X + 1` instead of `2X - 1`).

### §B.6 — Risk profile

| Risk | Mitigation |
|---|---|
| Mathlib hook name drift (`factorial_mul_shiftedLegendre_eq`) | Verify with `lean_hover_info` / `lean_local_search` before writing the proof |
| `map_iteratedDerivative` missing as a direct lemma | Use §B.4 backup induction (~6 LOC) |
| smul-vs-C-mul shape mismatch with Mathlib's hook | Adapt the `rw` chain at Step 5; try `Polynomial.intCast_mul`, `Polynomial.C_intCast`, or unfold smul to C-mul first |
| Sign convention error in (342e) | Catch at the `n = 1` non-vacuity witness; check `eval 1/2 = 0` |
| `Polynomial.map_intCast_smul` not the right name | Try `Polynomial.map_nsmul`, `Polynomial.map_zsmul`, or convert smul to multiplication first |
| `congr 1` peels wrong layer at Step 3 | Use `rw [Polynomial.C_inj]`-style cancellation, or `have h_ne : Polynomial.C ((-1 : ℝ) ^ n) ≠ 0 := by simp [pow_ne_zero]; ...` and divide |

None of these is showstopping; all have established workarounds.
Plan ~80–120 LOC budget (theorem body + private helper + three
non-vacuity examples + docstring).

### §B.7 — Aristotle suitability

Medium-high. The structural identity is exactly the kind of
`rw`/`simp` chain Aristotle handles well. If the manual proof
stalls past 60 minutes, submit a single Aristotle job with the
target theorem and the (342b)/(342c) infrastructure in context.
**DO NOT submit preemptively** — manual closure is faster than the
30-minute Aristotle poll cycle for ~80 LOC of pure algebra.

---

## §C — Priority 2 stretch (~30 min, OPTIONAL): degree lemma `(butcherShiftedLegendre n).natDegree = n`

If §B closes well within budget, add:

```lean
theorem butcherShiftedLegendre_natDegree (n : ℕ) :
    (butcherShiftedLegendre n).natDegree = n := by
  unfold butcherShiftedLegendre
  -- C ((-1)^n) * map ι (shiftedLegendre n)
  -- The factor C ((-1)^n) is nonzero, so natDegree = natDegree of map ι (P_n)
  rw [Polynomial.natDegree_C_mul (by
        rcases Nat.even_or_odd n with he | ho
        · simp [he.neg_one_pow]
        · simp [ho.neg_one_pow]
        -- or: exact pow_ne_zero _ (by norm_num)
        )]
  -- Now goal: (map ι (shiftedLegendre n)).natDegree = n
  -- Mathlib: Polynomial.natDegree_map_eq_iff_of_injective for non-zero leading coeff
  sorry  -- worker: close via Polynomial.natDegree_shiftedLegendre + leadingCoeff non-zero argument
```

Mathlib gives `Polynomial.natDegree_shiftedLegendre n = n`
(`@[simp]`). The lift to `butcherShiftedLegendre` via `map` and
`C ·` multiplication should be ~10–20 LOC.

**Skip if §B took the full cycle budget.** Do NOT leave a sorry in
the stretch; if it doesn't close cleanly, omit the lemma entirely.

---

## §D — What NOT to try this cycle

* **DO NOT attempt (342a) orthogonality manually.** 200–400 LOC,
  multi-cycle. Submit to Aristotle (§A) if pursuing, otherwise defer.
* **DO NOT attempt (342d) `∫ P_n*² = 1/(2n+1)`.** Depends on (342a).
* **DO NOT attempt (342g) distinct zeros.** Depends on (342a).
* **DO NOT attempt (342f) three-term recurrence.** Higher risk
  (~150 LOC) than (342e); cycle 273 candidate if (342e) lands clean.
* **DO NOT modify cycle 271 deliverables** (`butcherShiftedLegendre`,
  `butcherShiftedLegendre_eval_one`,
  `butcherShiftedLegendre_eval_one_sub`, or non-vacuity examples).
  They are axiom-clean and load-bearing for §B.
* **DO NOT pivot to polymorphic-`E` Phase D.2/E.2** (cycle 270's
  leftover candidate). Cycle 265's HIGH-risk
  `ContinuousMultilinearMap` plumbing flag still applies; §342
  yields more textbook progress per cycle.
* **DO NOT attempt `lem:310B` Phase A.1**
  (`RootedTree.Vertex` scaffold). It's a legitimate target but
  belongs to a different sub-track; finish §342 cluster first.
* **DO NOT raise `maxHeartbeats` above 200000.** If §B's `ring` or
  `simp` chain stalls, decompose via the §B.4 backup induction.
* **DO NOT introduce `axiom` or `constant` declarations.**
* **DO NOT introduce sorries.** Cycles 149/200/201 all rolled back
  sorry-first scaffolds; cycle 272's deliverable must be axiom-clean
  or skipped entirely. Sorry count must remain 0.
* **DO NOT modify `scripts/autonomous_loop.py`.**
* **DO NOT attempt to compile `OpenMath/Chapter4/Section441.lean`
  on GPFS.** 43+ consecutive timeouts since cycle 182. Skip per
  `cycle_182_gpfs_slowness.md`.
* **DO NOT poll Aristotle this cycle** if you submitted in §A.
  Single poll discipline: cycle 273 checks once.
* **DO NOT use `push_cast` on `(Int.castRingHom ℝ) ((-1)^n)`** —
  cycle 271 dead end. Use `simp only [map_pow, map_neg, map_one]`
  instead (the `RingHom` `map_*` simp lemma family).
* **DO NOT use `simp only [Matrix.dotProduct]`** anywhere —
  `dotProduct` is at root namespace, not `Matrix.dotProduct` (cycle
  167 dead end).
* **DO NOT use `Polynomial.ext + ring`** on rational `C` constant
  identities (cycles 172/173 dead end); `ring` cannot fold
  `Polynomial.C (4/3) - Polynomial.C (-1/3) = Polynomial.C (5/3)`.
  Cycle 180's `Polynomial.funext + ring` recipe is the canonical
  closure for `Polynomial ℝ` constant arithmetic — but (342e) is
  symbolic, so this should not bite this cycle.

---

## §E — Pre-flight checklist (do these in order at cycle-start)

1. **Verify branch state** (≤30s):
   - `git log -1 --format='%H %s'` should show
     `191c709 Cycle 271 — §342 opening …`.
   - `wc -l OpenMath/Chapter3/Section342.lean` should show ~165 LOC.
   - `grep -c sorry OpenMath/Chapter3/Section342.lean` should be `0`.

2. **Decide on Aristotle submission for (342a)**. If yes, do §A
   first (~5 min). If no, skip.

3. **Verify Mathlib hook `Polynomial.factorial_mul_shiftedLegendre_eq`
   exists at HEAD** before writing §B's proof. Use
   `lean_local_search "factorial_mul_shiftedLegendre"` or
   `lean_hover_info` from inside Section342.lean. If the name has
   drifted, adapt the §B.3 recipe. ALSO verify the exact shape
   (smul-vs-C-mul; index over ℕ-or-ℤ).

4. **Ship §B Priority 1 (Rodrigues bridge)** following the §B.3
   recipe. Add §B.5 non-vacuity witnesses. Run `lake env lean
   OpenMath/Chapter3/Section342.lean` after each significant edit.

5. **Run `#print axioms butcherShiftedLegendre_rodrigues`** (and the
   private helper if any) via `lean_verify`. Expected:
   `[propext, Classical.choice, Quot.sound]` only.

6. **Run `lake env lean OpenMath/Chapter3.lean`** to confirm no
   downstream regressions.

7. **If time permits**, ship §C stretch (`natDegree` lemma).
   Otherwise skip.

8. **Write `task_results/cycle_272.md`** documenting deliverables,
   axioms, non-vacuity, and any deviations from this strategy.

9. **Update `lean_status.json`** for `lem:342A`: keep at `partial`
   (the JSON tracks per-entity status, not per-property; even with
   (342b), (342c), (342e) closed, the entity as a whole — covering
   all of 342a-g — remains partial until orthogonality lands).

10. **Update `plan.md`** entry for `lem:342A` to note cycle 272's
    new closure (342e), maintaining `[~]` status.

11. **Commit** with message
    `Cycle 272 — §342 (342e) Rodrigues bridge SHIPPED.`

---

## §F — Success criteria

* `butcherShiftedLegendre_rodrigues` shipped axiom-clean
  (`[propext, Classical.choice, Quot.sound]`).
* At least 3 non-vacuity `example`s on `n ∈ {0, 1, 2}` confirming
  Butcher's small-`n` values match.
* Sorry count: 0 → 0.
* No regressions on cycle 271's (342b)/(342c) or any other §3 file.
* `OpenMath/Chapter3.lean` aggregator builds.

Stretch (Priority 2): `butcherShiftedLegendre_natDegree` shipped
axiom-clean. Skip — do NOT leave a sorry — if it doesn't close
cleanly.

Optional (Priority 0): Aristotle (342a) project ID recorded for
cycle 273+ polling.

---

## §G — Outlook for cycle 273+

After (342e) lands:

* **Cycle 273 candidates** (single-cycle each):
  * (342f) three-term recurrence — ~150 LOC if Mathlib's
    `shiftedLegendre` has a recurrence already; otherwise direct via
    `coeff_shiftedLegendre` induction.
  * Polymorphic-`E` lift of cycle 266's
    `bseriesExactTerm_cherry_scalar` (Phase D.1/E.2 of
    `lem_310B_plan.md`). MEDIUM-HIGH risk per cycle 265's
    `ContinuousMultilinearMap` plumbing flag.
  * `lem:310B` Phase A.1 (`RootedTree.Vertex` + `vertices` Finset).
    80–120 LOC, axiom-clean target.

* **Cycle 273 Aristotle poll** (if §A submitted): one check, decide
  closure path. If COMPLETE clean → incorporate; if
  COMPLETE_WITH_ERRORS → apply suggested fixes; if IN_PROGRESS at
  low % → cancel and pivot.

* **Cycles 274+** depend on whether (342a) Aristotle returns
  cleanly. If yes → (342d) and (342g) become single-cycle
  consequences. If no → manual (342a) attempt (multi-cycle) or
  pivot to (342f) / polymorphic-`E` / `lem:310B` infrastructure.
