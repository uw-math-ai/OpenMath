# Cycle 072 strategy — commit staged cycle 071 work, then close `hstart_tendsto`

## Phase summary

Cycle 071 produced **real, substantive Lean work** (+268/−8 lines
across `Section404.lean` and `Section405.lean`: scaffold for
`convergent_isStable` plus 5 new helper lemmas), but **failed to
commit it**. The supervisor's score=−2 was a "no Lean diff" signal
caused by the missing commit, not a code-quality verdict. The work
is currently staged in the working tree at HEAD `9c209da` (Cycle
070).

Independently, the supervisor flagged `Section404.lean:4695` as a
"tautological proof". This is a scanner false positive of the same
type as cycles 010/013/014/015 (see
`tautology_scanner_false_positives.md`): line 4695 is part of a
**theorem statement** (the `∑ i : Fin k, M.α i.succ` summand inside
`globalError_recurrence_bound_textbook_nonauto_corollary`'s goal),
not a proof body. There is nothing for the worker to fix.

`Sorry locations` confirms only **one** sorry remains in the staged
tree: `Section405.lean:145` — the `hstart_tendsto` sub-claim inside
`convergent_isStable`. Cycle 072's deliverable is closing it.

---

## Priority 0 — Commit the staged cycle 071 work (BLOCKING)

Before doing anything else, verify the staged work is sound, then
**commit it**. This is the most important deliverable of cycle 072:
without it, cycle 071's helpers and scaffold are invisible to the
git history and to all downstream tooling.

### Step 0a — Verify the staged content compiles

Run, in order:

```bash
git status --short
git diff --stat HEAD -- OpenMath/
lake env lean OpenMath/Chapter4/Section404.lean
lake env lean OpenMath/Chapter4/Section405.lean
```

**Expected:**

* `git diff --stat`: ~+173/−0 in `Section404.lean`, ~+95/−8 in
  `Section405.lean`.
* Both `lake env lean` invocations exit cleanly. `Section405.lean`
  emits exactly **one** `sorry` warning at line 145.

If anything else turns up, stop and diagnose before proceeding.

### Step 0b — Verify the line-4695 "tautology" is a false positive

Run:

```bash
sed -n '4670,4710p' OpenMath/Chapter4/Section404.lean
```

Confirm visually that lines 4694–4704 are inside the **statement**
of `LinearMultistepMethod.globalError_recurrence_bound_textbook_nonauto_corollary`
(it's the `|yex … − Y n − ∑ … |` summand of the goal type), not a
proof body. The `∑ i : Fin k, M.α i.succ` substring on line 4695
is a quantifier-bound sum head, not a closer like `exact M.α …`.

This matches the `tautology_scanner_false_positives.md` issue file
(D1: scanner over-counts comment-stripped line numbers; D2: regex
fires inside multi-line theorem signatures). **Do NOT attempt to
"fix" line 4695 — the proof is correct.** If the supervisor's
prompt for the next cycle still flags this line, treat it as
phantom carry-over (cf. the cycle 008/014/015 phantom commits).

### Step 0c — Commit

If steps 0a and 0b pass, the staged work is sound. The natural
flow is to combine cycle 071's staged work with cycle 072's
`hstart_tendsto` closure into a **single commit** at the end of
this cycle, with a commit message that names both:

```
Cycle 072 — close thm:405A (convergent_isStable); land cycle 071 staging
```

This avoids the awkward "two commits in one cycle" pattern and
keeps `Section404.lean` / `Section405.lean` history monotone. The
combined commit gets all of `Section404.lean`'s 5 new helpers
(`runningMaxAbs` def + `runningMaxAbs_monotone` /
`runningMaxAbs_ge_abs` / `runningMaxAbs_atTop_of_unbounded` /
`runningMaxAbs_record_above` / `IsHomogeneousSolution.const_smul` /
`unbounded_homogeneous_contra`) and `Section405.lean`'s scaffold
**plus** the discharged `hstart_tendsto`.

If `hstart_tendsto` proves harder than expected (>2 hours of
worker effort), commit cycle 071's staged work *first* as a
self-contained cycle-072 delivery (drop the scaffold's outer
proof body, leave the original cycle-070 sorry intact in
`Section405.lean`, ship only the helpers), then defer the
scaffold + `hstart_tendsto` to cycle 073. Do NOT let cycle 072
end with another empty Lean diff.

---

## Priority 1 — Close `hstart_tendsto` (Section405.lean:145)

After Priority 0 verification, work on the lone remaining sorry.

### Goal

```lean
have hstart_tendsto : ∀ i : Fin k,
    Filter.Tendsto (fun h : ℝ => start h i) (nhds 0) (nhds 0)
```

where `start h i := if 0 < h then y i.val / ζ (Nat.ceil (1 / h)) else 0`
and `ζ = LinearMultistepMethod.runningMaxAbs y` is unbounded
(`hζ_atTop : Filter.Tendsto ζ Filter.atTop Filter.atTop`).

### Mathematical argument

Two-sided limit at `0`:

1. **Left side `h ≤ 0`**: the `if` branch is `else`, so
   `start h i = 0`. Trivially `Tendsto 0 (𝓝 0)` — handled by
   `tendsto_const_nhds` after restricting via `nhdsWithin_Iic_le`
   (or by case-splitting `h ≤ 0` vs `0 < h`).
2. **Right side `0 < h`**: `start h i = y i.val / ζ (Nat.ceil (1/h))`.
   * `1 / h → ∞` as `h → 0⁺` (Mathlib: search
     `Filter.tendsto_inv_zero_atTop` or
     `tendsto_one_div_atTop_nhds_zero` and look at the converse).
   * `Nat.ceil` monotone-and-cofinal: `Nat.ceil (1/h) → ∞` via
     `Nat.tendsto_ceil_atTop` (verify the exact name with
     `lean_local_search`; may live as `Nat.ceil_tendsto_atTop`
     or as `tendsto_natCeil_atTop`).
   * `ζ` unbounded composed with `→ ∞` gives
     `ζ (Nat.ceil (1/h)) → ∞`: `hζ_atTop.comp <Nat.ceil → ∞>`.
   * Quotient of constant numerator by `→ ∞` denominator → 0:
     `Filter.Tendsto.div_atTop tendsto_const_nhds <ζ-atTop>` (or
     `tendsto_const_div_atTop_nhds_zero_iff` if available).

### Recommended Lean tactic shape

The cleanest tactic shape is to split on the sign of `h` using
filter restriction. Outline:

```lean
have hstart_tendsto : ∀ i : Fin k,
    Filter.Tendsto (fun h : ℝ => start h i) (nhds 0) (nhds 0) := by
  intro i
  -- Right-tail: from `0 < h`, `start h i = y i.val / ζ (Nat.ceil (1/h))`.
  -- Show this branch tends to 0 as h → 0⁺.
  have h_right : Filter.Tendsto (fun h : ℝ => start h i)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h_inv_atTop : Filter.Tendsto (fun h : ℝ => 1 / h)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
      -- look up: tendsto_one_div_atTop / tendsto_inv_zero_atTop
      sorry
    have h_ceil_atTop : Filter.Tendsto
        (fun h : ℝ => (Nat.ceil (1 / h) : ℕ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
      -- compose Nat.ceil monotone-cofinal with h_inv_atTop
      sorry
    have h_zeta_atTop : Filter.Tendsto
        (fun h : ℝ => ζ (Nat.ceil (1 / h)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop :=
      hζ_atTop.comp h_ceil_atTop
    -- Bounded numerator / unbounded denominator → 0.
    have h_quot : Filter.Tendsto
        (fun h : ℝ => y i.val / ζ (Nat.ceil (1 / h)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      -- look up: Filter.Tendsto.div_atTop (numerator nhds, denom atTop)
      sorry
    -- Eventually (within Ioi 0) the if-branch is the y/ζ term.
    refine (Filter.tendsto_congr' ?_).mpr h_quot
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp [start, hh]
  -- Left-tail: for h ≤ 0, start h i = 0.
  have h_left : Filter.Tendsto (fun h : ℝ => start h i)
      (nhdsWithin (0 : ℝ) (Set.Iic 0)) (nhds 0) := by
    refine (Filter.tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with h hh
    have : ¬ 0 < h := not_lt.mpr hh
    simp [start, this]
  -- Combine via `nhds_eq_nhdsWithin_Ici_sup_nhdsWithin_Iic`-style fact.
  rw [← nhdsWithin_univ]
  rw [show (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ioi 0 by
        ext x; constructor <;> intro h <;> · cases le_or_lt x 0 <;> simp [*]]
  rw [nhdsWithin_union]
  exact Filter.Tendsto.sup h_left h_right
```

The exact splice (`nhdsWithin_union` vs. `nhds_eq_…_sup_…`) may
need adjustment; consult `lean_local_search "nhdsWithin"` for the
right lemma. `Filter.Tendsto.sup` is the combinator that takes two
`Tendsto` facts on filters whose join is the target.

### Mathlib lemma cheatsheet

Verify each name with `lean_local_search` before trusting it.

| Goal | Lemma (verify before use) |
|---|---|
| `1/h → ∞` as `h → 0⁺` (within `Set.Ioi 0`) | `tendsto_inv_zero_atTop` (note: this is for `nhdsWithin 0 (Ioi 0)`); check naming |
| `Nat.ceil` cofinal: `(x → ∞) → (Nat.ceil x → ∞)` | `Nat.tendsto_ceil_atTop` or compose `Nat.le_ceil` + `tendsto_natCast_atTop_iff` |
| Compose `Tendsto`s | `Filter.Tendsto.comp` |
| Const / atTop → 0 | `Filter.Tendsto.div_atTop` (numerator nhds c, denom atTop, result nhds 0) |
| Combine left/right limits | `nhdsWithin_Iic_sup_Ioi`-style lemma + `Filter.Tendsto.sup` |
| Eventually-equal congruence | `Filter.tendsto_congr'` + `filter_upwards` |
| Self in `nhdsWithin` | `self_mem_nhdsWithin` |
| `Metric.tendsto_nhds_nhds` ε-δ unfold (fallback) | `Metric.tendsto_nhds_nhds` |

If any name is missing or renamed, use `lean_loogle` with the
type pattern (e.g. `Tendsto _ (nhdsWithin _ _) atTop`).

### Aristotle batch submission (recommended at start of cycle)

This sub-claim is canonical filter chasing — Aristotle's strong
suit. Bundle it into a single Aristotle job at the **start** of
cycle 072 with a self-contained statement that abstracts away the
LMM-specific scaffolding:

```lean
-- Goal: from hζ_atTop : Tendsto ζ atTop atTop and a constant c : ℝ,
-- conclude that fun h ↦ if 0 < h then c / ζ (Nat.ceil (1/h)) else 0
-- tends to 0 as h → 0.
example (ζ : ℕ → ℝ) (hζ_atTop : Filter.Tendsto ζ Filter.atTop Filter.atTop)
    (c : ℝ) :
    Filter.Tendsto
      (fun h : ℝ => if 0 < h then c / ζ (Nat.ceil (1 / h)) else 0)
      (nhds 0) (nhds 0) := by
  sorry
```

Submit this single job, sleep 30 min per CLAUDE.md. While waiting,
attempt the proof manually using the recommended tactic shape. If
Aristotle returns first with a clean proof, port it into
`Section405.lean` (likely as a private helper lemma) and use it to
discharge `hstart_tendsto`. If your manual proof finishes first,
keep yours and discard Aristotle's (per the cycle 071 precedent
for `runningMaxAbs_atTop_of_unbounded`).

### Anti-patterns (do NOT try)

* **Do NOT try `simp` or `norm_num` on the goal directly.** It
  involves a non-elementary filter limit; nothing in `simp`'s
  database closes it.
* **Do NOT introduce `axiom` or `constant`.** CLAUDE.md is explicit.
* **Do NOT generalize `start` or rewrite the IVP setup.** The
  scaffold uses a piecewise `if 0 < h` definition for a reason —
  changing it ripples into `hY_props` (which discharges
  `start ((1-0)/m) i = y i.val / ζ m` via `if_pos`) and would
  invalidate the already-proven `hY_props` block at lines 149–173.
* **Do NOT raise `maxHeartbeats`.** If the proof is heavy,
  decompose into a separate private lemma in `Section404.lean`
  (e.g. `runningMaxAbs_quotient_tendsto_zero`) so the inline goal
  stays small.
* **Do NOT poll Aristotle more than once.** One status check
  after the 30-min sleep is the rule.

---

## Priority 2 — After landing `convergent_isStable`

If Priority 1 closes cleanly within the cycle's budget, the
remaining cycle 072 deliverable is bookkeeping:

1. Update `extraction/formalization_data/lean_status.json`: mark
   `thm:405A` as `formalized` (file
   `OpenMath/Chapter4/Section405.lean`, ~line 101). With
   `thm:405A`, `thm:405B`, `thm:405C` all formalized, also flip
   `thm:243A` from `partial` to `formalized` (the iff packager
   landed in cycle 069; with `convergent_isStable`,
   `convergent_isPreconsistent`, and `convergent_isConsistent`
   all closed, the reverse direction of the iff is fully proved).
2. Update `plan.md`: change the `[~]` markers on `thm:405A` and
   `thm:243A` to `[x]`, increment the progress counter
   (`Progress: 41 / 175` → `43 / 175`; cross-chapter deferral
   resolves).
3. Trim `attempts.md` of stale rows referring to cycle 071's
   "no commit" verdict and the line-4695 phantom (write a
   one-line note "cycle 072 confirmed cycle-071 staged work
   committed; line 4695 is a scanner false positive per
   `tautology_scanner_false_positives.md`").

---

## Priority 3 — Faithfulness check before commit

Per CLAUDE.md's Pre-Commit Faithfulness Checklist:

* `convergent_isStable`: textbook statement (Butcher §405A) is
  "A convergent linear multistep method is stable." Lean
  statement matches verbatim
  (`(hConv : M.IsConvergent) : M.IsStable`). ✓
* The proof uses the strengthened `IsConvergent` predicate
  (cycle 068, `is_convergent_strengthened.md`); this is already
  documented and accepted.
* The trivial-IVP setup `f ≡ 0, yex ≡ 0, x = 1` matches Butcher's
  textbook proof (Butcher's argument also uses a trivial IVP
  with starting values rescaled by `ζ_n`).
* Tautology check: conclusion `M.IsStable` is not a hypothesis. ✓
* Identity check: the proof is a non-trivial scaffold + 6 helpers
  + the new `hstart_tendsto`. Not vacuous. ✓
* `runningMaxAbs` and helpers: pure infrastructure, not Butcher
  entities; faithfulness check N/A. The recursive
  `runningMaxAbs (n+1) = max (|y (n+1)|) (runningMaxAbs n)` is
  the standard "running max" definition.

After commit, run `#print axioms LinearMultistepMethod.convergent_isStable`
to confirm only `[propext, Classical.choice, Quot.sound]`.

---

## Cycle 073 outlook (for context, not this cycle)

Once `convergent_isStable` lands and `thm:243A` is formalized,
the remaining unblocked Chapter 4 entities (per `plan.md`) are
in §410 (criteria for order: `thm:410A`, `thm:410B`, `thm:410C`,
`thm:410D`) and §422 (`thm:422A` underlying one-step method,
`thm:422C` LMM convergence). `thm:410A` is the natural §410
entry point and unblocks §410B–D. The §441 maximum-order theorems
are downstream of §410 and §431.

Defer §451 G-stability and §454 concluding remarks until the
§410/§422 cluster is in.

---

## Reminders

* CLAUDE.md "Aristotle-first": batch-submit `hstart_tendsto` (and
  any spin-off helpers) at the start of the cycle, sleep 30 min,
  then proceed with manual work.
* CLAUDE.md "Sorry-first": the scaffold already follows this
  pattern — `convergent_isStable` is fully structured, `sorry`
  isolated to one spot.
* CLAUDE.md "Never raise `maxHeartbeats`": if the closing
  argument is heavy, decompose into a private helper lemma.
* Do NOT poll Aristotle more than once per cycle.
* Do NOT modify `scripts/autonomous_loop.py` from the worker.
* The "tautology at line 4695" is a phantom — do not touch.

---

## Cross-references

* `.prover-state/issues/thm_405B_attempt.md` — closed cycle 069;
  similar shape (`convergent_*` lemmas closing via trivial IVPs).
* `.prover-state/issues/is_convergent_strengthened.md` — explains
  why `IsConvergent` carries joint-Lipschitz / `ContDiff` /
  bounded hypotheses.
* `.prover-state/issues/tautology_scanner_false_positives.md` —
  underlying scanner bugs; confirms the line-4695 false positive.
* `.prover-state/task_results/cycle_071.md` — full cycle 071
  deliverable record (in working tree, staged but not committed).
* `OpenMath/Chapter4/Section405.lean:101` — scaffold for
  `convergent_isStable`.
* `OpenMath/Chapter4/Section405.lean:145` — the lone remaining
  `sorry` (`hstart_tendsto`).
* `OpenMath/Chapter4/Section404.lean:5475` — cycle 068's
  `stable_consistent_isConvergent` (forward direction of the
  cycle-069 iff packager).
