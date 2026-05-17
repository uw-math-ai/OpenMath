# Cycle 362 — §422 Phase D.3.b parametricity step (Step 1)

## §A — Context check (5 min, mandatory before any code)

There is **no Aristotle batch to integrate** this cycle.

Repository state at HEAD `f046f5a` (cycle 361 ship):

* `OpenMath/Chapter4/Section422.lean` — 2120 LOC, **0 sorries**, builds clean.
* §422 streak: **27 consecutive axiom-clean cycles** (336–361).
* Last four deliverables on the Phase D.3 ladder:
  - Cycle 358: D.3.a.{1,2} (`elementaryWeightQ_phi_{mul,inv}_mk`).
  - Cycle 359: D.3.a.3 (`RKTableau.powRep` + `_pow_succ_mk`).
  - Cycle 360: D.3.b sig + base cases (`linearResidualAt` + `_vertex_eq_zero` + `_one_mk_eq`).
  - Cycle 361: D.3.b ℤ-form lift + general `i = m+1` closed form
    (`_zpow_{natCast,negSucc}_mk` + `_succ_mk_eq`).

The "What I'm stuck on" field in the prompt is **empty**; sorry count
is **0**. This is the same phantom-template firing pattern diagnosed
in `consultant_advice_cycle_248.md` / `consultant_advice_cycle_263.md`.
There is no remediation work; cycle 362 pivots directly to the next
planned deliverable.

Pre-flight verification (run once at cycle start):

```
git log -1 --format='%H %s'              # f046f5a … cycle 361 ship
wc -l OpenMath/Chapter4/Section422.lean  # 2120
grep -c sorry OpenMath/Chapter4/Section422.lean  # 0
```

If any disagrees, escalate; otherwise proceed to §B.

## §B — What to work on

**Primary target (P1, ~80–110 LOC, expected axiom-clean):**

Phase D.3.b inductive step **Step 1**, per the cycle 361 worker's
"Suggested next approach" recorded in
`.prover-state/issues/def_422B_phase_D_3_scoping.md` §"Cycle 362
entry point" (lines 605–612).

Ship a **per-`derivativeWeightWithSrc` substitution lemma** under
strict-subtree agreement of the source method's elementary weights:

```lean
/-- *Phase D.3.b inductive step Step 1 (cycle 362).* If two source
tableaux `M₁` and `M₁'` agree on elementary weights at every tree of
order strictly less than `t.order`, then `derivativeWeightWithSrc`
on `t` is unchanged (for any inner tableau `M₂` and stage `i`).

This is the cycle 226 `derivativeWeightWithSrc_subst_M₁` template
(which used the stronger `PhiEquivalent M₁ M₁'` hypothesis, i.e.
full elementary-weight agreement at every tree) **weakened** to the
substitution structure that the Phase D.3.b parametricity claim
needs: `M₁` and `M₁'` only have to agree at strict subtrees of `t`
because `derivativeWeightWithSrc M₂ M₁ i (mk children)` references
`M₁.elementaryWeight` exclusively at `c ∈ children` (strict subtrees
of `t`) and recursively at sub-subtrees of those (also strict
subtrees of `t` since order strictly decreases). -/
private theorem derivativeWeightWithSrc_eq_of_strict_subtree_agreement
    {s₁ s₁' s₂ : ℕ}
    {M₁ : RKTableau s₁} {M₁' : RKTableau s₁'}
    (M₂ : RKTableau s₂) :
    ∀ (t : RootedTree)
      (_h_strict : ∀ s : RootedTree, s.order < t.order →
          M₁.elementaryWeight s = M₁'.elementaryWeight s)
      (i : Fin s₂),
      M₂.derivativeWeightWithSrc M₁ i t
        = M₂.derivativeWeightWithSrc M₁' i t
```

Plus the obvious list-helper companion via a `mutual` block (signature
in §C.2 below).

**Place** the new mutual block in
`OpenMath/Chapter3/Section381.lean` **immediately after cycle 226's
`derivativeWeightWithSrc_subst_M₁` / `derivativeWeightWithSrcProd_subst_M₁`
block** (after line 2803, before the next `end` / `section` divider).
Mark both as `private` — they are Phase D.3.b infrastructure, not
public API.

**Plus one non-vacuity `example`** in
`OpenMath/Chapter4/Section422.lean` (after cycle 361 examples,
line ~2118):
exercise the substitution lemma with `M₁ = M₁' := explicitEuler`
at `t := RootedTree.cherry` (order 2). The trivial-agreement case
confirms the signature compiles and the lemma fires. A more
substantive witness exercising genuinely-distinct tableaux that
agree only at strict subtrees of `cherry` is left to cycle 363+
(it requires constructing two RKTableaux with deliberately matched
strict-subtree weights, which is more bookkeeping than the cycle's
budget allows).

**Stretch target (P2, ~60–80 LOC, foreseeably multi-cycle):**

If P1 closes within ~75 min budget, attempt the parametricity claim:

```lean
/-- *Phase D.3.b inductive step Step 2 (cycle 362 stretch).* The
linear residual `linearResidualAt i η_q t` depends only on `η_q`'s
values at strict subtrees of `t`. -/
theorem linearResidualAt_depends_only_on_strict_subtrees
    (i : ℕ) (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (t : RT)
    (h_strict : ∀ s : RT, s.order < t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    linearResidualAt i η_q t = linearResidualAt i η_q' t
```

P2 is **foreseeably multi-cycle**. Per cycle 361 worker's analysis,
the residual `linearResidualAt (m+1) ⟦M⟧ t` from the cycle 361
`_succ_mk_eq` closed form contains both the
`(M.powRep (m+1)).2.derivativeWeightWithSrc` sum (Step 1 handles
its substitution behaviour) AND a separate `M.elementaryWeight t`
term — so the cancellation of the linear-in-η_q(t) part is a
substantive algebraic identity, not just substitution. If P2 is
attempted, the path is:
- `Quotient.inductionOn₂` on `η_q, η_q'` to get representatives `M, M'`.
- Bridge `elementaryWeightQ_phi ⟦M⟧ s = M.elementaryWeight s` via cycle 226.
- Apply cycle 361's `_succ_mk_eq` to both sides.
- Cancel the `M.elementaryWeight t` and `M'.elementaryWeight t` terms
  by showing they equal via some property of the
  `(M.powRep (m+1)).2.derivativeWeightWithSrc` sum (the substantive
  identity — may not be tractable in 60–80 LOC).
- Apply Step 1 (P1) to each `derivativeWeightWithSrc` term on each side.

If P2 stalls within the stretch budget, **document the analysis in
the cycle results and defer to cycle 363**. Do not ship a partial
sorry-bearing P2.

**Graceful degradation (P3, fallback if P1 stalls):**

Pivot to the cycle 363 deliverable
**`sum_i_alpha_ne_zero_of_stable_preconsistent`** (Phase D.3.c) as
a small-LOC ship. Per §D.3 below, this is a 1–2 line corollary of
existing cycle 176 + cycle 344 infrastructure (~10 LOC + 1 BDF2
witness). Use ONLY IF P1 stalls past ~75 min; otherwise hold for
deliberate cycle 363 ship.

## §C — Concrete proof recipe for P1

### §C.1 — Mathematical content

For `t = mk children`,

```
derivativeWeightWithSrc M₂ M₁ i (mk children)
  = derivativeWeightWithSrcProd M₂ M₁ i children
  = ∏_{c ∈ children} (M₁.elementaryWeight c
                       + Σⱼ M₂.A i j · derivativeWeightWithSrc M₂ M₁ j c)
```

Each `c ∈ children` has `c.order < (mk children).order = t.order`
(by cycle 343 `RootedTree.order_lt_of_mem_children`), so
`M₁.elementaryWeight c` is read at a strict subtree of `t`. The
recursive `derivativeWeightWithSrc M₂ M₁ j c` references
`M₁.elementaryWeight` at `c`'s strict subtrees, which are
sub-subtrees of `t` — also strict subtrees of `t` since `s.order <
c.order < t.order`. So the entire computation only sees
`M₁.elementaryWeight` at strict subtrees of `t`; hence agreement at
strict subtrees implies equality.

### §C.2 — Mutual induction structure (mirrors cycle 226)

```lean
mutual
  private theorem derivativeWeightWithSrc_eq_of_strict_subtree_agreement
      {s₁ s₁' s₂ : ℕ}
      {M₁ : RKTableau s₁} {M₁' : RKTableau s₁'}
      (M₂ : RKTableau s₂) :
      ∀ (t : RootedTree)
        (_h_strict : ∀ s : RootedTree, s.order < t.order →
            M₁.elementaryWeight s = M₁'.elementaryWeight s)
        (i : Fin s₂),
        M₂.derivativeWeightWithSrc M₁ i t
          = M₂.derivativeWeightWithSrc M₁' i t
    | RootedTree.mk children, h_strict, i => by
        show M₂.derivativeWeightWithSrcProd M₁ i children
              = M₂.derivativeWeightWithSrcProd M₁' i children
        exact derivativeWeightWithSrcProd_eq_of_strict_subtree_agreement
          M₂ (RootedTree.mk children) h_strict children
          (fun c hc => RootedTree.order_lt_of_mem_children children c hc) i

  private theorem derivativeWeightWithSrcProd_eq_of_strict_subtree_agreement
      {s₁ s₁' s₂ : ℕ}
      {M₁ : RKTableau s₁} {M₁' : RKTableau s₁'}
      (M₂ : RKTableau s₂) (t : RootedTree)
      (h_strict : ∀ s : RootedTree, s.order < t.order →
          M₁.elementaryWeight s = M₁'.elementaryWeight s) :
      ∀ (children : List RootedTree)
        (_h_children_lt : ∀ c ∈ children, c.order < t.order)
        (i : Fin s₂),
        M₂.derivativeWeightWithSrcProd M₁ i children
          = M₂.derivativeWeightWithSrcProd M₁' i children
    | [], _, _ => rfl
    | c :: cs, h_children, i => by
        show (M₁.elementaryWeight c
                + ∑ j : Fin s₂,
                    M₂.A i j * M₂.derivativeWeightWithSrc M₁ j c)
              * M₂.derivativeWeightWithSrcProd M₁ i cs
            = (M₁'.elementaryWeight c
                + ∑ j : Fin s₂,
                    M₂.A i j * M₂.derivativeWeightWithSrc M₁' j c)
              * M₂.derivativeWeightWithSrcProd M₁' i cs
        have h_c_lt : c.order < t.order :=
          h_children c (List.mem_cons_self _ _)
        have h_cs_lt : ∀ c' ∈ cs, c'.order < t.order :=
          fun c' hc' => h_children c' (List.mem_cons_of_mem c hc')
        rw [derivativeWeightWithSrcProd_eq_of_strict_subtree_agreement
              M₂ t h_strict cs h_cs_lt i]
        congr 1
        rw [h_strict c h_c_lt]
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [derivativeWeightWithSrc_eq_of_strict_subtree_agreement
              M₂ c (fun s hs => h_strict s (hs.trans h_c_lt)) j]
end
```

Note the **two distinct uses of `h_strict`**:

1. **At `c` itself**: `rw [h_strict c h_c_lt]` swaps
   `M₁.elementaryWeight c` for `M₁'.elementaryWeight c`, using
   `h_c_lt : c.order < t.order`.
2. **At strict subtrees of `c`**: the recursive call needs
   agreement at `s` with `s.order < c.order`; this follows from
   `h_strict` via `s.order < c.order < t.order` (i.e. the
   `(fun s hs => h_strict s (hs.trans h_c_lt))` lambda).

This is the cycle 226 pattern (line 2769–2803) extended with the
strict-subtree restriction. Cycle 226 had simpler `hPhi₁ t` /
`hPhi₁ s` substitutions because `PhiEquivalent` agrees at EVERY
tree; cycle 362 carries an order-witness through the recursion.

### §C.3 — Key Mathlib / project hooks (verify early via §E)

* `RootedTree.order_lt_of_mem_children` — cycle 343 lemma,
  `OpenMath/Chapter3/Section301.lean` (search via §E.1).
* `List.mem_cons_self`, `List.mem_cons_of_mem` — standard `List` API.
* `Finset.sum_congr` — standard, used pervasively in §381.
* `Nat.lt_trans` / `.trans` on `<` for `Nat` — standard.
* Cycle 226 mutual block at `Section381.lean:2769–2803` — the
  template to mirror.

### §C.4 — Anticipated risks

* **R1 (medium): mutual-induction termination.** The block recurses
  on tree + list. Cycle 226 succeeded with the same shape, so Lean
  should infer termination automatically. If it fails, fallback is
  explicit `termination_by` + `decreasing_by` citing cycle 343's
  `WellFoundedRelation` instance (line ~177 of `Section301.lean`).

* **R2 (low): `show` reframing.** The `c :: cs` case needs an
  explicit `show` because `derivativeWeightWithSrcProd M₁ i (c :: cs)`
  doesn't definitionally reduce in the goal display. Mirror cycle
  226 line 2789–2796 verbatim.

* **R3 (low): hypothesis lambda elaboration.** The inner
  `(fun s hs => h_strict s (hs.trans h_c_lt))` may need a
  `Nat.lt_trans hs h_c_lt` if `.trans` doesn't elaborate on
  `Nat`-level `<`. Try `.trans` first; fall back to explicit
  `Nat.lt_trans` only if needed.

* **R4 (low): `List.mem_cons_self` / `List.mem_cons_of_mem` API
  drift.** Confirm both via §E.4 before writing the body. If
  renamed (likely to `List.mem_cons_self'` or similar), adjust.

### §C.5 — Non-vacuity `example` (P1 deliverable)

In `OpenMath/Chapter4/Section422.lean` after cycle 361 examples
(line ~2118):

```lean
/-- *Phase D.3.b Step 1 (cycle 362) — non-vacuity at `cherry`.*
Trivial-agreement case: `M₁ = M₁' = explicitEuler`, so the strict-
subtree hypothesis is discharged by `intro s _; rfl`. Confirms
the substitution lemma's signature compiles and the lemma fires
on a concrete tableau / tree pair. -/
example :
    OpenMath.Chapter3.Section312.RKTableau.derivativeWeightWithSrc
        OpenMath.Chapter3.Section312.RKTableau.explicitEuler
        OpenMath.Chapter3.Section312.RKTableau.explicitEuler
        0 RootedTree.cherry
      = OpenMath.Chapter3.Section312.RKTableau.derivativeWeightWithSrc
          OpenMath.Chapter3.Section312.RKTableau.explicitEuler
          OpenMath.Chapter3.Section312.RKTableau.explicitEuler
          0 RootedTree.cherry :=
  derivativeWeightWithSrc_eq_of_strict_subtree_agreement
    OpenMath.Chapter3.Section312.RKTableau.explicitEuler
    RootedTree.cherry (fun _ _ => rfl) 0
```

A more substantive non-vacuity witness (genuinely distinct M₁, M₁'
agreeing only at strict subtrees of cherry) is left to cycle 363+.

## §D — What NOT to attempt

### §D.1 — Things ruled out by cycle 361's analysis

* **Do NOT attempt P2 without P1 in hand.** P2 needs Step 1
  (per-`derivativeWeightWithSrc` substitution) as a load-bearing
  ingredient. Skipping straight to P2 has no path.

* **Do NOT attempt P2 by direct strong induction on `t.order`
  without Step 1.** Cycle 361's task results §"Dead ends" flagged
  this as foreseeable multi-cycle decomposition — the recursive
  structure of `derivativeWeightWithSrc M₂ M₁ i (mk children)`
  exposes `M₂`'s internal A-coefficients alongside
  `M₁.elementaryWeight` at subtrees, requiring delicate inductive
  infrastructure that simultaneously constrains both `Φ_η_q` and
  per-stage internal weights at strict subtrees.

* **Do NOT replace cycle 226's
  `derivativeWeightWithSrc_subst_M₁`** with the strict-subtree
  version. Cycle 226 is consumed by cycles 226–235's §384 path
  (left/right Φ-equivalent substitution lemmas, group homomorphism
  work) that genuinely needs FULL `PhiEquivalent`. Cycle 362's
  lemma is a strict generalisation taking a strict-subtree
  hypothesis — introduce as a **sibling**, not a replacement.

### §D.2 — Pattern-violation traps

* **Do NOT use `norm_num`** to bridge
  `-(((m+1) : ℕ) : ℤ) = Int.negSucc m`. This is definitional `rfl`
  (cycle 361 Discovery #1; memory entry
  `feedback_neg_natCast_int_negsucc_rfl`); `norm_num` leaves a
  display-ambiguous unsolved goal. (Not relevant to cycle 362 P1
  itself, but worth keeping in mind if P2 is attempted — it touches
  ℤ-form lifts.)

* **Do NOT introduce `sorry`/`axiom`/`constant`.** Cycle 200/201's
  rollback of `thm:381H`'s sorry-first scaffold and cycle 149/150's
  rollback of `def:530B`'s Path A sorry-first apply: either P1
  lands axiom-clean or we pivot to §D.3's P3 fallback. The §422
  streak is 27 consecutive axiom-clean cycles — do not break it
  with a sorry-bearing partial.

* **Do NOT modify `Section441.lean`.** GPFS-blocked (43+ consecutive
  timeouts per `cycle_182_gpfs_slowness.md` cycle 239). Keep all
  work in `Section381.lean` (mutual block) and `Section422.lean`
  (non-vacuity example only).

* **Do NOT use `induction t` on `RootedTree`.** Per memory
  `feedback_rootedtree_nested_induction`, `induction t` and
  `RootedTree.recOn` fail on nested inductives. The cycle 226
  / cycle 362 pattern uses `mutual` block with constructor pattern
  matching (`| RootedTree.mk children, _, _ => ...`), which is the
  correct approach for this datatype.

### §D.3 — Phase D.3.c is near-free (P3 fallback details)

Per cycle 361 worker's "Alternative cycle 362 deliverable" + manual
infrastructure check:

* Cycle 176 ships
  `LinearMultistepMethod.ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent`
  (`Section441.lean:599`): under `M.IsStable ∧ M.IsPreconsistent`,
  `M.ρPoly.derivative.eval 1 ≠ 0`.
* Cycle 344 ships `coef_α_eq_ρPoly_deriv_at_one_of_preconsistent`
  (`Section422.lean:704`): under `M.IsPreconsistent`,
  `(∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ) = M.ρPoly.derivative.eval 1`.

Phase D.3.c's target is therefore a one-line composition:

```lean
theorem sum_i_alpha_ne_zero_of_stable_preconsistent
    {k : ℕ} (M : LinearMultistepMethod k) (hk : 0 < k)
    (hStable : M.IsStable) (hPre : M.IsPreconsistent) :
    (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ) ≠ 0 := by
  rw [coef_α_eq_ρPoly_deriv_at_one_of_preconsistent M hPre]
  exact M.ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent hStable hPre
```

Plus 1 BDF2 witness via cycle 344's `bdf2LMM` + cycle 354's
`bdf2LMM_isStable` (~10 LOC total). Use as P3 fallback ONLY if P1
stalls past ~75 min — otherwise hold for cycle 363's deliberate
ship to preserve the planned cycle ordering.

Note: the scoping doc strawman uses
`∑ i : Fin (k+1), (i.val : ℝ) * M.α i` (sum over `Fin (k+1)` starting
at `i=0`). That equals the `coef_α` form (sum over `Fin k` with
`M.α i.succ`) via the `i=0` term being `0·M.α 0 = 0`. Prefer the
cycle 344 idiom for downstream consistency.

## §E — Mathlib hook verification (≤10 min budget)

Run before writing any P1 body:

1. `lean_local_search "order_lt_of_mem_children"` — confirm cycle
   343's lemma exists at `Section301.lean:~177`. Expected signature
   `(children : List RootedTree) (c : RootedTree) (hc : c ∈ children) : c.order < (RootedTree.mk children).order`.
2. `lean_hover_info` on `derivativeWeightWithSrc` at
   `Section381.lean:2680` — confirm the signature
   `(M₂ : RKTableau s₂) (M₁ : RKTableau s₁) : Fin s₂ → RootedTree → ℝ`
   hasn't drifted.
3. `lean_hover_info` on cycle 226's
   `derivativeWeightWithSrc_subst_M₁` at `Section381.lean:2769` —
   confirm the mutual-block shape we're mirroring.
4. `lean_local_search "List.mem_cons"` — confirm
   `List.mem_cons_self` and `List.mem_cons_of_mem` exist as named
   lemmas. (Mathlib has done some renames here recently; fallback
   names are `List.mem_cons` discharged by `Or.inl rfl` / `Or.inr ·`.)

If any hook has drifted (genuinely missing, not phantom), file a
sub-issue under `.prover-state/issues/` and pivot to P3.

## §F — Faithfulness check pre-flight (mandatory before commit)

For P1's substitution lemma:

* **Tautology check**: conclusion is
  `derivativeWeightWithSrc M₂ M₁ i t = derivativeWeightWithSrc M₂ M₁' i t`;
  hypothesis is strict-subtree elementary-weight agreement. The
  conclusion does NOT appear as hypothesis. ✓
* **Identity check**: proof uses cycle 343's subtree-order descent,
  cycle 226's mutual-block template (with weakened hypothesis), and
  standard `List`/`Finset` API. All substantive. Not identity.
* **Hypothesis strength check**: strict-subtree agreement is the
  *weakest* hypothesis that suffices — `derivativeWeightWithSrc`
  only references `M₁.elementaryWeight` at strict subtrees. Matches
  Butcher's "orders greater than r(t) − 1" verbatim
  (`extraction/raw_text/ch04.txt:1158`). No textbook deviation.
* **Definition smuggling check**: the substitution lemma is a
  *property* of `derivativeWeightWithSrc`, not a re-definition. The
  cycle 226 hook for the FULL-`PhiEquivalent` version remains
  intact (used by §384 work).
* **Absent theorem check**: docstring claims "cycle 226 template
  weakened"; verify the comparison is accurate before commit.

## §G — Time budget

| Phase                                  | Budget       |
|----------------------------------------|--------------|
| §A pre-flight verification             | ≤ 5 min      |
| §E Mathlib hook verification           | ≤ 10 min     |
| P1 proof (mutual block + non-vacuity)  | 60–75 min    |
| P2 attempt (stretch, only if P1 fast)  | 60–90 min    |
| Faithfulness check + `#print axioms`   | ≤ 10 min     |
| `lake build` + sorry-count regression  | ≤ 10 min     |
| Task results + scoping-doc update      | 20 min       |
| **Cycle total (P1 only)**              | **~2.5 hr** |
| **Cycle total (P1 + P2)**              | **~4 hr**   |

If §E reveals a missing hook (unlikely), file sub-issue + pivot to
P3. If P1 mutual block elaboration stalls past 75 min, ship P3
fallback only.

## §H — Post-cycle housekeeping (after ship)

1. **Append cycle 362 update** to
   `.prover-state/issues/def_422B_phase_D_3_scoping.md` §5 (cycle-362
   row table cell ✅) and §"Cycle 363 entry point" subsection
   describing the Step 2 attempt outlook.
2. **Update** `extraction/formalization_data/lean_status.json`'s
   `def:422B` row `cycle` field to 362 (formalization status remains
   `partial`).
3. **Append cycle 362 line** to `plan.md`'s `def:422B` partial-row
   entry, mirroring cycles 357–361's format.
4. **Write** `.prover-state/task_results/cycle_362.md` per CLAUDE.md
   template, including §"Faithfulness check" for the new substitution
   lemma.
5. **No new memory entry needed** for P1 alone — cycle 226 mutual
   template + cycle 343 descent are already canonical. If P2 reveals
   a novel pattern (e.g. a `Quotient.inductionOn₂` + Step 1 chain
   that closes cleanly), save as memory.

## §I — Strategic context

§422 streak now stands at **27 consecutive axiom-clean cycles
(336–361)**. Phase D.3.b is in its third cycle (D.3.b sig + base
cases @ cycle 360; ℤ-form lift + general closed form @ cycle 361;
parametricity Step 1 @ cycle 362). Phase D.3.c (near-free per §D.3)
and Phase D.3.d (`underlyingOneStepMethod_aux` recursion + spec)
remain ahead; Phase E sealing of `def:422B` projected for cycle 365.

**Do not pivot to a fresh entity** despite the long streak. The
Phase D.3 ladder's rhythm is productive (axiom-clean ships every
cycle since 336), and the textbook landmark `def:422B` is now
**~3–4 cycles away** — a discrete payoff in sight that justifies
continued investment. The cycle 361 worker's "no pivot temptation
— the ladder rhythm remains productive" applies verbatim to cycle
362.
