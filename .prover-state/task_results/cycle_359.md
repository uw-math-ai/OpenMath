# Cycle 359 Results

## Worked on

`def:422B` Phase D.3.a.3 — recursive `pow_succ`-style elementary-weight
identity at arbitrary trees. Three named symbols shipped:

1. `OpenMath.Chapter3.Section312.RKTableau.powRep` (recursive
   self-composition Σ-typed value, infrastructure).
2. `OpenMath.Chapter3.Section312.RKTableau.powRep_quotient_eq`
   (quotient-equality certifier).
3. `OpenMath.Chapter4.Section422.elementaryWeightQ_phi_pow_succ_mk`
   (the Phase D.3.a.3 ℕ-form identity).

Plus three non-vacuity `example`s on `RKTableau.explicitEuler`.

## Approach

Followed the cycle 359 strategy verbatim through Steps 1–3 + 5, with
two simplifications discovered during implementation (see Discovery).

**Step 1** — `RKTableau.powRep`: inserted in `Section381.lean`
immediately after `instGroup_phi` (line 4329), inside the
`OpenMath.Chapter3.Section312.RKTableau` namespace. Used the strategy's
direct pattern-match form (no intermediate `let`):

```lean
noncomputable def powRep {s : ℕ} (M : RKTableau s) :
    ℕ → Σ s' : ℕ, RKTableau s'
  | 0 => ⟨0, RKTableau.id⟩
  | m + 1 => ⟨(M.powRep m).1 + s, (M.powRep m).2.compose M⟩
```

The strategy's `RKTableau.powRep` name was dropped to `powRep` because
the surrounding namespace already prepends `RKTableau`.

**Step 2** — `powRep_quotient_eq`: same insertion location. Induction
on `m`:

```lean
theorem powRep_quotient_eq {s : ℕ} (M : RKTableau s) (m : ℕ) :
    Quotient.mk PhiEquivalent.setoidSigma (M.powRep m)
      = (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) ^ m := by
  induction m with
  | zero =>
    show Quotient.mk PhiEquivalent.setoidSigma (⟨0, RKTableau.id⟩ :
            Σ s' : ℕ, RKTableau s')
      = (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) ^ 0
    rw [pow_zero]
    rfl
  | succ k ih =>
    show Quotient.mk PhiEquivalent.setoidSigma
          (⟨(M.powRep k).1 + s, (M.powRep k).2.compose M⟩ :
            Σ s' : ℕ, RKTableau s')
      = (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) ^ (k + 1)
    rw [pow_succ, ← ih]
    rfl
```

The strategy's R1 fallback (explicit `show composeQ_phi ...`) was not
needed — `composeQ_phi_mk`-level definitional reduction via cycle
236's `instMul_phi` typeclass already exposes the right shape and
closes the goal by `rfl`. Added explicit Σ type ascriptions to
disambiguate `Σ` from `PSigma` (the elaborator was indecisive without
the ascription).

**Step 3** — `elementaryWeightQ_phi_pow_succ_mk`: inserted in
`Section422.lean` immediately after cycle 358's `_inv_mk` non-vacuity
example (line 618), before the Phase D.1 base-case content. After
discovering Risk R2 fires differently than the strategy predicted
(see Discovery #1 below), the final proof is 3 lines:

```lean
theorem elementaryWeightQ_phi_pow_succ_mk {s : ℕ} (M : RKTableau s)
    (m : ℕ) (t : RT) :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) ^ (m + 1)) t
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) ^ m) t
        + ∑ i : Fin s, M.b i *
            M.derivativeWeightWithSrc (M.powRep m).2 i t := by
  rw [pow_succ]
  rw [← RKTableau.powRep_quotient_eq M m]
  exact elementaryWeightQ_phi_mul_mk (M.powRep m).2 M t
```

**Step 5** — Three non-vacuity `example`s on `RKTableau.explicitEuler`
appended after `pow_succ_mk`: `powRep 0 = ⟨0, RKTableau.id⟩` (by
`rfl`), `(powRep 1).1 = 1` (by `rfl`), and the end-to-end ℕ-form at
`cherry` with `m = 0`.

**Step 4 (DEFER)** — ℤ-form not shipped, per strategy §C.4. The right
signature should be pinned by Phase D.3.b's consumption needs (cycle
360 deliverable).

## Result

**SUCCESS** — all three target symbols shipped axiom-clean
(`[propext, Classical.choice, Quot.sound]` only), verified via
`#print axioms` after `lake build` refreshed the .oleans:

```
'OpenMath.Chapter3.Section312.RKTableau.powRep' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter3.Section312.RKTableau.powRep_quotient_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter4.Section422.elementaryWeightQ_phi_pow_succ_mk' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Both `lake build OpenMath.Chapter3` and `lake build OpenMath.Chapter4`
exit 0. Sorry count remains 0 in both `Section381.lean` and
`Section422.lean`. The ship lands all of the strategy's Steps 1–3 + 5
without invoking any of the §C fallbacks.

## Faithfulness check

This cycle ships three new symbols, all under `def:422B` Phase D.3.a.3
infrastructure. None corresponds to a named Butcher theorem — these
are project-internal helpers required to bridge cycle 341 P3
(`elementaryWeightQ_phi_zpow_vertex`) to arbitrary trees per the
cycle 358 worker's Discovery analysis (no canonical `η_q ^ m`
representative without a recursive construction). Faithfulness is
established by:

- **`RKTableau.powRep`**: project-internal Σ-typed recursive
  composition. Matches the cycle 358 Discovery's "canonical
  representative needed for the bottom-block" specification verbatim.
  No textbook claim.

- **`RKTableau.powRep_quotient_eq`**: project-internal certifier that
  the chosen representative realises the §383 quotient power. No
  textbook claim.

- **`elementaryWeightQ_phi_pow_succ_mk`**: at arbitrary `t`, the
  recursive shape `Φ_{⟦M⟧^(m+1)}(t) = Φ_{⟦M⟧^m}(t) + Σᵢ M.b i ·
  M.derivativeWeightWithSrc (M.powRep m).2 i t`. At `t = vertex` the
  bottom-block collapses (each `derivativeWeightWithSrc` factor is
  `1` by cycle 341's `derivativeWeightWithSrc_vertex`) and the
  formula reduces to the additive `Φ_{⟦M⟧^(m+1)}(τ) = Φ_{⟦M⟧^m}(τ) +
  Φ_M(τ)` form, recoverable from cycle 341 P3's closed form `(m+1) ·
  Φ_M(τ) = m · Φ_M(τ) + Φ_M(τ)`. The Phase D.3.a.3 statement is
  strictly more general than the vertex closed form (it accepts
  arbitrary `t`), and is the exact recursive identity needed for the
  Phase D.3.b linear-coefficient extraction (per the scoping doc
  §4.b: "η⁻ⁱ(t) viewed as a polynomial in η(t) has linear coefficient
  i·(−1)^r(t)" requires unpacking η^i's recursive shape, which is
  what `pow_succ_mk` provides).

No tautology, identity, or definition smuggling. No structure with
Prop fields. No hypothesis strengthening (the theorem is unconditional
in `m, t, s, M`).

## Dead ends

**None this cycle.** The strategy's recipe worked first-attempt for
Steps 1 and 5. Steps 2 and 3 each had one wrinkle (see Discovery)
that simplified rather than complicated the final proof.

The strategy's §G "Plan B" (split `powRep_quotient_eq` into a private
helper + main lemma) and "Plan C" (Aristotle for
`powRep_quotient_eq`) graceful-degradation paths were not needed.

## Discovery

**1. `rw [← powRep_quotient_eq M m]` fires globally, not just on one
side.** The strategy's Step 3 proof recipe (Steps A through D) used
`rw [← ...]` to rewrite the LHS factor, then `conv_rhs => rw [← ...]`
to rewrite the RHS first summand separately. In practice, the first
`rw` fires on both occurrences simultaneously (it's a global rewrite,
not conv-localised), and the second `conv_rhs => rw [← ...]` then
fails with "Did not find an occurrence of the pattern" because the
pattern is already gone. **Lesson**: a global `rw [← q_eq]` for a
multi-occurrence pattern is a single-step alternative to two
`conv`-localised rewrites. The proof simplifies from ~6 lines to 3
lines. This is a generalisable observation worth flagging for the
cycle 360 worker.

**2. `Σ` vs `PSigma` ambiguity in `show` ascriptions.** The
strategy's `show` form for `powRep_quotient_eq` (e.g. `show Quotient.mk
PhiEquivalent.setoidSigma ⟨0, RKTableau.id⟩ = _`) doesn't elaborate
without an explicit type ascription, because Lean's elaborator picks
the wrong sigma type (defaults to `PSigma` in the abstract context).
Adding `(⟨0, RKTableau.id⟩ : Σ s' : ℕ, RKTableau s')` disambiguates.
The succ case has the same issue and the same fix. Both are noted in
the scoping doc's cycle 359 update for the cycle 360 worker.

**3. Strategy's R1 (`rfl` failure through `instMul_phi`) and R2
(global-`rw` pattern-not-found) risks did not fire as predicted.**
R1 did not fire — `composeQ_phi`'s definitional unfold through
`instMul_phi` reduces cleanly to the expected form, so `rfl` closes
the succ-case immediately without the fallback `show composeQ_phi
...` reframing. R2 fired in a different shape than predicted — the
pattern *is* found by the first `rw`, but the strategy's second
`conv_rhs` rewrite then fails because the global first rewrite
already removed all occurrences. The mitigation is to remove the
second rewrite, not (as the strategy proposes) to use `conv_lhs` to
localise the first one.

**4. `noncomputable def` propagation is benign.** The strategy's R3
risk ("`noncomputable` propagation through `powRep`'s recursive
definition may trigger unexpected `Decidable` lookup failures") did
not fire. The `noncomputable def powRep` compiles without surfacing
any `Decidable` lookup obligations downstream, including in the
non-vacuity `rfl`-`example`s on `explicitEuler`.

**5. Linter noise**: cycle 358 left several
`unused simp arg` linter warnings in `Section381.lean` unrelated to
this cycle's content. They don't block compile but should be cleaned
up at some point. Not in scope for this cycle.

## Suggested next approach

**Cycle 360 should ship Phase D.3.b** (linear coefficient
extraction: `coeff_eta_t_in_eta_zpow_neg`, the textbook claim
"coefficient of η(t) in η⁻ⁱ(t) is i(−1)^r(t)") per scoping doc §5
phase table, ~100 LOC.

**Concrete first task for the cycle 360 worker**:

1. Read this cycle's discovery #1 (global-`rw` behavior of
   `powRep_quotient_eq`) — the same pattern probably applies to
   D.3.b's η^(-i) recursion, which will compose D.3.a.2
   (`elementaryWeightQ_phi_inv_mk`) with D.3.a.3
   (`elementaryWeightQ_phi_pow_succ_mk`).

2. Verify the ℤ-form signature *after* drafting D.3.b's statement:
   the cycle 360 worker should write D.3.b first, see what
   ℤ-form-of-D.3.a.3 it needs (positive-`i` via `_pow_succ_mk`,
   negative-`i` via D.3.a.2-then-`_pow_succ_mk` composition?), then
   ship `elementaryWeightQ_phi_zpow_mk` with exactly that signature.

3. The textbook claim "coefficient of η(t) in η⁻ⁱ(t) is i(−1)^r(t)"
   is a structural claim about how the §381 convolution-product
   expansion of `(η⁻¹ · η⁻¹ · ... · η⁻¹)` (i copies) on tree `t`
   decomposes when η(t) is viewed as the variable. The Phase D.3.b
   load-bearing observation (from scoping doc §1 textbook excerpt):
   "all terms on the right-hand side contain only terms with orders
   less than r(t)". This is the strong-induction hook into the
   cycle 343 `WellFoundedRelation RootedTree := measure
   RootedTree.order` infrastructure.

**Pivot temptation note**: the §422 streak is now 25 consecutive
axiom-clean cycles (336–359), with Phase E sealing of `def:422B`
projected ~4 cycles away (D.3.b → D.3.c → D.3.d → Phase E). The
compound investment payoff is high; stay on `def:422B` through
cycle 363 unless a hard blocker surfaces.
