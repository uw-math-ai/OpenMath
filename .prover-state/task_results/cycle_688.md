# Cycle 688 Results

## Worked on
§521 Step C.11 — fully-named consolidated form of
`toGLM_stabilityMatrix_charpoly_explicit`, plus the optional stretch
deliverable `rowFNamedSum_degree_lt` (degree bound for the α + PY·β
named row decomposition). Also: retroactive cycle 687 commit covering
the 136 lines of Step C.10 work that cycle 687 left uncommitted.

## Approach

### Step C.11 — `toGLM_stabilityMatrix_charpoly_named`
The strategy's suggested closing recipe worked verbatim, in 4 rewrites
with no `ring` / `simp` / `ring_nf` cleanup:

```lean
rw [toGLM_stabilityMatrix_charpoly_explicit m hz hs,
    toGLM_stabilityMatrixPHF_zero_charpoly,
    ← rowYQuot_mul_X_pow_eq_RowY m hs,
    toGLM_stabilityCharpolyRowF_eq_alphaPoly_plus_PY_betaPoly m hs]
```

All four rewrites fire cleanly because the named substitution targets
appear at the polynomial level on both sides — no associativity or
commutativity reshuffling is needed. The `Polynomial.C` coefficient
opacity worry the planner flagged did not materialise.

### Stretch — `rowFNamedSum_degree_lt`
Followed the planner sketch:

1. `Polynomial.degree_add_le` reduces to `max` of two degrees.
2. `max_lt` splits the goal into two strict inequalities.
3. **α-term**: `rowFAlphaPoly_degree_lt` gives `< (2*s - 1 : ℕ)`;
   bridged to `< (2*s : ℕ)` via `(2*s - 1 : ℕ) ≤ 2*s` (via `omega`).
4. **PY·β term**: `Polynomial.degree_mul_le` plus
   `Matrix.charpoly_natDegree_eq_dim` (giving natDegree = s, hence
   degree = s after `Polynomial.degree_eq_natDegree` with monic
   `Matrix.charpoly_monic`), plus `rowFBetaPoly_degree_lt` (`< s`).
   Cast `2*s` to `s + s` and finish with `WithBot.add_lt_add_left`.

The `s = 0` case is handled uniformly because
`rowFBetaPoly_degree_lt` returns `degree < (0 : WithBot ℕ)`, forcing
`degree = ⊥`, after which `WithBot.add_lt_add_left` still applies on
the additive side.

## Result
SUCCESS for both Step C.11 (mandatory) and the stretch
`rowFNamedSum_degree_lt`.
- `OpenMath/LMMAsGLM/StabilityCharpoly.lean` compiles clean
  (no errors, no warnings).
- `OpenMath/LMMAsGLM.lean` umbrella compiles clean.
- `grep -c sorry OpenMath/LMMAsGLM/StabilityCharpoly.lean` returns 0.

## Dead ends
None. The planner's recipes worked on the first attempt for both
deliverables.

## Discovery
- The named substitution chain for the consolidated charpoly is
  textbook-clean: each named identity (`PHF(0).charpoly = X^s`,
  `RowY = rowYQuot · X^s`, `RowF = α + PY·β`) is shaped exactly so
  that `rw` substitutes without leftover residual algebraic shuffling.
  This validates the cycle 678/680/682/684 named-poly architecture —
  the substitution targets are all "first-class" rewrite handles.
- `Matrix.charpoly_monic` + `Polynomial.degree_eq_natDegree` is the
  standard recipe for upgrading natDegree-equality bounds to
  degree-equality bounds when the polynomial is a charpoly.
- `WithBot.add_lt_add_left` has the signature
  `(hx : x ≠ ⊥) : y < z → x + y < x + z` — the non-`⊥` hypothesis is
  on the *unchanging* left summand, not on either of the comparators.

## Suggested next approach
Step C.12 — the polynomial-evaluation bridge from the named consolidated
charpoly (Step C.11) to `LMM.stabilityPoly` evaluated at the GLM
stability matrix eigenvalue. Concretely, once `D` (the resolvent
denominator) is multiplied into Step C.11, the `X^s` factor on the
"non-rank-one" half pulls out cleanly and the two halves combine into
`X^s · activeStabilityPolyPoly m z` modulo a degree-`< 2s` residual
governed by `rowFNamedSum_degree_lt` (proved this cycle). That is the
missing piece (b) the planner flagged for the eventual A-stability iff
bridge.

A reasonable next-cycle target is:

```
theorem D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    Polynomial.C (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        (m.toGLM.stabilityMatrix z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s * activeStabilityPolyPoly m z
        - (rowYQuot m * X^s · C (z β_last) + (α + PY·β) · C z)
```

Specifically, the BDF specialisation `D_mul_toGLM_charpoly_eq_X_pow_mul_active_of_bdf`
already has the right shape — the general version drops out by
multiplying Step C.11 by `Polynomial.C (1 - z β_last)` and unfolding
`activeStabilityPolyPoly`.
