# Cycle 778 Results

## Worked on
§530 LMM-as-GLM order-≥ 2 witness layer. Per the cycle 778
strategy's witness-first directive, landed both the **must-land**
trapezoid witness and the **stretch** BDF2 witness in one cycle:

- `trapezoidalRule_toGLM_hasOrderGe2 : trapezoidalRule.toGLM.HasOrderGe2`
- `bdf2_toGLM_hasOrderGe2 : bdf2.toGLM.HasOrderGe2`

Both appended to `OpenMath/LMMAsGLM.lean` immediately after the
cycle-776 order-≥ 1 witness block (lines 1652–1722).

## Approach
Identical four-step recipe per witness, mirroring the strategy's
"Step-by-step recipe":

1. Refine the `HasOrderGe2` existential with the explicit
   `(q, q', q'')` triple (`Fin.addCases` on `Fin.cast (Nat.two_mul s)`).
2. Subgoal 1 (`V q = q`): the witness `q` is **definitionally**
   `LMM.nordsieckQ s` (line 1380), so the cycle-614 lemma
   `toGLM_V_nordsieckQ_eq` closes it via `exact`. No reindexing needed.
3. Subgoals 2, 3, 4 (`U q = 𝟙`, `B 𝟙 + V q' = q + q'`,
   `2 (B c) + V q'' = q + 2 q' + q''`): close by
   `intro k; fin_cases k; simp [LMM.toGLM, <method>, Fin.addCases,
   Fin.sum_univ_two | Fin.sum_univ_succ]; norm_num`.

The trapezoid witness lands with `Fin.sum_univ_two` (since
`Fin (2 * 1) = Fin 2`); BDF2 needs `Fin.sum_univ_succ` (since
`Fin (2 * 2) = Fin 4`).

### Witness data

For trapezoid (`s = 1`, `r = 2`):
- `q = (1, 0)` — past-`y` indicator.
- `q' = (0, 1)` — Nordsieck `h y'_n` content.
- `q'' = (0, 0)` — the strategy's predicted zero vector.

For BDF2 (`s = 2`, `r = 4`):
- `q = (1, 1, 0, 0)` — past-`y` indicator on first two slots.
- `q' = (0, 1, 1, 1)` — Nordsieck `h y'_n` content
  (`(j : ℝ)` on past-`y`, `1` on past-`h·f`, matching cycle 614).
- `q'' = (0, 1, 0, 2)` = `((j : ℝ)²` on past-`y`, `2 (j : ℝ)`
  on past-`h·f`).

The BDF2 `q''` was derived by hand-solving the four `HasOrderGe2`
identities at `s = 2`:

* `k = 0` (past-`y` j=0, shift): `0 + q'' 1 = 1 + 0 + q'' 0` ⇒ `b = 1 + a`.
* `k = 1` (past-`y` j=1, last): `2 (2/3 · 2) + (-1/3) a + (4/3) b = 1 + 2 + b`
  ⇒ `b = 1 + a` (consistent).
* `k = 2` (past-`h·f` j=0, shift): `0 + d = 0 + 2 + c` ⇒ `d = 2 + c`.
* `k = 3` (past-`h·f` j=1, last): `2 (1 · 2) + 0 = 0 + 2 + d` ⇒ `d = 2`.

Free `a`; choosing `a = 0` ⇒ `(a, b, c, d) = (0, 1, 0, 2)` matches
the Taylor-moment table `q'' j = j² (past-y), q'' j = 2 j (past-h·f)`.

### What about the strategy's "do not propose `j² / 2j`" warning?

The strategy correctly cautioned against blindly *symbolic*
generalization of `q'` to `q''`. The numerical verification above
(constraint-solving the four `HasOrderGe2` identities at BDF2's
specific coefficients) **confirms** the Taylor-moment table at
this rung; this is a checked match, not a guess. The trapezoid
case `q'' ≡ 0` matches because at `s = 1`, `j ∈ Fin 1` so `j² = 0`
and `2 j = 0` everywhere — the Taylor table degenerates to zero.

## Result
SUCCESS for both witnesses.

- `lake env lean OpenMath/LMMAsGLM.lean` — clean compile, sorry-free.
- `lake build OpenMath.LMMAsGLM` — green (only pre-existing
  `BDF.lean:148` `simp` lint warnings, unrelated to this cycle).

## Dead ends
None. The witness-first plan was crisp, and the existing simp
projection lemmas (`toGLM_A_apply`, `toGLM_U_castAdd`,
`toGLM_U_natAdd`, `toGLM_V_*`, `toGLM_B_*`) are strong enough
that `simp [LMM.toGLM, <method>, Fin.addCases, Fin.sum_univ_*]`
+ `norm_num` collapses every obligation. No `show` rewrites or
manual `Fin.cast` manipulation needed.

## Discovery
1. **Reusing `nordsieckQ` for the `V q = q` obligation is a
   one-liner.** Because the chosen `q` is definitionally
   `LMM.nordsieckQ s`, `exact m.toGLM_V_nordsieckQ_eq hcons`
   closes obligation 1 for *any* consistent `m` — no `s`-specific
   reindexing required. This is the same trick the cycle-614
   stability defect work used and it ports cleanly to order-≥ 2.

2. **The Taylor-moment `q''` (`j²` / `2 j`) extends to BDF2.**
   The strategy's caution was correct in principle (don't
   generalize without checking), but the constraint-solving
   matches the moment table at trapezoid (`= 0`) and at BDF2
   (`= (0, 1, 0, 2)`). This is encouraging evidence that the
   general bridge `LMM.toGLM_hasOrderGe2 (m : LMM s) (h2 :
   m.HasOrder 2) (hcon : m.IsConsistent)` should use this `q''`
   form as the witness — the next cycle's job.

3. **`Fin.sum_univ_succ` works for `Fin (2 * 2) = Fin 4`** without
   needing to manually unfold to `Fin (4 + 0)` or similar. It
   peels one term at a time, and combined with `Fin.addCases`
   reduction, `simp` finishes the `Finset` enumeration.

## Suggested next approach
**Cycle 780 — general `LMM.toGLM_hasOrderGe2` bridge.** With
both `s = 1` and `s = 2` witnesses landed under the unified
witness shape

```
q  k = Fin.addCases (fun _ : Fin s => 1) (fun _ : Fin s => 0) (Fin.cast _ k)
q' k = Fin.addCases (fun j : Fin s => (j : ℝ)) (fun _ : Fin s => 1) (Fin.cast _ k)
q''k = Fin.addCases (fun j : Fin s => (j : ℝ)^2) (fun j : Fin s => 2 (j : ℝ)) (Fin.cast _ k)
```

state and prove

```
LMM.toGLM_hasOrderGe2 (m : LMM s) (h2 : m.HasOrder 2)
    (hcon : m.IsConsistent) : m.toGLM.HasOrderGe2
```

The first three obligations port from `toGLM_isConsistent`'s
existing 800-line `Fin.addCases` reindexing plus a parallel block
for the new `q''`. The fourth obligation is the new work; it
parallels the cycle-614 third obligation's structure (last-row
case via `m.sigma_two`-style identities, shift-row case by direct
sum collapse).

If the general bridge is still too big a swing for one cycle,
break it into:

* **Cycle 780**: state the predicate and prove the first three
  obligations from the consistency witness (mostly copy-paste
  from `toGLM_isConsistent` with one extra `q''`-aware reindex).
* **Cycle 782**: prove obligation four, the new second-derivative
  identity, using `m.HasOrder 2 → m.sigma_two = ...` + the
  `last-y` and `last-f` row analyses already used in cycle 614.

After the general bridge lands, derive `forwardEuler` /
`backwardEuler` order-≥ 2 statements as **non-theorems**: forward
and backward Euler are order 1 only, so `m.HasOrder 2` is false
for them, and the bridge is silent (no witness obtainable). Per
the strategy's "What NOT to try" item 4, that's the correct
behavior.

The §530 ladder above order ≥ 2 (order ≥ 3, ≥ 4, …) on the LMM
side is the natural follow-up after the order-≥ 2 bridge lands.
The RK side already has order ≥ 6 (cycle 774); the §530 final
form is the joint LMM/RK ladder.

## Files touched
- `OpenMath/LMMAsGLM.lean` — appended 2 witness theorems
  (~50 lines, well under the file size cap).

## Commit
`Cycle 778: §530 LMM-as-GLM order ≥ 2 witnesses (trapezoid + BDF2)`
