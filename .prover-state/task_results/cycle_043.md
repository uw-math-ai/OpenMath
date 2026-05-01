# Cycle 043 Results

## Worked on

Closed the final `sorry` of `lem:406B` — the main theorem
`LinearMultistepMethod.localTruncationError_bound` at
`OpenMath/Chapter4/Section404.lean:991–1007`. With this, the entire
`OpenMath/` tree is `sorry`-free and `lem:406B` graduates from
`partial` / `in_progress` → `formalized`.

Two new namespaced helper lemmas introduced (above the main theorem):

- `localTruncationError_α_sum_bound` (lines ≈883–921)
- `localTruncationError_β_sum_bound` (lines ≈930–966)

## Approach

Followed the planner's decomposition recipe verbatim:

1. **Aristotle poll (single).** Project
   `53d674e4-20e3-43e8-9600-0b189c62c8f5` returned **COMPLETE** at
   100% (status check at `2026-04-30T22:08:13` → `2026-05-01T00:56:47`).
   Downloaded + extracted the result. Aristotle did succeed in proving
   all five sub-lemmas in its private `sub_lemmas.lean` worksheet
   (`ARISTOTLE_SUMMARY.md` reports zero sorries), but per the cycle
   strategy, **none of those proofs were imported** — sub-lemmas A–E
   already have axiom-clean manual proofs in the file (closed cycles
   040–042). Aristotle's worksheet sits at
   `/tmp/aristotle_53d674e4_extracted/sub_lemmas_aristotle/sub_lemmas.lean`
   for archival reference. Notable: Aristotle had to add a
   `(hf_cont : Continuous f)` hypothesis to its sub-lemma B; our
   manual proof avoids that by deriving continuity of `f∘y` from
   `ContDiff ℝ 1 y` + the ODE (a cleaner approach).

2. **α-sum helper.** Goal:
   `|∑ α_{i+1} · residual_i| ≤ (∑ (i+1)² |α_{i+1}|) · ((1/2) h² L M)`.
   Triangle inequality (`Finset.abs_sum_le_sum_abs`), distribute the
   coefficient over the sum (`Finset.sum_mul`), then summand-wise
   monotonicity (`Finset.sum_le_sum`) using `residual_bound` (sub-lemma
   C) at index `i.val + 1`. The cast `((i.val + 1 : ℕ) : ℝ)` produced
   by sub-lemma E's decomposition matched `residual_bound`'s
   `((i.val + 1 : ℕ) : ℝ)` exactly — no `push_cast` bridge needed.
   Final step: `ring`.

3. **β-sum helper.** Identical shape using `deriv_diff_bound`
   (sub-lemma D) instead of `residual_bound`. Final
   coefficient `(h * L * M)` instead of `((1/2) h² L M)`.

4. **Main combiner.** Rewrite by sub-lemma E, then
   `abs_add_le _ _` (NB the planner sketched `abs_add` — that name
   does not exist in current Mathlib; the correct name is
   `abs_add_le`). Pull the leading `h` out of the β-term using
   `abs_mul` + `abs_of_nonneg hh`. Apply `add_le_add hα _` with the
   β-side scaled by `h ≥ 0`. Final algebra closed by
   `apply le_of_eq; ring` — no `maxHeartbeats` issue.

## Result

**SUCCESS.** `lake env lean OpenMath/Chapter4/Section404.lean` returns
only the two pre-existing unused-variable warnings (`hM` at 527,
`hh` at 586) — no errors. `lake build OpenMath.Chapter4.Section404`
rebuilt the `.olean` cache successfully (8027/8027 jobs, 219s).

`#print axioms` reports the standard tripod for all three new
declarations:

```
'…localTruncationError_bound'        depends on axioms: [propext, Classical.choice, Quot.sound]
'…localTruncationError_α_sum_bound'  depends on axioms: [propext, Classical.choice, Quot.sound]
'…localTruncationError_β_sum_bound'  depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`. Project `OpenMath/` is now `sorry`-free.

## Faithfulness check

### Main theorem `lem:406B`

- **Entity ID + textbook statement** (quoted from
  `extraction/formalization_data/entities/lem_406B.json`):

  > If $y$ is the exact solution to the standard initial value
  > problem and $x \in [x_0 + kh, \bar{x}]$, then
  > $L(y, x, h) \leq \left( \tfrac{1}{2} \sum_{i=1}^{k} i^2 |\alpha_i|
  >                + \sum_{i=1}^{k} i|i\alpha_i - \beta_i| \right)
  >   L M h^2.$

- **Lean statement captures.** The Lean RHS is
  `((1/2) ∑ (i+1)² |α_{i+1}| + ∑ (i+1) |β_{i+1}|) · L · M · h²`.
  This **differs** from the textbook RHS in the second-sum
  coefficient (Butcher: `i |i α_i − β_i|`; Lean: `(i+1) |β_{i+1}|`).

- **Justification for divergence.** Tracked in
  `.prover-state/issues/lem_406B_textbook_check.md`. The textbook
  decomposition `L(y,x,h) = ∑ α_i (y(x) − y(x−ih) − ih y'(x))
                            + h ∑ (iα_i − β_i)(y'(x) − y'(x−ih))`
  has a typo: the coefficient of the y'-difference must be `β_i`,
  not `iα_i − β_i`, for the consistency identity (404b)
  `∑ i α_i = ∑ β_i` to make the algebra work. Both the cycle 040
  worker and consultant verified this independently. The Lean
  statement encodes the corrected form. The docstring at lines
  977–986 documents this and points to the issue file.

- **Hypothesis-strength check.** `ContDiff ℝ 1 y` (instead of
  textbook-implicit "y is the exact solution of the IVP") was
  introduced in cycle 040 and documented at lines 517–525 of
  `Section404.lean`. Picard–Lindelöf (Butcher §110, our `thm:110C`)
  produces exactly such a `C¹` solution from a Lipschitz `f`, so
  this is making implicit content explicit, not strengthening.
  No new hypotheses introduced this cycle.

- **Tautology check.** The conclusion is a strict numerical
  inequality with non-trivial RHS; none of the hypotheses asserts
  `|L(y,x,h)| ≤ …`. Clean.

- **Identity check.** Proof is a four-step chain
  (`rw decomposition → abs_add_le → habs_h → le_trans → ring`).
  Not a single `exact`. Clean.

- **Definition smuggling check.** N/A — this is a theorem, not a
  definition.

### α-sum helper `localTruncationError_α_sum_bound`

- Pure helper lemma (no textbook entity ID). Bounds
  `|∑ α_{i+1} · (y(x) − y(x−(i+1)h) − (i+1)h y'(x))|` by the right
  α-coefficient.
- Tautology check: clean (LHS is an absolute-value sum, RHS is a
  product; not a hypothesis).
- Identity check: proof has 4 distinct steps. Clean.
- Hypothesis-strength check: same hypothesis list as
  `residual_bound`; none stronger than needed.

### β-sum helper `localTruncationError_β_sum_bound`

- Pure helper lemma. Bounds
  `|∑ β_{i+1} · (y'(x) − y'(x−(i+1)h))|` by the right β-coefficient.
- All checks clean (analogous to α-sum helper).

## Dead ends

- **Initial `abs_add` typo (planner-suggested).** The planner's
  combiner sketch used `abs_add _ _` for the triangle inequality.
  Mathlib's name is `abs_add_le _ _`; `abs_add` no longer exists in
  the version pinned by `lake-manifest.json`. Replaced and
  re-compiled — clean. (Recorded here so future cycles know the
  current Mathlib spelling.)

- No other dead ends. The decomposition recipe held up exactly as
  planned: triangle → distribute → summand-wise monotonicity →
  ring. Total wall-time well under cycle budget.

## Discovery

1. **`abs_add` ≠ `abs_add_le` in current Mathlib.** The plain
   `abs_add` identifier produces "Unknown identifier" errors; use
   `abs_add_le` (signature: `|a + b| ≤ |a| + |b|`). This may be a
   recent rename — earlier cycles' planner notes referenced
   `abs_add`. Adding to MEMORY would be borderline (it's grep-able),
   but worth flagging here.

2. **Cast bridge between `residual_bound` and the decomposition was
   trivial.** `residual_bound` is parameterised by `(i : ℕ)`; we
   pass `i.val + 1` and the resulting cast `((i.val + 1 : ℕ) : ℝ)`
   matches sub-lemma E's decomposition output verbatim. No
   `push_cast` bridge needed (contrary to the cautionary note in
   the planner). The MEMORY.md `SatisfiesEq404b cast bridging`
   pattern is specific to the (404b) identity, not to this assembly.

3. **`ring` closes the final algebra in one shot.** Both sides of
   the final inequality (after the `add_le_add` step) expand to
   `(1/2) A L M h² + B L M h²` where `A = ∑ (i+1)² |α|` and
   `B = ∑ (i+1) |β|`. No need for the planner's contingency
   `final_assembly` helper or `Finset.sum_mul`/`Finset.mul_sum`
   distribution. ~219s build time end-to-end (full `lake build`),
   no heartbeat warnings.

4. **Aristotle's sub-lemma B added a `Continuous f` hypothesis we
   avoided.** Aristotle's worksheet
   (`sub_lemmas_aristotle/sub_lemmas.lean`) needed
   `(hf_cont : Continuous f)` for sub-lemma B's Bochner-integrability
   argument. Our manual proof uses
   `(fun t => f (y t)) = deriv y` (via the ODE) and pulls continuity
   from `ContDiff ℝ 1 y`, avoiding a separate continuity-of-`f`
   hypothesis. The Lipschitz hypothesis is enough downstream
   (Lipschitz ⇒ Continuous), but our proof is structurally cleaner.

## Suggested next approach

`lem:406B` is closed. The natural next target per the textbook
chain is **`thm:406C`** (Global error bound for linear multistep
methods), which depends only on `lem:406B` + the consistency /
stability machinery already in place. Cycle 044 should:

1. Read `extraction/formalization_data/entities/thm_406C.json` for
   the textbook statement (Butcher §406C, the convergence theorem
   for stable + consistent LMMs).
2. Open a sorry-first scaffold for `thm:406C` in
   `OpenMath/Chapter4/Section404.lean` (or a new file
   `Section406.lean` if the section grows large — current
   Section404.lean is ~1010 lines).
3. Identify natural sub-lemmas (likely a Grönwall-type bound for
   the discrete recursion + the `lem:406B` LTE bound).
4. Submit ~5 of those sub-lemmas to Aristotle in batch, sleep 30
   min, then start manual closure.

Stretch ahead: `thm:406D` (necessary part of the convergence
characterisation) closes the §406 block and unblocks the
cross-chapter `thm:243A` (Ch.2 → Ch.4 deferral). Do not start
`thm:243A` until both `thm:406C` and `thm:406D` are formalized.

Cycle 044 should also re-validate that the `sorry` count is
genuinely zero project-wide:

```
rg -nP '^\s*sorry\b|:=\s*sorry\b' OpenMath/   # expect: no matches
```

(Per cycle 042 discovery: `#print axioms` reads cached `.olean`,
so only trust it after `lake build`. The cycle 043 sequence
edit → `lake env lean` → `lake build` → `#print axioms` is the
correct order and was followed.)
