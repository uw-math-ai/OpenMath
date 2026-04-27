# Cycle 482 Results

## Worked on

Adams–Moulton 11-step **vector** quantitative convergence chain in
`OpenMath/LMMAM11VectorConvergence.lean`. Mirror of the cycle-481 scalar
AM11 chain (`LMMAM11Convergence.lean`) but in a finite-dimensional normed
vector space `E` with `•` (smul) in place of `*`. The key challenge was
the cycle-480 wall: a 13-abstract-witness algebraic identity blows the
200000-heartbeat statement-elaboration budget when each witness equality
mentions twelve scalar-mul-sub terms inline.

## Approach

1. Built the file by transplanting the AM10 vector template (cycle 478,
   `LMMAM10VectorConvergence.lean`, 1881 lines) and extending by one step.
2. Established the thirteenth-order vector Taylor helpers in-file
   (`iteratedDeriv_thirteen_bounded_on_Icc_vec`,
   `y_thirteenth_order_taylor_remainder_vec`,
   `derivY_twelfth_order_taylor_remainder_vec`) by integrating the
   twelfth-order helper from `LMMAB11VectorConvergence.lean` against the
   thirteenth-order iterated derivative bound.
3. Stated the residual algebraic identity over **thirteen abstract
   witnesses** `A B C D F G I J K L P Q R : E` (skipping `E` as that's
   the type variable, `H` for `h`, `M` for the bound, `N`/`O` for clarity).
4. **Packed-poly extraction (cycle-482 lesson)**: the 13-witness statement
   still timed out when each `hX : X = … - (m h) • d0 - ((m h)^2/2) • d2t
   - … - ((m h)^12/479001600) • d12t` chain was inlined. To fix this,
   introduced two private helpers
   `am11Vec_yPoly12 (m h) d0 d2t … d12t` and
   `am11Vec_dPoly11 (m h) d2t … d12t` that pack the 12-term y-form and
   11-term deriv-form Taylor polynomials. Each witness equality then
   collapses to `hX : X = y_k - y_0 - am11Vec_yPoly12 k h d0 d2t … d12t`
   — a single function call instead of an inline twelve-fold scalar-mul-sub
   chain. This brought the 13-witness statement back inside the 200K
   budget.
5. The proof body of `am11Vec_residual_alg_identity` is `subst hA … hR`
   (13 substs) followed by `unfold am11Vec_yPoly12 am11Vec_dPoly11` and
   then `module`. `module` is then operating on the unfolded explicit
   polynomial form, so it closes within budget.
6. In `am11Vec_pointwise_residual_bound`, after `set A := y11 - y0
   - am11Vec_yPoly12 11 h d0 …` (and twelve siblings), the 13 norm bounds
   `‖A‖ ≤ M / 6227020800 * (11*h)^13` etc. are established by
   `rw [hA_def]; unfold am11Vec_yPoly12; convert hRy11 using 2; module`
   — i.e. the existing `set` hypothesis lets us unfold the packed-poly
   form back into the chained-subtraction form that
   `y_thirteenth_order_taylor_remainder_vec` produces, with `module`
   closing the algebraic mismatch (`a - (b+c+d) = a - b - c - d`).
   Crucially `clear_value A B C D F G I J K L P Q R` is moved to **after**
   the bounds are established — earlier, with `clear_value` before the
   bounds, the def equalities were gone and the rewrite couldn't run.
7. Two further extracted helpers tame the 200K budget elsewhere in the
   one-step error bound:
   - `am11Vec_max11_bounds`: returns the conjunction of 11 bounds for the
     nested 11-fold max of `eN`, avoiding the inline
     `le_trans (le_max_left …) …` chain blowup observed when extracted
     inline.
   - `am11Vec_slack_aux`: returns `(hcoeffE_le, hcoeffτ_le, hA_pos)` for
     the slack arithmetic, computed in a clean context (the giant
     ~50-hypothesis context inside the one-step error bound made
     `linarith`/`nlinarith` essentially quadratic).
8. The headline `LMM.am11Vec_global_error_bound` mirrors the AM10 vec
   headline at lines 1569–1879: 11-fold max window `EN`, 11 base cases
   N=0..10 in a `match`, inductive case `N' + 11`, condition
   `(N+10)·h ≤ T`, growth `(1 + h*(61*L))`, conclusion
   `‖yseq N - y(t₀ + N·h)‖ ≤ exp((61·L)·T) · ε₀ + K · h^11`. Routed
   through `lmm_error_bound_from_local_truncation` with `p := 11`,
   `L := 61 * L`.

## Result

**SUCCESS**. `OpenMath/LMMAM11VectorConvergence.lean` (~2495 lines)
compiles cleanly with `lake env lean` and contains zero `sorry`. All
declarations from the strategy land in the documented order:
`IsAM11TrajectoryVec`, `am11VecResidual`,
`am11Vec_localTruncationError_eq`, `am11Vec_one_step_lipschitz`,
`am11Vec_one_step_error_bound`, `am11Vec_one_step_error_pair_bound`,
the four extracted residual helpers
(`am11Vec_residual_alg_identity`, `am11Vec_residual_bound_alg_identity`,
`am11Vec_residual_thirteen_term_triangle`,
`am11Vec_residual_combine_aux`),
`am11Vec_pointwise_residual_bound`, `am11Vec_local_residual_bound`, and
the headline `am11Vec_global_error_bound`.

`plan.md` has the new bullet on line 102 right after the AM11 scalar
bullet.

## Dead ends

- **First attempt with inline witness equalities** (each `hX : X = y_k -
  y_0 - (m h) • d0 - ((m h)^2/2) • d2t - … - ((m h)^12/479001600) • d12t`
  written inline 13 times in the alg identity statement) hit the 200K
  budget at *statement elaboration* — exactly the cycle-480 wall. This
  is the failure mode that needed packed-poly extraction.
- **First attempt at `am11Vec_one_step_error_bound`** with inline
  `linarith [hsmall]` for `hcoeffτ_le` and inline 11-fold
  `le_trans (le_max_left …) …` chains for the max bounds blew the budget
  in the giant `set`-context. Multiple iterative tweaks (`change` rewrites,
  `nlinarith`, `clear_value` of unused locals) all still timed out
  because `linarith` is roughly quadratic in context size. Fix:
  extract `am11Vec_max11_bounds` and `am11Vec_slack_aux` as small
  private aux lemmas computed in clean contexts.
- **First attempt at norm-bounds passing to `am11Vec_residual_combine_aux`**
  used `have hA_bd := hRy11` directly. This failed because `A` was
  defined by `set` with the packed-poly form `am11Vec_yPoly12 …` while
  `hRy11` mentions the chained-subtraction Taylor remainder form — these
  are propositionally but not definitionally equal. Fix: introduce each
  bound by `rw [hA_def]; unfold am11Vec_yPoly12; convert hRy11 using 2;
  module` to bridge the `+` vs `-` chain associativity. Also required
  moving `clear_value` to *after* the bound block (so `hA_def` etc. are
  still in scope at rewrite time).

## Discovery

**The cycle-482 lesson — packed-poly extraction unblocks the 13-witness
vector wall.** When a parameterized residual algebraic identity has too
many witnesses (≥ 13) and each witness equality mentions a 12-term
Taylor polynomial inline, statement elaboration alone overflows the
200K heartbeat budget. The fix is to introduce two private definitions
packing the y-form and deriv-form Taylor polynomials as single function
calls, then state each witness equality as `X = … - amXVec_yPoly… (m h)
d0 …`. The proof body adds `unfold` before `module`, which keeps `module`
operating on the explicit polynomial form (this is what closes the
identity).

This bullet was promised to unblock AB12 vector — and it does. AB12 vector
has the same 13-witness shape (twelve weights, thirteen-term residual
identity), and the only structural difference is that AB12 is explicit
(no implicit `β_11` weight), so its parameterized identity has the same
13-witness skeleton. With `am11Vec_yPoly12` / `am11Vec_dPoly11` as
templates and the cycle-482 packed-poly extraction trick, AB12 vector
should land in cycle 483 without rerunning the cycle-480 timeout dance.

## Suggested next approach

**Cycle 483: AB12 vector**, using the cycle-482 packed-poly extraction.
Reuse the now-public thirteenth-order vector Taylor helpers
(`iteratedDeriv_thirteen_bounded_on_Icc_vec`,
`y_thirteenth_order_taylor_remainder_vec`,
`derivY_twelfth_order_taylor_remainder_vec`) from
`LMMAM11VectorConvergence.lean`. The AB12 scalar chain is already done
(cycle 479, `LMMAB12Convergence.lean`); the vector chain should route
through `ab_global_error_bound_generic_vec` at `s = p = 12` exactly as
AB11 vector (cycle 476) routed at `s = p = 11`. The packed-poly extraction
is the only structural change vs the cycle-480 attempt.

After AB12 vector lands, the §1.2 Adams quantitative-convergence frontier
is complete through 11/12 steps — both AB and AM, both scalar and vector.
The next §1.2 frontier is then either Adams-PEC (predictor-corrector
with one fixed-point iteration) or pushing to AB/AM 13–14, but more
likely we move to §1.3 (the BDF chain past BDF7 is zero-unstable and
moot, so §1.3 is the next chapter — multistep methods for stiff systems
beyond BDF, or stiff RK methods).

## Aristotle policy this cycle

**SKIPPED** as documented in strategy. Cert was still expired at the
start of this cycle. No `mcp__aristotle__submit_*` calls were made. All
proofs were closed manually using LSP tooling and the cycle-476/478
parameterized-identity pattern with the new cycle-482 packed-poly
extension.
