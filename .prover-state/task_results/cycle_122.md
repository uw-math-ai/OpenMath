# Cycle 122 Results

## Worked on
Closing 3 of 4 sorry's in `OpenMath/ReflectedMethods.lean` — the reflected-method transfer theorems for simplifying assumptions B, C, D (Theorem 343B from Iserles).

## Approach
1. **Aristotle results**: Downloaded Aristotle's completed proof of `reflect_satisfiesB` (project `4928f1e9`). Adapted its approach (algebraic binomial-coefficient identity over ℝ) rather than directly porting the ℚ-based proof.

2. **Combinatorial helper lemmas**: Built a shared infrastructure of 7 private lemmas:
   - `choose_div_succ'`: C(n,k)/(k+1) = C(n+1,k+1)/(n+1) over ℝ
   - `alternating_choose_shift'`: Shifted alternating sum = 1 (over ℤ)
   - `alternating_binom_div_succ`: Core identity ∑ C(n,k)(-1)^k/(k+1) = 1/(n+1)
   - `choose_div_cast`: C(k-1,m)/(m+1) = C(k,m+1)/k
   - `alternating_shifted_binom_sum`: ∑ C(k,m+1)(-1)^m = 1 over ℝ
   - `weighted_binom_sum`: ∑ C(k,m+1)(-1)^m x^{m+1} = 1-(1-x)^k
   - `binom_one_sub_pow_div`: Combined identity for transfer proofs
   - `binom_pow_div`: Variant for the D proof
   - `one_sub_pow_expand`: Binomial expansion of (1-x)^(k-1)

3. **B/C/D condition helpers**:
   - `bc_combined`: Combines B + C to get ∑(b_j - A_{i,j})c_j^m = (1-c_i^{m+1})/(m+1)

4. **Proof structure** (same pattern for B, C, D):
   - Expand (1-c)^{k-1} via binomial theorem
   - Swap finite sums
   - Apply the original B/C/D hypothesis to each inner sum
   - Reduce to a combinatorial identity via choose_div and alternating sum lemmas

## Result
**SUCCESS** — 3 of 4 sorry's closed. Regression reversed from 4→1 sorry.

### Closed:
- `reflect_satisfiesB` (Theorem 343B, eq. 343d) — 0 sorry
- `reflect_satisfiesC` (Theorem 343B, eq. 343e) — 0 sorry
- `reflect_satisfiesD` (Theorem 343B, eq. 343f) — 0 sorry

### Remaining:
- `reflect_satisfiesE` (Theorem 343B, eq. 343g) — 1 sorry. This requires a double binomial sum identity that is significantly more complex.

### Aristotle jobs:
- `4928f1e9` (B): COMPLETE — proof adapted and incorporated
- `0384c983` (C): COMPLETE_WITH_ERRORS — used approach ideas but rewrote independently
- `1e6ea557` (D): IN_PROGRESS (16%) — proved manually before completion
- `9cc99ed3` (E): IN_PROGRESS (15%) — still running, check next cycle

### Verification:
All three theorems verified with `lean_verify`: only standard axioms (propext, Classical.choice, Quot.sound). File compiles cleanly with only the E sorry warning.

## Dead ends
- Aristotle's B proof was over ℚ and couldn't be directly ported — needed adaptation to ℝ.
- `ring` tactic doesn't handle `↑(k+1)` vs `↑k + 1` inversions — required `push_cast` workarounds.
- `conv ... ext i` fails with "No ext theorem for ℝ" when navigating into lambda bodies — used `simp_rw` with explicit `show` statements instead.

## Discovery
- The binomial-expansion + sum-swap + apply-hypothesis pattern works uniformly for B, C, D.
- The key infrastructure is the pair of identities: `alternating_binom_div_succ` and `binom_one_sub_pow_div`.
- For E, the double-sum structure requires a more complex combinatorial identity involving a double binomial sum over 1/((b+1)(a+b+2)), which doesn't reduce easily to single-variable identities.

## Suggested next approach
1. Check Aristotle jobs `1e6ea557` (D) and `9cc99ed3` (E) — if E completed, incorporate.
2. For E: try partial-fraction decomposition 1/((b+1)(a+b+2)) = 1/(a+1) * [1/(b+1) - 1/(a+b+2)], which separates the double sum into products of single sums. The inner sum ∑_b C(l-1,b)(-1)^b/(a+b+2) can be evaluated as a beta function ratio.
3. Alternative for E: prove by induction on l, using the l=1 base case and a telescoping identity.
