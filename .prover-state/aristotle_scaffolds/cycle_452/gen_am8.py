"""Generate LMMAM8Convergence.lean from LMMAM7Convergence.lean by audited substitutions.

Numerical substitutions are validated explicitly for AM8:
  β_0..β_8 = (-33953, 312874, -1291214, 3146338, -5033120, 5595358, -4604594,
              4467094, 1070017) / 3628800
  S_num = sum(|β_i| for i < 8) = 24484545
  β_s   = 1070017/3628800 (implicit)
  D     = 3628800
  Sum of explicit |β| over D ≈ 6.747
  Growth constant G = 15 (smallest integer ≥ 2*(β_s + S) ≈ 14.08)
  Residual coefficient C = 4555920744497/6858432000 ≈ 664.28, slack to 665.
  N1 = D*G - β_s_num - S_num = 28877438
  N2 = G * β_s_num = 16050255
  hL bound from hsmall: hL ≤ 1814400/1070017
  Verification: N2 * (1814400/1070017) = 15 * 1814400 = 27216000 ≤ 28877438 ✓
"""

# ==== This is a scratch script for cycle 452. We'll build the file by hand. ====
