#!/usr/bin/env python3
"""Build LMMAM8Convergence.lean from scratch with exact AM8 numerics.

This avoids sed/regex pitfalls by emitting each section explicitly with
verified numerical parameters. We import only the structural skeleton
(section headers, helper lemma signatures); the proofs themselves are
rebuilt with AM8 numbers.
"""

import sys
from pathlib import Path

OUT = Path('/mmfs1/gscratch/amath/mathai/OpenMath/OpenMath/LMMAM8Convergence.lean')

# ===== AM8 parameters =====
# Recurrence: y_{n+8} = y_{n+7} + h * (β_8 f_{n+8} + β_7 f_{n+7} - β_6 f_{n+6}
#                                     + β_5 f_{n+5} - β_4 f_{n+4} + β_3 f_{n+3}
#                                     - β_2 f_{n+2} + β_1 f_{n+1} - β_0 f_n)
# Absolute numerators over D = 3628800:
B0 = 33953     # -
B1 = 312874    # +
B2 = 1291214   # -
B3 = 3146338   # +
B4 = 5033120   # -
B5 = 5595358   # +
B6 = 4604594   # -
B7 = 4467094   # +
B8 = 1070017   # + (implicit)
D  = 3628800

# Sign in recurrence as written above (j=0..8 reverse of summing convention)
# In the trajectory, recurrence is written from highest index down:
#   + β8*f_{n+8}  (implicit, sign +)
#   + β7*f_{n+7}                   (sign +)
#   - β6*f_{n+6}                   (sign -)
#   + β5*f_{n+5}                   (sign +)
#   - β4*f_{n+4}                   (sign -)
#   + β3*f_{n+3}                   (sign +)
#   - β2*f_{n+2}                   (sign -)
#   + β1*f_{n+1}                   (sign +)
#   - β0*f_n                       (sign -)

S_num = B0+B1+B2+B3+B4+B5+B6+B7  # 24484545
assert S_num == 24484545
G = 15
N1 = D*G - B8 - S_num  # 54432000 - 1070017 - 24484545 = 28877438
N2 = G * B8  # 15 * 1070017 = 16050255
assert N1 == 28877438
assert N2 == 16050255

# Residual coefficient
C_num = 4555920744497
C_den = 6858432000
C_slack = 665

print(f"S_num={S_num}, β_s_num={B8}, G={G}, N1={N1}, N2={N2}")
print(f"C_exact = {C_num}/{C_den} ≈ {C_num/C_den:.4f}")
print(f"C_slack = {C_slack}")
print(f"N2 * (D/(2*B8)) = {N2*D/(2*B8)}, slack to N1: {N1 - N2*D/(2*B8)}")
