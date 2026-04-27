import OpenMath.MultistepMethods

/-!
# Adams Methods

Adams-Bashforth and Adams-Moulton linear multistep methods from Iserles,
*A First Course in the Numerical Analysis of Differential Equations*, Section 1.2.
-/

open Finset Real

/-! ## Definitions -/

/-- **Adams–Bashforth 2-step** method:
y_{n+2} = y_{n+1} + h·(3/2·f_{n+1} - 1/2·f_n).
Coefficients: α = [0, -1, 1], β = [-1/2, 3/2, 0]. -/
noncomputable def adamsBashforth2 : LMM 2 where
  α := ![0, -1, 1]
  β := ![-1/2, 3/2, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 2-step** method:
y_{n+2} = y_{n+1} + h·(5/12·f_{n+2} + 8/12·f_{n+1} - 1/12·f_n).
Coefficients: α = [0, -1, 1], β = [-1/12, 8/12, 5/12].
This is an implicit method of order 3.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsMoulton2 : LMM 2 where
  α := ![0, -1, 1]
  β := ![-1/12, 8/12, 5/12]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 3-step** method:
y_{n+3} = y_{n+2} + h·(23/12·f_{n+2} - 16/12·f_{n+1} + 5/12·f_n).
Coefficients: α = [0, 0, -1, 1], β = [5/12, -16/12, 23/12, 0].
This is an explicit method of order 3.
Reference: Iserles, Section 1.3. -/
noncomputable def adamsBashforth3 : LMM 3 where
  α := ![0, 0, -1, 1]
  β := ![5/12, -16/12, 23/12, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 3-step** method:
y_{n+3} = y_{n+2} + h·(9/24·f_{n+3} + 19/24·f_{n+2}
  - 5/24·f_{n+1} + 1/24·f_n).
Coefficients: α = [0, 0, -1, 1], β = [1/24, -5/24, 19/24, 9/24].
This is an implicit method of order 4.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsMoulton3 : LMM 3 where
  α := ![0, 0, -1, 1]
  β := ![1/24, -5/24, 19/24, 9/24]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 4-step** method:
y_{n+4} = y_{n+3} + h·(55/24·f_{n+3} - 59/24·f_{n+2}
  + 37/24·f_{n+1} - 9/24·f_n).
Coefficients: α = [0, 0, 0, -1, 1], β = [-9/24, 37/24, -59/24, 55/24, 0].
This is an explicit method of order 4.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsBashforth4 : LMM 4 where
  α := ![0, 0, 0, -1, 1]
  β := ![-9/24, 37/24, -59/24, 55/24, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 4-step** method:
y_{n+4} = y_{n+3} + h·(251/720·f_{n+4} + 646/720·f_{n+3}
  - 264/720·f_{n+2} + 106/720·f_{n+1} - 19/720·f_n).
Coefficients: α = [0, 0, 0, -1, 1], β = [-19/720, 106/720, -264/720, 646/720, 251/720].
This is an implicit method of order 5.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsMoulton4 : LMM 4 where
  α := ![0, 0, 0, -1, 1]
  β := ![-19/720, 106/720, -264/720, 646/720, 251/720]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 5-step** method:
y_{n+5} = y_{n+4} + h·(1901/720·f_{n+4} - 2774/720·f_{n+3}
  + 2616/720·f_{n+2} - 1274/720·f_{n+1} + 251/720·f_n).
Coefficients: α = [0, 0, 0, 0, -1, 1], β = [251/720, -1274/720, 2616/720, -2774/720, 1901/720, 0].
This is an explicit method of order 5.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsBashforth5 : LMM 5 where
  α := ![0, 0, 0, 0, -1, 1]
  β := ![251/720, -1274/720, 2616/720, -2774/720, 1901/720, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 6-step** method:
y_{n+6} = y_{n+5} + h·(4277/1440·f_{n+5} - 7923/1440·f_{n+4}
  + 9982/1440·f_{n+3} - 7298/1440·f_{n+2}
  + 2877/1440·f_{n+1} - 475/1440·f_n).
Coefficients: α = [0, 0, 0, 0, 0, -1, 1],
β = [-475/1440, 2877/1440, -7298/1440, 9982/1440, -7923/1440, 4277/1440, 0].
This is an explicit method of order 6.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsBashforth6 : LMM 6 where
  α := ![0, 0, 0, 0, 0, -1, 1]
  β := ![-475/1440, 2877/1440, -7298/1440, 9982/1440, -7923/1440, 4277/1440, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 5-step** method:
y_{n+5} = y_{n+4} + h·(475/1440·f_{n+5} + 1427/1440·f_{n+4}
  − 798/1440·f_{n+3} + 482/1440·f_{n+2} − 173/1440·f_{n+1} + 27/1440·f_n).
Coefficients: α = [0, 0, 0, 0, -1, 1],
β = [27/1440, -173/1440, 482/1440, -798/1440, 1427/1440, 475/1440].
This is an implicit method of order 6.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsMoulton5 : LMM 5 where
  α := ![0, 0, 0, 0, -1, 1]
  β := ![27/1440, -173/1440, 482/1440, -798/1440, 1427/1440, 475/1440]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 6-step** method:
y_{n+6} = y_{n+5} + h·(19087/60480·f_{n+6} + 65112/60480·f_{n+5}
  − 46461/60480·f_{n+4} + 37504/60480·f_{n+3}
  − 20211/60480·f_{n+2} + 6312/60480·f_{n+1} − 863/60480·f_n).
Coefficients: α = [0, 0, 0, 0, 0, -1, 1],
β = [-863/60480, 6312/60480, -20211/60480, 37504/60480, -46461/60480,
     65112/60480, 19087/60480].
This is an implicit method of order 7.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsMoulton6 : LMM 6 where
  α := ![0, 0, 0, 0, 0, -1, 1]
  β := ![-863/60480, 6312/60480, -20211/60480, 37504/60480, -46461/60480,
        65112/60480, 19087/60480]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 7-step** method:
y_{n+7} = y_{n+6} + h·(198721/60480·f_{n+6} - 447288/60480·f_{n+5}
  + 705549/60480·f_{n+4} - 688256/60480·f_{n+3}
  + 407139/60480·f_{n+2} - 134472/60480·f_{n+1} + 19087/60480·f_n).
Coefficients: α = [0, 0, 0, 0, 0, 0, -1, 1],
β = [19087/60480, -134472/60480, 407139/60480, -688256/60480,
     705549/60480, -447288/60480, 198721/60480, 0].
This is an explicit method of order 7.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsBashforth7 : LMM 7 where
  α := ![0, 0, 0, 0, 0, 0, -1, 1]
  β := ![19087/60480, -134472/60480, 407139/60480, -688256/60480,
        705549/60480, -447288/60480, 198721/60480, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 7-step** method:
y_{n+7} = y_{n+6} + h·(36799/120960·f_{n+7} + 139849/120960·f_{n+6}
  − 121797/120960·f_{n+5} + 123133/120960·f_{n+4}
  − 88547/120960·f_{n+3} + 41499/120960·f_{n+2}
  − 11351/120960·f_{n+1} + 1375/120960·f_n).
Coefficients: α = [0, 0, 0, 0, 0, 0, -1, 1],
β = [1375/120960, -11351/120960, 41499/120960, -88547/120960,
     123133/120960, -121797/120960, 139849/120960, 36799/120960].
This is an implicit method of order 8.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsMoulton7 : LMM 7 where
  α := ![0, 0, 0, 0, 0, 0, -1, 1]
  β := ![1375/120960, -11351/120960, 41499/120960, -88547/120960,
        123133/120960, -121797/120960, 139849/120960, 36799/120960]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 8-step** method:
y_{n+8} = y_{n+7} + h·(434241/120960·f_{n+7} - 1152169/120960·f_{n+6}
  + 2183877/120960·f_{n+5} - 2664477/120960·f_{n+4}
  + 2102243/120960·f_{n+3} - 1041723/120960·f_{n+2}
  + 295767/120960·f_{n+1} - 36799/120960·f_n).
Coefficients: α = [0, 0, 0, 0, 0, 0, 0, -1, 1],
β = [-36799/120960, 295767/120960, -1041723/120960, 2102243/120960,
     -2664477/120960, 2183877/120960, -1152169/120960, 434241/120960, 0].
This is an explicit method of order 8.
Reference: Iserles, Section 1.2 (k = 8 Adams–Bashforth); coefficients
verified against the order conditions
`Σ β_k · (k - 7)^j = 1/(j + 1)` for j = 0,…,7. -/
noncomputable def adamsBashforth8 : LMM 8 where
  α := ![0, 0, 0, 0, 0, 0, 0, -1, 1]
  β := ![-36799/120960, 295767/120960, -1041723/120960, 2102243/120960,
        -2664477/120960, 2183877/120960, -1152169/120960, 434241/120960, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 9-step** method:
y_{n+9} = y_{n+8} + h·(14097247/3628800·f_{n+8} - 43125206/3628800·f_{n+7}
  + 95476786/3628800·f_{n+6} - 139855262/3628800·f_{n+5}
  + 137968480/3628800·f_{n+4} - 91172642/3628800·f_{n+3}
  + 38833486/3628800·f_{n+2} - 9664106/3628800·f_{n+1}
  + 1070017/3628800·f_n).
Coefficients: α = [0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
β = [1070017/3628800, -9664106/3628800, 38833486/3628800, -91172642/3628800,
     137968480/3628800, -139855262/3628800, 95476786/3628800,
     -43125206/3628800, 14097247/3628800, 0].
This is an explicit method of order 9.
Reference: Iserles, Section 1.2 (k = 9 Adams–Bashforth); coefficients
verified against the Lagrange-interpolation-and-integrate construction on
nodes 0,…,8 over the interval [8, 9] (denominator `10! = 3628800`). -/
noncomputable def adamsBashforth9 : LMM 9 where
  α := ![0, 0, 0, 0, 0, 0, 0, 0, -1, 1]
  β := ![1070017/3628800, -9664106/3628800, 38833486/3628800, -91172642/3628800,
        137968480/3628800, -139855262/3628800, 95476786/3628800,
        -43125206/3628800, 14097247/3628800, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 10-step** method:
y_{n+10} = y_{n+9} + h·(30277247/7257600·f_{n+9} - 104995189/7257600·f_{n+8}
  + 265932680/7257600·f_{n+7} - 454661776/7257600·f_{n+6}
  + 538363838/7257600·f_{n+5} - 444772162/7257600·f_{n+4}
  + 252618224/7257600·f_{n+3} - 94307320/7257600·f_{n+2}
  + 20884811/7257600·f_{n+1} - 2082753/7257600·f_n).
Coefficients: α = [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
β = [-2082753/7257600, 20884811/7257600, -94307320/7257600,
     252618224/7257600, -444772162/7257600, 538363838/7257600,
     -454661776/7257600, 265932680/7257600, -104995189/7257600,
     30277247/7257600, 0].
This is an explicit method of order 10.
Reference: Iserles, Section 1.2 (k = 10 Adams–Bashforth); coefficients
verified against the Lagrange-interpolation-and-integrate construction on
nodes 0,…,9 over the interval [9, 10] (denominator `2·10! = 7257600`);
sums to 1 over the common denominator. -/
noncomputable def adamsBashforth10 : LMM 10 where
  α := ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1]
  β := ![-2082753/7257600, 20884811/7257600, -94307320/7257600,
        252618224/7257600, -444772162/7257600, 538363838/7257600,
        -454661776/7257600, 265932680/7257600, -104995189/7257600,
        30277247/7257600, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 11-step** method:
y_{n+11} = y_{n+10} + h·(2132509567/479001600·f_{n+10}
  - 8271795124/479001600·f_{n+9}
  + 23591063805/479001600·f_{n+8}
  - 46113029016/479001600·f_{n+7}
  + 63716378958/479001600·f_{n+6}
  - 63176201472/479001600·f_{n+5}
  + 44857168434/479001600·f_{n+4}
  - 22329634920/479001600·f_{n+3}
  + 7417904451/479001600·f_{n+2}
  - 1479574348/479001600·f_{n+1}
  + 134211265/479001600·f_n).
Coefficients: α = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
β = [134211265/479001600, -1479574348/479001600,
     7417904451/479001600, -22329634920/479001600,
     44857168434/479001600, -63176201472/479001600,
     63716378958/479001600, -46113029016/479001600,
     23591063805/479001600, -8271795124/479001600,
     2132509567/479001600, 0].
This is an explicit method of order 11.
Reference: Iserles, Section 1.2 (k = 11 Adams–Bashforth); coefficients
verified by exact `Fraction` arithmetic from the Lagrange-interpolation-and-
integrate construction on nodes 0,…,10 over `[10, 11]` (denominator `12! =
479001600`); the numerators sum to `479001600`. -/
noncomputable def adamsBashforth11 : LMM 11 where
  α := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1]
  β := ![134211265/479001600, -1479574348/479001600,
        7417904451/479001600, -22329634920/479001600,
        44857168434/479001600, -63176201472/479001600,
        63716378958/479001600, -46113029016/479001600,
        23591063805/479001600, -8271795124/479001600,
        2132509567/479001600, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 12-step** method:
y_{n+12} = y_{n+11} + h·(4527766399/958003200·f_{n+11}
  - 19433810163/958003200·f_{n+10}
  + 61633227185/958003200·f_{n+9}
  - 135579356757/958003200·f_{n+8}
  + 214139355366/958003200·f_{n+7}
  - 247741639374/958003200·f_{n+6}
  + 211103573298/958003200·f_{n+5}
  - 131365867290/958003200·f_{n+4}
  + 58189107627/958003200·f_{n+3}
  - 17410248271/958003200·f_{n+2}
  + 3158642445/958003200·f_{n+1}
  - 262747265/958003200·f_n).
Coefficients: α = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
β = [-262747265/958003200, 3158642445/958003200,
     -17410248271/958003200, 58189107627/958003200,
     -131365867290/958003200, 211103573298/958003200,
     -247741639374/958003200, 214139355366/958003200,
     -135579356757/958003200, 61633227185/958003200,
     -19433810163/958003200, 4527766399/958003200, 0].
This is an explicit method of order 12.
Reference: Iserles, Section 1.2 (k = 12 Adams–Bashforth); coefficients
verified by exact `Fraction` arithmetic from the Lagrange-interpolation-and-
integrate construction on nodes 0,…,11 over `[11, 12]` (smallest common
denominator `958003200`); the numerators sum to `958003200`. -/
noncomputable def adamsBashforth12 : LMM 12 where
  α := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1]
  β := ![-262747265/958003200, 3158642445/958003200,
        -17410248271/958003200, 58189107627/958003200,
        -131365867290/958003200, 211103573298/958003200,
        -247741639374/958003200, 214139355366/958003200,
        -135579356757/958003200, 61633227185/958003200,
        -19433810163/958003200, 4527766399/958003200, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 13-step** method. Coefficients
α = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
β = [703604254357/2615348736000, -9160551085734/2615348736000,
     55060974662412/2615348736000, -202322913738370/2615348736000,
     507140369728425/2615348736000, -915883387152444/2615348736000,
     1226443086129408/2615348736000, -1233589244941764/2615348736000,
     932884546055895/2615348736000, -524924579905150/2615348736000,
     214696591002612/2615348736000, -61497552797274/2615348736000,
     13064406523627/2615348736000, 0].
This is an explicit method of order 13.
Reference: Iserles, Section 1.2 (k = 13 Adams–Bashforth); coefficients
verified by exact `Fraction` arithmetic from the Lagrange-interpolation-and-
integrate construction on nodes 0,…,12 over `[12, 13]` (smallest common
denominator `2615348736000 = 420 · 13!`); the numerators sum to
`2615348736000`. -/
noncomputable def adamsBashforth13 : LMM 13 where
  α := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1]
  β := ![703604254357/2615348736000, -9160551085734/2615348736000,
        55060974662412/2615348736000, -202322913738370/2615348736000,
        507140369728425/2615348736000, -915883387152444/2615348736000,
        1226443086129408/2615348736000, -1233589244941764/2615348736000,
        932884546055895/2615348736000, -524924579905150/2615348736000,
        214696591002612/2615348736000, -61497552797274/2615348736000,
        13064406523627/2615348736000, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 8-step** method:
y_{n+8} = y_{n+7} + h·(1070017/3628800·f_{n+8} + 4467094/3628800·f_{n+7}
  − 4604594/3628800·f_{n+6} + 5595358/3628800·f_{n+5}
  − 5033120/3628800·f_{n+4} + 3146338/3628800·f_{n+3}
  − 1291214/3628800·f_{n+2} + 312874/3628800·f_{n+1}
  − 33953/3628800·f_n).
Coefficients: α = [0, 0, 0, 0, 0, 0, 0, -1, 1],
β = [-33953/3628800, 312874/3628800, -1291214/3628800, 3146338/3628800,
     -5033120/3628800, 5595358/3628800, -4604594/3628800, 4467094/3628800,
     1070017/3628800].
This is an implicit method of order 9.
Reference: Iserles, Section 1.2 (k = 8 Adams–Moulton); coefficients
verified against the Lagrange-interpolation-and-integrate construction on
nodes 0,…,8 over the interval [7, 8] (denominator `10! = 3628800`). -/
noncomputable def adamsMoulton8 : LMM 8 where
  α := ![0, 0, 0, 0, 0, 0, 0, -1, 1]
  β := ![-33953/3628800, 312874/3628800, -1291214/3628800, 3146338/3628800,
        -5033120/3628800, 5595358/3628800, -4604594/3628800, 4467094/3628800,
        1070017/3628800]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 9-step** method:
y_{n+9} = y_{n+8} + h·(2082753/7257600·f_{n+9}
  + 9449717/7257600·f_{n+8} − 11271304/7257600·f_{n+7}
  + 16002320/7257600·f_{n+6} − 17283646/7257600·f_{n+5}
  + 13510082/7257600·f_{n+4} − 7394032/7257600·f_{n+3}
  + 2687864/7257600·f_{n+2} − 583435/7257600·f_{n+1}
  + 57281/7257600·f_n).
Coefficients: α = [0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
β = [57281/7257600, -583435/7257600, 2687864/7257600,
     -7394032/7257600, 13510082/7257600, -17283646/7257600,
     16002320/7257600, -11271304/7257600, 9449717/7257600,
     2082753/7257600].
This is an implicit method of order 10.
Reference: Iserles, Section 1.2 (k = 9 Adams–Moulton); coefficients
verified against the Lagrange-interpolation-and-integrate construction on
nodes 0,…,9 over the interval [8, 9] (denominator `2·10! = 7257600`);
sums to 1 over the common denominator. -/
noncomputable def adamsMoulton9 : LMM 9 where
  α := ![0, 0, 0, 0, 0, 0, 0, 0, -1, 1]
  β := ![57281/7257600, -583435/7257600, 2687864/7257600,
        -7394032/7257600, 13510082/7257600, -17283646/7257600,
        16002320/7257600, -11271304/7257600, 9449717/7257600,
        2082753/7257600]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 10-step** method:
y_{n+10} = y_{n+9} + h·(134211265/479001600·f_{n+10}
  + 656185652/479001600·f_{n+9}
  − 890175549/479001600·f_{n+8}
  + 1446205080/479001600·f_{n+7}
  − 1823311566/479001600·f_{n+6}
  + 1710774528/479001600·f_{n+5}
  − 1170597042/479001600·f_{n+4}
  + 567450984/479001600·f_{n+3}
  − 184776195/479001600·f_{n+2}
  + 36284876/479001600·f_{n+1}
  − 3250433/479001600·f_n).
Coefficients: α = [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
β = [-3250433/479001600, 36284876/479001600,
     -184776195/479001600, 567450984/479001600,
     -1170597042/479001600, 1710774528/479001600,
     -1823311566/479001600, 1446205080/479001600,
     -890175549/479001600, 656185652/479001600,
     134211265/479001600].
This is an implicit method of order 11.
Reference: Iserles, Section 1.2 (k = 10 Adams–Moulton); coefficients
verified by exact `Fraction` arithmetic from the Lagrange-interpolation-and-
integrate construction on nodes 0,…,10 over `[9, 10]` (denominator `12! =
479001600`); the numerators sum to `479001600`. -/
noncomputable def adamsMoulton10 : LMM 10 where
  α := ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1]
  β := ![-3250433/479001600, 36284876/479001600,
        -184776195/479001600, 567450984/479001600,
        -1170597042/479001600, 1710774528/479001600,
        -1823311566/479001600, 1446205080/479001600,
        -890175549/479001600, 656185652/479001600,
        134211265/479001600]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 11-step** method:
y_{n+11} = y_{n+10} + h·(262747265/958003200·f_{n+11}
  + 1374799219/958003200·f_{n+10}
  - 2092490673/958003200·f_{n+9}
  + 3828828885/958003200·f_{n+8}
  - 5519460582/958003200·f_{n+7}
  + 6043521486/958003200·f_{n+6}
  - 4963166514/958003200·f_{n+5}
  + 3007739418/958003200·f_{n+4}
  - 1305971115/958003200·f_{n+3}
  + 384709327/958003200·f_{n+2}
  - 68928781/958003200·f_{n+1}
  + 5675265/958003200·f_n).
Coefficients: α = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
β = [5675265/958003200, -68928781/958003200,
     384709327/958003200, -1305971115/958003200,
     3007739418/958003200, -4963166514/958003200,
     6043521486/958003200, -5519460582/958003200,
     3828828885/958003200, -2092490673/958003200,
     1374799219/958003200, 262747265/958003200].
This is an implicit method of order 12.
Reference: Iserles, Section 1.2 (k = 11 Adams–Moulton); coefficients
verified by exact `Fraction` arithmetic from the Lagrange-interpolation-and-
integrate construction on nodes 0,…,11 over `[10, 11]` (denominator
`2·12! = 958003200`); the numerators sum to `958003200`. -/
noncomputable def adamsMoulton11 : LMM 11 where
  α := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1]
  β := ![5675265/958003200, -68928781/958003200,
        384709327/958003200, -1305971115/958003200,
        3007739418/958003200, -4963166514/958003200,
        6043521486/958003200, -5519460582/958003200,
        3828828885/958003200, -2092490673/958003200,
        1374799219/958003200, 262747265/958003200]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 12-step** method:
y_{n+12} = y_{n+11} + h·Σ b_j f_{n+j} with denominator `2615348736000`.

Coefficients: α = [0, ..., 0, -1, 1] (length 13),
β = [-13695779093, 179842822566, -1092096992268, 4063327863170,
     -10344711794985, 19058185652796, -26204344465152, 27345870698436,
     -21847538039895, 13465774256510, -6616420957428, 3917551216986,
     703604254357] / 2615348736000.

This is an implicit method of order 13.
Reference: Iserles, Section 1.2 (k = 12 Adams–Moulton); coefficients
verified by exact `Fraction` arithmetic from the Lagrange-interpolation-and-
integrate construction on nodes 0,…,12 over `[11, 12]`; the numerators sum
to `2615348736000`. -/
noncomputable def adamsMoulton12 : LMM 12 where
  α := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1]
  β := ![-13695779093/2615348736000, 179842822566/2615348736000,
        -1092096992268/2615348736000, 4063327863170/2615348736000,
        -10344711794985/2615348736000, 19058185652796/2615348736000,
        -26204344465152/2615348736000, 27345870698436/2615348736000,
        -21847538039895/2615348736000, 13465774256510/2615348736000,
        -6616420957428/2615348736000, 3917551216986/2615348736000,
        703604254357/2615348736000]
  normalized := by simp [Fin.last]

/-! ## Consistency / explicitness / implicitness -/

/-- Adams–Bashforth 2-step is consistent. -/
theorem adamsBashforth2_consistent : adamsBashforth2.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth2, Fin.sum_univ_three],
   by simp [LMM.sigma, adamsBashforth2, Fin.sum_univ_three]; norm_num⟩

/-- Adams–Bashforth 2-step is explicit (β₂ = 0). -/
theorem adamsBashforth2_explicit : adamsBashforth2.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth2, Fin.last]

/-- Adams–Moulton 2-step is consistent. -/
theorem adamsMoulton2_consistent : adamsMoulton2.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton2, Fin.sum_univ_three],
   by simp [LMM.sigma, adamsMoulton2, Fin.sum_univ_three]; norm_num⟩

/-- Adams–Moulton 2-step is implicit (β₂ = 5/12 ≠ 0). -/
theorem adamsMoulton2_implicit : adamsMoulton2.IsImplicit := by
  simp [LMM.IsImplicit, adamsMoulton2, Fin.last]

/-- Adams–Bashforth 3-step is consistent. -/
theorem adamsBashforth3_consistent : adamsBashforth3.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth3, Fin.sum_univ_four],
   by simp [LMM.sigma, adamsBashforth3, Fin.sum_univ_four]; norm_num⟩

/-- Adams–Bashforth 3-step is explicit (β₃ = 0). -/
theorem adamsBashforth3_explicit : adamsBashforth3.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth3, Fin.last]

/-- Adams–Moulton 3-step is consistent. -/
theorem adamsMoulton3_consistent : adamsMoulton3.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton3, Fin.sum_univ_four],
   by simp [LMM.sigma, adamsMoulton3, Fin.sum_univ_four]; norm_num⟩

/-- Adams–Moulton 3-step is implicit (β₃ = 9/24 ≠ 0). -/
theorem adamsMoulton3_implicit : adamsMoulton3.IsImplicit := by
  simp [LMM.IsImplicit, adamsMoulton3, Fin.last]

/-- Adams–Bashforth 4-step is consistent. -/
theorem adamsBashforth4_consistent : adamsBashforth4.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth4, Fin.sum_univ_five],
   by simp [LMM.sigma, adamsBashforth4, Fin.sum_univ_five]; norm_num⟩

/-- Adams–Bashforth 4-step is explicit (β₄ = 0). -/
theorem adamsBashforth4_explicit : adamsBashforth4.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth4, Fin.last]

/-- Adams–Moulton 4-step is consistent. -/
theorem adamsMoulton4_consistent : adamsMoulton4.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton4, Fin.sum_univ_five],
   by simp [LMM.sigma, adamsMoulton4, Fin.sum_univ_five]; norm_num⟩

/-- Adams–Moulton 4-step is implicit (β₄ = 251/720 ≠ 0). -/
theorem adamsMoulton4_implicit : adamsMoulton4.β 4 ≠ 0 := by
  change (251 / 720 : ℝ) ≠ 0
  norm_num

/-- Adams–Bashforth 5-step is consistent. -/
theorem adamsBashforth5_consistent : adamsBashforth5.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth5, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsBashforth5, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Bashforth 5-step is explicit (β₅ = 0). -/
theorem adamsBashforth5_explicit : adamsBashforth5.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth5, Fin.last]

/-- Adams–Bashforth 6-step is consistent. -/
theorem adamsBashforth6_consistent : adamsBashforth6.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth6, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsBashforth6, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Bashforth 6-step is explicit (β₆ = 0). -/
theorem adamsBashforth6_explicit : adamsBashforth6.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth6, Fin.last]

/-- Adams–Bashforth 7-step is consistent. -/
theorem adamsBashforth7_consistent : adamsBashforth7.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth7, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsBashforth7, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Bashforth 7-step is explicit (β₇ = 0). -/
theorem adamsBashforth7_explicit : adamsBashforth7.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth7, Fin.last]

/-- Adams–Bashforth 8-step is consistent. -/
theorem adamsBashforth8_consistent : adamsBashforth8.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth8, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsBashforth8, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Bashforth 8-step is explicit (β₈ = 0). -/
theorem adamsBashforth8_explicit : adamsBashforth8.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth8, Fin.last]

/-- Adams–Bashforth 9-step is consistent. -/
theorem adamsBashforth9_consistent : adamsBashforth9.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth9, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsBashforth9, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Bashforth 9-step is explicit (β₉ = 0). -/
theorem adamsBashforth9_explicit : adamsBashforth9.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth9, Fin.last]

/-- Adams–Bashforth 10-step is consistent. -/
theorem adamsBashforth10_consistent : adamsBashforth10.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth10, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsBashforth10, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Bashforth 10-step is explicit (β₁₀ = 0). -/
theorem adamsBashforth10_explicit : adamsBashforth10.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth10, Fin.last]

/-- Adams–Bashforth 11-step is consistent. -/
theorem adamsBashforth11_consistent : adamsBashforth11.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth11, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsBashforth11, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Bashforth 11-step is explicit (β₁₁ = 0). -/
theorem adamsBashforth11_explicit : adamsBashforth11.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth11, Fin.last]

/-- Adams–Bashforth 12-step is consistent. -/
theorem adamsBashforth12_consistent : adamsBashforth12.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth12, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsBashforth12, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Bashforth 12-step is explicit (β₁₂ = 0). -/
theorem adamsBashforth12_explicit : adamsBashforth12.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth12, Fin.last]

/-- Adams–Bashforth 13-step is consistent. -/
theorem adamsBashforth13_consistent : adamsBashforth13.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth13, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsBashforth13, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Bashforth 13-step is explicit (β₁₃ = 0). -/
theorem adamsBashforth13_explicit : adamsBashforth13.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth13, Fin.last]

/-- Adams–Moulton 5-step is consistent. -/
theorem adamsMoulton5_consistent : adamsMoulton5.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton5, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsMoulton5, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Moulton 5-step is implicit (β₅ = 475/1440 ≠ 0). -/
theorem adamsMoulton5_implicit : adamsMoulton5.β 5 ≠ 0 := by
  change (475 / 1440 : ℝ) ≠ 0
  norm_num

/-- Adams–Moulton 6-step is consistent. -/
theorem adamsMoulton6_consistent : adamsMoulton6.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton6, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsMoulton6, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Moulton 6-step is implicit (β₆ = 19087/60480 ≠ 0). -/
theorem adamsMoulton6_implicit : adamsMoulton6.β 6 ≠ 0 := by
  change (19087 / 60480 : ℝ) ≠ 0
  norm_num

/-- Adams–Moulton 9-step is consistent. -/
theorem adamsMoulton9_consistent : adamsMoulton9.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton9, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsMoulton9, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Moulton 9-step is implicit (β₉ = 2082753/7257600 ≠ 0). -/
theorem adamsMoulton9_implicit : adamsMoulton9.IsImplicit := by
  simp [LMM.IsImplicit, adamsMoulton9, Fin.last]

/-- Adams–Moulton 10-step is consistent. -/
theorem adamsMoulton10_consistent : adamsMoulton10.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton10, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsMoulton10, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Moulton 10-step is implicit (β₁₀ = 134211265/479001600 ≠ 0). -/
theorem adamsMoulton10_implicit : adamsMoulton10.IsImplicit := by
  simp [LMM.IsImplicit, adamsMoulton10, Fin.last]

/-- Adams–Moulton 11-step is consistent. -/
theorem adamsMoulton11_consistent : adamsMoulton11.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton11, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsMoulton11, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Moulton 11-step is implicit (β₁₁ = 262747265/958003200 ≠ 0). -/
theorem adamsMoulton11_implicit : adamsMoulton11.IsImplicit := by
  simp [LMM.IsImplicit, adamsMoulton11, Fin.last]

/-- Adams–Moulton 12-step is consistent. -/
theorem adamsMoulton12_consistent : adamsMoulton12.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton12, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsMoulton12, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Moulton 12-step is implicit
(β₁₂ = 703604254357/2615348736000 ≠ 0). -/
theorem adamsMoulton12_implicit : adamsMoulton12.IsImplicit := by
  simp [LMM.IsImplicit, adamsMoulton12, Fin.last]

/-! ## Order theorems -/

/-- Adams–Bashforth 2-step has order 2. -/
theorem adamsBashforth2_order_two : adamsBashforth2.HasOrder 2 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;> simp [LMM.orderCondVal, adamsBashforth2, Fin.sum_univ_three] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth2, Fin.sum_univ_three]; norm_num

/-- Adams–Moulton 2-step has order 3. -/
theorem adamsMoulton2_order_three : adamsMoulton2.HasOrder 3 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton2, Fin.sum_univ_three] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton2, Fin.sum_univ_three]; norm_num

/-- Adams–Bashforth 3-step has order 3. -/
theorem adamsBashforth3_order_three : adamsBashforth3.HasOrder 3 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth3, Fin.sum_univ_four] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth3, Fin.sum_univ_four]; norm_num

/-- Adams–Moulton 3-step has order 4. -/
theorem adamsMoulton3_order_four : adamsMoulton3.HasOrder 4 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton3, Fin.sum_univ_four] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton3, Fin.sum_univ_four]; norm_num

/-- Adams–Bashforth 4-step has order 4. -/
theorem adamsBashforth4_order_four : adamsBashforth4.HasOrder 4 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth4, Fin.sum_univ_five] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth4, Fin.sum_univ_five]; norm_num

/-- Adams–Moulton 4-step has order 5. -/
theorem adamsMoulton4_order_five : adamsMoulton4.HasOrder 5 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton4, Fin.sum_univ_five] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton4, Fin.sum_univ_five]; norm_num

/-- Adams–Bashforth 5-step has order 5. -/
theorem adamsBashforth5_order_five : adamsBashforth5.HasOrder 5 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth5, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth5, Fin.sum_univ_succ]; norm_num

/-- Adams–Bashforth 6-step has order 6. -/
theorem adamsBashforth6_order_six : adamsBashforth6.HasOrder 6 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth6, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth6, Fin.sum_univ_succ]; norm_num

/-- Adams–Bashforth 7-step has order 7. -/
theorem adamsBashforth7_order_seven : adamsBashforth7.HasOrder 7 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth7, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth7, Fin.sum_univ_succ]; norm_num

/-- Adams–Bashforth 8-step has order 8. -/
theorem adamsBashforth8_order_eight : adamsBashforth8.HasOrder 8 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth8, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth8, Fin.sum_univ_succ]; norm_num

/-- Adams–Bashforth 9-step has order 9. -/
theorem adamsBashforth9_order_nine : adamsBashforth9.HasOrder 9 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth9, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth9, Fin.sum_univ_succ]; norm_num

/-- Adams–Bashforth 10-step has order 10. -/
theorem adamsBashforth10_order_ten : adamsBashforth10.HasOrder 10 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth10, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth10, Fin.sum_univ_succ]; norm_num

/-- Adams–Bashforth 11-step has order 11. -/
theorem adamsBashforth11_order_eleven : adamsBashforth11.HasOrder 11 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth11, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth11, Fin.sum_univ_succ]; norm_num

/-- Adams–Bashforth 12-step has order 12. -/
theorem adamsBashforth12_order_twelve : adamsBashforth12.HasOrder 12 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth12, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth12, Fin.sum_univ_succ]; norm_num

/-- Adams–Bashforth 13-step has order 13. -/
theorem adamsBashforth13_order_thirteen : adamsBashforth13.HasOrder 13 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth13, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth13, Fin.sum_univ_succ]; norm_num

/-- Adams–Moulton 5-step has order 6. -/
theorem adamsMoulton5_order_six : adamsMoulton5.HasOrder 6 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton5, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton5, Fin.sum_univ_succ]; norm_num

/-- Adams–Moulton 6-step has order 7. -/
theorem adamsMoulton6_order_seven : adamsMoulton6.HasOrder 7 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton6, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton6, Fin.sum_univ_succ]; norm_num

/-- Adams–Moulton 9-step has order 10. -/
theorem adamsMoulton9_order_ten : adamsMoulton9.HasOrder 10 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton9, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton9, Fin.sum_univ_succ]; norm_num

/-- Adams–Moulton 10-step has order 11. -/
theorem adamsMoulton10_order_eleven : adamsMoulton10.HasOrder 11 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton10, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton10, Fin.sum_univ_succ]; norm_num

/-- Adams–Moulton 11-step has order 12. -/
theorem adamsMoulton11_order_twelve : adamsMoulton11.HasOrder 12 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton11, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton11, Fin.sum_univ_succ]; norm_num

/-- Adams–Moulton 12-step has order 13. -/
theorem adamsMoulton12_order_thirteen : adamsMoulton12.HasOrder 13 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton12, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton12, Fin.sum_univ_succ]; norm_num

/-! ## Error constants

The leading error constant of an order-`p` LMM is
`C_{p+1} = orderCondVal (p+1) / (p+1)!`. The values below are the standard
Iserles §1.2 / §2.2 Adams error constants.
-/

/-- Adams–Bashforth 2-step has error constant `C_3 = 5/12`. -/
theorem adamsBashforth2_errorConstant :
    adamsBashforth2.errorConstant 2 = 5 / 12 := by
  unfold LMM.errorConstant LMM.orderCondVal adamsBashforth2
  simp [Fin.sum_univ_three, Nat.factorial]
  norm_num

/-- Adams–Moulton 2-step has error constant `C_4 = -1/24`. -/
theorem adamsMoulton2_errorConstant :
    adamsMoulton2.errorConstant 3 = -(1 / 24) := by
  unfold LMM.errorConstant LMM.orderCondVal adamsMoulton2
  simp [Fin.sum_univ_three, Nat.factorial]
  norm_num

/-- Adams–Bashforth 3-step has error constant `C_4 = 3/8`. -/
theorem adamsBashforth3_errorConstant :
    adamsBashforth3.errorConstant 3 = 3 / 8 := by
  unfold LMM.errorConstant LMM.orderCondVal adamsBashforth3
  simp [Fin.sum_univ_four, Nat.factorial]
  norm_num

/-- Adams–Moulton 3-step has error constant `C_5 = -19/720`. -/
theorem adamsMoulton3_errorConstant :
    adamsMoulton3.errorConstant 4 = -(19 / 720) := by
  unfold LMM.errorConstant LMM.orderCondVal adamsMoulton3
  simp [Fin.sum_univ_four, Nat.factorial]
  norm_num

/-- Adams–Bashforth 4-step has error constant `C_5 = 251/720`. -/
theorem adamsBashforth4_errorConstant :
    adamsBashforth4.errorConstant 4 = 251 / 720 := by
  unfold LMM.errorConstant LMM.orderCondVal adamsBashforth4
  simp [Fin.sum_univ_five, Nat.factorial]
  norm_num

/-- Adams–Moulton 4-step has error constant `C_6 = -3/160`. -/
theorem adamsMoulton4_errorConstant :
    adamsMoulton4.errorConstant 5 = -(3 / 160) := by
  unfold LMM.errorConstant LMM.orderCondVal adamsMoulton4
  simp [Fin.sum_univ_five, Nat.factorial]
  norm_num

/-- Adams–Bashforth 5-step has error constant `C_6 = 95/288`. -/
theorem adamsBashforth5_errorConstant :
    adamsBashforth5.errorConstant 5 = 95 / 288 := by
  unfold LMM.errorConstant LMM.orderCondVal adamsBashforth5
  simp [Fin.sum_univ_succ, Nat.factorial]
  norm_num

/-- Adams–Moulton 5-step has error constant `C_7 = -863/60480`. -/
theorem adamsMoulton5_errorConstant :
    adamsMoulton5.errorConstant 6 = -(863 / 60480) := by
  unfold LMM.errorConstant LMM.orderCondVal adamsMoulton5
  simp [Fin.sum_univ_succ, Nat.factorial]
  norm_num

/-- Adams–Bashforth 6-step has error constant `C_7 = 19087/60480`. -/
theorem adamsBashforth6_errorConstant :
    adamsBashforth6.errorConstant 6 = 19087 / 60480 := by
  unfold LMM.errorConstant LMM.orderCondVal adamsBashforth6
  simp [Fin.sum_univ_succ, Nat.factorial]
  norm_num

/-- Adams–Moulton 6-step has error constant `C_8 = -275/24192`. -/
theorem adamsMoulton6_errorConstant :
    adamsMoulton6.errorConstant 7 = -(275 / 24192) := by
  unfold LMM.errorConstant LMM.orderCondVal adamsMoulton6
  simp [Fin.sum_univ_succ, Nat.factorial]
  norm_num

/-- Adams–Bashforth error constants are strictly positive (AB2–AB6). -/
theorem adamsBashforth_errorConstant_pos :
    0 < adamsBashforth2.errorConstant 2 ∧
    0 < adamsBashforth3.errorConstant 3 ∧
    0 < adamsBashforth4.errorConstant 4 ∧
    0 < adamsBashforth5.errorConstant 5 ∧
    0 < adamsBashforth6.errorConstant 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [adamsBashforth2_errorConstant, adamsBashforth3_errorConstant,
      adamsBashforth4_errorConstant, adamsBashforth5_errorConstant,
      adamsBashforth6_errorConstant]

/-- Adams–Moulton error constants are strictly negative (AM2–AM6). -/
theorem adamsMoulton_errorConstant_neg :
    adamsMoulton2.errorConstant 3 < 0 ∧
    adamsMoulton3.errorConstant 4 < 0 ∧
    adamsMoulton4.errorConstant 5 < 0 ∧
    adamsMoulton5.errorConstant 6 < 0 ∧
    adamsMoulton6.errorConstant 7 < 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [adamsMoulton2_errorConstant, adamsMoulton3_errorConstant,
      adamsMoulton4_errorConstant, adamsMoulton5_errorConstant,
      adamsMoulton6_errorConstant]

/-! ## Zero-stability theorems -/

/-- Any LMM whose first characteristic polynomial has the Adams form
`ρ(ξ) = ξ^k(ξ - 1)`, with `k > 0` and a nonzero derivative at `1`, is zero-stable.

All Adams--Bashforth and Adams--Moulton methods in this file share this
characteristic polynomial shape; only the `β` coefficients differ. -/
theorem adams_zeroStable_of_rhoC_pow_mul {s k : ℕ} (m : LMM s) (hk : 0 < k)
    (hrho : ∀ ξ : ℂ, m.rhoC ξ = ξ ^ k * (ξ - 1))
    (hderiv_one : m.rhoCDeriv 1 ≠ 0) :
    m.IsZeroStable := by
  refine ⟨?_, ?_⟩
  · intro ξ hξ
    have hroot : ξ ^ k * (ξ - 1) = 0 := by
      simpa [hrho ξ] using hξ
    rcases mul_eq_zero.mp hroot with hpow | hsub
    · have hξ0 : ξ = 0 := by
        exact (pow_eq_zero_iff (n := k) (a := ξ) (Nat.ne_of_gt hk)).mp hpow
      rw [hξ0]
      simp
    · have hξ1 : ξ = 1 := sub_eq_zero.mp hsub
      rw [hξ1]
      simp
  · intro ξ hξ habs
    have hroot : ξ ^ k * (ξ - 1) = 0 := by
      simpa [hrho ξ] using hξ
    rcases mul_eq_zero.mp hroot with hpow | hsub
    · have hξ0 : ξ = 0 := by
        exact (pow_eq_zero_iff (n := k) (a := ξ) (Nat.ne_of_gt hk)).mp hpow
      rw [hξ0] at habs
      simp at habs
    · have hξ1 : ξ = 1 := sub_eq_zero.mp hsub
      rw [hξ1]
      exact hderiv_one

/-- Adams–Bashforth 2-step is zero-stable: ρ(ξ) = ξ² - ξ has roots 0 and 1,
both in the closed unit disk, and the unit root ξ = 1 is simple (ρ'(1) = 1 ≠ 0). -/
theorem adamsBashforth2_zeroStable : adamsBashforth2.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsBashforth2 (by norm_num : 0 < 1)
    (by
      intro ξ
      simp [LMM.rhoC, adamsBashforth2, Fin.sum_univ_three]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsBashforth2, Fin.sum_univ_three]
      norm_num)

/-- Adams–Moulton 2-step is zero-stable: ρ(ξ) = ξ² - ξ has roots 0 and 1
(same as Adams–Bashforth 2-step). -/
theorem adamsMoulton2_zeroStable : adamsMoulton2.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsMoulton2 (by norm_num : 0 < 1)
    (by
      intro ξ
      simp [LMM.rhoC, adamsMoulton2, Fin.sum_univ_three]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsMoulton2, Fin.sum_univ_three]
      norm_num)

/-- Adams–Bashforth 3-step is zero-stable: ρ(ξ) = ξ³ - ξ² = ξ²(ξ - 1) has a double
root at 0 (interior to the unit disk) and a simple root at 1 (on the unit circle,
with ρ'(1) = 1 ≠ 0). -/
theorem adamsBashforth3_zeroStable : adamsBashforth3.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsBashforth3 (by norm_num : 0 < 2)
    (by
      intro ξ
      simp [LMM.rhoC, adamsBashforth3, Fin.sum_univ_four]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsBashforth3, Fin.sum_univ_four]
      norm_num)

/-- Adams–Moulton 3-step is zero-stable: it has the same first characteristic
polynomial as Adams–Bashforth 3-step. -/
theorem adamsMoulton3_zeroStable : adamsMoulton3.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsMoulton3 (by norm_num : 0 < 2)
    (by
      intro ξ
      simp [LMM.rhoC, adamsMoulton3, Fin.sum_univ_four]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsMoulton3, Fin.sum_univ_four]
      norm_num)

/-- Adams–Bashforth 4-step is zero-stable: ρ(ξ) = ξ⁴ - ξ³ = ξ³(ξ - 1) has a triple
root at 0 (interior to the unit disk) and a simple root at 1 (on the unit circle,
with ρ'(1) = 1 ≠ 0). -/
theorem adamsBashforth4_zeroStable : adamsBashforth4.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsBashforth4 (by norm_num : 0 < 3)
    (by
      intro ξ
      simp [LMM.rhoC, adamsBashforth4, Fin.sum_univ_five]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsBashforth4, Fin.sum_univ_five]
      norm_num)

/-- Adams–Moulton 4-step is zero-stable: ρ(ξ) = ξ⁴ - ξ³ = ξ³(ξ - 1) has a triple
root at 0 (interior to the unit disk) and a simple root at 1 (on the unit circle,
with ρ'(1) = 1 ≠ 0). -/
theorem adamsMoulton4_zeroStable : adamsMoulton4.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsMoulton4 (by norm_num : 0 < 3)
    (by
      intro ξ
      simp [LMM.rhoC, adamsMoulton4, Fin.sum_univ_five]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsMoulton4, Fin.sum_univ_five]
      norm_num)

/-- Adams–Bashforth 5-step is zero-stable: ρ(ξ) = ξ⁵ - ξ⁴ = ξ⁴(ξ - 1) has a quadruple
root at 0 (interior to the unit disk) and a simple root at 1 (on the unit circle,
with ρ'(1) = 1 ≠ 0). -/
theorem adamsBashforth5_zeroStable : adamsBashforth5.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsBashforth5 (by norm_num : 0 < 4)
    (by
      intro ξ
      simp [LMM.rhoC, adamsBashforth5, Fin.sum_univ_succ]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsBashforth5, Fin.sum_univ_succ]
      norm_num)

/-- Adams–Bashforth 6-step is zero-stable: ρ(ξ) = ξ⁶ - ξ⁵ = ξ⁵(ξ - 1) has a
quintuple root at 0 (interior to the unit disk) and a simple root at 1 (on the
unit circle, with ρ'(1) = 1 ≠ 0). -/
theorem adamsBashforth6_zeroStable : adamsBashforth6.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsBashforth6 (by norm_num : 0 < 5)
    (by
      intro ξ
      simp [LMM.rhoC, adamsBashforth6, Fin.sum_univ_succ]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsBashforth6, Fin.sum_univ_succ]
      norm_num)

/-- Adams–Moulton 5-step is zero-stable: ρ(ξ) = ξ⁵ - ξ⁴ = ξ⁴(ξ - 1) has a quadruple
root at 0 (interior to the unit disk) and a simple root at 1 (on the unit circle,
with ρ'(1) = 1 ≠ 0). Same ρ as Adams–Bashforth 5-step. -/
theorem adamsMoulton5_zeroStable : adamsMoulton5.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsMoulton5 (by norm_num : 0 < 4)
    (by
      intro ξ
      simp [LMM.rhoC, adamsMoulton5, Fin.sum_univ_succ]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsMoulton5, Fin.sum_univ_succ]
      norm_num)

/-- Adams–Moulton 6-step is zero-stable: ρ(ξ) = ξ⁶ - ξ⁵ = ξ⁵(ξ - 1) has a
quintuple root at 0 (interior to the unit disk) and a simple root at 1 (on the
unit circle, with ρ'(1) = 1 ≠ 0). Same ρ as Adams–Bashforth 6-step. -/
theorem adamsMoulton6_zeroStable : adamsMoulton6.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsMoulton6 (by norm_num : 0 < 5)
    (by
      intro ξ
      simp [LMM.rhoC, adamsMoulton6, Fin.sum_univ_succ]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsMoulton6, Fin.sum_univ_succ]
      norm_num)

/-- Adams–Bashforth 8-step is zero-stable: ρ(ξ) = ξ⁸ - ξ⁷ = ξ⁷(ξ - 1). -/
theorem adamsBashforth8_zeroStable : adamsBashforth8.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsBashforth8 (by norm_num : 0 < 7)
    (by
      intro ξ
      simp [LMM.rhoC, adamsBashforth8, Fin.sum_univ_succ]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsBashforth8, Fin.sum_univ_succ]
      norm_num)

/-- Adams–Bashforth 9-step is zero-stable: ρ(ξ) = ξ⁹ - ξ⁸ = ξ⁸(ξ - 1). -/
theorem adamsBashforth9_zeroStable : adamsBashforth9.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsBashforth9 (by norm_num : 0 < 8)
    (by
      intro ξ
      simp [LMM.rhoC, adamsBashforth9, Fin.sum_univ_succ]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsBashforth9, Fin.sum_univ_succ]
      norm_num)

/-- Adams–Bashforth 10-step is zero-stable: ρ(ξ) = ξ¹⁰ - ξ⁹ = ξ⁹(ξ - 1). -/
theorem adamsBashforth10_zeroStable : adamsBashforth10.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsBashforth10 (by norm_num : 0 < 9)
    (by
      intro ξ
      simp [LMM.rhoC, adamsBashforth10, Fin.sum_univ_succ]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsBashforth10, Fin.sum_univ_succ]
      norm_num)

/-- Adams–Bashforth 11-step is zero-stable: ρ(ξ) = ξ¹¹ - ξ¹⁰ = ξ¹⁰(ξ - 1). -/
theorem adamsBashforth11_zeroStable : adamsBashforth11.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsBashforth11 (by norm_num : 0 < 10)
    (by
      intro ξ
      simp [LMM.rhoC, adamsBashforth11, Fin.sum_univ_succ]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsBashforth11, Fin.sum_univ_succ]
      norm_num)

/-- Adams–Bashforth 12-step is zero-stable: ρ(ξ) = ξ¹² - ξ¹¹ = ξ¹¹(ξ - 1). -/
theorem adamsBashforth12_zeroStable : adamsBashforth12.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsBashforth12 (by norm_num : 0 < 11)
    (by
      intro ξ
      simp [LMM.rhoC, adamsBashforth12, Fin.sum_univ_succ]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsBashforth12, Fin.sum_univ_succ]
      norm_num)

/-- Adams–Bashforth 13-step is zero-stable: ρ(ξ) = ξ¹³ - ξ¹² = ξ¹²(ξ - 1). -/
theorem adamsBashforth13_zeroStable : adamsBashforth13.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsBashforth13 (by norm_num : 0 < 12)
    (by
      intro ξ
      simp [LMM.rhoC, adamsBashforth13, Fin.sum_univ_succ]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsBashforth13, Fin.sum_univ_succ]
      norm_num)

/-- Adams–Moulton 9-step is zero-stable: ρ(ξ) = ξ⁹ - ξ⁸ = ξ⁸(ξ - 1). -/
theorem adamsMoulton9_zeroStable : adamsMoulton9.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsMoulton9 (by norm_num : 0 < 8)
    (by
      intro ξ
      simp [LMM.rhoC, adamsMoulton9, Fin.sum_univ_succ]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsMoulton9, Fin.sum_univ_succ]
      norm_num)

/-- Adams–Moulton 10-step is zero-stable: ρ(ξ) = ξ¹⁰ - ξ⁹ = ξ⁹(ξ - 1). -/
theorem adamsMoulton10_zeroStable : adamsMoulton10.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsMoulton10 (by norm_num : 0 < 9)
    (by
      intro ξ
      simp [LMM.rhoC, adamsMoulton10, Fin.sum_univ_succ]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsMoulton10, Fin.sum_univ_succ]
      norm_num)

/-- Adams–Moulton 11-step is zero-stable: ρ(ξ) = ξ¹¹ - ξ¹⁰ = ξ¹⁰(ξ - 1). -/
theorem adamsMoulton11_zeroStable : adamsMoulton11.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsMoulton11 (by norm_num : 0 < 10)
    (by
      intro ξ
      simp [LMM.rhoC, adamsMoulton11, Fin.sum_univ_succ]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsMoulton11, Fin.sum_univ_succ]
      norm_num)

/-- Adams–Moulton 12-step is zero-stable: ρ(ξ) = ξ¹² - ξ¹¹ = ξ¹¹(ξ - 1). -/
theorem adamsMoulton12_zeroStable : adamsMoulton12.IsZeroStable :=
  adams_zeroStable_of_rhoC_pow_mul adamsMoulton12 (by norm_num : 0 < 11)
    (by
      intro ξ
      simp [LMM.rhoC, adamsMoulton12, Fin.sum_univ_succ]
      ring)
    (by
      simp [LMM.rhoCDeriv, adamsMoulton12, Fin.sum_univ_succ]
      norm_num)
