# Final Verification Report

## Summary

| Metric | Value | Status |
|--------|-------|--------|
| Total formal statements | 175 | OK |
| Theorems | 104 | OK |
| Definitions | 45 | OK |
| Lemmas | 22 | OK |
| Corollaries | 4 | OK |
| Statements with proofs | 106/175 | See below |
| LaTeX conversions | 175/175, 0 errors | OK |
| Unique equations | 619 (197 key) | OK |
| Cross-reference edges | 270 | OK |
| Page numbers present | 175/175 | OK |
| Page order (per chapter) | All monotonic | OK |

## Issue 1: Proof Truncation (MEDIUM)

**68 of 106 proofs may be truncated.** Root causes:

1. **Running page headers in text** (5 cases): pdftotext includes running
   headers like `RUNGE–KUTTA METHODS    165` in the middle of proofs.
   These break proof extraction at page boundaries.

2. **Trailing whitespace artifacts** (many cases): pdftotext adds
   significant trailing whitespace to lines. Proofs that actually
   end with `.` or equation displays appear incomplete due to
   whitespace padding. Many of these are false positives.

3. **Page boundary splits** (~30 cases): When a proof spans a page
   boundary, pdftotext inserts headers/footers that the extractor
   treats as structural boundaries, causing premature termination.

**Impact on formalization**: The theorem STATEMENTS are complete. The
proofs serve as context for understanding the theorem but are not
directly formalized in Lean 4. The original PDF should be referenced
for any proof that appears truncated.

**Recommended fix**: Update `extract_formal.py` to:
- Filter running headers from proof text before boundary detection
- Ignore bare page numbers (3-digit numbers matching page numbers)
  that appear at page boundaries

### Theorems without proofs (20)

These theorems have no proof extracted. Some are genuinely stated
without proof in the textbook (e.g., results from other references),
others may be extraction misses:

| Theorem | Page | Likely reason |
|---------|------|--------------|
| 111A | 45 | Superposition principle — stated without formal proof |
| 123B | 57 | Invariance result — brief, no proof given |
| 212A | 89 | Global error bound — proof is in preceding text (sec 212) |
| 213B | 89 | Uniform convergence — follows from 213A |
| 243A | 130 | Convergence iff consistency+stability — proof deferred to Ch4 |
| 304A | 167 | Generating function — combinatorial, stated without proof |
| 311C | 175 | Order of truncation error — derivation precedes statement |
| 314A | 182 | Independence — proof omitted |
| 343A | 242 | Reflected methods — stated without proof |
| 352D | 259 | Padé property — stated without proof |
| 352E | 259 | Padé property — stated without proof |
| 357D | 273 | Non-linear stability — reference to literature |
| 388E | 322 | Algebraic — proof embedded in statement text |
| 388G | 322 | Algebraic — stated without proof |
| 410B | 351 | Order barrier — derivation precedes statement |
| 410C | 351 | Order barrier — proof embedded in statement text |
| 410D | 351 | Order barrier — stated without proof |
| 515D | 417 | Convergence theorem — proof is in preceding subsections |
| 520D | 419 | Stability — stated without proof |
| 523B | 428 | Spectral radius — stated without proof |

## Issue 2: Subsection Tracking (MINOR)

**1 statement has incorrect subsection assignment:**

- Theorem 388H: `subsection=302` but should be `388`
  - Cause: Section tracking in `extract_formal.py` lost sync when
    a bare 3-digit number in the text was misidentified as a
    subsection header
  - Chapter (3) and page (323) are correct
  - Does not affect LaTeX output or dependency graph

## Issue 3: Statement Completeness (OK)

**1 very short statement:** Theorem 123A (34 chars: "H(y(x)) is invariant.")
- Verified against PDF page 35: This IS the complete theorem statement.
  The theorem is intentionally brief.

All other statements have reasonable length for their content.

## LaTeX Quality Assessment

Verified 10 diverse statements using DeepSeek:

| Statement | Verdict | Notes |
|-----------|---------|-------|
| Theorem 212A | OK | Faithful conversion, cases correct |
| Definition 310A | OK | Elementary differentials properly formatted |
| Theorem 342C | OK | Simplifying assumptions, proof truncated but LaTeX matches |
| Lemma 312B | OK | Index notation correct |
| Definition 510A | OK | Preconsistency definition proper |
| Theorem 515D | OK | One-sentence theorem |
| Corollary 550C | OK | Matrix notation correct |
| Theorem 388H | OK | Group theory notation preserved |
| Definition 350A | OK | A-stability definition complete |
| Theorem 101A | OK | Hamiltonian/angular momentum, proof complete |

**Key finding from DeepSeek review**: The LaTeX conversion faithfully
represents the original extracted text. It does NOT add or fabricate
content beyond what was extracted.

## Chapter Coverage

| Chapter | Statements | Pages | Coverage |
|---------|-----------|-------|----------|
| 1 (Diff/Diff Eqs) | 17 | 26-69 | OK |
| 2 (Numerical Methods) | 4 | 89-130 | Low — Ch2 is introductory |
| 3 (Runge-Kutta) | 92 | 161-323 | OK — largest chapter |
| 4 (Linear Multistep) | 27 | 340-387 | OK |
| 5 (General Linear) | 35 | 406-463 | OK |

Chapter 2 has only 4 formal statements because it is an introductory
survey chapter. Most content is expository rather than formal.

## Recommendations

1. **For immediate use**: The extraction is usable for Lean 4
   formalization planning. Use the LaTeX output for theorem/definition
   statements. Reference the original PDF for proofs.

2. **Proof extraction improvement**: Update the terminator logic to
   skip running headers and page-boundary artifacts. This would
   recover ~30 truncated proofs.

3. **Manual review**: Spot-check 5-10 statements from each chapter
   against the PDF to catch any remaining issues.
