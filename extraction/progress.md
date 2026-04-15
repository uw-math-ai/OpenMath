# Extraction Pipeline Progress Report

**Project**: Formalizing Butcher's "Numerical Methods for Ordinary Differential Equations" (2nd ed., 2008) in Lean 4
**Date**: 2026-04-13
**Textbook**: 484 pages, 5 chapters, LaTeX-typeset PDF

---

## Pipeline Overview

A 9-phase Python pipeline extracts formal statements from the PDF, converts
them to LaTeX, builds a dependency graph, and generates a LeanBlueprint for
formalization tracking.

```
PDF ──→ pdftotext/pdftohtml ──→ per-chapter text + formatting.json
    ──→ formal statement extraction (175 statements)
    ──→ equation extraction (619 equations)
    ──→ reference extraction (regex + concept + equation + LLM)
    ──→ dependency graph (JSON + DOT + HTML)
    ──→ DeepSeek LaTeX conversion (all 175)
    ──→ LeanBlueprint (5 chapters, interactive dep graph)
```

### Scripts (`extraction/pipeline/`)

| Script | Phase | Purpose |
|--------|-------|---------|
| `extract_text.py` | 1a | `pdftotext` → full text → 5 chapter files |
| `extract_html.py` | 1b | `pdftohtml` → bold/italic detection → `formatting.json` |
| `extract_formal.py` | 2 | Entity extraction: 175 statements + 106 proofs |
| `extract_equations.py` | 3 | 619 equations, 197 key (referenced 3+ times) |
| `extract_references.py` | 4a | Regex + concept name + equation linking |
| `extract_references_llm.py` | 4a+ | DeepSeek-assisted dependency discovery |
| `build_graph.py` | 4b | Dependency graph (JSON + DOT + interactive HTML) |
| `generate_markdown.py` | 5 | Per-chapter markdown knowledge base |
| `convert_to_latex.py` | 6 | DeepSeek LaTeX conversion (CLI with --resume) |
| `verify.py` | 7 | Automated consistency checks |
| `generate_blueprint.py` | 8 | LeanBlueprint generation (--no-llm, --only-explicit flags) |
| `run_pipeline.py` | - | Master orchestrator (phases 1-7) |

---

## Entities Extracted

| Kind | Count | With Proofs |
|------|-------|-------------|
| Theorems | 104 | 84 |
| Definitions | 45 | 0 |
| Lemmas | 22 | 20 |
| Corollaries | 4 | 2 |
| **Total** | **175** | **106** |

### How Entities Are Detected

1. **Bold declarations as ground truth**: `pdftohtml` finds all `<b>Theorem NNN[A-Z]</b>` tags. This gives us the definitive list of 175 (kind, number) pairs.

2. **Text scanning**: `extract_formal.py` scans pdftotext output line by line. When a line matches `^Theorem\s+(\d{3}[A-Z])`, it checks if that number is in the bold set. If yes → extract as declaration. If no → skip as back-reference.

3. **Statement body boundary**: Collects lines from the header until a **terminator**:
   - Another formal header (Theorem/Definition/Lemma/Corollary/Proof)
   - A structural boundary (section `\d{2}\s{2,}`, subsection `\d{3}\s{2,}`, or `Exercises \d{2}`)
   - Running page headers are detected and **skipped** (not treated as terminators)

4. **Proof association**: Proofs are linked to their preceding theorem/lemma by position, then merged into the parent's `proof_text` field.

### Numbering Scheme

Butcher uses an unusual scheme: 3-digit subsection number + uppercase letter.
- Theorems: `Theorem 101A`, `Theorem 212A`, `Theorem 342C`
- Definitions: `Definition 110A`, `Definition 350A`
- Equations: `(100a)`, `(210b)`, `(342j)`
- Sections: 2-digit (`10`, `21`, `35`)
- Subsections: 3-digit (`100`, `213`, `350`)

---

## Reference Extraction

### Method 1: Explicit Regex (26 edges)
Scans statement+proof text for `(Theorem|Definition|Lemma|Corollary)\s+(\d{3}[A-Z])`.
Only creates edge if target exists in the 175 known statements. High precision.

### Method 2: Concept Name Matching (81 edges)
1. Extracts quoted terms from definitions (e.g., `'Lipschitz condition'`, `'A-stable'`)
2. Word-boundary matches these terms in other statements' text
3. Filters generic single-word terms (`stable`, `convergent`, `consistent`)
4. Removes shorter substrings of longer kept terms

### Method 3: Equation-to-Statement Linking (19 edges)
Maps each equation `(NNNx)` to its "owning" statement (same subsection, definitions prioritized).
When statement A references equation owned by statement B → edge A→B.

### Method 4: LLM-Assisted (250 edges)
Sends each statement + full entity list to DeepSeek. Asks it to identify conceptual dependencies.
Cycles detected and broken by removing back-edges (page-order heuristic).

### Total: 395 edges (371 formal-to-formal after dedup, 19 section refs)

Blueprint supports filtering via flags:
```
python -m pipeline.generate_blueprint              # All 371 edges
python -m pipeline.generate_blueprint --no-llm     # 121 edges (no LLM)
python -m pipeline.generate_blueprint --no-concept  # No concept matches
python -m pipeline.generate_blueprint --only-explicit # 26 edges (regex only)
```

---

## LaTeX Conversion

### Process
- Tool: DeepSeek API (`deepseek-chat`), ~$0.11 for all 175 statements
- Each statement's raw pdftotext sent with a conversion prompt
- CLI: `python -m pipeline.convert_to_latex --run-api --resume`
- All 175 converted, 0 errors

### Post-Processing (in `generate_blueprint.py`)
1. Strip content after `\end{kind}` / `\end{proof}` (removes appended context)
2. Remove banned environments (tikzpicture, figure, tabular, algorithm, verbatim)
3. Strip `\hline`, `\cline`, `|` in array column specs
4. Convert `\begin{tabular}` → `\begin{array}`
5. Add `[title]` to `\begin{theorem}` if missing
6. Warn if >5000 chars (no truncation — fix by reconverting)

### Conversion Guide
See `extraction/latex_conversion_guide.md` for the full list of plasTeX
constraints and prompt templates for future conversions.

---

## LeanBlueprint

### Structure
```
OpenMath/blueprint/
├── build.py              # Build wrapper (sets recursion limit)
├── src/
│   ├── web.tex           # plasTeX preamble with blueprint package
│   ├── print.tex         # xelatex preamble
│   ├── content.tex       # \input{chapter1}...\input{chapter5}
│   ├── plastex.cfg       # plasTeX config (split-level=0, no imager)
│   ├── chapter1-5.tex    # Generated LaTeX with \label, \lean, \uses, \proves
│   └── macros/
│       ├── common.tex    # \newtheorem definitions + math macros
│       └── web.tex       # Web-specific macros
```

### Building
```bash
python -m pipeline.generate_blueprint     # Generate blueprint/src/*.tex
python blueprint/build.py                 # Build HTML (needs pdflatex)
leanblueprint serve                       # Serve at localhost:8000
```

### What Each Statement Gets
```latex
\begin{theorem}[212A]
  \label{thm:212A}
  \lean{Butcher.Ch2.Thm212A}       % Placeholder Lean name
  \uses{thm:110C, def:110A}        % Dependencies
  ... LaTeX body ...
\end{theorem}

\begin{proof}
  \proves{thm:212A}
  \uses{thm:110C, def:110A}
  ... proof body ...
\end{proof}
```

### Repo
Blueprint source pushed to `uw-math-ai/OpenMath` (commit `2689fb4`).

---

## Remaining Problems

### P1: Proof Truncation (57/106 proofs) — HIGH
**Root cause**: pdftotext inserts page numbers (bare 3-digit numbers like `165`) at page boundaries. These match the subsection header pattern `^\d{3}\s*$`, causing `_is_terminator` to end proof collection prematurely.

**Impact**: 57 proofs may be incomplete. The LaTeX conversion of those proofs is also affected.

**Fix**: Validate that a bare 3-digit number is in the `_VALID_SUBSECTIONS` set AND belongs to the current chapter before treating it as a terminator. This check exists for `SUBSECTION_HEADER_RE` but not for `SUBSECTION_BARE_RE` in all code paths.

### P2: Section Assignment (86 mismatches) — MEDIUM
**Root cause**: Same as P1 — page numbers misidentified as subsections cause the section tracker to jump. For example, 27 ch5 statements are assigned to section `51` instead of sections `52`-`55`.

**Impact**: `formal_statements.json` has wrong section fields. The blueprint generator works around this by deriving sections from statement numbers (`int(number[:3]) // 10`).

**Fix**: Same as P1. Fixing subsection detection also fixes section tracking.

### P3: LLM Reference Quality (250 edges) — MEDIUM
**Root cause**: DeepSeek identifies conceptual dependencies without ground truth validation. Unknown precision/recall.

**Impact**: Dependency graph may have false edges.

**Status**: Currently included by default, removable via `--no-llm`. User does not fully trust these.

### P4: Concept Matching Ambiguity — LOW
**Root cause**: Terms like `stability function` have 2 definitions (520C, 542A). The matcher links to both without disambiguation.

**Impact**: Some edges may point to the wrong definition.

**Fix**: Use chapter proximity as tiebreaker — prefer the definition in the same or preceding chapter.

### P5: Missing Equation Labels in Blueprint — LOW
**Root cause**: DeepSeek generates `\eqref{eq:100a}` but no `\label{eq:100a}` is defined.

**Impact**: 28 "Label could not be resolved" warnings in plasTeX. Broken equation cross-links in HTML.

**Fix**: Strip `\eqref{}` calls in the sanitizer, or generate dummy equation labels.

### P6: 1 Oversized Statement (>5000 chars) — LOW
One theorem exceeds 5000 chars. Needs reconversion with a concise prompt. No truncation fallback (removed because truncation corrupts plasTeX state).
