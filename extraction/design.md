# Math Entity Extraction Pipeline — Design & Reproduction Guide

Complete design document for extracting formal statements (theorems,
definitions, lemmas, corollaries) from a mathematical PDF textbook and
generating a LeanBlueprint project with per-entity context, named nodes,
and a dependency graph.

**Reference implementation**: Butcher's *Numerical Methods for Ordinary
Differential Equations* (2nd ed., 2008, 484 pages).

---

## Part 1: Goals & Deliverables

### Goals
1. Extract every formal statement (theorem/definition/lemma/corollary) from a PDF
2. Convert each statement's body and proof to clean LaTeX
3. Identify dependencies between statements (cross-references)
4. Extract missing context (variables, equations, preamble) needed to understand each statement
5. Generate descriptive informal names for all statements
6. Build a LeanBlueprint that renders as HTML with interactive dependency graph

### Deliverables (produced by the pipeline)
- `raw_text/formal_statements.json` — 175 statements with metadata (number, chapter, section, subsection, page, text, proof_text, introduces)
- `raw_text/formal_statements_latex.json` — each statement in proper LaTeX
- `raw_text/statement_names.json` — short descriptive name per statement
- `raw_text/statement_context.json` — external variables/equations/preamble
- `raw_text/context_latex.json` — context rendered as LaTeX
- `raw_text/references_merged.json` — cross-reference edges (cycle-free)
- `raw_text/cycles_removed.json` — audit log of broken cycles
- `blueprint/src/*.tex` — LeanBlueprint LaTeX source (one file per chapter)
- `blueprint/web/` — built HTML with interactive dep graph
- `knowledge_base/*.md` — per-chapter markdown knowledge base

---

## Part 2: Prerequisites

### System tools (install via Homebrew)
```bash
brew install graphviz           # for pygraphviz
brew install --cask basictex    # for pdflatex (used by plasTeX imager)
# After basictex install, add to PATH:
eval "$(/usr/libexec/path_helper)"  # or use /usr/local/texlive/2026basic/bin/universal-darwin
```

Poppler tools `pdftotext` and `pdftohtml` should already be on macOS
(check at `/opt/homebrew/bin/pdftotext` and `pdftohtml`).

### Python packages
```bash
pip install openai python-dotenv pygraphviz leanblueprint
```

Python 3.11+ required.

### API keys
Place in `extraction/.env`:
```
DEEPSEEK_API_KEY=sk-xxxxxxxxx
```
DeepSeek API is OpenAI-compatible; uses `deepseek-chat` model.
Total pipeline cost: **~$0.35** for 175 statements.

### Lean project
The blueprint needs to live under a Lean 4 project root (so `leanblueprint`
can find `lakefile.toml`). In this repo, the blueprint lives at
`OpenMath/blueprint/` and the Lean project is at `OpenMath/`.

---

## Part 3: Project Structure

```
OpenMath/                            # Lean 4 project root
├── lakefile.toml                    # Lean project config
├── lean-toolchain                   # Lean version
├── extraction/                      # This pipeline
│   ├── .env                         # DeepSeek API key
│   ├── Butcher_J_*.pdf              # Input PDF
│   ├── design.md                    # THIS FILE
│   ├── deepseek_prompts.md          # All LLM prompts documented
│   ├── latex_conversion_guide.md    # plasTeX constraints for LaTeX
│   ├── concept_matching_audit.md    # Concept alias rules
│   ├── pipeline/                    # 16 Python modules
│   │   ├── config.py                # Paths, regex patterns, subsection titles
│   │   ├── extract_text.py          # Phase 1a
│   │   ├── extract_html.py          # Phase 1b
│   │   ├── extract_formal.py        # Phase 2
│   │   ├── extract_equations.py     # Phase 3a
│   │   ├── extract_context.py       # Phase 3b (equation context + DeepSeek)
│   │   ├── fix_introduces.py        # Phase 2b (LaTeX + DeepSeek concepts)
│   │   ├── extract_names.py         # Phase 2c (3-tier naming)
│   │   ├── extract_references.py    # Phase 4a (regex + concept + equation)
│   │   ├── extract_references_llm.py # Phase 4a+ (DeepSeek deps)
│   │   ├── break_cycles.py          # Phase 4c
│   │   ├── build_graph.py           # Phase 4b (JSON/DOT/HTML graph)
│   │   ├── convert_to_latex.py      # Phase 6 (statement bodies)
│   │   ├── convert_context_to_latex.py # Phase 6b (context blocks)
│   │   ├── generate_markdown.py     # Phase 5
│   │   ├── generate_blueprint.py    # Phase 8 (LeanBlueprint source)
│   │   ├── verify.py                # Phase 7
│   │   └── run_pipeline.py          # Orchestrator for phases 1-7
│   ├── raw_text/                    # All intermediate JSON artifacts
│   ├── knowledge_base/              # Per-chapter markdown
│   └── graph/                       # Graph JSON/DOT/HTML
└── blueprint/                       # LeanBlueprint project
    ├── build.py                     # Wrapper (increases recursion limit,
    │                                #  runs plasTeX, post-processes graph labels)
    └── src/                         # Generated LaTeX source
        ├── web.tex                  # plasTeX entry point
        ├── print.tex                # xelatex entry point
        ├── content.tex              # \input{chapter1}...\input{chapter5}
        ├── chapter1.tex ... chapter5.tex
        ├── plastex.cfg              # plasTeX config
        ├── extra_styles.css         # (empty, required placeholder)
        └── macros/
            ├── common.tex           # theorem environments + math macros
            └── web.tex               # web-only macros
```

---

## Part 4: Pipeline Phases (in order)

### Phase 1a: Text Extraction (`extract_text.py`)
**Purpose**: PDF → plain text → per-chapter files.

- Runs `pdftotext -layout` on the PDF
- Splits at `Chapter N` markers into `ch01.txt`–`ch05.txt`
- Normalizes Unicode ligatures (ff, fi, fl)
- **Outputs**: `raw_text/full_text.txt`, `ch01.txt`–`ch05.txt`

**Run**: `python -m pipeline.extract_text`

### Phase 1b: HTML Formatting (`extract_html.py`)
**Purpose**: Extract bold declarations and italic text for reliable parsing.

- Runs `pdftohtml -stdout -i -noframes` on the PDF
- Finds `<b>Theorem NNN[A-Z]</b>`-style headers (ground truth for 175 entities)
- Extracts italic statement bodies
- **Outputs**: `raw_text/html_full.html`, `raw_text/formatting.json`

**Run**: `python -m pipeline.extract_html`

### Phase 2: Formal Statement Extraction (`extract_formal.py`)
**Purpose**: Extract statements + proofs from chapter text.

- Uses bold declarations from `formatting.json` as ground truth
- Scans pdftotext chapter files for headers matching `Theorem NNN[A-Z]`, etc.
- Collects body until a terminator (next formal header, section boundary)
- **Proof termination uses the QED box** (`\x01` character in pdftotext output)
- Filters running page headers out of collected text
- Populates `introduces` field from quoted terms (`'term'`)
- **Outputs**: `raw_text/formal_statements.json` (175 entries)

**Schema** (per entity):
```json
{
  "kind": "theorem|definition|lemma|corollary",
  "number": "212A",
  "chapter": 2, "section": "21", "subsection": "212", "page": 89,
  "text": "Theorem 212A Assuming that f satisfies...",
  "proof_text": "Proof. We have...",
  "line_start": 3821, "line_end": 3830,
  "introduces": ["concept name 1", ...]
}
```

**Run**: `python -m pipeline.extract_formal`

**Key regex patterns** (in `config.py`):
- Theorem: `^Theorem\s+(\d{3}[A-Z])`
- Definition: `^De(?:fi|ﬁ)nition\s+(\d{3}[A-Z])`
- Lemma: `^Lemma\s+(\d{3}[A-Z])`
- Corollary: `^Corollary\s+(\d{3}[A-Z])?`
- Equation: `\((\d{3}[a-z])\)`

### Phase 2b: Fix Introduces (`fix_introduces.py`) — optional
**Purpose**: Improve `introduces` coverage using LaTeX emphasis + DeepSeek.

- Method A: Parse `\emph{}` and `\textit{}` from `formal_statements_latex.json`
  (zero cost; catches 6-10 additional concepts)
- Method B: For definitions still missing `introduces`, ask DeepSeek
  to identify named concepts (~$0.004 for ~10 calls)
- **Output**: updates `raw_text/formal_statements.json` in-place

**Prerequisite**: Requires `formal_statements_latex.json` to exist (Phase 6 first)

**Run**:
```bash
python -m pipeline.fix_introduces            # Method A only
python -m pipeline.fix_introduces --run-api  # A + B
```

### Phase 2c: Statement Names (`extract_names.py`)
**Purpose**: Generate a short descriptive name for each entity.

3-tier resolution:
- **Tier 1 (free)**: Use first entry in `introduces` field
- **Tier 2 (free)**: Use subsection title from `SUBSECTION_TITLES` in `config.py`
  (only if this statement is primary in the subsection)
- **Tier 3 (DeepSeek)**: For remaining statements, ask DeepSeek for a 3-8 word name (~$0.02)

**Output**: `raw_text/statement_names.json` (key: `"kind:number"`, value: name string)

**Run**: `python -m pipeline.extract_names --run-api`

### Phase 3a: Equation Extraction (`extract_equations.py`)
**Purpose**: Catalog all numbered equations `(NNNa)`, `(NNNb)`, …

- Scans chapter text for `(\d{3}[a-z])` patterns
- Records first occurrence as the "definition site"
- Counts references (equations with 3+ references = "key equations")
- **Output**: `raw_text/equations.json` (619 equations, 197 key)

**Run**: `python -m pipeline.extract_equations`

### Phase 3b: Missing Context (`extract_context.py`)
**Purpose**: For each statement, identify variables/equations/preamble defined above.

Two parts:
- **Part 1 (free)**: For each equation tag, extract its text + surrounding
  context from the chapter file → `raw_text/equations_context.json`
- **Part 2 (DeepSeek, ~$0.15)**: For each statement, send its text + 1500
  chars of preceding chapter text. DeepSeek returns JSON with:
  - `variables`: list of `{name, definition}`
  - `equations`: list of `{tag, content}`
  - `preamble`: 1-3 sentence summary
- **Output**: `raw_text/statement_context.json`

**Run**: `python -m pipeline.extract_context --run-api`

### Phase 4a: Cross-References (`extract_references.py`)
**Purpose**: Build dependency edges using regex + concept matching + equation linking.

Three methods:
1. **Regex**: Find explicit "Theorem NNN[A-Z]" references
2. **Concept matching**: Match concept names (from `introduces` + aliases) in statement text
   - Alias generation: dash normalization (`-` / `–` / `—` / `--`), pdftotext
     hyphen-space (`P-` ↔ `P -`), trailing qualifier strip
     ("in its second variable", "principle", "relative to"), plural forms
   - **Longest-match-wins**: "A-stable" consumed before "stable" can match inside it
   - **Full-name priority**: If text matches someone's full `introduces` entry, prefer that target over aliases
   - **Chapter-proximity disambiguation**: for polysemic concepts (e.g., "stable" defined in 3 chapters), pick same/nearest-preceding chapter
   - See `concept_matching_audit.md` for full details
3. **Equation linking**: An equation's "owner" is the statement in its subsection; when another statement references that equation, create an edge

**Output**: `raw_text/references.json` (~237 edges)

**Run**: `python -m pipeline.extract_references`

### Phase 4a+: LLM References (`extract_references_llm.py`)
**Purpose**: Find implicit dependencies via DeepSeek.

For each of 175 statements:
- Send its full LaTeX body + proof (from `formal_statements_latex.json`)
- Send a compact catalog of other 174 entities:
  - Named entities (have `introduces` or a name): one-line summary
  - Unnamed entities: full LaTeX body without proof
- Ask for minimal set of dependencies (≤10 typically)
- **Output**: `raw_text/references_llm.json` (~464 edges)

**Cost**: ~$0.21 for full run.

**Run**: `python -m pipeline.extract_references_llm --run-api --resume`

### Phase 4c: Break Cycles (`break_cycles.py`)
**Purpose**: Remove minimum-confidence edges until the merged graph is a DAG
(LeanBlueprint requires this).

- Merges `references.json` + `references_llm.json` into `references_merged.json`
  (called externally before this phase — see run_pipeline.py)
- **Confidence scoring**:
  - regex reference: 3
  - equation-linked, concept-matched: 2
  - LLM-only: 1
  - Multi-method edges sum their weights
- **Algorithm**: DFS cycle detection; for each cycle, remove the edge with
  lowest total confidence (tiebreaker: largest positive page_diff = most backward)
- **Outputs**: updates `references_merged.json`; audit log `cycles_removed.json`

**Run**: `python -m pipeline.break_cycles`

### Phase 4b: Dependency Graph (`build_graph.py`)
**Purpose**: Build standalone graph artifacts (separate from blueprint).

- Nodes: 175 formal statements
- Edges: filtered from `references_merged.json` (formal-to-formal only)
- **Outputs**: `graph/dependency_graph.json`, `graph/dependency_graph.dot`,
  `graph/stats.json`, `graph/explore.html`

**Run**: `python -m pipeline.build_graph`

### Phase 5: Markdown Knowledge Base (`generate_markdown.py`)
**Purpose**: Per-chapter markdown summary.

- One file per chapter: `knowledge_base/ch01_differential_difference.md` etc.
- Includes: statement text, proof, references
- **Output**: `knowledge_base/*.md`

**Run**: `python -m pipeline.generate_markdown`

### Phase 6: LaTeX Conversion (`convert_to_latex.py`)
**Purpose**: Convert each statement's raw pdftotext body to clean LaTeX.

- Uses DeepSeek with strict plasTeX constraints
  (see `latex_conversion_guide.md`)
- **Banned in output**: tikzpicture, tabular, \hline, | in array column specs,
  figure/algorithm/verbatim environments
- **Output**: `raw_text/formal_statements_latex.json`
- Incremental saves, supports `--resume`, `--limit N`, `--dry-run`

**Cost**: ~$0.11 for all 175

**Run**: `python -m pipeline.convert_to_latex --run-api --resume`

### Phase 6b: Context LaTeX (`convert_context_to_latex.py`)
**Purpose**: Convert context blocks (preamble + variables + equations) to LaTeX.

- Input: `raw_text/statement_context.json`
- Uses DeepSeek to produce a single LaTeX block per statement
- **Output**: `raw_text/context_latex.json` (key: `"kind:number"`, value: LaTeX)
- Cost: ~$0.09

**Run**: `python -m pipeline.convert_context_to_latex --run-api`

### Phase 7: Verification (`verify.py`)
**Purpose**: Sanity checks on extraction counts.

- Expected counts: ~110 theorems, ~45 definitions, ~22 lemmas, ~4 corollaries
- Checks formal_statements.json, references.json, graph JSON, knowledge_base dir

**Run**: `python -m pipeline.verify`

### Phase 8: Generate Blueprint (`generate_blueprint.py`)
**Purpose**: Build LeanBlueprint LaTeX source files.

- Loads: statements, LaTeX, references_merged, context_latex, statement_names
- For each chapter, emits `\chapter{title}` then iterates ALL sections from
  `CHAPTERS[ch]["sections"]` in order (including empty ones for TOC completeness)
- For each statement, injects context, then the sanitized LaTeX with macros:
  - `\label{kind:NNN[A-Z]}`
  - `\lean{Butcher.ChN.KindNNN[A-Z]}` (placeholder Lean name)
  - `\uses{...}` (from deps_map)
  - `\proves{...}` (on proof environments)
- Title includes extracted name: `\begin{theorem}[Name (212A)]`
- Filter flags:
  - `--no-llm`: exclude LLM edges
  - `--no-concept`: exclude concept-match edges
  - `--only-explicit`: only regex edges
- **Output**: `blueprint/src/chapter{1..5}.tex`, boilerplate files

**Run**: `python -m pipeline.generate_blueprint`

---

## Part 5: DeepSeek Prompts

All prompts are documented in detail in `deepseek_prompts.md` with templates,
rationale, and cost estimates. Scripts that use DeepSeek:

| Phase | Script | What the prompt asks |
|-------|--------|----------------------|
| 2b | `fix_introduces.py` | Identify quoted/italicized concept names |
| 2c | `extract_names.py` | Propose 3-8 word descriptive name |
| 3b | `extract_context.py` | Identify missing variables/equations/preamble |
| 4a+ | `extract_references_llm.py` | Find minimal dependency set |
| 6 | `convert_to_latex.py` | Convert pdftotext → plasTeX-compatible LaTeX |
| 6b | `convert_context_to_latex.py` | Convert context JSON → LaTeX block |

All prompts use `deepseek-chat` (OpenAI-compatible API, base URL
`https://api.deepseek.com`), temperature 0.1.

---

## Part 6: LeanBlueprint Build

### Boilerplate files (generated by `generate_blueprint.py`)

`blueprint/src/web.tex`:
```latex
\documentclass{report}
\usepackage{amssymb, amsthm, amsmath}
\usepackage{hyperref}
\usepackage[showmore, dep_graph]{blueprint}
\input{macros/common}
\title{Numerical Methods for ODEs -- Blueprint}
\begin{document}
\maketitle
\input{content}
\end{document}
```

`blueprint/src/plastex.cfg`:
```ini
[general]
renderer=HTML5
plugins=plastexdepgraph plastexshowmore leanblueprint
[document]
toc-depth=4
[files]
directory=../web/
split-level=0    # 0 = split per chapter (5 HTML pages)
[html5]
mathjax-dollars=False
[images]
imager=none      # avoid pdflatex image generation crashes
```

`blueprint/src/macros/common.tex` (theorem environments required):
```latex
\newtheorem{theorem}{Theorem}[chapter]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
```

### Build wrapper: `blueprint/build.py`

```python
# Runs plasTeX with raised recursion limit (large dep graph),
# then post-processes dep_graph_document.html to replace DOT node labels
# with "NNN[A-Z] Name" instead of just "NNN[A-Z]".
```

### Run
```bash
python blueprint/build.py
# Output: blueprint/web/index.html + sect0001.html ... sect0005.html + dep_graph_document.html
```

### Serve
```bash
cd blueprint/web && python3 -m http.server 8000
# http://localhost:8000
# http://localhost:8000/dep_graph_document.html
```

### Useful tweaks
- **Disable transitive reduction** (show all direct edges): change
  `\usepackage[showmore, dep_graph]{blueprint}` → `\usepackage[showmore, dep_graph, nonreducedgraph]{blueprint}`
  in `generate_blueprint.py`'s boilerplate writer.
- **Change split level**: `split-level=-1` puts everything in `index.html`;
  `split-level=1` splits per-section (may hit plasTeX page limits).

---

## Part 7: Full Reproduction (Step-by-Step)

From scratch, assuming a fresh clone of the Lean project:

```bash
# --- 1. Setup ---
cd /path/to/OpenMath                       # Lean project root
brew install graphviz                      # if not already installed
brew install --cask basictex               # if pdflatex not installed
eval "$(/usr/libexec/path_helper)"         # add TeX to PATH
pip install openai python-dotenv pygraphviz leanblueprint

# --- 2. API key ---
mkdir -p extraction
echo "DEEPSEEK_API_KEY=sk-YOUR_KEY" > extraction/.env

# --- 3. Drop the PDF ---
cp path/to/textbook.pdf extraction/        # must match config.py PDF_PATH
# Update extraction/pipeline/config.py PDF_PATH if filename differs

# --- 4. Run the base pipeline ---
cd extraction
python -m pipeline.extract_text            # chapter files
python -m pipeline.extract_html            # bold/italic formatting
python -m pipeline.extract_formal          # 175 formal statements
python -m pipeline.extract_equations       # 619 equations

# --- 5. Convert to LaTeX (DeepSeek, ~$0.11) ---
python -m pipeline.convert_to_latex --run-api

# --- 6. Enrich introduces field ---
python -m pipeline.fix_introduces --run-api

# --- 7. Generate names ---
python -m pipeline.extract_names --run-api

# --- 8. Extract missing context (DeepSeek, ~$0.15) ---
python -m pipeline.extract_context --run-api

# --- 9. Convert context to LaTeX (DeepSeek, ~$0.09) ---
python -m pipeline.convert_context_to_latex --run-api

# --- 10. Build references ---
python -m pipeline.extract_references                    # regex + concept + equation
python -m pipeline.extract_references_llm --run-api --resume  # +DeepSeek (~$0.21)

# Merge the two reference files (script below)
python -c "
import json
with open('raw_text/references.json') as f: r = json.load(f)
with open('raw_text/references_llm.json') as f: l = json.load(f)
seen = {(e['source'], e['target'], e['edge_type']) for e in r}
merged = list(r)
for e in l:
    key = (e['source'], e['target'], e['edge_type'])
    if key not in seen:
        merged.append(e); seen.add(key)
with open('raw_text/references_merged.json', 'w') as f:
    json.dump(merged, f, indent=2, ensure_ascii=False)
print(f'Merged: {len(merged)} edges')
"

# --- 11. Break cycles ---
python -m pipeline.break_cycles

# --- 12. Build standalone graph + markdown KB ---
python -m pipeline.build_graph
python -m pipeline.generate_markdown
python -m pipeline.verify

# --- 13. Generate & build LeanBlueprint ---
python -m pipeline.generate_blueprint
# Create placeholder css (plasTeX expects it)
touch ../blueprint/src/extra_styles.css
rm -rf ../blueprint/web
python ../blueprint/build.py

# --- 14. Serve ---
cd ../blueprint/web && python3 -m http.server 8000
# Open http://localhost:8000
```

### Cost summary
Total DeepSeek spend for one full run: **~$0.56** (roughly)
- LaTeX conversion: $0.11
- Context extraction: $0.15
- Context → LaTeX: $0.09
- References LLM: $0.21
- Names: $0.02
- Fix introduces: $0.004

### Timing
- All non-LLM steps: ~10 seconds
- DeepSeek calls (sequential, 175 statements × 5 LLM phases): ~30-60 minutes
- Can be parallelized by running LLM scripts in background

---

## Part 8: Key Design Decisions

### Entity detection strategy: bold + text scanning
- `pdftohtml` bold tags (`<b>Theorem NNN[A-Z]</b>`) are the ground truth
- This separates declarations from back-references (e.g., "by Theorem 101A"
  is in plain text, not bold)

### Statement boundary detection
- Upper bound: next formal header, section/subsection header, or Exercises line
- Proof bound: **QED box (`\x01` in pdftotext)** — primary signal for proof end

### Concept matching: full-name priority + longest-match-wins
Critical for handling polysemy:
- "stable" has 3 definitions (matrix, LMM, GLM) — chapter proximity picks
- "A-stable" must not be matched as "stable" (longest-match-wins with hyphen-aware boundaries)
- "Lipschitz condition" as alias matches def:110A correctly

### Cycle removal: confidence-weighted
- Multi-method edges (regex + concept + LLM all agreeing) are preserved
- LLM-only edges are removed first when breaking cycles
- Audit log in `cycles_removed.json`

### Blueprint generation: per-chapter section completeness
- Emit `\section{}` header for every section defined in `CHAPTERS` config,
  even if the section has no formal statements (expository sections)
- Ensures TOC matches textbook structure

### LaTeX sanitization for plasTeX
plasTeX is more restrictive than pdflatex. Must avoid:
- tikzpicture, figure/table floats, tabular, algorithm, verbatim
- `\hline`, `\cline`, `|` in array column specs
- Bodies >5000 chars tend to crash the renderer

See `latex_conversion_guide.md` for full details.

---

## Part 9: Adapting to a New Textbook

1. **Update `config.py`**:
   - `PDF_PATH`
   - `CHAPTERS` dict (titles, sections, page ranges)
   - `RUNNING_HEADERS` (filter page headers)
   - `SUBSECTION_TITLES` (extract from TOC — see helper in `extract_names.py`)
   - Regex patterns if numbering scheme differs

2. **Adjust `extract_text.py`**:
   - `find_chapter_boundaries` pattern if not "Chapter N" format

3. **Check bold patterns in `extract_html.py`**:
   - `BOLD_THEOREM_RE`, `BOLD_DEFINITION_RE`, etc.

4. **Adjust plural map in `extract_references.py`**:
   - Add domain-specific nouns if they're commonly pluralized

5. **Re-run pipeline** end-to-end.

Most of the work is in `config.py`. The rest of the pipeline is textbook-agnostic.

---

## Part 10: Troubleshooting

### plasTeX fails with "Unknown environment 'proof'"
The `proof` environment comes from `amsthm`. Make sure
`\usepackage{amssymb, amsthm, amsmath}` is in web.tex.

### plasTeX runs out of memory / recursion
`blueprint/build.py` sets `sys.setrecursionlimit(10000)`. If still failing,
the issue is likely an extremely long LaTeX body — check the warning from
`generate_blueprint.py` about >5000 char statements, and reconvert them
with a concise DeepSeek prompt.

### Dep graph shows fewer edges than expected
plasTeX applies transitive reduction by default. To see all direct edges,
edit `generate_blueprint.py` to add `nonreducedgraph` to the blueprint
package options.

### pdflatex not found
```bash
eval "$(/usr/libexec/path_helper)"
# Or explicitly:
export PATH="/usr/local/texlive/2026basic/bin/universal-darwin:$PATH"
```

### Sections appear with wrong numbers
The plasTeX section numbering is 1-based per chapter (1.1, 1.2, ...)
whereas Butcher uses 10, 11, 12. The config-defined section numbers
(10, 11, etc.) are only used for matching statement numbers; the
displayed numbering is plasTeX's.

### DeepSeek errors in background
Background scripts save incrementally. Re-run with `--resume` to continue.
Failed entries keep their error string in the JSON for inspection.

### Cycles persist after `break_cycles.py`
Re-check that `references_merged.json` is freshly merged before cycle-breaking.
The merge must happen BEFORE cycle-breaking, not after.

---

## Part 11: Current Results (reference textbook)

| Metric | Value |
|--------|-------|
| Formal statements | 175 (104 thm, 45 def, 22 lem, 4 cor) |
| Statements with proofs | 106 |
| Statements with LaTeX | 175 |
| Statements with context | 138 |
| Statements with names | 175 |
| Concept aliases generated | 156 |
| References (total merged, pre-cycle) | 710 |
| References (final, cycle-free) | ~621 |
| Cycles broken | ~86 |
| Dep graph nodes | 175 |
| Dep graph visible edges (after transitive reduction) | ~155 |
| Blueprint sections | 36 (all rendered, including 9 empty) |

---

## References

- **`deepseek_prompts.md`** — All LLM prompt templates
- **`latex_conversion_guide.md`** — plasTeX compatibility rules
- **`concept_matching_audit.md`** — Concept alias generation rules
- **`verification_report.md`** — Quality audit of extraction
- **`progress.md`** — Historical progress log
