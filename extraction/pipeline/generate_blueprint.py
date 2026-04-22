"""Phase 8: Generate LeanBlueprint project from extracted data.

Creates a complete blueprint/ directory with LaTeX source files
containing \\label{}, \\lean{}, \\uses{}, and \\proves{} macros
for building an interactive dependency graph with leanblueprint.

Usage:
    python -m pipeline.generate_blueprint
"""
from __future__ import annotations

import json
import re
from pathlib import Path

from pipeline.config import (
    RAW_TEXT_DIR,
    BLUEPRINT_DIR,
    CHAPTERS,
)


# ── Constants ──────────────────────────────────────────────────────────

SRC_DIR = BLUEPRINT_DIR / "src"
MACROS_DIR = SRC_DIR / "macros"

KIND_PREFIX = {
    "theorem": "thm",
    "definition": "def",
    "lemma": "lem",
    "corollary": "cor",
}
KIND_LEAN = {
    "theorem": "Thm",
    "definition": "Def",
    "lemma": "Lem",
    "corollary": "Cor",
}
# Map our kind names to LeanBlueprint environment names
KIND_ENV = {
    "theorem": "theorem",
    "definition": "definition",
    "lemma": "lemma",
    "corollary": "corollary",
}


def _make_id(kind: str, number: str) -> str:
    return f"{KIND_PREFIX.get(kind, kind[:3])}:{number}"


def _make_lean_name(kind: str, number: str, chapter: int) -> str:
    return f"Butcher.Ch{chapter}.{KIND_LEAN.get(kind, kind.title())}{number}"


# ── Data loading ───────────────────────────────────────────────────────

_EXCLUDE_EDGE_TYPES: set[str] = set()


def _load_data() -> tuple[list[dict], dict[str, str], dict[str, list[str]], dict[str, str], dict[str, str]]:
    """Load statements, LaTeX map, dependency map, context LaTeX, and names.

    Returns (statements, latex_map, deps_map, context_map, names_map).
    """
    with open(RAW_TEXT_DIR / "formal_statements.json", encoding="utf-8") as f:
        statements = json.load(f)

    # Build LaTeX map from the latex file
    latex_map: dict[str, str] = {}
    latex_path = RAW_TEXT_DIR / "formal_statements_latex.json"
    if latex_path.exists():
        with open(latex_path, encoding="utf-8") as f:
            latex_stmts = json.load(f)
        for s in latex_stmts:
            if s.get("latex_status") == "completed" and s.get("latex"):
                sid = _make_id(s["kind"], s["number"])
                latex_map[sid] = s["latex"]

    # Build dependency map. Prefer Phase 8's final edge set (post-denylist,
    # post-cycle-break on the extension-merged graph). Fall back to the raw
    # merged file if Phase 8 hasn't run yet.
    deps_map: dict[str, list[str]] = {}
    final_refs = RAW_TEXT_DIR.parent / "formalization_data" / "references_final.json"
    if final_refs.exists():
        refs_path = final_refs
    else:
        refs_path = RAW_TEXT_DIR / "references_merged.json"
        if not refs_path.exists():
            refs_path = RAW_TEXT_DIR / "references.json"
    if refs_path.exists():
        with open(refs_path, encoding="utf-8") as f:
            edges = json.load(f)
        skipped = 0
        for e in edges:
            # Filter by edge type
            if e.get("edge_type", "") in _EXCLUDE_EDGE_TYPES:
                skipped += 1
                continue
            target = e["target"]
            # Only formal-to-formal edges
            if any(target.startswith(p + ":") for p in KIND_PREFIX.values()):
                deps_map.setdefault(e["source"], []).append(target)
        # Deduplicate
        for k in deps_map:
            deps_map[k] = sorted(set(deps_map[k]))
        if skipped:
            print(f"  Skipped {skipped} edges (excluded types: {_EXCLUDE_EDGE_TYPES})")

    # Load context LaTeX
    context_map: dict[str, str] = {}
    ctx_path = RAW_TEXT_DIR / "context_latex.json"
    if ctx_path.exists():
        with open(ctx_path, encoding="utf-8") as f:
            context_map = json.load(f)

    # Load statement names
    names_map: dict[str, str] = {}
    names_path = RAW_TEXT_DIR / "statement_names.json"
    if names_path.exists():
        with open(names_path, encoding="utf-8") as f:
            names_map = json.load(f)

    return statements, latex_map, deps_map, context_map, names_map


# ── LaTeX sanitization ─────────────────────────────────────────────────

# Environments that plasTeX cannot handle
_BANNED_ENVS = [
    "tikzpicture", "figure", "table", "algorithm", "algorithmic",
    "verbatim", "lstlisting", "minted", "pgfplots", "wrapfigure",
]

# Commands to strip
_BANNED_CMDS = [
    r"\\hline", r"\\cline\{[^}]*\}", r"\\toprule", r"\\midrule",
    r"\\bottomrule", r"\\rowcolor\{[^}]*\}", r"\\cellcolor\{[^}]*\}",
    r"\\caption\{[^}]*\}", r"\\centering",
    r"\\draw\b[^;]*;", r"\\node\b[^;]*;", r"\\path\b[^;]*;",
    r"\\tikz\b[^;]*;",
]


def _sanitize_latex(latex: str, kind: str) -> str:
    """Clean up DeepSeek LaTeX to be plasTeX-compatible.

    1. Remove banned environments (tikzpicture, figure, table, etc.)
       and replace with a comment
    2. Strip banned commands (hline, cline, etc.)
    3. Remove | from array column specs
    4. Strip content after the main \\end{kind} and \\end{proof} blocks
       (DeepSeek sometimes appends unrelated text from surrounding context)
    """
    # Step 1: Strip content that appears after the main environment closes.
    # Keep only: \begin{kind}...\end{kind} and optionally \begin{proof}...\end{proof}
    env = KIND_ENV.get(kind, kind)
    # Find the main \end{env}
    end_env = f"\\end{{{env}}}"
    end_proof = "\\end{proof}"

    # Locate the last relevant \end tag
    last_end = -1
    pos = latex.rfind(end_proof)
    if pos >= 0:
        last_end = pos + len(end_proof)
    else:
        pos = latex.rfind(end_env)
        if pos >= 0:
            last_end = pos + len(end_env)

    if last_end >= 0:
        latex = latex[:last_end]

    # Step 2: Remove banned environments entirely
    for env_name in _BANNED_ENVS:
        pattern = re.compile(
            r"\\begin\{" + re.escape(env_name) + r"\}.*?\\end\{" + re.escape(env_name) + r"\}",
            re.DOTALL,
        )
        latex = pattern.sub(f"% [Removed {env_name} environment]", latex)

    # Step 3: Strip banned commands
    for cmd_pat in _BANNED_CMDS:
        latex = re.sub(cmd_pat, "", latex)

    # Step 4: Remove | from array column specs
    def clean_array_cols(m):
        cols = m.group(1).replace("|", "")
        return f"\\begin{{array}}{{{cols}}}"
    latex = re.sub(r"\\begin\{array\}\{([^}]*)\}", clean_array_cols, latex)

    # Same for tabular (convert to array)
    def tabular_to_array(m):
        cols = m.group(1).replace("|", "")
        return f"\\begin{{array}}{{{cols}}}"
    latex = re.sub(r"\\begin\{tabular\}\{([^}]*)\}", tabular_to_array, latex)
    latex = latex.replace("\\end{tabular}", "\\end{array}")

    # Step 5: Clean up empty lines from removals
    latex = re.sub(r"\n{3,}", "\n\n", latex)

    # Step 6: Warn about oversized statements (should be fixed at
    # conversion time via DeepSeek prompt, not by truncation)
    if len(latex) > 5000:
        import sys
        print(f"  WARNING: {kind} is {len(latex)} chars (>5000). "
              f"Reconvert with --limit to keep concise.", file=sys.stderr)

    return latex.strip()


# ── LaTeX injection ────────────────────────────────────────────────────

def _inject_macros(
    latex: str,
    label: str,
    lean_name: str,
    uses_list: list[str],
    kind: str,
    number: str = "",
    name: str = "",
) -> str:
    """Inject \\label, \\lean, \\uses into existing LaTeX environments."""
    env = KIND_ENV.get(kind, kind)
    macros = f"  \\label{{{label}}}\n  \\lean{{{lean_name}}}\n"
    if uses_list:
        macros += f"  \\uses{{{', '.join(uses_list)}}}\n"
    else:
        macros += "  \\uses{}\n"

    # Build the title: "Name (NNN[A-Z])" if name given, else just "NNN[A-Z]"
    # Escape LaTeX special characters in the name
    if name:
        safe_name = name.replace("$", "\\$").replace("&", "\\&").replace("%", "\\%").replace("#", "\\#").replace("_", "\\_")
        title = f"{safe_name} ({number})" if number else safe_name
    else:
        title = number

    # Replace/add [title] on \begin{env}
    # Handle three cases:
    #   \begin{env}           -> \begin{env}[title]
    #   \begin{env}[old]      -> \begin{env}[new_title]
    begin_with_title = re.compile(
        r"\\begin\{" + re.escape(env) + r"\}\[[^\]]*\]"
    )
    begin_no_title = re.compile(
        r"\\begin\{" + re.escape(env) + r"\}(?!\[)"
    )
    if title:
        if begin_with_title.search(latex):
            latex = begin_with_title.sub(
                f"\\\\begin{{{env}}}[{title}]", latex, count=1
            )
        elif begin_no_title.search(latex):
            latex = begin_no_title.sub(
                f"\\\\begin{{{env}}}[{title}]", latex, count=1
            )

    # Inject after \begin{env}[title]
    pattern = re.compile(
        r"(\\begin\{" + re.escape(env) + r"\}(?:\[[^\]]*\])?)\s*\n?"
    )
    m = pattern.search(latex)
    if m:
        insert_pos = m.end()
        latex = latex[:insert_pos] + "\n" + macros + latex[insert_pos:]
    else:
        # Fallback: prepend macros at the top
        latex = macros + latex

    # Inject \proves into \begin{proof} blocks
    if f"\\begin{{proof}}" in latex:
        proof_macros = f"  \\proves{{{label}}}\n"
        if uses_list:
            proof_macros += f"  \\uses{{{', '.join(uses_list)}}}\n"
        latex = latex.replace(
            "\\begin{proof}\n",
            "\\begin{proof}\n" + proof_macros,
            1,  # Only first occurrence
        )
        # Also handle \begin{proof} without trailing newline
        latex = latex.replace(
            "\\begin{proof}",
            "\\begin{proof}\n" + proof_macros,
            1,
        )
        # Clean up double-injection (if both replacements fired)
        latex = re.sub(
            r"(\\proves\{[^}]+\}\n\s*\\uses\{[^}]*\}\n)\s*\\proves\{[^}]+\}\n\s*\\uses\{[^}]*\}\n",
            r"\1",
            latex,
        )

    return latex


def _make_fallback_latex(
    stmt: dict,
    label: str,
    lean_name: str,
    uses_list: list[str],
) -> str:
    """Generate blueprint LaTeX for a statement without DeepSeek conversion."""
    env = KIND_ENV.get(stmt["kind"], stmt["kind"])
    uses_str = ", ".join(uses_list) if uses_list else ""

    lines = [
        f"\\begin{{{env}}}[{stmt['number']}]",
        f"  \\label{{{label}}}",
        f"  \\lean{{{lean_name}}}",
        f"  \\uses{{{uses_str}}}",
        f"  % Raw text (not yet converted to LaTeX):",
    ]
    # Add raw text as comments
    for tline in stmt["text"].split("\n"):
        stripped = tline.strip()
        if stripped:
            lines.append(f"  % {stripped}")
    lines.append(f"\\end{{{env}}}")

    if stmt.get("proof_text"):
        lines.append("")
        lines.append("\\begin{proof}")
        lines.append(f"  \\proves{{{label}}}")
        lines.append(f"  \\uses{{{uses_str}}}")
        lines.append("  % Proof text omitted (see formal\\_statements.json)")
        lines.append("\\end{proof}")

    return "\n".join(lines)


# ── Chapter generation ─────────────────────────────────────────────────

def _build_statement_block(
    stmt: dict,
    chapter: int,
    latex_map: dict[str, str],
    deps_map: dict[str, list[str]],
    context_map: dict[str, str] | None,
    names_map: dict[str, str] | None,
) -> str:
    """Build the LaTeX block for a single statement (context + theorem env)."""
    sid = _make_id(stmt["kind"], stmt["number"])
    label = sid
    lean_name = _make_lean_name(stmt["kind"], stmt["number"], chapter)
    uses = deps_map.get(sid, [])

    parts = []

    # Inject context block before the statement (if available)
    ctx_key = f"{stmt['kind']}:{stmt['number']}"
    if context_map and ctx_key in context_map:
        ctx_latex = context_map[ctx_key]
        if ctx_latex and not ctx_latex.startswith("% Error"):
            ctx_latex = re.sub(
                r"\\paragraph\{[^}]*\}",
                r"\\noindent\\textbf{Context.}",
                ctx_latex,
            )
            parts.append(ctx_latex)
            parts.append("")

    # Get name if available
    name = ""
    if names_map:
        name = names_map.get(f"{stmt['kind']}:{stmt['number']}", "")

    if sid in latex_map:
        sanitized = _sanitize_latex(latex_map[sid], stmt["kind"])
        latex = _inject_macros(
            sanitized, label, lean_name, uses, stmt["kind"],
            stmt["number"], name
        )
    else:
        latex = _make_fallback_latex(stmt, label, lean_name, uses)

    parts.append(latex)
    parts.append("")
    return "\n".join(parts)


def _generate_chapter(
    chapter: int,
    statements: list[dict],
    latex_map: dict[str, str],
    deps_map: dict[str, list[str]],
    context_map: dict[str, str] | None = None,
    names_map: dict[str, str] | None = None,
) -> str:
    """Generate the LaTeX content for one chapter file.

    Emits a \\section header for EVERY section defined in CHAPTERS config,
    even if that section has no formal statements (for TOC completeness).
    """
    ch_info = CHAPTERS[chapter]
    ch_stmts = [s for s in statements if s["chapter"] == chapter]

    # Group statements by their derived section (from subsection number,
    # more reliable than the section field which can lose sync)
    stmts_by_section: dict[int, list[dict]] = {}
    for stmt in ch_stmts:
        subsec = stmt.get("subsection", "")
        if subsec and len(subsec) >= 3 and subsec.isdigit():
            sec_num = int(subsec) // 10
        else:
            try:
                sec_num = int(stmt.get("section", "0"))
            except ValueError:
                sec_num = 0
        stmts_by_section.setdefault(sec_num, []).append(stmt)

    lines = [f"\\chapter{{{ch_info['title']}}}", ""]

    # Iterate through ALL sections defined in the chapter config,
    # emitting a section header for each (even empty ones).
    for sec_num in sorted(ch_info["sections"].keys()):
        sec_title = ch_info["sections"][sec_num]
        lines.append(f"\\section{{{sec_title}}}")
        lines.append("")

        section_stmts = stmts_by_section.get(sec_num, [])
        if not section_stmts:
            # Empty section — add a placeholder comment for clarity
            lines.append(f"% Section {sec_num} has no formal statements in the textbook.")
            lines.append("")
            continue

        for stmt in section_stmts:
            lines.append(_build_statement_block(
                stmt, chapter, latex_map, deps_map, context_map, names_map
            ))

    return "\n".join(lines)


# ── Boilerplate files ──────────────────────────────────────────────────

def _write_boilerplate() -> None:
    """Write the standard LeanBlueprint project files."""
    MACROS_DIR.mkdir(parents=True, exist_ok=True)

    # web.tex — needs blueprint package for plasTeX
    # Transitive reduction is enabled by default (cleaner graph).
    # To see all direct edges, add 'nonreducedgraph' to the package options.
    (SRC_DIR / "web.tex").write_text(r"""\documentclass{report}

\usepackage{amssymb, amsthm, amsmath}
\usepackage{hyperref}
\usepackage[showmore, dep_graph]{blueprint}

\input{macros/common}

\title{Numerical Methods for ODEs -- Blueprint}
\author{Butcher Formalization Project}

\begin{document}
\maketitle
\input{content}
\end{document}
""", encoding="utf-8")

    # print.tex
    (SRC_DIR / "print.tex").write_text(r"""\documentclass{report}

\usepackage{amssymb, amsthm, amsmath}
\usepackage{hyperref}
\usepackage[showmore]{blueprint}

\input{macros/common}

\title{Numerical Methods for ODEs -- Blueprint}
\author{Butcher Formalization Project}

\begin{document}
\maketitle
\input{content}
\end{document}
""", encoding="utf-8")

    # content.tex
    (SRC_DIR / "content.tex").write_text(r"""\input{chapter1}
\input{chapter2}
\input{chapter3}
\input{chapter4}
\input{chapter5}
""", encoding="utf-8")

    # macros/common.tex — theorem environments required
    (MACROS_DIR / "common.tex").write_text(r"""% Common macros for Butcher's Numerical Methods for ODEs

% Math shortcuts
\newcommand{\R}{\mathbb{R}}
\newcommand{\N}{\mathbb{N}}
\newcommand{\C}{\mathbb{C}}
\newcommand{\Z}{\mathbb{Z}}

% Theorem environments (needed for blueprint)
\newtheorem{theorem}{Theorem}[chapter]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
""", encoding="utf-8")

    # macros/web.tex
    (MACROS_DIR / "web.tex").write_text(r"""% Web-specific macros (plasTeX)
""", encoding="utf-8")

    # plastex.cfg
    (SRC_DIR / "plastex.cfg").write_text(r"""[general]
renderer=HTML5
copy-theme-extras=yes
plugins=plastexdepgraph plastexshowmore leanblueprint

[document]
toc-depth=4
toc-non-files=True

[files]
directory=../web/
split-level=0

[html5]
localtoc-level=1
extra-css=extra_styles.css
mathjax-dollars=False

[images]
imager=none
""", encoding="utf-8")


# ── Main ───────────────────────────────────────────────────────────────

def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(
        description="Generate LeanBlueprint project from extracted data"
    )
    parser.add_argument(
        "--no-llm", action="store_true",
        help="Exclude LLM-discovered dependencies (edge_type=llm_dependency)",
    )
    parser.add_argument(
        "--no-concept", action="store_true",
        help="Exclude concept-name dependencies (edge_type=uses_concept)",
    )
    parser.add_argument(
        "--no-equation", action="store_true",
        help="Exclude equation-to-statement links (edge_type=uses_equation_from)",
    )
    parser.add_argument(
        "--only-explicit", action="store_true",
        help="Only keep explicit regex references (Theorem/Definition/Lemma/Corollary NNN[A-Z])",
    )
    args = parser.parse_args()

    if args.only_explicit:
        _EXCLUDE_EDGE_TYPES.update({"llm_dependency", "uses_concept", "uses_equation_from"})
    else:
        if args.no_llm:
            _EXCLUDE_EDGE_TYPES.add("llm_dependency")
        if args.no_concept:
            _EXCLUDE_EDGE_TYPES.add("uses_concept")
        if args.no_equation:
            _EXCLUDE_EDGE_TYPES.add("uses_equation_from")

    print("Phase 8: Generating LeanBlueprint project ...")
    if _EXCLUDE_EDGE_TYPES:
        print(f"  Excluding edge types: {_EXCLUDE_EDGE_TYPES}")

    statements, latex_map, deps_map, context_map, names_map = _load_data()
    print(f"  Statements: {len(statements)}")
    print(f"  LaTeX available: {len(latex_map)}")
    print(f"  Context available: {len(context_map)}")
    print(f"  Names available: {len(names_map)}")
    print(f"  Statements with dependencies: {len(deps_map)}")
    total_deps = sum(len(v) for v in deps_map.values())
    print(f"  Total dependency edges: {total_deps}")

    # Create directory structure
    SRC_DIR.mkdir(parents=True, exist_ok=True)

    # Write boilerplate
    _write_boilerplate()
    print(f"  Wrote boilerplate (web.tex, print.tex, content.tex, macros/)")

    # Generate chapter files
    for ch in range(1, 6):
        content = _generate_chapter(ch, statements, latex_map, deps_map, context_map, names_map)
        out_path = SRC_DIR / f"chapter{ch}.tex"
        out_path.write_text(content, encoding="utf-8")
        ch_stmts = sum(1 for s in statements if s["chapter"] == ch)
        print(f"  chapter{ch}.tex: {ch_stmts} statements")

    print(f"\n  Blueprint project generated at {BLUEPRINT_DIR}")
    print(f"  To build: cd {BLUEPRINT_DIR} && leanblueprint web")


if __name__ == "__main__":
    main()
