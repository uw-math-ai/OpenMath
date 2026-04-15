"""Phase 5: Generate markdown knowledge base files organized by chapter.

Creates one .md file per chapter with all definitions, theorems, lemmas,
corollaries, cross-references, and page numbers.
"""
from __future__ import annotations

import json
from pathlib import Path

from pipeline.config import RAW_TEXT_DIR, KB_DIR, CHAPTERS


def _make_id(kind: str, number: str) -> str:
    prefix = {"theorem": "thm", "definition": "def", "lemma": "lem", "corollary": "cor"}.get(kind, kind[:3])
    return f"{prefix}:{number}"


def generate_chapter_markdown(
    chapter: int,
    statements: list[dict],
    ref_edges: list[dict],
) -> str:
    """Generate markdown content for one chapter."""
    ch_info = CHAPTERS[chapter]
    lines = []
    lines.append(f"# Chapter {chapter}: {ch_info['title']}")
    lines.append(f"\nPages {ch_info['page_start']}-{ch_info['page_end']}")
    lines.append("")

    # Sections
    lines.append("## Sections")
    lines.append("")
    for sec_num, sec_title in sorted(ch_info["sections"].items()):
        lines.append(f"- **{sec_num}** {sec_title}")
    lines.append("")

    # Filter statements for this chapter
    ch_stmts = [s for s in statements if s["chapter"] == chapter]

    # Build reference maps
    outgoing: dict[str, list[dict]] = {}
    incoming: dict[str, list[dict]] = {}
    for e in ref_edges:
        outgoing.setdefault(e["source"], []).append(e)
        incoming.setdefault(e["target"], []).append(e)

    # Group by kind
    for kind, kind_title in [
        ("definition", "Definitions"),
        ("theorem", "Theorems"),
        ("lemma", "Lemmas"),
        ("corollary", "Corollaries"),
    ]:
        kind_stmts = [s for s in ch_stmts if s["kind"] == kind]
        if not kind_stmts:
            continue

        lines.append(f"## {kind_title} ({len(kind_stmts)})")
        lines.append("")

        for s in kind_stmts:
            sid = _make_id(s["kind"], s["number"])
            page_str = f" (p.{s['page']})" if s.get("page") else ""
            lines.append(f"### {kind.title()} {s['number']}{page_str}")
            lines.append(f"*Section {s['section']}, Subsection {s['subsection']}*")
            lines.append("")

            # Statement text
            lines.append("```")
            lines.append(s["text"])
            lines.append("```")
            lines.append("")

            # Proof
            if s.get("proof_text"):
                lines.append("<details><summary>Proof</summary>")
                lines.append("")
                lines.append("```")
                lines.append(s["proof_text"])
                lines.append("```")
                lines.append("</details>")
                lines.append("")

            # References from this statement
            out_refs = outgoing.get(sid, [])
            if out_refs:
                lines.append("**References:**")
                for ref in out_refs:
                    lines.append(f"- {ref['edge_type']}: `{ref['target']}`")
                lines.append("")

            # Referenced by
            in_refs = incoming.get(sid, [])
            if in_refs:
                lines.append("**Referenced by:**")
                for ref in in_refs:
                    lines.append(f"- `{ref['source']}` ({ref['edge_type']})")
                lines.append("")

            lines.append("---")
            lines.append("")

    return "\n".join(lines)


def main() -> None:
    print("Phase 5: Generating markdown knowledge base ...")

    KB_DIR.mkdir(parents=True, exist_ok=True)

    # Load data
    with open(RAW_TEXT_DIR / "formal_statements.json", encoding="utf-8") as f:
        statements = json.load(f)
    with open(RAW_TEXT_DIR / "references.json", encoding="utf-8") as f:
        ref_edges = json.load(f)

    for ch in range(1, 6):
        ch_info = CHAPTERS[ch]
        md_content = generate_chapter_markdown(ch, statements, ref_edges)
        out_path = KB_DIR / f"{ch_info['slug']}.md"
        out_path.write_text(md_content, encoding="utf-8")

        ch_count = sum(1 for s in statements if s["chapter"] == ch)
        print(f"  {out_path.name}: {ch_count} statements")

    print(f"\nPhase 5 complete: {len(list(KB_DIR.glob('*.md')))} knowledge base files")


if __name__ == "__main__":
    main()
