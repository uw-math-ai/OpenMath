"""Phase 3a: Extract numbered equations and count their references.

Scans per-chapter text files for equation tags like (100a), (210b), etc.
Identifies equations referenced 3+ times as 'key equations'.
"""
from __future__ import annotations

import json
import re
from collections import Counter
from pathlib import Path

from pipeline.config import (
    RAW_TEXT_DIR,
    EQUATION_TAG_RE,
    chapter_from_subsection,
    section_from_subsection,
)


def extract_equations() -> list[dict]:
    """Extract all numbered equations and their reference counts."""
    # First pass: find all equation tags and their locations
    all_tags: list[dict] = []
    tag_counter: Counter = Counter()

    for ch in range(1, 6):
        filepath = RAW_TEXT_DIR / f"ch{ch:02d}.txt"
        if not filepath.exists():
            continue
        text = filepath.read_text(encoding="utf-8")
        lines = text.split("\n")

        for i, line in enumerate(lines):
            for m in EQUATION_TAG_RE.finditer(line):
                tag = m.group(1)
                tag_counter[tag] += 1
                # Record first occurrence as the defining location
                existing = [t for t in all_tags if t["tag"] == tag]
                if not existing:
                    subsec = int(tag[:3])
                    all_tags.append({
                        "tag": tag,
                        "chapter": ch,
                        "section": str(section_from_subsection(subsec)),
                        "subsection": str(subsec),
                        "line": i + 1,
                        "context": line.strip()[:200],
                    })

    # Enrich with reference counts
    equations = []
    for eq in all_tags:
        tag = eq["tag"]
        count = tag_counter[tag]
        eq["reference_count"] = count
        eq["is_key"] = count >= 3
        equations.append(eq)

    # Sort by tag
    equations.sort(key=lambda e: e["tag"])
    return equations


def main() -> None:
    print("Phase 3a: Extracting equations ...")
    equations = extract_equations()

    out_path = RAW_TEXT_DIR / "equations.json"
    out_path.write_text(
        json.dumps(equations, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )

    key_count = sum(1 for e in equations if e["is_key"])
    print(f"  Total unique equations: {len(equations)}")
    print(f"  Key equations (3+ refs): {key_count}")
    print(f"  Wrote {out_path}")


if __name__ == "__main__":
    main()
