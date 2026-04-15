"""Phase 7: Verify extraction results for completeness and consistency."""
from __future__ import annotations

import json
from pathlib import Path

from pipeline.config import RAW_TEXT_DIR, GRAPH_DIR, KB_DIR, CHAPTERS


# Expected count ranges (min, max)
EXPECTED_COUNTS = {
    "theorem": (90, 115),
    "definition": (35, 50),
    "lemma": (18, 28),
    "corollary": (2, 8),
}


def verify() -> list[str]:
    """Run all verification checks. Returns list of issues found."""
    issues: list[str] = []

    # 1. Check chapter files exist
    print("  Checking chapter files ...")
    for ch in range(1, 6):
        path = RAW_TEXT_DIR / f"ch{ch:02d}.txt"
        if not path.exists():
            issues.append(f"Missing chapter file: {path}")
        else:
            lines = path.read_text(encoding="utf-8").split("\n")
            if len(lines) < 100:
                issues.append(f"Chapter {ch} has only {len(lines)} lines (suspiciously few)")

    # 2. Check formal statements
    print("  Checking formal statements ...")
    stmts_path = RAW_TEXT_DIR / "formal_statements.json"
    if not stmts_path.exists():
        issues.append("Missing formal_statements.json")
        return issues

    with open(stmts_path, encoding="utf-8") as f:
        statements = json.load(f)

    kind_counts: dict[str, int] = {}
    ch_counts: dict[int, int] = {}
    for s in statements:
        kind_counts[s["kind"]] = kind_counts.get(s["kind"], 0) + 1
        ch_counts[s["chapter"]] = ch_counts.get(s["chapter"], 0) + 1

    for kind, (lo, hi) in EXPECTED_COUNTS.items():
        actual = kind_counts.get(kind, 0)
        if actual < lo:
            issues.append(f"Too few {kind}s: {actual} (expected >= {lo})")
        elif actual > hi:
            issues.append(f"Too many {kind}s: {actual} (expected <= {hi})")

    # Check all chapters represented
    for ch in range(1, 6):
        if ch not in ch_counts:
            issues.append(f"No statements found in chapter {ch}")

    # Check for empty text
    empty_text = [s for s in statements if not s["text"].strip()]
    if empty_text:
        issues.append(f"{len(empty_text)} statements have empty text")

    # Check for duplicate numbers
    seen_nums: dict[str, list[str]] = {}
    for s in statements:
        key = f"{s['kind']}:{s['number']}"
        seen_nums.setdefault(key, []).append(str(s["chapter"]))
    dupes = {k: v for k, v in seen_nums.items() if len(v) > 1}
    if dupes:
        for k, chs in dupes.items():
            issues.append(f"Duplicate statement: {k} in chapters {', '.join(chs)}")

    # 3. Check references
    print("  Checking references ...")
    refs_path = RAW_TEXT_DIR / "references.json"
    if refs_path.exists():
        with open(refs_path, encoding="utf-8") as f:
            edges = json.load(f)
        # Check for self-references
        self_refs = [e for e in edges if e["source"] == e["target"]]
        if self_refs:
            issues.append(f"{len(self_refs)} self-referencing edges found")
    else:
        issues.append("Missing references.json")

    # 4. Check graph
    print("  Checking dependency graph ...")
    graph_path = GRAPH_DIR / "dependency_graph.json"
    if graph_path.exists():
        with open(graph_path, encoding="utf-8") as f:
            graph = json.load(f)
        if len(graph["nodes"]) != len(statements):
            issues.append(
                f"Graph nodes ({len(graph['nodes'])}) != statements ({len(statements)})"
            )
    else:
        issues.append("Missing dependency_graph.json")

    # 5. Check knowledge base
    print("  Checking knowledge base ...")
    for ch in range(1, 6):
        slug = CHAPTERS[ch]["slug"]
        kb_path = KB_DIR / f"{slug}.md"
        if not kb_path.exists():
            issues.append(f"Missing knowledge base file: {kb_path}")

    return issues


def main() -> None:
    print("Phase 7: Verification ...")
    issues = verify()

    if issues:
        print(f"\n  ISSUES FOUND ({len(issues)}):")
        for issue in issues:
            print(f"    - {issue}")
    else:
        print("\n  All checks passed!")

    # Print summary statistics
    print("\n  Summary:")
    stmts_path = RAW_TEXT_DIR / "formal_statements.json"
    if stmts_path.exists():
        with open(stmts_path, encoding="utf-8") as f:
            statements = json.load(f)
        print(f"    Total statements: {len(statements)}")
        kind_counts: dict[str, int] = {}
        for s in statements:
            kind_counts[s["kind"]] = kind_counts.get(s["kind"], 0) + 1
        for k, v in sorted(kind_counts.items()):
            print(f"      {k}: {v}")
        with_proof = sum(1 for s in statements if s.get("proof_text"))
        print(f"    Statements with proofs: {with_proof}")

    refs_path = RAW_TEXT_DIR / "references.json"
    if refs_path.exists():
        with open(refs_path, encoding="utf-8") as f:
            edges = json.load(f)
        print(f"    Total cross-reference edges: {len(edges)}")

    eqs_path = RAW_TEXT_DIR / "equations.json"
    if eqs_path.exists():
        with open(eqs_path, encoding="utf-8") as f:
            equations = json.load(f)
        key_eqs = sum(1 for e in equations if e["is_key"])
        print(f"    Total equations: {len(equations)} ({key_eqs} key)")


if __name__ == "__main__":
    main()
