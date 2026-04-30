#!/usr/bin/env python3
"""Sync \\leanok markers in blueprint/src/chapter*.tex from lean_status.json.

Source of truth: extraction/formalization_data/lean_status.json
  status == "formalized"   -> \\leanok in env body AND in proof block;
                              if a theorem/lemma/corollary has no \\begin{proof}
                              block at all, a stub proof block is inserted so
                              the dep graph node renders as fully formalized.
  status == "in_progress"  -> no markers (statement may be typed but proof isn't)
  status == "unformalized" -> no markers

Idempotent. Re-run after every formalization cycle, then rebuild blueprint:
    python3 blueprint/sync_leanok.py
    python3 blueprint/build.py

Insertion location: a new \\leanok line right after \\uses{...} (or \\lean{...}
if \\uses is absent), preserving the surrounding indentation. Removal: any
\\leanok line inside a block whose entity is no longer formalized.

Proof binding: prefer \\proves{<label>}; fall back to the most recent labeled
theorem-like environment if a proof has no \\proves.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STATUS_PATH = ROOT / "extraction" / "formalization_data" / "lean_status.json"
SRC_DIR = ROOT / "blueprint" / "src"
ENV_KINDS = ("theorem", "lemma", "corollary", "definition")
THM_LIKE_KINDS = ("theorem", "lemma", "corollary")

LABEL_RE = re.compile(r"\\label\{([a-z]+:\w+)\}")
PROVES_RE = re.compile(r"\\proves\{([a-z]+:\w+)\}")
LEANOK_RE = re.compile(r"^\s*\\leanok\s*$")
USES_RE = re.compile(r"^(\s*)\\uses\{[^}]*\}\s*$")
LEAN_RE = re.compile(r"^(\s*)\\lean\{[^}]*\}\s*$")
ENV_BEGIN_RE = re.compile(r"\\begin\{(" + "|".join(ENV_KINDS) + r")\}")
ENV_END_RE = re.compile(r"\\end\{(" + "|".join(ENV_KINDS) + r")\}")
PROOF_BEGIN_RE = re.compile(r"\\begin\{proof\}")
PROOF_END_RE = re.compile(r"\\end\{proof\}")


def adjust_block(block_lines: list[str], should_have_leanok: bool) -> tuple[list[str], int, int]:
    """Insert or remove \\leanok in the block. Returns (new_lines, added, removed)."""
    has_leanok = any(LEANOK_RE.match(line) for line in block_lines)

    if should_have_leanok and not has_leanok:
        for i, line in enumerate(block_lines):
            m = USES_RE.match(line)
            if m:
                block_lines.insert(i + 1, f"{m.group(1)}\\leanok\n")
                return block_lines, 1, 0
        for i, line in enumerate(block_lines):
            m = LEAN_RE.match(line)
            if m:
                block_lines.insert(i + 1, f"{m.group(1)}\\leanok\n")
                return block_lines, 1, 0
        # Fallback: insert right after \begin{...} with detected indent.
        for i, line in enumerate(block_lines):
            if ENV_BEGIN_RE.search(line) or PROOF_BEGIN_RE.search(line):
                indent = "  "
                for j in range(i + 1, len(block_lines)):
                    if block_lines[j].strip():
                        indent = block_lines[j][: len(block_lines[j]) - len(block_lines[j].lstrip())]
                        break
                block_lines.insert(i + 1, f"{indent}\\leanok\n")
                return block_lines, 1, 0
        return block_lines, 0, 0

    if not should_have_leanok and has_leanok:
        new = [line for line in block_lines if not LEANOK_RE.match(line)]
        return new, 0, len(block_lines) - len(new)

    return block_lines, 0, 0


def make_proof_stub(label: str) -> list[str]:
    return [
        "\n",
        "\\begin{proof}\n",
        f"  \\proves{{{label}}}\n",
        "  \\leanok\n",
        "  Formalized in Lean.\n",
        "\\end{proof}\n",
    ]


def sync_file(tex_path: Path, status: dict) -> dict:
    text = tex_path.read_text(encoding="utf-8")
    proven_labels = set(PROVES_RE.findall(text))
    lines = text.splitlines(keepends=True)
    out: list[str] = []
    i = 0
    last_env_label: str | None = None
    stats = {"env_marks": 0, "env_removes": 0, "proof_marks": 0, "proof_removes": 0,
             "proof_stubs": 0, "missing": [], "in_progress": []}

    while i < len(lines):
        line = lines[i]

        if ENV_BEGIN_RE.search(line):
            kind_match = ENV_BEGIN_RE.search(line)
            env_kind = kind_match.group(1) if kind_match else None
            block = [line]
            j = i + 1
            while j < len(lines) and not ENV_END_RE.search(lines[j]):
                block.append(lines[j])
                j += 1
            if j < len(lines):
                block.append(lines[j])

            label = None
            for ln in block:
                m = LABEL_RE.search(ln)
                if m:
                    label = m.group(1)
                    break

            if label and label in status:
                st = status[label].get("status")
                want_ok = st == "formalized"
                if st == "in_progress":
                    stats["in_progress"].append(label)
                block, added, removed = adjust_block(block, want_ok)
                stats["env_marks"] += added
                stats["env_removes"] += removed
                last_env_label = label
            else:
                if label:
                    stats["missing"].append(label)
                last_env_label = label

            out.extend(block)
            i = j + 1

            # If this is a formalized theorem-like with no associated proof
            # block anywhere, append a stub so the dep graph renders fully.
            if (label and label in status and env_kind in THM_LIKE_KINDS
                    and status[label].get("status") == "formalized"
                    and label not in proven_labels):
                out.extend(make_proof_stub(label))
                proven_labels.add(label)
                stats["proof_stubs"] += 1
            continue

        if PROOF_BEGIN_RE.search(line):
            block = [line]
            j = i + 1
            while j < len(lines) and not PROOF_END_RE.search(lines[j]):
                block.append(lines[j])
                j += 1
            if j < len(lines):
                block.append(lines[j])

            bound = None
            for ln in block:
                m = PROVES_RE.search(ln)
                if m:
                    bound = m.group(1)
                    break
            if not bound:
                bound = last_env_label

            if bound and bound in status:
                want_ok = status[bound].get("status") == "formalized"
                block, added, removed = adjust_block(block, want_ok)
                stats["proof_marks"] += added
                stats["proof_removes"] += removed

            out.extend(block)
            i = j + 1
            continue

        out.append(line)
        i += 1

    new_text = "".join(out)
    if new_text != text:
        tex_path.write_text(new_text, encoding="utf-8")
    return stats


def find_orphan_labels(tex_files: list[Path], status: dict) -> dict[str, list[str]]:
    """Return formalized labels that exist in .tex but not inside any env block.

    These are authoring defects (e.g. a stray \\label{def:NNNX} not wrapped in
    \\begin{definition}...\\end{definition}). Such labels can't get a \\leanok
    until the env wrapper is added.
    """
    formalized = {k for k, v in status.items() if v.get("status") == "formalized"}
    orphans: dict[str, list[str]] = {}
    for tex in tex_files:
        text = tex.read_text(encoding="utf-8")
        all_labels = set(LABEL_RE.findall(text))
        env_labels: set[str] = set()
        for m in re.finditer(
            r"\\begin\{(" + "|".join(ENV_KINDS) + r")\}.*?\\end\{\1\}",
            text, re.DOTALL,
        ):
            env_labels.update(LABEL_RE.findall(m.group(0)))
        local_orphans = sorted((all_labels - env_labels) & formalized)
        if local_orphans:
            orphans[tex.name] = local_orphans
    return orphans


def main() -> int:
    if not STATUS_PATH.exists():
        print(f"error: {STATUS_PATH} not found", file=sys.stderr)
        return 1
    with open(STATUS_PATH) as f:
        status = json.load(f)

    tex_files = sorted(SRC_DIR.glob("chapter*.tex"))
    if not tex_files:
        print(f"error: no chapter*.tex under {SRC_DIR}", file=sys.stderr)
        return 1

    grand = {"env_marks": 0, "env_removes": 0, "proof_marks": 0,
             "proof_removes": 0, "proof_stubs": 0}
    missing: list[str] = []
    in_progress: list[str] = []

    for tex in tex_files:
        s = sync_file(tex, status)
        for k in grand:
            grand[k] += s[k]
        missing.extend(s["missing"])
        in_progress.extend(s["in_progress"])
        print(f"  {tex.name}: +{s['env_marks']} env, +{s['proof_marks']} proof, "
              f"+{s['proof_stubs']} stubs, "
              f"-{s['env_removes'] + s['proof_removes']} removed")

    print()
    print(f"Total inserted: {grand['env_marks']} env + {grand['proof_marks']} proof  "
          f"\\leanok markers, {grand['proof_stubs']} stub proof blocks")
    print(f"Total removed:  {grand['env_removes'] + grand['proof_removes']}")

    formalized = sum(1 for v in status.values() if v.get("status") == "formalized")
    print(f"Status file: {formalized}/{len(status)} entities marked formalized "
          f"({len(in_progress)} in_progress, {len(status) - formalized - len(in_progress)} unformalized)")

    if in_progress:
        print(f"  in_progress (no marker added): {', '.join(sorted(in_progress))}")

    orphans = find_orphan_labels(tex_files, status)
    if orphans:
        print()
        print("WARNING: formalized labels found outside any env block "
              "(missing \\begin{definition|theorem|...} wrapper):")
        for fname, labels in orphans.items():
            for label in labels:
                print(f"  {fname}: \\label{{{label}}} — wrap it in an env to get \\leanok")

    if missing:
        uniq = sorted(set(missing))
        print(f"  {len(uniq)} env labels in TeX have no entry in lean_status.json "
              f"(first 5: {uniq[:5]})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
