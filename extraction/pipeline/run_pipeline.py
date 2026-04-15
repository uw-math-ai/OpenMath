"""Master pipeline orchestrator: runs all extraction phases sequentially."""
from __future__ import annotations

import time
import sys


def run_phase(name: str, func) -> None:
    """Run a pipeline phase with timing."""
    print(f"\n{'='*60}")
    start = time.time()
    try:
        func()
    except Exception as e:
        print(f"  ERROR in {name}: {e}")
        raise
    elapsed = time.time() - start
    print(f"  [{name} completed in {elapsed:.1f}s]")


def main() -> None:
    print("=" * 60)
    print("Butcher ODE Textbook Extraction Pipeline")
    print("=" * 60)

    overall_start = time.time()

    # Phase 1a: Text extraction
    from pipeline.extract_text import main as extract_text_main
    run_phase("Phase 1a: Text Extraction", extract_text_main)

    # Phase 1b: HTML formatting extraction
    from pipeline.extract_html import main as extract_html_main
    run_phase("Phase 1b: HTML Formatting", extract_html_main)

    # Phase 2: Formal statement extraction
    from pipeline.extract_formal import main as extract_formal_main
    run_phase("Phase 2: Formal Statements", extract_formal_main)

    # Phase 3a: Equation extraction
    from pipeline.extract_equations import main as extract_equations_main
    run_phase("Phase 3a: Equations", extract_equations_main)

    # Phase 4a: Cross-reference extraction
    from pipeline.extract_references import main as extract_references_main
    run_phase("Phase 4a: Cross-References", extract_references_main)

    # Phase 4c: Break cycles in merged references (must run before graph)
    from pipeline.break_cycles import main as break_cycles_main
    run_phase("Phase 4c: Break Cycles", break_cycles_main)

    # Phase 4b: Dependency graph
    from pipeline.build_graph import main as build_graph_main
    run_phase("Phase 4b: Dependency Graph", build_graph_main)

    # Phase 5: Markdown knowledge base
    from pipeline.generate_markdown import main as generate_markdown_main
    run_phase("Phase 5: Knowledge Base", generate_markdown_main)

    # Phase 6: LLM LaTeX conversion (stub)
    from pipeline.convert_to_latex import main as convert_to_latex_main
    run_phase("Phase 6: LaTeX Conversion", convert_to_latex_main)

    # Phase 7: Verification
    from pipeline.verify import main as verify_main
    run_phase("Phase 7: Verification", verify_main)

    total_elapsed = time.time() - overall_start
    print(f"\n{'='*60}")
    print(f"Pipeline complete in {total_elapsed:.1f}s")
    print("=" * 60)


if __name__ == "__main__":
    main()
