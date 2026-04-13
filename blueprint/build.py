#!/usr/bin/env python3
"""Build the blueprint web output with increased recursion limit.

plasTeX can hit Python's default recursion limit (1000) when processing
large documents with deep dependency graphs. This wrapper increases it.

Usage: python blueprint/build.py
"""
import sys
import os

sys.setrecursionlimit(10000)

# Ensure TeX is on PATH
tex_path = "/usr/local/texlive/2026basic/bin/universal-darwin"
if os.path.isdir(tex_path):
    os.environ["PATH"] = tex_path + ":" + os.environ.get("PATH", "")

os.chdir(os.path.join(os.path.dirname(__file__), "src"))

from plasTeX.client import plastex
sys.argv = ["plastex", "-c", "plastex.cfg", "web.tex"]
plastex()
