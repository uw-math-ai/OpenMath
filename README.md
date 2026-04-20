# OpenMath

Semi-autonomous formalization of undergraduate numerical analysis in Lean 4 / Mathlib.

## Overview

Most undergraduate mathematics is present in Mathlib but several big gaps remain: differential geometry, partial differential equations, numerical analysis. We will formalize an undergraduate textbook on numerical analysis for differential equations: *Numerical Methods for Ordinary Differential Equations* (2nd ed., 2008) by J. C. Butcher. Since manual formalization is time-consuming, we will build a semi-autonomous AI agent along the way. The hope is that as the project progresses, we will automate more and more of the formalization process.

## Motivation

There are two motivations:

1. **The formalization itself is valuable**, especially if we upstream some of the results to Mathlib.
2. **Automating mathematical formalization is valuable**, as it unlocks scalable, hallucination-free automated math research.

## Initial experiments

[Clawristotle](https://github.com/Vilin97/Clawristotle) semi-autonomously formalized two theorems in 10 days and 8 days respectively -- one in PDE theory and one in Algebraic Geometry. While not very sophisticated, it was good enough at the scale of ~10k LOC.

## Extracted source material

The textbook has already been extracted into structured, formalization-ready data under [`extraction/`](extraction/). Per-theorem context (statement, LaTeX, dependencies, proof, page) lives in `extraction/formalization_data/entities/<id>.json`; a topological order of what to formalize next is in `extraction/formalization_data/topo_order.json`. See [`extraction/CLAUDE.md`](extraction/CLAUDE.md) for how to consume the data.

## Setup

Requires Lean 4 (v4.28.0) and Mathlib v4.28.0.

```bash
lake update
lake build
```
