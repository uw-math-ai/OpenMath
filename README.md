# OpenMath

Semi-autonomous formalization of undergraduate numerical analysis in Lean 4 / Mathlib.

## Overview

Most undergraduate mathematics is present in Mathlib but several big gaps remain: differential geometry, partial differential equations, numerical analysis. We will formalize an undergraduate textbook on numerical analysis for differential equations: [*A First Course in the Numerical Analysis of Differential Equations*](https://www.cambridge.org/highereducation/books/a-first-course-in-the-numerical-analysis-of-differential-equations/7B2E51E3C75B48A985992D2B20E1B9A7). Since manual formalization is time-consuming, we will build a semi-autonomous AI agent along the way. The hope is that as the project progresses, we will automate more and more of the formalization process.

## Motivation

There are two motivations:

1. **The formalization itself is valuable**, especially if we upstream some of the results to Mathlib.
2. **Automating mathematical formalization is valuable**, as it unlocks scalable, hallucination-free automated math research.

## Initial experiments

[Clawristotle](https://github.com/uw-math-ai/Aristotle) semi-autonomously formalized two theorems in 10 days and 8 days respectively -- one in PDE theory and one in Algebraic Geometry. While not very sophisticated, it was good enough at the scale of ~10k LOC.

## Setup

Requires Lean 4 (v4.28.0) and Mathlib v4.28.0.

```bash
lake update
lake build
```
