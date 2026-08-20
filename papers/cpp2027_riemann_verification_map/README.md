# CPP 2027 Submission — The Riemann Hypothesis: A Machine-Checked Verification Map

## Paper

- paper.tex — acmart, anonymous
- refs.bib

Compile: `tectonic paper.tex` (or pdflatex with the \Bbbk fix in the preamble)

## Content

A verification map for the Riemann hypothesis, built for the
credibility-bootstrap problem of independent authors: the first page lists
the main theorem (exact mathlib statement), the axioms (propext / choice /
quot.sound only), the fifteen-link chain C011–C025 with machine-checked
theorem names, the proof dependency graph, and archive anchors.

- 15 claims machine-checked (Lean 4.32.2, mathlib v4.32.2, 0 sorry, 3631 jobs)
- 141 theorems: ComplexAxis 128 + PrimeDriftPositions 6 + ZetaEulerProduct 7
- Status legend per link: LP (machine-checked) / CK (classical, machine-checked restatement)
- The Riemann hypothesis itself: one CONJECTURAL edge, stated exactly, left open (Section "The gap")

## Artifact

- artifact/formal/ZeroRelative/ — ComplexAxis.lean, PrimeDriftPositions.lean, ZetaEulerProduct.lean
- artifact/formal/Toolkit/ — CriticalPrimeCircles.lean, PatRiemannTwinPrimes.lean
- artifact/README.md — build + theorem inventory + provenance

## Double-blind note

No author / affiliation / email / DOI / repository identifiers.
