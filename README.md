# CPP 2026 Submission Package — Lean Formalization of the Riemann Direction

## Paper

- `paper.tex` — ACM format (acmart), anonymous, 8 pages target
- `refs.bib` — bibliography

Compile: `pdflatex paper && bibtex paper && pdflatex paper && pdflatex paper`

## Artifact

- `artifact/formal/` — Lean 4 source (20 .lean files, 5285 lines) + lakefile + toolchain
- `artifact/claims/` — claim ledger (25 YAML, C001–C025)
- `artifact/README.md` — build instructions + theorem inventory

Build: `cd artifact/formal && lake build` (mathlib v4.32.2, 3631 jobs, no sorry)

## Submission metadata

- **Title**: Formalizing the Riemann Direction in Lean: Projection-Induced Structure
  Loss, the Circle of Primes, and the Euler Product (C011–C025, all PROVED, no sorry)
- **Author**: Anonymous (double-blind)
- **Category**: CPP (Certified Programs and Proofs) — formalization / verification
- **Keywords**: Lean, formalization, Riemann zeta, Gaussian integers, Euler product,
  projection, intuition
- **Abstract**: (in paper.tex)

## Claims (all PROVED, novelty KNOWN, no sorry)

C011 projection construction / basepoint drift
C012 primes land on translated integer points
C013 1/2 as duality center
C014 sums of two squares
C015 curling (inversion compactness)
C016 lattice-point orbit structure
C017 unique orbit (8 points)
C018 symmetry square root (i)
C019 critical line is a circle
C020 two circles intersection
C021 zero shape (vertical line ↔ circle)
C022 same circle (zero set = critical circle)
C023 prime-circle product p^4
C024 splitting into conjugate Gaussian primes
C025 Euler product = ζ, zero-free region

## Honest boundary (important for reviewers)

- Riemann hypothesis NOT proved.
- All results are classical (novelty: KNOWN); the contribution is the machine-checked
  formalization and the recoverability dichotomy (projection-induced structure loss).
- mathlib's `RiemannHypothesis` is referenced, not proved.

## Provenance

- Published record (DOI) will be linked after acceptance (double-blind)
- Anonymous artifact repository (double-blind): github.com/CrucibleClarity/The-Unified-Framework-of-Representation-Logic-and-Intuition
