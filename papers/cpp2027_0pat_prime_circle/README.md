# CPP 2027 Submission — 0pat Exercise XXIV: The Prime Axis as a Circle (Fermat's Little Theorem)

## Paper

- paper.tex — acmart, anonymous
- refs.bib

Compile: `pdflatex paper && bibtex paper && pdflatex paper && pdflatex paper`

## Content

Second completed exercise of the 0pat re-formalization program:
- pat insight: prime axis, periodized, is a circle; observable in the Euler-circle view without the complex plane
- 0pat re-statement: algebra of the multiplicative circle group (Z/pZ)^×
  - circle size: |(Z/pZ)^×| = p − 1
  - circle algebra: Fermat's little theorem (coprime form a^(p−1) ≡ 1, complete form a^p ≡ a)
  - global structure: infinitely many primes
- Lean proof: 4 theorems, 0 errors, 0 sorry, mathlib v4.32.2 only (no pat concepts)
- Method: genealogy-map path-walking (coordinate (R23,C3), no complex plane)

## Artifact

- artifact/formal/proof.lean — the 4-theorem proof (212 lines)
- artifact/README.md — build + theorem inventory + provenance

## Double-blind note

No author / affiliation / email / DOI / repository identifiers.
