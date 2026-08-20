# CPP 2027 Submission — 0pat Exercise XXVI: Zero Reflection Symmetry (First Analytic Material of the Riemann Bridge)

## Paper

- Exercise_XXVI_Zero_Reflection.tex — acmart, anonymous
- refs.bib

Compile: `tectonic Exercise_XXVI_Zero_Reflection.tex`

## Content

First analytic theorem of the Riemann-direction chain:
- functional equation (mathlib riemannZeta_one_sub): ζ(1−s) = 2(2π)^(−s) Γ(s) cos(πs/2) ζ(s)
- corollary 1: zero reflection — ζ(s)=0 ⟹ ζ(1−s)=0 (symmetric about Re = 1/2)
- corollary 2: reflection stays in the critical strip
- corollary 3: off-line zeros (Re s ≠ 1/2) occur in pairs
- positional meaning: first material of the open span between the
  Euler-product bank (C025) and the geometric bank (C019–C022)

## Artifact

- artifact/formal/proof.lean — the 3-theorem proof (62 lines)
- artifact/README.md — build + theorem inventory + provenance

## Double-blind note

No author / affiliation / email / DOI / repository identifiers.
