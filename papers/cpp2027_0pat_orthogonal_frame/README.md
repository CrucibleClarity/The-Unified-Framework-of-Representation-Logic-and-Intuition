# CPP 2027 Submission — 0pat Exercise XXV: Orthogonal Euler Circles as an Observation Frame

## Paper

- Exercise_XXV_Orthogonal_Euler_Circles.tex — acmart, anonymous
- refs.bib

Compile: `tectonic Exercise_XXV_Orthogonal_Euler_Circles.tex` (or pdflatex with the \Bbbk fix in the preamble)

## Content

Third completed exercise of the 0pat re-formalization program:
- pat insight: the prime axis observed through two orthogonal Euler circles (periodized number lines)
- 0pat re-statement: double-modulus observation algebra
  - coordinate law: CRT — coprime m,n ⟹ Z/(mn) ≃ Z/m × Z/n (ZMod.chineseRemainder)
  - prime factors visible: p | a ⟹ (a : Z/p) = 0
  - distinct primes distinguished: p ≠ q ⟹ (p : Z/q) ≠ 0
  - non-own circle: p^(q−1) ≡ 1 (mod q) — unit of the foreign circle group
  - own circle: complete Fermat a^p ≡ a (mod p) — connects Exercise XXIV
- Lean proof: 7 theorems, 0 errors, 0 sorry, mathlib v4.32.2 only
- Method: genealogy-map path-walking (coordinate (R23,C3)), connects XXIII (CRT factorization) + XXIV (prime circle)

## Artifact

- artifact/formal/proof.lean — the 7-theorem proof (272 lines)
- artifact/README.md — build + theorem inventory + provenance

## Double-blind note

No author / affiliation / email / DOI / repository identifiers.
