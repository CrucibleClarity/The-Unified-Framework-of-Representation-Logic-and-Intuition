# CPP 2027 Submission — 0pat Exercise XXVII: Split-Complex Numbers (Imaginary-Radius Orthogonal Euler Circles)

## Paper

- Exercise_XXVII_Split_Complex.tex — acmart, anonymous
- refs.bib

Compile: `tectonic Exercise_XXVII_Split_Complex.tex`

## Content

Formal implementation of the radius-1 / radius-i orthogonal Euler circle frame:
- split-complex host: a + bj, j² = +1, pseudo-norm ‖z‖² = a² − b²
- radius-i circle exists: ‖j‖² = −1 (impossible in ℂ: |z| = i has no solution)
- orthogonality: 1² + i² = 0 (split-metric concentric orthogonality)
- conjugate hyperbolas disjoint (coordinate pair, not one circle)
- observation contrast: every odd prime is a split pseudo-norm
  p = ((p+1)/2)² − ((p−1)/2)², vs ℂ Fermat two-squares (only p ≡ 1,2 mod 4)
- 7 theorems, 0 errors, 0 sorry; self-built 30-line standard structure

## Artifact

- artifact/formal/proof.lean — the 7-theorem proof (135 lines)
- artifact/README.md — build + theorem inventory + provenance

## Double-blind note

No author / affiliation / email / DOI / repository identifiers.
