# CPP 2027 Submission — 0pat Exercise XXXI: Observing the Real and Imaginary Axes through the Euler Circles

## Paper

- Exercise_XXXI_Real_Imag_Axes.tex — acmart, anonymous
- refs.bib

Compile: `tectonic Exercise_XXXI_Real_Imag_Axes.tex`

## Content

Observational determination (by solving equations, not definitions) of
how the real and imaginary axes sit in the orthogonal Euler circle frame:
- real axis ∩ imaginary axis = {(0,0)} (solve ⟨a,0⟩=⟨0,b⟩)
- real axis ∩ radius-1 circle = {±1} (solve a²=1)
- real axis ∩ radius-i circle = ∅ (a²=−1 no real solution)
- imaginary axis ∩ radius-1 circle = ∅ (−b²=1 no real solution)
- imaginary axis ∩ radius-i circle = {±i} (solve −b²=−1)
- Observed conclusion: axes meet at (0,0); i is the unit of the
  radius-i circle on its own axis, not the axes' intersection
- 5 theorems, 0 errors, 0 sorry

## Artifact

- artifact/formal/proof.lean — the 5-theorem proof (190 lines)
- artifact/README.md — build + theorem inventory + provenance

## Double-blind note

No author / affiliation / email / DOI / repository identifiers.
