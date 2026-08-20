# CPP 2027 Submission — 0pat Exercise XXXIII: The Imaginary Part Compressed into a Coefficient Axis

## Paper

- Exercise_XXXIII_Imag_Compression.tex — acmart, anonymous
- refs.bib

Compile: `tectonic Exercise_XXXIII_Imag_Compression.tex`

## Content

What happens when the imaginary part is compressed into a coefficient
axis (the axis shows coefficients, not the unit i):
- axis point = coefficient × unit: z = t·i ⟺ re=0 ∧ im=t
- ℂ: real part of (a+bi)(c+di) = ac − bd — the product of imaginary
  coefficients bd leaks to the real part with sign − (i² = −1)
- cross terms stay imaginary: im = ad + bc
- split frame: real part of (a+bj)(c+dj) = ac + bd (sign +, j² = +1)
- leak sign = unit square: i·i = −1 vs j·j = +1
- 5 theorems, 0 errors, 0 sorry

## Artifact

- artifact/formal/proof.lean — the 5-theorem proof (95 lines)
- artifact/README.md — build + theorem inventory + provenance

## Double-blind note

No author / affiliation / email / DOI / repository identifiers.
