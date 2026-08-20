# CPP 2027 Submission — 0pat Exercise XXXVI: Divergence–Period Symmetry on the Zeta Series

## Paper

- Exercise_XXXVI_Divergence_Period_Symmetry.tex — acmart, anonymous
- refs.bib

Compile: `tectonic Exercise_XXXVI_Divergence_Period_Symmetry.tex`

## Content

A single conjugation symmetry S has two eigenspaces on the series
terms 1/n^s = n^{−σ}·e^{−it·ln n} of the zeta function:
- the divergence axis (the real part): ‖n^s‖ = n^{Re s} — the modulus
  is controlled entirely by the divergence axis; the period axis
  contributes |e^{−it ln n}| = 1, never
- the period axis (the imaginary part): exp(iθ)·exp(−iθ) = 1 — phase
  mirror pairs collapse to unit 1
- the divergence axis mirror: r·(1/r) = 1 — numerical mirror pairs
  collapse to unit 1 (log mirror)
- conjugation = period-axis reversal: conj(n^s) = n^{conj s}
- the functional equation ζ(1−s) = 2(2π)^{−s}Γ(s)cos(πs/2)ζ(s) is the
  pairing of the divergent region with the convergent region — the
  mechanism of analytic continuation, machine-checked in mathlib
  (riemannZeta_one_sub)

5 theorems, 0 errors, 0 sorry.

## Artifact

- artifact/formal/proof.lean — the 5-theorem proof
- artifact/README.md — build + theorem inventory + provenance

## Double-blind note

No author / affiliation / email / DOI / repository identifiers.
