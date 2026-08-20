# CPP 2027 Submission — 0pat Exercise XXXII: Imaginary-Axis Coefficient Type and the Origin

## Paper

- Exercise_XXXII_Axis_Coefficient_Origin.tex — acmart, anonymous
- refs.bib

Compile: `tectonic Exercise_XXXII_Axis_Coefficient_Origin.tex`

## Content

Origin computation with explicit imaginary-axis coefficient type:
- natural coefficients (discrete axis {n·i : n ∈ ℕ}): real ∩ imag = {(0,0)}
  (solve x = n·i ⟹ x=0 ∧ n=0)
- imaginary-part / real coefficients (continuous {t·i : t ∈ ℝ}):
  real ∩ imag = {(0,0)} (solve x = t·i ⟹ x=0 ∧ t=0)
- transposition: T(real axis) = imaginary axis (real continuous coefficients)
- transposition preserves natural coefficients (natural imaginary → natural real)
- origin = (0,0) under both conventions; 4 theorems, 0 errors, 0 sorry

## Artifact

- artifact/formal/proof.lean — the 4-theorem proof (175 lines)
- artifact/README.md — build + theorem inventory + provenance

## Double-blind note

No author / affiliation / email / DOI / repository identifiers.
