# CPP 2027 Submission Package — Formalizing Operator Semantics for Quantized Recurrent Inference

## Paper

- `paper.tex` — ACM format (acmart), anonymous, 8 pages
- `refs.bib` — bibliography

Compile: `pdflatex paper && bibtex paper && pdflatex paper && pdflatex paper`

## Artifact

- `artifact/formal/` — Lean 4 source (10 files in `Formal/ZeroRelative/` + `Formal.lean` + lakefile + toolchain), mathlib v4.32.2
- `artifact/claims/` — claim ledger (10 YAML, C026–C038)
- `artifact/evidence/` — empirical bridge: assembly inference chain alignment + decision preservation + Q2_0 grid encoding table

Build: `cd artifact/formal && lake build` (mathlib v4.32.2, no sorry)

## Submission metadata

- **Title**: Formalizing Operator Semantics for Quantized Recurrent Inference: basepoint-relative operators, symplectic projection, and Q2_0 symbol quantization (C026–C038, all PROVED, no sorry)
- **Author**: Anonymous (double-blind)
- **Category**: CPP (Certified Programs and Proofs) — formalization / verification
- **Keywords**: Lean, formalization, quantization, SSM, basepoint, symplectic, operator semantics

## Claims (all PROVED, no sorry)

| Claim | Title |
|---|---|
| C026 | Basepoint move of operators — every operator has its own basepoint (2×2 ≠ 2 on the real axis) |
| C028 | Operator family — all operators with their basepoints; Q2_0 grid = basepoint cluster |
| C029 | Basepoints ±1 = projection of a higher-dimensional structure (unit circle), two positions |
| C030 | Symplectic projection — J² = −I and projection cancellation of the four phases |
| C031 | Discretization — four-phase group C₄, recip = conjugation, D₄, basepoint cluster |
| C033 | Dual projection — wave–particle duality = Re/Im projections of one complex amplitude |
| C035 | Matrix/tensor dot and cross products under operator semantics |
| C036 | Trigonometric direction — cos even (loss), sin odd (kept), basepoints, four-phase grid |
| C037 | Q2_0 four grid points = symbol quantization of the four phases (sign encoding, not homomorphism) |
| C038 | State-matrix complex structure — 50% square redundancy, lossless complex compactification |

Note: claim numbers C027, C032, C034 are reserved in the numbering scheme and have
no separate files; the implemented claims are the 10 files above.
