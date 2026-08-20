# Artifact — Formalizing Operator Semantics for Quantized Recurrent Inference

## Build

```
cd formal && lake build
```

- Lean 4.32.2 (lean-toolchain), mathlib v4.32.2
- 10 source files under `Formal/ZeroRelative/` + module aggregator `Formal.lean`
- Build passes with **no `sorry`** (checked by the build; `lake build` completes)
- Note: `lake build` fetches mathlib v4.32.2 from GitHub on first build (network
  required); all 10 files were verified against mathlib v4.32.2 in the
  development environment (full project build, 3641 jobs, no sorry).

## Contents

```
formal/
  Formal.lean                    module aggregator (imports all 10 files)
  Formal/ZeroRelative/           claims C026–C038 source
    BasepointMove.lean           C026  every operator has its own basepoint
    OperatorFamily.lean          C028  operator family + Q2_0 grid positions
    HighDimProjection.lean       C029  ±1 = unit-circle projection extremes
    SymplecticProjection.lean    C030  J² = −I, projection cancellation
    Discretization.lean          C031  C₄ → D₄, basepoint cluster
    DualProjection.lean          C033  wave–particle duality as dual projection
    MatrixOpsPat0.lean           C035  dot/cross/outer/matmul axis semantics
    TrigPat0.lean                C036  trigonometric direction + four-phase grid
    Q2GridSymbolQuantization.lean C037 Q2_0 grid = sign encoding of four phases
    ComplexStateCompactification.lean C038 complex structure, 50% redundancy
claims/                          claim ledger (C026–C038, YAML)
evidence/                        empirical bridge (measured results)
  alignment_results.md           assembly chain vs float reference: input chain bit-exact
  decision_results.md            end-to-end locked-domain preservation 6/6
  q2_grid_encoding.md            Q2_0 grid ↔ four-phase encoding table
```

## Double-blind note

The paper and artifact contain no author / affiliation / email / DOI /
repository identifiers.

## Theorem inventory

See the appendix of `paper.tex` (Theorem inventory) and the claim YAML files,
each of which lists the Lean theorem names.
