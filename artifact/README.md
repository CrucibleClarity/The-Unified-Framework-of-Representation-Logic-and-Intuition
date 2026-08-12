# CPP 2026 Artifact — Lean Formalization of the Riemann Direction (C011–C025)

## Overview

Machine-checked Lean 4 / mathlib formalization of classical results in the Riemann
direction. All claims C011–C025 are PROVED, with no `sorry`, full `lake build` passes.

## Content

```
formal/Formal/ZeroRelative/
  ComplexAxis.lean        projection construction, basepoint drift, inversion,
                          prime-circle structure, critical-line geometry,
                          recoverability theorem
  ZetaEulerProduct.lean   Euler product, identification with riemannZeta,
                          zero-free region
  Heap.lean               heap laws, retract group (support)
  TorsorHeap.lean         torsor–heap correspondence (support)
  ... (20 files total)
claims/ZeroRelative/
  C011.yaml .. C025.yaml  claim ledger (statement / formalization / novelty)
lakefile.toml             build configuration (mathlib v4.32.2)
lean-toolchain            Lean version pin
```

## Build instructions

Requires: Lean 4, mathlib v4.32.2 (see `lean-toolchain`).

```bash
cd formal
lake build          # full build, 3631 jobs, no errors, no sorry
```

To verify absence of `sorry`:

```bash
grep -r "sorry" Formal/ZeroRelative/*.lean
# expected: no output (all theorems PROVED)
```

## Theorem highlights (Lean identifiers)

| Theorem | Lean name |
|---|---|
| $J^2 = -1$ | `J_sq` |
| projection drops multiplication | `proj_mul_not_preserved` |
| basepoint drift unobservable | `proj_chain_basepoint_independent` |
| sums of two squares | `prime_two_axis` (reuses `Nat.Prime.sq_add_sq`) |
| unique orbit (8 points) | `prime_sq_add_sq_unique` |
| norm multiplicative | `norm_mul` |
| inversion involution | `recip_involutive` |
| critical line is a circle | `critical_line_is_circle` |
| recoverability dichotomy | `proj_not_recoverable`, `proj_recoverable_symmetry`, `projection_recovery_theorem` |
| Euler product = ζ | `zeta_euler_product`, `riemannZeta_euler_product` |
| zero-free region | `riemannZeta_ne_zero_of_one_le_re` |

## Honest boundary

The Riemann hypothesis is NOT proved. All results are restatements of classical
mathematics (novelty: KNOWN). The critical-line geometry is an algebraic restatement
of the functional-equation symmetry.

## Provenance

Zenodo DOI: 10.5281/zenodo.21897167 (full paper)
Zenodo DOI: 10.5281/zenodo.21896990 (technical record)
