# Artifact — 0pat Exercise XXVII: Split-Complex Numbers

## Build

```bash
# Lean 4.32.2 + mathlib v4.32.2
lean proof.lean   # 0 errors, 0 warnings, 0 sorry
```

## Theorems (7, all 0pat)

| Theorem | Statement |
|---|---|
| j_sq | j² = 1 (defining algebra, contrast ℂ J² = −1) |
| normSq_mul | ‖zw‖² = ‖z‖²‖w‖² (pseudo-norm multiplicativity) |
| imaginary_radius_circle | ‖j‖² = −1 (radius-i circle nonempty) |
| real_radius_circle | ‖1‖² = 1 |
| orthogonal_radii | 1 + (−1) = 0 (radii orthogonality in split metric) |
| circles_disjoint | ¬∃ z, ‖z‖² = 1 ∧ ‖z‖² = −1 (conjugate hyperbolas) |
| odd_prime_is_split_norm | every odd prime p = ((p+1)/2)² − ((p−1)/2)² |

## Position

Imaginary-radius orthogonal Euler circles (pat insight 2026-08-21):
host = split-complex numbers (standard mathematics, self-built 30 lines).
First observation: split frame does not discriminate primes (all odd
primes are pseudo-norms), vs complex frame (Fermat two-squares, only
p ≡ 1,2 mod 4).

## Provenance

Original pat insight: src/pat-excercises/exercises/27_split_complex/
0pat re-formalization: pure known mathematics (split-complex is a standard
structure), no pat concepts.

## Double-blind

No author / affiliation / email / repository identifiers.
