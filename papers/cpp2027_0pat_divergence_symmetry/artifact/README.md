# Artifact — 0pat Exercise XXXVI: Divergence–Period Symmetry on the Zeta Series

## Build

```bash
# Lean 4.32.2 + mathlib v4.32.2
lean proof.lean   # 0 errors, 0 warnings, 0 sorry
```

## Theorems (5, all 0pat)

| Theorem | Statement |
|---|---|
| zeta_term_norm_split | ‖n^s‖ = n^(Re s) for n > 0 — modulus = divergence factor |
| period_pair_reduces | exp(θ)·exp(−θ) = 1 — period-axis mirror pair collapses |
| divergence_pair_reduces | r·(1/r) = 1 (r ≠ 0) — divergence-axis mirror pair collapses |
| term_conj_symmetry | conj(n^s) = n^(conj s) for n > 0 — conjugation is period-axis reversal |
| functional_equation_bridges | ζ(1−s) = 2(2π)^(−s)Γ(s)cos(πs/2)ζ(s) — mathlib riemannZeta_one_sub |

## Result

Each series term 1/n^s = n^(−σ)·e^(−it·ln n) is a product of two
eigenspaces of one conjugation symmetry: the divergence axis (real
part) controls the modulus; the period axis (imaginary part) has unit
modulus and is reversed by conjugation. Mirror pairs collapse to unit 1
on both axes. The functional equation pairs the divergent region with
the convergent region through the same symmetry — analytic continuation
as the symmetry's mechanism.

## Provenance

Original pat insight: src/pat-excercises/exercises/36_divergence_period_symmetry/
(divergence axis (1) and period axis (i) as the two eigenspaces of one
conjugacy symmetry; the zeta series realizes the pairing as the
functional equation).
0pat re-formalization: pure known mathematics, no pat concepts.

## Double-blind

No author / affiliation / email / repository identifiers.
