# Artifact — The Riemann Hypothesis: A Machine-Checked Verification Map

## Build

```bash
# Lean 4.32.2 + mathlib v4.32.2 (lake build: 3631 jobs, no sorry)
# Files import mathlib + each other; build order:
#   PrimeDriftPositions.lean  (independent)
#   ComplexAxis.lean          (base construction)
#   ZetaEulerProduct.lean     (imports mathlib LSeries + ComplexAxis concepts)
#   Toolkit/CriticalPrimeCircles.lean
#   Toolkit/PatRiemannTwinPrimes.lean
lean --run /dev/null 2>/dev/null; # per-file: lean <file>.lean
```

`#print axioms` on representative theorems yields exactly:
`[propext, Classical.choice, Quot.sound]` — no new axioms, no sorry.

## Theorems (141, all machine-checked)

| File | Theorems | Content |
|---|---|---|
| PrimeDriftPositions.lean | 6 | prime positions in drift frame; inversion dual; p/2 non-integer; irrational axis |
| ComplexAxis.lean | 128 | J²=−1; projection; basepoint drift unobservable; prime circles; UFD uniqueness; critical line ⇔ circle; zero-set circle duality; products; splitting |
| ZetaEulerProduct.lean | 7 | Euler product = ζ (Re s > 1); zero-free region; conditional circle restatement |

## Claims

C011–C025 in the claims ledger: status PROVED, novelty_status KNOWN
(restatements of classical mathematics), per-claim SHA-256 publication.
The Riemann hypothesis is NOT claimed proved; mathlib's
`RiemannHypothesis` remains unproved. The gap is stated exactly in
Section "The gap" of the paper.

## Provenance

Riemann direction: visualization 2026-08-06 (138,067 zeros, Riemann–Siegel
correction, error 9e-4); thinking document 2026-08-07; formalization
session 2026-08-12 (C011–C025). Numerical facts are observational, not
part of any machine-checked statement.

## Double-blind

No author / affiliation / email / repository identifiers.
