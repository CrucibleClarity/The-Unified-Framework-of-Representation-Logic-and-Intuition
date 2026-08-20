# Artifact — 0pat Exercise XXVIII: Split-Complex Critical Line Observation

## Build

```bash
# Lean 4.32.2 + mathlib v4.32.2
lean proof.lean   # 0 errors, 0 warnings, 0 sorry
```

## Theorems (6, all 0pat)

| Theorem | Statement |
|---|---|
| inv_mul_self | z⁻¹ z = 1 when ‖z‖² ≠ 0 (split inverse) |
| critical_line_pseudonorm | ‖1/2 + tj‖² = 1/4 − t² |
| threshold_timelike | t² < 1/4 ⟹ ‖z‖² > 0 (radius-1 region) |
| threshold_spacelike | t > 1/2 ⟹ ‖z‖² < 0 (radius-i region) |
| zero_observation_spacelike | |t| > 1/2 ⟹ ‖z‖² < 0 (known zeros all spacelike) |
| recip_critical_line_hyperbola | recip(1/2 + tj) lies on (a−1)² − b² = 1 |

## Dual structure

Complex frame (C019–C022): recip(critical line) = circle (a−1)² + b² = 1.
Split frame (this file): recip(critical line) = hyperbola (a−1)² − b² = 1.
Same reciprocal map, two hosts; center (1,0) and radius 1 unchanged.

## Provenance

Original pat insight: src/pat-excercises/exercises/28_split_complex_critical_line/
(observe the critical line through the imaginary-radius Euler circles).
0pat re-formalization: pure known mathematics, no pat concepts.

## Double-blind

No author / affiliation / email / repository identifiers.
