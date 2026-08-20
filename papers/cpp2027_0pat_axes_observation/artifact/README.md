# Artifact — 0pat Exercise XXXI: Real and Imaginary Axes Observation

## Build

```bash
# Lean 4.32.2 + mathlib v4.32.2
lean proof.lean   # 0 errors, 0 warnings, 0 sorry
```

## Theorems (5, all 0pat)

| Theorem | Statement |
|---|---|
| realAxis_inter_imaginaryAxis | realAxis ∩ imaginaryAxis = {(0,0)} |
| realAxis_inter_unitCircle | realAxis ∩ unitCircle = {⟨1,0⟩, ⟨−1,0⟩} |
| realAxis_inter_imaginaryCircle | realAxis ∩ imaginaryCircle = ∅ |
| imaginaryAxis_inter_unitCircle | imaginaryAxis ∩ unitCircle = ∅ |
| imaginaryAxis_inter_imaginaryCircle | imaginaryAxis ∩ imaginaryCircle = {⟨0,1⟩, ⟨0,−1⟩} |

## Observed conclusion

Axes intersect at (0,0) — obtained by solving equations. Units ±1
(real axis, radius-1 circle) and ±i (imaginary axis, radius-i circle)
lie on their own axes; cross-intersections empty.

## Provenance

Original pat insight: src/pat-excercises/exercises/31_real_imag_axes/
(user instruction: observe the axes through the Euler circles by solving
equations, not by definitions).
0pat re-formalization: pure known mathematics, no pat concepts.

## Double-blind

No author / affiliation / email / repository identifiers.
