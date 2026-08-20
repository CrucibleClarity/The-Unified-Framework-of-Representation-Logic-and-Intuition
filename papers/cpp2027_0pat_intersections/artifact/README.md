# Artifact — 0pat Exercise XXIX: Complex Plane Intersections

## Build

```bash
# Lean 4.32.2 + mathlib v4.32.2 (LEAN_PATH must include Formal/ZeroRelative build)
lean proof.lean   # 0 errors, 0 warnings, 0 sorry
```

## Theorems (5, all 0pat)

| Theorem | Statement |
|---|---|
| imagAxis_inter_criticalCircle | t·J ∈ criticalCircle ↔ t = 0 (imaginary axis ∩ = {0}) |
| realAxis_inter_primeCircle | lift r ∈ primeCircle p ↔ r² = p ({±√p}) |
| imagAxis_inter_primeCircle | t·J ∈ primeCircle p ↔ t² = p ({±i√p}) |
| prime3Circle_inter_criticalCircle | 3/2 + √3/2·J in both circles |
| primeCircle_inter_criticalCircle_ge5 | p ≥ 5 ⟹ primeCircle p ∩ criticalCircle = ∅ |

## Structural result

Prime circle (radius √p, center 0) meets critical circle (center (1,0),
radius 1) iff p ∈ {2,3}. Proof: z in both ⟹ a = p/2, b² = p(4−p)/4 < 0
for p ≥ 5.

## Provenance

Original pat insight: src/pat-excercises/exercises/29_complex_plane_intersections/
(observe intersections of real axis / imaginary axis / critical circle /
prime circles). Builds on C011 (ComplexAxis), C020 (real axis ∩ critical
circle = {0,2}, prime-2 circle ∩ critical circle = {1±i}).

## Double-blind

No author / affiliation / email / repository identifiers.
