# Artifact — 0pat Exercise XXX: Transpose and Origin

## Build

```bash
# Lean 4.32.2 + mathlib v4.32.2
lean proof.lean   # 0 errors, 0 warnings, 0 sorry
```

## Theorems (7, all 0pat)

| Theorem | Statement |
|---|---|
| transpose_involutive | T(T z) = z |
| transpose_maps_one_to_i | T(1) = i |
| transpose_origin_fixed | T(0) = 0 — the origin is fixed |
| transpose_maps_unit_to_imaginary | ‖z‖² = 1 ⟹ ‖Tz‖² = −1 |
| transpose_maps_imaginary_to_unit | ‖z‖² = −1 ⟹ ‖Tz‖² = 1 |
| lattice_unique_unit | a²−b² = 1 ⟹ (a,b) = (1,0) |
| lattice_unique_imaginary | b²−a² = 1 ⟹ (a,b) = (0,1) |

## Result

The origin of the orthogonal Euler circle frame is (0,0): the common
center of the conjugate hyperbolas a²−b² = ±1, fixed by the
transposition. The units 1 and i are the unique lattice points of their
circles, transposes of each other — not the origin.

## Provenance

Original pat insight: src/pat-excercises/exercises/30_transpose_origin/
(prove the transposition, then determine the origin when the imaginary
axis is the imaginary-unit-coefficient axis).
0pat re-formalization: pure known mathematics, no pat concepts.

## Double-blind

No author / affiliation / email / repository identifiers.
