# Artifact — 0pat Exercise XXXII: Axis Coefficient Type and Origin

## Build

```bash
# Lean 4.32.2 + mathlib v4.32.2
lean proof.lean   # 0 errors, 0 warnings, 0 sorry
```

## Theorems (4, all 0pat)

| Theorem | Statement |
|---|---|
| origin_natural_coefficients | realAxis ∩ naturalImaginaryAxis = {0} (n ∈ ℕ) |
| origin_imaginary_part | realAxis ∩ imaginaryAxis = {0} (t ∈ ℝ) |
| transpose_realAxis_eq_imaginaryAxis | transpose '' realAxis = imaginaryAxis |
| transpose_natural_imaginary_is_natural_real | transpose preserves ℕ coefficients |

## Result

The origin is (0,0) under both coefficient conventions (natural and
imaginary-part). The transposition maps the real axis onto the
imaginary axis with continuous coefficients; natural coefficients are
preserved by transposition.

## Provenance

Original pat insight: src/pat-excercises/exercises/32_axis_coefficients_origin/
(user instruction: label coefficient types when solving — imaginary axis
has natural coefficients but represents the imaginary part; compute the
origin under both conventions; prove the transposition).
0pat re-formalization: pure known mathematics, no pat concepts.

## Double-blind

No author / affiliation / email / repository identifiers.
