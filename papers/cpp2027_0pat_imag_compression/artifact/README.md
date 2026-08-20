# Artifact — 0pat Exercise XXXIII: Imaginary Part Compression

## Build

```bash
# Lean 4.32.2 + mathlib v4.32.2
lean proof.lean   # 0 errors, 0 warnings, 0 sorry
```

## Theorems (5, all 0pat)

| Theorem | Statement |
|---|---|
| complex_imag_axis_coefficient | z = t·I ⟺ z.re = 0 ∧ z.im = t |
| complex_mul_imag_leaks | re((a+bI)(c+dI)) = ac − bd |
| complex_mul_cross_stays_imag | im((a+bI)(c+dI)) = ad + bc |
| split_mul_imag_leaks | re((a,bj)(c,dj)) = ac + bd |
| leak_sign_is_unit_square | I·I = −1 ∧ j·j = +1 |

## Result

Compressing the imaginary part into a coefficient axis has one
consequence: the product of two imaginary coefficients leaks into the
real part, with sign equal to the square of the unit (−1 in ℂ, +1 in
the split frame). Cross terms stay imaginary.

## Provenance

Original pat insight: src/pat-excercises/exercises/33_imag_coefficient_compression/
(the imaginary axis shows only real coefficients of the imaginary part;
the product of imaginary parts appears elsewhere under compression).
0pat re-formalization: pure known mathematics, no pat concepts.

## Double-blind

No author / affiliation / email / repository identifiers.
