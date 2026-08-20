# Artifact — 0pat Exercise XXVI: Zero Reflection Symmetry

## Build

```bash
# Lean 4.32.2 + mathlib v4.32.2
lean proof.lean   # 0 errors, 0 warnings, 0 sorry
```

## Theorems (3, all 0pat)

| Theorem | Statement |
|---|---|
| zeta_zero_reflection | ζ(s)=0 ∧ s ≠ −n ∧ s ≠ 1 ⟹ ζ(1−s)=0 (rw functional equation + ring) |
| zeta_zero_strip_reflection | ζ(s)=0 ∧ 0<Re s<1 ⟹ ζ(1−s)=0 ∧ 0<Re(1−s)<1 (sub_re + linarith) |
| zeta_zero_offline_pair | + Re s ≠ 1/2 ⟹ 1−s ≠ s (off-line zeros occur in pairs) |

## Position in the verification map

Left bank (C025: Euler product, zero-free region Re ≥ 1) — FIRST SPAN
MATERIAL (this file: functional-equation corollaries) — right bank
(C019–C022: critical line ⟺ critical circle). The span remains open:
reflection permits off-line pairs; RH denies them.

## Provenance

Original pat insight: src/pat-excercises/exercises/26_zeta_zero_reflection/
(the "middle span" of the Riemann bridge needs analytic tools; mathlib's
riemannZeta_one_sub is the only known analytic material connecting the banks).
0pat re-formalization: pure mathlib, no pat concepts.

## Double-blind

No author / affiliation / email / repository identifiers.
