# Artifact — 0pat Exercise XXXVII: The Riemann Direction, Unified

## Build

```bash
# Lean 4.32.2 + mathlib v4.32.2
lean proof.lean   # 0 errors, 0 warnings, 0 sorry
```

## Theorems (98, all 0pat)

Merged from exercises XXIV–XXXVI (original namespaces preserved) plus
new theorems in `RiemannUnifiedObservation`:

| Layer | Representative theorems |
|---|---|
| Prime structure | infinitely_many_primes, fermat_little, card_units_zmod_prime |
| Frame | j_sq, orthogonal_radii, transpose_involutive, transpose_maps_one_to_i |
| Axes/circles | realAxis_inter_imaginaryAxis, realAxis_inter_unitCircle, imaginaryAxis_inter_imaginaryCircle |
| Critical/prime circles | imagAxis_inter_criticalCircle, primeCircle_inter_criticalCircle_ge5 |
| Compression | complex_mul_imag_leaks, split_mul_imag_leaks, leak_sign_is_unit_square |
| Divergence/period | zeta_term_norm_split, period_pair_reduces, divergence_pair_reduces, term_conj_symmetry, functional_equation_bridges, complex_zeta_convergence_region |
| Zeta conjugation | zeta_conj_of_one_lt_re (Re > 1, series), zeta_conj_of_re_lt_zero (Re < 0, functional equation), zeta_conj_of_critical_strip (0 < Re < 1, Mellin definition penetration), chi_conj |
| Zero structure | zeta_zero_reflection, prime_factor_zero, trivial_zero_condition, critical_line_observation |
| i-iteration | i_pow_i_eq_exp_neg_pi_div_two, i_pow_i_ne_i, axis_tick_pow, prime_no_power_decomposition |
| Completed zeta | xi_symmetry₀, xi_symmetry, xi_entire, zeta_series_form, zeta_functional_equation |

## Result

The Riemann direction is machine-checked up to its honest boundary:
the functional equation, zero symmetry, prime-factor zeros on the
imaginary axis, trivial zeros from the trigonometric factor, the
critical-line observation, the real axis as iteration of i
(i^i = e^{−π/2}), and the completed zeta structure. The Riemann
hypothesis itself is not claimed; the twelve observation records in
observation.md document the numerical evidence and the exact location
of the gap.

## Provenance

Original pat insight: src/pat-excercises/exercises/37_riemann_unified/
(merge of XXIV–XXXVI: prime circle, orthogonal Euler circles, split
complex, critical line, intersections, transpose, axes, compression,
divergence axis, divergence–period symmetry).
0pat re-formalization: pure known mathematics, no pat concepts.

## Double-blind

No author / affiliation / email / repository identifiers.
