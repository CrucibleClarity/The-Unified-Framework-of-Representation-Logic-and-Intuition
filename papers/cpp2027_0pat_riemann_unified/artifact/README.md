# Artifact — 0pat Exercise XXXVII: The Riemann Direction, Unified

## Build

```bash
# Lean 4.32.2 + mathlib v4.32.2
lean proof_unified.lean   # 0 errors, 0 warnings, 0 sorry
```

## Theorems (156, all 0pat)

`proof_unified.lean` = iso 分块 (zeta_*_iso.lean, 27 块独立编译通过) 拼接为
单文件完整证明 + Hardy Z (翻转缺口 1+1b): 156 声明 (124 theorems/lemmas +
32 definitions), 声明级去重 (同名保留首现; zetaUnit ℝ 版重命名
zetaUnitOnLine), 只 import Mathlib。

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
| Zeta conjugation | zeta_conj_of_one_lt_re (Re > 1, series), zeta_conj_of_re_lt_zero (Re < 0, functional equation), zeta_conj_of_critical_strip (0 < Re < 1, Mellin definition penetration), chi_conj, chi_mul_chi_one_sub |
| Re/Im split | zeta_re_conj_symm (even real part), zeta_im_conj_antisymm (odd imaginary part), zeta_re_even_on_line, zeta_im_odd_on_line (critical line), zeta_eq_zero_iff_re_im (zero = common zero) |
| Gamma doubling | cpow_two_half_minus_im (doubling multiplier 2^{1/2−it} = √2·(cos(t·ln2) − i·sin(t·ln2)); phase −t·ln2 linear) |
| Multi-axis phase | term_on_line_explicit (each term n^−(1/2+it) = n^{−1/2}·(cos(t·ln n) − i·sin(t·ln n)); frequency axes ln n) |
| Γ modulus by symmetry | gamma_abs_sq_on_line (|Γ(1/2+it)|² = π/cosh(πt) exactly via reflection + conjugation + sin), sin_pi_half_add_mul_I |
| Explicit χ phase | cpow_two_on_line_explicit, cpow_pi_on_line_explicit (linear phases t·ln2, t·lnπ), sin_pi_quarter_add_mul_I (sin(π/4+iπt/2) explicit; real part positive) |
| Edge cancellation | zero_left_right_bijection (off-line zeros mirror left/right halves via ρ ↦ 1−ρ̄; skeleton of zero-count conservation) |
| Base point i | critical_line_equidistant_basepoint_i (line = perpendicular bisector of i and 1+i), recip_basepoint_i_on_unit_circle (T(z) = 1/(z−i) − 1 sends the line to the unit circle) |
| Base point 1 | on_line_iff_equidistant_base_one (on-line ⟺ equidistance to 0 and −1; critical-line circle = unit circle) |
| Affine base-point shift | affine_image_critical_line_is_line (affine shifts keep the critical line a line; circle view only from inversion) |
| Euler-circle split norm | zero_split_normSq (zero on the split cone Re²−Im² = 0), zero_not_on_euler_circles (zeros avoid both orthogonal Euler circles) |
| p-adic split / zero region | zeta_eq_zero_iff_p_split (zero = common zero of odd/even parts), odd_part_extra_zero_on_imag_axis (extra odd-part zeros on the imaginary axis), riemannZeta_ne_zero_of_re_lt_zero, riemannZeta_ne_zero_of_re_eq_zero, nontrivial_zero_in_critical_strip (nontrivial zeros in 0 < Re < 1) |
| Hardy Z | chi (self-contained Landau multiplier), chi_pair_product (χ(s)·χ(1−s)=1), chi_conj_symm (conj passes through χ), chi_unit_modulus (|χ(1/2+it)|=1), zeta_eq_chi_conj_on_line (critical-line functional equation), hardyZ_conj (conj(Z)=Z, conjugation-reflection symmetry), hardyZ_im_zero (Z real-valued), chi_continuousOn_line, hardyZ_eq_zero_iff (Z=0 ⟺ ζ=0 on the line), hardyZ_continuousOn, hardyZ_zero_between (Re Z(a) < 0 < Re Z(b) ⟹ ∃t∈(a,b), Z(t)=0; intermediate value — every flip records a critical-line zero) |
| Conjugation counting | zero_orbit_counting: zeros form 2-point conjugate pairs on the line, 4-point orbits off the line; orbit_degenerate_iff_on_line, recip_on_critical_circle_iff, zero_orbit_four |
| Zero structure | zeta_zero_reflection, prime_factor_zero, trivial_zero_condition, critical_line_observation |
| i-iteration | i_pow_i_eq_exp_neg_pi_div_two, i_pow_i_ne_i, axis_tick_pow, prime_no_power_decomposition |
| Completed zeta | xi_symmetry₀, xi_symmetry, xi_entire, zeta_series_form, zeta_functional_equation |

## Result

The Riemann direction is machine-checked up to its honest boundary:
the functional equation, zero symmetry, prime-factor zeros on the
imaginary axis, trivial zeros from the trigonometric factor, the
critical-line observation, the real axis as iteration of i
(i^i = e^{−π/2}), the completed zeta structure, and the Hardy Z
function: real-valuedness (conj(Z)=Z) and the intermediate-value
flip-to-zero theorem (a sign change of Z forces a critical-line
zero). The Riemann hypothesis itself is not claimed; the thirty-five
observation records in observation.md document the numerical evidence
and the exact location of the remaining gap (the converse zero
counting: every critical-line zero counted by a flip, matching N(T)).

## Provenance

Original pat insight: src/pat-excercises/exercises/37_riemann_unified/
(merge of XXIV–XXXVI: prime circle, orthogonal Euler circles, split
complex, critical line, intersections, transpose, axes, compression,
divergence axis, divergence–period symmetry).
0pat re-formalization: pure known mathematics, no pat concepts.

## Double-blind

No author / affiliation / email / repository identifiers.

## Stage artifacts (iso/)

`iso/` 包含 22 个隔离文件 (zeta_*_iso.lean) — 每个 = 独立编译通过 (mathlib-only,
0 error 0 sorry) 的阶段成果, 按 0pat 隔离开发纪律先独立验证再合并入 proof.lean。
`iso_hashes.md` = 阶段成果 hash + 时间戳台账 (SHA256 前 16 位, mtime 精确到秒),
与合并文件 hash (claims_manifest.md) 分离保留, 可独立追溯。

## 发布 v2 状态 (2026-08-21)

iso/ 下 28 个隔离文件; 24 个当前环境 0 error 0 sorry (含新增 zeta_continuation_iso.lean)。
proof.lean (合并总) 与新 mathlib 905b95818e API 迁移适配中, 内容以 iso 文件为准。
编译状态表见 iso/ISO_README.md。
