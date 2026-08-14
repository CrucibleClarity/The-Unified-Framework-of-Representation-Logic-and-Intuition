/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# 欧拉乘积收敛 (Re s > 1): ∏_p (1 - p⁻ˢ)⁻¹ = Σ_n 1/n^s

ζ(s) 的欧拉乘积表示 (KNOWN: 欧拉 1737)。mathlib 组合:
  * Complex.summable_one_div_nat_cpow: 1 < re s ⟹ Σ 1/n^s 收敛;
  * EulerProduct.eulerProduct_completely_multiplicative_tprod:
    f 完全乘法且 Σ‖f‖ 收敛 ⟹ ∏'_p (1 - f p)⁻¹ = ∑'_n f n。
收敛到的具体值是级数 ∑' 1/n^s (即 ζ(s) 在 Re s > 1 的定义)。
-/

namespace ZeroRelative

/-- f(n) = 1/n^s : ℕ →*₀ ℂ (完全乘法, s ≠ 0)。 -/
noncomputable def zetaEulerF (s : ℂ) (hs0 : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := 1 / (n : ℂ) ^ s
  map_zero' := by
    simp [Complex.zero_cpow hs0]
  map_one' := by
    simp [Complex.one_cpow]
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm, Complex.zero_cpow hs0]
    · by_cases hn : n = 0
      · simp [hn, Complex.zero_cpow hs0]
      · have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm
        have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
        rw [Nat.cast_mul]
        rw [Complex.natCast_mul_natCast_cpow m n s]
        field_simp [(Complex.cpow_ne_zero_iff_of_exponent_ne_zero hs0).2 hm0, (Complex.cpow_ne_zero_iff_of_exponent_ne_zero hs0).2 hn0]

/-- ‖1/n^s‖ = n^(-Re s) — 级数项范数的显式形式。 -/
lemma zetaEulerF_norm (s : ℂ) (hs0 : s ≠ 0) (hne : -s.re ≠ 0) (n : ℕ) :
    ‖zetaEulerF s hs0 n‖ = (n : ℝ) ^ (-s.re) := by
  by_cases hn : n = 0
  · have h0 : (0 : ℝ) ^ (-s.re) = 0 := Real.zero_rpow hne
    simp [zetaEulerF, hn, h0, hs0]
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    simp [zetaEulerF]
    have hnorm : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re := by
      simpa using (Complex.norm_cpow_eq_rpow_re_of_pos hnpos s)
    rw [hnorm]
    rw [← Real.rpow_neg (show 0 ≤ (n : ℝ) from by exact_mod_cast (Nat.zero_le n))]

/-- 欧拉乘积收敛于具体值 (Re s > 1):
∏'_p (1 - 1/p^s)⁻¹ = ∑'_n 1/n^s — ζ(s) 的欧拉乘积表示。 -/
theorem zeta_euler_product (s : ℂ) (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (1 - 1 / (p : ℂ) ^ s)⁻¹) = ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    norm_num at hs
  have hne : -s.re ≠ 0 := by linarith
  have hsum : Summable (fun n : ℕ => ‖zetaEulerF s hs0 n‖) := by
    have hsr : -s.re < -1 := by linarith
    have hsumR : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) :=
      (Real.summable_nat_rpow (p := -s.re)).2 hsr
    simpa [zetaEulerF_norm s hs0 hne] using hsumR
  exact EulerProduct.eulerProduct_completely_multiplicative_tprod (f := zetaEulerF s hs0) hsum


/-! ## 欧拉乘积与非平凡零点的关系

mathlib 有完整黎曼 ζ (riemannZeta : ℂ → ℂ, 解析延拓) 和黎曼猜想陈述
(RiemannHypothesis : Prop — "构造它的一个 term 值一百万美元"):
  RiemannHypothesis := ∀ s, riemannZeta s = 0 → ¬平凡零点 → s ≠ 1 → s.re = 1/2

关系 (KNOWN, 经典分析数论):
  1. 欧拉乘积定义域 (Re s > 1) 是 ζ 的无零点区域: 每个因子 (1-p⁻ˢ)⁻¹ ≠ 0
     ⟹ 乘积 ≠ 0 — 非平凡零点被赶出 Re ≥ 1 (mathlib
     riemannZeta_ne_zero_of_one_le_re);
  2. 零点只能在临界带 0 < Re < 1; 黎曼猜想 (RiemannHypothesis) 断言
     它们在 Re = 1/2 (即 C019-C022 的临界线位置几何, mathlib 定义,
     未证);
  3. 零点 ↔ 素数分布: log ζ = Σ_p Σ_k p⁻ᵏˢ/k (欧拉乘积取对数),
     显式公式 ψ(x) = x - Σ x^ρ/ρ (深层分析, 未形式化)。 -/

/-- riemannZeta 的欧拉乘积 (Re > 1): mathlib 的 ζ (解析延拓) 与我们的
欧拉乘积拼接 — 级数定义 ⟹ 欧拉乘积 (zeta_eq_tsum_one_div_nat_cpow +
zeta_euler_product)。 -/
theorem riemannZeta_euler_product (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = (∏' p : Nat.Primes, (1 - 1 / (p : ℂ) ^ s)⁻¹) := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  exact (zeta_euler_product s hs).symm

/-- 关系 1: 非平凡零点不在 Re ≥ 1 — 欧拉乘积域是无零点区域
(mathlib: riemannZeta_ne_zero_of_one_le_re; 经典来源: 欧拉乘积
因子非零 ⟹ 乘积非零)。 -/
theorem riemannZeta_ne_zero_of_one_le_re (s : ℂ) (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  _root_.riemannZeta_ne_zero_of_one_le_re hs


/-! ## 临界线条件的框架重写 (基点 i 的后继, 0 点视角)

黎曼猜想的断言 (非平凡零点 s.re = 1/2) 在框架语言下:
  s.re = 1/2 ⟺ 1 - s = conj s (绕 1/2 的反射, 反射 = i 的平方, C018)
  ⟺ recip s 在圆心 (1,0) 半径 1 的圆上 (0 点视角, C019 的 ℂ 版)。 -/

/-- 临界线条件 (ℂ 层): Re(s) = 1/2 ⟺ 1 - s = conj s。 -/
theorem critical_line_iff_conj_complex (s : ℂ) : s.re = 1 / 2 ↔ 1 - s = star s := by
  constructor
  · intro h
    apply Complex.ext
    · simp [h]
      norm_num
    · simp
  · intro h
    have hre : (1 - s).re = (star s).re := congrArg Complex.re h
    simp at hre
    nlinarith


/-! ## 数值验证的零点都在临界线圆上

数学事实: 前 10^13 个零点 (外部数值计算) 实部 = 1/2, 因此 (recip 后)
都在临界线圆上。可形式化的是几何条件句 (与零点数量无关):
  若 s 的实部 = 1/2 (数值验证的事实), 则 recip s 在圆上 |1/s - 1| = 1。
外部数值事实本身未在 Lean 中 (mathlib 无具体零点记录)。 -/

/-- 临界线点的 recip 在圆上 (ℂ 层): s.re = 1/2 ⟹ ‖1/s - 1‖ = 1
(数值验证的零点实部 = 1/2, 故它们都在临界线圆上)。 -/
theorem verified_zero_on_circle (s : ℂ) (hs0 : s ≠ 0) (h12 : s.re = 1 / 2) :
    ‖1 / s - 1‖ = 1 := by
  have hdiv : 1 / s - 1 = (1 - s) / s := by
    field_simp [hs0]
  rw [hdiv]
  rw [norm_div]
  have hsq : ‖1 - s‖ ^ 2 = ‖s‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp [h12]
    ring_nf
  have hnorm : ‖1 - s‖ = ‖s‖ := by
    have habs : |‖1 - s‖| = |‖s‖| := (sq_eq_sq_iff_abs_eq_abs ‖1 - s‖ ‖s‖).1 hsq
    rw [abs_of_nonneg (norm_nonneg (1 - s)), abs_of_nonneg (norm_nonneg s)] at habs
    exact habs
  rw [hnorm]
  have hns : ‖s‖ ≠ 0 := by exact norm_ne_zero_iff.mpr hs0
  field_simp [hns]

/-- 零点的版本: 若 s 是 riemannZeta 的零点 (数值验证实部 = 1/2),
则 recip s 在临界线圆上。 -/
theorem zeta_zero_on_circle (s : ℂ) (hs0 : s ≠ 0) (hz : riemannZeta s = 0)
    (h12 : s.re = 1 / 2) : ‖1 / s - 1‖ = 1 :=
  verified_zero_on_circle s hs0 h12

end ZeroRelative
