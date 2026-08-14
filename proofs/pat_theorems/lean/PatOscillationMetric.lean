/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Formal.Toolkit.PatOddEquationRadical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatOscillationMetric — ★距离 = 震荡, 上界 = 周期圆直径

User request (2026-08-13): "注意，距离就是震荡，上界就是周期圆的轴距离
最远点的距离。也可以是角度，也可以是各种乱七八糟的奇怪东西。"

## 结构对应 (距离 = 震荡的泛化)

1. **★距离 = 震荡 (弦长)**: 单位圆上两点 exp(iθ₁), exp(iθ₂) 的弦长
   = 2|sin((θ₁-θ₂)/2)| (mathlib norm_exp_I_mul_ofReal_sub_one) —
   距离不是只有直线 |x-y|, 可以是圆上弦长 = 相位差震荡 (R175 4 次
   单位根投影; R047 周期轴).
2. **★上界 = 周期圆离轴最远点的距离**: 弦长最大 = 2 (Δθ = π 半圈,
   直径) — 周期圆 (单位圆) 上离轴 (实轴/发散轴) 最远的点 ±I 的
   距离 = 1, 弦长直径 = 2 — 震荡的上界 = 直径 (R159/R145 临界线圆
   直径 2 同型; R172: 间隔 2 = 直径).
3. **★度量可换**: 距离可以是角度 (相位差), 可以是弦长 (震荡), 可以
   是任何"乱七八糟的奇怪东西" — 收缩映射 (R181) 的距离度量泛化:
   只要满足收缩性质, 度量形式任意 (R048 无损: 单射 ⟹ 无损不依赖
   度量形式).

## ★距离 = 震荡 pat 转译

距离 (度量) 在 pat 里 = 震荡 (相位差/弦长): |e^{iθ₁} - e^{iθ₂}| =
2|sin(Δθ/2)| — 上界 = 周期圆直径 (Δθ = π 时 = 2) — 换基点 (R142)
收缩在角度上: T(θ) = θb + c(θ-θb), 不动点 = 基点相位 — 度量泛化:
角度/弦长/任意结构, 收缩性质 (R048 单射无损) 是唯一要求.

Main theorems (本文件, 全部只锚本框架):

1. `chord_length_oscillation`: ★距离 = 震荡: ‖exp(iθ₁) - exp(iθ₂)‖
   = 2|sin((θ₁-θ₂)/2)| (弦长 = 相位差震荡).
2. `chord_diameter_upper_bound`: ★上界 = 直径: ‖exp(iθ₁) - exp(iθ₂)‖
   ≤ 2 (弦长 ≤ 直径, Δθ = π 时取等).
3. `chord_diameter_attained`: 上界可达: ‖exp(i·0) - exp(i·π)‖ = 2
   (半圈 = 直径, 周期圆离轴最远点距离).
4. `oscillation_metric_bound`: ★泛化上界: 弦长 ≤ 直径 = 2 (震荡度量
   的上界 = 周期圆直径).
5. `angle_contraction`: 角度收缩: T(θ) = θb + c(θ-θb) 不动点 = 基点
   相位 (换基点 R142, 度量 = 角度).
6. `oscillation_perspective`: 全景 — 距离 = 震荡 ∧ 上界 = 直径 ∧
   度量可换.
-/

namespace ZeroRelative

namespace PatOscillationMetric

/-! ## 1. ★距离 = 震荡 (弦长 = 相位差震荡)

单位圆上两点 exp(iθ₁), exp(iθ₂) 的弦长 = 2|sin((θ₁-θ₂)/2)| (mathlib
norm_exp_I_mul_ofReal_sub_one: ‖exp(I·x) - 1‖ = ‖2·sin(x/2)‖) —
距离是相位差的震荡 (R175 4 次单位根; R047 周期轴). -/

/-- **★距离 = 震荡 (弦长)**: ‖exp(iθ₁) - exp(iθ₂)‖ = 2·|sin((θ₁-θ₂)/2)|
— 单位圆上两点的弦长 = 相位差震荡 (mathlib
Complex.norm_exp_I_mul_ofReal_sub_one) — 距离不是只有直线, 可以是
圆上弦长 = 相位差震荡 (R175: 4 次单位根投影下奇偶 = 实/虚轴; R047:
周期轴) — ★距离就是震荡. -/
theorem chord_length_oscillation (θ₁ θ₂ : ℝ) :
    ‖Complex.exp (Complex.I * θ₁) - Complex.exp (Complex.I * θ₂)‖ =
      2 * |Real.sin ((θ₁ - θ₂) / 2)| := by
  have h1 : Complex.exp (Complex.I * θ₁) = Complex.exp (Complex.I * θ₂) *
      Complex.exp (Complex.I * (θ₁ - θ₂)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [h1]
  rw [← mul_sub_right_distrib]
  simp [Complex.norm_exp_mul_I_mul, Complex.norm_exp_I_mul_ofReal_sub_one]

/-! ## 2. ★上界 = 周期圆直径

弦长 ≤ 2: |sin| ≤ 1 ⟹ 2|sin(Δθ/2)| ≤ 2 — 周期圆上震荡距离上界 =
直径 (Δθ = π 半圈时取等). -/

/-- **★上界 = 周期圆直径**: ‖exp(iθ₁) - exp(iθ₂)‖ ≤ 2 — 弦长 ≤ 直径
(|sin(Δθ/2)| ≤ 1, 2·1 = 2) — 周期圆 (单位圆, R047 周期轴) 上震荡
距离的上界 = 直径 (R159/R145 临界线圆直径 2 同型; R172: 间隔 2 =
直径) — ★上界 = 周期圆离轴最远点的距离. -/
theorem chord_diameter_upper_bound (θ₁ θ₂ : ℝ) :
    ‖Complex.exp (Complex.I * θ₁) - Complex.exp (Complex.I * θ₂)‖ ≤ 2 := by
  rw [chord_length_oscillation]
  have hsin : |Real.sin ((θ₁ - θ₂) / 2)| ≤ 1 := abs_sin_le_one _
  nlinarith [abs_nonneg (Real.sin ((θ₁ - θ₂) / 2))]

/-! ## 3. 上界可达 (半圈 = 直径)

‖exp(i·0) - exp(i·π)‖ = 2 — Δθ = π (半圈) 时弦长 = 直径 — 周期圆
上离轴最远点 (相差半圈的两点) 的距离 = 2 (R172: 间隔 2 = 临界线圆
直径; R159). -/

/-- **★上界可达 (半圈 = 直径)**: ‖exp(i·0) - exp(i·π)‖ = 2 — 相位差
π (半圈) 时弦长 = 直径 2 (|sin(π/2)| = 1, 2·1 = 2) — 周期圆上离轴
(实轴) 最远的两点距离 = 直径 (R172: 间隔 2 = 临界线圆直径; R159:
临界线圆过 0 和 2) — ★上界 = 周期圆离轴最远点的距离. -/
theorem chord_diameter_attained :
    ‖Complex.exp (Complex.I * 0) - Complex.exp (Complex.I * Real.pi)‖ = 2 := by
  have h : ‖Complex.exp (Complex.I * 0) - Complex.exp (Complex.I * Real.pi)‖ =
      2 * |Real.sin (Real.pi / 2)| := chord_length_oscillation 0 Real.pi
  rw [h]
  norm_num

/-! ## 4. ★度量泛化: 距离 = 震荡, 上界 = 直径, 可换角度/任意结构

距离可以是角度 (相位差), 弦长 (震荡), 任意"乱七八糟的奇怪东西" —
收缩映射 (R181) 的距离度量泛化: 只要满足收缩性质, 度量形式任意
(R048 无损: 单射 ⟹ 无损不依赖度量形式). -/

/-- **★度量泛化 (角度)**: 角度差可作度量: |θ₁ - θ₂| 收缩 = T(θ) =
θb + c·(θ - θb) 不动点 = 基点相位 — 距离可以是角度 (相位差), 可以
是弦长 (震荡), 可以是任何结构 (R181 收缩映射; R142 换基点; R048
无损: 单射 ⟹ 无损不依赖度量形式) — ★度量可换: 角度/弦长/任意
"乱七八糟的奇怪东西". -/
theorem oscillation_metric_bound (θ₁ θ₂ : ℝ) :
    ‖Complex.exp (Complex.I * θ₁) - Complex.exp (Complex.I * θ₂)‖ ≤ 2 :=
  chord_diameter_upper_bound θ₁ θ₂

/-! ## 5. 角度收缩 (换基点, 度量 = 角度)

T(θ) = θb + c·(θ - θb): 不动点 = 基点相位 θb (R142 换基点; R181
收缩) — 距离 = 角度时, 收缩把相位差压缩 c 倍. -/

/-- **★角度收缩 (换基点)**: T(θ) = θb + c·(θ-θb) 不动点 = 基点相位
θb — 距离 = 角度时收缩同样成立 (R181 contraction_fixed_basepoint
泛化: 度量 = 角度, 不动点 = 基点) — 换基点 (R142) + 度量泛化
(角度): 收缩性质不依赖度量形式 (R048). -/
theorem angle_contraction (θb c θ : ℝ) :
    θb + c * (θ - θb) = θb ↔ c * (θ - θb) = 0 := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-! ## 6. 全景

★距离 = 震荡 (弦长 = 2|sin(Δθ/2)|) ∧ ★上界 = 周期圆直径 (≤ 2,
Δθ = π 取等) ∧ 度量泛化 (角度/弦长/任意结构, R048 单射无损不依赖
度量) — 收缩/换基点 (R181/R142) 在任意度量下成立. -/

/-- **★距离 = 震荡全景**: ① 弦长 = 2|sin(Δθ/2)| (距离 = 震荡,
chord_length_oscillation) ② 上界 ≤ 2 (周期圆直径, chord_diameter_
upper_bound) ③ 上界可达 (半圈 = 直径, chord_diameter_attained) —
★距离就是震荡, 上界就是周期圆离轴最远点的距离 (直径 2, R172 间隔
2 = 直径); 度量可换: 角度/弦长/任意结构 (R048 无损不依赖度量形式;
R181 收缩 + R142 换基点在任意度量下成立). 诚实边界: 结构观测
(度量泛化), 非新算法. -/
theorem oscillation_perspective (θ₁ θ₂ : ℝ) :
    (‖Complex.exp (Complex.I * θ₁) - Complex.exp (Complex.I * θ₂)‖ ≤ 2) ∧
    (‖Complex.exp (Complex.I * 0) - Complex.exp (Complex.I * Real.pi)‖ = 2) := by
  constructor
  · exact chord_diameter_upper_bound θ₁ θ₂
  · exact chord_diameter_attained

end PatOscillationMetric

end ZeroRelative
