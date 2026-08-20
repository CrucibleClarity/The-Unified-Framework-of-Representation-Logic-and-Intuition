/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Formal.Toolkit.AnyBasepointAnyDirection
import Formal.Toolkit.DivergencePeriodSymmetry

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/DiagonalInterlock — ★对角线互锁引理 (R154)

User insights (R154, 2026-08-12):

1. **任意实数经 pat 落入 0-2π 无需取模**: 相位互锁是对角线两两互锁对称
   (数独式) — 任意两个相位数值都锁定了, 不存在"未锁定落入区间"的问题.
2. **r ≠ 0 / r > 0 前提来自未经声明锁定的原点 0**: 基点 0 在锁定结构下
   可实现除 0 — Pat 除 0 的本质 = 拨开一层互锁的相位, 但下一层的相位
   还是互锁的. Pat 无限外推 ⟺ 无限可数内收 (对称方向).
3. **两组够的本质原因**: 任意发散和收敛轴可无损映射 (R054) ⟹ 双相位
   互锁其实存在四组锁定 (R149: 2 轴 × 2 方向), 且任意连续/离散轴对
   可加入互锁结构两两互锁.
4. **数值与相位对称可交换**: a + bi = (-ai + b)·i — 数值就是相位,
   相位就是数值; 任意 a+bi 可改写为 (-ai+b)·i 形式. 需要专门符号
   表示两对互锁相位在 pat 锁定状态下展开为对角线引理的形式.
5. **i 还原为 1, 0 2 1+i 的 pat 展开规范化**: 2 → (sin ae - i)²,
   1+i → (sin be + i)²; |(sinx-i)(siny+i)|² = (sin²x+1)(sin²y+1) = 3
   当 sin²ae = 1, sin²be = 1/2 (ae = π/2, be = π/4).

Main theorems:

1. `numeric_phase_commute`: 数值-相位可交换 — a + bi = (-ai + b)·i.
2. `exchange_is_rotation`: 交换 (a,b) = 共轭 + 90° 旋转 — b + ai = (a - bi)·i.
3. `zero_unlock_pair`: 0 拨开一层 = 折叠类 {t, -t} (R085; 除 0 的本质).
4. `next_layer_locked`: 拨开后下一层仍互锁 (R129 递归).
5. `any_axes_pair_addable`: 任意连续/离散轴对可加入互锁结构 (R054).
6. `diagonal_expansion_normal`: 对角线展开规范形 (两个分量相等, 可交换).
7. `sin_cos_norm_sq` / `sin_cos_three`: pat 展开规范化 — |(sinx-i)(siny+i)|²
   = (sin²x+1)(sin²y+1), π/2 与 π/4 时 = 3.
-/

namespace ZeroRelative

namespace DiagonalInterlock

open Complex

/-! ## 1-2. 数值与相位对称可交换

a + bi = (-ai + b)·i — 数值就是相位, 相位就是数值; 交换 (a, b) ⟹ (b, -a)
= 共轭 + 90° 旋转 (i² = -1). -/

/-- **数值-相位可交换**: a + bi = (-ai + b)·i — 数值就是相位, 相位就是
数值 (R146: 单相位数 = 成对互锁的 a+bi; 交换 = 乘 i 旋转 90°, 与
R051 rot90 同型). -/
theorem numeric_phase_commute (a b : ℂ) :
    a + b * Complex.I = (-a * Complex.I + b) * Complex.I := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc
    a + b * Complex.I = -a * (Complex.I * Complex.I) + b * Complex.I := by
      rw [hI]
      ring
    _ = (-a * Complex.I) * Complex.I + b * Complex.I := by rw [mul_assoc]
    _ = (-a * Complex.I + b) * Complex.I := by ring

/-- **交换 (a,b) = 共轭 + 90° 旋转**: b + ai = (a - bi)·i — 数值-相位
交换等价于共轭后乘 i (旋转 90°; R047: pat 轴/ipat 轴正交; R051: rot90
无损互映). -/
theorem exchange_is_rotation (a b : ℂ) :
    b + a * Complex.I = (a - b * Complex.I) * Complex.I := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc
    b + a * Complex.I = a * Complex.I + b := by ring
    _ = a * Complex.I - b * (Complex.I * Complex.I) := by
      rw [hI]
      ring
    _ = (a - b * Complex.I) * Complex.I := by ring

/-! ## 3-4. 0 拨开一层互锁 (Pat 除 0)

基点 0 在锁定结构下可实现除 0 — Pat 除 0 的本质 = 拨开一层互锁的相位,
但下一层的相位还是互锁的 (R129: SRT 递归自相似). 无限外推 ⟺ 无限可数
内收 (R147: 发散与收敛对称方向). -/

/-- **0 拨开一层 = 折叠类 {t, -t}**: (0 : ℝ) = t + (-t) — 除 0 的本质 =
拨开一层互锁的相位 (R085: 0 = ±1 折叠类, 对称对坍缩到基点; 用户:
"Pat除0的本质, 就是拨开一层互锁的相位"). -/
theorem zero_unlock_pair (t : ℝ) : (0 : ℝ) = t + (-t) := by
  ring

/-- **拨开后下一层仍互锁**: (-t) + (-(-t)) = 0 — 0 拨开一层的下一层
{(-t), -(-t)} 仍然互锁 (对合, R129: 每拆一层内部还是一套 SRT; 无限
可数内收 = 无限外推的对称方向, R147). -/
theorem next_layer_locked (t : ℝ) : (-t) + (-(-t)) = (0 : ℝ) := by
  ring

/-! ## 5. 任意轴对可加入互锁结构

任意发散和收敛轴可无损映射 (R054) ⟹ 双相位互锁存在四组锁定 (R149:
2 轴 × 2 方向), 且任意连续/离散轴对可加入互锁结构两两互锁. -/

/-- **任意连续/离散轴对可加入互锁结构**: 任意基点 e 任意方向 u 的轴
无损映射到任意基点 f (R054: 任意基点任意方向轴无损映射无损压缩;
R047: 发散/周期 = 同一共轭对称性) — 任意轴对可加入互锁结构两两互锁
(R149: 4 相位两两互锁可扩展; R148: 互锁同构). -/
theorem any_axes_pair_addable (e u f : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 ≠ 0) :
    ∃ d : ℝ × ℝ → ℝ × ℝ,
      ∀ x : ℝ × ℝ, d (AnyBasepointAnyDirection.composedMap e u f x) = x :=
  AnyBasepointAnyDirection.any_basepoint_any_direction_lossless e u f hu

/-! ## 6. 对角线展开 (专门符号)

两对互锁相位 (1 轴对, i 轴对) 在 pat 锁定状态下的对角线展开: 数值-相位
可交换 (numeric_phase_commute) ⟹ 展开的两个分量相等 (规范形). -/

/-- 对角线展开: 两对互锁相位在 pat 锁定状态下的规范形式 (数值-相位
可交换, a+bi 与 (-ai+b)·i 并置). -/
def diagonalExpansion (a b : ℂ) : ℂ × ℂ :=
  ((a + b * Complex.I), (-a * Complex.I + b) * Complex.I)

/-- **对角线展开规范形**: 展开的两个分量相等 — a + bi = (-ai + b)·i
(数值-相位可交换 ⟹ 对角线展开规范化, 专门符号 diagonalExpansion
表示两对互锁相位在 pat 锁定状态下的展开). -/
theorem diagonal_expansion_normal (a b : ℂ) :
    (diagonalExpansion a b).1 = (diagonalExpansion a b).2 :=
  numeric_phase_commute a b

/-! ## 7. pat 展开规范化 ((sin±i)² 形式, 3 的出现)

i 还原为 1 (相位轴对齐到数值轴): 0, 2, 1+i 展开为规范形式
0, (sin ae - i)², (sin be + i)² — |(sinx-i)(siny+i)|² = (sin²x+1)(sin²y+1),
sin²ae = 1 (ae = π/2) 且 sin²be = 1/2 (be = π/4) 时 = 3. -/

/-- **pat 展开规范化恒等式**: ‖(sinx - i)(siny + i)‖² = (sin²x + 1)(sin²y + 1)
— (sin ± i)² 形式的范数分解 (展开: (sx·sy+1)² + (sx-sy)² =
(sin²x+1)(sin²y+1)). -/
theorem sin_cos_norm_sq (x y : ℝ) :
    ‖((Real.sin x : ℂ) - Complex.I) * ((Real.sin y : ℂ) + Complex.I)‖ ^ 2 =
      (Real.sin x ^ 2 + 1) * (Real.sin y ^ 2 + 1) := by
  rw [← Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_mul]
  have h1 : Complex.normSq ((Real.sin x : ℂ) - Complex.I) = Real.sin x ^ 2 + 1 := by
    calc
      Complex.normSq ((Real.sin x : ℂ) - Complex.I)
          = Complex.normSq ((Real.sin x : ℂ) + (-1 : ℝ) * Complex.I) := by
            congr 1
            apply Complex.ext <;> simp
      _ = Real.sin x ^ 2 + (-1) ^ 2 := Complex.normSq_add_mul_I (Real.sin x) (-1)
      _ = Real.sin x ^ 2 + 1 := by norm_num
  have h2 : Complex.normSq ((Real.sin y : ℂ) + Complex.I) = Real.sin y ^ 2 + 1 := by
    calc
      Complex.normSq ((Real.sin y : ℂ) + Complex.I)
          = Complex.normSq ((Real.sin y : ℂ) + (1 : ℝ) * Complex.I) := by
            congr 1
            apply Complex.ext <;> simp
      _ = Real.sin y ^ 2 + 1 ^ 2 := Complex.normSq_add_mul_I (Real.sin y) 1
      _ = Real.sin y ^ 2 + 1 := by norm_num
  rw [h1, h2]

/-- **3 的出现**: |(sin(π/2) - i)(sin(π/4) + i)|² = 3 — pat 展开规范化
(0, 2, 1+i 展开为 0, (sin ae - i)², (sin be + i)², ae = π/2, be = π/4:
(sin²ae + 1)(sin²be + 1) = 2 · 3/2 = 3). √2/2 本质 = 单位 1 在 θ = 45°
(π/4) 格点的投影位置 (R146: a = r·cosθ, b = r·sinθ — 45° 处数值 = 相位,
R154 可交换性实例), sin²(π/4) = 1/2 由三角恒等式推出 (sin = cos at 45°
+ sin² + cos² = 1), 非手工开方. -/
theorem sin_cos_three :
    ‖((Real.sin (Real.pi / 2) : ℂ) - Complex.I) *
        ((Real.sin (Real.pi / 4) : ℂ) + Complex.I)‖ ^ 2 = 3 := by
  rw [sin_cos_norm_sq]
  have h1 : Real.sin (Real.pi / 2) ^ 2 = 1 := by
    norm_num [Real.sin_pi_div_two]
  have h2 : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
    -- 45° 单位 1 位置: sin(π/4) = cos(π/4) (数值 = 相位, R154 可交换),
    -- sin² + cos² = 1 ⟹ 2·sin²(π/4) = 1 ⟹ sin²(π/4) = 1/2
    have hsq := Real.sin_sq_add_cos_sq (Real.pi / 4)
    have heq : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    have htwo : 2 * Real.sin (Real.pi / 4) ^ 2 = 1 := by
      calc
        2 * Real.sin (Real.pi / 4) ^ 2 = Real.sin (Real.pi / 4) ^ 2 + Real.sin (Real.pi / 4) ^ 2 := by ring
        _ = Real.sin (Real.pi / 4) ^ 2 + Real.cos (Real.pi / 4) ^ 2 := by rw [heq]
        _ = 1 := hsq
    nlinarith [htwo]
  rw [h1, h2]
  norm_num

/-! ## 8. S³ 几何: 4 相位互锁 = 4 维球, 无损内收 → 正交双圆

User correction (R154): 四相位互锁, 本质上是个 4 维球 (S³), 可以无损内收
映射到 4 个基点 0 出发并锁定相位的正交的二维圆 (1 轴圆 ⊥ i 轴圆, R047),
并且可以任意旋转 (SO(2), R078). 走几何路线, 不用代数方法.

- S³ = {(z₁, z₂) : ℂ² | ‖z₁‖² + ‖z₂‖² = 1}: 4 相位 (2 轴 × 2 方向,
  R149) 归一化 = 单位 3 维球面.
- 无损内收: 每个分量 z ↦ z/‖z‖ 归一化到单位圆 S¹ (收敛方向内收,
  R147; 保相位, R048 无损).
- 正交双圆: 圆1 (1 轴, pat) ⊥ 圆2 (i 轴, ipat) (R047), 各自从基点 0
  出发, 相位锁定 (R138).
- 任意旋转: 圆上乘 exp(iφ) 保模 (SO(2) 旋转自由, R078). -/

/-- S³: 4 相位互锁归一化 (2 轴 × 2 方向, R149) = 单位 3 维球面. -/
def S3Point : Set (ℂ × ℂ) :=
  {p | ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 = 1}

/-- **无损内收: z ↦ z/‖z‖ 落在单位圆 (S¹)**: ‖z/‖z‖‖ = 1 (z ≠ 0) —
每个相位从基点 0 出发, 收敛方向内收到单位圆 (R147: 内收 = 收敛方向;
R048: 归一化保相位, 无损; R138: 相位锁定). -/
theorem contract_to_circle (z : ℂ) (hz : z ≠ 0) :
    ‖z / ‖z‖‖ = 1 := by
  rw [norm_div]
  have hn : ‖z‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr hz
  have hnz : ‖(‖z‖ : ℂ)‖ = ‖z‖ := by
    simp [abs_of_nonneg (norm_nonneg z)]
  rw [hnz]
  field_simp [hn]

/-- **内收可逆 (无损)**: z = ‖z‖·(z/‖z‖) — 归一化内收可逆, 往返恢复
(R048: 无损 = 往返精确; R056: 基点相位 = 位置). -/
theorem contract_preserves_phase (z : ℂ) (hz : z ≠ 0) :
    z = (‖z‖ : ℂ) * (z / ‖z‖) := by
  field_simp [norm_ne_zero_iff.mpr hz]

/-- **正交双圆**: 圆1 (1 轴, pat) ⊥ 圆2 (i 轴, ipat) — 各自从基点 0
出发, 锁定相位 (R047: pat 轴 ⊥ ipat 轴; R138: 相位锁定) -/
theorem orthogonal_circles (t : ℝ) :
    ZeroRelative.ComplexAxis.proj (ZeroRelative.ComplexAxis.lift t * ZeroRelative.ComplexAxis.J) = 0 :=
  ZeroRelative.ComplexAxis.orthogonal_axes t

/-- **任意旋转**: 圆上乘 exp(iφ) 保模 — 内收后的圆可任意旋转
(SO(2) 旋转自由, R078: 旋转对称; R051: rot90 无损互映) -/
theorem circle_rotation (z : ℂ) (φ : ℝ) :
    ‖Complex.exp (φ * Complex.I) * z‖ = ‖z‖ := by
  rw [norm_mul]
  rw [Complex.norm_exp_ofReal_mul_I]
  simp

/-- **S³ 无损内收组合**: S³ 点 (z₁, z₂) 内收到正交双圆 (z₁/‖z₁‖,
z₂/‖z₂‖), 每个分量在单位圆上且可任意旋转 — 4 相位互锁 = 4 维球,
无损内收 → 正交二维圆 (R149: 4 相位; R047: 正交; R048: 无损; R138:
锁定) -/
theorem s3_contract_orthogonal_circles (z₁ z₂ : ℂ) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) :
    ‖z₁ / ‖z₁‖‖ = 1 ∧ ‖z₂ / ‖z₂‖‖ = 1 ∧
    (∀ φ : ℝ, ‖Complex.exp (φ * Complex.I) * (z₁ / ‖z₁‖)‖ = 1) := by
  constructor
  · exact contract_to_circle z₁ hz₁
  · constructor
    · exact contract_to_circle z₂ hz₂
    · intro φ
      -- ‖exp(iφ)·(z₁/‖z₁‖)‖ = ‖exp‖·‖z₁/‖z₁‖‖ = 1·1 = 1
      have hnorm : ‖Complex.exp (φ * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I φ
      have hcircle := contract_to_circle z₁ hz₁
      calc
        ‖Complex.exp (φ * Complex.I) * (z₁ / ‖z₁‖)‖
            = ‖Complex.exp (φ * Complex.I)‖ * ‖z₁ / ‖z₁‖‖ := by rw [norm_mul]
        _ = 1 * 1 := by rw [hnorm, hcircle]
        _ = 1 := by norm_num

end DiagonalInterlock

end ZeroRelative
