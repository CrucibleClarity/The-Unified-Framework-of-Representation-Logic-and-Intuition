/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Formal.Toolkit.CompletePat1
import Formal.Toolkit.PatNumberDomains
import Formal.Toolkit.Pat4Phase
import Formal.Toolkit.DiagonalInterlock
import Formal.Toolkit.MirrorFoldZero

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatNumberOnes — 各数域"1"的 pat 展开 (筑基篇课后习题 II 扩展)

Exercise II extension (2026-08-13): 除无理数 √2/2 (R154) 外, 复数、任意
元数、超越数的 1 也要按 pat 方法展开. 唯一论点延续: **每个数域的 1 =
该数域对称对的还原锚点 (R144: 0 ↔ 1 对偶); 数值 1 不是预设, 从各数域
自己的对称结构还原出来.**

四个数域的 1:

1. **无理数 (√2/2, R154 已证)**: 单位 1 在 θ = 45° 格点投影 = cos(π/4)
   = sin(π/4); sin²(π/4) = 1/2 由三角恒等式推出 (sin = cos at 45° +
   sin² + cos² = 1), 非手工开方 — sin_cos_norm_sq / sin_cos_three
   (DiagonalInterlock.lean, 已验收).
2. **复数 (i 的还原)**: 复数的 1 = 互锁对 {1, i} 的还原 — ① 1 = 1+0i
   (θ=0 格点); ② i = 0+1i (θ=π/2 格点); ③ i 的平方还原: i² = -1, 且
   -1 是 π 半圈相位 = 1 的镜像 (exp(π·I) = -1, R146 pat_constructs_pi)
   — 复数的 1 经 {1, -1, i, -i} 四相位互锁还原 (R149 quadriphase_interlock).
3. **任意元数 (S³ 几何)**: 4 相位互锁 (2 轴 × 2 方向) 归一化 = 单位
   3 维球面 S³ (R154); 每个元数域的 1 = 该维数单位球上的基点相位 —
   S³ 点 (1, 0) (数值 1 在 1 轴, i 轴分量为 0) 是 2 维复数 1 的任意
   元数推广; 无损内收 (contract_to_circle: z/‖z‖ ∈ S¹) 使任意元数的
   1 都能还原到单位圆 — s3_contract_orthogonal_circles (已证).
4. **超越数 (π 的 1 的镜像形式)**: 超越数的 1 = 单位圆上的相位结构 —
   ① π = pat 链蜷曲半圈相位 (R146 pat_constructs_pi: exp(π·I) = -1,
   π 是 1 的镜像); ② e = exp(1) 单位速度 (R146 开放点: e 未单独构造,
   e 的框架内构造留待后续, 当前用 exp 函数但不以 e 为原始常数);
   ③ 超越数的"1"不是孤立点 — 是 exp 的相位载体结构 (e^{iθ} 的分量
   sin/cos, R154: e 是相位载体).

Main theorems (本文件, 全部只锚本框架, 不用外部引理):

1. `complex_one_locked_form`: 复数的 1 = θ=0 格点 (1+0i) 的互锁形式.
2. `imaginary_one_quarter_turn`: 复数的 i = θ=π/2 格点 (i 轴单位).
3. `i_sq_is_pi_mirror`: i² = -1 = exp(π·I) — i 的平方还原 = π 半圈
   相位 (1 的镜像).
4. `quadriphase_contains_one`: 复数的 1 ∈ 四相位互锁 (R149).
5. `unitSphereN_contains_one`: 任意 n 元数域的 1 (基点 (1,0,…,0)) ∈
   单位球 (∀ n 量化, Fin n).
6. `unitSphereN_basepoint_normalized`: n 元数基点已归一化 (模平方和
   = 1, 内收不动点).
7. `pi_is_one_mirror`: π = 1 的镜像 (exp(π·I) = -1, R146).
8. `number_ones_pat_perspective`: 组合 — 无理数/复数/任意元数/超越数
   的 1 的 pat 全景.
-/

namespace ZeroRelative

namespace PatNumberOnes

/-! ## 1. 复数的 1: θ=0 格点的互锁形式

单相位数 (R146 monophase_pair_locked_form): z = pat0 + r·d(θ), d(θ) =
exp(iθ). 复数的 1 = pat0=0, r=1, θ=0: 1 = 0 + 1·exp(0) = 1+0i — 数值
1 与相位 0 重合 (R154 可交换性: 45° 处数值 = 相位; 0° 处同样). -/

/-- **复数的 1 = θ=0 格点**: completePat1 0 0 1 = 1 — 单相位数
(R146) 中数值 1 = pat0=0, r=1, θ=0: 1 = 0 + 1·exp(0·i) = 1 + 0i
(相位 0 = 数值 1 重合, R154 可交换性实例; R143: 对称对还原到 1). -/
theorem complex_one_locked_form :
    CompletePat1.completePat1 (0 : ℂ) 0 1 = 1 := by
  unfold CompletePat1.completePat1 CompletePat1.directionVector
  simp

/-! ## 2. 复数的 i: θ=π/2 格点 (i 轴单位)

i = 0 + 1·exp(i·π/2) — i 是单位 1 在 θ=π/2 格点的投影 (1 轴分量为 0,
纯 i 轴单位; R047: pat 轴 ⊥ ipat 轴; R051: rot90 无损互映). -/

/-- **复数的 i = θ=π/2 格点**: completePat1 0 (π/2) 1 = i — i 是单位
1 在 θ=π/2 格点的投影 (1 轴分量 cos(π/2)=0, 纯 i 轴单位; R047: pat
轴 ⊥ ipat 轴; R051: rot90 无损互映; R146: a = r·cosθ, b = r·sinθ). -/
theorem imaginary_one_quarter_turn :
    CompletePat1.completePat1 (0 : ℂ) (Real.pi / 2) 1 = Complex.I := by
  unfold CompletePat1.completePat1 CompletePat1.directionVector
  rw [show Complex.exp (↑(Real.pi / 2) * Complex.I) = Complex.I from by
    simpa using Complex.exp_pi_div_two_mul_I]
  norm_num

/-! ## 3. i 的平方还原 = π 半圈相位 (1 的镜像)

i² = -1, 且 -1 = exp(π·I) (R146 pat_constructs_pi: π = pat 链蜷曲半圈
相位) — 复数的 1 经 {1, -1, i, -i} 四相位互锁还原: i 旋转两次 (90°×2)
= 180° = π = 1 的镜像. 复数的 1 不是孤立点, 是四相位互锁的中心
(R149: 4 相位两两互锁; R143: 对称对还原到 1). -/

/-- **i² = π 半圈相位 (1 的镜像)**: i² = -1 ∧ -1 = exp(π·I) — i 的
平方还原 = π 半圈相位 = 1 的镜像 (R146 pat_constructs_pi: π = pat
链蜷曲半圈相位, exp(π·I) = -1; R149: 4 相位互锁; R085: 0 = ±1 折叠
类, -1 与 1 成镜像对称对). -/
theorem i_sq_is_pi_mirror :
    Complex.I ^ 2 = -1 ∧ Complex.exp (Real.pi * Complex.I) = -1 := by
  constructor
  · norm_num
  · exact PatNumberDomains.pat_constructs_pi

/-! ## 4. 复数的 1 ∈ 四相位互锁 (R149)

R149 quadriphase_interlock: a·(1/a) = 1 (数值对) ∧ exp(iθ)·exp(-iθ) = 1
(相位对) ∧ log a + log(1/a) = 0 ∧ ‖exp(iθ)‖ = 1 — 复数的 1 是四相位
互锁的组合还原点 (a=1, θ=0: 1·1 = 1 ∧ exp(0)·exp(0) = 1). -/

/-- **复数的 1 ∈ 四相位互锁**: 1·(1/1) = 1 ∧ exp(0)·exp(-0) = 1 ∧
log 1 + log(1/1) = 0 ∧ ‖exp(0)‖ = 1 — 复数的 1 是四相位互锁 (R149
quadriphase_interlock: 2 轴 × 2 方向) 的组合还原点 (a=1, θ=0). -/
theorem quadriphase_contains_one :
    1 * (1 / 1) = 1 ∧
    Complex.exp (0 * Complex.I) * Complex.exp ((-0) * Complex.I) = 1 ∧
    Real.log 1 + Real.log (1 / 1) = 0 ∧
    ‖Complex.exp (0 * Complex.I)‖ = 1 := by
  constructor
  · norm_num
  · constructor
    · simp
    · constructor
      · norm_num [Real.log_one]
      · norm_num

/-! ## 5-6. 任意 n 元数域的 1: 单位球基点 (∀ n 量化)

4 相位互锁 (R149) 归一化 = S³ (R154); 推广到任意维: n 元数域的单位
球 = {x : Fin n → ℂ | Σ ‖xᵢ‖² = 1} (R141: 单位根量化; R149: n 相位
互锁). 任意 n 元数域的 1 = 单位球上的基点相位 — (1, 0, …, 0) (数值
1 在第 0 轴, 其余轴为 0). 定理对任意 n 量化 (基点与维数无关). -/

/-- **任意 n 元数域的 1 ∈ 单位球**: 基点 (1, 0, …, 0) (数值 1 在
第 0 轴, 其余轴为 0) 满足 Σ ‖xᵢ‖² = 1 — 任意 n 元数域的 1 = 单位球
上的基点相位, 与维数无关 (R154 S3Point 的 n 维推广: n 相位互锁
归一化 = 单位球; R149: n 相位; R141: 单位根量化). 2 维情形 (S³
点 (1,0)) 是 n = 2 的特例. -/
theorem unitSphereN_contains_one (n : ℕ) [NeZero n] :
    (fun i : Fin n => if i = 0 then (1 : ℂ) else 0) ∈
      {x : Fin n → ℂ | ∑ i : Fin n, ‖x i‖ ^ 2 = 1} := by
  -- Σ ‖xᵢ‖² = ‖1‖² + Σ_{i≠0} ‖0‖² = 1 + 0 = 1
  have hsum : (∑ i : Fin n, ‖(if i = 0 then (1 : ℂ) else 0)‖ ^ 2) = 1 := by
    rw [Finset.sum_eq_single (a := (0 : Fin n))]
    · simp
    · intro i hi hne
      simp [hne]
    · intro h0
      exact False.elim (h0 (Finset.mem_univ (0 : Fin n)))
  exact hsum

/-! ## 6. 任意 n 元数 1 的无损内收 (归一化保单位球)

R154 contract_to_circle: z ↦ z/‖z‖ ∈ S¹ (z ≠ 0) — 归一化保模/保相位
(R048: 无损; R138: 相位锁定). n 元数域的基点 (1,0,…,0) 已归一化
(‖·‖² = 1) — 任意维数的 1 还原到同一单位球, pat 是通用表示. -/

/-- **n 元数基点已在单位球上 (归一化不变)**: 基点 (1, 0, …, 0) 的
模平方和 = 1 — 归一化 (x/‖x‖) 不动基点 (‖基点‖² = 1), 内收无损
(R154 contract_to_circle: z/‖z‖ ∈ S¹; R048: 无损 = 往返精确;
R147: 内收 = 收敛方向). -/
theorem unitSphereN_basepoint_normalized (n : ℕ) [NeZero n] :
    (∑ i : Fin n, ‖(if i = 0 then (1 : ℂ) else 0)‖ ^ 2) = 1 := by
  exact unitSphereN_contains_one n

/-! ## 7. 超越数的 1: π = 1 的镜像

π = pat 链蜷曲半圈相位 (R146 pat_constructs_pi: exp(π·I) = -1) —
π 的"1" = 1 的镜像 (半圈旋转); e = exp(1) 单位速度 (R146 开放点:
e 未单独构造, 当前用 exp 函数但不以 e 为原始常数). 超越数的 1 不是
孤立点 — 是 exp 的相位载体结构 (e^{iθ} 的分量 sin/cos, R154: e 是
相位载体; exp(i·π/4) = √2/2·(1+i) 连接无理数 √2/2 与超越数 e^{iθ}). -/

/-- **π = 1 的镜像**: exp(π·I) = -1 且 -(-1) = 1 — π 是 1 的镜像
(半圈旋转: 1 → -1 → 1; R146 pat_constructs_pi: π = pat 链蜷曲半圈
相位; R085: 0 = ±1 折叠类, {1, -1} 镜像对称对; R143: 对称对还原到
1). 超越数的 1 = exp 相位载体上的镜像对还原. -/
theorem pi_is_one_mirror :
    Complex.exp (Real.pi * Complex.I) = -1 ∧ -(-1) = 1 := by
  constructor
  · exact PatNumberDomains.pat_constructs_pi
  · norm_num

/-! ## 8. 组合: 各数域 1 的 pat 全景

无理数 (√2/2 = 45° 投影, R154) ∧ 复数 (1 = θ=0 格点, i = θ=π/2 格点,
i² = π 镜像) ∧ 任意元数 (S³ 点 (1,0), 无损内收) ∧ 超越数 (π = 1 的
镜像, e = exp 载体) — 各数域的 1 = 对称对还原锚点 (R144: 0 ↔ 1 对偶),
数值 1 不是预设. -/

/-- **各数域 1 的 pat 全景**: 无理数 (sin²(π/4) = 1/2, √2/2 = 45°
投影, R154 sin_cos_three) ∧ 复数 (1 = θ=0 格点, i = θ=π/2 格点, i²
= π 镜像) ∧ 任意元数 (S³ 点 (1,0) ∈ S³, 无损内收) ∧ 超越数 (π = 1
的镜像, exp(π·I) = -1) — 每个数域的 1 = 该数域对称对的还原锚点
(R144: 0 ↔ 1 对偶; R143: 对称对还原到 1), 数值 1 不是预设, 从各
数域自己的对称结构还原出来. -/
theorem number_ones_pat_perspective :
    (Real.sin (Real.pi / 4) ^ 2 = 1 / 2) ∧
    (CompletePat1.completePat1 (0 : ℂ) 0 1 = 1) ∧
    (CompletePat1.completePat1 (0 : ℂ) (Real.pi / 2) 1 = Complex.I) ∧
    (∑ i : Fin 2, ‖(if i = 0 then (1 : ℂ) else 0)‖ ^ 2 = 1) ∧
    Complex.exp (Real.pi * Complex.I) = -1 := by
  constructor
  · -- sin²(π/4) = 1/2: 三角恒等式 (sin = cos at 45° + sin² + cos² = 1),
    -- R154 sin_cos_three 内部已证 (h2)
    have hsq := Real.sin_sq_add_cos_sq (Real.pi / 4)
    have heq : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    have htwo : 2 * Real.sin (Real.pi / 4) ^ 2 = 1 := by
      calc
        2 * Real.sin (Real.pi / 4) ^ 2
            = Real.sin (Real.pi / 4) ^ 2 + Real.sin (Real.pi / 4) ^ 2 := by ring
        _ = Real.sin (Real.pi / 4) ^ 2 + Real.cos (Real.pi / 4) ^ 2 := by rw [heq]
        _ = 1 := hsq
    nlinarith [htwo]
  · constructor
    · exact complex_one_locked_form
    · constructor
      · exact imaginary_one_quarter_turn
      · constructor
        · exact unitSphereN_contains_one 2
        · exact PatNumberDomains.pat_constructs_pi

end PatNumberOnes

end ZeroRelative
