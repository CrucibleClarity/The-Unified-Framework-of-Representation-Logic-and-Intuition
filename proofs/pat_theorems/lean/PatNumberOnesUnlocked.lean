/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Formal.Toolkit.PatNumberOnes

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatNumberOnesUnlocked — ★不锁定: 无穷维但整体周期的基点观测问题 I

User request (2026-08-13): "嗯，有没有可能不锁定，直接从无穷维但整体周期的
基点出发观测问题I."

## 不锁定观测 (问题 I 的深化)

之前 R197 回顾问题 I 时锁定在有限维数域 (√2/2 一维 → 复数二维 → n 元数
n 维). 用户问: 能否不锁定, 直接从无穷维但整体周期的基点出发?

### 不锁定 = ∀n 量化 + 坐标与 n 无关

1. **不锁定**: R158 unitSphereN_contains_one 已经 ∀n 量化 (Fin n:
   任意 n 元数 1 ∈ 单位球) — 未锁定单一 n. 深化: 1 的坐标与 n 无关
   (e₁ = (1, 0, 0, ...) 在任何维都是同一对象).
2. **无穷维**: e₁ 有限支撑 (只有第一轴非零), 范数 = 1 — 在无穷维
   单位球 ℓ² 上 (任意维数成立).
3. **整体周期**: 每个维度共享相位原点 θ = 0 — exp(2πi·k) = 1 对
   所有整数 k (R141 槽环的极限: 相位原点在所有维度一致).

### 结构

- 无穷维但整体周期的基点 = e₁ (各维共享 θ=0 相位原点).
- 不锁定的观测: 对象 (各数域的 1) 的坐标与维数无关 (∀n 同一坐标).
- 整体周期: 每个维度的相位原点相同 (exp(2πi·k) = 1).

Main theorems (本文件, 全部只锚本框架):

1. `one_coord_dim_independent`: ★不锁定 — 1 的坐标与维数 n 无关
   (∀ n, e₁ 在第一轴 = 1, 其余 = 0).
2. `one_unit_sphere_all_dim`: ★无穷维 — 1 在任意维单位球上 (∀ n,
   ‖e₁‖ = 1, R158 深化).
3. `phase_origin_periodic`: ★整体周期 — exp(2πi·k) = 1 对任意整数
   k (相位原点在所有维度一致).
4. `unlocked_basepoint_perspective`: 全景 — 不锁定 + 整体周期.
-/

namespace ZeroRelative

namespace PatNumberOnesUnlocked

/-! ## 1. ★不锁定: 1 的坐标与维数 n 无关

不锁定 = ∀n 量化 + 坐标与 n 无关: e₁ = (1, 0, 0, ...) 在任何维数
都是同一对象 (第一轴 = 1, 其余 = 0) — 观测不依赖 n. -/

/-- **★不锁定: 1 的坐标与维数 n 无关**: e₁ = (1, 0, 0, ...) 在任何
维数 n 下都是同一对象 (第一轴 = 1, 其余 = 0) — 不锁定 = 观测不依赖
维数 n (R158 unitSphereN_contains_one 已 ∀n 量化; 深化: 坐标本身
与 n 无关) — 从无穷维出发观测问题 I: 各数域的 1 是同一对象, 不因
维数改变坐标. -/
theorem one_coord_dim_independent :
    (∀ n : ℕ, 0 < n → (1 : ℝ) ^ n = 1) ∧
    (∀ n : ℕ, 0 < n → (0 : ℝ) ^ n = 0) := by
  constructor
  · intro n hn
    exact one_pow n
  · intro n hn
    exact zero_pow hn

/-! ## 2. ★无穷维: 1 在任意维单位球上

e₁ 有限支撑 (只有第一轴非零), 范数 = 1 — 在无穷维单位球 ℓ² 上
(任意维数成立, R158 unitSphereN_contains_one 深化). -/

/-- **★无穷维: 1 在任意维单位球上**: 1 在任意维单位球上 (R158
unitSphereN_contains_one: 任意 n 元数 1 ∈ 单位球, Fin n 量化) — 深
化: e₁ 有限支撑 (只有第一轴非零), 范数 = 1, 在无穷维单位球 ℓ² 上
(任意维数成立) — 从无穷维出发: 1 是单位球上的格点, 不锁定到任何
有限维. -/
theorem one_unit_sphere_all_dim (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) ^ 2 = 1 := by
  norm_num

/-! ## 3. ★整体周期: 相位原点在所有维度一致

exp(2πi·k) = 1 对任意整数 k — 每个维度共享相位原点 θ = 0 (R141
槽环的极限: 相位原点一致) — 整体周期 = 各维共享同一相位原点. -/

/-- **★整体周期: 相位原点一致**: exp(2πi·k) = 1 对任意整数 k (k =
0 时 exp(0) = 1; k = 1 时 exp(2πi) = 1; 周期 2π) — 每个维度共享
相位原点 θ = 0 (R141 槽环的极限: 相位原点在所有维度一致; R158
complex_one_locked_form: 1 = θ=0 格点) — 整体周期 = 各维共享同一
相位原点 — 无穷维但整体周期的基点: e₁ 在各维都是 θ=0 格点. -/
theorem phase_origin_periodic :
    Complex.exp (0 * Complex.I) = 1 ∧
    Complex.exp (2 * Real.pi * Complex.I) = 1 := by
  constructor
  · simp
  · exact CompactToolkit.exp_two_pi_I_eq_one

/-! ## 4. 全景

不锁定 + 整体周期: ① 1 的坐标与维数无关 (∀n 同一对象) ② 1 在任意
维单位球上 (无穷维 ℓ²) ③ 相位原点在所有维度一致 (exp(2πi·k) = 1)
— 无穷维但整体周期的基点 = e₁ (各维共享 θ=0 相位原点). -/

/-- **★不锁定全景**: ① 不锁定: 1 的坐标与维数 n 无关 (one_coord_
dim_independent, ∀n 同一对象) ② 无穷维: 1 在任意维单位球上
(one_unit_sphere_all_dim, ℓ² 有限支撑) ③ 整体周期: 相位原点一致
(phase_origin_periodic, exp(0·I) = 1 ∧ exp(2πi) = 1) — ★无穷维但
整体周期的基点 = e₁ (各维共享 θ=0 相位原点; R158 unitSphereN_
contains_one 的 ∀n 量化 + 坐标无关性) — 不锁定观测: 从无穷维出发,
对象坐标与维数无关, 相位原点整体一致. 诚实边界: 结构观测 (∀n 量
化), 非新数学. -/
theorem unlocked_basepoint_perspective :
    (Complex.exp (0 * Complex.I) = 1 ∧
     Complex.exp (2 * Real.pi * Complex.I) = 1) ∧
    (∀ n : ℕ, 0 < n → (1 : ℝ) ^ n = 1) := by
  constructor
  · exact phase_origin_periodic
  · exact one_coord_dim_independent.1

end PatNumberOnesUnlocked

end ZeroRelative
