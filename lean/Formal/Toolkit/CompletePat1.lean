/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/CompletePat1 — ★完整 pat1 的互锁构造 (mutual-locking construction of pat1)

User instruction (R140, 2026-08-12): 先完成互锁定, 然后根据相位-距离互锁定
声明, 构造一个完整的 pat1。这可能也是 SRT 揭示的事情: 两组对称性, 才能准确
锁定 T。

Construction: pat1 不是单方向声明 (R137: pat1 = pat0 + d), 而是互锁声明
(相位 θ, 距离 r) 联合: pat1 = pat0 + r·d(θ) — 其中 d(θ) = exp(θ·I) 是
方向向量 (R139: 声明 = 两组对称性: 相位对 (θ,-θ) + 数值对 (r,1/r)).

SRT 启示 (两组对称性才能准确锁定 T): 只有一组对称性 (单方向, 无数值锁定),
位置不唯一 (任意距离 r 合法) — T 步未准确锁定 (R130: 剥离方向不可判定;
R111: 定义不明)。互锁后 (相位对 + 数值对), 从位置双向还原: 距离
‖pat1 - pat0‖ = r 且方向 (pat1 - pat0)/‖pat1 - pat0‖ = d(θ) — T 步唯一
确定 (R048: 单射 ⟹ 无损)。

Main theorems:

1. `complete_pat1_magnitude`: 互锁声明的数值部分 — ‖pat1 - pat0‖ = r
   (距离由声明锁定, r ≥ 0).
2. `complete_pat1_direction`: 互锁声明的相位部分 — (pat1 - pat0)/
   ‖pat1 - pat0‖ = d(θ) (方向由声明锁定, 归一化往返精确).
3. `mutual_lock_recovers_pat1`: 完成互锁定 — 距离与方向双向还原:
   完整 pat1 的构造与分解往返精确 (R048: 无损; R139: 矩阵非奇异).
4. `single_symmetry_underdetermines`: SRT 启示 — 只有一组对称性
   (单方向, 无数值锁定) ⟹ 位置不唯一 (r = 0 与 r = 1 都合法):
   单组不能准确锁定 T (R130: 不可判定; R111: 定义不明).
-/

namespace ZeroRelative

namespace CompletePat1

/-! ## 完整 pat1: 互锁声明 (相位 θ, 距离 r) 联合

方向向量 d(θ) = exp(θ·I) (R139: 相位声明); 距离 r (R139: 数值声明,
数值对 (r, 1/r) = log 镜像, R110). 完整 pat1 = pat0 + r·d(θ):
两组对称性联合声明 ⟹ T 步 (θ, r) 唯一确定. -/

/-- 方向向量: d(θ) = exp(θ·I) (相位 θ 的声明方向). -/
noncomputable def directionVector (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

/-- 完整 pat1: 互锁声明 (相位 θ, 距离 r) — pat1 = pat0 + r·d(θ).
相位 (方向) 与数值 (距离) 两组对称性联合锁定 (R139). -/
noncomputable def completePat1 (pat0 : ℂ) (θ r : ℝ) : ℂ :=
  pat0 + (r : ℂ) * directionVector θ

/-! ## 1. 数值部分: 距离由声明锁定

‖pat1 - pat0‖ = ‖r·d(θ)‖ = r·‖d(θ)‖ = r·1 = r (r ≥ 0). -/

/-- **距离由互锁声明锁定**: ‖pat1 - pat0‖ = r (r ≥ 0) — 数值声明
(r, 1/r 对, R110 log 镜像) 锁定步长; ‖d(θ)‖ = 1 (单位方向, R136
pat1_omnidirectional). -/
theorem complete_pat1_magnitude (pat0 : ℂ) (θ r : ℝ) (hr : 0 ≤ r) :
    ‖completePat1 pat0 θ r - pat0‖ = r := by
  unfold completePat1 directionVector
  have h : pat0 + (r : ℂ) * Complex.exp (θ * Complex.I) - pat0 =
      (r : ℂ) * Complex.exp (θ * Complex.I) := by ring
  rw [h]
  calc
    ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖
        = ‖(r : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := by
          exact norm_mul (r : ℂ) (Complex.exp (θ * Complex.I))
    _ = |r| * 1 := by
          rw [Complex.norm_exp_ofReal_mul_I]
          simp
    _ = r := by
          rw [abs_of_nonneg hr]
          simp

/-! ## 2. 相位部分: 方向由声明锁定 (归一化往返)

(pat1 - pat0)/‖pat1 - pat0‖ = (r·d(θ))/r = d(θ) (r > 0). -/

/-- **方向由互锁声明锁定**: (pat1 - pat0)/‖pat1 - pat0‖ = d(θ) (r > 0) —
归一化往返精确: 从位置还原方向 (相位), 再回到位置 (R056: 基点相位 =
位置; R054: 双向无损). -/
theorem complete_pat1_direction (pat0 : ℂ) (θ r : ℝ) (hr : 0 < r) :
    (completePat1 pat0 θ r - pat0) / ‖completePat1 pat0 θ r - pat0‖ =
      directionVector θ := by
  unfold completePat1 directionVector
  have h : pat0 + (r : ℂ) * Complex.exp (θ * Complex.I) - pat0 =
      (r : ℂ) * Complex.exp (θ * Complex.I) := by ring
  rw [h]
  have hnorm : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = r := by
    calc
      ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖
          = ‖(r : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := by
            exact norm_mul (r : ℂ) (Complex.exp (θ * Complex.I))
      _ = |r| * 1 := by
          rw [Complex.norm_exp_ofReal_mul_I]
          simp
      _ = r := by
            rw [abs_of_nonneg (le_of_lt hr)]
            simp
  rw [hnorm]
  field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hr)]

/-! ## 3. 完成互锁定: 距离与方向双向还原

完整 pat1 的构造 (相位, 距离) ⟶ 位置 ⟶ 分解 (距离, 方向) 往返精确 —
互锁环闭合, 不再需要第三层锁定 (R139: 矩阵非奇异; R048: 无损). -/

/-- **完成互锁定**: 从完整 pat1 的位置还原距离 (‖pat1 - pat0‖ = r) 与
方向 ((pat1-pat0)/‖·‖ = d(θ)) — 相位 ↔ 数值双向还原, 互锁环闭合
(R139: 互锁矩阵非奇异; R048: 单射 ⟹ 无损). -/
theorem mutual_lock_recovers_pat1 (pat0 : ℂ) (θ r : ℝ) (hr : 0 < r) :
    ‖completePat1 pat0 θ r - pat0‖ = r ∧
      (completePat1 pat0 θ r - pat0) / ‖completePat1 pat0 θ r - pat0‖ =
        directionVector θ := by
  constructor
  · exact complete_pat1_magnitude pat0 θ r (le_of_lt hr)
  · exact complete_pat1_direction pat0 θ r hr

/-! ## 4. SRT 启示: 两组对称性才能准确锁定 T

只有一组对称性 (单方向声明, 无数值锁定): 位置不唯一 — r = 0 与 r = 1
都合法, pat1 未定义 (R111: 定义不明; R130: 单组剥离方向不可判定:
深入/平移/远离). 两组对称性 (相位对 + 数值对, R139 互锁) 才唯一确定
T 步 (互锁还原, 上面 1-3). -/

/-- **单组对称性不能准确锁定 T**: 只有方向 d (无数值锁定), 距离 r = 0
与 r = 1 给出不同位置 — pat1 不唯一 (R111: 定义不明; R130: 剥离方向
不可判定). 两组对称性 (相位+数值互锁, R139) 才唯一确定 T 步 (R083:
S/R 都是 T 家族; R129: SRT 递归). -/
theorem single_symmetry_underdetermines (pat0 d : ℂ) (hd : d ≠ 0) :
    pat0 + (0 : ℂ) * d ≠ pat0 + (1 : ℂ) * d := by
  simpa using hd

end CompletePat1

end ZeroRelative
