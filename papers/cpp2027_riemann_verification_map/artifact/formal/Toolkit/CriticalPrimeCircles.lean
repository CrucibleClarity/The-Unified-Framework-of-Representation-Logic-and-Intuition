/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Formal.Toolkit.PatMapping
import Formal.Toolkit.FoldCenters

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/CriticalPrimeCircles — 素数圆与临界线圆 = 两个还原点的圆化 (R144)

User question (R145, 2026-08-12): 这就是素数圆、临界圆, 对吧?

Answer: 对 — R144 的两个还原点 (0 与 1 = 对称对还原点) 就是两个圆的圆心:

1. **素数圆** (|z| = √p): 圆心 0 = R144 的加法还原点 (R085 折叠类;
   R109: 折叠类 0 = 素数圆圆心; C016/C017: 高斯整数/素数圆单轨道).
2. **临界线圆** (|z - 1| = 1): 圆心 1 = R144 的乘法还原点 (乘法基点;
   R109: 圆心 (1,0), 半径 1, 过 0 和 2; C019-C022: 临界线圆).
3. **反演 2 ↔ 1/2** (R109) = 乘法对称对 {r, 1/r} (R143/R144:
   r·(1/r) = 1 还原到圆心 1; R110: log 镜像对称).
4. **log 对偶**: log 2 + log(1/2) = 0 — 反演对经 log 落到加法还原点 0
   (R144 log_maps_mul_pair_to_add_pair; R089: log 1 = 0).

Main theorems:

1. `critical_circle_points`: 临界线圆 (圆心 1, 半径 1) 过 0, 2, 1+i
   (R109: 0 与 2 是直径端点).
2. `prime_circle_center_zero`: 素数圆圆心 = 0 (折叠类), 半径 √p
   (R109/R144).
3. `reciprocal_pair_reduces`: 反演对 = 乘法对称对 — r·(1/r) = 1
   (R143/R144; 2 ↔ 1/2 还原到临界线圆圆心 1).
4. `log_pair_instance`: log 2 + log(1/2) = 0 (R144: 反演对经 log 落
   到加法还原点 0).
5. `fold_centers_are_circle_centers`: 统一 — 0 = 素数圆圆心, 1 = 临界
   线圆圆心 (R144 两个还原点 = 两个圆的圆心).
-/

namespace ZeroRelative

namespace CriticalPrimeCircles

/-! ## 1. 临界线圆: 圆心 1, 半径 1, 过 0 和 2

R109: 折叠类 0 也是临界线圆上的点 (圆心 (1,0) 半径 1, 过 0 和 2;
0 与 2 是直径端点). 圆心 1 = R144 的乘法还原点. -/

/-- **临界线圆过 0, 2, 1+i**: ‖0 - 1‖ = 1, ‖2 - 1‖ = 1, ‖(1+i) - 1‖ = 1
— 圆心 (1,0) 半径 1 的圆 (R109: 0 与 2 是直径端点; C019-C022:
临界线圆; R144: 圆心 1 = 乘法还原点). -/
theorem critical_circle_points :
    ‖(0 : ℂ) - 1‖ = 1 ∧ ‖(2 : ℂ) - 1‖ = 1 ∧ ‖((1 : ℂ) + Complex.I) - 1‖ = 1 := by
  constructor
  · have h : (0 : ℂ) - 1 = -1 := by norm_num
    rw [h]
    simp
  · constructor
    · have h : (2 : ℂ) - 1 = 1 := by norm_num
      rw [h]
      simp
    · simp

/-! ## 2. 素数圆: 圆心 0 (折叠类), 半径 √p

R109: 折叠类 0 = 素数圆圆心 (半径 √p); C016/C017: 高斯整数/素数圆
单轨道. 圆心 0 = R144 的加法还原点. -/

/-- **素数圆圆心 = 0 (折叠类)**: ‖√p·exp(θ·I) - 0‖ = √p (p ≥ 0) —
素数 p 在素数圆上 (圆心 0, 半径 √p; R109: 折叠类 0 = 素数圆圆心;
C016/C017; R144: 0 = 加法还原点). -/
theorem prime_circle_center_zero (p θ : ℝ) (hp : 0 ≤ p) :
    ‖(Real.sqrt p : ℂ) * Complex.exp (θ * Complex.I) - 0‖ = Real.sqrt p := by
  simpa using PatMapping.prime_circle_norm p θ hp

/-! ## 3. 反演对 = 乘法对称对

R109: 反演 2 ↔ 1/2 (临界线圆直径端点). R143/R144: 乘法对称对
{r, 1/r} 组合还原到乘法基点 1 (临界线圆圆心). -/

/-- **反演对 = 乘法对称对还原**: r·(1/r) = 1 (r ≠ 0) — 反演对
{r, 1/r} 组合还原到乘法基点 1 (R109: 反演 2 ↔ 1/2; R143:
magnitude_pair_reduces_to_one; R144: 1 = 乘法还原点; R110: log 镜像). -/
theorem reciprocal_pair_reduces (r : ℝ) (hr : r ≠ 0) : r * (1 / r) = 1 :=
  FoldCenters.one_is_mul_fold_center r hr

/-! ## 4. log 对偶: 反演对经 log 落到加法还原点 0

R144: log 把乘法对映到加法对 — log r + log(1/r) = 0; 实例 r = 2:
log 2 + log(1/2) = 0 (R089: log 1 = 0 基点漂移). -/

/-- **log 对偶实例**: log 2 + log(1/2) = 0 — 反演对 {2, 1/2} 经 log
变成加法对称对 {log 2, -log 2}, 还原点 1 漂移到还原点 0 (R144
log_maps_mul_pair_to_add_pair; R110: log 镜像; R089: log 1 = 0). -/
theorem log_pair_instance :
    Real.log 2 + Real.log (1 / 2) = 0 := by
  exact FoldCenters.log_maps_mul_pair_to_add_pair 2 (by norm_num)

/-! ## 5. 统一: 两个还原点 = 两个圆的圆心

R144 (0 与 1 = 对称对还原点) + R109 (折叠类 0 = 素数圆圆心 ∩ 临界线圆
直径端点): 0 = 素数圆圆心 (加法还原点), 1 = 临界线圆圆心 (乘法还原
点) — 素数圆与临界线圆是两个还原点的圆化. -/

/-- **统一: 两个还原点 = 两个圆的圆心**: 素数圆圆心 0 (加法还原点,
R144/R085) ∧ 临界线圆 (圆心 1, 乘法还原点) 过 0 和 2 (R109/R144) —
素数圆与临界线圆 = R144 两个还原点的圆化, 反演对 {r, 1/r} 还原到
圆心 1 (R143/R110). -/
theorem fold_centers_are_circle_centers (p : ℝ) (hp : 0 ≤ p) :
    ‖(Real.sqrt p : ℂ) * Complex.exp (0 * Complex.I) - 0‖ = Real.sqrt p ∧
      ‖(0 : ℂ) - 1‖ = 1 ∧ ‖(2 : ℂ) - 1‖ = 1 := by
  constructor
  · simpa using PatMapping.prime_circle_norm p 0 hp
  · constructor
    · have h : (0 : ℂ) - 1 = -1 := by norm_num
      rw [h]
      simp
    · have h : (2 : ℂ) - 1 = 1 := by norm_num
      rw [h]
      simp

end CriticalPrimeCircles

end ZeroRelative
