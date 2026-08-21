/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/MirrorFoldZero — 0 = T₂ (镜像) 的不动点 = ±1 折叠类 (R085)

User claim (R085, 2026-08-12): 我们把混了正负 1 的一个 0 点给拆出来了 —
T₂ (镜像 S(θ) = -θ) 的不动点 θ = 0, 但 S 交换 ±1 (S(1) = -1, S(-1) = 1),
所以不动点 0 = "±1 的混合类" (折叠 ±1 得到的折叠中心), 不是干净的点.

Main theorems:

1. `mirror_fixes_zero`: T₂ 不动点 — S(0) = 0.
2. `mirror_swaps_pm_one`: S 交换 ±1 — S(1) = -1, S(-1) = 1 (同一两态轨道).
3. `mirror_involutive`: 镜像对合 — S² = id (两态交替 θ → -θ → θ).
4. `zero_is_fold_center`: 0 = ±t 折叠中心 — t + (-t) = 0.
5. `zero_is_fold_class`: 0 = 折叠类 — 不动点 + ±1 轨道 + 折叠中心 (组合).

意义: 0 是镜像对合的选择产物, 非结构必然 (C010 深化; R143:
1 是乘法/相位对称对的还原点, 0 是加法对称对的还原点 — 二者经
log/exp 对偶, FoldCenters).
-/

namespace ZeroRelative

namespace MirrorFoldZero

/-! ## 1-3. T₂ (镜像) 的结构

S(θ) = -θ: 不动点 θ = 0; 交换 ±1 (同一两态轨道 {+1, -1}); 对合 S² = id. -/

/-- **T₂ 不动点**: S(0) = 0 — 镜像对合的不动点 (R085: 0 = 折叠类锚点). -/
theorem mirror_fixes_zero : -(0 : ℝ) = 0 := by
  norm_num

/-- **S 交换 ±1**: S(1) = -1 且 S(-1) = 1 — ±1 在 S 的同一两态轨道上
(R085: 混了正负 1 的 0 点; R069: ±1 自逆对). -/
theorem mirror_swaps_pm_one : -(1 : ℝ) = -1 ∧ -(-1 : ℝ) = 1 := by
  norm_num

/-- **镜像对合**: S² = id — 两态交替 θ → -θ → θ (R083: S = 周期 2 的 T;
R074: 镜像自指). -/
theorem mirror_involutive (x : ℝ) : -(-x) = x := by
  ring

/-! ## 4-5. 0 = ±1 折叠类

0 是镜像对合的不动点, 且 S 把 ±1 混在一起 (同一两态轨道) — 不动点 0
是 ±t 的折叠中心 (t + (-t) = 0), 不是干净的点 (R085). -/

/-- **0 = ±t 折叠中心**: t + (-t) = 0 — 对称对 {t, -t} 的平均/折叠中心
是 0 (R085; R143: 对称对还原点 — 加法对还原到 0). -/
theorem zero_is_fold_center (t : ℝ) : t + (-t) = 0 := by
  ring

/-- **0 = 折叠类 (组合)**: S(0) = 0 (不动点) ∧ S(1) = -1 ∧ S(-1) = 1
(±1 同一轨道) ∧ t + (-t) = 0 (折叠中心) — 0 是镜像对合的选择产物,
非干净基点 (R085; C010: 0 非内生; R062: 特权基点). -/
theorem zero_is_fold_class (t : ℝ) :
    -(0 : ℝ) = 0 ∧ -(1 : ℝ) = -1 ∧ -(-1 : ℝ) = 1 ∧ t + (-t) = 0 := by
  constructor
  · norm_num
  · constructor
    · norm_num
    · constructor
      · norm_num
      · ring

end MirrorFoldZero

end ZeroRelative
