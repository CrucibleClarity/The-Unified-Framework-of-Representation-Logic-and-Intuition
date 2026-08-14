/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Formal.Toolkit.MutualLocking
import Formal.Toolkit.OrthogonalAxes
import Formal.Toolkit.DivergencePeriodSymmetry

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatAxisDual — ★互锁 = 单位 1 的两重对称分解 (1 和 i 还原后的 1)

User correction (R143, 2026-08-12): pat 相位互锁定理揭示了一个方向 — 互锁的
两组向量组成一个 2×2 矩阵, 这两个分量本身就是 1 和 i 还原后的 1.

The two components of the mutual-lock matrix (R139 declaredMatrix
!![θ, r; -θ, 1/r]) are each the reduction of a symmetry pair to the unit 1:

1. **相位分量 (i 轴) = i 还原后的 1**: 相位对 (θ, -θ) 组合
   exp(iθ) · exp(-iθ) = 1 — i 轴 (周期轴, R047 J) 上的对称对还原为
   单位 1 (R085: 对称对坍缩到基点; R090: 乘法单位 1 = exp(0i), 相位 0).
2. **数值分量 (1 轴) = 1 还原后的 1**: 数值对 (r, 1/r) 组合
   r · (1/r) = 1 — 1 轴 (发散轴, R047 lift) 上的对称对还原为乘法基点 1
   (R110: log 镜像对称 log(1/a) = -log a; R089: 乘法基点 1).
3. **互锁 = 单位 1 的两重对称分解**: 1 分裂为两组对称性 (相位方向 i +
   数值方向 1), 每组对称对都还原回 1 — 相位锁定 = i 与 1 的锁定.
4. **背景**: pat 轴 (1) 与 ipat 轴 (i) 正交共享基点 0 (R047), 无损互映
   (R051 rot90), 无穷维闭包上的映射 (R054/R133).

Main theorems:

1. `phase_pair_reduces_to_one`: ★相位分量 = i 还原后的 1 —
   exp(iθ)·exp(-iθ) = 1 (i 轴对称对还原为单位 1).
2. `magnitude_pair_reduces_to_one`: ★数值分量 = 1 还原后的 1 —
   r·(1/r) = 1 (1 轴对称对还原为乘法基点 1).
3. `mutual_lock_reduces_to_one`: 互锁矩阵的两个分量都还原为 1 (互锁 =
   单位 1 的两重对称分解).
4. `pat_ipat_orthogonal`: 两轴正交 (R047).
5. `pat_ipat_lossless`: rot90 无损互映 (R051).
6. `phase_on_ipat_axis`: 相位在 i 轴 (周期轴) (R047/C011).
7. `magnitude_on_pat_axis`: 数值对在 1 轴 (发散轴, log 镜像) (R110).
-/

namespace ZeroRelative

namespace PatAxisDual

/-! ## 1. ★相位分量 = i 还原后的 1

互锁矩阵的相位列 (θ, -θ) (R139 declaredMatrix): 相位对组合
exp(iθ) · exp(-iθ) = exp(0) = 1 — i 轴 (周期轴, R047 J) 上的对称对
还原为单位 1 (R085: 0 = ±1 折叠类; R090: 乘法单位 1 = exp(0i) 相位 0;
R074: 镜像 S 对合 S² = id 同型). -/

/-- **★相位分量 = i 还原后的 1**: exp(iθ) · exp(-iθ) = 1 — 相位对
(θ, -θ) 在 i 轴 (周期轴) 上的组合还原为单位 1 (R139 互锁矩阵的相位列;
R085: 对称对坍缩到基点; R090: 乘法单位 1 = exp(0i), 三轴单位元交汇于
相位 0). -/
theorem phase_pair_reduces_to_one (θ : ℝ) :
    Complex.exp (θ * Complex.I) * Complex.exp ((-θ) * Complex.I) = 1 := by
  have h : θ * Complex.I + (-θ) * Complex.I = 0 := by ring
  rw [← Complex.exp_add, h]
  simp

/-! ## 2. ★数值分量 = 1 还原后的 1

互锁矩阵的数值列 (r, 1/r) (R139 declaredMatrix): 数值对组合
r · (1/r) = 1 — 1 轴 (发散轴, R047 lift) 上的对称对还原为乘法基点 1
(R110: log 镜像对称 log(1/a) = -log a; R089: 乘法基点 1 经 log 漂移到
加法基点 0). -/

/-- **★数值分量 = 1 还原后的 1**: r · (1/r) = 1 (r ≠ 0) — 数值对
(r, 1/r) 在 1 轴 (发散轴) 上的组合还原为乘法基点 1 (R139 互锁矩阵的
数值列; R110: log 镜像对称; R089: 乘法基点 1). -/
theorem magnitude_pair_reduces_to_one (r : ℝ) (hr : r ≠ 0) :
    r * (1 / r) = 1 := by
  field_simp [hr]

/-! ## 3. 互锁 = 单位 1 的两重对称分解

互锁矩阵的两个分量 (相位列, 数值列) 都是 1 的还原: 1 分裂为两组对称性
(相位方向 i + 数值方向 1), 每组对称对都还原回 1 — 相位锁定 = i 与 1
的锁定 (R139 矩阵非奇异; R085/R090 还原锚点). -/

/-- **互锁 = 单位 1 的两重对称分解**: 相位对还原 (exp(iθ)·exp(-iθ) = 1)
且数值对还原 (r·(1/r) = 1) — 互锁矩阵的两个分量本身就是 1 和 i 还原后的
1 (R139 declaredMatrix; R085: 对称对坍缩到基点; R090: 单位元交汇). -/
theorem mutual_lock_reduces_to_one (θ r : ℝ) (hr : r ≠ 0) :
    Complex.exp (θ * Complex.I) * Complex.exp ((-θ) * Complex.I) = 1 ∧
      r * (1 / r) = 1 := by
  constructor
  · exact phase_pair_reduces_to_one θ
  · exact magnitude_pair_reduces_to_one r hr

/-! ## 4. 背景: pat 轴 (1) 与 ipat 轴 (i) 的对偶

R047: 发散轴 (lift, 1) 与周期轴 (J, i) 是共轭对称性 S 的两个特征空间,
正交, 共享基点 0. R051: rot90 无损互映. -/

/-- **两轴正交**: proj (lift t * J) = 0 — 周期方向 (i 轴) 在发散轴
(1 轴) 上投影为 0 (R047 orthogonal_axes; C011: 投影丢方向分量). -/
theorem pat_ipat_orthogonal (t : ℝ) :
    ZeroRelative.ComplexAxis.proj (ZeroRelative.ComplexAxis.lift t * ZeroRelative.ComplexAxis.J) = 0 :=
  ZeroRelative.ComplexAxis.orthogonal_axes t

/-- **pat 轴 ↔ ipat 轴无损映射**: rot90 (×J) 是双射 (周期 4,
rot90⁴ = id) — 两轴互映无损 (R051 rot90_bijective; R052/R054:
任意方向轴无损映射; R133: 无限维闭包). -/
theorem pat_ipat_lossless : Function.Bijective ZeroRelative.ComplexAxis.rot90 :=
  ZeroRelative.OrthogonalAxes.rot90_bijective

/-! ## 5. 相位在 i 轴, 数值对在 1 轴

相位 θ 是 i 轴 (周期方向) 上的点; 数值对 (r, 1/r) 是 1 轴 (发散方向)
上的对称性. -/

/-- **相位在 i 轴 (周期轴)**: ‖exp(θ·I)‖ = 1 — 相位 θ 是周期方向
(i 轴) 上的单位点 (R047: J 轴; C011: 投影不可观测; R136
pat1_omnidirectional). -/
theorem phase_on_ipat_axis (θ : ℝ) :
    ‖Complex.exp (θ * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

/-- **数值对在 1 轴 (发散轴)**: log(1/r) = -log r (r > 0) — 数值的
倒数对在 log 轴上是镜像对 (R110: log 双对称的镜像部分; R139
magnitude_pair_log_mirror: 互锁矩阵的数值列; R089: log 把乘法基点 1
漂移到加法基点 0). -/
theorem magnitude_on_pat_axis (r : ℝ) (hr : 0 < r) :
    Real.log (1 / r) = -Real.log r :=
  MutualLocking.magnitude_pair_log_mirror r hr

end PatAxisDual

end ZeroRelative
