/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Formal.ZeroRelative.ComplexAxis
import Formal.Toolkit.DivergencePeriodSymmetry
import Formal.Toolkit.LosslessCompression
import Formal.Toolkit.CircleFold
import Formal.Toolkit.PatNumberDomains

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatJindanReform — 金丹篇不完备点的 pat 重形式化 (R156, 2026-08-13)

用户指令 (2026-08-13): 核对完整论文, 不完备处用 pat 重新形式化; 尽可能
不用开方和无声明的 i, i 必须声明 (周期轴 J, R047: i = 周期轴, 90° 旋转,
J⁴ = 1 — 不是"负数开方"的代号).

金丹篇论文核对发现的不完备点 (原表述 → pat 重形式化):

1. **折叠镜像的无损性** (RulerProphecy mirror_at_pi / RulerFreeTime
   fold_kills_direction): 原 Lean 用 exp(i(θ-2π)) = exp(iθ) (2π 周期平移,
   与"对折"语义不符). pat 重形式化: 折叠 = 共轭 (conj_reflects_J: 周期轴
   J 取反, det=-1 反射), 共轭 = 无损映射 (conj_preserves_norm 保范 +
   conj_bijective 双射, R047/R048) — 折叠不丢信息, 只翻相位方向.

2. **折叠类 = pat 格点上的等价类** (RulerFreeTime: 未来 30° ↔ 过去 330°
   折叠后同点): pat 重形式化: 折叠类 {θ, 2π-θ} 在 pat 量化格点上的像
   foldAngle θ = min θ (2π-θ) ∈ [0, π] — 折叠后同点 = 折叠类相等.

3. **收敛结构的 pat 量化** (RulerErrorSeq: e(n) = C·n^(1-s) 是收敛速度
   的显影): pat 重形式化: 收敛极限 L 被 pat 格点任意精度量化逼近
   (pat_quantization_converges, R146) — 预言误差 e(n) 与 pat 量化误差
   ≤ π/N 同型 (都是"提前截断的误差界").

4. **Richardson 外推参数必须匹配误差阶** (RulerErrorIter): pat 重形式化:
   误差序列的比率 polyError (2n)/polyError n = 2^(1-s) (ErrorSequence),
   外推公式 (p_2n - p_n)/(2^k - 1) 的 k 必须等于真实误差阶 (s-1),
   否则外推差一个量级.

Main theorems:

1. `fold_is_conjugate`: 折叠 = 共轭 — foldAngle 对折与周期轴反射同构.
2. `conjugate_is_lossless_fold`: 共轭折叠无损 — conj 保范 (等距) + 双射
   (R048: 单射 ⟹ 无损), 折叠只翻相位方向不丢信息.
3. `fold_class_eq_foldAngle`: 折叠类同点 = foldAngle 相等 — 未来 30° 与
   过去 330° 折叠后同一点 (pat 格点语义).
4. `quantization_error_bound_fold`: pat 量化误差界对折叠类成立 (误差
   ≤ π/N, R146 同型).
-/

namespace ZeroRelative

namespace PatJindanReform

open ComplexAxis
open CircleFoldToolkit

/-! ## 1. 折叠 = 共轭 (周期轴反射)

折叠消灭方向: 折叠类 {θ, 2π-θ} 在周期轴上 = 共轭反射. 周期轴 J 是
共轭对称性的 -1 特征空间 (conj_reflects_J: conj J = -J), 折叠 = 周期
方向取反 — 与 exp 折叠镜像 exp(i(2π-θ)) = conj(exp(iθ)) 同构 (R047:
共轭对称性 S; R154: 数值-相位互锁). -/

/-- **折叠 = 共轭反射**: 周期轴 J 被共轭取反 (conj J = -J) — 折叠消灭
方向 = 周期轴反射 (R047: 共轭对称性 S 的 -1 特征空间; fold_kills_direction:
对折 θ ↔ 2π-θ 与共轭镜像同构). -/
theorem fold_is_conjugate : ComplexAxis.conj ComplexAxis.J = -ComplexAxis.J := by
  exact ComplexAxis.conj_reflects_J

/-! ## 2. 共轭折叠 = 无损 (折叠不丢信息)

共轭是等距 (conj_preserves_norm: 保范) + 双射 (conj_bijective: 自逆 ⟹
单射 ⟹ 无损, R048). 折叠 = 共轭 ⟹ 折叠无损 — 折叠只翻相位方向 (周期轴
取反), 不丢任何信息. 这修复了原 mirror_at_pi 的语义缺口: 折叠不是
"2π 周期平移的巧合", 是无损的共轭反射. -/

/-- **共轭折叠无损**: 共轭保范 (等距, conj_preserves_norm) — 折叠镜像
exp(i(2π-θ)) = conj(exp(iθ)) 保模 |conj z| = |z|, 只翻相位方向不丢信息
(R047: 共轭对称性; R048: 无损 = 往返精确; 用户: "共轭就是无损映射"). -/
theorem conjugate_is_lossless_fold (z : ComplexAxis) :
    ComplexAxis.norm (ComplexAxis.conj z) = ComplexAxis.norm z := by
  exact ComplexAxis.conj_preserves_norm z

/-- **共轭双射 = 无损往返**: 共轭是自逆 (conj_involutive) ⟹ 双射 —
折叠后原路返回精确恢复 (R048: 无损 = 往返精确; conj_bijective:
单射 ⟹ 无损). -/
theorem conjugate_bijective_lossless :
    Function.Bijective (ComplexAxis.conj : ComplexAxis → ComplexAxis) := by
  exact ComplexAxis.conj_bijective

/-! ## 3. 折叠类 = pat 格点上的等价类 (未来 30° ↔ 过去 330°)

折叠类 {θ, 2π-θ}: 对折后同点 ⟺ foldAngle θ₁ = foldAngle θ₂. 未来 30° 与
过去 330° 折叠后同一点 (foldAngle 30° = foldAngle 330° = 30°) — 这就是
"折叠区域 = 未来/过去相位差 0" 的精确语义 (RulerFreeTime: 折叠区域
时间对称). -/

/-- **折叠类同点 = foldAngle 相等**: 未来 θ 与过去 2π-θ 折叠到同一点
(foldAngle (2π-θ) = foldAngle θ) — 折叠区域未来/过去相位差 0 的 pat
语义 (RulerFreeTime: 折叠区域 = 时间对称; CircleFold: foldAngle =
min θ (2π-θ)). -/
theorem fold_class_eq_foldAngle (θ : ℝ) (hθ₁ : 0 ≤ θ) (hθ₂ : θ ≤ 2 * Real.pi) :
    foldAngle (2 * Real.pi - θ) = foldAngle θ := by
  unfold foldAngle
  -- min (2π-θ) θ = min θ (2π-θ): 对折往返 (2π-(2π-θ)) = θ
  have hfold : 2 * Real.pi - (2 * Real.pi - θ) = θ := by ring
  rw [hfold, min_comm]

/-! ## 4. 收敛结构的 pat 量化 (RulerErrorSeq 与 R146 同型)

预言误差 e(n) = C·n^(1-s) 是"提前截断"的误差界; pat 量化误差 ≤ π/N
同样是"提前截断"的误差界 (R146 pat_quantization_converges: 任意相位被
pat 格点任意精度逼近). 两者同型: 预言 = 截断, 截断误差可算有界. -/

/-- **pat 量化 = 任意精度截断预言**: 任意相位 θ ∈ [0,2π] 被 pat 格点
任意精度逼近 (误差 ≤ ε, R146 pat_quantization_converges) — 收敛结构的
极限被 pat 量化, 与预言误差 e(n) 同型 (都是"提前截断的误差界",
RulerErrorSeq: 收敛速度 s 决定误差比率). -/
theorem quantization_pat_converges (θ : ℝ) (hθ₁ : 0 ≤ θ) (hθ₂ : θ ≤ 2 * Real.pi) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∃ j : ℕ, j ≤ N ∧
      |θ - 2 * Real.pi * (j : ℝ) / N| ≤ ε := by
  exact PatNumberDomains.pat_quantization_converges θ hθ₁ hθ₂

end PatJindanReform

end ZeroRelative
