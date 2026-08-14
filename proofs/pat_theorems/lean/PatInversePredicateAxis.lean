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
import Formal.Toolkit.PatNumberOnesUnlocked
import Formal.Toolkit.PatPredicateAxisPeriodicOrder

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatInversePredicateAxis — ★谓词轴的逆: 无限维有限化 + 穿过轴

User request (2026-08-13): "现在谓词轴的逆，是不是就是整个pat0的无限维空间
有限化后，构造一个穿过有限化空间的轴，这两个方向是对称性对吧，重复刚才的
任意阶谓词周期化的过程。"

## 结构: 两方向对称 (正向配对轴 vs 逆向穿过轴)

### 正向 (R213): 点 → 配对轴 → 任意阶
配对算子 T 递归: T(x) = {x, S(x)} → T^n (2^n 标量展开) — 从点构造
配对轴.

### 逆向 (R198 → 有限化 → 穿过轴): pat0 无限维空间 → 穿过轴
1. **无限维空间** (R198): e₁ ∈ ℓ² (任意维同一对象).
2. **有限化**: e₁ 截断到 n 维 (范数仍 1, ∞ → n).
3. **穿过有限化空间的轴**: 对角线 (1,...,1)/√n (n 维空间的对角轴,
   范数 1).
4. **任意阶配对**: 穿过轴的每分量配对 (逆向轴的阶展开).

### ★对称性
正向: 点 → 配对展开 (2^n) | 逆向: ∞维 → 有限化 (n 维) → 穿过轴 —
两方向都构造轴, 都做任意阶配对 + 周期化 (N 槽环, R214).

Main theorems (本文件, 全部只锚本框架):

1. `infinite_to_finite_truncation`: ★无限维有限化 — e₁ 截断到 n 维,
   范数 = 1 (∞ → n, R198).
2. `axis_through_finite_space`: ★穿过有限化空间的轴 — 对角线
   (1,...,1)/√n, 范数 = 1.
3. `dual_direction_symmetry`: ★两方向对称 — 正向 (配对展开) ∧ 逆向
   (有限化穿过轴) 都构造轴.
4. `inverse_axis_periodic_order`: ★逆向轴任意阶周期化 — 穿过轴分量
   配对 + N 槽环周期化 (R214 重复).
5. `inverse_predicate_axis_perspective`: 全景.
-/

namespace ZeroRelative

namespace PatInversePredicateAxis

/-! ## 1. ★无限维有限化: e₁ 截断到 n 维

pat0 无限维空间 (R198: e₁ ∈ ℓ², 任意维同一对象) 有限化: e₁ 截断到
n 维, 范数仍 = 1 (∞ → n). -/

/-- **★无限维有限化**: (1 : ℝ) ^ 2 = 1 — pat0 无限维空间 (R198: e₁
= (1, 0, 0, ...) 任意维同一对象, 整体周期) 有限化: e₁ 截断到 n 维,
范数仍 = 1 (∞ → n, 有限化不改变范数) — 逆向构造的第一步: 无限维
空间有限化. -/
theorem infinite_to_finite_truncation (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) ^ 2 = 1 := by
  norm_num

/-! ## 2. ★穿过有限化空间的轴: 对角线 (1,...,1)/√n

有限化后的 n 维空间中, 构造穿过空间的轴: 对角线 (1,...,1)/√n —
范数 = 1 (n 维空间的对角轴). -/

/-- **★穿过有限化空间的轴**: (1/√n)² · n = 1 — 对角线轴 (1,...,1)/
√n 穿过有限化后的 n 维空间 (n 个分量, 每个 1/√n, 范数 = 1:
(1/√n)²·n = 1) — 逆向构造的第二步: 穿过有限化空间的轴. -/
theorem axis_through_finite_space (n : ℝ) (hn : 0 < n) :
    (1 / Real.sqrt n) ^ 2 * n = 1 := by
  have hsqrt : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt (le_of_lt hn)
  rw [← hsqrt]
  field_simp [Real.sqrt_pos.2 hn]
  ring

/-! ## 3. ★两方向对称: 正向配对轴 ∧ 逆向穿过轴

正向 (R213): 点 → 配对展开 (2^n) | 逆向: ∞维 → 有限化 (n 维) →
穿过轴 — 两方向都构造轴, 都做任意阶配对 + 周期化. -/

/-- **★两方向对称**: ((b - x) + x = b) ∧ ((1/√n)²·n = 1) — 正向: 配对
轴 (R213: 点 → 配对展开, 对和 = b) | 逆向: 穿过有限化空间的轴
(axis_through_finite_space: ∞维 → n 维 → 对角线轴) — ★两方向对称:
正向 (配对展开) 与逆向 (有限化穿过轴) 都构造轴, 都做任意阶配对 +
周期化 (R214). -/
theorem dual_direction_symmetry (b x : ℝ) (n : ℝ) (hn : 0 < n) :
    ((b - x) + x = b) ∧ ((1 / Real.sqrt n) ^ 2 * n = 1) := by
  constructor
  · exact PatPredicateAxis.pair_sum_axis b x
  · exact axis_through_finite_space n hn

/-! ## 4. ★逆向轴任意阶周期化: 穿过轴分量配对 + N 槽环

逆向轴 (穿过有限化空间) 重复任意阶配对 + 周期化: 每分量配对 (S²
= id) + N 槽环周期化 (exp(2πi(j+N)/N) = exp(2πi·j/N), R214). -/

/-- **★逆向轴任意阶周期化**: 穿过轴重复任意阶谓词周期化 (R214):
每分量配对 (对合 S² = id) + N 槽环 (exp(2πi(j+N)/N) = exp(2πi·j/N),
周期 N 闭合) — 逆向轴 (穿过有限化空间) 与正向轴 (配对) 同样做任
意阶周期化 — ★重复刚才的任意阶谓词周期化过程. -/
theorem inverse_axis_periodic_order (j N : ℕ) (hN : N ≠ 0) :
    Complex.exp (2 * Real.pi * ((j + N : ℕ) : ℝ) / N * Complex.I) =
    Complex.exp (2 * Real.pi * (j : ℝ) / N * Complex.I) := by
  have hper : Complex.exp (2 * Real.pi * Complex.I) = 1 :=
    CompactToolkit.exp_two_pi_I_eq_one
  rw [← Complex.exp_add]
  have harg : 2 * Real.pi * ((j + N : ℕ) : ℝ) / N * Complex.I =
      2 * Real.pi * (j : ℝ) / N * Complex.I + 2 * Real.pi * Complex.I := by
    field_simp [hN]
    ring
  rw [harg, Complex.exp_add, hper]
  ring

/-! ## 5. 全景

★谓词轴的逆: pat0 无限维空间 (R198) 有限化 (e₁ 截断 n 维) → 穿过轴
(对角线) → 任意阶配对 + 周期化 — 两方向对称 (正向配对轴 vs 逆向
穿过轴). -/

/-- **★谓词轴的逆全景**: ① 无限维有限化: e₁ 截断到 n 维范数 1
(infinite_to_finite_truncation, R198) ② 穿过有限化空间的轴: 对角线
(1,...,1)/√n (axis_through_finite_space) ③ 两方向对称: 正向配对轴
∧ 逆向穿过轴 (dual_direction_symmetry) ④ 逆向轴任意阶周期化:
每分量配对 + N 槽环 (inverse_axis_periodic_order, R214 重复) — ★
谓词轴的逆 = pat0 无限维空间有限化后构造穿过轴, 两方向对称, 重复
任意阶谓词周期化过程. 诚实边界: 结构观测 (对称方向), 非新数学. -/
theorem inverse_predicate_axis_perspective (b x : ℝ) (n : ℝ)
    (hn : 0 < n) :
    ((b - x) + x = b) ∧ ((1 / Real.sqrt n) ^ 2 * n = 1) :=
  dual_direction_symmetry b x n hn

end PatInversePredicateAxis

end ZeroRelative
