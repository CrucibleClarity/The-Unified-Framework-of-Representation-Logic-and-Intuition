/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Formal.ZeroRelative.ComplexAxis
import Formal.Toolkit.MutualLocking
import Formal.Toolkit.MirrorFoldZero

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatDualityConvergence — 构造 (原点 0, 实轴数轴): 对偶内容收敛 (R163)

User question (2026-08-13, 承接素数对偶审计): "但是否可以构造一个原点和
一个数轴, 把这个对偶的内容收敛起来."

背景: 素数对偶 (C012-C014/C023): 8 整点成 4 共轭对 (z ↔ conj z, 每对
乘积 = p), 乘积 p⁴ 与 0 点视角 p⁻⁴ 互为倒数. 用户问: 能否构造 (原点,
数轴) 让这些对偶内容收敛 (统一).

★ 构造 (全部锚已证材料, ComplexAxis 为 ℝ×ℝ 无 i):
  原点 0 = ComplexAxis.zero (⟨0,0⟩), 数轴 = 实轴 (lift 的像 = proj 的不动点).

  对偶统一形式 = "对偶平均收敛":
  ① 共轭对 (z, conj z) 平均 = 数轴上的点: z + conj z = lift (2·proj z)
     — 对偶和收敛到数轴 (R047 分解的固定分量: conj 对虚部取反,
     b + (-b) = 0; R085: 镜像对收敛到折叠类).
  ② 倒数对 (p, 1/p) log 平均 = 原点 0: log p + log(1/p) = 0
     — 对偶和收敛到原点 (R110: log(1/a) = -log a, log 镜像对称;
     R085: 折叠类 0).
  ③ 乘积对 (p⁴, p⁻⁴) 互为倒数: 0 点视角 = 未反演视角的倒数 (R110).
  ④ 对偶对合: 1/(1/p) = p (倒数两次回自身; 共轭两次回自身,
     conj_involutive C011) — 对偶 = 对合, 收敛是往返无损的.

  pat 视角: 对偶内容 (共轭/倒数/乘积) 在 (原点 0, 实轴) 下统一为
  镜像对 (关于原点的对合), 对偶和收敛到数轴/原点 — 所有对偶是
  同一个折叠结构的实例 (R085/R143: 对称对还原).

Main theorems (本文件, 全部只锚本框架 + mathlib 基础):

1. `conj_pair_sums_to_axis`: 共轭对和 = 数轴上的点 (z + conj z = lift(2·proj z)).
2. `conj_pair_midpoint_on_axis`: 共轭对中点的虚分量 = 0 (中点在数轴上).
3. `log_pair_sums_origin`: 倒数对 log 和 = 0 (log p + log(1/p) = 0, R110).
4. `recip_pair_involutive`: 倒数对合 (1/(1/p) = p, p ≠ 0).
5. `recip_fourth_pair`: 乘积对互为倒数 ((1/p)^4 = 1/p^4 的形式).
6. `duality_fold_class`: 对偶和 = 折叠类 (R085: t + (-t) = 0 的实例).
7. `duality_convergence_perspective`: 全景 — 共轭对 → 数轴 ∧ 倒数对
   → 原点 0 ∧ 乘积对互为倒数.
-/

namespace ZeroRelative

namespace PatDualityConvergence

open ComplexAxis

/-! ## 1-2. 共轭对收敛到数轴

构造 (原点 0, 实轴): 共轭对 (z, conj z) 的和 = ⟨2a, 0⟩ = 数轴上的点
(实轴 = lift 的像, proj 不动; R047: conj 只翻转虚分量 (周期轴), 固定
实分量 (发散轴) — 对偶平均 = 发散轴投影). -/

/-- **共轭对和 = 数轴上的点**: z + conj z = lift (2·proj z) — 共轭对
(z, conj z) 的平均收敛到数轴 (实轴): 虚分量抵消 (b + (-b) = 0),
实分量加倍 (a + a = 2a) (R047: conj 固定发散分量/翻转周期分量;
R085: 镜像对收敛到折叠类). -/
theorem conj_pair_sums_to_axis (z : ComplexAxis) :
    z + conj z = lift (2 * proj z) := by
  ext <;> simp [conj, lift, proj, add] <;> ring

/-- **共轭对中点在数轴上**: (z + conj z) 的虚分量 = 0 — 对偶中点
落在数轴 (实轴) 上, 与 z 无关 (R047: 周期分量被 conj 翻转, 和抵消;
收敛到数轴 = 发散轴投影). -/
theorem conj_pair_midpoint_on_axis (z : ComplexAxis) :
    (z + conj z).b = 0 := by
  simp [conj, add]

/-! ## 3. 倒数对 log 和 = 原点 0

构造 (原点 0, log 数轴): 倒数对 (p, 1/p) 在 log 轴上关于原点 0 镜像
(R110: log(1/a) = -log a — log 双对称的镜像部分; R085: 折叠类 0). -/

/-- **倒数对 log 和 = 0**: log p + log(1/p) = 0 (p > 0) — 倒数对
(p, 1/p) 在 log 轴上关于原点 0 镜像: 对偶和收敛到原点 (R110
magnitude_pair_log_mirror; R085: 折叠类 0 — 对偶还原到折叠类). -/
theorem log_pair_sums_origin (p : ℝ) (hp : 0 < p) :
    Real.log p + Real.log (1 / p) = 0 := by
  rw [MutualLocking.magnitude_pair_log_mirror p hp]
  ring

/-! ## 4. 对偶对合: 倒数两次回自身

对偶 = 对合 (往返无损): 倒数两次回自身 1/(1/p) = p, 共轭两次回自身
(conj_involutive, C011) — 收敛是可逆的, 不丢信息 (R048: 单射 ⟹ 无损). -/

/-- **倒数对合**: 1/(1/p) = p (p ≠ 0) — 倒数对偶两次回自身, 往返
无损 (R110: 倒数对; R048: 对合 = 双射 = 无损; 与 conj_involutive
(C011) 同型 — 对偶 = 对合结构). -/
theorem recip_pair_involutive (p : ℝ) (hp : p ≠ 0) :
    1 / (1 / p) = p := by
  field_simp [hp]

/-! ## 5. 乘积对互为倒数

0 点视角 (recip) 的乘积对 = 未反演视角的倒数: (1/p)^4 与 p^4 互为
倒数 (R110: 倒数对; C023: 素数圆 8 整点乘积 p⁴ / 真 0 点视角 p⁻⁴). -/

/-- **乘积对互为倒数**: (1/p)^4 · p^4 = 1 (p ≠ 0) — 0 点视角乘积对
(1/p)^4 与未反演视角乘积对 p^4 互为倒数 (C023: 8 整点乘积 p⁴ / 0 点
视角 p⁻⁴; R110: 倒数对 — 对偶内容在 recip 下收敛为倒数). -/
theorem recip_fourth_pair (p : ℝ) (hp : p ≠ 0) :
    (1 / p) ^ 4 * p ^ 4 = 1 := by
  field_simp [hp]

/-! ## 6. 对偶和 = 折叠类

R085: 折叠类 0 = 镜像对的和收敛: t + (-t) = 0. 对偶 (u, v) 满足
v = f(u), f 对合且关于原点镜像 ⟹ u + v 收敛到折叠类 (数轴投影或
原点). -/

/-- **对偶和 = 折叠类**: t + (-t) = 0 — 镜像对 (对偶) 的和收敛到
折叠类 0 (R085 mirror_fixes_zero/zero_is_fold_class; 构造 (原点 0,
数轴): 对偶 = 关于原点的镜像, 对偶和 = 折叠类 — 素数对偶 (共轭/
倒数/乘积) 的统一形式). -/
theorem duality_fold_class (t : ℝ) : t + (-t) = 0 := by
  ring

/-! ## 7. 全景: 对偶内容在 (原点 0, 数轴) 下收敛

构造 (原点 0, 实轴数轴) 收敛全部对偶内容: ① 共轭对 (z, conj z)
平均 = 数轴上的点 (虚部抵消) ② 倒数对 (p, 1/p) log 平均 = 原点 0
(log 镜像) ③ 乘积对 (p⁴, p⁻⁴) 互为倒数 ④ 对偶对合往返无损
⑤ 对偶和 = 折叠类 (R085). -/

/-- **对偶收敛全景**: 共轭对和 = 数轴上的点 (z + conj z = lift(2·proj z))
∧ 倒数对 log 和 = 原点 0 (log p + log(1/p) = 0) ∧ 乘积对互为倒数
((1/p)^4·p^4 = 1) ∧ 对偶和 = 折叠类 (t + (-t) = 0) — 构造 (原点 0,
实轴数轴) 把素数对偶内容 (共轭/倒数/乘积, C012-C014/C023/R110) 统一
为镜像对收敛 (R085: 折叠类; R047: 共轭固定发散分量). -/
theorem duality_convergence_perspective (p : ℝ) (hp : 0 < p) (z : ComplexAxis) :
    z + conj z = lift (2 * proj z) ∧
    Real.log p + Real.log (1 / p) = 0 ∧
    (1 / p) ^ 4 * p ^ 4 = 1 ∧
    (∀ t : ℝ, t + (-t) = 0) := by
  constructor
  · exact conj_pair_sums_to_axis z
  · constructor
    · exact log_pair_sums_origin p hp
    · constructor
      · exact recip_fourth_pair p (ne_of_gt hp)
      · exact duality_fold_class

end PatDualityConvergence

end ZeroRelative
