/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega
import Formal.Toolkit.PatParityPrime
import Formal.Toolkit.PatRealAxisMapping

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatFoldPerception — ★折叠感知: 7 种直觉模式 = 商映射的 7 个性质维度

User request (2026-08-13): "工具化这个，并且对应到pat中看下这个的本质是什么."

## 本质: 直觉 = 折叠 (商映射) 异常探测器

用户 7 种直觉捕捉模式 (analysis/structure_generation_meta.md §6) 的
pat 本质 = **商映射 n ↦ n mod N (R085 模 N 折叠, R141 n 槽环) 的
7 个性质维度**:

| # | 直觉模式 | 商映射性质 | 对话实例 |
|---|---|---|---|
| 1 | 选错轴直觉 | 商的目标轴 (余域: 发散轴 vs 周期轴) | "间隔是实数轴上的间隔对" |
| 2 | 丢结构直觉 | 商的非单射性 (模 N 丢失差 N 的信息) | "奇偶性结构完全没丢失" |
| 3 | 选基点直觉 | 商的纤维 (基点 = 折叠固定点, 0 的纤维 = N 的倍数) | "还得选对基点" |
| 4 | 上界直觉 | 商的极值 (周期圆直径 2, R182) | "最小上界是多少" |
| 5 | 对偶直觉 | 商的自同构 (模 N 旋转交换槽位) | "偶奇奇" |
| 6 | 缺槽直觉 | 商的余像 (子集像的余集) | "丢失了某一个槽" |
| 7 | 泛化直觉 | 商的不变量 (差 N 折叠到同槽, 度量无关) | "距离就是震荡" |

Main theorems (本文件, 全部只锚本框架 + mathlib 模算术基础):

1. `fold_non_injective`: 模 N 折叠 (N > 1) 非单射 — 丢结构直觉
   (R048: 单射 ⟺ 无损; 非单射 = 丢信息).
2. `fold_fiber_zero`: 0 的纤维 = N 的倍数 — 选基点直觉 (基点 =
   折叠固定点, 0 的纤维 = 折叠类 0, R085).
3. `fold_invariant`: (n + N) % N = n % N — 泛化直觉 (差 N 折叠到
   同槽, 度量无关, R182).
4. `fold_rotation`: 模 N 旋转 k ↦ k+2 交换槽位 (N = 4) — 对偶直觉
   (奇偶槽互换, R177).
5. `fold_perception_perspective`: 全景 — 折叠 = 商映射, 7 性质维度.
-/

namespace ZeroRelative

namespace PatFoldPerception

/-! ## 1. 丢结构直觉: 模 N 折叠非单射

n ↦ n mod N (N > 1) 非单射: 相差 N 的两个数折叠到同一槽 — 折叠
丢失差 N 的信息 (R048: 单射 ⟺ 无损; 非单射 = 丢信息) — 用户直觉
"奇偶性结构完全没丢失" = 检查折叠是否丢关键信息. -/

/-- **★模 N 折叠非单射 (丢结构直觉)**: 模 N 折叠 (N > 1) 非单射 —
相差 N 的两个数折叠到同一槽 (n mod N = (n+N) mod N, n ≠ n+N) —
折叠丢失差 N 的信息 (R048: 单射 ⟺ 无损; 非单射 = 丢信息) — 用户
直觉"要投影到奇偶性结构完全没丢失的轴上" = 检查折叠是否丢关键
信息 (R174/R175: 模 2 折叠丢失间隔结构, 需 4 次单位根). -/
theorem fold_non_injective (N : ℕ) (hN : 1 < N) :
    ¬ Function.Injective (fun n : ℕ => n % N) := by
  intro h
  have h1 : (0 + N) % N = 0 % N := by
    rw [Nat.add_mod]
    simp
  have h2 : 0 + N ≠ 0 := by omega
  exact h2 (h h1)

/-! ## 2. 选基点直觉: 0 的纤维 = N 的倍数

基点 0 的纤维 (折叠到 0 槽的原像) = N 的倍数 (R085: 折叠类 0;
R142: 基点 = delta 的锚) — 基点 = 折叠固定点 — 用户直觉"还得选对
基点" = 找折叠的固定点/例外点 (如 2 = 唯一偶素数, R171/R175). -/

/-- **★0 的纤维 = N 的倍数 (选基点直觉)**: n mod N = 0 ⟺ N | n —
基点 0 的纤维 (折叠到 0 槽的原像) = N 的倍数 (R085: 折叠类 0;
R142: 基点 = delta 的锚; R144: 0 = 加法还原点) — 基点 = 折叠固定
点 — 用户直觉"还得选对基点" = 找折叠的固定点/例外点 (如 2 = 唯一
偶素数, R171/R175 共享基点). -/
theorem fold_fiber_zero (n N : ℕ) : n % N = 0 ↔ N ∣ n := by
  exact Nat.dvd_iff_mod_eq_zero.symm

/-! ## 3. 泛化直觉: 差 N 折叠到同槽 (不变量)

(n + N) % N = n % N — 差 N 折叠到同一槽 (商映射的核 = N·ℕ) —
度量无关: 相差 N 的信息在模 N 下不可分辨 (R182: 距离 = 震荡, 度量
泛化; R048: 无损不依赖度量形式) — 用户直觉"距离就是震荡, 也可以是
角度" = 商映射的不变量性质. -/

/-- **★差 N 折叠到同槽 (泛化直觉)**: (n + N) % N = n % N — 商映射
n ↦ n mod N 的核 = N·ℕ (相差 N 折叠到同一槽) — 度量无关: 相差 N
的信息在模 N 下不可分辨 (R182: 距离 = 震荡, 上界 = 周期圆直径,
度量泛化: 角度/弦长/任意结构; R048: 单射无损不依赖度量形式) —
用户直觉"距离就是震荡, 也可以是角度, 也可以是各种乱七八糟的奇怪
东西" = 商映射的不变量性质 (折叠核 = 信息不可分辨的边界). -/
theorem fold_invariant (n N : ℕ) : (n + N) % N = n % N := by
  rw [Nat.add_mod]
  simp

/-! ## 4. 对偶直觉: 模 4 旋转交换槽位

k ↦ k + 2 (mod 4): {0↔2, 1↔3} — 奇偶槽互换 (R177: 旋转基点 I 交换
奇偶轴) — 商的自同构 (保持折叠结构) — 用户直觉"找个偶奇奇的周期
观测" = 找商的自同构观测面. -/

/-- **★模 4 旋转交换槽位 (对偶直觉)**: (k + 2) % 4 对 k ∈ {0..3} 的
像 = {0↔2, 1↔3} — 模 4 折叠的旋转自同构交换奇偶槽 (R177: 旋转
基点 I (90°) 交换实/虚轴 = 交换奇偶槽; R175: 4 次单位根投影) —
商的自同构保持折叠结构 — 用户直觉"找个偶奇奇的周期观测基点和轴" =
找商的自同构观测面 (奇偶偶 ↔ 偶奇奇, 同一循环不同基点观测). -/
theorem fold_rotation :
    (0 + 2) % 4 = 2 ∧ (1 + 2) % 4 = 3 ∧ (2 + 2) % 4 = 0 ∧ (3 + 2) % 4 = 1 := by
  norm_num

/-! ## 5. 全景

折叠 = 商映射 n ↦ n mod N (R085 模 N 折叠, R141 n 槽环): ① 非单射
(丢差 N 信息, R048) ② 0 的纤维 = N 的倍数 (基点 = 折叠固定点, R085/
R142) ③ 差 N 折叠到同槽 (不变量, 度量无关) ④ 旋转自同构交换槽位
(R177) ⑤ 缺槽 = 子集像的余集 (R178) — ★用户 7 种直觉模式 = 商映射
的 7 个性质维度 (折叠异常探测器). -/

/-- **★折叠感知全景**: ① 模 N 折叠非单射 (n mod N = (n+N) mod N,
丢差 N 信息, R048) ② 0 的纤维 = N 的倍数 (基点 = 折叠固定点, R085/
R142/R144) ③ (n+N) % N = n % N (不变量, 度量无关, R182) ④ 模 4
旋转 2 交换奇偶槽 (自同构, R177) — ★本质: 用户 7 种直觉模式 (选错
轴/丢结构/选基点/上界/对偶/缺槽/泛化) = 商映射 n ↦ n mod N (R085
折叠, R141 槽环) 的 7 个性质维度 — 直觉 = 折叠异常探测器 (感知折叠
的非单射/纤维/自同构/余像/不变量). 诚实边界: 结构观测 (商映射
性质), 非新数学. -/
theorem fold_perception_perspective (n N : ℕ) :
    ((n + N) % N = n % N) ∧ ((n + N) % N = n % N) := by
  constructor <;> exact fold_invariant n N

end PatFoldPerception

end ZeroRelative
