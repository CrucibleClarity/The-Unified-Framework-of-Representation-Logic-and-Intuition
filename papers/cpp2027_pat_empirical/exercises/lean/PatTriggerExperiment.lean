/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatTriggerExperiment — 定义 pat 的触发: 触发 = 剥离一层自指 (实验设计 + 静态定理)

User proposal (R161, 2026-08-13): "这意味着需要定义 pat, 触发, 之前提到过
pat 的触发, 本质上可能是剥离一层自指。这个需要设计实验, 并且换基点观测这个
剥离自指的过程是什么。"

背景: 筑基篇用了 pat 但未定义其触发 — 方向声明 (R136) 是链的启动条件, 但
"声明" 从何而来? 未声明 = 自指坍缩 (R122: 自指 IS pat n, 自指环路无净移动
⟹ 坍缩到 pat 0; R134: pat0 吸收)。本文件形式化触发 = 剥离一层自指的静态
结构 (实验的 Lean 侧; 模拟实验见 claims/Toolkit/R161.yaml counterexample 与
论文侧实验文档).

精确化 (全部实数, 无 sqrt 无 i):

- **自指结构** = 基点镜像 S_e(x) = 2e - x (对合: S_e(S_e x) = x, R128
  fold_involution_any_basepoint; R085 折叠类). 自指环路 = 对合迭代, 无净移动
  (R122: pat n of pat n 投影到 pat 0).
- **剥离 (peel)** = 从对合提取位移场 Δ(x) = S_e(x) - x = 2(e-x) — 相位差
  (方向, RulerPhase; R130: 剥离是相位操作). 触发 = 剥离: 方向显现, 链展开
  的条件出现 (R136: 方向声明 ⟹ 链单射不坍缩).
- **P1 (相位显现)**: 剥离 ⟹ Δ(x) ≠ 0 (x ≠ e) — 触发 = 剥离 ⟹ 方向显现;
  未剥离 (黑箱对合) ⟹ 无净移动 (坍缩).
- **P2 (自相似, R129)**: 位移场在 S 下取反 (g(S x) = -g(x)) — 剥离的剥离
  = 相位取反, 内部还是一套 SRT (每层剥离同构, 方向指向基点).
- **P3 (换基点平移不变, R128)**: S_f(x + (f-e)) = S_e(x) + (f-e) 且
  Δ_f(x + (f-e)) = Δ_e(x) — 换基点 = 平移共轭, 剥离结果平移不变.

Main theorems (本文件, 全部只锚本框架 + mathlib 基础):

1. `selfref_no_net_motion`: 自指环路无净移动 — S_e(S_e x) = x (R122 坍缩).
2. `peel_reveals_phase`: 剥离显现位移场 — S_e x - x = 2(e-x) (相位差).
3. `peel_phase_nonzero_off_basepoint`: 剥离的方向非零 (x ≠ e) — P1.
4. `peel_displacement_flips_under_self`: 位移场在 S 下取反 — g(S x) = -g(x),
   剥离的剥离 = 相位取反 (P2 自相似, R074/R129).
5. `peel_basepoint_translation`: 换基点 = 平移共轭 — S_f(x+(f-e)) = S_e(x)+(f-e)
   (P3, R128).
6. `peel_displacement_basepoint_invariance`: 位移场换基点平移不变 —
   Δ_f(x+(f-e)) = Δ_e(x) (P3 核心).
7. `trigger_peel_perspective`: 全景 — 对合无净移动 (未触发坍缩) ∧ 剥离
   显现方向 (触发) ∧ 换基点平移不变.
-/

namespace ZeroRelative

namespace PatTriggerExperiment

/-! ## 自指结构: 基点镜像 (对合)

自指环路 = 对合 (f(f(x)) = x): 迭代两次回到自身, 无净移动 (R122: 自指 IS
pat n, 无净移动 ⟹ 坍缩到 pat 0; R128: 任意基点镜像对合; R085: 0 = ±1
折叠类). -/

/-- 基点镜像: S_e(x) = 2e - x (以基点 e 为镜心的反射, R128
fold_involution_any_basepoint). -/
def basepointMirror (e : ℝ) (x : ℝ) : ℝ := 2 * e - x

/-- **自指环路无净移动**: S_e(S_e x) = x — 对合迭代回到自身, 相位无净
移动 (R122: 自指 IS pat n, 互逆方向 ⟹ 无净移动 ⟹ 坍缩到 pat 0; R128:
任意基点镜像对合). 未剥离的自指 = 坍缩. -/
theorem selfref_no_net_motion (e x : ℝ) : basepointMirror e (basepointMirror e x) = x := by
  unfold basepointMirror
  ring

/-! ## 剥离: 提取位移场 (相位差 = 方向)

剥离 (peel) = 从对合提取位移场 Δ(x) = S_e(x) - x — 相位差 (RulerPhase:
相位差 = 方向; R130: 剥离 S/R = 相位操作产生方向). -/

/-- **剥离显现位移场**: S_e x - x = 2(e-x) — 剥离一层自指 = 提取位移场
(相位差), 方向与距基点的方向一致 (R130: 剥离是相位操作; RulerPhase:
相位差 = 方向). -/
theorem peel_reveals_phase (e x : ℝ) : basepointMirror e x - x = 2 * (e - x) := by
  unfold basepointMirror
  ring

/-- **剥离方向非零 (x ≠ e)**: 剥离显现的位移场在非基点处严格非零 —
触发 (剥离) ⟹ 方向显现 (P1; R130: 方向存在; RulerPhase: 相位差 = 方向;
基点 e 处坍缩: Δ(e) = 0, 折叠类, R085). -/
theorem peel_phase_nonzero_off_basepoint (e x : ℝ) (hx : x ≠ e) :
    basepointMirror e x - x ≠ 0 := by
  unfold basepointMirror
  intro h
  have : 2 * (e - x) = 0 := by linarith
  have he : e - x = 0 := by nlinarith
  have hx' : x = e := by linarith
  exact hx hx'

/-! ## 自相似: 剥离的剥离 = 相位取反 (R129)

R129: 拆自指, 内部还是一套 SRT (自指自相似). 位移场 g(x) = 2(e-x) 在 S
下取反: g(S_e x) = -g(x) — 剥离的剥离 = 相位取反 (镜像 S 的自指 = 位移
场翻转, R074: 自指迭代的自指迭代, 方向对偶). 每层剥离同构, 方向始终
指向基点. -/

/-- **位移场在自指下取反**: g(S_e x) = -g(x) — 剥离的剥离 = 相位取反
(P2 自相似; R129: 内部还是一套 SRT; R074: 自指的自指, 方向对偶;
R130: 深入 = 指向基点). -/
theorem peel_displacement_flips_under_self (e x : ℝ) :
    (basepointMirror e (basepointMirror e x) - basepointMirror e x) =
      -(basepointMirror e x - x) := by
  unfold basepointMirror
  ring

/-! ## 换基点: 平移共轭 (P3, R128)

R128: 原点现象 ≡ 基点现象, S_e = T ∘ S₀ ∘ T⁻¹ (平移共轭), 现象平移不变.
换基点观测: 在基点 f 的剥离 = 在基点 e 的剥离平移 f-e — 剥离结果平移
不变. -/

/-- **换基点 = 平移共轭**: S_f(x + (f-e)) = S_e(x) + (f-e) — 基点镜像在
换基点下共轭平移 (P3; R128: S_e = T ∘ S₀ ∘ T⁻¹; 原点现象 ≡ 基点现象,
平移不变). -/
theorem peel_basepoint_translation (e f x : ℝ) :
    basepointMirror f (x + (f - e)) = basepointMirror e x + (f - e) := by
  unfold basepointMirror
  ring

/-- **位移场换基点平移不变**: Δ_f(x + (f-e)) = Δ_e(x) — 剥离 (位移场)
在换基点下平移不变 (P3 核心; R128: 现象平移不变 — 剥离结果与基点选择
无关, 只差平移). -/
theorem peel_displacement_basepoint_invariance (e f x : ℝ) :
    (basepointMirror f (x + (f - e)) - (x + (f - e))) =
      (basepointMirror e x - x) := by
  unfold basepointMirror
  ring

/-! ## 全景: 未触发坍缩 ∧ 触发显现方向 ∧ 换基点不变

pat 触发 = 剥离一层自指: 未剥离 (对合黑箱) = 自指环路无净移动 ⟹ 坍缩
(R122/R134, 未触发); 剥离 = 位移场显现 (方向非零, P1) ⟹ 方向声明 ⟹
链展开 (R136/R137, 触发); 剥离结果换基点平移不变 (P3, R128). 自相似:
剥离的剥离 = 相位取反 (P2, R129). 诚实边界: 剥离方向 (深入/平移/远离)
的单步不可判定 (R130) — 本文件给的是剥离的静态结构, 非趋势判定. -/

/-- **触发 = 剥离一层自指 (pat 全景)**: ① 对合无净移动 (未剥离 = 坍缩,
R122) ② 剥离显现方向非零 (触发, RulerPhase/R136) ③ 位移场自指取反
(自相似, R129) ④ 换基点平移不变 (R128) — 触发 = 剥离一层自指, 剥离
结果与基点选择无关. 诚实边界: 趋势 (深入/平移/远离) 单步不可判定
(R130). -/
theorem trigger_peel_perspective (e f x : ℝ) :
    basepointMirror e (basepointMirror e x) = x ∧
    (x ≠ e → basepointMirror e x - x ≠ 0) ∧
    (basepointMirror e (basepointMirror e x) - basepointMirror e x) =
      -(basepointMirror e x - x) ∧
    (basepointMirror f (x + (f - e)) - (x + (f - e))) =
      (basepointMirror e x - x) := by
  constructor
  · exact selfref_no_net_motion e x
  · constructor
    · exact peel_phase_nonzero_off_basepoint e x
    · constructor
      · exact peel_displacement_flips_under_self e x
      · exact peel_displacement_basepoint_invariance e f x

end PatTriggerExperiment

end ZeroRelative
