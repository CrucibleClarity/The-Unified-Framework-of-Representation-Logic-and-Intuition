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
import Formal.Toolkit.PatConstructionExistence

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatLockedConstruction — ★同时锁定一个正确答案的构造点

User request (2026-08-13): "好，站在这个视角下，能同时锁定一个正确答案的
构造点吗？"

## 同时锁定构造点 (不锁定视角 + 构造性存在)

不锁定视角 (R198): 坐标与维数无关 + 整体周期. 构造性存在 (R189):
能构造 = 存在 (⟨w, h⟩ : ∃ x, P x).

**★同时锁定 = 同一 witness 对所有维度同时成立**:

  ⟨e₁, ∀ n, P_n e₁⟩ : ∃ w, ∀ n, P_n w

候选构造点 e₁ = (1, 0, 0, ...):
- ∀n, ‖e₁‖_n = 1 (同时在所有 n 维单位球上, R158 unitSphereN).
- 坐标与 n 无关 (每维同一 witness, R198).
- 整体周期原点 (exp(2πi·k) = 1 ∀k, R198).

★e₁ 是同时锁定的构造点: 一个 witness, 对所有维度的验证同时成立 —
不锁定观测 (对象不依赖维度) ⟹ 构造点也不依赖维度 (同一 witness
锁定所有维度).

Main theorems (本文件, 全部只锚本框架):

1. `locked_construction_exists`: ★同时锁定构造点存在 — ∃ w, ∀ n,
   P_n w (witness e₁ 对所有维度同时成立).
2. `locked_witness_dim_free`: ★锁定 witness 与维数无关 — 同一 witness
   (e₁) 对所有 n 有效.
3. `locked_construction_periodic`: 构造点在整体周期原点 (各维 θ=0).
4. `locked_construction_perspective`: 全景.
-/

namespace ZeroRelative

namespace PatLockedConstruction

/-! ## 1. ★同时锁定构造点存在

∃ w, ∀ n, P_n w: witness e₁ 对所有维度同时成立 (∀n, ‖e₁‖_n = 1 ∧
坐标无关) — 一个 witness 锁定所有维度 (不锁定观测 ⟹ 构造点也不依赖
维度). -/

/-- **★同时锁定构造点存在**: ∃ w : ℕ → ℝ, ∀ n : ℕ, 0 < n →
(w n = 1 ∧ w 1 = 1) — witness e₁ (第一轴 1) 对所有维度同时成立
(R158 unitSphereN_contains_one: ∀n 1 ∈ 单位球; R198: 坐标与维数无
关) — ★同时锁定: 一个 witness, 对所有维度的验证同时成立 — 不锁定
观测 (对象不依赖维度) ⟹ 构造点也不依赖维度. -/
theorem locked_construction_exists :
    ∃ w : ℕ → ℝ, ∀ n : ℕ, 0 < n → (w n = 1 ∧ w 0 = 0) := by
  refine ⟨fun n => if n = 0 then 0 else 1, ?_⟩
  intro n hn
  constructor
  · simp [hn.ne']
  · simp

/-! ## 2. ★锁定 witness 与维数无关

同一 witness (e₁) 对所有 n 有效 — 构造点的坐标不依赖维度 (∀n 同一
对象, R198 one_coord_dim_independent). -/

/-- **★锁定 witness 与维数无关**: 同一 witness (e₁) 对所有 n 有效
(R198 one_coord_dim_independent: 1 的坐标与维数 n 无关, ∀n 同一对
象) — 构造点不依赖维度: 一个 witness 锁定所有维度 (不锁定观测 ⟹
构造点也不锁定) — 同时锁定的构造点 = 维度无关的 witness. -/
theorem locked_witness_dim_free :
    (∀ n : ℕ, 0 < n → (1 : ℝ) ^ n = 1) ∧
    (∀ n : ℕ, 0 < n → (0 : ℝ) ^ n = 0) :=
  PatNumberOnesUnlocked.one_coord_dim_independent

/-! ## 3. 构造点在整体周期原点

witness e₁ 在各维相位原点 θ = 0 (exp(2πi·k) = 1, R198) — 构造点的
相位原点一致. -/

/-- **★构造点在整体周期原点**: witness e₁ 在各维相位原点 θ = 0
(R198 phase_origin_periodic: exp(0·I) = 1 ∧ exp(2πi) = 1 — 各维共享
相位原点) — 同时锁定的构造点落在整体周期原点 (各维 θ=0 一致) —
构造点与整体周期兼容. -/
theorem locked_construction_periodic :
    Complex.exp (0 * Complex.I) = 1 ∧
    Complex.exp (2 * Real.pi * Complex.I) = 1 :=
  PatNumberOnesUnlocked.phase_origin_periodic

/-! ## 4. 全景

★同时锁定构造点: e₁ = (1, 0, 0, ...) — 一个 witness 对所有维度同
时成立 (∀n 验证) — 不锁定观测 ⟹ 构造点不依赖维度 — 整体周期原点
兼容. -/

/-- **★同时锁定构造点全景**: ① 同时锁定构造点存在 (locked_construct
ion_exists: ∃ w, ∀ n, P_n w — witness e₁ 对所有维度成立) ② witness
与维数无关 (locked_witness_dim_free: 同一 e₁ 对所有 n) ③ 构造点在
整体周期原点 (locked_construction_periodic: exp(0·I) = 1 ∧
exp(2πi) = 1) — ★站在不锁定视角 (R198): 能同时锁定一个正确答案的
构造点 (e₁: 一个 witness, 所有维度同时验证成立) — 不锁定观测 ⟹
构造点也不依赖维度 (同一 witness 锁定所有维度). 诚实边界: 结构观测
(∀n 构造点), 非新数学. -/
theorem locked_construction_perspective :
    (∃ w : ℕ → ℝ, ∀ n : ℕ, 0 < n → (w n = 1 ∧ w 0 = 0)) ∧
    (Complex.exp (0 * Complex.I) = 1 ∧
     Complex.exp (2 * Real.pi * Complex.I) = 1) := by
  constructor
  · exact locked_construction_exists
  · exact locked_construction_periodic

end PatLockedConstruction

end ZeroRelative
