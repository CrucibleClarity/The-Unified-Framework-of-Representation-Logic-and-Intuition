/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Ring
import Formal.Toolkit.PatConstruction
import Formal.Toolkit.OmnidirectionalUnit
import Formal.Toolkit.TimeArrowToPeriodAxis

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PhaseRelationLocking — ★相位关系锁定: Pat N 的收敛化

User instruction (R138, 2026-08-12): Pat N (R137) 是离散的发散链, 但发散与
收敛是同一个高维结构 (R047), 任何轴/方向/相位都要收敛到可数可达可构造的。
因此下一步不是多相位数, 而是相位之间的锁定 (phase-relation locking):
相位之间的关系, 与 pat0 自指循环等价 (R122), 所以可以用相同的方法
(R136 方向声明) 锁定位相之间的关系。

Main theorems:

1. `unlocked_phase_relation_collapses`: 相位关系未锁定 = pat0 自指循环 —
   相位差与互逆差同相位 (Δθ ≡ -Δθ, R122 机制: 方向 = 互逆方向 ⟹ 循环
   相位无净移动) ⟹ 双倍相位闭合: exp(2Δθ·I) = 1 — 折叠类 {0, π} 条件
   (R085: 0 = ±1 折叠类; R076: 相位折叠).
2. `phase_relation_locked_pair`: 用相同方法 (R136) 锁定位相之间的关系 —
   相位差按对称性一次性成对声明 (Δθ, -Δθ): declaredPair Δθ =
   declaredPair (-Δθ) (无序对, 无先后, 无特权相位).
3. `locked_phase_relation_composes`: 锁定后相位关系可加: (θ₃-θ₂) + (θ₂-θ₁)
   = θ₃-θ₁ (RulerPhase: 相位差可加, Ruler2Exam teleport_parameter_compose
   的相位形式) — 相位关系组成交换链.
4. `pat_chain_curls_to_circle`: Pat N (离散发散链) 经相位关系锁定蜷曲到
   相位环: exp(2π·((t+T)/T)·I) = exp(2π·(t/T)·I) (R055 机制: 时间轴蜷曲
   保映射) — 发散链收敛化.
5. `pat_chain_phase_finite`: Pat N 的相位在单位圆上 (‖exp(θ·I)‖ = 1) —
   收敛到可数可达可构造 (R059 单位根 n 槽环; R123 闭包 + R125/R126 棋盘
   可达面).
-/

namespace ZeroRelative

namespace PhaseRelationLocking

open ZeroRelative.OmnidirectionalUnit

/-! ## 1. 相位关系未锁定 = pat0 自指循环 (坍缩到折叠类)

相位之间的关系 = 相位差 Δθ = θ₂ - θ₁ (RulerPhase: 相位差 = 方向).
未锁定时, 相位差与其互逆差不可区分 (Δθ ≡ -Δθ) — 正是 R122 的机制
(方向 = 互逆方向 ⟹ 循环相位无净移动 ⟹ 全坍缩): 双倍相位闭合
exp(2Δθ·I) = 1, 即 Δθ 落在折叠类 {0, π} (R085: 0 = ±1 折叠类).
-/

/-- 相位关系: 相位差 Δθ = θ₂ - θ₁ (RulerPhase: 相位差 = 方向). -/
def phaseRelation (θ₁ θ₂ : ℝ) : ℝ := θ₂ - θ₁

/-- **相位关系未锁定 = pat0 自指循环**: 相位差与互逆差同相位
(exp(Δθ·I) = exp(-Δθ·I), R122 机制: 方向 = 互逆方向 ⟹ 循环相位无净
移动) ⟹ 双倍相位闭合 exp(2Δθ·I) = 1 — 相位差坍缩到折叠类 {0, π}
(R085: 0 = ±1 折叠类; R076: 相位折叠链). -/
theorem unlocked_phase_relation_collapses (Δθ : ℝ)
    (h : Complex.exp (Δθ * Complex.I) = Complex.exp ((-Δθ) * Complex.I)) :
    Complex.exp (2 * Δθ * Complex.I) = 1 := by
  have harg : 2 * Δθ * Complex.I = Δθ * Complex.I + Δθ * Complex.I := by ring
  calc
    Complex.exp (2 * Δθ * Complex.I)
        = Complex.exp (Δθ * Complex.I) * Complex.exp (Δθ * Complex.I) := by
          rw [harg, Complex.exp_add]
    _ = Complex.exp (Δθ * Complex.I) * Complex.exp ((-Δθ) * Complex.I) := by
          nth_rw 2 [h]
    _ = 1 := by
          have hz : Δθ * Complex.I + (-Δθ) * Complex.I = 0 := by ring
          rw [← Complex.exp_add, hz]
          simp

/-! ## 2. 相位关系锁定: 用相同方法 (R136 成对一次性声明)

与锁定方向相同 (R136 ②③): 相位差按对称性一次性成对声明 (Δθ, -Δθ) —
无序对, 无先后, 无特权相位. -/

/-- **相位关系锁定 = 成对一次性声明**: 相位差 Δθ 按对称性成对声明,
与方向声明同一方法 (R136 ②③): declaredPair Δθ = declaredPair (-Δθ)
(无序对, 无先后, 无特权相位 — R119 互逆结构固有). -/
theorem phase_relation_locked_pair (Δθ : ℝ) :
    declaredPair Δθ = declaredPair (-Δθ) :=
  one_shot_pair_order_free Δθ

/-! ## 3. 锁定后相位关系可加 (交换链)

RulerPhase: 对齐相位 = 解构所有基点变换; Ruler2Exam
teleport_parameter_compose: 相位差可加. -/

/-- **锁定后相位关系可加**: (θ₃-θ₂) + (θ₂-θ₁) = θ₃-θ₁ — 相位关系组成
交换链 (RulerPhase: 相位差可加; Ruler2Exam teleport_parameter_compose
的相位形式; RulerFourier: 相位解构). -/
theorem locked_phase_relation_composes (θ₁ θ₂ θ₃ : ℝ) :
    phaseRelation θ₂ θ₃ + phaseRelation θ₁ θ₂ = phaseRelation θ₁ θ₃ := by
  unfold phaseRelation
  ring

/-! ## 4. Pat N (离散发散链) 经相位锁定蜷曲到相位环

R055: 时间轴蜷曲保映射 — t ↦ exp(2π·t/T·I) 周期 T. Pat N 是发散链
(等距 {pat0 + n·d}, R137), 相位关系锁定后蜷曲到环 ⟹ 收敛化. -/

/-- **Pat N 蜷曲到相位环 (R055 机制)**: exp(2π·((t+T)/T)·I) =
exp(2π·(t/T)·I) 对 t = patChain pat0 d n — 离散发散链经相位锁定周期化,
未来 = 环上相位重现 (RulerTimeLoop). -/
theorem pat_chain_curls_to_circle (pat0 d T : ℝ) (hT : T ≠ 0) (n : ℕ) :
    Complex.exp (2 * Real.pi * ((PatConstruction.patChain pat0 d n + T) / T) * Complex.I) =
      Complex.exp (2 * Real.pi * (PatConstruction.patChain pat0 d n / T) * Complex.I) :=
  TimeArrowToPeriodAxis.time_axis_curls_to_circle T hT (PatConstruction.patChain pat0 d n)

/-! ## 5. Pat N 的相位在单位圆上 (收敛到可数可达可构造)

R059: 单位根 n 槽环有限化; R123/R125/R126: 闭包的可计算表面 (棋盘). -/

/-- **Pat N 的相位在单位圆上**: ‖exp(2π·(pat n / T)·I)‖ = 1 — 相位锁定
后 Pat N 的每个点都落在单位圆上 (R059: 可数可达可构造的单位根 n 槽环;
R125/R126: 闭包的可达网格). -/
theorem pat_chain_phase_finite (pat0 d T : ℝ) (hT : T ≠ 0) (n : ℕ) :
    ‖Complex.exp (2 * Real.pi * (PatConstruction.patChain pat0 d n / T) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

end PhaseRelationLocking

end ZeroRelative
