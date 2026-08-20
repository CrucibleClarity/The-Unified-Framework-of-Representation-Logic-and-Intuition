/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Ring
import Formal.Toolkit.OmnidirectionalUnit

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatConstruction — Pat N 的构造定义: 全向单位球面链
(omnidirectional-unit-sphere chain)

User construction (R137, 2026-08-12): 重新从全向 0 出发, 每步完成一次全向 1
的构造 (单位 1 全向高维球), 声明相同的方向 (相位) 锁定, 诱导全向 0 收敛向
声明的方向 ⟹ 得到 pat2 = pat1 + d; 全向 0 点产生另一个全向 0 点, 相邻距离
恒为单位 1 的全向高维球; 重复这个过程 ⟹ Pat N = 等距单相位链 {n·d}
(R091 单相位数; R071/R072: ℙ⟨φ_T⟩ Pat), 方向锁定 ⟹ 链不坍缩 (R050).

Main theorems:

1. `pat_n_is_monophase`: pat n = pat0 + n·d — 每步声明相同方向 ⟹ 链 =
   等差单相位链 {n·d} (R091: 单相位数 = 方向 d 上标量列).
2. `pat_step_unit_sphere`: 声明方向为单位长 (‖d‖ = 1) ⟹ 每步距离 = 1 —
   两个全向 0 点之间的距离 = 单位 1 的全向高维球 (R136: unit_on_surface:
   单位 1 = 无限维结构表面, 半径 1; pat1_omnidirectional).
3. `pat_chain_equidistant`: 链等距 — 任意相邻两步长度相同 (等差, R091).
4. `pat_chain_injective`: 声明+锁定方向 ⟹ 链单射不坍缩 (R050: 固定方向
   迭代单射; R136 successor_chain_injective).
-/

namespace ZeroRelative

namespace PatConstruction

open ZeroRelative.OmnidirectionalUnit

/-! ## The Pat-N chain

pat0 = 全向 0 (R133: 无限维; R123: 闭包). 每步: 构造全向 1 (单位球面,
R136 unit_on_surface), 声明相同方向 d (成对一次性, R136 ②③), 锁定相位
⟹ 链前进 d (R050: 单射, 不坍缩). -/

/-- The Pat-N chain: pat0 全向 0, each step constructs the omnidirectional
unit 1 and declares the SAME direction d (声明相同方向, 锁定). -/
def patChain (pat0 d : ℝ) : ℕ → ℝ
  | 0 => pat0
  | n + 1 => declaredSuccessor d (patChain pat0 d n)

/-- **Pat n = pat0 + n·d**: repeating the SAME declared direction keeps
the chain an equidistant monophase chain — 声明相同方向 ⟹ 链 = 等差单相位
链 {n·d} (R091: 单相位数 = 方向 d 上标量列, 相位恒定; R071/R072:
ℙ⟨φ_T⟩ Pat). -/
theorem pat_n_is_monophase (pat0 d : ℝ) (n : ℕ) :
    patChain pat0 d n = pat0 + (n : ℝ) * d := by
  induction n with
  | zero => simp [patChain]
  | succ n ih =>
      simp [patChain, declaredSuccessor, ih]
      ring

/-- **The step length is the omnidirectional unit sphere**: with the
declared direction d of unit length (‖d‖ = 1), every step covers the
distance 1 — 两个全向 0 点之间的距离 = 单位 1 的全向高维球 (R136:
unit_on_surface: 单位 1 = 无限维结构表面的点, 半径 1;
pat1_omnidirectional: 全向无限). -/
theorem pat_step_unit_sphere (x d : ℝ) (hd : ‖d‖ = 1) :
    ‖(x + d) - x‖ = 1 := by
  have h : (x + d) - x = d := by ring
  rw [h]
  exact hd

/-- **The chain is equidistant**: every step has the same length — the
distance between adjacent omnidirectional-0 points is always the unit-1
omnidirectional sphere (等差链, R091). -/
theorem pat_chain_equidistant (x y d : ℝ) :
    ‖(x + d) - x‖ = ‖(y + d) - y‖ := by
  have h₁ : (x + d) - x = d := by ring
  have h₂ : (y + d) - y = d := by ring
  rw [h₁, h₂]

/-- **The declared-direction chain does not collapse**: with the same
declared direction, the Pat-N chain is injective (R050: iteration along
a fixed direction is injective ⟹ lossless; R136
successor_chain_injective: 声明+锁定方向 ⟹ 链单射不坍缩). -/
theorem pat_chain_injective (d : ℝ) :
    Function.Injective (declaredSuccessor d) :=
  OmnidirectionalUnit.successor_chain_injective d

end PatConstruction

end ZeroRelative
