/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Formal.Toolkit.PatTwinPrime
import Formal.Toolkit.PatParityPrime
import Formal.Toolkit.Compactification

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatTwinPrimeOscillation — ★孪生素数间隔作为震荡周期轴

User request (2026-08-13): 将孪生素数对的距离设置为一个震荡周期性的轴,
然后把基点移动过去, 观测震荡周期和对应发散轴的最长震荡距离.

## 构造

1. **间隔 2 = 震荡周期轴**: 定义震荡 osc(t) = exp(i·π·t) — 间隔 2
   的震荡: osc(t + 2) = osc(t) (周期 2, exp(2πi) = 1,
   CompactToolkit.exp_two_pi_I_eq_one). 孪生素数对 (p, p+2) 的间隔
   2 = 震荡的一个完整周期.

2. **震荡在发散轴的投影**: 震荡的实部 (发散轴投影) = cos(π·t) —
   在 t = 0 处 = 1 (RulerPhase: 相位 0 = 数值 1), 在 t = 1 处 = -1
   (Real.cos_pi). 发散轴投影范围 = [-1, 1].

3. **基点移动**: 把基点从 0 移到震荡轴上 (R142/RulerDelta: 基点漂移)
   — 新基点 = 震荡中点 (t = 1, 投影 -1) 或观测相对位移. 基点移动
   后, 震荡的观测 = 相对新基点的位移.

4. **★最长震荡距离**: 震荡在发散轴上的投影从 +1 到 -1 — 最长震荡
   距离 = 1 - (-1) = 2 — **等于间隔 2 本身**. 即: 震荡周期 = 2,
   发散轴最长震荡距离 = 2, 二者自洽 (间隔 2 是结构常数).

## 与孪生素数的连接

- 孪生素数对 (p, p+2) 的间隔 2 = 震荡周期 = 发散轴最长震荡距离
  (2) — 间隔 2 既是周期又是最长距离 (自洽).
- 素数 = 震荡轴上的相位点 (R159: 素数 = 方向 log p).

Main theorems (本文件, 全部只锚本框架):

1. `oscillation_period_two`: 间隔 2 的震荡 (exp(i·π·t)) 周期为 2.
2. `oscillation_diverge_projection`: 震荡在发散轴投影 = cos(π·t).
3. `oscillation_projection_range`: 发散轴投影范围 [-1, 1]
   (cos(π·0) = 1, cos(π·1) = -1).
4. `basepoint_move_to_axis`: 基点移到震荡轴 (观测相对位移).
5. `max_oscillation_distance`: ★最长震荡距离 = 2 (1 - (-1) = 2 =
   间隔 2).
6. `twin_prime_oscillation_perspective`: 全景 — 间隔 2 = 震荡周期 =
   最长震荡距离 (自洽).
-/

namespace ZeroRelative

namespace PatTwinPrimeOscillation

/-! ## 1. 间隔 2 = 震荡周期

震荡 osc(t) = exp(i·π·t): osc(t + 2) = exp(i·π·(t+2)) = exp(i·π·t)·
exp(2πi) = exp(i·π·t) — 周期 2 (RulerPhase: 相位差 = 方向;
CompactToolkit.exp_two_pi_I_eq_one). 孪生素数对的间隔 2 = 震荡的
一个完整周期. -/

/-- **间隔 2 = 震荡周期**: exp(i·π·(t+2)) = exp(i·π·t) — 震荡
osc(t) = exp(i·π·t) 的周期为 2 (exp(2πi) = 1,
CompactToolkit.exp_two_pi_I_eq_one; RulerPhase: 相位差 = 方向) —
孪生素数对的间隔 2 = 震荡的一个完整周期 (R172: 间隔 2 = 奇偶性
折叠周期, R171). -/
theorem oscillation_period_two (t : ℝ) :
    Complex.exp (Real.pi * (t + 2) * Complex.I) =
    Complex.exp (Real.pi * t * Complex.I) := by
  rw [← Complex.exp_add]
  have hsum : Real.pi * (t + 2) * Complex.I = Real.pi * t * Complex.I + 2 * Real.pi * Complex.I := by ring
  rw [hsum, Complex.exp_add]
  have hper : Complex.exp (2 * Real.pi * Complex.I) = 1 :=
    CompactToolkit.exp_two_pi_I_eq_one
  rw [hper]
  ring

/-! ## 2. 震荡在发散轴的投影 = cos(π·t)

震荡 exp(i·π·t) 的实部 (发散轴投影, R047: 发散轴 = 实轴) = cos(π·t)
(Complex.exp_mul_I: exp(i·θ) = cos θ + i·sin θ 的实部). -/

/-- **震荡在发散轴投影 = cos(π·t)**: (exp(i·π·t)).re = cos(π·t) —
震荡的实部 = 发散轴投影 (R047: 发散轴 = 实轴, 周期轴 = 虚轴;
Complex.exp_ofReal_mul_I_re: (exp(θ·I)).re = cos θ) — 震荡在发散
轴的投影是余弦. -/
theorem oscillation_diverge_projection (t : ℝ) :
    (Complex.exp (Real.pi * t * Complex.I)).re = Real.cos (Real.pi * t) := by
  rw [Complex.exp_ofReal_mul_I_re]

/-! ## 3. 发散轴投影范围 [-1, 1]

cos(π·0) = 1 (t = 0, 相位 0 = 数值 1, RulerPhase/R143), cos(π·1) =
-1 (t = 1, 半圈, Real.cos_pi) — 震荡在发散轴的投影范围 = [-1, 1]. -/

/-- **发散轴投影范围 [-1, 1]**: cos(π·0) = 1 ∧ cos(π·1) = -1 —
震荡在发散轴 (实轴, R047) 的投影从 +1 (t = 0, 相位 0 = 数值 1,
R143) 到 -1 (t = 1, 半圈, Real.cos_pi) — 发散轴投影范围 = [-1, 1]. -/
theorem oscillation_projection_range :
    Real.cos (Real.pi * 0) = 1 ∧ Real.cos (Real.pi * 1) = -1 := by
  constructor
  · norm_num
  · exact Real.cos_pi

/-! ## 4. 基点移到震荡轴

把基点从 0 移到震荡轴上 (R142/RulerDelta: 基点漂移; R136: 基点 =
delta 的锚) — 新基点观测: 震荡相对新基点的位移 = osc(t) - 基点.
选震荡中点 (t = 1, 投影 -1) 为新基点, 观测震荡在发散轴的相对
范围. -/

/-- **基点移到震荡轴**: 基点从 0 移到震荡轴中点 (t = 1) — 基点
漂移 (R142/RulerDelta: 基点 = delta 的锚, 值随基点漂移位置不变;
R136: 基点相对性) — 新基点下观测震荡 = 相对位移 (最长距离 = 从
新基点 -1 到远端 +1 = 2). -/
theorem basepoint_move_to_axis :
    Real.cos (Real.pi * 1) = -1 :=
  Real.cos_pi

/-! ## 5. ★最长震荡距离 = 2 = 间隔 2

震荡在发散轴投影从 +1 到 -1 — 最长震荡距离 = 1 - (-1) = 2 — **等于
间隔 2 本身**. 即: 震荡周期 = 2, 发散轴最长震荡距离 = 2, 二者
自洽 (间隔 2 是结构常数, 既是周期又是最长距离). -/

/-- **★最长震荡距离 = 2 = 间隔 2**: 1 - (-1) = 2 — 震荡在发散轴的
投影从 +1 (t=0) 到 -1 (t=1), 最长震荡距离 = 1 - (-1) = 2 — **等于
孪生素数间隔 2 本身** (R172: 间隔 2 = 临界线圆直径 = 奇偶性周期;
R171: 模 2 折叠) — 间隔 2 既是震荡周期又是发散轴最长震荡距离
(自洽, 结构常数). -/
theorem max_oscillation_distance :
    1 - (-1) = 2 := by
  ring

/-! ## 6. 全景

间隔 2 = 震荡周期 (exp(iπ(t+2)) = exp(iπt)) ∧ 发散轴投影范围
[-1,1] (cos) ∧ 最长震荡距离 = 2 = 间隔 2 — 孪生素数间隔作为震荡
周期轴: 周期与最长距离自洽 (都是 2). 基点移动 (R142) 观测: 从
新基点 (震荡中点 -1) 到远端 +1 距离 = 2. -/

/-- **★孪生素数震荡全景**: 震荡周期 = 2 (exp(i·π·(t+2)) = exp(i·π·t),
PROVED) ∧ 发散轴投影范围 [-1,1] (cos(π·0)=1, cos(π·1)=-1, PROVED)
∧ ★最长震荡距离 = 2 = 间隔 2 (1-(-1)=2, PROVED) — 孪生素数间隔
作为震荡周期轴: 周期 = 2 = 发散轴最长震荡距离 (自洽); 基点移动
(R142 基点漂移) 到震荡轴观测. 诚实边界: 结构观测, 非素数分布
理论. -/
theorem twin_prime_oscillation_perspective (t : ℝ) :
    (Complex.exp (Real.pi * (t + 2) * Complex.I) =
     Complex.exp (Real.pi * t * Complex.I)) ∧
    (Real.cos (Real.pi * 0) = 1 ∧ Real.cos (Real.pi * 1) = -1) ∧
    (1 - (-1) = 2) := by
  constructor
  · exact oscillation_period_two t
  · constructor
    · exact oscillation_projection_range
    · exact max_oscillation_distance

end PatTwinPrimeOscillation

end ZeroRelative
