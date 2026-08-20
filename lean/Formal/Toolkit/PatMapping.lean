/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Formal.Toolkit.PatConstruction
import Formal.Toolkit.PatCircle
import Formal.Toolkit.TimeArrowToPeriodAxis
import Formal.Toolkit.MonophaseCaseDesign

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatMapping — 基点 0 视角: 自然数 ↔ 单相位数映射 (发散/收敛) + 素数环

User request (R142, 2026-08-12): 基点 0 视角下, 自然数到单相位数的映射关系,
以及单相位数在自然数上的映射关系 (包括发散映射与收敛映射); 素数环做相同的
操作.

The mapping (each link anchored to proven claims):

1. **自然数 → 单相位 (φ)**: 自然数 n = 基点 0 出发单位方向的单相位链第 n 层 —
   patChain 0 1 n = n (R137 pat_n_is_monophase: pat n = pat0 + n·d, d = 1,
   pat0 = 0; R091: 单相位 = {n·d}; R070: Nat = Chain(0)).
2. **单相位 → 自然数, 发散映射 (ψ_div)**: 层数 = 值/d — (n·d)/d = n
   (R091: 单相位链 {n·d} 的层数提取; log 版: log(p^k) = k·log p, R097 素数
   幂链 = 单相位, R089: log 基点漂移).
3. **单相位 → 自然数, 收敛映射 (ψ_conv)**: 相位蜷曲到圆 + 单位根量化 —
   pat n 的相位量化到单位根 n 槽环, 误差 ≤ π/n (R138/R055 蜷曲,
   R141 phase_quantizable: |x - round x| ≤ 1/2).
4. **素数环**: 素数圆 |z| = √p (C016/C017); 素数幂链 {p^k} 经 log 是单相位
   (R097); 素数幂链蜷曲到圆 (R055 机制); 合数 = 多相位 (R112:
   p^a·p^b = p^(a+b) 相位向量加法).

Main theorems:

1. `nat_is_monophase_chain`: 自然数 n = 基点 0 单位方向单相位链第 n 层
   (patChain 0 1 n = n).
2. `monophase_layer_extract`: 发散映射 — 层数 = 值/d: (n·d)/d = n.
3. `prime_power_log_layer`: 素数幂链 = 单相位 — log(p^k) = k·log p (R097).
4. `nat_phase_quantized`: 收敛映射 — 自然数相位量化到单位根格点 (R141).
5. `prime_power_curls`: 素数幂链蜷曲到圆 (R055 机制).
6. `prime_circle_norm`: 素数圆 — ‖√p·exp(θ·I)‖ = √p (C016/C017).
7. `composite_polyphase`: 合数 = 多相位 — p^a·p^b = p^(a+b) (R112).
-/

namespace ZeroRelative

namespace PatMapping

/-! ## 1. 自然数 → 单相位 (基点 0 视角)

自然数 n = 基点 0 出发、单位方向 d = 1 的单相位链第 n 层: patChain 0 1 n = n
(R137: pat n = pat0 + n·d; R091: 单相位 = {n·d}; R070: Nat = Chain(zero);
RulerDelta: 基点 = delta 的锚). -/

/-- **自然数 = 基点 0 单位方向的单相位链**: patChain 0 1 n = n — 自然数 n
是基点 0 出发、方向 d = 1 的单相位链第 n 层 (R137 pat_n_is_monophase;
R091: 单相位 = {n·d}; R070: Nat = Chain(0); R062: 0 是特权基点选择). -/
theorem nat_is_monophase_chain (n : ℕ) :
    PatConstruction.patChain 0 1 n = (n : ℝ) := by
  rw [PatConstruction.pat_n_is_monophase]
  simp

/-! ## 2. 单相位 → 自然数, 发散映射 (ψ_div)

层数 = 值/d: 单相位链 {n·d} 的第 n 层值 v = n·d, 提取层数 n = v/d
(R091: 标量列; R067: 数值 = 基点投影). log 版 (素数幂链): log(p^k) = k·log p
(R097: 素数幂链 = 单相位; R089: log 把乘法基点 1 漂移到加法基点 0). -/

/-- **发散映射: 层数 = 值/d**: (n·d)/d = n — 单相位链 {n·d} 的层数由
值经除法提取 (R091: 标量列; RulerDelta: delta 类 = 身份, 基点 = 锚). -/
theorem monophase_layer_extract (n d : ℝ) (hd : d ≠ 0) :
    (n * d) / d = n := by
  field_simp [hd]

/-- **素数幂链 = 单相位 (log 视角)**: log(p^k) = k·log p — 素数幂链经
log 是等差单相位链 (R097: 间隔 log p; R089: log 把乘法基点 1 漂移到加法
基点 0; R091: 单相位 = {n·d}). -/
theorem prime_power_log_layer (p : ℝ) (k : ℕ) :
    Real.log (p ^ k) = (k : ℝ) * Real.log p :=
  Real.log_pow p k

/-! ## 3. 单相位 → 自然数, 收敛映射 (ψ_conv)

相位蜷曲到圆 (R138/R055: t ↦ exp(2π·t/T·I)), 量化到单位根 n 槽环
(R141 phase_quantizable: 误差 ≤ π/n) — 自然数在圆上的表示 = 格点序号. -/

/-- **收敛映射: 自然数相位量化到单位根格点**: 自然数 n 的相位
2π·n/T 量化到单位根 n 槽环, 误差 ≤ π/N (R138: pat n 蜷曲到相位环;
R141 phase_quantizable: |x - round x| ≤ 1/2; R059: 单位根 n 槽环). -/
theorem nat_phase_quantized (T : ℝ) (N : ℕ) (hN : 0 < N) (n : ℕ)
    (hθ₁ : 0 ≤ 2 * Real.pi * (n : ℝ) / T)
    (hθ₂ : 2 * Real.pi * (n : ℝ) / T ≤ 2 * Real.pi) :
    ∃ j : ℕ, j ≤ N ∧
      |2 * Real.pi * (n : ℝ) / T - 2 * Real.pi * (j : ℝ) / N| ≤ Real.pi / N :=
  PatCircle.phase_quantizable (2 * Real.pi * (n : ℝ) / T) N hN hθ₁ hθ₂

/-! ## 4. 素数环: 相同操作

素数圆 |z| = √p (C016/C017: 高斯整数/素数圆单轨道); 素数幂链蜷曲到圆
(R055 机制); 合数 = 多相位 (R112: 乘法 = 相位向量加法). -/

/-- **素数幂链蜷曲到圆 (收敛映射)**: exp(2π·((k·log p + T)/T)·I) =
exp(2π·(k·log p/T)·I) — 素数幂链 (log 等差单相位, R097) 蜷曲到相位环,
未来 = 环上相位重现 (R055: 时间轴蜷曲保映射; R138: pat n 同机制). -/
theorem prime_power_curls (p T : ℝ) (hT : T ≠ 0) (k : ℕ) :
    Complex.exp (2 * Real.pi * ((((k : ℝ) * Real.log p) + T) / T) * Complex.I) =
      Complex.exp (2 * Real.pi * ((k : ℝ) * Real.log p / T) * Complex.I) := by
  simpa using
    (TimeArrowToPeriodAxis.time_axis_curls_to_circle T hT ((k : ℝ) * Real.log p))

/-- **素数圆**: ‖√p · exp(θ·I)‖ = √p — 素数 p 在素数圆上 (半径 √p,
C016/C017: 高斯整数/素数圆单轨道; R109: 折叠类 0 = 素数圆圆心). -/
theorem prime_circle_norm (p θ : ℝ) (hp : 0 ≤ p) :
    ‖(Real.sqrt p : ℂ) * Complex.exp (θ * Complex.I)‖ = Real.sqrt p := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I]
  simp [abs_of_nonneg (Real.sqrt_nonneg p)]

/-- **合数 = 多相位**: p^a·p^b = p^(a+b) — 乘法 = 相位向量加法 (R112
polyphase_exponent_add: 指数逐点相加, 格点平移; R097: 合数 log n =
Σ k_i·log p_i 多相位叠加). -/
theorem composite_polyphase (p a b : ℕ) :
    (p ^ a) * (p ^ b) = p ^ (a + b) :=
  MonophaseCaseDesign.polyphase_exponent_add p a b

end PatMapping

end ZeroRelative
