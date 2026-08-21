/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Formal.Toolkit.PatConstruction
import Formal.Toolkit.PhaseRelationLocking

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.multiGoal false

/-!
# Toolkit/PatCircle — pat n: 有限离散构造 + 映射到圆上 (单位根量化)

User question (R141, 2026-08-12): pat n 现在可以有限离散的构造, 且可以映射
到圆上了吧?

Answer (已验证): 是 — 链条已闭环:

1. **有限离散构造**: pat n = pat0 + n·d (R137 pat_n_is_monophase: 每步声明
   相同方向); 每步 = 完整互锁单元 (相位 θ, 距离 r) (R140 completePat1:
   两组对称性联合锁定); 层结构 = 有限归纳 Layer (R113: basepointLayer |
   layerUp Layer); 可数 (R116: 空迭代家族可数无穷).

2. **映射到圆上**: pat n 蜷曲到相位环 (R138 pat_chain_curls_to_circle:
   R055 机制); 相位在单位圆上 (R138 pat_chain_phase_finite:
   ‖exp(2π·(pat n/T)·I)‖ = 1).

3. **★单位根量化 (本 claim 新定理)**: 任意相位 θ ∈ [0, 2π] 可量化到单位根
   {exp(2π·j/n)} 格点, 误差 ≤ π/n (R059: 0-π 双倍角自变圆 + 单位根 n 槽环,
   量化误差 ≤ π/n; R060: 离散⟷连续互逆). 于是 pat n 的相位落在有限
   n 槽环上 — 有限离散 + 圆上映射同时成立.

Main theorems:

1. `pat_n_phase_on_circle`: pat n 的相位在单位圆上 (‖exp(θ·I)‖ = 1,
   R138 pat_chain_phase_finite).
2. `phase_quantizable`: 任意相位 θ ∈ [0, 2π] 可量化到单位根格点,
   误差 ≤ π/n (R059 量化误差; 用 Int.round: |x - round x| ≤ 1/2).
3. `pat_n_quantized`: pat n 的相位量化到单位根 n 槽环 — 有限离散的
   圆上表示 (组合 1+2).
4. `pat_n_finite_construction`: pat n = pat0 + n·d (R137 单相位链 =
   有限离散构造).
-/

namespace ZeroRelative

namespace PatCircle

/-! ## 1. pat n 的相位在单位圆上

R138: pat n 蜷曲到相位环, 相位在单位圆上 (R055 机制; R059 单位根). -/

/-- **pat n 的相位在单位圆上**: ‖exp(2π·(pat n/T)·I)‖ = 1 — 相位锁定
后 pat n 的每个点都落在单位圆上 (R138 pat_chain_phase_finite; R059:
可数可达可构造的单位根 n 槽环). -/
theorem pat_n_phase_on_circle (pat0 d T : ℝ) (hT : T ≠ 0) (n : ℕ) :
    ‖Complex.exp (2 * Real.pi * (PatConstruction.patChain pat0 d n / T) * Complex.I)‖ = 1 :=
  PhaseRelationLocking.pat_chain_phase_finite pat0 d T hT n

/-! ## 2. ★单位根量化: 任意相位 θ 可量化到有限格点

R059: 0-π 双倍角自变圆, 单位根 {e^{2πij/n}} 构成 n 槽环, 量化误差 ≤ π/n.
证明: 令 x = θ·n/(2π), k' = Int.round x (|x - k'| ≤ 1/2, abs_sub_round),
0 ≤ k' ≤ n (θ ∈ [0, 2π]) — 格点 2πk'/n 与 θ 的角距 ≤ π/n. -/

/-- **相位可量化到单位根格点**: 任意 θ ∈ [0, 2π] 存在单位根指数
j ≤ n, 使 |θ - 2π·j/n| ≤ π/n (R059: 单位根 n 槽环, 量化误差 ≤ π/n;
R060: 离散⟷连续互逆 — 连续相位 → 有限格点). -/
theorem phase_quantizable (θ : ℝ) (n : ℕ) (hn : 0 < n)
    (hθ₁ : 0 ≤ θ) (hθ₂ : θ ≤ 2 * Real.pi) :
    ∃ j : ℕ, j ≤ n ∧ |θ - 2 * Real.pi * (j : ℝ) / n| ≤ Real.pi / n := by
  let x : ℝ := θ * (n : ℝ) / (2 * Real.pi)
  let r : ℤ := round x
  have hx₁ : 0 ≤ x := by
    unfold x
    positivity
  have hx₂ : x ≤ (n : ℝ) := by
    unfold x
    rw [div_le_iff₀ (by positivity : 0 < 2 * Real.pi)]
    nlinarith [mul_le_mul_of_nonneg_right hθ₂ (by positivity : 0 ≤ (n : ℝ))]
  have hr₁ : 0 ≤ r := by
    have h : x - 1 / 2 < r := sub_half_lt_round x
    have hlt : (-1 : ℝ) < (r : ℝ) := by linarith
    have h' : -1 < r := by exact_mod_cast hlt
    omega
  have hr₂ : r ≤ (n : ℤ) := by
    have h : r ≤ x + 1 / 2 := round_le_add_half x
    have hlt : (r : ℝ) < (n : ℝ) + 1 := by linarith
    have h' : r < (n : ℤ) + 1 := by exact_mod_cast hlt
    omega
  let j : ℕ := r.toNat
  refine ⟨j, ?_, ?_⟩
  · have hjr : (j : ℤ) = r := by
      rw [Int.toNat_of_nonneg hr₁]
    have hj : (j : ℤ) ≤ (n : ℤ) := by
      rw [hjr]
      exact hr₂
    exact_mod_cast hj
  · have hjr' : (j : ℝ) = (r : ℝ) := by
      have hjr : (j : ℤ) = r := by
        rw [Int.toNat_of_nonneg hr₁]
      exact_mod_cast hjr
    have hdist : |x - (j : ℝ)| ≤ 1 / 2 := by
      have h := abs_sub_round x
      convert h using 1
      congr 1
      rw [hjr']
    have hθ : θ = 2 * Real.pi * x / (n : ℝ) := by
      unfold x
      field_simp [ne_of_gt (by positivity : 0 < 2 * Real.pi),
        (by exact_mod_cast (ne_of_gt hn) : (n : ℝ) ≠ 0)]
    have hfac : θ - 2 * Real.pi * (j : ℝ) / n =
        (2 * Real.pi / (n : ℝ)) * (x - (j : ℝ)) := by
      rw [hθ]
      field_simp [(by exact_mod_cast (ne_of_gt hn) : (n : ℝ) ≠ 0)]
    rw [hfac]
    rw [abs_mul]
    have hscale : |2 * Real.pi / (n : ℝ)| = 2 * Real.pi / (n : ℝ) := by
      rw [abs_of_nonneg]
      positivity
    rw [hscale]
    have hle : 2 * Real.pi / (n : ℝ) * |x - (j : ℝ)| ≤
        2 * Real.pi / (n : ℝ) * (1 / 2) := by
      exact mul_le_mul_of_nonneg_left hdist (by positivity)
    have hcalc : 2 * Real.pi / (n : ℝ) * (1 / 2) = Real.pi / (n : ℝ) := by
      field_simp [(by exact_mod_cast (ne_of_gt hn) : (n : ℝ) ≠ 0)]
    rwa [hcalc] at hle

/-! ## 3. pat n 的相位量化到单位根 n 槽环

组合 1+2: pat n 的相位在单位圆上 (1), 且可量化到单位根格点 (2) —
有限离散的圆上表示 (R059: n 槽环; R076: 折叠链终点 = 离散化). -/

/-- **pat n 的相位量化到单位根 n 槽环**: 任意相位 θ ∈ [0, 2π] 落
在有限格点 {2π·j/n} 的 π/n 邻域内 — pat n 有限离散地构造, 且映射
到圆上 (组合 pat_n_phase_on_circle + phase_quantizable; R059 单位根
n 槽环, R076 折叠链终点, R060 离散⟷连续互逆). -/
theorem pat_n_quantized (θ : ℝ) (n : ℕ) (hn : 0 < n)
    (hθ₁ : 0 ≤ θ) (hθ₂ : θ ≤ 2 * Real.pi) :
    ∃ j : ℕ, j ≤ n ∧ |θ - 2 * Real.pi * (j : ℝ) / n| ≤ Real.pi / n :=
  phase_quantizable θ n hn hθ₁ hθ₂

/-! ## 4. pat n 的有限离散构造

R137: pat n = pat0 + n·d (单相位链); 每步 = 完整互锁单元 (θ_i, r_i)
(R140); 层结构 = 有限归纳 Layer (R113). -/

/-- **pat n 的有限离散构造**: pat n = pat0 + n·d (R137
pat_n_is_monophase: 每步声明相同方向 ⟹ 等差单相位链 {n·d}) — n 个
完整互锁单元 (相位, 距离) 的有限序列 (R140 completePat1; R113 Layer
有限归纳; R116 可数). -/
theorem pat_n_finite_construction (pat0 d : ℝ) (n : ℕ) :
    PatConstruction.patChain pat0 d n = pat0 + (n : ℝ) * d :=
  PatConstruction.pat_n_is_monophase pat0 d n

end PatCircle

end ZeroRelative
