/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# C029: 基点 ±1 = 高维结构的投影, 出了 2 个位置 (2026-08-18)

用户洞察 (2026-08-18): **基点正负 1 说明这他妈是一个高维结构的投影, 出了 2 个位置**。

解释:
  - 加法基点 0: 一维结构 (实数轴) 的原点 — 单个位置
  - 乘法基点 ±1: **两个**位置 — 这在一维数轴上无法内生产生,
    只能是一维数轴 (实轴) 作为**高维结构 (单位圆 S¹ / 四相位) 的投影**:
      单位圆上的点投影到实轴 (Re), 极值位置恰为 ±1 (两个位置);
      投影到虚轴 (Im), 极值位置恰为 ±i (两个位置)。
  - 四相位 {1, -1, i, -i} (R149) 是单位圆上 4 个特殊点:
      实轴投影出 ±1, 虚轴投影出 ±i — 每根投影轴出 2 个位置。
  - Q2_0 格点 {-1, 0, 1, 2} 中的 ±1 = 这个投影的证据:
      高维结构投影到实轴, 出了 ±1 两个位置 (C028 对照).

形式化: 单位圆 S¹ = {z : ℂ | ‖z‖ = 1}; 实轴投影 Re。
  T1 real_proj_range: 单位圆投影到实轴的像 ⊆ [-1, 1]
  T2 real_proj_extreme_pos: 实部取极值 +1 的点恰是 z = 1
  T3 real_proj_extreme_neg: 实部取极值 -1 的点恰是 z = -1
  T4 real_proj_extremes: 投影极值位置 = {±1} (两个位置)
  T5 quad_phase_proj: 四相位 {1,-1,i,-i} 的投影: 实轴出 ±1, 虚轴出 ±i
-/

namespace ZeroRelative

noncomputable section

open Complex

-- T1: 单位圆投影到实轴的像 ⊆ [-1, 1] (Re 的绝对值 ≤ 半径)
theorem real_proj_range {z : ℂ} (hz : Complex.normSq z = 1) : |Complex.re z| ≤ 1 := by
  have hsq : Complex.re z ^ 2 ≤ 1 := by
    nlinarith [Complex.normSq_apply z, hz]
  have hle : Complex.re z ≤ 1 := by
    by_contra h
    have hgt : 1 < Complex.re z := lt_of_not_ge h
    have : 1 < Complex.re z ^ 2 := by nlinarith
    nlinarith [hsq]
  have hge : -1 ≤ Complex.re z := by
    by_contra h
    have hlt : Complex.re z < -1 := lt_of_not_ge h
    have : 1 < Complex.re z ^ 2 := by nlinarith
    nlinarith [hsq]
  exact abs_le.mpr ⟨hge, hle⟩

-- 同样: 虚轴投影的像 ⊆ [-1, 1]
theorem imag_proj_range {z : ℂ} (hz : Complex.normSq z = 1) : |Complex.im z| ≤ 1 := by
  have hsq : Complex.im z ^ 2 ≤ 1 := by
    nlinarith [Complex.normSq_apply z, hz]
  have hle : Complex.im z ≤ 1 := by
    by_contra h
    have hgt : 1 < Complex.im z := lt_of_not_ge h
    have : 1 < Complex.im z ^ 2 := by nlinarith
    nlinarith [hsq]
  have hge : -1 ≤ Complex.im z := by
    by_contra h
    have hlt : Complex.im z < -1 := lt_of_not_ge h
    have : 1 < Complex.im z ^ 2 := by nlinarith
    nlinarith [hsq]
  exact abs_le.mpr ⟨hge, hle⟩

-- T2: 实部极值 +1 的点恰是 z = 1 (单位圆上)
theorem real_proj_extreme_pos {z : ℂ} (hz : Complex.normSq z = 1) :
    Complex.re z = 1 ↔ z = 1 := by
  constructor
  · intro hre
    apply Complex.ext
    · exact hre
    · have hsq : Complex.re z ^ 2 + Complex.im z ^ 2 = 1 := by
        nlinarith [Complex.normSq_apply z, hz]
      have : Complex.im z ^ 2 = 0 := by nlinarith
      simp [sq_eq_zero_iff.mp this]
  · intro hz1
    simp [hz1]

-- T3: 实部极值 -1 的点恰是 z = -1 (单位圆上)
theorem real_proj_extreme_neg {z : ℂ} (hz : Complex.normSq z = 1) :
    Complex.re z = -1 ↔ z = -1 := by
  constructor
  · intro hre
    apply Complex.ext
    · exact hre
    · have hsq : Complex.re z ^ 2 + Complex.im z ^ 2 = 1 := by
        nlinarith [Complex.normSq_apply z, hz]
      have : Complex.im z ^ 2 = 0 := by nlinarith
      simp [sq_eq_zero_iff.mp this]
  · intro hz1
    simp [hz1]

-- T4: 实轴投影的极值位置 = {±1} (两个位置) — 高维结构投影的证据
theorem real_proj_extremes :
    {z : ℂ | Complex.normSq z = 1 ∧ Complex.re z = 1} = ({1} : Set ℂ) := by
  ext z
  constructor
  · intro hz
    have : z = 1 := (real_proj_extreme_pos hz.1).1 hz.2
    simp [this]
  · intro hz
    rcases hz with rfl
    norm_num [Complex.normSq]

theorem real_proj_extremes_neg :
    {z : ℂ | Complex.normSq z = 1 ∧ Complex.re z = -1} = ({-1} : Set ℂ) := by
  ext z
  constructor
  · intro hz
    have : z = -1 := (real_proj_extreme_neg hz.1).1 hz.2
    simp [this]
  · intro hz
    rcases hz with rfl
    norm_num [Complex.normSq]

-- 虚轴对称: 虚部极值 ±1 的点恰是 ±i
theorem imag_proj_extreme_pos {z : ℂ} (hz : Complex.normSq z = 1) :
    Complex.im z = 1 ↔ z = Complex.I := by
  constructor
  · intro him
    apply Complex.ext
    · have hsq : Complex.re z ^ 2 + Complex.im z ^ 2 = 1 := by
        nlinarith [Complex.normSq_apply z, hz]
      have : Complex.re z ^ 2 = 0 := by nlinarith
      simp [sq_eq_zero_iff.mp this]
    · exact him
  · intro hz1
    rcases hz1 with rfl
    norm_num [Complex.normSq]

-- T5: 四相位 {1, -1, i, -i} 的投影 — 实轴出 ±1, 虚轴出 ±i, 交叉为 0
theorem quad_phase_real_proj :
    Complex.re (1 : ℂ) = 1 ∧ Complex.re (-1 : ℂ) = -1 := by
  norm_num

theorem quad_phase_imag_proj :
    Complex.im (Complex.I : ℂ) = 1 ∧ Complex.im (-Complex.I : ℂ) = -1 := by
  norm_num

theorem quad_phase_cross_proj :
    Complex.re (Complex.I : ℂ) = 0 ∧ Complex.im (1 : ℂ) = 0 := by
  norm_num

-- 四相位都落在单位圆上 (高维结构 S¹ 的 4 个特殊点)
theorem quad_phase_on_unit_circle :
    Complex.normSq (1 : ℂ) = 1 ∧ Complex.normSq (-1 : ℂ) = 1 ∧
    Complex.normSq (Complex.I : ℂ) = 1 ∧ Complex.normSq (-Complex.I : ℂ) = 1 := by
  norm_num [Complex.normSq]

-- 对照: 加法基点 0 在单位圆内部 (圆心 = 投影中心/折叠中心)
theorem zero_is_projection_center : Complex.re (0 : ℂ) = 0 ∧ Complex.im (0 : ℂ) = 0 := by
  norm_num

end

end ZeroRelative
