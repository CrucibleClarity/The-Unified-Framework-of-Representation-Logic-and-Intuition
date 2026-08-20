/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# C030: 辛投影 — J² = -I 下四相位的投影对消 (2026-08-18)

衔接 R047 (轴间正交/辛正交) 与 R149 (四相位互锁)。

辛结构: J(z) = i·z (虚数乘法), J² = -I。
四相位 {1, -1, i, -i} (R149) 在 J 下循环: 1 → i → -1 → -i → 1 (4 步回自身)。

核心命题 (投影对消):
  1. 四相位向量和 = 0: 1 + i + (-1) + (-i) = 0
  2. 互锁对: 实轴对 {±1} 对消, 虚轴对 {±i} 对消
  3. **任意方向投影对消**: 四相位在任意方向 u 的投影之和 = 0
     (投影 = Re(z · conj u); 由向量和 = 0 与 Re 线性直接推出)
  4. J 是正交变换 (保内积) 且 J² = -I — 辛结构的载体

这解释了"投影对消" (互锁对在任意方向投影和 = 0):
四相位是单位圆上的平衡点组, 在任何投影方向上都整体对消 —
Q2_0 格点中 ±1 的对消对 (C028/C029) 是它在实轴方向的投影对消。
-/

namespace ZeroRelative

noncomputable section

open Complex
open scoped ComplexConjugate

/-- 辛结构: `J(z) = i·z` (虚数乘法, 四相位旋转). -/
def J (z : ℂ) : ℂ := Complex.I * z

-- T1: J² = -I (辛结构定义)
theorem j_squared (z : ℂ) : J (J z) = -z := by
  simp [J]
  rw [← mul_assoc, Complex.I_mul_I]
  simp

-- T2: 四相位在 J 下循环: 1 → i → -1 → -i → 1
theorem j_phase_cycle :
    J (1 : ℂ) = Complex.I ∧ J Complex.I = -1 ∧
    J (-1 : ℂ) = -Complex.I ∧ J (-Complex.I) = 1 := by
  norm_num [J]

-- T3: 4 步循环回自身 (四相位循环 q→p→−q→−p→q)
theorem j_cycle_four : J (J (J (J (1 : ℂ)))) = 1 := by
  norm_num [J]

-- T4: 四相位向量和 = 0 (投影对消的基础)
theorem quad_phase_sum_zero : (1 : ℂ) + Complex.I + (-1) + (-Complex.I) = 0 := by
  norm_num

-- T5: 互锁对 — 实轴对 {±1} 对消
theorem real_pair_cancel : (1 : ℂ) + (-1 : ℂ) = 0 := by
  norm_num

-- T6: 互锁对 — 虚轴对 {±i} 对消
theorem imag_pair_cancel : Complex.I + (-Complex.I) = 0 := by
  norm_num

-- T7 (core): 任意方向投影对消 — 四相位在任意方向 u 的投影和 = 0
-- (投影 = Re(z · conj u); 由向量和 = 0 与 Re 线性直接推出)
theorem projection_cancel_any_direction (u : ℂ) :
    Complex.re ((1 : ℂ) * conj u) + Complex.re (Complex.I * conj u) +
    Complex.re ((-1 : ℂ) * conj u) + Complex.re ((-Complex.I) * conj u) = 0 := by
  have hsum : (1 : ℂ) * conj u + Complex.I * conj u + (-1 : ℂ) * conj u +
      (-Complex.I) * conj u = 0 := by
    rw [← add_mul, ← add_mul, ← add_mul]
    rw [quad_phase_sum_zero]
    norm_num
  have hre : Complex.re ((1 : ℂ) * conj u + Complex.I * conj u + (-1 : ℂ) * conj u +
      (-Complex.I) * conj u) = Complex.re ((1 : ℂ) * conj u) + Complex.re (Complex.I * conj u) +
      Complex.re ((-1 : ℂ) * conj u) + Complex.re ((-Complex.I) * conj u) := by
    repeat rw [Complex.add_re]
  rw [← hre, hsum]
  norm_num

-- T8: J 是正交变换 (保内积): <Jx, Jy> = <x, y>
-- (|i| = 1, 虚数乘法保内积)
theorem j_orthogonal (x y : ℂ) :
    Complex.re (J x * conj (J y)) = Complex.re (x * conj y) := by
  simp [J]

-- T9: J² = -I 与正交性合起来 = 辛结构 (R047 辛正交载体)
-- 辛配对 ω(x, y) := <Jx, y>; 反对称性 ω(y, x) = -ω(x, y)
theorem symplectic_antisymm (x y : ℂ) :
    Complex.re (J y * conj x) = -Complex.re (J x * conj y) := by
  -- I·y·conj x 与 I·x·conj y 的关系: 前者 = -conj(后者) (ℂ 交换 + conj_I)
  have hconj : conj (J x * conj y) = -(J y * conj x) := by
    simp [J, Complex.conj_I]
    ring
  -- Re(conj w) = Re w
  have hre1 : Complex.re (conj (J x * conj y)) = Complex.re (J x * conj y) :=
    Complex.conj_re (J x * conj y)
  rw [hconj] at hre1
  -- Re(-w) = -Re w
  have hneg : Complex.re (-(J y * conj x)) = -Complex.re (J y * conj x) :=
    Complex.neg_re (J y * conj x)
  rw [hneg] at hre1
  -- -Re(J y · conj x) = Re(J x · conj y) → 目标
  linarith

end

end ZeroRelative
