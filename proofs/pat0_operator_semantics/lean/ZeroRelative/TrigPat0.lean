/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# C036: 三角函数方向问题 — pat0 形式化分析 (2026-08-18)

用户指令 (2026-08-18): 三角函数也做 pat0 原生化, 有方向问题吗?

★ 方向问题 (三角函数是方向问题重灾区):
  1. **Real.cos 偶函数: cos(-θ) = cos(θ)** — 单用 Real.cos 丢方向!
     (R136: 方向必须成对声明 — Real.cos 把 θ 与 -θ 投影到同一点,
     θ ≠ -θ 却无法区分 ⟹ 方向信息丢失)
  2. **Real.sin 奇函数: sin(-θ) = -sin(θ)** — 保留方向 (符号随 θ 反号)
  3. **基点不同**: Real.cos 的基点 = 1 (乘法基点, Real.cos 0 = 1);
     Real.sin 的基点 = 0 (加法基点, Real.sin 0 = 0)
  4. **周期 2π = 四相位互锁 R149 的连续化**: 90° 格点上的 (cos, sin)
     只取 {(1,0), (0,1), (-1,0), (0,-1)} — 与 C030 辛投影 J²=-I 同构
     (rotJ² = -I, rotJ⁴ = I)

★ pat0 落实: 连续旋转 → 四相位格点旋转 (rot_pat0 in pat0_ops.py) —
  θ 量化到 90° 格点, cos/Real.sin 只取 {0, ±1} (无小数!), 纯格点运算;
  旋转必须成对使用 (cos, sin) — 单用 Real.cos = 方向丢失 (R136 破坏)。
-/

namespace ZeroRelative

noncomputable section

-- ==================== 1. 方向问题: Real.cos 偶 / Real.sin 奇 ====================

-- Real.cos 偶函数: cos(-θ) = cos(θ) — 单用 Real.cos 丢方向 (R136: 方向必须成对声明)
theorem cos_even_direction_loss (θ : ℝ) : Real.cos (-θ) = Real.cos θ := by
  rw [Real.cos_neg]

-- Real.sin 奇函数: sin(-θ) = -sin(θ) — 保留方向 (方向声明对 {d, -d} 的竖轴半)
theorem sin_odd_direction_keep (θ : ℝ) : Real.sin (-θ) = -Real.sin θ := by
  rw [Real.sin_neg]

-- 方向丢失的具体化: Real.cos 不是单射 — 存在 θ₁ ≠ θ₂ 且 Real.cos θ₁ = Real.cos θ₂
-- (θ 与 -θ 同值, 无法区分 ⟹ 单用 Real.cos 无法恢复方向)
theorem cos_not_injective_direction_loss :
    ∃ θ₁ θ₂ : ℝ, θ₁ ≠ θ₂ ∧ Real.cos θ₁ = Real.cos θ₂ := by
  refine ⟨Real.pi, -Real.pi, ?_, ?_⟩
  · linarith [Real.pi_pos]
  · rw [Real.cos_neg]

-- 方向保留: 旋转成对 (cos, sin) 保范 — 旋转不丢任何信息 (可逆)
theorem rot_keeps_norm (θ : ℝ) (x y : ℝ) :
    (x * Real.cos θ - y * Real.sin θ) ^ 2 + (x * Real.sin θ + y * Real.cos θ) ^ 2 = x ^ 2 + y ^ 2 := by
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq θ]

-- ==================== 2. 基点: Real.cos 基点 = 1 (乘法), Real.sin 基点 = 0 (加法) ====================

-- Real.cos 的基点 = 1 (乘法基点: Real.cos 0 = 1 — 0 处回到乘法单位)
theorem cos_basepoint_one : Real.cos 0 = 1 := by
  norm_num

-- Real.sin 的基点 = 0 (加法基点: Real.sin 0 = 0 — 0 处回到加法原点)
theorem sin_basepoint_zero : Real.sin 0 = 0 := by
  norm_num

-- ==================== 3. 四相位格点 (R149: 90° 格点 = 四相位互锁) ====================

-- 90° 格点: (cos, sin) 只取 {(1,0), (0,1), (-1,0), (0,-1)} — 全在基点格点上 (无小数)
theorem quad_phase_grid_0 : (Real.cos 0, Real.sin 0) = (1, 0) := by
  norm_num

theorem quad_phase_grid_half : (Real.cos (Real.pi / 2), Real.sin (Real.pi / 2)) = (0, 1) := by
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem quad_phase_grid_pi : (Real.cos Real.pi, Real.sin Real.pi) = (-1, 0) := by
  simp [Real.cos_pi, Real.sin_pi]

theorem quad_phase_grid_3half : (Real.cos (3 * Real.pi / 2), Real.sin (3 * Real.pi / 2)) = (0, -1) := by
  rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring]
  rw [Real.cos_add_pi, Real.sin_add_pi]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num

-- ==================== 4. 90° 旋转 J 与 C030 辛投影同构 ====================

-- 90° 格点旋转 J: (x, y) ↦ (-y, x)
def rotJ (v : ℝ × ℝ) : ℝ × ℝ := (-v.2, v.1)

-- J² = -I: 两次 90° 旋转 = 取反 (与 C030 SymplecticProjection J²=-I 一致)
theorem rotJ_sq_neg_id (x y : ℝ) : rotJ (rotJ (x, y)) = (-x, -y) := by
  simp [rotJ]

-- J⁴ = I: 四次 90° 旋转 = 回到基点 (四相位循环 1→i→-1→-i→1)
theorem rotJ_pow4_id (x y : ℝ) : rotJ (rotJ (rotJ (rotJ (x, y)))) = (x, y) := by
  simp [rotJ]

-- 90° 旋转 = 相位推进: J(Real.cos θ, Real.sin θ) = (cos(θ+π/2), sin(θ+π/2))
-- (格点上: 1 → i → -1 → -i → 1 的相位循环)
theorem rot90_phase_advance (θ : ℝ) :
    rotJ (Real.cos θ, Real.sin θ) = (Real.cos (θ + Real.pi / 2), Real.sin (θ + Real.pi / 2)) := by
  unfold rotJ
  ext <;> simp [Real.cos_add, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two]

end

end ZeroRelative
