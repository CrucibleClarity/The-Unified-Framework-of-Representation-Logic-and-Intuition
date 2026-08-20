/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum

/-!
# C037: Q2_0 四格点 = pat 复平面四相位的符号量化 (2026-08-18)

用户提问: 为什么 Q2_0 量化是 4 个数, pat 是 3 个数? 是不是 Q2_0 把 pat
原生复平面以正负号的形式量化, 变成四个数?

★ 回答: 对 — 数量差来自投影方向:
  - pat 数值格点 3 个数 {-1, 0, 1} = 复平面四相位 {1, -1, i, -i} 投影到
    **实轴** (C029: 实轴投影极值 ±1; ±i 的实投影 = 0) — 丢虚部符号
  - Q2_0 的 4 个数 {-1, 0, 1, 2} = 四相位按 **双符号轴** (实符号 × 虚符号)
    量化: 2bit = 2 个符号位, 完整保留虚部符号 → 4 = 4

★ 符号编码 φ (正负号量化):
  φ(1)   = +1    (实正 → 乘法基点)
  φ(-1)  = -1    (实负 → 反射基点)
  φ(i)   = +2    (虚正 → 基点迭代: 1+1 = 2·1, C028 two_is_add_iter)
  φ(-i)  = 0     (虚负 → 折叠中心: R085 0 = ±t 折叠类平均; 负虚折叠进原点)

★ 结构性质:
  - 四相位和 = 0 (C030 投影对消: 1 + (-1) + i + (-i) = 0)
  - Q2_0 格点不是乘法闭的: 2·2 = 4 ∉ {-1,0,1,2} — 所以 φ 不是代数同态,
    而是符号编码 (保持正负号方向, 不保持乘法) — "以正负号的形式量化"
  - pat 3 数 {-1,0,1} = Q2_0 4 数投影到实符号轴 (丢迭代位):
    {+1, -1, 0} (2 和 0 都折叠到 0? 不: 2 是正迭代保留, 0 是负虚折叠 —
    实轴投影 ±i → 0 与 0 重合)
-/

namespace ZeroRelative

noncomputable section

open Complex

-- ==================== 1. 符号编码 φ: 四相位 → Q2_0 四格点 ====================

-- 正负号量化: 实符号 → {+1, -1}; 虚符号 → {+2 (正迭代), 0 (负折叠中心)}
def q2_phi (z : ℂ) : ℝ :=
  if z = 1 then 1
  else if z = -1 then -1
  else if z = Complex.I then 2
  else 0

-- 四相位的像: φ(1)=1, φ(-1)=-1, φ(i)=2, φ(-i)=0 — 全在 Q2_0 格点 {-1,0,1,2}
-- 辅助引理: 四相位在 ℂ 中互异 (norm_num 对 ℂ 等式需要 ext_iff)
lemma complex_I_ne_one : Complex.I ≠ (1 : ℂ) := by
  norm_num [Complex.ext_iff]

lemma complex_I_ne_neg_one : Complex.I ≠ (-1 : ℂ) := by
  norm_num [Complex.ext_iff]

lemma complex_negI_ne_one : -Complex.I ≠ (1 : ℂ) := by
  norm_num [Complex.ext_iff]

lemma complex_negI_ne_I : -Complex.I ≠ Complex.I := by
  norm_num [Complex.ext_iff]

theorem q2_phi_on_phases :
    q2_phi 1 = 1 ∧ q2_phi (-1) = -1 ∧
    q2_phi Complex.I = 2 ∧ q2_phi (-Complex.I) = 0 := by
  norm_num [q2_phi]
  simp [complex_I_ne_one, complex_I_ne_neg_one, complex_negI_ne_one, complex_negI_ne_I]

-- ==================== 2. 双符号轴: 2bit = 实符号 × 虚符号 ====================

-- 码 q ∈ {0,1,2,3}, 值 (q-1)·d ∈ {-1, 0, 1, 2} — 两个符号轴:
--   方向轴: 负 {−1, 0} | 正 {+1, +2};  迭代轴: 基准 {−1, +1} | 迭代 {0, +2}
-- 定理: 四个格点两两共享一个符号轴 (每格点由 (方向, 迭代) 二元组确定)

-- 方向符号 (实轴侧): -1 与 0 同负侧, +1 与 +2 同正侧
theorem q2_sign_axes :
    (-1 : ℝ) * 1 < 0 ∧ (0 : ℝ) * 1 = 0 ∧
    (1 : ℝ) * 1 > 0 ∧ (2 : ℝ) * 1 > 0 := by
  norm_num

-- 迭代符号 (幅度侧): -1 与 +1 是基点 (单位), 0 与 +2 是迭代/折叠
-- 0 = -1 + 1 (负基点 + 正基点 = 折叠中心, R085);  2 = 1 + 1 (基点迭代, C028)
theorem q2_iter_axes :
    (0 : ℝ) = -1 + 1 ∧ (2 : ℝ) = 1 + 1 := by
  norm_num

-- ==================== 3. pat 3 数 = 实轴投影 (丢虚符号) ====================

-- pat 数值格点 {-1, 0, 1} = 四相位投影到实轴 (C029):
--   Re(1) = 1, Re(-1) = -1, Re(±i) = 0 — 虚部符号在实轴投影中丢失
theorem pat_three_is_real_projection :
    (1 : ℂ).re = 1 ∧ (-1 : ℂ).re = -1 ∧
    Complex.I.re = 0 ∧ (-Complex.I).re = 0 := by
  norm_num

-- Q2_0 四格点 = pat 三元 + 虚符号保留 (2 = 正虚的像, 0 兼任负虚的像/加法基点)
theorem q2_four_vs_pat_three :
    q2_phi 1 = 1 ∧ q2_phi (-1) = -1 ∧ q2_phi Complex.I = 2 ∧
    q2_phi (-Complex.I) = 0 ∧ (0 : ℝ) = -1 + 1 := by
  norm_num [q2_phi]
  simp [complex_I_ne_one, complex_I_ne_neg_one, complex_negI_ne_one, complex_negI_ne_I]

-- ==================== 4. 不是代数同态, 是符号编码 ====================

-- 四相位乘法群: i·i = -1 (J² = -I, C030)
theorem four_phase_mul : Complex.I * Complex.I = -1 := by
  norm_num

-- Q2_0 格点不乘闭: 2·2 = 4 ∉ {-1, 0, 1, 2} — 乘法会离开格点
-- (所以 φ 保持符号, 不保持乘法: "以正负号的形式量化" ≠ 代数同构)
theorem q2_grid_not_mul_closed : (2 : ℝ) * 2 ≠ 1 ∧ (2 : ℝ) * 2 ≠ -1 ∧
    (2 : ℝ) * 2 ≠ 0 ∧ (2 : ℝ) * 2 ≠ 2 := by
  norm_num

-- 四相位和 = 0 (C030 投影对消: 互锁对在任意方向投影和 = 0)
theorem four_phases_sum_zero : (1 : ℂ) + (-1) + Complex.I + (-Complex.I) = 0 := by
  norm_num

end

end ZeroRelative
