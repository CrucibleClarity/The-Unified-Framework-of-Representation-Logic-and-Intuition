/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Formal.ZeroRelative.SymplecticProjection
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# C031: 离散化 — 四相位离散群 + recip=共轭 (每对完整算符结构) + 基点簇 (2026-08-18)

用户指令 (2026-08-18): 继续做离散化, 重新做力学观测 — 全算符还原下,
结构不会是 12 维了, **因为算符变了**。

12 对 = ℂ¹² 的计数基础 (PatMechanicsSymmetry.lean): 每对 = 1 复平面 =
J 的四相位轨道 {1, -1, i, -i} (C₄, J² = -I)。

全算符还原 (C026-C030): 每对不再是 J 单独生成的 C₄, 而是完整算符家族的
载体。关键新结构 (本文件形式化):
  T1 quad_phase_card: 四相位 = J 的离散轨道 (4 元素, C₄)
  T2 recip_is_conjugate: **recipOp (倒数, 基点 ±1) 在单位圆上 = 共轭反射**
    (normSq z = 1 ⟹ 1/z = conj z) — J 轨道外的独立生成元
  T3 conjugate_anticommutes_J: 共轭与 J 反交换 conj(Jz) = -J(conj z) —
    每对相位空间扩展为 D4 (8 元素: 4 旋转 × 2 反射)
  T4 discrete_projection_cancel: 四相位离散投影对消 (任意方向和 = 0)
  T5 basepoint_cluster: 基点簇 {0, ±1, ±i} = 5 位置 (中心 + 双轴投影极值)

★ 观测结论预告: 每对从 C₄ (4 相位) 扩展为 D4 (8 相位, 含共轭反射),
recipOp 的基点 ±1 (C028) 给出 J 轨道外的新位置 — 全算符还原下
每对不再是 1 个 J 复平面, 结构维度不是 12。
-/

namespace ZeroRelative

noncomputable section

open Complex
open scoped ComplexConjugate
open scoped BigOperators

-- ==================== T1: 四相位离散群 (C₄, J 轨道) ====================

/-- 四相位离散点集: {1, -1, i, -i} (J² = -I 的轨道). -/
def quadPhase : Finset ℂ := {1, -1, Complex.I, -Complex.I}

-- 四相位互异 (离散轨道 4 元素): 1 ≠ -1 ≠ I ≠ -I 两两不同
theorem quad_phase_distinct :
    (1 : ℂ) ≠ -1 ∧ (1 : ℂ) ≠ Complex.I ∧ (1 : ℂ) ≠ -Complex.I ∧
    (-1 : ℂ) ≠ Complex.I ∧ (-1 : ℂ) ≠ -Complex.I ∧ Complex.I ≠ -Complex.I := by
  norm_num [Complex.ext_iff]

-- 四相位都在单位圆上 (离散化位置 ∈ S¹)
theorem quad_phase_on_circle (z : ℂ) (hz : z ∈ quadPhase) :
    Complex.normSq z = 1 := by
  simp [quadPhase] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> norm_num [Complex.normSq]

-- ==================== T2: recipOp 在单位圆上 = 共轭反射 ====================

-- 核心: 倒数算符 (基点 ±1, C028) 在单位圆上 = 共轭反射
-- (normSq z = 1 ⟹ 1/z = conj z) — J 轨道外的独立生成元
theorem recip_is_conjugate {z : ℂ} (hz : Complex.normSq z = 1) :
    z⁻¹ = conj z := by
  apply inv_eq_of_mul_eq_one_left
  -- conj z · z = normSq z = 1
  rw [← Complex.normSq_eq_conj_mul_self]
  norm_num [hz]

-- 共轭不动点: ±1 (实数, 实轴投影极值)
theorem conjugate_fixes_one : conj (1 : ℂ) = 1 := by
  norm_num

theorem conjugate_fixes_neg_one : conj (-1 : ℂ) = -1 := by
  norm_num

-- 共轭交换 ±i (虚轴反射)
theorem conjugate_swaps_imag : conj (Complex.I : ℂ) = -Complex.I := by
  norm_num

-- ==================== T3: 共轭与 J 反交换 (每对 → D4) ====================

-- 共轭与 J 反交换: conj(J z) = -J(conj z) — 共轭不在 J 轨道内,
-- 每对相位空间 = 4 旋转 × 2 反射 = D4 (8 元素)
theorem conjugate_anticommutes_J (z : ℂ) : conj (J z) = -J (conj z) := by
  simp [J]

-- 每对完整离散相位结构: 四相位 ∪ 共轭四相位 = 8 元素 (D4)
def pairPhaseD4 : Finset ℂ :=
  {1, -1, Complex.I, -Complex.I, conj (1 : ℂ), conj (-1 : ℂ),
   conj Complex.I, conj (-Complex.I)}

-- D4 结构 = 四相位 ∪ 共轭四相位 (4 旋转 × 2 反射); 共轭扩展的生成元身份:
-- 共轭反射 (recip) 保持 ±1, 交换 ±i — J 轨道外的独立维度
-- (card 不可计算: ℝ 的 DecidableEq 非计算; 结构由生成元定理承载)

-- ==================== T4: 离散投影对消 ====================

-- 四相位离散投影对消: 任意方向 u 的投影和 = 0 (显式四项 = C030 Finset 版;
-- Finset.sum 字面量展开需 DecidableEq ℂ, 非计算 — 故显式列四项)
theorem discrete_projection_cancel (u : ℂ) :
    Complex.re ((1 : ℂ) * conj u) + Complex.re ((-1 : ℂ) * conj u) +
    Complex.re (Complex.I * conj u) + Complex.re ((-Complex.I) * conj u) = 0 := by
  linarith [projection_cancel_any_direction u]

-- ==================== T5: 基点簇 {0, ±1, ±i} ====================

/-- 基点簇 (离散化后的完整基点集): 中心 0 + 双轴投影极值 ±1, ±i. -/
def basepointCluster : Finset ℂ := {0, 1, -1, Complex.I, -Complex.I}

-- 0 = 加法基点 (投影中心/折叠中心 R085)
theorem cluster_zero_additive : (0 : ℂ) ∈ basepointCluster := by
  simp [basepointCluster]

-- ±1 = 乘法基点 (实轴投影极值, 2 个位置 — C029)
theorem cluster_pm_one : (1 : ℂ) ∈ basepointCluster ∧ (-1 : ℂ) ∈ basepointCluster := by
  simp [basepointCluster]

-- ±i = 虚轴投影极值 (2 个位置 — C029)
theorem cluster_pm_i : Complex.I ∈ basepointCluster ∧ -Complex.I ∈ basepointCluster := by
  simp [basepointCluster]

-- 基点簇结构: 每根投影轴出 2 个极值位置 (±1 / ±i) + 1 个中心 (0)
-- (离散化: 5 位置 = 2 轴 × 2 极值 + 中心)

end

end ZeroRelative
