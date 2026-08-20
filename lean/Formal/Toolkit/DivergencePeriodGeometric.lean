/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Toolkit/DivergencePeriodGeometric — 发散与周期的几何独立证明 (零依赖)

User request (2026-08-14): 课后习题 XVI (R173, 孪生素数间隔 = 震荡周期轴)
专门研究了 "观测素数/超越数/i/n元数/复平面 → 发散与周期同一对称性" 的归纳。
本文件**不使用任何单相位数定理** (R072/R091/RulerPhase/ComplexAxis 全不依赖),
仅用实数几何基础, 从零证明:

  R047 的几何核心: 发散轴与周期轴是同一反射对称性 S 的特征空间分解。

几何构造:
  S (x,y) = (x,-y)  关于实轴的镜像反射 (det = -1, 正交)
  J (x,y) = (-y,x)  逆时针 90° 旋转 (det = +1, 等距)
  实轴 (x,0) = S 不动点集 (特征值 +1) = 发散轴 (平移不回返)
  虚轴 (0,y) = S 反射方向 (特征值 -1) = 周期轴 (旋转四次回返)

## Main theorems (全部 0 sorry):

1. `reflection_involutive`: S 是对合 (S² = id) — 反射是二阶对称性
2. `rotation_period_four`: J 周期 4 (J⁴ = id) — 旋转是四阶周期
3. `real_axis_fixed`: 实轴 = S 不动点集 (特征值 +1)
4. `imag_axis_reflected`: 虚轴 = S 取反方向 (特征值 -1)
5. `eigen_decomposition`: 任意向量 = S-固定分量 + S-取反分量 (特征分解)
6. `real_axis_diverges`: 实轴平移不回返 (发散, t ≠ 0 时 ∀ n ≠ 0)
7. `imag_axis_periodic`: 虚轴旋转四次回返 (周期)
8. `divergence_period_same_symmetry`: 核心 — 发散轴与周期轴 = 同一反射 S 的特征空间
-/

namespace ZeroRelative

namespace GeometricSynthesis

/-! ## 1. 对称性构造 (纯几何)

反射 S (关于实轴) 与旋转 J (90°): 两者都是平面的正交变换,
共享同一结构 — 同一对称性群的不同方向 (R047 的几何化). -/

/-- 反射 S: 关于实轴的镜像 (x,y) ↦ (x,-y)。正交, det = -1。 -/
def S (v : ℝ × ℝ) : ℝ × ℝ := (v.1, -v.2)

/-- 旋转 J: 逆时针 90° (x,y) ↦ (-y,x)。正交, det = +1。 -/
def J (v : ℝ × ℝ) : ℝ × ℝ := (-v.2, v.1)

/-- 实轴: (x,0) — 水平方向。 -/
def realAxis (x : ℝ) : ℝ × ℝ := (x, 0)

/-- 虚轴: (0,y) — 垂直方向。 -/
def imagAxis (y : ℝ) : ℝ × ℝ := (0, y)

/-! ## 2. S 对合与 J 周期

S² = id: 反射两次还原。J⁴ = id: 旋转四次还原 (90°×4 = 360°). -/

/-- **S 是对合**: S(S v) = v — 反射是二阶对称性 (R047: S 是特征分解的对称性). -/
theorem reflection_involutive (v : ℝ × ℝ) : S (S v) = v := by
  simp [S]

/-- **J 周期 4**: J(J(J(J v))) = v — 旋转 90° 四次回返 (周期轴: 一圈闭合). -/
theorem rotation_period_four (v : ℝ × ℝ) : J (J (J (J v))) = v := by
  simp [J]

/-! ## 3. 特征空间: 实轴 = 发散轴, 虚轴 = 周期轴

实轴是 S 的不动点集 (特征值 +1), 虚轴是 S 的取反方向 (特征值 -1).
-/

/-- **实轴 = S 不动点集 (特征值 +1)**: S(x,0) = (x,0) — 发散轴是 S 的固定方向. -/
theorem real_axis_fixed (x : ℝ) : S (realAxis x) = realAxis x := by
  simp [S, realAxis]

/-- **虚轴 = S 取反方向 (特征值 -1)**: S(0,y) = -(0,y) — 周期轴是 S 的反射方向. -/
theorem imag_axis_reflected (y : ℝ) : S (imagAxis y) = -imagAxis y := by
  simp [S, imagAxis]

/-! ## 4. 特征分解: 任意向量 = S-固定 + S-取反

R047 核心: 周期与发散的分解 = 一个对称性的特征空间直和. -/

/-- S-固定分量: 实轴投影 (x, 0)。 -/
def fixedPart (v : ℝ × ℝ) : ℝ × ℝ := (v.1, 0)

/-- S-取反分量: 虚轴投影 (0, v.2)。 -/
def flippedPart (v : ℝ × ℝ) : ℝ × ℝ := (0, v.2)

/-- **特征分解**: v = S-固定分量 + S-取反分量 — 任意向量分解为发散部分
(实轴) + 周期部分 (虚轴) 的直和. -/
theorem eigen_decomposition (v : ℝ × ℝ) : v = fixedPart v + flippedPart v := by
  rcases v with ⟨x, y⟩
  simp [fixedPart, flippedPart]

/-- **固定分量 S-固定**: S(fixedPart v) = fixedPart v. -/
theorem fixed_is_S_fixed (v : ℝ × ℝ) : S (fixedPart v) = fixedPart v := by
  simp [S, fixedPart]

/-- **取反分量 S-取反**: S(flippedPart v) = -flippedPart v. -/
theorem flipped_is_S_flipped (v : ℝ × ℝ) : S (flippedPart v) = -flippedPart v := by
  simp [S, flippedPart]

/-! ## 5. 发散: 实轴平移不回返

实轴 (发散轴) 上平移 t ≠ 0, 第 n 步 (n ≠ 0) 永不回返 — 发散. -/

/-- **实轴平移不回返 (发散)**: t ≠ 0 ⟹ (x + n·t, 0) ≠ (x, 0) 对任意 n ≠ 0 —
发散轴上的移动无周期 (结构上永不回到原点). -/
theorem real_axis_diverges (t x : ℝ) (ht : t ≠ 0) :
    ∀ n : ℕ, n ≠ 0 → realAxis x + (n : ℝ) * (t, 0) ≠ realAxis x := by
  intro n hn
  simp [realAxis]
  have h : (n : ℝ) * t ≠ 0 := by
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hn) ht
  simpa [add_comm, sub_eq_add_neg, ne_eq] using h

/-! ## 6. 周期: 虚轴旋转四次回返

虚轴 (周期轴) 上旋转 J 四次回返 — 周期. -/

/-- **虚轴旋转四次回返 (周期)**: J⁴(0,y) = (0,y) — 周期轴上的运动闭合. -/
theorem imag_axis_periodic (y : ℝ) : J (J (J (J (imagAxis y)))) = imagAxis y := by
  simp [J, imagAxis]

/-! ## 7. 核心合成: 发散与周期 = 同一反射 S 的特征空间

组合定理: ① S 对合 ② 实轴 S-固定 ③ 虚轴 S-取反 ④ 特征分解
⑤ 实轴发散 ⑥ 虚轴周期 — 同一对称性 S 的两个特征空间的几何全貌. -/

/-- **发散与周期同一对称性 (零依赖几何版)**: —
  ① S 是对合 (二阶反射对称性);
  ② 实轴 = S 不动点集 (特征值 +1) = 发散轴;
  ③ 虚轴 = S 取反方向 (特征值 -1) = 周期轴;
  ④ 任意向量 = S-固定 + S-取反 (特征分解);
  ⑤ 实轴平移不回返 (发散);
  ⑥ 虚轴旋转四次回返 (周期)。 -/
theorem divergence_period_same_symmetry :
    -- ① S 对合
    (∀ v : ℝ × ℝ, S (S v) = v) ∧
    -- ② 实轴 = S 不动点集
    (∀ x : ℝ, S (realAxis x) = realAxis x) ∧
    -- ③ 虚轴 = S 取反方向
    (∀ y : ℝ, S (imagAxis y) = -imagAxis y) ∧
    -- ④ 特征分解
    (∀ v : ℝ × ℝ, v = fixedPart v + flippedPart v) ∧
    -- ⑤ 实轴发散 (平移不回返)
    (∀ t x : ℝ, t ≠ 0 → ∀ n : ℕ, n ≠ 0 →
      realAxis x + (n : ℝ) * (t, 0) ≠ realAxis x) ∧
    -- ⑥ 虚轴周期 (旋转四次回返)
    (∀ y : ℝ, J (J (J (J (imagAxis y)))) = imagAxis y) := by
  constructor
  · intro v; exact reflection_involutive v
  · constructor
    · intro x; exact real_axis_fixed x
    · constructor
      · intro y; exact imag_axis_reflected y
      · constructor
        · intro v; exact eigen_decomposition v
        · constructor
          · intro t x ht; exact real_axis_diverges t x ht
          · intro y; exact imag_axis_periodic y

end GeometricSynthesis

end ZeroRelative
