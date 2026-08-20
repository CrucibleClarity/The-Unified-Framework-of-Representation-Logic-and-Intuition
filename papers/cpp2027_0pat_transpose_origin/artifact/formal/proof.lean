import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# 习题 XXX: 横纵轴转置与正交视角下的原点 (0pat)

用户洞察 (2026-08-21): 在欧拉圆 1 (半径 1) 与欧拉圆 i (半径 i) 的正交视角下,
先证明横纵轴转置 (1 ↔ i 的镜像), 再确定原点。

精确结果:
1. 转置 (a,b) ↦ (b,a) 是自逆对合, 把 1 = (1,0) 映到 i = (0,1)。
2. 转置把半径 1 圆 (a²-b²=1) 映到半径 i 圆 (a²-b²=-1) — 双向。
3. 自然数格点唯一性: 半径 1 圆唯一格点 (1,0) = 1; 半径 i 圆唯一格点 (0,1) = i。
   (上一轮"1 i 是转置结果"的精确化: 每个圆在格点观测下只剩自己的单位。)
4. 原点判定: 转置保持原点 (0,0) 不动; 两个共轭双曲线关于原点中心对称 —
   正交视角下的原点是 (0,0) (分裂零元, 双曲线的公共中心), 不是 i。

谱系坐标: (R20, C8) 圆上量化 × 构造; 连接 XXVII (分裂复数)。
-/

namespace TransposeOrigin

noncomputable section

/-- 分裂复数: a + bj, j² = +1 (XXVII 结构复用, 独立文件)。 -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩
instance : Add SplitComplex := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Mul SplitComplex :=
  ⟨fun z w => ⟨z.re * w.re + z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
instance : Neg SplitComplex := ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

@[simp] theorem re_zero : (0 : SplitComplex).re = 0 := rfl
@[simp] theorem im_zero : (0 : SplitComplex).im = 0 := rfl
@[simp] theorem re_mul (z w : SplitComplex) : (z * w).re = z.re * w.re + z.im * w.im := rfl
@[simp] theorem im_mul (z w : SplitComplex) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] theorem re_one : (1 : SplitComplex).re = 1 := rfl
@[simp] theorem im_one : (1 : SplitComplex).im = 0 := rfl

/-- 虚数单位 j (j² = +1)。 -/
def j : SplitComplex := ⟨0, 1⟩

/-- 伪范数 (闵可夫斯基度量): ‖a + bj‖² = a² - b²。 -/
def normSq (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

/-- 半径 1 圆 (双曲线): ‖z‖² = 1。 -/
def unitCircle : Set SplitComplex := {z | normSq z = 1}

/-- 半径 i 圆 (共轭双曲线): ‖z‖² = -1。 -/
def imaginaryCircle : Set SplitComplex := {z | normSq z = -1}

/-- 横纵轴转置: (a, b) ↦ (b, a) (镜像)。 -/
def transpose (z : SplitComplex) : SplitComplex := ⟨z.im, z.re⟩

@[simp] theorem re_transpose (z : SplitComplex) : (transpose z).re = z.im := rfl
@[simp] theorem im_transpose (z : SplitComplex) : (transpose z).im = z.re := rfl

/-- 转置是对合 (自逆): transpose (transpose z) = z。 -/
theorem transpose_involutive (z : SplitComplex) : transpose (transpose z) = z := by
  ext <;> simp [transpose]

/-- 转置把 1 映到 i: transpose 1 = j。 -/
theorem transpose_maps_one_to_i : transpose (1 : SplitComplex) = j := by
  ext <;> simp [transpose, j]

/-- 转置保持原点: transpose 0 = 0 (原点在镜像下不动 — 原点不是 1 或 i)。 -/
theorem transpose_origin_fixed : transpose (0 : SplitComplex) = 0 := by
  ext <;> simp [transpose]

/-- 转置把半径 1 圆映到半径 i 圆 (正向): z ∈ 单位圆 ⟹ transpose z ∈ 虚半径圆。 -/
theorem transpose_maps_unit_to_imaginary {z : SplitComplex} (hz : z ∈ unitCircle) :
    transpose z ∈ imaginaryCircle := by
  simp [unitCircle, imaginaryCircle, normSq] at hz ⊢
  nlinarith

/-- 转置把半径 i 圆映到半径 1 圆 (反向)。 -/
theorem transpose_maps_imaginary_to_unit {z : SplitComplex} (hz : z ∈ imaginaryCircle) :
    transpose z ∈ unitCircle := by
  simp [unitCircle, imaginaryCircle, normSq] at hz ⊢
  nlinarith

/-- 自然数格点唯一性 (半径 1 圆): a² - b² = 1 的自然数解唯一 = (1, 0)。
    b = 0 时 a² = 1 ⟹ a = 1; b ≥ 1 时 (b+1)² - b² ≥ 3 矛盾。 -/
theorem lattice_unique_unit {a b : ℕ} (h : a ^ 2 - b ^ 2 = 1) : a = 1 ∧ b = 0 := by
  by_cases hb : b = 0
  · -- b = 0: a² = 1 ⟹ a = 1
    subst b
    have ha : a ^ 2 = 1 := by simpa using h
    have hle1 : a ≤ 1 := by
      by_contra h2
      have h2a : 2 ≤ a := Nat.succ_le_of_lt (Nat.lt_of_not_ge h2)
      have hsq : 4 ≤ a ^ 2 := by
        have hsq' : 2 ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left h2a 2
        norm_num at hsq' ⊢
        exact hsq'
      omega
    have ha0 : a ≠ 0 := by
      intro hz
      subst a
      norm_num at ha
    omega
  · -- b ≥ 1: a² - b² = 1 不可能 (a > b 时差值 ≥ 3)
    have hb1 : 1 ≤ b := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb)
    have hagtb : b < a := by
      have hgt : b ^ 2 < a ^ 2 := by
        have ha_eq : b ^ 2 + 1 = a ^ 2 := by omega
        omega
      by_contra hba
      have hle : a ≤ b := Nat.le_of_not_gt hba
      have hsq : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    have ha1 : b + 1 ≤ a := Nat.succ_le_of_lt hagtb
    have hsq1 : (b + 1) ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left ha1 2
    have hsub : a ^ 2 - b ^ 2 ≥ (b + 1) ^ 2 - b ^ 2 :=
      Nat.sub_le_sub_right hsq1 (b ^ 2)
    have hdiff : (b + 1) ^ 2 - b ^ 2 ≥ 3 := by
      have hring : (b + 1) ^ 2 = b ^ 2 + (2 * b + 1) := by ring
      rw [hring]
      omega
    omega

/-- 自然数格点唯一性 (半径 i 圆): b² - a² = 1 的自然数解唯一 = (0, 1)。 -/
theorem lattice_unique_imaginary {a b : ℕ} (h : b ^ 2 - a ^ 2 = 1) : a = 0 ∧ b = 1 := by
  by_cases ha : a = 0
  · -- a = 0: b² = 1 ⟹ b = 1
    subst a
    have hb : b ^ 2 = 1 := by simpa using h
    have hle1 : b ≤ 1 := by
      by_contra h2
      have h2b : 2 ≤ b := Nat.succ_le_of_lt (Nat.lt_of_not_ge h2)
      have hsq : 4 ≤ b ^ 2 := by
        have hsq' : 2 ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left h2b 2
        norm_num at hsq' ⊢
        exact hsq'
      omega
    have hb0 : b ≠ 0 := by
      intro hz
      subst b
      norm_num at hb
    omega
  · -- a ≥ 1: b² - a² = 1 不可能 (b > a 时差值 ≥ 3)
    have ha1 : 1 ≤ a := Nat.succ_le_of_lt (Nat.pos_of_ne_zero ha)
    have hagta : a < b := by
      have hgt : a ^ 2 < b ^ 2 := by
        have hb_eq : a ^ 2 + 1 = b ^ 2 := by omega
        omega
      by_contra hba
      have hle : b ≤ a := Nat.le_of_not_gt hba
      have hsq : b ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    have hb1 : a + 1 ≤ b := Nat.succ_le_of_lt hagta
    have hsq1 : (a + 1) ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hb1 2
    have hsub : b ^ 2 - a ^ 2 ≥ (a + 1) ^ 2 - a ^ 2 :=
      Nat.sub_le_sub_right hsq1 (a ^ 2)
    have hdiff : (a + 1) ^ 2 - a ^ 2 ≥ 3 := by
      have hring : (a + 1) ^ 2 = a ^ 2 + (2 * a + 1) := by ring
      rw [hring]
      omega
    omega

end SplitComplex

end
end TransposeOrigin
