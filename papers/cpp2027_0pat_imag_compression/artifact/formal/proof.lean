import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# 习题 XXXIII: 虚部被压进系数轴 — 乘积的泄漏 (0pat)

用户洞察 (2026-08-21): 复平面的虚轴不代表虚部, 只代表虚部的实系数。
虚轴上的刻度是实数 t, "虚" (i) 被压进轴的语义里。
当虚部被压进实系数轴时, 虚部与虚部的乘积会出现在其他地方 —
乘法中两个虚部系数的乘积 bd 泄漏到实部坐标, 符号由虚数单位的平方决定:

  ℂ  (i² = −1): (a+bi)(c+di) 实部 = ac − bd   ← 虚部乘积带负号泄漏到实部
  分裂 (j² = +1): (a+bj)(c+dj) 实部 = ac + bd   ← 虚部乘积带正号泄漏到实部

定理:
1. complex_imag_axis_coefficient: 虚轴上的点 = 实系数 t × 虚单位 i
   (z = t·i ⟺ z.re = 0 ∧ z.im = t; 轴刻度只显示系数, 不显示 i)
2. complex_mul_imag_leaks: ℂ 中虚部系数乘积 bd 出现在实部 (带 −, i²=−1)
3. split_mul_imag_leaks: 分裂中虚部系数乘积 bd 出现在实部 (带 +, j²=+1)
4. leak_sign_is_unit_square: 泄漏符号 = 虚数单位的平方 (−1 vs +1)

谱系坐标: (R20, C8) 圆上量化 × 构造; 连接 XXVII/XXXII。
-/

namespace ImagCoefficientCompression

noncomputable section

open Complex

/-- 定理 1: 虚轴上的点 = 实系数 × 虚单位 — 轴刻度只显示系数 t,
    虚单位 i 被压进轴 (z.re = 0 时, z = t·i 且 t = z.im)。 -/
theorem complex_imag_axis_coefficient {z : ℂ} {t : ℝ} :
    z = t * I ↔ z.re = 0 ∧ z.im = t := by
  constructor
  · intro h
    rw [h]
    simp [Complex.I]
  · intro hz
    -- z = ⟨0, t⟩ = t·i
    apply Complex.ext <;> simp [Complex.I, hz.1, hz.2]

/-- 定理 2: ℂ 中虚部系数乘积泄漏到实部 (带负号, i² = −1)。
    (a+bi)(c+di) 的实部 = ac − bd: 两个虚部系数的乘积 bd
    离开虚部, 出现在实部, 符号由 i·i = −1 决定。 -/
theorem complex_mul_imag_leaks (a b c d : ℝ) :
    ((a + b * I) * (c + d * I) : ℂ).re = a * c - b * d := by
  simp [Complex.I]

/-- 定理 2b: ℂ 中交叉项留在虚部: 虚部 = ad + bc。 -/
theorem complex_mul_cross_stays_imag (a b c d : ℝ) :
    ((a + b * I) * (c + d * I) : ℂ).im = a * d + b * c := by
  simp [Complex.I]

/-- 分裂复数的乘法 (XXVII 结构, 独立文件)。 -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩
instance : Mul SplitComplex :=
  ⟨fun z w => ⟨z.re * w.re + z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp] theorem re_one : (1 : SplitComplex).re = 1 := rfl
@[simp] theorem im_one : (1 : SplitComplex).im = 0 := rfl

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

/-- 定理 3: 分裂中虚部系数乘积泄漏到实部 (带正号, j² = +1)。
    (a+bj)(c+dj) 的实部 = ac + bd — 同样的"压进", 符号由 j·j = +1 决定。 -/
theorem split_mul_imag_leaks (a b c d : ℝ) :
    ((⟨a, b⟩ : SplitComplex) * ⟨c, d⟩).re = a * c + b * d := by
  rfl

/-- 定理 4: 泄漏符号 = 虚数单位的平方。
    ℂ: i·i = −1 (泄漏带 −); 分裂: j·j = +1 (泄漏带 +)。 -/
theorem leak_sign_is_unit_square :
    I * I = -1 ∧ (⟨0, 1⟩ : SplitComplex) * ⟨0, 1⟩ = 1 := by
  constructor
  · apply Complex.ext <;> simp [Complex.I]
  · change (⟨0 * 0 + 1 * 1, 0 * 1 + 1 * 0⟩ : SplitComplex) = 1
    ext <;> norm_num

end SplitComplex

end
end ImagCoefficientCompression
