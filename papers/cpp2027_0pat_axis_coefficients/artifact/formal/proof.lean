import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# 习题 XXXII: 虚轴系数类型与原点 (0pat)

用户指令 (2026-08-21): 解方程时必须标明系数类型 —
虚轴的系数是自然数, 但虚轴代表复数的虚部。

设定:
  A. 按自然数算: 虚轴 = {n·i : n ∈ ℕ} (离散, 自然数系数)
  B. 按虚部算:   虚轴 = {t·i : t ∈ ℝ} (连续, 实系数)
  实轴始终 = ℝ (连续实数轴)。

计算结果:
  1. 按自然数算: 实轴 ∩ 自然数虚轴 = {0}  (解 x = n·i: x = 0 且 n = 0)
  2. 按虚部算:   实轴 ∩ 连续虚轴 = {0}    (解 x = t·i: x = 0 且 t = 0)
  → 两种算法下, 原点都是 (0,0)。

转置定理 (用户要求: 按自然数算时, 另一根轴转置到虚轴并按虚部算):
  3. transpose '' realAxis = imaginaryAxis: 实轴的转置像 = 虚轴 (连续, 实系数) —
     实轴转置后按虚部 (连续) 算。
  4. transpose 保持自然数系数: 自然数虚轴的转置 = 自然数实轴 (离散保持离散)。

谱系坐标: (R20, C8); 连接 XXX/XXXI。
-/

namespace AxisCoefficientsOrigin

noncomputable section

/-- 分裂复数: a + bj, j² = +1 (XXVII 结构复用, 独立文件)。 -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩

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

/-- 实轴: 虚部为 0 的点 (连续实数轴)。 -/
def realAxis : Set SplitComplex := {z | z.im = 0}

/-- 虚轴 (按虚部算): 实部为 0 的点, 系数为实数 (连续)。 -/
def imaginaryAxis : Set SplitComplex := {z | z.re = 0}

/-- 虚轴 (按自然数算): 虚部系数为自然数 (离散): {n·i : n ∈ ℕ}。 -/
def naturalImaginaryAxis : Set SplitComplex := {z | ∃ n : ℕ, z = ⟨0, (n : ℝ)⟩}

/-- 横纵轴转置: (a, b) ↦ (b, a)。 -/
def transpose (z : SplitComplex) : SplitComplex := ⟨z.im, z.re⟩

/-- 计算 1 (按自然数算): 实轴 ∩ 自然数虚轴 = {0}。
    解 x = n·i: 实部 x = 0 且虚部系数 n = 0 — 原点是 0。 -/
theorem origin_natural_coefficients :
    realAxis ∩ naturalImaginaryAxis = ({0} : Set SplitComplex) := by
  ext z
  constructor
  · intro hz
    -- z ∈ 实轴: z.im = 0; z ∈ 自然数虚轴: ∃ n, z = ⟨0, n⟩
    have him : z.im = 0 := hz.1
    rcases hz.2 with ⟨n, hn⟩
    -- z = ⟨0, n⟩ 且 z.im = 0 ⟹ n = 0 ⟹ z = 0
    have hn0 : (n : ℝ) = 0 := by
      -- ⟨0, n⟩.im = n = z.im = 0
      have : (⟨0, (n : ℝ)⟩ : SplitComplex).im = z.im := by rw [hn]
      simpa [him] using this
    have hnz : n = 0 := by
      exact_mod_cast hn0
    have hz0 : z = 0 := by
      rw [hn]
      apply SplitComplex.ext
      · simp
      · rw [hnz]
        simp
    exact hz0
  · intro hz
    -- z = 0: 在实轴 (im 0 = 0) 且在自然数虚轴 (0 = ⟨0, 0⟩, n = 0)
    subst z
    constructor
    · simp [realAxis]
    · refine ⟨0, ?_⟩
      apply SplitComplex.ext <;> simp

/-- 计算 2 (按虚部算): 实轴 ∩ 连续虚轴 = {0}。
    解 x = t·i: x = 0 且 t = 0 — 原点是 0。 -/
theorem origin_imaginary_part :
    realAxis ∩ imaginaryAxis = ({0} : Set SplitComplex) := by
  ext z
  constructor
  · intro hz
    have him : z.im = 0 := hz.1
    have hre : z.re = 0 := hz.2
    have hz0 : z = 0 := by
      apply SplitComplex.ext
      · simpa using hre
      · simpa using him
    subst z
    rfl
  · intro hz
    subst z
    simp [realAxis, imaginaryAxis]

/-- 转置定理 1: transpose '' realAxis = imaginaryAxis —
    实轴的转置像 = 虚轴 (连续, 实系数): 实轴转置后按虚部 (连续) 算。 -/
theorem transpose_realAxis_eq_imaginaryAxis :
    transpose '' realAxis = imaginaryAxis := by
  ext z
  constructor
  · -- z = transpose x, x ∈ realAxis (x.im = 0)
    rintro ⟨x, hx, rfl⟩
    -- transpose x = ⟨x.im, x.re⟩ = ⟨0, x.re⟩ ⟹ re = 0
    have hx0 : x.im = 0 := hx
    simp [imaginaryAxis, transpose, hx0]
  · -- z ∈ imaginaryAxis (z.re = 0): z = transpose ⟨z.im, 0⟩, 且 ⟨z.im, 0⟩ ∈ realAxis
    intro hz
    have hre : z.re = 0 := hz
    refine ⟨⟨z.im, 0⟩, ?_, ?_⟩
    · simp [realAxis]
    · -- transpose ⟨z.im, 0⟩ = ⟨0, z.im⟩ = z
      ext <;> simp [transpose, hre]

/-- 转置定理 2: 转置保持自然数系数 —
    自然数虚轴的转置 = 自然数实轴 (离散保持离散, 自然数不因转置变连续)。 -/
theorem transpose_natural_imaginary_is_natural_real :
    transpose '' naturalImaginaryAxis = {z | ∃ n : ℕ, z = ⟨(n : ℝ), 0⟩} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨n, rfl⟩
    -- transpose ⟨0, n⟩ = ⟨n, 0⟩
    refine ⟨n, ?_⟩
    ext <;> simp [transpose]
  · intro hz
    rcases hz with ⟨n, hn⟩
    -- z = ⟨n, 0⟩ = transpose ⟨0, n⟩, 且 ⟨0, n⟩ ∈ naturalImaginaryAxis
    refine ⟨⟨0, (n : ℝ)⟩, ?_, ?_⟩
    · refine ⟨n, ?_⟩
      rfl
    · -- transpose ⟨0, n⟩ = ⟨n, 0⟩ = z
      rw [hn]
      ext <;> simp [transpose]

end SplitComplex

end
end AxisCoefficientsOrigin
