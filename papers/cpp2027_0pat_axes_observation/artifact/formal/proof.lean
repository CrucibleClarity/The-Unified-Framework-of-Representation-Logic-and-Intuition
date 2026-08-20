import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# 习题 XXXI: 实轴虚轴在欧拉圆视角下的观测 (0pat)

用户指令 (2026-08-21): 不允许根据定义直接得出结论, 必须观测实轴虚轴
在欧拉圆 1 / 欧拉圆 i 视角下的图形。

观测方法: 把实轴 (im = 0)、虚轴 (re = 0) 放进分裂复数框架
(半径 1 圆 a²-b²=1, 半径 i 圆 a²-b²=-1), 解方程求交点。

观测结果 (全部机器验证):
  1. 实轴 ∩ 虚轴 = {(0,0)}     ← 解 ⟨a,0⟩=⟨0,b⟩ 得 a=0 ∧ b=0 (观测, 非定义)
  2. 实轴 ∩ 半径 1 圆 = {±1}   ← 解 a²=1
  3. 实轴 ∩ 半径 i 圆 = ∅      ← 解 a²=-1 无实解
  4. 虚轴 ∩ 半径 1 圆 = ∅      ← 解 -b²=1 无实解
  5. 虚轴 ∩ 半径 i 圆 = {±i}   ← 解 -b²=-1

观测结论: 实轴与虚轴的交点是 (0,0) (解方程得出);
i = (0,1) 是虚轴与半径 i 圆的交点 (单位), 不是两轴交点。
-/

namespace RealImagAxes

noncomputable section

/-- 分裂复数: a + bj, j² = +1 (XXVII 结构复用, 独立文件)。 -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩
instance : Neg SplitComplex := ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp] theorem re_zero : (0 : SplitComplex).re = 0 := rfl
@[simp] theorem im_zero : (0 : SplitComplex).im = 0 := rfl

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

/-- 虚数单位 j (j² = +1)。 -/
def j : SplitComplex := ⟨0, 1⟩

/-- 伪范数: ‖z‖² = a² - b²。 -/
def normSq (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

/-- 半径 1 圆 (双曲线): ‖z‖² = 1。 -/
def unitCircle : Set SplitComplex := {z | normSq z = 1}

/-- 半径 i 圆 (共轭双曲线): ‖z‖² = -1。 -/
def imaginaryCircle : Set SplitComplex := {z | normSq z = -1}

/-- 实轴: 虚部为 0 的点。 -/
def realAxis : Set SplitComplex := {z | z.im = 0}

/-- 虚轴: 实部为 0 的点。 -/
def imaginaryAxis : Set SplitComplex := {z | z.re = 0}

/-- 观测 1: 实轴 ∩ 虚轴 = {(0,0)}。
    解 ⟨a,0⟩ = ⟨0,b⟩: a = 0 且 b = 0 — 两轴的交点由方程给出。 -/
theorem realAxis_inter_imaginaryAxis :
    realAxis ∩ imaginaryAxis = ({0} : Set SplitComplex) := by
  ext z
  constructor
  · intro hz
    -- z ∈ 实轴: z.im = 0; z ∈ 虚轴: z.re = 0 ⟹ z = ⟨0,0⟩
    have him : z.im = 0 := hz.1
    have hre : z.re = 0 := hz.2
    have hz0 : z = 0 := by
      apply SplitComplex.ext
      · simpa using hre
      · simpa using him
    subst z
    rfl
  · intro hz
    -- z = 0 ⟹ z 在实轴 (im 0 = 0) 且虚轴 (re 0 = 0)
    subst z
    simp [realAxis, imaginaryAxis]

/-- 观测 2: 实轴 ∩ 半径 1 圆 = {±1}。
    解 a² = 1: 实轴上落在半径 1 圆上的点只有 a = 1 和 a = -1。 -/
theorem realAxis_inter_unitCircle :
    realAxis ∩ unitCircle = {z | z = ⟨1, 0⟩ ∨ z = ⟨-1, 0⟩} := by
  ext z
  constructor
  · intro hz
    -- z = ⟨a, 0⟩ (实轴), a² = 1 (单位圆)
    have him : z.im = 0 := hz.1
    have hn : normSq z = 1 := hz.2
    -- 解 a² = 1 ⟹ a = ±1
    have ha : z.re ^ 2 = 1 := by
      simpa [normSq, him] using hn
    have hcases : z.re = 1 ∨ z.re = -1 := by
      -- ℝ 中 a² = 1 ⟹ a = 1 ∨ a = -1
      have h1 : z.re ^ 2 = 1 ^ 2 := by simpa using ha
      exact sq_eq_sq_iff_eq_or_eq_neg.mp h1
    rcases hcases with h1 | hm1
    · left
      ext <;> simp [h1, him]
    · right
      ext <;> simp [hm1, him]
  · intro hz
    rcases hz with hz1 | hz2
    · rcases hz1 with rfl
      simp [realAxis, unitCircle, normSq]
    · rcases hz2 with rfl
      simp [realAxis, unitCircle, normSq]

/-- 观测 3: 实轴 ∩ 半径 i 圆 = ∅。
    解 a² = -1: 无实解 — 实轴上没有任何点落在半径 i 圆上。 -/
theorem realAxis_inter_imaginaryCircle :
    realAxis ∩ imaginaryCircle = ∅ := by
  ext z
  constructor
  · intro hz
    have him : z.im = 0 := hz.1
    have hn : normSq z = -1 := hz.2
    have ha : z.re ^ 2 = -1 := by
      simpa [normSq, him] using hn
    nlinarith
  · intro hz
    simp at hz

/-- 观测 4: 虚轴 ∩ 半径 1 圆 = ∅。
    解 -b² = 1: 无实解。 -/
theorem imaginaryAxis_inter_unitCircle :
    imaginaryAxis ∩ unitCircle = ∅ := by
  ext z
  constructor
  · intro hz
    have hre : z.re = 0 := hz.1
    have hn : normSq z = 1 := hz.2
    have hb : -z.im ^ 2 = 1 := by
      simpa [normSq, hre] using hn
    nlinarith
  · intro hz
    simp at hz

/-- 观测 5: 虚轴 ∩ 半径 i 圆 = {±i}。
    解 -b² = -1 ⟹ b = ±1: 虚轴上落在半径 i 圆上的点只有 j 和 -j。 -/
theorem imaginaryAxis_inter_imaginaryCircle :
    imaginaryAxis ∩ imaginaryCircle = {z | z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩} := by
  ext z
  constructor
  · intro hz
    have hre : z.re = 0 := hz.1
    have hn : normSq z = -1 := hz.2
    have hb : -z.im ^ 2 = -1 := by
      simpa [normSq, hre] using hn
    have hcases : z.im = 1 ∨ z.im = -1 := by
      have h1 : z.im ^ 2 = 1 := by nlinarith
      have h2 : z.im ^ 2 = 1 ^ 2 := by simpa using h1
      exact sq_eq_sq_iff_eq_or_eq_neg.mp h2
    rcases hcases with h1 | hm1
    · left
      ext <;> simp [hre, h1]
    · right
      ext <;> simp [hre, hm1]
  · intro hz
    rcases hz with hz1 | hz2
    · rcases hz1 with rfl
      simp [imaginaryAxis, imaginaryCircle, normSq]
    · rcases hz2 with rfl
      simp [imaginaryAxis, imaginaryCircle, normSq]

end SplitComplex

end
end RealImagAxes
