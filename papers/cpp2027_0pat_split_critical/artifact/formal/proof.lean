import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# 习题 XXVIII: 分裂复数下的临界线观测 (0pat)

在分裂复数架构 (XXVII: j²=+1, 伪范数 a²-b²) 下观测黎曼方向的临界线:

1. 临界线点 1/2 + tj 的伪范数 = 1/4 - t² — 实部条件 Re=1/2
   在分裂坐标下变成虚部阈值 |t| = 1/2 (实部↔虚部角色互换)。
2. 阈值: |t| > 1/2 ⟹ 类空 (半径 i 圆区域); |t| < 1/2 ⟹ 类时。
3. recip (乘法逆) 把临界线映到双曲线 (a-1)² - b² = 1 —
   这是 ℂ 中"recip(临界线) = 圆 (a-1)²+b² = 1" (C019-C022 已证) 的
   分裂对偶: 同一映射, 两个宿主, 圆 ⟷ 双曲线。
4. 零点观测: 临界线零点 (若存在) 的分裂伪范数 < 0 (类空),
   因为已知零点虚部 |t| ≥ 14.13 > 1/2 — 阈值 1/2 由分裂结构本身给出。

谱系坐标: (R23, C3) × (R20, C8); 连接 XXVII (分裂复数) 与 C019-C022 (临界圆)。
-/

namespace SplitComplexCritLine

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

@[simp] theorem re_add (z w : SplitComplex) : (z + w).re = z.re + w.re := rfl
@[simp] theorem im_add (z w : SplitComplex) : (z + w).im = z.im + w.im := rfl
@[simp] theorem re_mul (z w : SplitComplex) : (z * w).re = z.re * w.re + z.im * w.im := rfl
@[simp] theorem im_mul (z w : SplitComplex) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] theorem re_one : (1 : SplitComplex).re = 1 := rfl
@[simp] theorem im_one : (1 : SplitComplex).im = 0 := rfl

/-- 伪范数 (闵可夫斯基度量)。 -/
def normSq (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

/-- 乘法逆: (a+bj)⁻¹ = (a-bj)/(a²-b²), 当伪范数非零。 -/
noncomputable instance : Inv SplitComplex :=
  ⟨fun z => ⟨z.re / normSq z, -z.im / normSq z⟩⟩

@[simp] theorem re_inv (z : SplitComplex) : (z⁻¹).re = z.re / normSq z := rfl
@[simp] theorem im_inv (z : SplitComplex) : (z⁻¹).im = -z.im / normSq z := rfl

/-- 逆是乘法逆 (当伪范数非零)。 -/
theorem inv_mul_self {z : SplitComplex} (hz : normSq z ≠ 0) : z⁻¹ * z = 1 := by
  have hz' : z.re ^ 2 - z.im ^ 2 ≠ 0 := by simpa [normSq] using hz
  ext
  · dsimp [normSq]
    field_simp [hz']
    ring
  · dsimp [normSq]
    field_simp [hz']
    ring

/-- 临界线点 1/2 + tj 的伪范数: ‖1/2 + tj‖² = 1/4 - t²。
    实部条件 Re = 1/2 在分裂坐标下变成虚部阈值 |t| = 1/2。 -/
theorem critical_line_pseudonorm (t : ℝ) : normSq (⟨1 / 2, t⟩ : SplitComplex) = 1 / 4 - t ^ 2 := by
  simp [normSq]
  ring

/-- 阈值 (类时侧): |t| < 1/2 ⟹ 伪范数为正 (半径 1 圆区域)。 -/
theorem threshold_timelike {t : ℝ} (ht : t ^ 2 < 1 / 4) :
    normSq (⟨1 / 2, t⟩ : SplitComplex) > 0 := by
  rw [critical_line_pseudonorm]
  nlinarith

/-- 阈值 (类空侧): |t| > 1/2 ⟹ 伪范数为负 (半径 i 圆区域)。 -/
theorem threshold_spacelike {t : ℝ} (ht : 1 / 2 < t) :
    normSq (⟨1 / 2, t⟩ : SplitComplex) < 0 := by
  rw [critical_line_pseudonorm]
  nlinarith

/-- 零点观测: 临界线零点 (实部 1/2, |虚部| > 1/2) 的分裂伪范数为负 (类空)。
    已知零点 |t| ≥ 14.13 > 1/2 — 阈值 1/2 由分裂结构本身给出。 -/
theorem zero_observation_spacelike {t : ℝ} (ht : 1 / 2 < |t|) :
    normSq (⟨1 / 2, t⟩ : SplitComplex) < 0 := by
  rw [critical_line_pseudonorm]
  have ht2 : (1 / 2) ^ 2 < t ^ 2 := by
    rcases le_or_gt t 0 with htle | htgt
    · have habs : |t| = -t := abs_of_nonpos htle
      rw [habs] at ht
      nlinarith
    · have habs : |t| = t := abs_of_pos htgt
      rw [habs] at ht
      nlinarith
  nlinarith

/-- recip 临界线 ⟹ 双曲线 (a-1)² - b² = 1 (分裂版本的临界圆)。
    对偶: ℂ 中 recip(临界线) = 圆 (a-1)² + b² = 1 (C019-C022 已证);
    分裂中 = 双曲线 — 同一 recip 映射, 两个宿主。 -/
theorem recip_critical_line_hyperbola (t : ℝ) (ht : 1 / 4 - t ^ 2 ≠ 0) :
    let w : SplitComplex := (⟨1 / 2, t⟩ : SplitComplex)⁻¹
    (w.re - 1) ^ 2 - w.im ^ 2 = 1 := by
  let d : ℝ := 1 / 4 - t ^ 2
  have hd : d ≠ 0 := ht
  rw [show (⟨1 / 2, t⟩ : SplitComplex)⁻¹ = ⟨(1 / 2) / d, -t / d⟩ by
    ext <;> simp [normSq, d] <;> ring]
  simp
  field_simp [hd]
  dsimp [d]
  ring

end SplitComplex

end
end SplitComplexCritLine
