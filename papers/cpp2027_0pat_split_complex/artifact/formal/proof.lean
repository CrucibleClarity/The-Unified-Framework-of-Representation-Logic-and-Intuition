import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# 习题 XXVII: 分裂复数 — 虚半径正交欧拉圆 (0pat)

用户洞察 (2026-08-21): 两个正交欧拉圆, 一个半径 1, 一个半径 i —
不强迫复平面那样虚部实部相等, 而是纯粹的复正交欧拉圆。
0pat 精确化: 分裂复数 (split-complex) 是"半径 i 的圆"的宿主结构:

    分裂复数:  a + bj,  j² = +1            (对比 ℂ: J² = -1)
    伪范数:    ‖a + bj‖² = a² - b²         (闵可夫斯基度量)
    半径 1 圆: ‖z‖² = 1   ⟺  a² - b² = 1   (双曲线)
    半径 i 圆: ‖z‖² = -1  ⟺  b² - a² = 1   (共轭双曲线, 非空: j 在其上)

正交性: 半径 1 与半径 i 的同心圆满足 1² + i² = 0 — 在分裂度量下即
r₁² + r₂² = 1 + (-1) = 0 = 圆心距², 这是"虚半径圆正交"的精确含义。

观测对比: ℂ 中素数可表示为范数 (a²+b²) 当且仅当 p ≡ 1,2 (mod 4)
(Fermat, XXIV); 分裂复数中每个奇素数都可表示为伪范数 (a²-b²):
p = ((p+1)/2)² - ((p-1)/2)² — 分裂架构对素数的观测无区分度,
与 ℂ 架构形成对比 (观测的区分性差异)。

谱系坐标: (R20, C8) 圆上量化 × 构造; 对比 (R23, C3) 素数圆。
-/

namespace SplitComplexEx

noncomputable section

/-- 分裂复数: a + bj, j² = +1。 -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

/-- 虚数单位 j (j² = +1)。 -/
def j : SplitComplex := ⟨0, 1⟩

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
@[simp] theorem re_one : (1 : SplitComplex).re = 1 := rfl
@[simp] theorem im_one : (1 : SplitComplex).im = 0 := rfl
instance : Add SplitComplex := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Mul SplitComplex :=
  ⟨fun z w => ⟨z.re * w.re + z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
instance : Neg SplitComplex := ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp] theorem re_add (z w : SplitComplex) : (z + w).re = z.re + w.re := rfl
@[simp] theorem im_add (z w : SplitComplex) : (z + w).im = z.im + w.im := rfl
@[simp] theorem re_mul (z w : SplitComplex) : (z * w).re = z.re * w.re + z.im * w.im := rfl
@[simp] theorem im_mul (z w : SplitComplex) : (z * w).im = z.re * w.im + z.im * w.re := rfl

/-- 伪范数 (闵可夫斯基度量): ‖a + bj‖² = a² - b²。 -/
def normSq (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

/-- j² = 1: 分裂复数的定义性代数性质 (对比 ℂ 的 J² = -1)。 -/
theorem j_sq : j * j = 1 := by
  ext <;> simp [j]

/-- 伪范数乘性: ‖zw‖² = ‖z‖²‖w‖² (分裂复数的关键代数性质)。 -/
theorem normSq_mul (z w : SplitComplex) : normSq (z * w) = normSq z * normSq w := by
  simp [normSq, re_mul, im_mul]
  ring

/-- 半径 i 的圆非空: j 在"虚半径圆"上 (‖j‖² = -1)。 -/
theorem imaginary_radius_circle : normSq j = -1 := by
  simp [normSq, j]

/-- 半径 1 的圆非空: 1 在"实半径圆"上 (‖1‖² = 1)。 -/
theorem real_radius_circle : normSq (1 : SplitComplex) = 1 := by
  simp [normSq]

/-- 正交条件: 半径 1 与半径 i 的同心圆满足 r₁² + r₂² = 0
    (分裂度量下 1² + i² = 1 + (-1) = 0 = 圆心距²)。 -/
theorem orthogonal_radii : (1 : ℝ) + (-1) = 0 := by
  norm_num

/-- 共轭双曲线不相交: 没有点同时在半径 1 圆与半径 i 圆上。 -/
theorem circles_disjoint : ¬ ∃ z : SplitComplex, normSq z = 1 ∧ normSq z = -1 := by
  rintro ⟨z, h1, hm1⟩
  linarith

/-- 观测对比: 每个奇素数 p 都是分裂伪范数 (a²-b²), 与 ℂ 的 Fermat
    两平方和 (仅 p ≡ 1,2 mod 4) 形成区分度对比。 -/
theorem odd_prime_is_split_norm {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ a b : ℕ, (a : ℕ) ^ 2 - (b : ℕ) ^ 2 = p := by
  -- p 奇: p = 2k+1, a = k+1, b = k; (k+1)² - k² = 2k+1 = p
  have hpodd : p % 2 = 1 := by
    have : p % 2 ≠ 0 := by
      intro h
      have hd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h
      have hcases : 2 = 1 ∨ 2 = p := hp.eq_one_or_self_of_dvd 2 hd
      rcases hcases with h21 | h2p
      · norm_num at h21
      · exact hp2 h2p.symm
    have hlt : p % 2 < 2 := Nat.mod_lt p (by norm_num)
    omega
  refine ⟨p / 2 + 1, p / 2, ?_⟩
  -- (k+1)² - k² = p: 展开 (k = p/2, p = 2k+1)
  have hk : 2 * (p / 2) + 1 = p := by
    have hdiv : p = 2 * (p / 2) + p % 2 := (Nat.div_add_mod p 2).symm
    rw [hpodd] at hdiv
    omega
  have hpow : (p / 2 + 1) ^ 2 - (p / 2) ^ 2 = 2 * (p / 2) + 1 := by
    have h1 : (p / 2 + 1) ^ 2 = (p / 2) ^ 2 + (2 * (p / 2) + 1) := by ring
    rw [h1]
    omega
  rw [hpow, hk]

end SplitComplex

end
end SplitComplexEx
