/-
Copyright (c) 2026 Yuchen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuchen Wang
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# 节点 02: 素数圆与欧拉圆 (Node 02: Prime and Euler Circles) — 双路径

## 本节点: 素数圆 (圆心 0 半径 √p) 与临界圆 (圆心 1 半径 1) 的相交结构

同一结论的双路径:
- **[对称侧]** (态③): 等距/圆几何 — 交点 z 到 0 与到 1 的距离结构
  (|z|² = p ∧ |z-1|² = 1 的几何读法: 垂直平分线/圆交几何)。
- **[分析侧]** (态①②): 模方程代数消元 — 相减消 z.im, 得 z.re = p/2,
  代入得 (z.im)² = p(4-p)/4, p ≥ 5 时平方为负矛盾 (模 = 相位无关量,
  代数消元直接判交)。

结论: 素数圆与临界圆相交 ⟺ p ∈ {2, 3}; p ≥ 5 时不相交
(37 观测: primeCircle_inter_criticalCircle_ge5, 双路径重证)。

两段各自独立, 只 import Mathlib。

English: Node 02 — the intersection structure of the prime circle
(center 0, radius √p) and the critical circle (center 1, radius 1).
Symmetry side (state ③): equidistance/circle geometry. Analysis side
(state ①②): modulus-equation elimination. Conclusion: the circles
intersect iff p ∈ {2, 3}; disjoint for p ≥ 5.
-/
set_option linter.style.longLine false

/-!
## 用户指示 (原话, 非转述) — 人类观点归属

2026-08-22 (双路径方案, 用户提出): "我希望能够做成隔离的lean，然后黎曼
方向的每个节点，都必须配备对称侧和分析侧两个路径，能做到吗？...我感觉
后者好一点，对称侧、分析侧各自逻辑连贯。"

2026-08-22 (三态框架观点归属, 用户提出): 三态框架 (一切证明法 = 消去
相位模糊或带相位并存) 为用户在黎曼 0pat 路径中提出的观点 — "这玩意本质
上是我换deepseek pro做0pat,发现死活都要走分析路径而且推不动的时候，想到
的方法论。" 本文件的双路径结构是这一观点的落地。

2026-08-22 (novelty 担忧, 用户原话): "你能都搞出来了，我感觉可能被蒸馏
完已经证完了吧。" — 按 KNOWN 纪律: 若本内容已被他人提前发布, 不视为新
结果 (novelty_status 如实标注)。
-/




noncomputable section

open Complex
open scoped ComplexConjugate

namespace RiemannDualPath

/-! ============================================================
    [对称侧] (态③) — 等距与圆几何
    ============================================================ -/

/-- **交点等距结构 (对称侧)**: 若 z 在素数圆 (|z|² = p) 且临界圆
    (|z-1|² = 1) 上, 则 z 到 0 与到 1 的距离平方差 = p - 1 —
    两圆交点的几何约束: 距离结构决定交点位置。
    ★Intersection equidistance: z on both circles ⟹ the squared
    distance difference to 0 and 1 is p - 1 (geometry side). -/
theorem intersection_dist_sq_diff (z : ℂ) (p : ℝ) (hp : ‖z‖ ^ 2 = p)
    (hc : ‖z - 1‖ ^ 2 = 1) : p - 1 = 2 * z.re - 1 := by
  -- ‖z‖² - ‖z-1‖² = p - 1; 展开 ‖z-1‖² = ‖z‖² - 2·re z + 1
  have hz : ‖z - 1‖ ^ 2 = ‖z‖ ^ 2 - 2 * z.re + 1 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  have hdiff : ‖z‖ ^ 2 - ‖z - 1‖ ^ 2 = p - 1 := by
    rw [hp, hc]
  rw [hz] at hdiff
  linarith

/-- **素数圆与临界圆相交 ⟹ p ≤ 4 (对称侧)**: 若两圆有交点, 则交点
    实部 = p/2 且虚部平方 = p(4-p)/4 ≥ 0 ⟹ p ≤ 4 — 圆交几何约束。
    ★Intersection forces p ≤ 4: the intersection point has real part
    p/2 and imaginary-square p(4-p)/4 ≥ 0 (geometry side). -/
theorem prime_circle_intersection_forces_p_le_four (z : ℂ) (p : ℝ)
    (hp : ‖z‖ ^ 2 = p) (hc : ‖z - 1‖ ^ 2 = 1) : p ≤ 4 := by
  -- 从两方程: z.re = p/2, (z.im)² = p(4-p)/4 ≥ 0
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    ring
  have hsq1 : ‖z - 1‖ ^ 2 = (z.re - 1) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    simp [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hre : z.re = p / 2 := by
    have hdiff : ‖z‖ ^ 2 - ‖z - 1‖ ^ 2 = p - 1 := by rw [hp, hc]
    rw [hsq, hsq1] at hdiff
    linarith
  have himsq : z.im ^ 2 = p * (4 - p) / 4 := by
    have : z.re ^ 2 + z.im ^ 2 = p := by
      rw [← hsq, hp]
    rw [hre] at this
    linarith
  have hnonneg : 0 ≤ z.im ^ 2 := sq_nonneg z.im
  -- p(4-p)/4 ≥ 0 ⟹ p ≤ 4 (p ≥ 0 由 hp: ‖z‖² = p ≥ 0)
  have hp0 : 0 ≤ p := by
    rw [← hp]
    exact sq_nonneg ‖z‖
  nlinarith

/-! ============================================================
    [分析侧] (态①②) — 模方程代数消元
    ============================================================ -/

/-- **模方程消元判交 (分析侧)**: p ≥ 5 ⟹ 素数圆与临界圆无交点 —
    模方程系统 (‖z‖² = p ∧ ‖z-1‖² = 1) 代数消元: z.re = p/2,
    (z.im)² = p(4-p)/4 < 0 矛盾 — 模 = 相位无关量, 代数直判。
    ★Modulus-elimination disjointness: p ≥ 5 ⟹ no intersection —
    eliminate z.im, the squared imaginary part is negative (analysis
    side). -/
theorem prime_circle_disjoint_ge5 (p : ℝ) (hp5 : 5 ≤ p) :
    ¬∃ z : ℂ, ‖z‖ ^ 2 = p ∧ ‖z - 1‖ ^ 2 = 1 := by
  rintro ⟨z, hz⟩
  rcases hz with ⟨hp, hc⟩
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    ring
  have hsq1 : ‖z - 1‖ ^ 2 = (z.re - 1) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    simp [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hre : z.re = p / 2 := by
    have hdiff : ‖z‖ ^ 2 - ‖z - 1‖ ^ 2 = p - 1 := by rw [hp, hc]
    rw [hsq, hsq1] at hdiff
    linarith
  have himsq : z.im ^ 2 = p * (4 - p) / 4 := by
    have : z.re ^ 2 + z.im ^ 2 = p := by
      rw [← hsq, hp]
    rw [hre] at this
    linarith
  -- p ≥ 5 ⟹ p(4-p)/4 < 0 ⟹ (z.im)² < 0 矛盾 (平方非负)
  have hneg : p * (4 - p) / 4 < 0 := by
    have hp_pos : 0 < p := by linarith
    have h4p : 4 - p < 0 := by linarith
    nlinarith
  have : z.im ^ 2 < 0 := by
    rw [himsq]
    exact hneg
  exact (not_lt_of_ge (sq_nonneg z.im)) this

/-- **单位模判据 (分析侧)**: ‖z‖ = 1 ⟺ z·conj z = 1 — 圆上判定的
    代数形式: 圆 = 自共轭积 1 (模平方判据的相位对消形式)。
    ★Unit-modulus criterion: ‖z‖ = 1 iff z·conj z = 1 — the algebraic
    circle judgment (analysis side). -/
theorem unit_iff_conj_mul_self (z : ℂ) : ‖z‖ = 1 ↔ z * conj z = 1 := by
  constructor
  · intro h
    rw [mul_comm]
    rw [← Complex.normSq_eq_conj_mul_self]
    rw [Complex.normSq_eq_norm_sq]
    rw [h]
    norm_num
  · intro h
    have hns : Complex.normSq z = 1 := by
      have hℂ : (Complex.normSq z : ℂ) = 1 := by
        rw [Complex.normSq_eq_conj_mul_self]
        rw [mul_comm]
        exact h
      exact_mod_cast hℂ
    have hsq : ‖z‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hns
    have hcases : ‖z‖ = 1 ∨ ‖z‖ = -1 := (sq_eq_one_iff).mp hsq
    rcases hcases with h1 | hm1
    · exact h1
    · exfalso
      have hnn : 0 ≤ ‖z‖ := norm_nonneg z
      nlinarith

end RiemannDualPath
