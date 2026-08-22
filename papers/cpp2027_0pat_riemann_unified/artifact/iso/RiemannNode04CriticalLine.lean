/-
Copyright (c) 2026 Yuchen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuchen Wang
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# 节点 04: 临界线相位 (Node 04: The Critical-Line Phase) — 双路径

## 本节点: 临界线 Re z = 1/2 的相位刻画

同一结论的双路径:
- **[对称侧]** (态③): 垂直平分线 (等距) — 临界线 = i 与 1+i 的垂直
  平分线 (‖z-i‖ = ‖z-(1+i)‖); 位置形式 1-z = conj z (1/2 的双重
  对称性: 反射与共轭在临界线上重合)。
- **[分析侧]** (态①②): 反演圆判据 (模计算) — 临界线经 1/z 反演 =
  单位圆 (‖1/z - 1‖ = 1); T 坐标 (基点 i): ‖1/(z-i) - 1‖ = 1 —
  模方程直接判定在线。

背景 (37): 临界线 = 相位基点 (各项模齐轴 + 函数方程对称轴);
χ 在临界线单位模 (|χ(1/2+it)| = 1) — 本节点建立在线判定的双路径。

两段各自独立, 只 import Mathlib。

English: Node 04 — phase characterizations of the critical line.
Symmetry side: the perpendicular bisector (equidistance to i and
1+i); the position form 1-z = conj z. Analysis side: the inversion
circle criterion ‖1/z - 1‖ = 1 and the T-coordinate ‖1/(z-i) - 1‖ = 1.
-/
set_option linter.style.longLine false

noncomputable section

open Complex
open scoped ComplexConjugate

namespace RiemannDualPath

/-! ============================================================
    [对称侧] (态③) — 垂直平分线与位置形式
    ============================================================ -/

/-- **临界线 = 垂直平分线 (对称侧)**: Re z = 1/2 ⟺ ‖z-i‖ = ‖z-(1+i)‖ —
    临界线是 i 与 1+i 的垂直平分线: 到两点等距 — 等距 (垂直) 的
    几何结构 (基点 i 观测)。
    ★The critical line is the perpendicular bisector: Re z = 1/2 iff
    z is equidistant from i and 1+i (symmetry side). -/
theorem critical_line_equidistant_basepoint_i (z : ℂ) :
    z.re = 1 / 2 ↔ ‖z - Complex.I‖ = ‖z - (1 + Complex.I)‖ := by
  constructor
  · intro hre
    have hsq : ‖z - Complex.I‖ ^ 2 = ‖z - (1 + Complex.I)‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply]
      rw [hre]
      ring
    have habs : |‖z - Complex.I‖| = |‖z - (1 + Complex.I)‖| :=
      (sq_eq_sq_iff_abs_eq_abs ‖z - Complex.I‖ ‖z - (1 + Complex.I)‖).mp hsq
    simpa [abs_of_nonneg (norm_nonneg _)] using habs
  · intro h
    have hsq : ‖z - Complex.I‖ ^ 2 = ‖z - (1 + Complex.I)‖ ^ 2 := by rw [h]
    have hns : Complex.normSq (z - Complex.I) = Complex.normSq (z - (1 + Complex.I)) := by
      simpa [Complex.normSq_eq_norm_sq] using hsq
    rw [Complex.normSq_apply, Complex.normSq_apply] at hns
    simp at hns
    nlinarith

/-- **临界线位置形式 (对称侧)**: Re z = 1/2 ⟺ 1-z = conj z — 1/2 的
    双重对称性: 反射 (1-z) 与共轭 (conj z) 在临界线上重合 — 轨道
    退化 (在线零点 2 点轨道) 的位置判据。
    ★Position form: Re z = 1/2 iff 1-z = conj z — reflection and
    conjugation coincide on the critical line (symmetry side). -/
theorem critical_line_iff_one_sub_conj (z : ℂ) : z.re = 1 / 2 ↔ 1 - z = conj z := by
  constructor
  · intro h
    apply Complex.ext
    · simp [h, Complex.sub_re, Complex.ofReal_re]
      norm_num
    · simp [Complex.sub_im, Complex.ofReal_im]
  · intro h
    have hre : (1 - z).re = (conj z).re := congrArg Complex.re h
    simp [Complex.sub_re, Complex.ofReal_re] at hre
    linarith

/-! ============================================================
    [分析侧] (态①②) — 反演圆判据 (模计算)
    ============================================================ -/

/-- **反演圆判据 (分析侧)**: Re z = 1/2 ⟺ ‖1/z - 1‖ = 1 (z ≠ 0) —
    临界线经 1/z 反演 = 单位圆: 在线 ⟺ 反演像在圆上 — 模方程直接
    判定 (recip_on_critical_circle_iff; 37 观测 AA 反演圆判据 6/6)。
    ★Inversion-circle criterion: Re z = 1/2 iff ‖1/z - 1‖ = 1 — the
    critical line maps to the unit circle under 1/z (analysis side). -/
theorem critical_line_iff_recip_circle (z : ℂ) (hz : z ≠ 0) :
    z.re = 1 / 2 ↔ ‖1 / z - 1‖ = 1 := by
  -- 反演圆判据 (37 recip_on_critical_circle_iff 同证明, 方向反转)
  have hnorm (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    calc
      ‖w‖ ^ 2 = Complex.normSq w := (Complex.normSq_eq_norm_sq w).symm
      _ = w.re ^ 2 + w.im ^ 2 := by
        simp [Complex.normSq_apply]
        ring
  have hz1 : (1 / z : ℂ) - 1 = (1 - z) / z := by
    field_simp [hz]
  have hne_z : ‖z‖ ≠ 0 := by exact norm_ne_zero_iff.mpr hz
  constructor
  · intro hσ
    have hsq' : (1 - z.re) ^ 2 + (-z.im) ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [hσ]
      ring
    have hsq : ‖1 - z‖ ^ 2 = ‖z‖ ^ 2 := by
      simpa [Complex.sub_re, Complex.sub_im, hnorm] using hsq'
    have hnorm_eq : ‖1 - z‖ = ‖z‖ := by
      rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h1 | h1
      · exact h1
      · exfalso
        have hz0 : ‖z‖ = 0 := by
          linarith [norm_nonneg (1 - z), norm_nonneg z, h1]
        exact hne_z hz0
    calc
      ‖1 / z - 1‖ = ‖(1 - z) / z‖ := by rw [hz1]
      _ = ‖1 - z‖ / ‖z‖ := by rw [norm_div]
      _ = 1 := by
        rw [hnorm_eq]
        field_simp [hne_z]
  · intro h
    have hdiv : ‖(1 - z) / z‖ = 1 := by
      rw [← hz1]
      exact h
    have hnorm_eq : ‖1 - z‖ = ‖z‖ := by
      rw [norm_div] at hdiv
      exact (div_eq_one_iff_eq hne_z).mp hdiv
    have hsq : ‖1 - z‖ ^ 2 = ‖z‖ ^ 2 := by rw [hnorm_eq]
    have hsq' : (1 - z.re) ^ 2 + (-z.im) ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      simpa [Complex.sub_re, Complex.sub_im, hnorm] using hsq
    have hσ : z.re = 1 / 2 := by
      nlinarith
    exact hσ

theorem critical_line_iff_T_unit_circle (z : ℂ) (hz : z ≠ Complex.I) :
    z.re = 1 / 2 ↔ ‖1 / (z - Complex.I) - 1‖ = 1 := by
  have hrewrite : 1 / (z - Complex.I) - 1 = -((z - (1 + Complex.I)) / (z - Complex.I)) := by
    field_simp [sub_ne_zero.mpr hz]
    ring
  have hne : ‖z - Complex.I‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)
  rw [hrewrite, norm_neg, Complex.norm_div, div_eq_one_iff_eq hne]
  simpa [eq_comm] using (critical_line_equidistant_basepoint_i z)

end RiemannDualPath
