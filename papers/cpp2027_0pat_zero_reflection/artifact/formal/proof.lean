import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# 习题 XXVI: 零点反射对称性 — 中间桥面的第一块分析材料 (0pat)

黎曼方向缺口的精确定位: 左岸 (Re ≥ 1 欧拉乘积/无零区) 与右岸 (临界线⟺圆几何)
之间的"中间桥面" = 临界带 0 < Re(s) < 1 内 ζ 的零点位置控制, 需要分析学工具。
mathlib 提供经典函数方程 riemannZeta_one_sub:

    ζ(1-s) = 2 (2π)^(-s) Γ(s) cos(πs/2) ζ(s)   (s ≠ -n, s ≠ 1)

本习题是函数方程的第一个推论 — 第一个真正使用分析的定理:
- 零点反射对称性: ζ(s) = 0 ⟹ ζ(1-s) = 0 (零点关于临界线 Re = 1/2 对称)
- 反射保持临界带: 带内零点反射后仍在带内
- 离线配对: 若零点离线 (Re s ≠ 1/2), 则 1-s 是另一个不同的带内零点
  (离线零点成对出现 — 函数方程给的第一条离线结构约束)

谱系坐标: (R23, C3) 解析数论; 中间桥面材料 #1。
-/

namespace ZetaZeroReflection

noncomputable section

open scoped BigOperators

/-- 零点反射对称性: ζ(s)=0 (非平凡点, 非极点) ⟹ ζ(1-s)=0。
    函数方程 riemannZeta_one_sub 的直接推论 — 零点关于临界线 Re=1/2 对称。 -/
theorem zeta_zero_reflection {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ∀ n : ℕ, s ≠ -n) (hone : s ≠ 1) : riemannZeta (1 - s) = 0 := by
  rw [riemannZeta_one_sub htriv hone, hz]
  ring

/-- 反射保持临界带: 带内零点 (0 < Re s < 1) 的反射 1-s 仍在带内。 -/
theorem zeta_zero_strip_reflection {s : ℂ} (hz : riemannZeta s = 0)
    (hstrip : 0 < s.re ∧ s.re < 1)
    (htriv : ∀ n : ℕ, s ≠ -n) (hone : s ≠ 1) :
    riemannZeta (1 - s) = 0 ∧ 0 < (1 - s).re ∧ (1 - s).re < 1 := by
  constructor
  · exact zeta_zero_reflection hz htriv hone
  · constructor
    · rw [Complex.sub_re, Complex.one_re]; linarith [hstrip.1, hstrip.2]
    · rw [Complex.sub_re, Complex.one_re]; linarith [hstrip.1, hstrip.2]

/-- 离线配对: 若带内零点 s 离线 (Re s ≠ 1/2), 则 1-s 是另一个不同的带内零点
    (离线零点成对出现 — 函数方程给的第一条离线结构约束)。 -/
theorem zeta_zero_offline_pair {s : ℂ} (hz : riemannZeta s = 0)
    (hstrip : 0 < s.re ∧ s.re < 1)
    (htriv : ∀ n : ℕ, s ≠ -n) (hone : s ≠ 1) (hre : s.re ≠ 1 / 2) :
    1 - s ≠ s ∧ riemannZeta (1 - s) = 0 ∧ 0 < (1 - s).re ∧ (1 - s).re < 1 := by
  constructor
  · -- 1-s ≠ s: 若 1-s = s 则 re s = 1/2, 与 hre 矛盾
    intro h
    apply hre
    have hre' : (1 - s).re = s.re := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re] at hre'
    linarith
  · exact zeta_zero_strip_reflection hz hstrip htriv hone

end
end ZetaZeroReflection
