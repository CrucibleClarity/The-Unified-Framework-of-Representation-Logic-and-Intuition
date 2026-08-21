/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Formal.ZeroRelative.ComplexAxis

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# ZeroRelative/DivergencePeriodSymmetry — divergence and periodicity as the eigenspace decomposition of one symmetry

User-proposed construction (R047, 2026-08-12): "直接用已证理论构造一个对称性,
证明这个对称性实质上就是周期和发散的分解 — 一根轴和它的复数轴, 正交,
二者共享基点, 方向不同"。

The construction reuses C011 (ComplexAxis: a = real-axis lift, b = imaginary
axis J with J² = -1, J⁴ = 1):

* The real axis `lift t = ⟨t, 0⟩` is the DIVERGENCE axis: values grow along
  it, projection `proj` observes it (proj_lift), and -1 has no square root
  there (sqrt_neg_one_not_exists_axis).
* The imaginary axis `J = ⟨0, 1⟩` is the PERIODIC axis: ×J is a 90° rotation
  with period 4 (J_pow_four), the phase circle.
* The symmetry is conjugation `conj (a + bJ) = a - bJ` — reflection across
  the real axis, the "det = -1" partner of rotation (NS3: time reversal is
  an O(n) reflection). Both axes share the basepoint 0 and are orthogonal
  (proj J = 0).

Main theorems:

1. `conj_fixes_lift`: the divergence (real) axis is the fixed-point set of
   the symmetry — S(lift t) = lift t.
2. `conj_reflects_J`: the periodic (imaginary) axis is the reflected
   direction — S(J) = -J.
3. `symmetry_decomposition`: every element decomposes into the S-fixed
   component (divergence part, on the real axis) and the S-reflected
   component (periodic part, along J): z = lift (proj z) + ⟨0, z.b⟩,
   with the first fixed by S and the second negated by S.
4. `orthogonal_axes`: the axes are orthogonal — proj J = 0, and the
   divergence point lift t times the period direction J has zero
   projection (cross-axis product invisible to the divergence axis).
5. `divergence_axis_no_sqrt`: -1 has no square root on the divergence axis
   (sqrt_neg_one_not_exists_axis): the divergence axis alone cannot see the
   periodicity — the period axis is needed (sqrt_neg_one_exists_high).
6. `conj_preserves_norm`: S is an orthogonal symmetry (isometry).

This is the user's construction: divergence and periodicity are not two
separate phenomena but the two eigenspaces of ONE conjugation symmetry
sharing a basepoint with different (orthogonal) directions. RulerPhase
(phase = essence of basepoint) + RulerCycle (symmetry = periodic function of
phase) + NS3 (det = ±1 direction pair) are the claim-level theory; this file
is their Lean instance on the C011 axis pair.
-/

namespace ZeroRelative

namespace ComplexAxis

/-- **发散轴是共轭对称性的不动点集**: 实轴 lift t 被 S = conj 固定 —
发散轴 = S 的特征空间 (特征值 +1)。 -/
theorem conj_fixes_lift (t : ℝ) : conj (lift t) = lift t := by
  ext <;> simp [conj, lift]

/-- **周期轴是共轭对称性的反射方向**: S(J) = -J — 虚轴 J 是 S 的特征空间
(特征值 -1)。周期方向与发散方向共享基点 0, 但方向不同 (一个固定, 一个
取反)。 -/
theorem conj_reflects_J : conj J = -J := by
  change conj J = neg J
  ext <;> simp [conj, J, neg]

/-- **对称性分解**: 任意元素 z 分解为 发散部分 (实轴, S 固定) + 周期部分
(虚轴, S 取反)。z = lift (proj z) + ⟨0, z.b⟩ — 这是 S 的特征空间直和,
"周期与发散的分解" = 一个共轭对称性的特征分解。 -/
theorem symmetry_decomposition (z : ComplexAxis) :
    z = lift (proj z) + ⟨0, z.b⟩ := by
  cases z with
  | mk a b =>
    ext <;> simp [lift, proj, add]

/-- 分解的两部分: 发散部分被 S 固定, 周期部分被 S 取反。 -/
theorem decomposition_fixed_reflected (z : ComplexAxis) :
    conj (lift (proj z)) = lift (proj z) ∧ conj ⟨0, z.b⟩ = -⟨0, z.b⟩ := by
  constructor
  · exact conj_fixes_lift (proj z)
  · change conj ⟨0, z.b⟩ = neg ⟨0, z.b⟩
    ext <;> simp [conj, neg]
/-- **正交**: 两根轴共享基点 0 且方向正交 — 周期方向 J 在发散轴上投影为 0
(proj J = 0), 发散点 lift t 与周期方向 J 的乘积在发散轴上不可观测
(proj (lift t * J) = 0)。 -/
theorem orthogonal_axes (t : ℝ) : proj (lift t * J) = 0 := by
  change (mul (lift t) J).a = 0
  simp [lift, J, mul]

/-- **发散轴自身看不见周期**: -1 在发散轴 (实轴) 上无平方根 — 周期结构
(开方/旋转) 需要周期轴 J 才存在 (sqrt_neg_one_exists_high)。 -/
theorem divergence_axis_no_sqrt : ¬ ∃ t : ℝ, lift (t * t) = -1 := by
  intro h
  rcases h with ⟨t, ht⟩
  have hsq : t * t = -1 := by
    have ha : (lift (t * t)).a = (neg one).a := by
      change (lift (t * t)).a = (-1 : ComplexAxis).a
      exact congrArg ComplexAxis.a ht
    change t * t = (-1 : ℝ)
    simpa [lift, neg, one] using ha
  nlinarith [sq_nonneg t]

/-- **S 是正交对称性 (等距)**: conj 保持范数 — 反射 det = -1 型对称
(NS3: 时间反演是 O(n) 反射)。 -/
theorem conj_preserves_norm (z : ComplexAxis) : norm (conj z) = norm z := by
  cases z with
  | mk a b => simp [conj, norm]

end ComplexAxis

end ZeroRelative
