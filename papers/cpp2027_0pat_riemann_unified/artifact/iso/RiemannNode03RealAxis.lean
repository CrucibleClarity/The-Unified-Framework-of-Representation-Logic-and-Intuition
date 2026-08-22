/-
Copyright (c) 2026 Yuchen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuchen Wang
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# 节点 03: 假实轴 (Node 03: The False Real Axis) — 双路径

## 本节点: 实轴的相位结构 — 实值 = 反射不动

同一结论的双路径:
- **[对称侧]** (态③): 实轴 = 反射不动点集 — 共轭 (实轴反射) 固定
  的点恰是实轴; 实值函数在实轴上与共轭反射一致。
- **[分析侧]** (态①②): 投影判定 — 虚部为零 ⟺ 共轭固定; 实值的
  相位平凡 (arg 退化为 0 或 π)。

背景 (37 假实轴框架): ζ 在实轴上实值 (zeta_im_zero_on_real) — 实轴
是"相位退化轴" (无连续相位) — 本节点建立相位判定的双路径基础。

两段各自独立, 只 import Mathlib。

English: Node 03 — the phase structure of the real axis: real values
are reflection-fixed. Symmetry side: the real axis is the fixed set
of conjugation (reflection). Analysis side: im = 0 iff conjugation-
fixed; real values have trivial phase.
-/
set_option linter.style.longLine false

noncomputable section

open scoped ComplexConjugate
open Complex

namespace RiemannDualPath

/-! ============================================================
    [对称侧] (态③) — 反射不动点
    ============================================================ -/

/-- **实轴 = 共轭不动点集 (对称侧)**: z ∈ ℝ ⟺ conj z = z — 实轴
    是实轴反射 (共轭) 的不动点集: 反射不动的点恰是实值点。
    ★The real axis is the fixed set of conjugation: z real iff
    conj z = z (symmetry side: reflection fixed points). -/
theorem real_iff_conj_fixed (z : ℂ) : z ∈ Set.range (fun r : ℝ => (r : ℂ)) ↔ conj z = z := by
  constructor
  · rintro ⟨r, rfl⟩
    simp
  · intro h
    rcases (Complex.conj_eq_iff_real.mp h) with ⟨r, hr⟩
    exact ⟨r, hr.symm⟩

/-- **实值函数与反射一致 (对称侧)**: f 实值 ⟹ f x 关于共轭反射不变 —
    实值函数沿实轴的行为 = 反射对称 (假实轴框架: ζ 在实轴实值 ⟹
    共轭对称)。态③: 反射结构直接给出。
    ★A real-valued function agrees with reflection: f real-valued
    ⟹ conj (f x) = f x (symmetry side). -/
theorem real_valued_reflection_fixed (f : ℝ → ℝ) (x : ℝ) :
    conj ((f x : ℝ) : ℂ) = (f x : ℂ) := by
  simp

/-! ============================================================
    [分析侧] (态①②) — 投影判定
    ============================================================ -/

/-- **虚部零 ⟺ 共轭固定 (分析侧)**: z.im = 0 ⟺ conj z = z — 投影
    判定: 虚部 (相位泄漏分量) 为零 ⟺ 反射不变 — 态①: 实值 = 相位
    平凡的投影判据。
    ★Imaginary part zero iff conjugation-fixed: z.im = 0 ⟺ conj z = z
    (analysis side: projection judgment). -/
theorem im_zero_iff_conj_fixed (z : ℂ) : z.im = 0 ↔ conj z = z :=
  Complex.conj_eq_iff_im.symm

/-- **实值分解 (分析侧)**: z = (z + conj z)/2 + (z - conj z)/2 — 实部
    与虚部 (虚轴泄漏) 的分解: 实部 = 反射平均 (共轭固定), 虚部 =
    反射差半 (共轭反号) — 态②: 与反射并存的分解恒等式。
    ★Real/imaginary decomposition: z = re part + im part — the
    reflection average is real, the half-difference is imaginary
    (analysis side, state ②). -/
theorem real_imag_decomposition (z : ℂ) :
    z = (z + conj z) / 2 + (z - conj z) / 2 := by
  ring

end RiemannDualPath
