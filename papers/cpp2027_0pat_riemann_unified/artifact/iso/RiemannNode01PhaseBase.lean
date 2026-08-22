/-
Copyright (c) 2026 Yuchen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuchen Wang
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Ring

/-!
# 节点 01: 相位基础 (Node 01: Phase Base) — 对称侧 + 分析侧双路径

黎曼方向双路径重做 — 每个节点配备对称侧 (态③: 显式利用相位模糊)
与分析侧 (态①②: 消去/并存相位模糊) 两条独立路径, 各自逻辑连贯,
零交叉引用, 只 import Mathlib。

## 本节点: 相位基础

相位模糊 = 2πiℤ 歧义 (同一点 e^{iθ} 携带代表 θ + 2πn)。
- **[对称侧]** (态③): 整圈 = 1 (桥1) / exp 核 2πiℤ (桥2) / 反射对消 /
  单位圆闭合 (桥3) — 相位模糊的对称结构直接操作。
- **[分析侧]** (态①②): 模消相位 (绝对收敛) / 相位对消 = 模平方 /
  实值判定 (共轭固定) / 模乘法性 / exp 无零点 — 相位模糊的消去与并存。

两段各自独立: 对称侧只依赖反射/周期/圆结构, 分析侧只依赖模/共轭/级数。

## 用户指示 (原话, 非转述)

2026-08-22: "我希望能够做成隔离的lean，然后黎曼方向的每个节点，都必须
配备对称侧和分析侧两个路径，能做到吗？...我感觉后者好一点，对称侧、
分析侧各自逻辑连贯。" + "开始吧。"

English: Node 01 of the dual-path Riemann direction: the phase base.
Symmetry side (state ③): full turn = 1, exp kernel 2πiℤ, reflection
cancellation, unit-circle closure. Analysis side (state ①②): modulus
eliminates phase, self-conjugate product = squared modulus, real-valued
judgment, modulus multiplicativity, exp has no zeros. Both sides are
self-contained, mutually independent, Mathlib-only.
-/
set_option linter.style.longLine false

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex Filter
open scoped Topology

namespace RiemannDualPath

/-! ============================================================
    [对称侧] (态③) — 相位模糊的对称结构
    ============================================================ -/

/-- **整圈 = 1 (桥1)**: exp (2πi) = 1 — 绕单位圆一整圈回到原点,
    相位 + 2π 复原 — 圈数的对称结构 (自然数 = 圈数的起点)。
    ★Full turn is one: exp (2πi) = 1 — one full turn around the unit
    circle returns to the start (Bridge 1). -/
theorem two_pi_turn_is_one : Complex.exp (2 * ↑Real.pi * Complex.I) = 1 :=
  Complex.exp_two_pi_mul_I

/-- **相位模糊结构 (桥2)**: exp z = exp w ⟺ ∃ n : ℤ, z = w + 2πi·n —
    同一点的相位代表差 2π 整数倍 — 相位模糊 = 2πiℤ 核的精确形式。
    ★Phase ambiguity structure: exp z = exp w iff z = w + 2πi·n —
    the kernel 2πiℤ (Bridge 2). -/
theorem phase_equiv_iff_two_pi_int (z w : ℂ) :
    Complex.exp z = Complex.exp w ↔
      ∃ n : ℤ, z = w + (n : ℂ) * (2 * ↑Real.pi * Complex.I) :=
  Complex.exp_eq_exp_iff_exists_int

/-- **反射对消 (基点 e)**: x + (2e-x) = 2e — 关于基点 e 的反射对消:
    相位取反 (θ → 2θ₀-θ) 的对称对消 — 残差只依赖基点。
    ★Reflection cancellation about e: x + (2e-x) = 2e — the reflected
    pair cancels, leaving only the basepoint. -/
theorem reflection_cancel_at_basepoint (x e : ℂ) : x + (2 * e - x) = 2 * e := by
  ring

/-- **单位圆乘法闭合 (桥3)**: ‖z‖=1 → ‖w‖=1 → ‖z·w‖=1 — 单位圆上
    相位叠加仍在圆上 (模恒 1, 只有相位变)。
    ★Unit-circle closure: ‖z‖=1 → ‖w‖=1 → ‖z·w‖=1 — phase superposition
    stays on the circle (Bridge 3). -/
theorem unit_mul_closed (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) : ‖z * w‖ = 1 := by
  rw [Complex.norm_mul, hz, hw]
  norm_num

/-! ============================================================
    [分析侧] (态①②) — 相位模糊的消去与并存
    ============================================================ -/

/-- **模消相位 (态①)**: Summable ‖a‖ ⟹ Summable a — 模 = 相位无关量,
    绝对收敛 = 相位模糊被模消去后的收敛判定。
    ★Modulus eliminates phase: absolute summability implies summability
    (state ①). -/
theorem abs_summable_implies_summable {ι : Type*} {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {a : ι → E} (h : Summable fun i => ‖a i‖) : Summable a :=
  Summable.of_norm h

/-- **相位对消 = 模平方 (态①)**: z · conj z = ‖z‖² — 乘共轭 (反射) 把
    相位消干净 (θ + (-θ) = 0), 剩模平方 — 一阶对消二阶保留的分析侧。
    ★Phase cancellation = squared modulus: z·conj z = ‖z‖² (state ①). -/
theorem conj_mul_self_normSq (z : ℂ) : z * conj z = (‖z‖ ^ 2 : ℂ) := by
  rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
  have hns : (Complex.normSq z : ℂ) = (‖z‖ ^ 2 : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    norm_num
  exact hns

/-- **实值判定 (态①)**: conj z = z ⟺ ∃ r : ℝ, z = r — 实值 = 相位退化
    (0 或 π, 无连续相位) — 相位平凡处代数方法可行。
    ★Real-valued judgment: conj z = z iff z is real — phase is trivial
    (state ①). -/
theorem conj_fixed_iff_real (z : ℂ) : conj z = z ↔ ∃ r : ℝ, z = r :=
  Complex.conj_eq_iff_real

/-- **模乘法性 (态①)**: ‖z·w‖ = ‖z‖·‖w‖ — 相位叠加 (θ_z + θ_w) 下模
    独立: 模操作与相位解耦。
    ★Modulus multiplicativity: ‖z·w‖ = ‖z‖·‖w‖ — the modulus decouples
    from phase (state ①). -/
theorem norm_mul_eq (z w : ℂ) : ‖z * w‖ = ‖z‖ * ‖w‖ :=
  Complex.norm_mul z w

/-- **exp 无零点 (态①)**: exp z ≠ 0 — 模 = e^{re z} > 0 恒成立 ⟹ 相位
    (arg) 处处有定义 — 单位圆上无零点。
    ★exp never vanishes: exp z ≠ 0 — the modulus is always positive, so
    the phase is defined everywhere (state ①). -/
theorem exp_ne_zero_all (z : ℂ) : Complex.exp z ≠ 0 :=
  Complex.exp_ne_zero z

end RiemannDualPath
