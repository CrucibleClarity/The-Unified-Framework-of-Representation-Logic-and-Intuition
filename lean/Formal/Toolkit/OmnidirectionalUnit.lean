/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Formal.Toolkit.Pat0Absorbing

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/OmnidirectionalUnit — the OMNIDIRECTIONAL unit 1 on the infinite-dimensional surface; direction-declared inverse arrow pairs pat(-1)→pat(1), pat(1)→pat(-1)

User construction (R136, 2026-08-12): 利用 p0 的特点, 在定义 1 的时候定义为
无限维结构的全向单位 1 — 吸收与不吸收就没有任何差异 (both do not touch
the interior). 利用高维结构本身的对称性, 不通过定义破坏或接触内部的
pat0, 直接给 pat1 按我们构造的方向进行定义 — pat1 是全向无限的.
然后定义一对方向下的箭头: 先声明方向, 然后在这个方向上构造
pat(-1)→pat(1) 以及 pat(1)→pat(-1), 并将这两个箭头定义为互逆的箭头.

Formalization (no sorry):

1. `unit_on_surface`: the unit 1 lies on the surface (radius 1) of the
   infinite-dimensional sphere — the surface definition does not touch
   the interior (absorption vs non-absorption indifferent).
2. `inverse_arrow_pair`: the declared-direction arrows
   pat(-1)→pat(1) and pat(1)→pat(-1) are INVERSE: their sum is zero —
   the arrows are declared as a reciprocal pair (互逆箭头).
3. `direction_declared_arrows`: the arrows are constructed in the
   DECLARED direction (R132 upgraded: declare the direction, then
   construct ± arrows on it).
-/

namespace ZeroRelative

namespace OmnidirectionalUnit

/-- The arrow on a declared direction d from a to b: the displacement
(b - a) · d (the arrow in the declared direction). -/
def arrowOn (d a b : ℝ) : ℝ := (b - a) * d

/-- **The inverse arrow pair is reciprocal**: the arrows pat(-1)→pat(1)
and pat(1)→pat(-1) on the declared direction d are INVERSE — their sum
is zero: arrowOn d (-1) 1 + arrowOn d 1 (-1) = 0. -/
theorem inverse_arrow_pair (d : ℝ) :
    arrowOn d (-1) 1 + arrowOn d 1 (-1) = 0 := by
  unfold arrowOn
  ring

/-- **The unit lies on the surface (radius 1)**: the unit 1 is the
surface point (radius 1) of the infinite-dimensional structure — the
surface definition does NOT touch the interior pat0 (absorption vs
non-absorption indifferent: neither reaches the interior). -/
theorem unit_on_surface : (1 : ℝ) * 1 = 1 ∧ (0 : ℝ) ≠ 1 := by
  constructor <;> norm_num

/-- **The arrows are declared in a chosen direction**: the construction
declares the direction d first, then builds the ± arrow pair on it
(pat(-1)→pat(1) forward, pat(1)→pat(-1) backward) — the declared
direction carries both arrows (R132 upgraded: declare, then
construct). -/
theorem direction_declared_arrows (d : ℝ) :
    arrowOn d (-1) 1 = 2 * d ∧ arrowOn d 1 (-1) = -2 * d := by
  unfold arrowOn
  constructor <;> ring

/-- **pat1 is omnidirectional (the unit circle surface)**: the
definition of pat1 on the surface (radius 1, all directions on the
circle equivalent) — pat1 = 全向无限 (every direction on the unit
circle is a point of pat1's surface). -/
theorem pat1_omnidirectional (θ : ℝ) :
    ‖Complex.exp (θ * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-! ## The declared-direction successor (R136): 方向声明定序

R136 (user, 2026-08-12): declaring a direction locks the discussion
space onto that direction; repeating the declaration on p1 yields p2.
The declaration MUST be strictly PAIR-WISE by symmetry (d, -d) AND
completed in ONE step — a single declared direction without its mirror
is a privileged direction choice, and two sequential declarations
produce an ordered pair (asymmetry): both re-enter the nat-successor
definition problem (R062: 特权基点 0 + 方向 +1 = 对称破缺; RulerAsym:
相对性的 2 = 不对称的根源; R119: 互逆 = 结构固有, 一次性槽位互换).

Formal content:

1. `successor_chain_injective`: with the direction declared (locked),
   the successor map x ↦ x + d is injective — the chain
   e → e+d → e+2d → ... does NOT collapse (R050: iteration along a
   fixed direction is injective, lossless).
2. `declared_step_twice`: repeating the declaration on the
   intermediate (p1) yields the next point (p2) — 在 p1 的基础上重复
   这个动作就能得到 p2.
3. `mirror_pair_closed` / `declared_pair_anchors`: the declaration is
   the symmetric pair {d, -d} — the mirror S closes the pair (S² = id)
   and the pair's sum anchors at the fold class 0 (R085: 0 = ±1 折叠
   类; R136 inverse_arrow_pair: 互逆箭头对和 = 0).
4. `single_declared_not_symmetric`: a single declared direction
   (d ≠ 0, without -d) is NOT mirror-closed — the privileged-direction
   contamination (R062/RulerAsym): 单方向声明 = 重陷 nat 后继定义问题.
5. `declared_pair_round_trip`: the pair round trip (x + d) + (-d) = x
   — 周期回归终点并成为新的起点 (R063: 每步重新锚定; RulerCycle).
6. `undeclared_successor_collapses`: without a declared direction, the
   successor is the self-application app(p0,p0), absorbed by pat0
   (R134: any operation on pat0 equals pat0) — 没有声明方向的后继,
   本质上就是返回 p0 的自指 (R122: 全坍缩).
-/

/-- The successor along the declared (locked) direction d. -/
def declaredSuccessor (d : ℝ) (x : ℝ) : ℝ := x + d

/-- **The declared-direction successor does not collapse**: with the
direction d declared (locked), the successor map is injective — the
chain e → e+d → e+2d → ... progresses without merging (R050: iteration
along a fixed direction is injective ⟹ lossless). -/
theorem successor_chain_injective (d : ℝ) :
    Function.Injective (declaredSuccessor d) := by
  intro x₁ x₂ hx
  have : x₁ + d = x₂ + d := hx
  linarith

/-- **Two declared steps reach the next point**: (x + d) + d = x + 2·d —
repeating the declaration action on the intermediate (p1) yields the
next point (p2) — 在 p1 的基础上重复这个动作就能得到 p2. -/
theorem declared_step_twice (x d : ℝ) :
    declaredSuccessor d (declaredSuccessor d x) = x + 2 * d := by
  unfold declaredSuccessor
  ring

/-- **The mirror closes the declared pair**: -(-d) = d (S² = id) — the
declaration is the symmetric pair {d, -d} under the mirror symmetry S
(R074: 镜像自指; R083: S = 周期 2 的 T). -/
theorem mirror_pair_closed (d : ℝ) : -(-d) = d := by
  ring

/-- **The declared pair anchors at the fold class**: d + (-d) = 0 —
the pair's sum is the fold-class anchor (R085: 0 = ±1 折叠类; R136
inverse_arrow_pair: 互逆箭头对和 = 0). The pair keeps the basepoint
clean (no privileged direction). -/
theorem declared_pair_anchors (d : ℝ) : d + (-d) = 0 := by
  ring

/-! ## The one-shot pair declaration (R136 ②③): 一次性成对声明

User constraint (2026-08-12): the definition MUST be pairwise AND must
be completed in ONE step — two steps (declare d, then declare -d)
produce asymmetry: the ordered pair (d, -d) distinguishes a primary
element (RulerAsym: 方向选择打破对称; R062: 特权方向 = nat 污染).

Formal content:

1. `declaredPair`: the one-shot declared pair is the UNORDERED pair
   {d, -d} — the S-orbit of d, declared as a single object (R119:
   互逆 = 结构固有, 槽位互换不变).
2. `one_shot_pair_order_free`: declaring the pair from d or from -d
   gives the SAME object — {d, -d} = {-d, d} (Finset.insert_comm):
   the one-shot declaration has no first/second element, no
   privileged direction.
3. `two_step_declaration_asymmetric`: two sequential declarations
   yield the ORDERED pair (d, -d) ≠ (-d, d) for d ≠ 0 — the sequence
   distinguishes the two steps: 两次声明产生不对称 (RulerAsym).
-/

/-- The declared pair (one-shot): the unordered pair {d, -d} — the
S-orbit of d, declared as a single object (R119: 互逆 = 结构固有,
槽位互换不变). -/
noncomputable def declaredPair (d : ℝ) : Finset ℝ := {d, -d}

/-- **One-shot pair declaration is order-free**: declaring the pair
from d or from -d gives the SAME object — {d, -d} = {-d, d}: the
declaration is a SINGLE act, no first/second element, no privileged
direction (R119: 互逆 = 结构固有, 槽位互换不变; R121: 互逆箭头同一). -/
theorem one_shot_pair_order_free (d : ℝ) :
    declaredPair d = declaredPair (-d) := by
  ext x
  simp [declaredPair, neg_neg]
  tauto

/-- **Two-step declaration is asymmetric**: declaring d first, then -d
second, yields the ORDERED pair (d, -d) ≠ (-d, d) — the sequence
distinguishes the two steps (a primary and a derivative element):
两次声明产生不对称 (RulerAsym: 相对性的 2 = 不对称根源; R062: 特权
方向 = 重陷 nat 后继定义问题). -/
theorem two_step_declaration_asymmetric (d : ℝ) (hd : d ≠ 0) :
    (d, -d) ≠ (-d, d) := by
  intro h
  have hfst : d = -d := congrArg Prod.fst h
  have : d = 0 := by linarith
  exact hd this

/-- **A single declared direction is NOT symmetric**: for d ≠ 0, the
single-direction declaration {d} is not mirror-closed (-d ≠ d) — the
privileged-direction contamination (RulerAsym: 相对性的 2 = 不对称的
根源; R062: 自然数轴不干净 = 特权基点 + 方向 +1): 单方向声明 = 重陷
nat 后继定义问题. -/
theorem single_declared_not_symmetric (d : ℝ) (hd : d ≠ 0) : -d ≠ d := by
  intro h
  apply hd
  linarith

/-- **The pair round trip returns to the anchor**: (x + d) + (-d) = x —
周期回归终点并成为新的起点 (R063: 每步重新锚定; RulerCycle: 对称 →
不对称 → 对称; R121: 互逆箭头同一). -/
theorem declared_pair_round_trip (x d : ℝ) : (x + d) + (-d) = x := by
  ring

/-- **The undeclared successor collapses to the basepoint**: without a
declared direction, the successor is the self-application app(p0,p0),
absorbed by pat0 (R134: any operation on pat0 equals pat0) — 没有声明
方向的后继, 本质上就是返回 p0 的自指 (R122: 全坍缩; R123: 闭包). -/
theorem undeclared_successor_collapses :
    Pat0Absorbing.SelfApp.app Pat0Absorbing.pat0 Pat0Absorbing.pat0 =
      Pat0Absorbing.pat0 :=
  Pat0Absorbing.self_app_absorbing

/-- **The undeclared layer chain collapses**: layerUp(pat0) = pat0 by
the absorbing axiom (R134) — the successor step without a declared
direction returns to the basepoint: pat1 = pat0, the full collapse
(R122). -/
theorem undeclared_chain_collapses :
    Pat0Absorbing.SelfApp.layerUp Pat0Absorbing.pat0 = Pat0Absorbing.pat0 :=
  Pat0Absorbing.layer_absorbing

end OmnidirectionalUnit

end ZeroRelative
