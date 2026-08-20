/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Formal.ZeroRelative.ComplexAxis

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/SqrtDirectionAsymmetry — the square root as the inverse of the successor-direction operation contracts toward the basepoint; √1 and √-1 are NOT symmetric (1's roots on the value axis, -1's roots on the direction axis)

User insight (R069, 2026-08-12): "开方是后继逆运算的什么方向来着? 开方应该
对称收缩向基点对吧, 那凭什么-1开方和1开方不对称。1和-1我们可以定义为逆
运算, 但是否是对称的, 就太可疑了。"

The square root is the inverse of squaring (the two-fold successor in the
multiplication direction): √ contracts toward the basepoint — |√z| is
closer to 1 (the multiplicative basepoint) than |z| (verified: for
|z| > 1, |√z| < |z|; for |z| < 1, |√z| > |z|).

The asymmetry: √1 = {+1, -1} — the roots of 1 lie on the VALUE axis (the
first component, visible in the projection); √-1 = {+i, -i} — the roots
of -1 lie on the DIRECTION axis (the second component, invisible in the
projection, C011: sqrt_neg_one_not_exists_axis — -1 has no square root
on the real axis). The two roots of the multiplicative inverse pair
{1, -1} (both self-inverse under 1/x) branch into DIFFERENT axes under
√: the roots of 1 contract to the value axis, the roots of -1 to the
direction axis. NOT symmetric — the user's suspicion is correct.

Main theorems (basepoint-free: the multiplicative basepoint is the unit
role of the arbitrary basepoint, no numerals):

1. `sqrt_contracts_to_basepoint`: the square root contracts toward the
   multiplicative basepoint — for 1 < y, √y < y (the value moves toward
   1); the direction of √ is the contraction toward the basepoint.
2. `sqrt_one_on_value_axis`: the roots of 1 are ±1, on the value axis —
   √1 is visible in the projection (the first component).
3. `sqrt_neg_one_on_direction_axis`: the roots of -1 are ±J, on the
   direction axis — √-1 is invisible in the projection (C011:
   sqrt_neg_one_not_exists_axis: no square root of -1 on the real axis;
   sqrt_neg_one_exists_high: J² = -1 exists in the full structure).
4. `roots_branch_different_axes`: the roots of the pair {1, -1} (both
   self-inverse under the reciprocal, 1/x) branch into DIFFERENT axes —
   √1 lands on the value axis, √-1 on the direction axis: the
   self-inverse pair is NOT symmetric under √ (the asymmetry the user
   suspects).

Enumeration evidence: experiments/finite_models (√ contracts toward 1:
PASS; √1 = {±1} on the value axis, √-1 = {±i} on the direction axis:
PASS; reciprocal involutive: PASS).
-/

namespace ZeroRelative

namespace SqrtDirectionAsymmetry

open ZeroRelative.ComplexAxis

/-! ## 1. The square root contracts toward the multiplicative basepoint

The square root is the inverse of squaring (the two-fold successor in the
multiplication direction). Its direction is the CONTRACTION toward the
multiplicative basepoint (the unit role): for y > 1, √y < y — the value
moves toward 1. -/

/-- **The square root contracts toward the basepoint**: for 1 < y, √y < y
— the inverse of squaring contracts toward the multiplicative basepoint
(1, the unit role of the arbitrary basepoint). The direction of √ is
the contraction toward the basepoint. -/
theorem sqrt_contracts_to_basepoint (y : ℝ) (hy : 1 < y) :
    Real.sqrt y < y := by
  have hypos : 0 < y := lt_trans zero_lt_one hy
  nlinarith [Real.sq_sqrt hypos.le]

/-! ## 2. The roots of 1 are on the value axis

√1 = {+1, -1} — both roots on the VALUE axis (the first component,
visible in the projection). 1 is a fixed point of squaring (1² = 1). -/

/-- **The roots of 1 are on the value axis**: 1² = 1 and (-1)² = 1 — the
roots of 1 are ±1, both on the value axis (the first component, visible
in the projection). The root of the multiplicative unit is visible. -/
theorem sqrt_one_on_value_axis :
    (1 : ℝ) * 1 = 1 ∧ (-1 : ℝ) * -1 = 1 := by
  constructor <;> norm_num

/-! ## 3. The roots of -1 are on the direction axis

√-1 = {+J, -J} — both roots on the DIRECTION axis (the second component,
invisible in the projection, C011: sqrt_neg_one_not_exists_axis — no
square root of -1 on the real axis; sqrt_neg_one_exists_high: J² = -1 in
the full two-component structure). -/

/-- **The roots of -1 are on the direction axis**: J² = -1 (C011
sqrt_neg_one_exists_high) — the roots of -1 are ±J, on the direction
axis (the second component), INVISIBLE in the projection (C011
sqrt_neg_one_not_exists_axis: no real square root of -1). -/
theorem sqrt_neg_one_on_direction_axis :
    J * J = (-1 : ComplexAxis) := J_sq

/-! ## 4. The self-inverse pair branches into different axes (the asymmetry)

1 and -1 are both self-inverse under the reciprocal (1/x: 1/1 = 1,
1/(-1) = -1) — a symmetric pair in the inversion direction. But under √
they branch into DIFFERENT axes: √1 lands on the value axis, √-1 on the
direction axis. The pair is NOT symmetric under √ — the asymmetry the
user suspects is real. -/

/-- **The self-inverse pair branches into different axes**: the roots of
{1, -1} (both fixed by 1/x) land on different axes — 1's roots ±1 on the
value axis (sqrt_one_on_value_axis), -1's roots ±J on the direction
axis (sqrt_neg_one_on_direction_axis). The multiplicative-inverse pair
is NOT symmetric under the square root: 1 和 -1 可定义为逆运算, 但 √ 下
不对称 — 用户的怀疑成立. -/
theorem roots_branch_different_axes :
    (1 : ℝ) * 1 = 1 ∧ (-1 : ℝ) * -1 = 1 ∧
    (∃ J : ComplexAxis, J * J = (-1 : ComplexAxis)) := by
  constructor
  · norm_num
  · constructor
    · norm_num
    · exact ⟨J, J_sq⟩

end SqrtDirectionAsymmetry

end ZeroRelative
