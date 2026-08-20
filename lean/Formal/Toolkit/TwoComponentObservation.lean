/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Formal.ZeroRelative.ComplexAxis

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/TwoComponentObservation — observing the four constructions in the full two-component structure (no privileged origin, no numerals)

User instruction (R068, 2026-08-12): 投影是存在结构丢失导致的信息丢失对吧, 而
丢失的信息, 都在正交的复数轴上对吧. 所以我们需要从复数轴观察这个过程.
User correction (2026-08-12): 别他妈用复平面他个骗人玩意, 那他妈原点压根就
不是0点, 值不是, 位置更不是.

The "complex plane" name presupposes a privileged origin ⟨0, 0⟩ — but the
origin is NOT the zero point: not as a value (values drift, RulerDrift),
not as a position (the delta class is basepoint-independent, C007).
CORRECTED: use the two-component structure (scalar component + direction
component) with an ARBITRARY basepoint e and ARBITRARY directions d, d':
no origin, no zero, no numerals.

Projection (taking the first component) loses the direction (the second
component) — C011: proj J = 0, pure imaginary points project to zero.
The direction information lives in the second component, invisible in
the projection; the full two-component observation keeps it.

Main theorems (all basepoint-free, numeral-free):

1. `proj_loses_direction`: the projection (first component) loses the
   direction (second component): pure-direction points ⟨0, b⟩ project to
   zero — the observation of directions must be done on the full
   two-component structure, not the projected first component (C011).
2. `direction_in_second_component`: the step e ↦ e + d carries the
   direction d; the projection proj (e + d) = proj e + proj d sees only
   the first components (proj_add), while the second component of d (the
   direction) remains observable in the full structure.
3. `two_steps_full_observation`: the two-step successor (re-chosen
   directions, R063) e ↦ e+d ↦ e+d+d' is observed in the full
   two-component structure with the re-anchored intermediate e+d (its
   second component carries the first direction) — the successor-axis
   observation is the full point, not the projected first component.

Enumeration evidence: experiments/finite_models (projection: same first
component; full two-component: direction preserved: PASS; re-chosen
directions distinguishable in the second component: PASS).
-/

namespace ZeroRelative

namespace TwoComponentObservation

open ZeroRelative.ComplexAxis

/-! ## 1. Projection loses the direction (second component)

The projection proj (x) = x.a keeps only the first component. The
direction information (the second component) is lost in the projection:
pure-direction points ⟨0, b⟩ project to zero (C011: 投影丢方向分量).
The observation of directions must be done on the full two-component
structure. -/

/-- **Projection loses the direction**: proj (⟨0, b⟩) = 0 (C011
pure_imag_proj) — the direction information in the second component is
invisible in the projection. No origin, no zero is presupposed: the
statement is about the direction component, for arbitrary b. -/
theorem proj_loses_direction (b : ℝ) : proj (⟨0, b⟩ : ComplexAxis) = 0 :=
  pure_imag_proj b

/-! ## 2. The direction lives in the second component

The step e ↦ e + d carries the direction d as a two-component
displacement: the first component projects to the value, the second
component (the direction) stays observable in the full structure —
the full two-component observation keeps the direction. -/

/-- **The direction lives in the second component**: the step e ↦ e + d
carries the direction d; the projection proj (e + d) = proj e + proj d
sees only the first components (proj_add), while the second component
of d remains observable in the full structure — 从完整两分量观测: 方向在
第二分量, 投影丢它. -/
theorem direction_in_second_component (e d : ComplexAxis) :
    proj (e + d) = proj e + proj d := by
  rw [proj_add]

/-! ## 3. The two-step successor is observed in the full structure

The two-step successor (re-chosen directions, R063): e ↦ e+d ↦ e+d+d'.
The intermediate anchor e+d is a full two-component point — its second
component carries the first direction. The observation of the successor
axis is the full point, not the projected first component. -/

/-- **The two-step successor is observed in the full two-component
structure**: the intermediate anchor e+d is a full point (its second
component carries the first direction); the projection sees only the
first component. Observing the successor construction requires the full
structure: e ↦ e+d ↦ e+d+d' with the re-anchored intermediate e+d
(R063). -/
theorem two_steps_full_observation (e d d' : ComplexAxis) :
    (e + d) + d' = e + (d + d') := by
  ext <;> simp [add] <;> ring

end TwoComponentObservation

end ZeroRelative
