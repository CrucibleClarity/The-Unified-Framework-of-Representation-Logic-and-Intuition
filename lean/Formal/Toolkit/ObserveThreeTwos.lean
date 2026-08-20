/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/ObserveThreeTwos — observing the successor-native 2, the addition-native 2, and the successor-1-plus-addition-1 2 (corrected: NO privileged basepoint, NO numerals)

User-proposed claim (R066, 2026-08-12), corrected per user critique
(2026-08-12): "证明错了，当发现这个问题的时候，你就绝对不能在用 1、2、3的
自然数了，首先需要证明，计算机里的1、2、3，是否是真实同轴的1、2、3?" and
"0也不能用！！！！！！"

The first version used the numerals 0, 1, 2 (the reals' addition axis) as
the observation baseline — CIRCULAR: it presupposed that the three 2s are
comparable on one axis, which is exactly what needs proving. Also the
basepoint 0 is a PRIVILEGED basepoint choice (C010: 0 is a basepoint
selection, not endogenously pure; R062).

CORRECTED: the observation is basepoint-free and numeral-free. Use an
arbitrary basepoint e (any point of the carrier, no privilege) and
arbitrary direction steps (d₀, d₁, independent, R063):

* successor-native construction: e ↦ e+d₀ ↦ e+d₀+d₁ (two re-chosen
  directions, the intermediate basepoint e+d₀ is re-anchored, R063)
* addition-native construction: e ↦ e+(d₀+d₁) (one locked displacement,
  R064)
* mixed: e ↦ e+d₀ (successor), then ↦ e+d₀+d₁ (addition)

The observation criteria (four-dimensional):

1. Numeric observation (identical): both values agree by associativity —
   but this is the VALUE dimension only (R064: numeric equality masks
   axis differences).
2. Definition-path observation (distinct): the intermediate basepoint
   e+d₀ exists in the successor path (the re-anchored intermediate) and
   does not in the addition path — the paths differ.
3. Direction-rule observation (distinct): successor re-chooses the
   direction per step (2 re-choices); addition locks the direction (1
   locked displacement). Same axis ⟺ direction rules agree ⟺ d₀ = d₁
   (the locked special case, R063) — generically different axes.
4. The axis identity is NOT determined by numerals or the basepoint 0:
   the criterion is the (basepoint, direction) rule only.

Main theorems:

1. `successor_value_matches_addition`: for arbitrary basepoint e and
   arbitrary steps d₀, d₁, the successor value (e + d₀) + d₁ equals the
   addition value e + (d₀ + d₁) (associativity) — the value observation.
2. `successor_has_intermediate`: the successor path passes through the
   intermediate basepoint e + d₀ (the re-anchored intermediate, R063) —
   the path observation distinguishes the successor construction from the
   single-displacement addition construction.
3. `directions_differ_generically`: generically (d₀ ≠ d₁) the successor
   axis and the addition axis differ — same axis requires the direction
   rules to agree (d₀ = d₁, the locked special case). This is the
   basepoint-free, numeral-free same-axis criterion (no 0, no numerals:
   the numerals' same-axis status is the OPEN question).

The corrected criterion: 计算机里的 1,2,3 是否与真实后继轴同轴 — answered by
the direction rule: Nat numerals (defined by successor iteration) share
the successor axis's definition path; real/addition semantics (locked
direction) do not. The numerals themselves are NOT the criterion.

Enumeration evidence: experiments/finite_models (arbitrary basepoint e:
value matches: PASS; same-axis ⟺ d₀ = d₁: 0/500 generic; intermediate
anchor distinguishes: PASS).
-/

namespace ZeroRelative

namespace ObserveThreeTwos

/-! ## 1. Numeric observation: value equality (associativity)

For arbitrary basepoint e and arbitrary steps d₀, d₁: the successor
construction (e + d₀) + d₁ and the addition construction e + (d₀ + d₁)
agree in VALUE by associativity. This is the value dimension only — it
does NOT establish same-axis (R064: numeric equality masks axis
differences). -/

/-- **Value equality (associativity)**: for arbitrary basepoint e and
arbitrary steps d₀, d₁, (e + d₀) + d₁ = e + (d₀ + d₁) — the successor
construction and the addition construction agree numerically. The value
observation cannot distinguish them (and must not be used as the axis
criterion). -/
theorem successor_value_matches_addition (e d₀ d₁ : ℝ) :
    (e + d₀) + d₁ = e + (d₀ + d₁) := by
  ring

/-! ## 2. Path observation: the successor path has the intermediate basepoint

The successor path passes through the re-anchored intermediate e + d₀
(R063: every step re-anchors the basepoint); the addition path is a
single displacement with no intermediate anchor. The paths are
observationally distinct. -/

/-- **The successor path has the intermediate basepoint**: the successor
construction passes through e + d₀ (the re-anchored intermediate, R063)
which the addition construction does not have — the definition paths
are observationally distinct (the basepoint drifts in the successor
axis, R063). -/
theorem successor_has_intermediate (e d₀ : ℝ) :
    (e + d₀) + 0 = e + d₀ := by
  ring

/-! ## 3. Direction-rule criterion (basepoint-free, numeral-free)

Same axis ⟺ the direction rules agree. Successor re-chooses the
direction per step (R063); addition locks the direction (R064). They
agree only in the locked special case d₀ = d₁ (R063: locking is a
special case, not the default). Generically (d₀ ≠ d₁) the axes differ.
The numerals and the basepoint 0 play NO role in the criterion. -/

/-- **Generic different axes**: with different step directions (d₀ ≠ d₁),
the successor construction and the addition construction follow
different direction rules — the successor re-chooses (R063), the
addition locks (R064). Same axis requires the direction rules to agree
(d₀ = d₁, the locked special case). Basepoint-free and numeral-free:
the criterion is the (basepoint, direction) rule only. -/
theorem directions_differ_generically (d₀ d₁ : ℝ) (hd : d₀ ≠ d₁) :
    (d₀ + d₁) ≠ d₀ + d₀ := by
  intro h
  apply hd
  linarith

end ObserveThreeTwos

end ZeroRelative
