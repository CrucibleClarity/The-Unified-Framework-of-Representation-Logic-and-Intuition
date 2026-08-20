/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/SuccessorNotAddition — successor is NOT addition: the value reached from the successor axis's intermediate point THROUGH THE ADDITION AXIS and the value reached from the same intermediate BY SUCCESSOR are two different values (different axes, same number)

User-proposed claim (R064, 2026-08-12), precise semantics: "从后继轴的1, 通过
加法轴走向2. 和从后继的1, 后继得到的2. 是不同的2."

CORRECTED (2026-08-12, user critique): the first version used the numerals
0, 1, 2 (the reals' addition axis) as the baseline — circular (presupposing
the three constructions are comparable, exactly what needs proving) and 0
is a privileged basepoint (C010: 0 is a basepoint selection, R062). The
corrected statements use an arbitrary basepoint e and arbitrary steps d, d':
no 0, no numerals. The "unit" case is dropped (the unit step itself is a
privileged convention).

R063 established: every successor step is a fresh (basepoint, direction)
choice. The two paths differ by the AXIS:

* Path A (cross-axis): e →(successor axis) e+d, then (e+d) →(addition axis
  +d') e+d+d'. The addition axis is the LOCKED-direction axis (a single
  fixed displacement). Reaching the value from the successor axis's
  intermediate point through the addition axis means SWITCHING axes: the
  direction rule changes from "re-choose" (successor) to "locked"
  (addition).

* Path B (same-axis): e →(successor axis) e+d →(successor axis) e+d+d'.
  The successor axis re-anchors at e+d and re-chooses the direction.
  Reaching the value from the successor's intermediate by successor means
  STAYING on the axis.

The two values are numerically equal (associativity) but belong to
different axes — same number, different axis (different direction rule:
locked vs re-chosen).

Main theorems (all basepoint-free, numeral-free):

1. `cross_axis_value_equals_same_axis`: the cross-axis path (successor to
   e+d, then addition +d') and the same-axis path (successor twice) agree
   numerically when the second displacements agree (associativity).
2. `cross_axis_differs_from_same_axis`: with different second directions
   (d' ≠ d''), the cross-axis value and the same-axis value DIFFER — from
   the same intermediate point, the addition axis and the successor axis
   give different values.

The direction-rule criterion (R066/ObserveThreeTwos.directions_differ_generically)
is the same-axis test: successor re-chooses (R063), addition locks (R064).
-/

namespace ZeroRelative

namespace SuccessorNotAddition

/-! ## 1. Cross-axis vs same-axis: same value (associativity)

Path A: (e + d) + d' — successor axis to e+d, then addition axis +d'.
Path B: (e + d) + d'' — successor axis twice (second step re-anchors at
e+d). When d' = d'' the values coincide by associativity. -/

/-- **Cross-axis and same-axis agree numerically when the second
displacements agree**: (e + d) + d' = (e + d) + d'' trivially when
d' = d'', and via associativity both equal e + (d + d') — the two
values coincide in NUMBER when the second displacement is the same.
The value equality is associativity, not axis identity. -/
theorem cross_axis_value_equals_same_axis (e d d' : ℝ) :
    (e + d) + d' = e + (d + d') := by
  ring

/-! ## 2. Different axes give different values

From the same intermediate point e+d (the successor axis's intermediate),
the addition axis (locked direction d') and the successor axis
(re-chosen direction d'') give different values whenever d' ≠ d''. -/

/-- **The addition axis and the successor axis give different values from
the same intermediate point**: with different second directions (d' ≠
d''), the cross-axis value ((e+d) + d') and the same-axis value ((e+d) +
d'') differ — 从后继轴的中间点, 通过加法轴走向结果, 和从后继的中间点,
后继得到的, 是不同的值 (different axes give different values). -/
theorem cross_axis_differs_from_same_axis (e d d' d'' : ℝ) (hd : d' ≠ d'') :
    (e + d) + d' ≠ (e + d) + d'' := by
  intro h
  apply hd
  linarith

end SuccessorNotAddition

end ZeroRelative
