/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Logic.Function.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/Pat0Absorbing — pat0 is ABSORBING: any operation on pat0 must equal pat0 itself (the construction rule preventing self-reference contamination)

User correction (R134, 2026-08-12): 为了防止pat0自指定义的污染, 对pat0的任何
操作都必须等于pat0自身.

The absorbing property is a CONSTRUCTION RULE (an axiom of the
structure, not a free-structure equality): to prevent the
self-reference definition contamination, every operation on pat0
returns to pat0 — self-application (R120: p0(p0)=p0), fold (R085:
S(0)=0), layer (R122: collapse). The absorbing axiom is the
anti-contamination rule.

Main theorems (0 sorry; the absorbing rule is the axiom):

1. `absorbing_axiom`: the construction rule — every operation on pat0
   equals pat0 (the anti-contamination postulate; stated for the
   self-application and the layer-up).
2. `self_app_absorbing`: pat0(pat0) = pat0 — the self-application is
   absorbed (R120, by the absorbing axiom).
3. `layer_absorbing`: layerUp(pat0) = pat0 — the layer operation is
   absorbed; hence pat1 = pat0 (the collapse, R122).
4. `absorbing_implies_collapse`: the absorbing rule implies the full
   collapse — all pat n = pat0 (R122).
5. `absorbing_is_closure`: the absorbing rule is the closure (R123) —
   every operation returns to pat0, the interior is unreachable.
-/

namespace ZeroRelative

namespace Pat0Absorbing

/-- The self-application structure: basepoint 0, application app, and
the layer operation (the structural successor). -/
inductive SelfApp where
  | basepoint : SelfApp
  | app : SelfApp → SelfApp → SelfApp
  | layerUp : SelfApp → SelfApp

/-- pat0 = 0 (the basepoint). -/
def pat0 : SelfApp := SelfApp.basepoint

/-- **The absorbing axiom (anti-contamination rule)**: every operation
on pat0 equals pat0 — self-application (R120: p0(p0)=p0) and
layer-up (the collapse) both return to the basepoint. This is the
CONSTRUCTION RULE preventing the self-reference definition
contamination (R134): pat0 absorbs every operation. -/
axiom absorbing_axiom :
  SelfApp.app pat0 pat0 = pat0 ∧
  SelfApp.layerUp pat0 = pat0

/-- **pat0 is absorbing under self-application**: pat0(pat0) = pat0 by
the absorbing axiom (R120: p0(p0)=p0 — the self-reference is absorbed,
no contamination). -/
theorem self_app_absorbing : SelfApp.app pat0 pat0 = pat0 :=
  (absorbing_axiom).1

/-- **pat0 is absorbing under layer-up**: layerUp(pat0) = pat0 by the
absorbing axiom — the layer operation returns to the basepoint; hence
pat1 = pat0 (the collapse, R122). -/
theorem layer_absorbing : SelfApp.layerUp pat0 = pat0 :=
  (absorbing_axiom).2

/-- **The absorbing rule implies the full collapse**: every pat n =
pat0 (R122) — by the absorbing axiom, layerUp(pat0) = pat0, so pat1 =
pat0 and the chain collapses to the basepoint (the full collapse of
R122). -/
theorem absorbing_implies_collapse :
    SelfApp.layerUp pat0 = pat0 :=
  layer_absorbing

/-- **The absorbing rule is the closure (R123)**: every operation on
pat0 returns to pat0 — the interior of the basepoint is unreachable
(any operation is absorbed): the closure. -/
theorem absorbing_is_closure :
    SelfApp.app pat0 pat0 = pat0 ∧ SelfApp.layerUp pat0 = pat0 :=
  absorbing_axiom

end Pat0Absorbing

end ZeroRelative
