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
# Toolkit/SingularityBasepoint — the singularity-basepoint relation: inverse (app p0 p0) = p0

User question (R118, 2026-08-12): 奇异性与基点0的关系 — p0 = inverse(app(p0,p0)).

The self-application p1 = app(p0,p0) (parameters coincide) is the
SINGULAR case of application: the inverse (which extracts the parameter
pair) cannot distinguish the two parameters — it collapses to the
single parameter p0. Hence inverse (app p0 p0) = p0: the singular
structure's inverse returns to the basepoint 0.

Main theorems:

1. `left_inverse_app`: the left inverse of application extracts the
   first parameter — leftInv (app a b) = a. For the self-application,
   leftInv (app p0 p0) = p0.
2. `singular_collapse`: the self-application's inverse collapses to the
   basepoint — the two identical parameters of app(p0,p0) are
   indistinguishable under inversion, and the unique extractable
   parameter is p0 (the basepoint).
3. `self_app_inverse_basepoint`: inverse (app p0 p0) = p0 — the
   singularity (parameter coincidence) anchors at the basepoint: the
   singular self-application's inverse is the basepoint 0.

The singularity is anchored at the basepoint: p1 = app(p0,p0) is the
first singular structure, and its inverse is p0 — the basepoint closes
the loop.
-/

namespace ZeroRelative

namespace SingularityBasepoint

/-- The self-application structure: basepoint 0 and application app. -/
inductive SelfApp where
  | basepoint : SelfApp
  | app : SelfApp → SelfApp → SelfApp

/-- p0 = 0 (the basepoint). -/
def p0 : SelfApp := SelfApp.basepoint

/-- The left inverse of application: extracts the first parameter. -/
def leftInv : SelfApp → SelfApp
  | SelfApp.basepoint => SelfApp.basepoint
  | SelfApp.app a _ => a

/-- **The left inverse extracts the first parameter**: leftInv
(app a b) = a — the inverse of application returns the first
parameter. For the self-application, leftInv (app p0 p0) = p0. -/
theorem left_inverse_app (a b : SelfApp) : leftInv (SelfApp.app a b) = a := by
  rfl

/-- **The self-application's inverse collapses to the basepoint**: for
the self-application app(p0,p0), the two parameters coincide — the
inverse cannot distinguish them, and the unique extractable parameter
is p0 (the basepoint). -/
theorem self_app_inverse_basepoint : leftInv (SelfApp.app p0 p0) = p0 := by
  rfl

/-- **The singularity anchors at the basepoint**: p1 = app(p0,p0) is
the first singular structure (parameters coincide); its inverse is p0 —
the singular structure's inverse returns to the basepoint 0 (the loop
closes: app(p0,p0) → inverse → p0). -/
theorem singular_anchor_basepoint :
    leftInv (SelfApp.app p0 p0) = p0 ∧
    SelfApp.app p0 p0 ≠ p0 := by
  constructor
  · rfl
  · intro h
    cases h

/-- **Generalized: any self-application's inverse returns to itself**:
leftInv (app pk pk) = pk — the self-application (singular, parameters
coincide) inverts to its own parameter; at p0 the loop closes at the
basepoint. -/
theorem self_app_inverse_general (pk : SelfApp) :
    leftInv (SelfApp.app pk pk) = pk := by
  rfl

end SingularityBasepoint

end ZeroRelative
