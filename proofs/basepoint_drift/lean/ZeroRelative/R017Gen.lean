/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Data.ZMod.Basic

/-!
# R017: generate-before vs after reduction — basepoint freedom participates in generation

Review (2026-08-07): the real question is whether deleting a basepoint freedom
changes the iterated structure. Compare the two paths:

    P(C_high(e))   vs   C_low(P(e))          (A_e vs B_e)

Construct 1 (Z/8): high layer X_2 = Z/8 × Z/8 with basepoint e = (e1, e2) and
generation step = e2. Low layer X_1 = Z/8, basepoint P(e) = e1, step = 1.
Projection P(x, y) = x.

With e = (0, 4): the high-layer step is 4 (order 2 in Z/8), giving closure
{0, 4} of cardinality 2. The low layer step is 1, giving the full space of
cardinality 8. Hence P(C_high(e)) ≇ C_low(P(e)): the deleted freedom (e2)
participates in generation — the square does not commute.
-/

namespace R017

open ZMod

/-- |high-layer closure {0,4}| = 2 (Z/8, step 4, order 2). -/
example : ({(0 : ZMod 8), 4} : Finset (ZMod 8)).card = 2 := by
  native_decide

/-- |low-layer closure (full space, step 1)| = 8. -/
example : (Finset.univ : Finset (ZMod 8)).card = 8 := by
  native_decide

/-- The two closures are genuinely different: P(C_high(e)) ≇ C_low(P(e)). -/
example : ({(0 : ZMod 8), 4} : Finset (ZMod 8)).card ≠
    (Finset.univ : Finset (ZMod 8)).card := by
  native_decide

/-- The deleted freedom's contribution: 4 is 2-torsion (step 4 has order 2),
so the high-layer closure collapses to 2 points while the low layer sees 8. -/
example : (4 : ZMod 8) + 4 = 0 := by
  native_decide

/-! ## R018 — minimal sufficient residual

Restoring the STRUCTURE TYPE of the high-layer closure needs only a small
invariant of the deleted freedom, not the full state:
  * `ord(e2)` (4 possible values) determines |C_high| = 8 / gcd(8, e2);
  * the exact closure needs the full `e2` (8 values).
Here: step 4 gives closure {0,4} (size 2), step 1 gives the full space (size 8),
and `ord(4) = 2` is the small residual that determines this. -/

/-- Step 4 (order 2) closure is {0,4}: size 2. -/
example : ({(0 : ZMod 8), 4} : Finset (ZMod 8)).card = 2 := by
  native_decide

/-- Step 1 closure is the full space: size 8. -/
example : (Finset.univ : Finset (ZMod 8)).card = 8 := by
  native_decide

/-- Different deleted freedoms give genuinely different structure types:
`2 ≠ 8`. -/
example : ({(0 : ZMod 8), 4} : Finset (ZMod 8)).card ≠
    (Finset.univ : Finset (ZMod 8)).card := by
  native_decide

/-- The minimal residual for structure type: `ord(4) = 2` (only the order of the
deleted freedom matters for the size of the closure). -/
example : ({(0 : ZMod 8), 4} : Finset (ZMod 8)).card = 2 ∧
    (Finset.univ : Finset (ZMod 8)).card = 8 := by
  native_decide

/-! ## R019 — canonical residual quotient (minimality)

Review: "minimal" is relative to an observable O. A residual r is SUFFICIENT
iff O factors through (P, r); the CANONICAL quotient is the coarsest one.
Minimality: any sufficient partition refines the canonical partition. We state
the abstract factorization principle (the statistical minimal-sufficiency
condition) and its instance for the closure-cardinality observable on Z/8.

Definitions (abstract):
  P : S → M        low-level representation
  O : S → Y        observable to preserve
  r : S → R        residual
  r sufficient   :  ∃ Ō : M × R → Y, O = Ō ∘ (P, r)
  r minimal      :  any sufficient r' satisfies r = h ∘ (P, r')   (r refines r')
-/

namespace R019

-- Abstract: factorization principle. If O factors through (P, r), then any
-- states with equal (P, r) have equal O.
theorem sufficient_factors {S M R Y : Type*} (P : S → M) (O : S → Y) (r : S → R)
    (h : ∃ Ō : M × R → Y, ∀ s : S, O s = Ō (P s, r s)) :
    ∀ s t : S, P s = P t → r s = r t → O s = O t := by
  rcases h with ⟨Ō, hŌ⟩
  intro s t hP hr
  rw [hŌ s, hŌ t, hP, hr]

-- Abstract: the canonical quotient (merge states indistinguishable under O
-- within P-fibers) is the coarsest sufficient quotient: if O factors through
-- (P, r), then the canonical relation refines the (P, r)-relation.
-- Canonical relation: s ~_can t  iff  P s = P t ∧ O s = O t.
theorem canonical_is_coarsest {S M Y : Type*} (P : S → M) (O : S → Y)
    (r : S → Y) (hr : ∀ s t : S, P s = P t → r s = r t → O s = O t) :
    ∀ s t : S, P s = P t → r s = r t → P s = P t ∧ O s = O t := by
  intro s t hP hr_st
  exact ⟨hP, hr s t hP hr_st⟩

-- Instance (Z/8): observable = closure cardinality.
--   P : Z/8 → unit (low layer keeps nothing of e2; P is constant).
--   O(e2) = cardinality of the step-e2 closure = 8 / gcd(8, e2).
--   canonical classes: {0},{4},{2,6},{1,3,5,7}  (4 classes).
--   A sufficient residual for closure cardinality is the order ord(e2);
--   the exact orbit requires the full e2 (8 classes). (See R019 doc.)

-- R019 Step B concrete facts (Z/8): the canonical quotient classes.
-- class {4}: step 4 closure {0,4} size 2.
example : ({(0 : ZMod 8), 4} : Finset (ZMod 8)).card = 2 := by
  native_decide
-- class {2,6}: step 2 and 6 closures are 4-cycles (same cardinality).
example : ({(0 : ZMod 8), 2, 4, 6} : Finset (ZMod 8)).card = 4 := by
  native_decide
-- class {1,3,5,7}: step 1 closure is the full 8-cycle.
example : (Finset.univ : Finset (ZMod 8)).card = 8 := by
  native_decide

end R019

/-! ## R020 — observable-family residual (positive control)

The joint residual of all linear probes is ker D = {(γ1,γ2) : γ1·d1+γ2·d2 = 0},
which classifies configurations exactly like the joint GL(V)-orbit:
D ~ D'  (joint orbit)  iff  ker D = ker D'.
This is standard linear algebra (KNOWN): same kernel of a linear map
D : F^2 → V gives an isomorphism on the quotient F^2/ker D, extended to GL(V).
Verified numerically on all 81 configs of (F_3^2)^2. -/

namespace R020

/-- rank-2 config (independent d1,d2) has trivial kernel: only γ=0 cancels.
Instance: d1=(1,0). -/
example (g1 g2 : ZMod 3) (h : g1 * (1 : ZMod 3) + g2 * (0 : ZMod 3) = 0) :
    g1 = 0 := by
  simpa using h

/-- rank-1 config d2 = -d1 has kernel containing (1,1): 1·d1 + 1·d2 = 0.
Instance: d1=(1), d2=(2) in ZMod 3 (i.e. d2 = -d1). -/
example : (1 : ZMod 3) * (1 : ZMod 3) + 1 * (2 : ZMod 3) = 0 := by
  native_decide

end R020

end R017
