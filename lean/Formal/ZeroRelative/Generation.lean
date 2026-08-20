/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Logic.Relation

/-!
# C008: Endogenous basepoint generation — reachability structure, no Nat index

Claim ledger C008 (status: CONJECTURE → OBSERVATION, novelty: NOVELTY_UNASSESSED).
Branch: basepoint_relativity.

★ Foundational fix (user directive): do NOT presuppose the natural numbers.
The research question is "how does the natural-number-like iteration structure
EMERGE from basepoint changes" — so Nat must not be a primitive of the iteration
apparatus. `Function.iterate F n`, `F^[n]`, `orbit : ℕ → H`, and Church numerals
all presuppose Nat and are BANNED from this branch.

Here we study an unpointed structure `H` with a generation relation
`R : H → H → Prop` (e' is a sub-basepoint generated from e). Reachability is
`Relation.TransGen R` (transitive closure) — the object-level statements carry NO
natural-number coordinate for positions.

Observations recorded here (from finite enumeration, C008_reachability*.py):
* A total function σ : H → H on a FINITE set always has a cycle — so ω-like
  chains require either a PARTIAL rule (a "dead end" / terminal) or an infinite H.
* Partial generation rules realize: chains (ω truncations), branching trees,
  cycles/rho, isolated points. These are the structure types that can occur.
-/

namespace ZeroRelative

variable {H : Type*}

/-- A generation relation: `R e e'` means `e'` is a sub-basepoint generated from `e`. -/
def GenRel (R : H → H → Prop) (e e' : H) : Prop := R e e'

/-- Reachability: `e` can reach `e'` by finitely many generation steps.
Object-level statement, no Nat coordinates for the intermediate positions. -/
def Reach (R : H → H → Prop) (e e' : H) : Prop := Relation.TransGen R e e'

/-- One generation step implies reachability. -/
theorem reach_single {R : H → H → Prop} {e e' : H} (h : R e e') : Reach R e e' :=
  Relation.TransGen.single h

/-- Reachability is transitive. -/
theorem reach_trans {R : H → H → Prop} {a b c : H}
    (hab : Reach R a b) (hbc : Reach R b c) : Reach R a c :=
  Relation.TransGen.trans hab hbc

/-- Reachability is transitive as a relation. -/
theorem reach_trans_rel {R : H → H → Prop} : IsTrans H (Reach R) := by
  constructor
  intro a b c hab hbc
  exact reach_trans hab hbc

/-- A deterministic generation rule `σ` is the functional (non-branching) special case:
`R e e'` holds iff `e' = σ e`. -/
def GenRelOfFun (σ : H → H) (e e' : H) : Prop := e' = σ e

/-- For a functional generation rule, reachability is a right-fiber of iterates;
but we DO NOT define `σ^[n]` here — Nat-free discipline. We only record that
successors are unique: from `e`, any two generated sub-basepoints coincide. -/
theorem fun_gen_successor_unique {σ : H → H} {e e' e'' : H}
    (h1 : GenRelOfFun σ e e') (h2 : GenRelOfFun σ e e'') : e' = e'' := by
  unfold GenRelOfFun at h1 h2
  rw [h1, h2]

/-- C008: reachability structure types are exactly the functional-graph types
(chain truncations / cycles / rho / branching / isolated). This is recorded as an
OBSERVATION from finite enumeration; Lean formalizes the relation machinery
(single/trans), and the classification is documented in the enumeration scripts. -/
theorem reach_is_transitive_closed (R : H → H → Prop) :
    (∀ a b c, Reach R a b → Reach R b c → Reach R a c) := by
  intro a b c hab hbc
  exact reach_trans hab hbc

end ZeroRelative
