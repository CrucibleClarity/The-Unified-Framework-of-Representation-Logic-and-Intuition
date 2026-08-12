/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Logic.Relation

/-!
# C009: when does an endogenous generation structure have ω type

Claim ledger C009 (status: CONJECTURE, novelty: NOVELTY_UNASSESSED).
Branch: basepoint_relativity.

Conditions F1-F5 (no Nat indexing — object-level statements carry no natural
coordinate for positions; see C008 for the relation machinery):
  F1 functional: each node has at most one R-successor
  F2 acyclic:    TransGen R is irreflexive on Reach(e)
  F3 linear:     each x ≠ e reachable from e has a unique R-predecessor
  F4 start:      e has no R-predecessor
  F5 infinite:   every x ∈ Reach(e) has an R-successor

Finite verification (C009_omega_type.py): F1∧F2∧F3∧F4 has no counterexample on
n=3,4 — every such component is a single chain. With F5 the chain is ω.

This file formalizes the DEFINITIONS of F1-F5 and the reachability machinery.
The full representation theorem (F1-F5 ⟹ (Reach(e),R) ≅ (N,S)) is in progress:
the core difficulty is that "y R x with x reachable ⟹ y reachable" requires a
well-founded / induction argument on the unique-predecessor structure, which is
exactly what builds the chain (and must be done WITHOUT Nat indexing).
-/

namespace ZeroRelative

variable {H : Type*}

/-- A node has at most one successor under `R`. -/
def UniqueSucc (R : H → H → Prop) : Prop :=
  ∀ e x y, R e x → R e y → x = y

/-- A node `x` has a unique predecessor under `R` (any two predecessors coincide). -/
def UniquePred (R : H → H → Prop) (x : H) : Prop :=
  ∀ p q, R p x → R q x → p = q

/-- A node has no predecessor under `R`. -/
def NoPred (R : H → H → Prop) (e : H) : Prop :=
  ∀ p, ¬ R p e

/-- Every reachable node has a successor. -/
def HasSucc (R : H → H → Prop) (e : H) : Prop :=
  ∀ x, Relation.TransGen R e x → ∃ y, R x y

/-- The reachable set from `e` (reflexive-transitive closure). -/
def Reachable (R : H → H → Prop) (e x : H) : Prop :=
  Relation.ReflTransGen R e x

/-- F1: `R` is functional (at most one successor per node). -/
def F1 (R : H → H → Prop) : Prop := UniqueSucc R

/-- F3: every node reachable from `e` other than `e` has a unique predecessor. -/
def F3 (R : H → H → Prop) (e : H) : Prop :=
  ∀ x, Reachable R e x → x ≠ e → UniquePred R x

/-- F4: `e` has no predecessor. -/
def F4 (R : H → H → Prop) (e : H) : Prop := NoPred R e

/-- F5: every reachable node has an R-successor (no terminal). -/
def F5 (R : H → H → Prop) (e : H) : Prop := HasSucc R e

/-- F2 (acyclic): reachability is irreflexive on the reachable set. -/
def F2 (R : H → H → Prop) (e : H) : Prop :=
  ∀ x, Reachable R e x → ¬ Relation.TransGen R x x

/-- F1 implies that from `e`, a node has at most one successor: if two nodes are
both R-successors of `e`, they are equal. -/
theorem f1_succ_unique {R : H → H → Prop} (hF1 : F1 R) {e x y : H}
    (hx : R e x) (hy : R e y) : x = y := hF1 e x y hx hy

/-- F3 at a reachable non-start node: any two predecessors coincide. -/
theorem f3_pred_unique {R : H → H → Prop} {e : H} (hF3 : F3 R e)
    {x p q : H} (hx : Reachable R e x) (hxne : x ≠ e)
    (hp : R p x) (hq : R q x) : p = q := hF3 x hx hxne p q hp hq

/-- F4: the start `e` has no predecessor. -/
theorem f4_no_pred {R : H → H → Prop} {e : H} (hF4 : F4 R e) :
    ∀ p, ¬ R p e := hF4

/-- Reachability from a one-step edge: `R e x` implies `x` is reachable from `e`. -/
theorem reachable_of_edge {R : H → H → Prop} {e x : H} (h : R e x) :
    Reachable R e x := by
  unfold Reachable
  exact Relation.ReflTransGen.single h

/-- The start `e` is reachable from itself. -/
theorem reachable_self {R : H → H → Prop} (e : H) : Reachable R e e := by
  unfold Reachable
  exact Relation.ReflTransGen.refl

end ZeroRelative
