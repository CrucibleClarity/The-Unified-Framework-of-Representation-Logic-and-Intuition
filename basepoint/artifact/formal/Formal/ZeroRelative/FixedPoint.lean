/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Order.FixedPoints
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Logic.Function.Conjugate

/-!
# C002: least fixed point is preserved under order-isomorphic semiconjugacy

Claim ledger C002 (status: CONJECTURE, novelty: KNOWN).
Direction C candidate family C-C2.

Statement:
  Let L_e, L_f be complete lattices, F_e : L_e →o L_e, F_f : L_f →o L_f,
  and T : L_e ≃o L_f an order isomorphism.
  If T semiconjugates F_e to F_f (∀ x, T (F_e x) = F_f (T x)),
  then T (F_e.lfp) = F_f.lfp.

Mathlib facts used:
  * `OrderHom.lfp f = sInf {a | f a ≤ a}`  (Mathlib.Order.FixedPoints)
  * `map_sInf` — order isomorphisms preserve arbitrary infima
    (sInfHomClass, Mathlib.Order.Hom.CompleteLattice)
  * `OrderIsoClass.map_le_map_iff` — an order iso satisfies `f a ≤ f b ↔ a ≤ b`
    (Mathlib.Order.Hom.Basic)

Counterexample (order embedding, not isomorphism) is in
  experiments/counterexamples/C002_order_embedding_lfp.py:
  L_e = Unit, L_f = Bool, F = id both, T () = True.
-/

open Function

namespace ZeroRelative

variable {L_e L_f : Type*} [CompleteLattice L_e] [CompleteLattice L_f]

/-- Order isomorphisms map pre-fixed points of `F_e` onto pre-fixed points of `F_f`
when they semiconjugate `F_e` to `F_f`:
`T '' {a | F_e a ≤ a} = {b | F_f b ≤ b}`. -/
theorem pre_fixedPoints_image_of_orderIso_semiconj {F_e : L_e →o L_e} {F_f : L_f →o L_f}
    (T : L_e ≃o L_f) (h : ∀ x, T (F_e x) = F_f (T x)) :
    T '' {a | F_e a ≤ a} = {b | F_f b ≤ b} := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    calc
      F_f (T a) = T (F_e a) := (h a).symm
      _ ≤ T a := T.monotone ha
  · intro hb
    refine ⟨T.symm b, ?_, T.apply_symm_apply b⟩
    apply (OrderIsoClass.map_le_map_iff T).mp
    rw [T.apply_symm_apply b]
    calc
      T (F_e (T.symm b)) = F_f (T (T.symm b)) := h (T.symm b)
      _ = F_f b := by rw [T.apply_symm_apply b]
      _ ≤ b := hb

/-- C002: least fixed point is preserved under order-isomorphic semiconjugacy.
`T (F_e.lfp) = F_f.lfp` when `T` semiconjugates `F_e` to `F_f`. -/
theorem lfp_of_orderIso_semiconj {F_e : L_e →o L_e} {F_f : L_f →o L_f}
    (T : L_e ≃o L_f) (h : ∀ x, T (F_e x) = F_f (T x)) :
    T (F_e.lfp) = F_f.lfp := by
  change T (sInf {a | F_e a ≤ a}) = sInf {b | F_f b ≤ b}
  rw [map_sInf T {a | F_e a ≤ a}]
  rw [pre_fixedPoints_image_of_orderIso_semiconj T h]

/-- Greatest fixed point analogue: order-isomorphic semiconjugacy preserves `gfp`. -/
theorem gfp_of_orderIso_semiconj {F_e : L_e →o L_e} {F_f : L_f →o L_f}
    (T : L_e ≃o L_f) (h : ∀ x, T (F_e x) = F_f (T x)) :
    T (F_e.gfp) = F_f.gfp := by
  change T (sSup {a | a ≤ F_e a}) = sSup {b | b ≤ F_f b}
  rw [map_sSup T {a | a ≤ F_e a}]
  congr 1
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    calc
      T a ≤ T (F_e a) := T.monotone ha
      _ = F_f (T a) := h a
  · intro hb
    refine ⟨T.symm b, ?_, T.apply_symm_apply b⟩
    apply (OrderIsoClass.map_le_map_iff T).mp
    calc
      T (T.symm b) = b := T.apply_symm_apply b
      _ ≤ F_f b := hb
      _ = F_f (T (T.symm b)) := by rw [T.apply_symm_apply b]
      _ = T (F_e (T.symm b)) := (h (T.symm b)).symm

end ZeroRelative
