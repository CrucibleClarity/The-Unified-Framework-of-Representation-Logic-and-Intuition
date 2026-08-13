/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Order.FixedPoints
import Mathlib.Order.GaloisConnection.Defs
import Mathlib.Order.GaloisConnection.Basic

/-!
# C003: least fixed point is preserved under a Galois connection with one-sided semiconjugacy

Claim ledger C003 (status: CONJECTURE, novelty: NOVELTY_UNASSESSED).
Direction C candidate family C-C2 (weakening conditions for lfp preservation).

Statement (stronger than ledger: any Galois connection, not only insertion):
  Let L_e, L_f be complete lattices, F_e : L_e →o L_e, F_f : L_f →o L_f,
  l : L_e → L_f, u : L_f → L_e with `GaloisConnection l u` (adjunction l ⊣ u).
  If l semiconjugates F_e to F_f one-sidedly (∀ x, l (F_e x) = F_f (l x)),
  then l (F_e.lfp) = F_f.lfp.

Mathlib facts used:
  * `OrderHom.lfp`, `OrderHom.lfp_le`, `OrderHom.le_lfp`, `OrderHom.map_lfp`
    (Mathlib.Order.FixedPoints)
  * `GaloisConnection` and `GaloisConnection.le_iff_le` : l a ≤ b ↔ a ≤ u b
    (Mathlib.Order.GaloisConnection.Defs)

Note: the proof only uses `gc` (adjunction), not the insertion conditions
`u (l x) ≤ x` / `le_l_u`. So the result holds for any Galois connection.

Proof sketch (from C003.yaml):
  1. l a (a = F_e.lfp) is a fixed point of F_f: l (F_e a) = F_f (l a) and F_e a = a,
     so F_f.lfp ≤ l a by lfp_le.
  2. For any prefixpoint b of F_f (F_f b ≤ b):
     l (F_e (u b)) = F_f (l (u b)) ≤ F_f b ≤ b (since l (u b) ≤ b by adjunction,
     F_f monotone, F_f b ≤ b); hence by adjunction F_e (u b) ≤ u b, i.e. u b is a
     prefixpoint of F_e; so F_e.lfp ≤ u b; by adjunction l (F_e.lfp) ≤ b.
  3. Therefore l (F_e.lfp) is the least prefixpoint, equal to F_f.lfp.
-/

namespace ZeroRelative

variable {L_e L_f : Type*} [CompleteLattice L_e] [CompleteLattice L_f]

/-- C003: `l (F_e.lfp) = F_f.lfp` for a Galois connection `l ⊣ u`
with one-sided semiconjugacy `l (F_e x) = F_f (l x)`.
This strengthens the ledger statement (Galois insertion → arbitrary Galois connection). -/
theorem lfp_of_galoisConnection_semiconj (l : L_e → L_f) (u : L_f → L_e)
    (gc : GaloisConnection l u) {F_e : L_e →o L_e} {F_f : L_f →o L_f}
    (h : ∀ x, l (F_e x) = F_f (l x)) :
    l (F_e.lfp) = F_f.lfp := by
  apply le_antisymm
  · -- l (F_e.lfp) ≤ F_f.lfp: l (F_e.lfp) is the least prefixpoint of F_f
    apply F_f.le_lfp
    intro b hb
    rw [gc.le_iff_le]
    apply F_e.lfp_le
    rw [← gc.le_iff_le]
    rw [h (u b)]
    calc
      F_f (l (u b)) ≤ F_f b := F_f.mono ((gc.le_iff_le (a := u b) (b := b)).mpr (le_refl (u b)))
      _ ≤ b := hb
  · -- F_f.lfp ≤ l (F_e.lfp): l (F_e.lfp) is a fixed point of F_f
    have hfix : F_f (l F_e.lfp) = l F_e.lfp := by
      rw [← h F_e.lfp]
      exact congrArg l F_e.map_lfp
    exact F_f.lfp_le_fixed hfix

/-- C003 (insertion version, matches ledger statement): the Galois insertion case
is a special case of the Galois connection theorem. -/
theorem lfp_of_galoisInsertion_semiconj (l : L_e → L_f) (u : L_f → L_e)
    (gi : GaloisInsertion l u) {F_e : L_e →o L_e} {F_f : L_f →o L_f}
    (h : ∀ x, l (F_e x) = F_f (l x)) :
    l (F_e.lfp) = F_f.lfp :=
  lfp_of_galoisConnection_semiconj l u gi.gc h

end ZeroRelative
