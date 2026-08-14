/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Data.Int.Basic

/-!
# C007: Displacement equivalence and the basepoint-free change space

Claim ledger C007 (status: PROVED on the group model ℤ, novelty: KNOWN).
Branch: basepoint_relativity.

On a heap `H` (here the group model `ℤ` with `[x,y,z] = x - y + z`), define
displacement equivalence:
  `(e,a) ∼ (f,b) :⟺ b = [a,e,f] = a - e + f`.
That is, `(f, b)` represents the SAME relative displacement as `(e,a)` after
basepoint change `e ↦ f`.

Facts (verified here on the ℤ model):
* ∼ is an equivalence relation (reflexive / symmetric / transitive).
* For each fixed basepoint `e`, the map `a ↦ a - e` (the "relative displacement"
  coordinate) is a bijection `H → H`, so the change space recovers the group
  `G_e` — the quotient classes are in bijection with the acting group.

Interpretation: a single "numerical point" `a` is NOT basepoint-invariant; the
invariant is the relative displacement `(e,a)` (equivalently the translation
`τ_{e,a} : x ↦ x +_e a`). Choosing a basepoint trivializes the change space back
into the group. This matches the classical torsor / translation-group picture,
so novelty is KNOWN (a baseline for later: defining iteration on this
basepoint-free change space).
-/

namespace ZeroRelative

/-- Abelian heap on `ℤ`: `[x,y,z] = x - y + z`. -/
def intHeap (x y z : ℤ) : ℤ := x - y + z

/-- Displacement equivalence on the model: `(e,a) ∼ (f,b) :⟺ b = [a,e,f]`. -/
def dispRel (e a f b : ℤ) : Prop := b = intHeap a e f

theorem dispRel_def (e a f b : ℤ) : dispRel e a f b ↔ b = a - e + f := by
  rfl

/-- Reflexivity: `(e,a) ∼ (e,a)`. -/
theorem dispRel_refl (e a : ℤ) : dispRel e a e a := by
  unfold dispRel intHeap
  omega

/-- Symmetry: `(e,a) ∼ (f,b) → (f,b) ∼ (e,a)`. -/
theorem dispRel_symm : ∀ {e a f b : ℤ}, dispRel e a f b → dispRel f b e a := by
  intro e a f b h
  rw [dispRel_def] at h ⊢
  -- h : b = a - e + f ; want a = b - f + e
  calc
    a = (a - e + f) - f + e := by omega
    _ = b - f + e := by rw [h]

/-- Transitivity: `(e,a) ∼ (f,b)` and `(f,b) ∼ (g,c)` imply `(e,a) ∼ (g,c)`. -/
theorem dispRel_trans :
    ∀ {e a f b g c : ℤ}, dispRel e a f b → dispRel f b g c → dispRel e a g c := by
  intro e a f b g c h1 h2
  rw [dispRel_def] at h1 h2 ⊢
  -- h1 : b = a - e + f ; h2 : c = b - f + g ; want c = a - e + g
  calc
    c = b - f + g := h2
    _ = (a - e + f) - f + g := by rw [h1]
    _ = a - e + g := by omega

/-- C007: displacement equivalence is an equivalence relation on `ℤ × ℤ`. -/
theorem dispRel_is_equivalence : Equivalence fun p q : ℤ × ℤ => dispRel p.1 p.2 q.1 q.2 :=
  ⟨fun p => dispRel_refl p.1 p.2,
   fun h => dispRel_symm h,
   fun h1 h2 => dispRel_trans h1 h2⟩

/-- For each fixed basepoint `e`, the relative-displacement coordinate `a ↦ a - e`
is a bijection `ℤ → ℤ`, so the change space recovers the group `G_e`. -/
theorem displacement_coord_bijective (e : ℤ) : Function.Bijective (fun a : ℤ => a - e) := by
  refine ⟨?injective, ?surjective⟩
  · intro a b h
    change a - e = b - e at h
    omega
  · intro d
    refine ⟨d + e, ?_⟩
    change (d + e) - e = d
    omega

end ZeroRelative
