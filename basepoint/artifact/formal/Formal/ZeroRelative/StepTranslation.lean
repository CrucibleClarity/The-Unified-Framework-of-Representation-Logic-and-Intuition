/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Formal.ZeroRelative.Heap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ByContra
import Mathlib.Data.Int.Basic

/-!
# C006: basepoint-relative step translation and its transport in a heap

Claim ledger C006 (status: PROVED, novelty: DIRECT_COROLLARY / KNOWN).
Branch: basepoint_relativity.

The basepoint-relative step TRANSLATION: `τ_{e,a}(x) = [x, e, a]` (in the retract
group `G_e` this is `x ↦ x +_e a` — a translation, NOT a Peano successor), and
basepoint change `T_{e→f}(x) = [x, e, f]`.

Main theorem (transport, holds in ANY heap, not only abelian):
  `T_{e→f} (τ_{e,a} x) = τ_{f, T_{e→f}(a)} (T_{e→f} x)`.
That is, the endpoint `a` must be transported to `T_{e→f}(a) = [a,e,f]`.
Proof uses only para-associativity and the identity laws; no commutation.

Interpretation: `a` is "the endpoint representing a step when `e` is the origin";
`T_{e→f}(a)` is "the endpoint representing the SAME step when `f` is the origin".
The invariant is the relative displacement `(e, a)`, not `a` itself.

This is a direct corollary of the standard fact that a heap translation is a heap
morphism: `T_{e→f}` is a heap automorphism with `T_{e→f}(e) = f`, so
`T_{e→f}([x,e,a]) = [T_{e→f}(x), f, T_{e→f}(a)]`.

Counterexample (same endpoint, no transport): in ℤ-heap `[x,y,z]=x-y+z`,
`e=0,f=1,a=2,x=0` gives `[[0,0,2],0,1]=3 ≠ [[0,0,1],1,2]=2`. A NON-abelian heap
(any non-commutative group `[x,y,z]=x y⁻¹ z`) also distinguishes `[a,e,f]` from
`[f,e,a]` — so this is why the plain `Heap` hypothesis is the right level.
-/

namespace ZeroRelative

variable {H : Type*} [Heap H]

open Heap

/-- The basepoint-relative step translation at basepoint `e` with endpoint `a`:
`τ_{e,a}(x) = [x, e, a]` (translation `x ↦ x +_e a` in the retract group). -/
def stepTranslation (e a : H) (x : H) : H := heap x e a

/-- Basepoint change: `T_{e→f}(x) = [x, e, f]`. -/
def bpChange (e f : H) (x : H) : H := heap x e f

/-- C006: the step translation is transported under basepoint change,
`T_{e→f} (τ_{e,a} x) = τ_{f, T_{e→f}(a)} (T_{e→f} x)`, in any heap.
This is the naturality of heap translations (a direct corollary of `T_{e→f}`
being a heap morphism). -/
theorem step_transport (e f a x : H) :
    bpChange e f (stepTranslation e a x) = stepTranslation f (bpChange e f a) (bpChange e f x) := by
  unfold stepTranslation bpChange
  -- LHS: [ [x,e,a], e, f ] = [ x, e, [a,e,f] ]  (para-assoc backward)
  rw [heap_assoc'' x e a e f]
  -- RHS: [ [x,e,f], f, [a,e,f] ] = [ x, e, [ f, f, [a,e,f] ] ]  (para-assoc backward)
  rw [heap_assoc'' x e f f (heap a e f)]
  -- [ f, f, [a,e,f] ] = [a,e,f]  (left identity)
  rw [heap_left_id f (heap a e f)]

/-- `T_{e→f}` sends the basepoint to the new basepoint: `T_{e→f}(e) = f`. -/
theorem bpChange_basepoint (e f : H) : bpChange e f e = f := by
  unfold bpChange
  exact heap_left_id e f

/-- The same-endpoint (untransported) version fails in general.
Witness: `ℤ` with the abelian heap `[x,y,z]=x-y+z`, `e=0, f=1, a=2, x=0`:
LHS = `[[0,0,2],0,1] = 3`, RHS = `[[0,0,1],1,2] = 2`. `3 ≠ 2`. -/
theorem step_transport_same_endpoint_not_general :
    letI : AbelianHeap ℤ := {
      heap := fun x y z => x - y + z
      heap_assoc := by omega
      heap_assoc_mid := by omega
      heap_left_id := by omega
      heap_right_id := by omega
      heap_comm := by omega }
    bpChange (0 : ℤ) 1 (stepTranslation 0 2 0) ≠ stepTranslation 1 2 (bpChange (0 : ℤ) 1 0) := by
  letI : AbelianHeap ℤ := {
      heap := fun x y z => x - y + z
      heap_assoc := by omega
      heap_assoc_mid := by omega
      heap_left_id := by omega
      heap_right_id := by omega
      heap_comm := by omega }
  change (0 - 0 + 2 - 0 + 1) ≠ (0 - 0 + 1 - 1 + 2)
  norm_num

end ZeroRelative
