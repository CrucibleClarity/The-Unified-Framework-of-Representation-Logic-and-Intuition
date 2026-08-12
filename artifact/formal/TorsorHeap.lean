/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Algebra.Torsor.Basic
import Formal.ZeroRelative.Heap

/-!
# C005: Torsor-heap correspondence — directed constructions and round trips

Claim ledger C005 (status: PROVED, novelty: KNOWN).
Branch: basepoint_relativity (模型 II).

We use `Mathlib.Algebra.Torsor.*`. The old module path `Mathlib.Algebra.AddTorsor.*`
is deprecated; the `AddTorsor` typeclass itself is NOT deprecated and lives in
`Mathlib.Algebra.Torsor.*`.

Structure (per review):

* Direction A — Torsor → Heap: `(G,P,torsor) ↦ (P, [·,·,·])` with
  `[x,y,z] = (x -ᵥ y) +ᵥ z` (additive) / `(x /ₛ y) • z` (multiplicative),
  mirroring `x·y⁻¹·z`.
* Direction B — Pointed Heap → Group: `(H, [·,·,·], e) ↦ G_e` with
  `x +_e y = [x,e,y]`, `-_e y = [e,y,e]` (C004).
* Direction C — Pointed Heap → Self-torsor: `G_e ↷ H`.

Round-trip 1 (C005a): Heap → retract at e → induced heap recovers the ORIGINAL
heap exactly (equality of ternary operations), via `[x,e,[e,y,e]] = [x,y,e]`
and `[[x,y,e],e,z] = [x,y,z]`.

Round-trip 2 (C005b): AddTorsor G P → Heap P → retract at e produces a group
canonically isomorphic to G via `x ↦ x -ᵥ e` (NOT equal: carriers may differ).
-/

namespace ZeroRelative

open Function

section Dir1

/-! ## Direction A: a torsor induces a heap -/

variable {G : Type*} [CommGroup G] [Torsor G P]

/-- The heap operation on `P` induced by a torsor: `[x,y,z] = (x /ₛ y) • z`
(mirroring `x·y⁻¹·z` in a group: the group element `x /ₛ y` acts on point `z`). -/
def torsorHeap (x y z : P) : P := (x /ₛ y) • z

theorem torsorHeap_left_id (x y : P) : torsorHeap x x y = y := by
  -- [x,x,y] = (x /ₛ x) • y = 1 • y = y
  rw [torsorHeap, sdiv_self, one_smul]

theorem torsorHeap_right_id (x y : P) : torsorHeap x y y = x := by
  -- [x,y,y] = (x /ₛ y) • y = x  by sdiv_smul'
  simp [torsorHeap]

theorem torsorHeap_assoc (a b c d f : P) :
    torsorHeap a b (torsorHeap c d f) = torsorHeap (torsorHeap a b c) d f := by
  -- LHS: (a /ₛ b) • ((c /ₛ d) • f) = ((a /ₛ b) * (c /ₛ d)) • f  [smul_smul]
  -- RHS: (((a /ₛ b) • c) /ₛ d) • f = ((a /ₛ b) * (c /ₛ d)) • f  [smul_sdiv_assoc]
  unfold torsorHeap
  rw [smul_smul]
  congr 1
  rw [← smul_sdiv_assoc]

theorem torsorHeap_comm (a b c : P) : torsorHeap a b c = torsorHeap c b a := by
  -- [a,b,c] = (a /ₛ b) • c ; [c,b,a] = (c /ₛ b) • a
  -- sdiv_smul_comm : (p₁/p₂) • p₃ = (p₃/p₂) • p₁ gives exactly [a,b,c] = [c,b,a]
  unfold torsorHeap
  exact sdiv_smul_comm a b c

/-- Direction A statement (C005): the heap operation `(x /ₛ y) • z` induced by a torsor
satisfies the abelian heap axioms (left/right identity, para-associativity, commutation). -/
theorem torsor_induces_abelianHeap (G : Type*) {P : Type*} [CommGroup G] [Torsor G P] :
    (∀ x y : P, torsorHeap x x y = y) ∧
    (∀ x y : P, torsorHeap x y y = x) ∧
    (∀ a b c d f : P, torsorHeap a b (torsorHeap c d f) = torsorHeap (torsorHeap a b c) d f) ∧
    (∀ a b c : P, torsorHeap a b c = torsorHeap c b a) :=
  ⟨torsorHeap_left_id, torsorHeap_right_id, torsorHeap_assoc, torsorHeap_comm⟩

end Dir1

section Dir2

/-! ## Direction B + C: heap + chosen basepoint gives group and self-torsor -/

variable {H : Type*} [AbelianHeap H]

open AbelianHeap

/-- The additive group law on `H` with identity `e` (from C004): `x +_e y = [x,e,y]`. -/
def addAt (e : H) (x y : H) : H := Heap.heap x e y

/-- The additive inverse w.r.t. `e`: `-x := [e,x,e]`. -/
def negAt (e : H) (x : H) : H := Heap.heap e x e

/-- The vsub operation of the retracted torsor: `x -ᵥ y := x +_e (-_e y)`. -/
def retractVsub (e : H) (x y : H) : H := addAt e x (negAt e y)

/-- The vadd operation: `g +ᵥ x := g +_e x`. -/
def retractVadd (e : H) (g x : H) : H := addAt e g x

/-- Direction 2 (C005), torsor cancellation laws as propositions:
with the retracted group `G_e = (H, +_e, e)` from C004, the operations
`retractVsub` / `retractVadd` satisfy the two `AddTorsor` cancellation laws
`(p₁ -ᵥ p₂) +ᵥ p₂ = p₁` and `(g +ᵥ p) -ᵥ p = g`. -/
theorem heap_retract_torsor_cancel (e : H) :
    (∀ p₁ p₂ : H, retractVadd e (retractVsub e p₁ p₂) p₂ = p₁) ∧
    (∀ g p : H, retractVsub e (retractVadd e g p) p = g) := by
  constructor
  · intro p₁ p₂
    unfold retractVadd retractVsub addAt negAt
    -- goal: heap (heap p₁ e (heap e p₂ e)) e p₂ = p₁
    -- para-assoc (backward): heap (heap a b c) d f = heap a b (heap c d f)
    rw [Heap.heap_assoc'' p₁ e (Heap.heap e p₂ e) e p₂]
    -- goal: heap p₁ e (heap (heap e p₂ e) e p₂) = p₁
    -- inner: heap (heap e p₂ e) e p₂ = heap e p₂ (heap e e p₂) (para-assoc back)
    rw [Heap.heap_assoc'' e p₂ e e p₂]
    -- inner: heap e p₂ (heap e e p₂) ; heap e e p₂ = p₂ [left_id]; heap e p₂ p₂ = e [right_id]
    rw [Heap.heap_left_id e p₂]
    rw [Heap.heap_right_id e p₂]
    -- goal: heap p₁ e e = p₁ [right_id]
    exact Heap.heap_right_id p₁ e
  · intro g p
    unfold retractVadd retractVsub addAt negAt
    -- goal: heap (heap g e p) e (heap e p e) = g
    -- para-assoc (backward), a=g, b=e, c=p, d=e, f=heap e p e:
    rw [Heap.heap_assoc'' g e p e (Heap.heap e p e)]
    -- goal: heap g e (heap p e (heap e p e)) = g
    -- inner: heap p e (heap e p e) = heap (heap p e e) p e [para-assoc, a=p,b=e,c=e,d=p,f=e]
    rw [Heap.heap_assoc p e e p e]
    -- inner: heap (heap p e e) p e ; heap p e e = p [right_id]; heap p p e = e [left_id]
    rw [Heap.heap_right_id p e]
    rw [Heap.heap_left_id p e]
    -- goal: heap g e e = g [right_id]
    exact Heap.heap_right_id g e

end Dir2

section RoundTrip

/-! ## Round-trip 1 (C005a): Heap → retract at e → induced heap recovers the heap -/

variable {H : Type*} [AbelianHeap H]

open AbelianHeap

/-- In the retracted group `G_e`, subtraction is `x -_e y = [x, e, [e, y, e]] = [x, y, e]`.
This is the key computation behind round-trip 1. -/
theorem retract_sub_eq (e x y : H) : addAt e x (negAt e y) = Heap.heap x y e := by
  unfold addAt negAt
  -- heap x e (heap e y e) = heap (heap x e e) y e  [para-assoc]
  rw [Heap.heap_assoc x e e y e]
  -- heap (heap x e e) y e : heap x e e = x [right_id]
  rw [Heap.heap_right_id x e]

/-- C005a (round-trip 1): re-applying the torsor-induced heap to the retracted group
recovers the ORIGINAL heap exactly: `(x -_e y) +_e z = [x, y, z]`. -/
theorem heap_retract_induced_heap_eq (e x y z : H) :
    retractVadd e (retractVsub e x y) z = Heap.heap x y z := by
  -- (x -_e y) +_e z = [x, y, e] +_e z = [[x,y,e], e, z] = [x,y,[e,e,z]] = [x,y,z]
  unfold retractVadd retractVsub
  rw [retract_sub_eq]
  unfold addAt
  -- heap (heap x y e) e z = heap x y (heap e e z)  [para-assoc back]
  rw [Heap.heap_assoc'' x y e e z]
  -- heap e e z = z [left_id]
  rw [Heap.heap_left_id e z]

end RoundTrip

section RoundTrip2

/-! ## Round-trip 2 (C005b): AddTorsor G P → Heap → retract at e gives a group ≅ G -/

variable {G : Type*} [AddCommGroup G] [AddTorsor G P]

/-- The retracted group law on `P` at basepoint `e`, pushed to `G` via `φ_e x = x -ᵥ e`:
`φ_e (x +_e y) = (x -ᵥ e) + (y -ᵥ e)`. This is the homomorphism property of the
canonical isomorphism `G_e ≅ G`. -/
theorem retract_add_pushed (e x y : P) :
    ((x -ᵥ e) +ᵥ y) -ᵥ e = (x -ᵥ e) + (y -ᵥ e) := by
  rw [vadd_vsub_assoc]

/-- The canonical map `φ_e : P → G`, `x ↦ x -ᵥ e`, has right inverse `g ↦ g +ᵥ e`
(on the retracted group `G_e`), so `φ_e` is a bijection `G_e ≅ G`. -/
theorem retract_canonical_bij (e : P) :
    (∀ g : G, (g +ᵥ e) -ᵥ e = g) ∧ (∀ x : P, ((x -ᵥ e) +ᵥ e) = x) := by
  constructor
  · intro g
    rw [vadd_vsub]
  · intro x
    rw [vsub_vadd]

/-- C005b (round-trip 2): the retracted group `G_e` over the torsor-induced heap is
canonically isomorphic to the original group `G` via `φ_e x = x -ᵥ e`:
`φ_e` preserves the retracted addition (homomorphism property) and is a bijection. -/
theorem torsor_retract_group_iso (e : P) :
    (∀ x y : P, ((x -ᵥ e) +ᵥ y) -ᵥ e = (x -ᵥ e) + (y -ᵥ e)) ∧
    (∀ g : G, (g +ᵥ e) -ᵥ e = g) ∧
    (∀ x : P, ((x -ᵥ e) +ᵥ e) = x) := by
  constructor
  · intro x y
    exact retract_add_pushed e x y
  · exact retract_canonical_bij e

end RoundTrip2

end ZeroRelative
