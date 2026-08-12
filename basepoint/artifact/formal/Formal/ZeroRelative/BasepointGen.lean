/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Formal.ZeroRelative.Heap
import Formal.ZeroRelative.NatSource
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Abel

/-!
# C010: basepoint-dependent generation law Γ : e ↦ σ_e

Claim ledger C010 (status: PROVED, novelty: KNOWN/DIRECT_COROLLARY).
Branch: basepoint_relativity.

★ VISION: the real research start is the basepoint-dependent generation law
Γ : e ↦ σ_e, and how the minimal closure Chain_e behaves as e varies.

Negative result (now a theorem, R011): pure-heap-endogenous σ_e built from [·,·,·]
with leaves in {e, x} (NO literal 0) have Chain_e structure type INDEPENDENT of e.
Using a literal 0 smuggles in a privileged basepoint (violates "no privileged
basepoint"); the earlier split ([x,x,[x,e,0]] = x - e) is NOT pure-heap endogenous.

★ Mechanism (general term naturality): the basepoint-change transport
T_{e→f}(x) = [x,e,f] is a heap automorphism in ANY heap (the middle para-assoc
form makes the translation a homomorphism). Hence any pure-heap term t(e,x)
satisfies T_{e→f}(t(e,x)) = t(f, T_{e→f}(x)), so Chain(σ_f, f) = T_{e→f}(Chain(σ_e, e))
and the generated structures are isomorphic. This is universal-algebraic
"homomorphism preserves evaluation of terms" — NOT a novel phenomenon.
-/

namespace ZeroRelative

variable {H : Type*} [Heap H]

open Heap

/-- Pure-heap σ_e with leaves in {e, x}: `σ_e(x) = [x, e, x]` (reflection about e;
simplifies to `2x - e` in a group model). Uses ONLY e, x — no literal 0. -/
def reflectGen (e : H) (x : H) : H := heap x e x

/-- Pure-heap σ_e: `σ_e(x) = [x, e, e] = x` (identity; trivial, closure {e}). -/
def identGen (e : H) (x : H) : H := heap x e e

/-- Pure-heap σ_e: `σ_e(x) = [x, x, e] = e` (constant e; closure {e}). -/
def constGen (e : H) (x : H) : H := heap x x e

/-- The integer heap `[x,y,z] = x - y + z` (as a `Heap` instance). -/
instance intHeapInst : Heap ℤ where
  heap := fun x y z => x - y + z
  heap_assoc := by omega
  heap_assoc_mid := by omega
  heap_left_id := by omega
  heap_right_id := by omega

/-- In the group model [x,y,z] = x - y + z, the reflection is `2x - e`:
`[x, e, x] = x - e + x = 2x - e`. -/
theorem reflectGen_group_model (x e : ℤ) :
    reflectGen e x = 2 * x - e := by
  simp [reflectGen, Heap.heap]
  omega

/-- C010: the pure-heap expression family (leaves {e,x}, no literal 0) gives
Chain_e whose structure type is independent of e. Recorded as an OBSERVATION
from enumeration (C010_heap_endogenous.py: 104 expressions on Z/7, 0 e-dependent).
Here we record the concrete pure-heap generators. -/
theorem pure_heap_generators_recorded :
    (∀ e x : H, reflectGen e x = heap x e x) ∧
    (∀ e x : H, identGen e x = x) ∧
    (∀ e x : H, constGen e x = e) := by
  constructor
  · intro e x
    rfl
  · constructor
    · intro e x
      unfold identGen
      exact heap_right_id x e
    · intro e x
      unfold constGen
      exact heap_left_id x e

/-! ## Pure-heap endogenous generation is transport-covariant

The negative result of C010: pure-heap-endogenous σ_e (leaves only {e, x}, no
literal 0) have Chain_e structure type independent of e. The reason is that any
such expression is *transport-covariant*: under the basepoint change transport
T_{e→f}(x) = [x,e,f], the same pure-heap expression renamed e ↦ f satisfies

    T_{e→f}(σ_e(x)) = σ_f(T_{e→f}(x)).

This is a THEOREM (it follows from the heap laws and the purity of the
expression), not an extra equivariance assumption. Hence T_{e→f} restricts to an
isomorphism Chain(σ_e, e) ≅ Chain(σ_f, f), so the structure type cannot depend on e.

The covariance holds for ANY heap: the translation T is a heap homomorphism
via the middle para-assoc form (no commutativity needed). -/

/-- A pure-heap generation expression over a heap variable slot `x` and a
basepoint slot `e`, built from the ternary heap op with leaves `{x, e}` only.
No literal / constant symbol is allowed (a literal `0` would be a privileged
basepoint). -/
inductive PureGen : Type where
  | var : PureGen            -- the running point x
  | bpt : PureGen            -- the basepoint e
  | mix : PureGen → PureGen → PureGen → PureGen   -- [_,_,_]

namespace PureGen

/-- Evaluate a pure-heap generation expression in a heap `H` with a chosen
basepoint `e` and running point `x`. -/
def eval {H : Type*} [Heap H] : PureGen → H → H → H
  | var, _e, x => x
  | bpt, e, _x => e
  | mix a b c, e, x => heap (eval a e x) (eval b e x) (eval c e x)

/-- The basepoint-change transport `T_{e→f}(x) = [x,e,f]`. -/
def transport {H : Type*} [Heap H] (e f x : H) : H := heap x e f

/-- Cancellation: `[[x,e,f],[y,e,f],w] = [x,y,w]` (the e,f translations cancel
between the first two slots). Proved in ANY heap using the middle para-assoc
form: `[ [x,e,f], [y,e,f], w ] = [ x, [ [y,e,f], f, e ], w ]`, and the inner
`[ [y,e,f], f, e ] = y`. -/
lemma cancel {H : Type*} [Heap H] (e f x y w : H) :
    heap (heap x e f) (heap y e f) w = heap x y w := by
  -- [ [x,e,f], [y,e,f], w ] = [ x, [ [y,e,f], f, e ], w ]   (middle para-assoc)
  rw [heap_assoc_mid x e f (heap y e f) w]
  -- [ [y,e,f], f, e ] = [ y, e, [ f, f, e ] ]   (right-nested para-assoc backward)
  rw [heap_assoc'' y e f f e]
  -- [ f, f, e ] = e  (left identity); then [ y, e, e ] = y  (right identity)
  rw [heap_left_id f e, heap_right_id y e]

/-- Transport is a heap homomorphism in ANY heap: `T([x,y,z]) = [T x, T y, T z]`. -/
lemma transport_heap {H : Type*} [Heap H] (e f x y z : H) :
    transport e f (heap x y z) = heap (transport e f x) (transport e f y) (transport e f z) := by
  unfold transport
  -- LHS: [ [x,y,z], e, f ] = [ x, y, [z,e,f] ]  by para-assoc
  rw [heap_assoc'' x y z e f]
  -- RHS: [ [x,e,f], [y,e,f], [z,e,f] ] = [ x, y, [z,e,f] ]  by cancel (backwards)
  rw [← cancel e f x y (heap z e f)]

/-- Transport-covariance: for any pure-heap generation expression, renaming the
basepoint e ↦ f and transporting the running point commute.

    T_{e→f}(σ_e(x)) = σ_f(T_{e→f}(x))

This is the theorem that rules out phenomenon B (basepoint-dependent structure
types) for pure-heap-endogenous laws. Holds in ANY heap. -/
theorem eval_transport {H : Type*} [Heap H] (t : PureGen) (e f x : H) :
    transport e f (eval t e x) = eval t f (transport e f x) := by
  induction t with
  | var =>
      -- T(x) = [x,e,f]; σ_f = x ↦ x; both sides [x,e,f]
      simp [eval, transport]
  | bpt =>
      -- T(e) = [e,e,f] = f by heap_left_id; σ_f = x ↦ f; RHS f
      simp [eval, transport, Heap.heap_left_id]
  | mix a b c ih_a ih_b ih_c =>
      -- T([σ_a,σ_b,σ_c]) = [T σ_a, T σ_b, T σ_c] by transport_heap, and each
      -- T σ_i = σ'_i(T x) by IH.
      simp [eval, transport_heap] at ih_a ih_b ih_c ⊢
      rw [ih_a, ih_b, ih_c]

/-- `T_{e→f}` is invertible, with inverse `T_{f→e}`:
`T_{f→e}(T_{e→f}(x)) = x`. -/
theorem transport_inv {H : Type*} [Heap H] (e f x : H) :
    transport f e (transport e f x) = x := by
  unfold transport
  -- [ [x,e,f], f, e ] = [ x, e, [f,f,e] ]  (para-assoc backward)
  rw [heap_assoc'' x e f f e]
  -- [ f, f, e ] = e (left id); [ x, e, e ] = x (right id)
  rw [heap_left_id f e, heap_right_id x e]

/-- The other direction of invertibility: `T_{e→f}(T_{f→e}(x)) = x`. -/
theorem transport_inv' {H : Type*} [Heap H] (e f x : H) :
    transport e f (transport f e x) = x := by
  unfold transport
  rw [heap_assoc'' x f e e f]
  rw [heap_left_id e f, heap_right_id x f]

/-- `T_{e→f}` is a bijection. -/
theorem transport_bijective {H : Type*} [Heap H] (e f : H) :
    Function.Bijective (transport e f) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    -- apply T_{f→e} to both sides
    have h1 := congrArg (transport f e) hxy
    simp [transport_inv] at h1
    exact h1
  · intro y
    refine ⟨transport f e y, ?_⟩
    simp [transport_inv']

/-- The basepoint moves to the new basepoint: `T_{e→f}(e) = f`. This is the
unit-role naturality of the second review: the "0 of the current basepoint"
(realized as `I_e(0) = e`) transports exactly to the "0 of the new basepoint"
(`I_f(0) = f`), so the diagram (B) `T∘I_e = I_f` commutes for the unit ROLE —
even though the ABSOLUTE point 0 is moved by `T(0) = f - e ≠ 0` in a group
model. This separates VALUE (moves) from STRUCTURAL ROLE (persists). -/
theorem transport_bpt {H : Type*} [Heap H] (e f : H) :
    transport e f e = f := by
  unfold transport
  exact heap_left_id e f

/-- The relative-coordinate observation is equivariant (reviewer's diagram (A)):
`O_f(T_{e→f}(x)) = O_e(x)` where `O_e(x) := x - e` in the group model
`[x,y,z] = x - y + z`. The absolute basepoint cancels; only the relative
position survives the context move. -/
theorem relcoord_equiv {A : Type*} [AddCommGroup A] (e f x : A) :
    (letI : Heap A := {
        heap := fun x y z => x - y + z
        heap_assoc := by
          intro a b c d f
          abel
        heap_assoc_mid := by
          intro a b c d f
          abel
        heap_left_id := by
          intro a b
          abel
        heap_right_id := by
          intro a b
          abel };
      transport e f x) - f = x - e := by
  letI : Heap A := {
    heap := fun x y z => x - y + z
    heap_assoc := by
      intro a b c d f
      abel
    heap_assoc_mid := by
      intro a b c d f
      abel
    heap_left_id := by
      intro a b
      abel
    heap_right_id := by
      intro a b
      abel }
  unfold transport
  simp

/-- Fixed-point transport under conjugacy (third review, point 6): if the
context operators are conjugate `T∘H_e = H_f∘T` with `T : X_e ≃ X_f` an
equivalence, then the fixed-point sets transport exactly: `T(Fix H_e) = Fix H_f`.

This is the baseline: whenever a discovered phenomenon is "fixed-point count is
invariant / fixed-point set transports / fixed points are preserved", check
first whether it is a DIRECT COROLLARY of this conjugacy theorem. Only when
`T∘H_e ≠ H_f∘T` (a genuine transport defect) is there something new. -/
theorem fixed_points_transport {X Y : Type*} (T : X ≃ Y)
    (H_e : X → X) (H_f : Y → Y) (hconj : ∀ x : X, T (H_e x) = H_f (T x)) :
    T '' {x : X | H_e x = x} = {y : Y | H_f y = y} := by
  apply le_antisymm
  · -- forward: T(Fix H_e) ⊆ Fix H_f
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    -- hx : H_e x = x; need H_f (T x) = T x
    change H_f (T x) = T x
    rw [← hconj x]
    exact congrArg T hx
  · -- reverse: Fix H_f ⊆ T(Fix H_e); use T⁻¹.
    intro y hy
    refine ⟨T.symm y, ?_, by simp⟩
    -- show T.symm y ∈ Fix H_e: H_e (T.symm y) = T.symm y
    apply T.injective
    calc
      T (H_e (T.symm y)) = H_f (T (T.symm y)) := hconj (T.symm y)
      _ = H_f y := by simp
      _ = y := hy
      _ = T (T.symm y) := by simp

/-- Corollary: the conjugacy is symmetric under inversion:
`T∘H_e = H_f∘T` iff `T⁻¹∘H_f = H_e∘T⁻¹`. -/
theorem conjugacy_transpose {X Y : Type*} (T : X ≃ Y)
    (H_e : X → X) (H_f : Y → Y) (hconj : ∀ x : X, T (H_e x) = H_f (T x)) :
    ∀ y : Y, T.symm (H_f y) = H_e (T.symm y) := by
  intro y
  apply T.injective
  calc
    T (T.symm (H_f y)) = H_f y := by simp
    _ = T (H_e (T.symm y)) := by
        rw [show T (H_e (T.symm y)) = H_f y from by
          rw [hconj (T.symm y)]
          simp]
    _ = T (H_e (T.symm y)) := rfl

/-- Corollary: the fixed-point transport is symmetric in the two operators
(the conjugacy-equivariant statement bundles both directions). -/
theorem fixed_points_transport' {X Y : Type*} (T : X ≃ Y)
    (H_e : X → X) (H_f : Y → Y) (hconj : ∀ x : X, T (H_e x) = H_f (T x)) :
    T '' {x : X | H_e x = x} = {y : Y | H_f y = y} ∧
    T.symm '' {y : Y | H_f y = y} = {x : X | H_e x = x} := by
  constructor
  · exact fixed_points_transport T H_e H_f hconj
  · -- T⁻¹ (Fix H_f) = Fix H_e via fixed_points_transport on (T⁻¹, H_f, H_e)
    have hconj' : ∀ y : Y, T.symm (H_f y) = H_e (T.symm y) :=
      conjugacy_transpose T H_e H_f hconj
    exact fixed_points_transport T.symm H_f H_e hconj'

/-- Corollary: the closure at f is transported from the closure at e. Since the
transport image of Chain_e is σ_f-closed and contains f = transport e f e,
minimality of Chain_f gives `Chain(σ_f, f) ⊆ transport e f (Chain(σ_e, e))`.
Symmetricly `Chain(σ_e, e) ⊆ transport f e (Chain(σ_f, f))`, so the two minimal
closures are mutually transport-related — the structure type is basepoint-
independent. -/
theorem chain_transport_subset {H : Type*} [Heap H] (t : PureGen) (e f : H) :
    Chain (fun x => eval t f x) f ⊆
      transport e f '' Chain (fun x => eval t e x) e := by
  -- Show the transport image of Chain_e is σ_f-closed and contains f.
  apply chain_minimal
  constructor
  · -- f ∈ transport e f '' Chain_e : take x = e, since e ∈ Chain_e and [e,e,f] = f.
    refine ⟨e, chain_mem_self _ e, ?_⟩
    simp [transport, Heap.heap_left_id]
  · -- image is σ_f-closed: y = transport e f x, x ∈ Chain_e ⟹ σ_f y = transport e f (σ_e x).
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    refine ⟨eval t e x, chain_closed _ e x hx, ?_⟩
    -- T(σ_e(x)) = σ_f(T(x)) by covariance
    exact eval_transport t e f x

/-- Exact transport (R011): `Chain(σ_f, f) = T_{e→f}(Chain(σ_e, e))`.

The subset direction is `chain_transport_subset`. For the reverse, apply the
same argument with e, f swapped and then apply the inverse transport `T_{f→e}`:
`Chain_e ⊆ T_{f→e}(Chain_f)`, and `T_{e→f} ∘ T_{f→e} = id`. -/
theorem chain_transport_eq {H : Type*} [Heap H] (t : PureGen) (e f : H) :
    Chain (fun x => eval t f x) f =
      transport e f '' Chain (fun x => eval t e x) e := by
  apply le_antisymm
  · exact chain_transport_subset t e f
  · -- reverse: T_{e→f} (Chain_e) ⊆ Chain_f
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    -- By the swapped version, Chain_e ⊆ T_{f→e}(Chain_f); so x = T_{f→e}(z)
    -- for some z ∈ Chain_f, and then T_{e→f}(x) = z.
    have hsub : Chain (fun x => eval t e x) e ⊆
        transport f e '' Chain (fun x => eval t f x) f :=
      chain_transport_subset t f e
    have hx' := hsub hx
    rcases hx' with ⟨z, hz, hxz⟩
    -- x = transport f e z  ⟹  transport e f x = z
    have htz : transport e f x = z := by
      rw [← hxz]
      simp [transport_inv']
    rw [htz]
    exact hz

/-- R011 (generated-structure isomorphism): the generated structures at e and f
are isomorphic via the basepoint-change transport. Since `T_{e→f}` is bijective
and `Chain_f = T_{e→f}(Chain_e)`, `T` restricts to a bijection between the two
minimal closures. -/
def generatedStructureEquiv {H : Type*} [Heap H] (t : PureGen) (e f : H) :
    Chain (fun x => eval t e x) e ≃ Chain (fun x => eval t f x) f where
  toFun x := ⟨transport e f x, by
    -- transport e f x ∈ Chain_f follows from chain_transport_subset applied
    -- at the element level via the equality.
    have heq := chain_transport_eq t e f
    rw [heq]
    exact ⟨x, x.2, rfl⟩⟩
  invFun y := ⟨transport f e y, by
    have heq' := chain_transport_eq t f e
    rw [heq']
    exact ⟨y, y.2, rfl⟩⟩
  left_inv x := by
    ext
    simp [transport_inv']
  right_inv y := by
    ext
    simp [transport_inv]

/-- R011: the generated structures are isomorphic (set-level statement). -/
theorem generated_structure_iso {H : Type*} [Heap H] (t : PureGen) (e f : H) :
    Nonempty (Chain (fun x => eval t e x) e ≃ Chain (fun x => eval t f x) f) :=
  ⟨generatedStructureEquiv t e f⟩

/-! ## R012/R013: contextual equivariance

With a context parameter `c` that TRANSPORTS with the basepoint
(`c ↦ T_{e→f}(c)`), the term naturality extends: the context slot is just
another free variable of the pure term. Hence

    T_{e→f}(Γ(e,c,x)) = Γ(f, T_{e→f}(c), T_{e→f}(x))

and the closure is invariant. This is the Model-A (transported anchor) control
case of R012; it restores invariance. A FIXED anchor (c not transported) is the
Model-B case that can break equivariance (R012 enumeration: odd basepoint is
exactly the collision point e = c). -/

/-- A pure-heap term with a context slot `c` (leaves {x, e, c}, no literal). -/
inductive PureGenCtx : Type where
  | var : PureGenCtx            -- the running point x
  | bpt : PureGenCtx            -- the basepoint e
  | ctx : PureGenCtx            -- the context point c
  | mix : PureGenCtx → PureGenCtx → PureGenCtx → PureGenCtx

namespace PureGenCtx

/-- The coefficient triple (α, β, γ) of a term, tracking its value as
`α·x + β·e + γ·c` in a group model: leaves contribute unit triples and `mix`
combines them as `v1 - v2 + v3`. -/
def coeff : PureGenCtx → ℤ × ℤ × ℤ
  | var => (1, 0, 0)
  | bpt => (0, 1, 0)
  | ctx => (0, 0, 1)
  | mix a b c =>
      let (a1, a2, a3) := coeff a
      let (b1, b2, b3) := coeff b
      let (c1, c2, c3) := coeff c
      (a1 - b1 + c1, a2 - b2 + c2, a3 - b3 + c3)

/-- Coefficient-sum lemma: `α + β + γ = 1` for every term (the affine normal
form condition). This is the structural reason no absolute position survives:
each leaf has sum 1, and `mix` preserves sum (1 - 1 + 1 = 1). -/
theorem coeff_sum (t : PureGenCtx) : (coeff t).1 + (coeff t).2.1 + (coeff t).2.2 = 1 := by
  induction t with
  | var => simp [coeff]
  | bpt => simp [coeff]
  | ctx => simp [coeff]
  | mix a b c ih_a ih_b ih_c =>
      -- coeff (mix a b c) = (ca1 - cb1 + cc1, ca2 - cb2 + cc2, ca3 - cb3 + cc3)
      -- sum = (ca1+ca2+ca3) - (cb1+cb2+cb3) + (cc1+cc2+cc3) = 1 - 1 + 1 = 1
      simp [coeff]
      linarith

/-- Evaluate with basepoint `e`, context `c`, running point `x`. -/
def eval {H : Type*} [Heap H] : PureGenCtx → H → H → H → H
  | var, _e, _c, x => x
  | bpt, e, _c, _x => e
  | ctx, _e, c, _x => c
  | mix a b c, e, cc, x => heap (eval a e cc x) (eval b e cc x) (eval c e cc x)

/-- The affine normal form theorem (group model): in an abelian group with the
heap `[x,y,z] = x - y + z`, every contextual pure-heap term evaluates to
`αx + βe + γc`. We prove it by giving the evaluation map on a concrete abelian
group `A` and showing the inductive correspondence with the coefficient triple.

On any additive abelian group `A` with the integer-scaling structure we can
evaluate a term at basepoint `e`, context `c`, running point `x`, and it equals
`α • x + β • e + γ • c`. -/
theorem eval_eq_affine {A : Type*} [AddCommGroup A] (t : PureGenCtx) (e c x : A) :
    (letI : Heap A := {
        heap := fun x y z => x - y + z
        heap_assoc := by
          intro a b c d f
          abel
        heap_assoc_mid := by
          intro a b c d f
          abel
        heap_left_id := by
          intro a b
          abel
        heap_right_id := by
          intro a b
          abel };
      PureGenCtx.eval t e c x) =
      (coeff t).1 • x + (coeff t).2.1 • e + (coeff t).2.2 • c := by
  induction t with
  | var => simp [coeff, PureGenCtx.eval]
  | bpt => simp [coeff, PureGenCtx.eval]
  | ctx => simp [coeff, PureGenCtx.eval]
  | mix a b c ih_a ih_b ih_c =>
      letI : Heap A := {
        heap := fun x y z => x - y + z
        heap_assoc := by intro w x y z u; abel
        heap_assoc_mid := by intro w x y z u; abel
        heap_left_id := by intro w x; abel
        heap_right_id := by intro w x; abel }
      simp [coeff, PureGenCtx.eval]
      -- reduce to: (lhs of ih_a) - (lhs of ih_b) + (lhs of ih_c) = affine
      rw [ih_a, ih_b, ih_c]
      -- expand the ℤ-scaling on the right to per-coordinate terms
      simp [add_zsmul, sub_zsmul]
      abel
/-- Contextual equivariance with TRANSPORTED anchor (Model A):
`T_{e→f}(Γ(e,c,x)) = Γ(f, T_{e→f}(c), T_{e→f}(x))` in any heap.
This is the same term naturality as R011, with the context slot treated as a
free variable. -/
theorem eval_transport_ctx {H : Type*} [Heap H] (t : PureGenCtx) (e f c x : H) :
    transport e f (eval t e c x) = eval t f (transport e f c) (transport e f x) := by
  induction t with
  | var =>
      simp [eval, transport]
  | bpt =>
      simp [eval, transport, Heap.heap_left_id]
  | ctx =>
      -- T(c) = [c,e,f] = T_{e→f}(c); σ_f T(x)... RHS = T(c)
      simp [eval, transport]
  | mix a b c ih_a ih_b ih_c =>
      simp [eval, transport_heap] at ih_a ih_b ih_c ⊢
      rw [ih_a, ih_b, ih_c]

/-- Model-A closure invariance: with a transported anchor, the closure at f is
the transport of the closure at e (exact). -/
theorem chain_transport_eq_ctx {H : Type*} [Heap H] (t : PureGenCtx) (e f c : H) :
    Chain (fun x => eval t f (transport e f c) x) f =
      transport e f '' Chain (fun x => eval t e c x) e := by
  apply le_antisymm
  · -- forward: Chain_{f,T(c)} ⊆ T(Chain_{e,c}); show T(Chain_{e,c}) is
    -- σ_{f,T(c)}-closed and contains f = T(e).
    apply chain_minimal
    constructor
    · refine ⟨e, chain_mem_self _ e, ?_⟩
      simp [transport, Heap.heap_left_id]
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      refine ⟨eval t e c x, chain_closed _ e x hx, ?_⟩
      exact eval_transport_ctx t e f c x
  · -- reverse: T(Chain_{e,c}) ⊆ Chain_{f,T(c)}; show Chain_{e,c} is contained
    -- in the preimage-transported closed set, i.e. Chain_{e,c} ⊆ T_{f→e}(Chain_{f,T(c)})
    -- by minimality of Chain_{e,c}.
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    -- x ∈ Chain_{e,c}. Show Chain_{e,c} ⊆ transport f e '' Chain_{f,T(c)}:
    have hclosed :
        Chain (fun x => eval t e c x) e ⊆
          transport f e '' Chain (fun x => eval t f (transport e f c) x) f := by
      -- T_{f→e}(Chain_{f,T(c)}) contains e and is closed under σ_{e,c}
      apply chain_minimal
      constructor
      · -- e ∈ image: e = transport f e f, and f ∈ Chain_{f,T(c)} (it is the basepoint)
        refine ⟨f, chain_mem_self _ f, ?_⟩
        unfold transport
        -- [f, f, e] = e by left identity
        exact heap_left_id f e
      · -- image closed under σ_{e,c}: y = T_{f→e}(z), z ∈ Chain_{f,T(c)}
        -- ⟹ σ_{e,c}(y) = T_{f→e}(σ_{f,T(c)}(z)) by ctx covariance (e↔f, c↔T(c))
        intro y hy
        rcases hy with ⟨z, hz, rfl⟩
        refine ⟨eval t f (transport e f c) z, chain_closed _ f z hz, ?_⟩
        -- T_{f→e}(σ_{f,T(c)}(z)) = σ_{e,c}(T_{f→e}(z)) : apply ctx transport with
        -- basepoints f→e and context T(c) → c.
        have h := eval_transport_ctx t f e (transport e f c) z
        -- h : transport f e (eval t f (transport e f c) z) =
        --     eval t e (transport f e (transport e f c)) (transport f e z)
        -- simplify transport f e (transport e f c) = c
        simpa [transport_inv'] using h
    have hx' := hclosed hx
    rcases hx' with ⟨z, hz, hxz⟩
    -- x = transport f e z ⟹ T_{e→f}(x) = z
    have htz : transport e f x = z := by
      rw [← hxz]
      simp [transport_inv']
    rw [htz]
    exact hz

/-! ## T2 — Relative-context reduction (second review, 2026-08-07)

In the group model `[x,y,z] = x - y + z`, the affine normal form T1 says
`t(e,c,x) = αx + βe + γc`. Setting `y = x - e` and `d = c - e`, the absolute
positions `e` and `c` cancel:

    t(e,c,x) - e = α·(x-e) + γ·(c-e) = αy + γd.

Only the relative context `d = c - e` survives; the basepoint's absolute
position is irrelevant to the dynamics. -/

/-- T2: relative-context reduction (group model). With `y = x - e` and
`d = c - e`, `eval t e c x - e = α·y + γ·d`, where `(α,γ) = (coeff t).1, (coeff t).2.2`. -/
theorem eval_rel_affine {A : Type*} [AddCommGroup A] (t : PureGenCtx) (e c x : A) :
    (letI : Heap A := {
        heap := fun x y z => x - y + z
        heap_assoc := by
          intro a b c d f
          abel
        heap_assoc_mid := by
          intro a b c d f
          abel
        heap_left_id := by
          intro a b
          abel
        heap_right_id := by
          intro a b
          abel };
      eval t e c x) - e =
      (coeff t).1 • (x - e) + (coeff t).2.2 • (c - e) := by
  letI : Heap A := {
    heap := fun x y z => x - y + z
    heap_assoc := by
      intro a b c d f
      abel
    heap_assoc_mid := by
      intro a b c d f
      abel
    heap_left_id := by
      intro a b
      abel
    heap_right_id := by
      intro a b
      abel }
  -- LHS - e = (αx + βe + γc) - e by T1
  rw [eval_eq_affine t e c x]
  -- αx + βe + γc - e = α(x-e) + γ(c-e) using α+β+γ=1
  have hsum : (coeff t).1 + (coeff t).2.1 + (coeff t).2.2 = 1 := coeff_sum t
  -- (α+β+γ)•e = 1•e = e
  have hone : ((coeff t).1 + (coeff t).2.1 + (coeff t).2.2) • e = e := by
    rw [hsum]
    simp
  -- -e = -(α+β+γ)•e ; this replaces only the bare `-e` (not inside scaled terms)
  have hneg : -e = -(((coeff t).1 + (coeff t).2.1 + (coeff t).2.2) • e) := by
    congr
    exact hone.symm
  -- expand the LHS `... - e` into `... + -e`, then replace the bare `-e`
  conv_lhs => rw [sub_eq_add_neg]; rw [hneg]
  -- (-(α+β+γ))•e = -α•e + -β•e + -γ•e
  have hsplit2 : (-((coeff t).1 + (coeff t).2.1 + (coeff t).2.2)) • e =
      -(coeff t).1 • e + (-(coeff t).2.1 • e + -(coeff t).2.2 • e) := by
    calc
      (-((coeff t).1 + (coeff t).2.1 + (coeff t).2.2)) • e
          = -(((coeff t).1 + (coeff t).2.1 + (coeff t).2.2) • e) := by
            rw [neg_zsmul]
      _ = -((coeff t).1 • e + (coeff t).2.1 • e + (coeff t).2.2 • e) := by
            rw [add_zsmul, add_zsmul]
      _ = -(coeff t).1 • e + (-(coeff t).2.1 • e + -(coeff t).2.2 • e) := by
            rw [neg_add, neg_add]
            simp
            abel
  rw [← neg_zsmul]
  rw [hsplit2]
  -- expand RHS scalings α(x-e), γ(c-e)
  rw [zsmul_sub, zsmul_sub]
  -- turn -n•e into -(n•e) so abel can cancel
  simp [neg_zsmul]
  abel

/-! ## T3 — Automorphism-orbit invariance (second review, 2026-08-07)

In the group model the relative dynamics are `F_d(y) = αy + γd`. Any group
automorphism `φ : A ≃+ A` with `φ d = d'` intertwines the dynamics:

    φ (F_d(y)) = F_{d'}(φ(y))      (conjugacy)

because `φ` commutes with integer scaling and addition. Hence the generated
structure (closure type, cycle structure, fixed points) is preserved under the
Aut-orbit of `d`: `Type(d) = Type(d')`. For cyclic `A = Z/n` this gives the
`gcd(d,n)`-layering observed in R012. -/

/-- T3 (dynamics conjugacy): `φ (F_d y) = F_{φ d} (φ y)` for any automorphism φ
(here `F_d y := αy + γd`; φ commutes with addition and ℤ-scaling). -/
theorem F_d_conjugacy {A : Type*} [AddCommGroup A] (α γ : ℤ) (φ : A ≃+ A)
    (d y : A) :
    φ (α • y + γ • d) = α • φ y + γ • φ d := by
  rw [map_add, map_zsmul, map_zsmul]

/-- Fixed-point transport under conjugacy (group model; third review point 6):
the fixed-point set of `F_d` transports under an automorphism φ to the
fixed-point set of `F_{d'}` when `φ d = d'`. DIRECT COROLLARY of
`fixed_points_transport` (T∘H_e = H_f∘T ⟹ T(Fix H_e) = Fix H_f), NOT a new
phenomenon. -/
theorem fixed_points_aut_orbit {A : Type*} [AddCommGroup A] (α γ : ℤ)
    (φ : A ≃+ A) (d d' : A) (hφd : φ d = d') :
    φ '' {y : A | α • y + γ • d = y} = {y : A | α • y + γ • d' = y} := by
  have hconj : ∀ x : A, φ (α • x + γ • d) = α • φ x + γ • d' := by
    intro x
    rw [F_d_conjugacy α γ φ d x]
    rw [hφd]
  exact fixed_points_transport φ
    (fun y => α • y + γ • d) (fun y => α • y + γ • d') hconj

/-- Corollary: the fixed-point set of the relative dynamics is an Aut-orbit
invariant of the context parameter `d`. This is the "fixed-point observable"
of the second review — verified here to be a DIRECT COROLLARY of the
conjugacy theorem, so it is NOT evidence of a new context-sensitive
phenomenon. -/
theorem fixed_points_aut_orbit_nonempty {A : Type*} [AddCommGroup A] (α γ : ℤ)
    (φ : A ≃+ A) (d d' : A) (hφd : φ d = d') :
    Nonempty {y : A | α • y + γ • d = y} ↔ Nonempty {y : A | α • y + γ • d' = y} := by
  have h := fixed_points_aut_orbit α γ φ d d' hφd
  rw [← h]
  constructor
  · intro hn
    rcases hn with ⟨y, hy⟩
    exact ⟨φ y, y, hy, rfl⟩
  · intro hn
    rcases hn with ⟨z, y, hy, hφz⟩
    exact ⟨y, hy⟩

/-- T3 (automorphism-orbit invariance): if `φ d = d'`, then the minimal closure
of `F_{d'}` at `0` is transported from the closure of `F_d` at `0`.
Equivalently, the generated structure type is constant on the Aut-orbit of `d`. -/
theorem orbit_invariance_chain {A : Type*} [AddCommGroup A] (α γ : ℤ)
    (φ : A ≃+ A) (d d' : A) (hφd : φ d = d') :
    Chain (fun y => α • y + γ • d') 0 ⊆
      φ '' Chain (fun y => α • y + γ • d) 0 := by
  -- Show φ(Chain_d) is F_{d'}-closed and contains 0.
  apply chain_minimal
  constructor
  · -- 0 ∈ φ '' Chain_d : 0 = φ 0 and 0 ∈ Chain_d
    refine ⟨0, chain_mem_self _ 0, ?_⟩
    exact map_zero φ
  · -- φ(Chain_d) closed under F_{d'}: φ y = φ(F_d x) by conjugacy
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    refine ⟨α • x + γ • d, chain_closed _ 0 x hx, ?_⟩
    -- φ (F_d x) = F_{d'} (φ x)
    have h := F_d_conjugacy α γ φ d x
    rw [h]
    rw [hφd]

/-- T3 upgraded to EXACT transport: `φ(Chain_d) = Chain_{d'}` (automorphism-orbit
invariance, equality not just inclusion). Reverse direction via `φ⁻¹`. -/
theorem orbit_invariance_chain_eq {A : Type*} [AddCommGroup A] (α γ : ℤ)
    (φ : A ≃+ A) (d d' : A) (hφd : φ d = d') :
    φ '' Chain (fun y => α • y + γ • d) 0 =
      Chain (fun y => α • y + γ • d') 0 := by
  apply le_antisymm
  · -- forward: φ(Chain_d) ⊆ Chain_{d'}
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    -- use orbit_invariance_chain applied to (d,d'), then extract z
    have hsub := orbit_invariance_chain α γ φ d d' hφd
    -- Chain_{d'} ⊆ φ(Chain_d) gives the reverse; we need φ(Chain_d) ⊆ Chain_{d'}.
    -- Show Chain_{d'} is contained in φ(Chain_d) (hsub), so by applying φ⁻¹ to hsub
    -- we get Chain_d ⊆ φ⁻¹(Chain_{d'}) and hence φ(Chain_d) ⊆ Chain_{d'}.
    -- Direct: z = φ x, x ∈ Chain_d. Use the reverse-inclusion theorem on (d', d, φ⁻¹).
    have hφinv : φ.symm d' = d := by
      -- φ.symm (φ d) = d, and φ d = d'
      rw [← hφd]
      simp
    have hsub' := orbit_invariance_chain α γ (φ.symm) d' d hφinv
    -- hsub' : Chain_d ⊆ φ.symm '' Chain_{d'}
    -- x ∈ Chain_d, so x = φ.symm y for some y ∈ Chain_{d'}; then φ x = y ∈ Chain_{d'}
    have hx' := hsub' hx
    rcases hx' with ⟨y, hy, hxy⟩
    -- hxy : φ.symm y = x  ⟹  φ x = y
    have hφx : φ x = y := by
      rw [← hxy]
      simp
    rw [hφx]
    exact hy
  · -- reverse: Chain_{d'} ⊆ φ(Chain_d) — exactly orbit_invariance_chain
    exact orbit_invariance_chain α γ φ d d' hφd

/-- T3 bundled: the generated systems `(Chain_d, F_d)` and `(Chain_{d'}, F_{d'})`
are isomorphic (as pointed dynamical systems at 0) via the automorphism φ,
whenever `φ d = d'`. -/
def orbitSystemEquiv {A : Type*} [AddCommGroup A] (α γ : ℤ) (φ : A ≃+ A)
    (d d' : A) (hφd : φ d = d') :
    Chain (fun y => α • y + γ • d) 0 ≃ Chain (fun y => α • y + γ • d') 0 where
  toFun y := ⟨φ y, by
    -- φ y ∈ Chain_{d'} via the equality
    have heq := orbit_invariance_chain_eq α γ φ d d' hφd
    rw [← heq]
    exact ⟨y, y.2, rfl⟩⟩
  invFun y := ⟨φ.symm y, by
    have heq' := orbit_invariance_chain_eq α γ φ.symm d' d (by
      -- φ.symm d' = d
      rw [← hφd]
      simp)
    rw [← heq']
    exact ⟨y, y.2, rfl⟩⟩
  left_inv y := by
    ext
    simp
  right_inv y := by
    ext
    simp

/-- T3 (final): the generated structures are isomorphic under the Aut-orbit of d.
`Nonempty` version for convenience. -/
theorem orbit_structure_iso {A : Type*} [AddCommGroup A] (α γ : ℤ)
    (φ : A ≃+ A) (d d' : A) (hφd : φ d = d') :
    Nonempty (Chain (fun y => α • y + γ • d) 0 ≃ Chain (fun y => α • y + γ • d') 0) :=
  ⟨orbitSystemEquiv α γ φ d d' hφd⟩

/-! ## T4 — General automorphism naturality (third review, 2026-08-07)

The non-Abelian probe (S3, D4) showed Aut-orbit invariance survives the loss of
the affine normal form. The reason is universal-algebraic: ANY heap automorphism
preserves ALL term evaluations, commutativity not needed. This closes the
Aut-orbit invariance baseline as a KNOWN / DIRECT_COROLLARY.

    φ ∈ IsHeapAut  ⟹  φ(t(e,c,x)) = t(φe, φc, φx)   for every term t

and consequently the minimal closures transport exactly:

    φ(Chain_{e,c}) = Chain_{φe, φc}                  (generated systems isomorphic).

The context is a tuple `c : κ → H` (any index type, e.g. Fin k), so this covers
single AND multi context uniformly. -/

/-- T4 (naturality): any heap automorphism φ preserves the evaluation of every
pure-heap term, for any context, basepoint, and running point. (Multi-context
follows by treating each context slot as a free variable of the term.) -/
theorem aut_naturality_ctx {H : Type*} [Heap H] (t : PureGenCtx)
    (φ : H → H) (hφ : ZeroRelative.IsHeapAut φ) (e c x : H) :
    φ (eval t e c x) = eval t (φ e) (φ c) (φ x) := by
  induction t with
  | var =>
      simp [eval]
  | bpt =>
      simp [eval]
  | ctx =>
      simp [eval]
  | mix a b c ih_a ih_b ih_c =>
      simp [eval]
      -- φ([A,B,C]) = [φ A, φ B, φ C] by IsHeapAut.map_heap
      rw [hφ.map_heap]
      rw [ih_a, ih_b, ih_c]

/-- T4 (exact transport): `φ(Chain_{e,c}) = Chain_{φe, φc}` for any heap
automorphism φ. -/
theorem aut_chain_eq_ctx {H : Type*} [Heap H] (t : PureGenCtx) (φ : H → H)
    (hφ : ZeroRelative.IsHeapAut φ) (e c : H) :
    φ '' Chain (fun x => eval t e c x) e =
      Chain (fun x => eval t (φ e) (φ c) x) (φ e) := by
  apply le_antisymm
  · -- direction 1: φ(Chain_e) ⊆ Chain_{φe,φc}
    intro x hx
    rcases hx with ⟨w, hw, rfl⟩
    -- Chain_e ⊆ {z | φ z ∈ Chain_{φe,φc}} by minimality
    have hsub : Chain (fun x => eval t e c x) e ⊆
        {z : H | φ z ∈ Chain (fun x => eval t (φ e) (φ c) x) (φ e)} := by
      apply chain_minimal (σ := fun x => eval t e c x) (e := e)
      constructor
      · exact chain_mem_self (fun x => eval t (φ e) (φ c) x) (φ e)
      · intro z hz
        -- hz : z ∈ {z | φ z ∈ Chain σ₂ e₂}; prove φ(σ₁ z) ∈ Chain σ₂ e₂
        change φ (eval t e c z) ∈ Chain (fun x => eval t (φ e) (φ c) x) (φ e)
        rw [aut_naturality_ctx t φ hφ e c z]
        exact chain_closed (fun x => eval t (φ e) (φ c) x) (φ e) (φ z) hz
    exact hsub hw
  · -- direction 2: Chain_{φe,φc} ⊆ φ(Chain_e)
    apply chain_minimal (σ := fun x => eval t (φ e) (φ c) x) (e := φ e)
      (C := φ '' Chain (fun x => eval t e c x) e)
    constructor
    · refine ⟨e, chain_mem_self (fun x => eval t e c x) e, ?_⟩
      rfl
    · intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      refine ⟨eval t e c w, chain_closed (fun x => eval t e c x) e w hw, ?_⟩
      -- σ₂(φ w) = φ(σ₁ w) : naturality gives φ(σ₁ w) = σ₂(φ w)
      exact aut_naturality_ctx t φ hφ e c w

/-- T4 bundled: the generated systems `(Chain_{e,c}, σ_{e,c})` and
`(Chain_{φe,φc}, σ_{φe,φc})` are isomorphic (as pointed systems at the basepoint)
under any heap automorphism φ. -/
noncomputable def autSystemEquiv {H : Type*} [Heap H] (t : PureGenCtx) (φ : H → H)
    (hφ : ZeroRelative.IsHeapAut φ) (e c : H) :
    Chain (fun x => eval t e c x) e ≃
      Chain (fun x => eval t (φ e) (φ c) x) (φ e) := by
  -- Use the exact chain equality + bijectivity of φ to build the equivalence.
  let f : Chain (fun x => eval t e c x) e → Chain (fun x => eval t (φ e) (φ c) x) (φ e) :=
    fun x => ⟨φ x, by
      have heq := aut_chain_eq_ctx t φ hφ e c
      rw [← heq]
      exact ⟨x, x.2, rfl⟩⟩
  refine Equiv.ofBijective f ?_
  constructor
  · -- injective
    intro x y hxy
    apply Subtype.ext
    exact hφ.bijective.1 (congrArg Subtype.val hxy)
  · -- surjective
    intro y
    -- y : Chain σ₂ e₂; pick preimage x under φ
    rcases hφ.bijective.2 y.1 with ⟨x, hxy⟩
    -- show x ∈ Chain σ₁ e₁
    have hx : x ∈ Chain (fun x => eval t e c x) e := by
      have heq := aut_chain_eq_ctx t φ hφ e c
      -- φ x ∈ Chain σ₂  (given), and Chain σ₂ = φ '' Chain σ₁
      have hφx : φ x ∈ Chain (fun x => eval t (φ e) (φ c) x) (φ e) := by
        rw [hxy]
        exact y.2
      -- φ x ∈ φ '' Chain σ₁ : get witness z with φ z = φ x; injectivity gives z = x
      have hφx' : φ x ∈ φ '' Chain (fun x => eval t e c x) e := by
        rw [heq]
        exact hφx
      rcases hφx' with ⟨z, hz, hφz⟩
      -- φ z = φ x ⟹ z = x
      have hzx : z = x := hφ.bijective.1 hφz
      rwa [← hzx]
    refine ⟨⟨x, hx⟩, ?_⟩
    ext
    exact hxy

/-- T4 (final): the generated structures are isomorphic under any heap
automorphism. `Nonempty` version. -/
theorem aut_structure_iso {H : Type*} [Heap H] (t : PureGenCtx) (φ : H → H)
    (hφ : ZeroRelative.IsHeapAut φ) (e c : H) :
    Nonempty (Chain (fun x => eval t e c x) e ≃
      Chain (fun x => eval t (φ e) (φ c) x) (φ e)) :=
  ⟨autSystemEquiv t φ hφ e c⟩

/-! ## T5 — Context sufficiency (fourth review, 2026-08-07)

The review reframes the question: not "how many context points" but whether the
context is *sufficiently representable* — a factorization problem.

Real generation: `Γ(e, E, x)` with environment `E`. An observer keeps only
`q(e, E) = z`. `q` is a *sufficient representation* iff there is `Γ̄` with

    Γ(e, E, x) = Γ̄(q(e, E), x)      for all states.

For single context (Abelian): `q(e,c) = c - e` is sufficient for the RELATIVE
dynamics — in relative coordinates `y = x - e, d = c - e` the system becomes
autonomous `(y,d) ↦ (y',d')` with `y' = αy + γd`. Two environments with the same
`(x-e, c-e)` have identical relative evolution. This is exactly T2
(`eval_rel_affine`) restated as a sufficiency statement.

A sufficient invariant stops the search: no further context points are needed
once `q` captures the relational role. -/

/-- T5: single-context sufficiency. If two environments `(e,c)` and `(e',c')`
have the same relative state `(x-e, c-e)`, then the relative evolution is
identical: `Γ(e,c,x) - e = Γ(e',c',x') - e'`. Hence `q(e,c) = c-e` is a
sufficient representation of the relative dynamics. -/
theorem rel_dynamics_sufficient {A : Type*} [AddCommGroup A] (t : PureGenCtx)
    (e c e' c' x x' : A) (hrel : x - e = x' - e') (hd : c - e = c' - e') :
    (letI : Heap A := {
        heap := fun x y z => x - y + z
        heap_assoc := by
          intro a b c d f
          abel
        heap_assoc_mid := by
          intro a b c d f
          abel
        heap_left_id := by
          intro a b
          abel
        heap_right_id := by
          intro a b
          abel };
      eval t e c x) - e =
    (letI : Heap A := {
        heap := fun x y z => x - y + z
        heap_assoc := by
          intro a b c d f
          abel
        heap_assoc_mid := by
          intro a b c d f
          abel
        heap_left_id := by
          intro a b
          abel
        heap_right_id := by
          intro a b
          abel };
      eval t e' c' x') - e' := by
  -- both sides equal α(x-e) + γ(c-e) by T2, which agree by hypotheses
  rw [eval_rel_affine t e c x]
  rw [eval_rel_affine t e' c' x']
  rw [hrel, hd]

end PureGenCtx

end PureGen

end ZeroRelative
