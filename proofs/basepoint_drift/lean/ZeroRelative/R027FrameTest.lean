/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Data.ZMod.Basic

/-!
# R027 — Frame test: (V,J) = latent line structure, u = frame/trivialization

Ninth review (2026-08-07), sealing R026:

The (V, J, u) control is best read as: (V, J) with J² = -I is a 1-dim F_9
vector space; V∖{0} is an F_9ˣ-torsor; a nonzero basepoint u is a choice of
frame/basis:

    φ_u : F_9 ≃ V, z ↦ z·u

Changing basepoint u ↦ u' = a·u is a frame/gauge change with
T(v) = a·v (scalar multiplication by the ratio u'/u), satisfying
T∘J = J∘T and T(v ∗_u w) = T(v) ∗_{u'} T(w).  Hence the field structures are
isomorphic via a NATURAL frame-change map, not "accidentally".

VALUE/ROLE: J as an operator is unchanged; the point representing α ∈ F_9 in
the concrete field (V, ∗_u) is α_u = J(u) (since φ_u(α) = α·u = J(u)), and
under frame change J(u) ↦ J(u').  So VALUE of α moves, ROLE "multiplication
by α" persists.

The Frame Test (L4 in the compression ladder): for a family Γ_u, FIRST ask
whether ∃ φ_u : L → X_u and a common Γ* : L → L with Γ_u = φ_u ∘ Γ* ∘ φ_u⁻¹.
If so, the apparent Γ_u ≠ Γ_f is just a coordinate expression difference
([Γ_e] = [Γ_f] under the natural frame change).  Genuine regeneration requires
an intrinsic invariant to actually change.

This file formalizes the four sealing theorems (KNOWN frame/torsor benchmark).

NOTE on proof style: the theorems are closed propositions over the finite set
V = F_3 × F_3 (9 elements), so a single `native_decide` on the whole `∀`
suffices and is fast.  Do NOT use `fin_cases` + `native_decide` per variable
(that expands to 9^k subgoals, and `native_decide` on a goal with free
variables errors).  Do NOT implement the field inverse via `List.find?` (the
dependence on proof terms in the predicate makes `native_decide` unable to
generate code, which HANGS the compile).  Use a plain arithmetic inverse table
`finv2` with an explicit `u ≠ 0` hypothesis.

Conventions: V = F_3 × F_3 is both the carrier and the reference field F_9
((a,b)·(c,d) = (ac - bd, ad + bc), α² = -1).  The field structure on V with
unit u is the teleported multiplication v ∗_u w = v·w·u⁻¹ (u is the
multiplicative identity of (V,∗_u)).
-/

namespace R027

abbrev V := ZMod 3 × ZMod 3

/-- J(v) = (-b, a): multiply by α (the complex-like i).  J² = -I. -/
def Jv (v : V) : V := (-v.2, v.1)

/-- The abstract element α ∈ F_9 (α² + 1 = 0). -/
def alpha : V := (0, 1)

/-- F_9 multiplication on pairs (a,b)·(c,d) = (ac - bd, ad + bc), α² = -1. -/
def fmul (a b : V) : V := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

/-- Field inverse in F_9 as a plain arithmetic table (F_9ˣ cyclic of order 8).
Chosen over `List.find?` so that `native_decide` can generate code for it. -/
def finv2 (u : V) : V :=
  if u = (1, 0) then (1, 0) else if u = (2, 0) then (2, 0)
  else if u = (0, 1) then (0, 2) else if u = (1, 1) then (2, 1)
  else if u = (2, 1) then (1, 1) else if u = (0, 2) then (0, 1)
  else if u = (1, 2) then (2, 2) else if u = (2, 2) then (1, 2)
  else (0, 0)

/-- The frame map φ_u(z) = z·u (scalar action).  For u ≠ 0 this is a bijection
F_9 ≃ V: u is a singleton basis of the 1-dim F_9-space. -/
def phi (u z : V) : V :=
  (z.1 * u.1 - z.2 * u.2, z.1 * u.2 + z.2 * u.1)

/-- The teleported field multiplication on V with unit u:
v ∗_u w = v·w·u⁻¹, so that u is the identity of (V, ∗_u). -/
def star (u v w : V) : V := fmul (fmul v w) (finv2 u)

/-- Nonzero elements of F_9 have multiplicative inverses (computed by `finv2`).
This is the arithmetic fact underneath the frame statement, kept separate so the
theorem NAME matches its STATEMENT: it does NOT by itself claim "u is a frame".
The frame claim (φ_u bijective / singleton basis) is `phi_bijective`. -/
theorem nonzero_has_inverse : ∀ u : V, u ≠ (0, 0) →
    fmul u (finv2 u) = (1, 0) := by
  native_decide

/-- Nonzero basepoints ARE frames: φ_u(z) = z·u is a bijection F_9 ≃ V for every
u ≠ 0, i.e. u is a singleton basis / frame of the 1-dim F_9-space V.  This is
the proper "nonzero u is a frame" statement (bijective linear map), NOT merely
the inverse-existence arithmetic.  Decided on the finite 9-element carrier. -/
theorem phi_bijective : ∀ u : V, u ≠ (0, 0) → Function.Bijective (phi u) := by
  native_decide

/-- Frame change T = scalar multiplication by a commutes with J: T∘J = J∘T.
(α·a = a·α in the commutative field F_9.) -/
theorem frame_commutes_J : ∀ a v : V, phi a (Jv v) = Jv (phi a v) := by
  native_decide

/-- Frame change is a FIELD isomorphism: T(v ∗_u w) = T(v) ∗_{a·u} T(w) where
T(x) = a·x.  Here T(x) = phi a x and u' = a·u.  (a = 0 gives the degenerate
map; the genuine frame changes are a ≠ 0.) -/
theorem frame_field_iso : ∀ a u v w : V,
    phi a (star u v w) = star (phi a u) (phi a v) (phi a w) := by
  native_decide

/-- VALUE of α moves with the frame: the point representing α ∈ F_9 in frame u
is α_u = J(u) = φ_u(α); in frame u' it is J(u').  ROLE "multiplication by α"
persists (the operator J is the same). -/
theorem alpha_value_moves : ∀ u : V, Jv u = phi u alpha := by
  native_decide

end R027
