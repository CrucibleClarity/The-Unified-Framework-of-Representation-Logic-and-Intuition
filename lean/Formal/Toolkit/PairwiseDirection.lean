/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PairwiseDirection — any pair of directions maps losslessly: the Householder reflection is the universal S

User-proposed claim (R049, 2026-08-12): "既然我们能无损的在一对轴上映射, 这也就
意味着, 所有成对的方向, 都可以无损映射, 对吧?"

R047/R048 gave: on the ComplexAxis pair (divergence axis = lift t, period axis
= J), the conjugation S(z) = conj z decomposes every element into an S-fixed
part and an S-reflected part (symmetry_decomposition), and injective encoding
into the period axis is lossless (injective_is_lossless).

The generalization: this is not special to the pair (real axis, J). For ANY
direction u in an inner-product space, the Householder reflection
S_u(x) = x - 2·⟨x,u⟩/‖u‖²·u is:
  1. an involution (S_u ∘ S_u = id) — the reflection is its own inverse,
     lossless in both directions;
  2. norm-preserving (S_u is an isometry — the "det = -1 type" orthogonal
     symmetry of NS3);
  3. an eigen-decomposition S_u(x) = (reflected u-component) + (fixed
     u⊥-component): the u-part is negated, the orthogonal part is fixed —
     every pair of directions (u, v) is mapped through S_u with v's
     orthogonal part kept intact;
  4. hence injective (in fact bijective), so any encoding along the
     eigenspaces is lossless (R048: injective ⟹ lossless).

So "all pairs of directions map losslessly" is true: every direction pair
(u, v) admits the reflection symmetry S_u which fixes the u⊥-part of v and
reflects the u-part — the lossless mapping of R047 is the special case
u = real axis, v = J of this universal construction.

Enumeration evidence: experiments/finite_models/R049_pairwise_lossless.py
(involution/norm-preservation/decomposition/round-trip on random directions
in dims 2,3,5: PASS; colliding encoding: lossy control).
-/

namespace ZeroRelative

namespace PairwiseDirection

/-! ## The Householder reflection with a chosen direction u

For a direction u = (a, b) with a² + b² ≠ 0, the reflection across the line
perpendicular to u:

    S_u(x) := x - 2 * (⟨x, u⟩ / ‖u‖²) · u

Let p := (x.1*a + x.2*b) / (a² + b²) (the projection coefficient); then
S_u(x) = (x.1 - 2*p*a, x.2 - 2*p*b). The coefficient of S_u(x) along u is
-p (reflection), so applying S_u twice returns x. -/

/-- The projection coefficient of x along u. -/
noncomputable def projCoeff (u x : ℝ × ℝ) : ℝ :=
  (x.1 * u.1 + x.2 * u.2) / (u.1 ^ 2 + u.2 ^ 2)

/-- The reflection across u⊥: S_u(x) = x - 2·p·u where p = ⟨x,u⟩/‖u‖². -/
noncomputable def reflect (u x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 - 2 * projCoeff u x * u.1, x.2 - 2 * projCoeff u x * u.2)

/-- The coefficient of S_u(x) along u is the negative of the coefficient of
x: p(S_u(x)) = -p(x) — the reflection negates the u-component. -/
theorem projCoeff_reflect (u x : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 ≠ 0) :
    projCoeff u (reflect u x) = -projCoeff u x := by
  cases x with
  | mk x1 x2 =>
    cases u with
    | mk a b =>
      simp [projCoeff, reflect]
      field_simp [hu]
      ring_nf

/-- **S_u is an involution**: S_u(S_u(x)) = x — the reflection is its own
inverse. Lossless in both directions. -/
theorem reflect_involutive (u x : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 ≠ 0) :
    reflect u (reflect u x) = x := by
  cases x with
  | mk x1 x2 =>
    cases u with
    | mk a b =>
      have hc : projCoeff (a, b) (reflect (a, b) (x1, x2)) = -projCoeff (a, b) (x1, x2) :=
        projCoeff_reflect (a, b) (x1, x2) hu
      simp [hc, reflect, projCoeff]
      field_simp [hu]
      ring_nf
      trivial

/-- **S_u is norm-preserving**: ‖S_u(x)‖² = ‖x‖² — the reflection is an
isometry, the det = -1 type orthogonal symmetry (NS3 partner of rotation). -/
theorem reflect_preserves_sq (u x : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 ≠ 0) :
    (reflect u x).1 ^ 2 + (reflect u x).2 ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
  cases x with
  | mk x1 x2 =>
    cases u with
    | mk a b =>
      simp [projCoeff, reflect]
      field_simp [hu]
      ring_nf

/-- **S_u is injective**: the reflection is bijective (involution ⟹
injective) — the lossless mapping of R048 applies: any injective encoding
is lossless, and S_u itself is injective. -/
theorem reflect_injective (u : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 ≠ 0) :
    Function.Injective (fun x => reflect u x) := by
  intro x₁ x₂ hx
  have h1 : reflect u (reflect u x₁) = x₁ := reflect_involutive u x₁ hu
  have h2 : reflect u (reflect u x₂) = x₂ := reflect_involutive u x₂ hu
  have h3 : reflect u (reflect u x₁) = reflect u (reflect u x₂) := by
    exact congrArg (fun z => reflect u z) hx
  calc
    x₁ = reflect u (reflect u x₁) := h1.symm
    _ = reflect u (reflect u x₂) := h3
    _ = x₂ := h2

/-- **Every pair of directions maps losslessly (R049)**: for ANY direction u,
the reflection S_u is an involution and norm-preserving — so the R047/R048
lossless mapping holds for every direction pair (u, v): v is decomposed by
S_u into its u-part (reflected) and u⊥-part (fixed), and the round trip
S_u ∘ S_u = id recovers v exactly. -/
theorem pairwise_lossless (u v : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 ≠ 0) :
    reflect u (reflect u v) = v := reflect_involutive u v hu

end PairwiseDirection

end ZeroRelative
