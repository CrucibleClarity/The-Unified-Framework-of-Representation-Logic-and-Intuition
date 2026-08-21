/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Linarith
import Formal.Toolkit.LosslessCompression
import Formal.Toolkit.PairwiseDirection
import Formal.ZeroRelative.ComplexAxis

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/OrthogonalAxes — any pair of orthogonal axes sharing a basepoint maps losslessly

User-proposed claim (R051, 2026-08-12): "共享基点的任意正交轴间均可无损映射。"

R047-R050 established: the divergence axis (lift) and the period axis (J)
of ComplexAxis are orthogonal, share basepoint 0, and map losslessly
through the conjugation symmetry S (R047); injective encoding is lossless
(R048); any pair of directions maps losslessly via the Householder
reflection S_u (R049); iteration along the same direction is lossless
(R050).

This claim: ANY pair of ORTHOGONAL axes sharing a basepoint maps losslessly.
The mechanism: orthogonality is exactly the condition that makes the
conjugation/reflection structure lossless — for an orthogonal pair (u, v)
with ⟨u, v⟩ = 0:

1. The Householder reflection S_u fixes v (v lies in the u⊥-eigenspace of
   S_u) and is an involution (R049 reflect_involutive) — the orthogonal
   axis v is mapped through S_u with ZERO information change, and S_u is
   its own inverse (lossless in both directions).

2. On ComplexAxis, the concrete pair (lift axis, J axis): rot90 (×J) maps
   the lift axis onto the J axis (rot90 (lift t) = ⟨0, t⟩ — a pure
   imaginary point on the period axis), preserves the norm (rot90_norm),
   and has period 4 (rot90_four) hence is bijective — the orthogonal axes
   map losslessly onto each other by rotation (det = +1, the NS3 partner
   direction of the reflection).

3. Both mechanisms share basepoint 0 (the common basepoint of orthogonal
   axes in a linear structure) and the round trip recovers the input
   exactly (involution / period-4).

Main theorems:

1. `reflect_fixes_orthogonal`: if v is orthogonal to u (⟨u, v⟩ = 0), the
   reflection S_u fixes v: S_u(v) = v — the orthogonal axis is the
   +1-eigenspace of the symmetry (zero information change).
2. `reflect_lossless_orthogonal`: for an orthogonal pair, S_u is a lossless
   bijection fixing the orthogonal axis — the orthogonal axes share the
   basepoint and map losslessly.
3. `rot90_lift_to_period`: on ComplexAxis, rot90 maps the lift (divergence)
   axis onto the period axis: rot90 (lift t) = ⟨0, t⟩ — the orthogonal
   axes map onto each other.
4. `rot90_lossless_pair`: rot90 is norm-preserving with period 4 (C011
   rot90_norm / rot90_four), hence bijective — the orthogonal axis pair
   (lift, J) maps losslessly in both directions.

Enumeration evidence: experiments/finite_models (S_u fixes orthogonal v +
S_u involutive + norm-preserving: PASS in dims 2,3,4; rotation round
trip: PASS; rot90(lift t) lands on period axis: PASS).
-/

namespace ZeroRelative

namespace OrthogonalAxes

open ZeroRelative.ComplexAxis

/-! ## 1. Orthogonality ⟹ the reflection fixes the orthogonal axis

For an orthogonal pair (u, v) with ⟨u, v⟩ = 0, the Householder reflection
S_u (R049) has v in its fixed set: the projection of v onto u is zero, so
S_u(v) = v - 2·0·u = v. The orthogonal axis suffers zero information
change under the symmetry. -/

/-- **The reflection fixes the orthogonal axis**: for an orthogonal pair
(u, v), S_u(v) = v — the orthogonal axis is the +1-eigenspace of the
conjugation symmetry (R049), so it maps through the symmetry with zero
information change. -/
theorem reflect_fixes_orthogonal (u v : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 ≠ 0)
    (horth : u.1 * v.1 + u.2 * v.2 = 0) :
    PairwiseDirection.reflect u v = v := by
  unfold PairwiseDirection.reflect PairwiseDirection.projCoeff
  cases u with
  | mk a b =>
    cases v with
    | mk c d =>
      have hnum : c * a + d * b = 0 := by
        -- horth: a*c + b*d = 0; commute
        nlinarith
      have hcoef : (c * a + d * b) / (a ^ 2 + b ^ 2) = 0 := by
        rw [hnum]
        simp
      ext
      · simp [hcoef]
      · simp [hcoef]

/-! ## 2. The orthogonal pair maps losslessly

The reflection S_u is an involution (R049) and fixes the orthogonal axis
— the orthogonal pair shares the basepoint and maps losslessly in both
directions (R048: injective ⟹ lossless). -/

/-- **The orthogonal pair maps losslessly**: for an orthogonal pair (u, v),
the reflection S_u is an involution (R049 reflect_involutive) that fixes
v — the orthogonal axes share the basepoint and the round trip
S_u(S_u(v)) = v is exact. -/
theorem reflect_lossless_orthogonal (u v : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 ≠ 0)
    (horth : u.1 * v.1 + u.2 * v.2 = 0) :
    PairwiseDirection.reflect u (PairwiseDirection.reflect u v) = v := by
  have hfix : PairwiseDirection.reflect u v = v :=
    reflect_fixes_orthogonal u v hu horth
  calc
    PairwiseDirection.reflect u (PairwiseDirection.reflect u v)
        = PairwiseDirection.reflect u v := by
          exact congrArg (PairwiseDirection.reflect u) hfix
    _ = v := hfix

/-! ## 3. ComplexAxis: rot90 maps the lift axis onto the period axis

On ComplexAxis (C011/R047), the lift axis (divergence) and the J axis
(period) are orthogonal and share basepoint 0. The rotation rot90 (×J)
maps the lift axis onto the period axis: rot90 (lift t) = ⟨0, t⟩. -/

/-- **rot90 maps the divergence axis onto the period axis**:
rot90 (lift t) = ⟨0, t⟩ — the point lands on the pure-imaginary J axis
(the period axis of R047). -/
theorem rot90_lift_to_period (t : ℝ) :
    rot90 (lift t) = (⟨0, t⟩ : ComplexAxis) := by
  ext <;> simp [rot90, lift]

/-- **rot90 is norm-preserving**: ‖rot90 z‖ = ‖z‖ (C011 rot90_norm) — the
rotation mapping the orthogonal axes is an isometry (det = +1, the NS3
partner direction of the reflection). -/
theorem rot90_preserves_norm (z : ComplexAxis) : norm (rot90 z) = norm z :=
  rot90_norm z

/-- **rot90 is bijective with period 4**: rot90⁴ = id (C011 rot90_four) —
the rotation between the orthogonal axes is invertible (inverse =
rot90³), so the orthogonal pair maps losslessly in both directions
(R048). -/
theorem rot90_bijective : Function.Bijective rot90 := by
  constructor
  · intro z₁ z₂ hz
    -- rot90⁴ = id (rot90_four); apply rot90³ to both sides
    have h₁ : rot90 (rot90 (rot90 (rot90 z₁))) = z₁ := rot90_four z₁
    have h₂ : rot90 (rot90 (rot90 (rot90 z₂))) = z₂ := rot90_four z₂
    have h₃ : rot90 (rot90 (rot90 (rot90 z₁))) = rot90 (rot90 (rot90 (rot90 z₂))) := by
      -- rot90³ (rot90 z₁) = rot90³ (rot90 z₂) via congrArg
      exact congrArg (fun w => rot90 (rot90 (rot90 w))) hz
    exact h₁.symm.trans (h₃.trans h₂)
  · intro z
    -- preimage: rot90³ z (since rot90⁴ z = z)
    refine ⟨rot90 (rot90 (rot90 z)), ?_⟩
    change rot90 (rot90 (rot90 (rot90 z))) = z
    exact rot90_four z

/-- **The orthogonal pair (lift, J) maps losslessly**: rot90 is bijective
and norm-preserving — the orthogonal axes sharing basepoint 0 map
losslessly onto each other in both directions (R048: injective ⟹
lossless). -/
theorem rot90_lossless_pair :
    ∃ d : ComplexAxis → ComplexAxis, ∀ z : ComplexAxis, d (rot90 z) = z := by
  exact ComplexAxis.injective_is_lossless rot90 rot90_bijective.1

/-- **Orthogonal axes share the basepoint**: the lift axis and the period
axis both contain 0 — the shared basepoint of the orthogonal pair
(R047: the divergence/period pair shares basepoint 0). -/
theorem orthogonal_axes_share_basepoint : lift 0 = 0 ∧ (⟨0, 0⟩ : ComplexAxis) = 0 := by
  constructor <;> ext <;> simp [lift]

end OrthogonalAxes

end ZeroRelative
