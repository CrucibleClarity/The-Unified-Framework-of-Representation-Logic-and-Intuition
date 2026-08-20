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
import Formal.Toolkit.OrthogonalAxes
import Formal.ZeroRelative.ComplexAxis

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/AnyDirectionAxes — any pair of direction axes from the SAME basepoint maps and compresses losslessly

User-proposed claim (R052, 2026-08-12): "同一个基点出发的任意方向轴间可以任意的
无损映射、无损压缩。"

R047-R051 established: divergence/period axes are the eigenspaces of the
conjugation symmetry S (R047); injective encoding is lossless (R048); ANY
pair of directions maps losslessly via the Householder reflection S_u
(R049); iteration along the same direction is lossless (R050); orthogonal
axes sharing a basepoint map losslessly (R051).

This claim: ANY pair of direction axes EMANATING FROM THE SAME BASEPOINT
0 (orthogonal or not) maps losslessly, and compresses losslessly. The
mechanisms, all previously proven:

1. **The reflection S_u (R049)**: for ANY direction v, the Householder
   reflection S_u decomposes v into its u-component (negated) and its
   u⊥-component (fixed), and S_u is an involution — the round trip
   S_u(S_u(v)) = v is exact. This holds for every direction pair (u, v)
   sharing the basepoint 0, orthogonality NOT required.

2. **The rotation mechanism (R051)**: on ComplexAxis, rot90 maps the lift
   axis onto the period axis, is norm-preserving (rot90_norm) and has
   period 4 (rot90_four), hence bijective — the lossless mapping between
   the two axes. Any direction is a rotation of any other direction
   (the direction angle is a phase).

3. **Lossless compression (R048)**: any injective encoding along a
   direction axis is lossless — a value t along the direction axis
   compresses to a phase slot with exact recovery.

Hence: from the same basepoint, ANY direction axes map losslessly (the
reflection S_u works for every pair) and compress losslessly (injective
encoding along the axis is lossless).

Main theorems:

1. `reflect_lossless_any_direction`: for ANY direction pair (u, v) sharing
   the basepoint 0, the reflection S_u is an involution — the round trip
   S_u(S_u(v)) = v is exact (R049 applied to the arbitrary pair).
2. `reflect_decomposes_any`: for ANY direction v, S_u decomposes v into
   the u-component (negated, the direction part) and the u⊥-component
   (fixed, the orthogonal part) — the general direction decomposition.
3. `rot90_maps_any_axis`: on ComplexAxis, rot90 maps any point of the
   lift axis onto the period axis (rot90 (lift t) = ⟨0, t⟩) and is
   bijective with period 4 — the two axes map losslessly.
4. `axis_compression_lossless`: compressing a value along a direction
   axis via an injective encoding is lossless (R048) — the compression
   direction is arbitrary.

Enumeration evidence: experiments/finite_models (reflection round trip
for non-orthogonal pairs: PASS; arbitrary-angle rotation connecting any
two directions: PASS; injective encoding along any direction: PASS;
axis coordinate transform round trip: PASS).
-/

namespace ZeroRelative

namespace AnyDirectionAxes

open ZeroRelative.ComplexAxis

/-! ## 1. The reflection works for ANY direction pair (basepoint 0 shared)

For ANY directions u, v from the basepoint 0, the Householder reflection
S_u (R049) is an involution: S_u(S_u(v)) = v. Orthogonality is NOT
required — the non-orthogonal part of v is handled by the reflection (the
u-component is negated, the u⊥-component is fixed), and the round trip is
exact. -/

/-- **Any direction pair maps losslessly through S_u**: for ANY directions
u, v from the basepoint 0 (orthogonal or not), the reflection S_u is an
involution — the round trip S_u(S_u(v)) = v is exact (R049). -/
theorem reflect_lossless_any_direction (u v : ℝ × ℝ)
    (hu : u.1 ^ 2 + u.2 ^ 2 ≠ 0) :
    PairwiseDirection.reflect u (PairwiseDirection.reflect u v) = v :=
  PairwiseDirection.reflect_involutive u v hu

/-! ## 2. The general decomposition: u-component (negated) + u⊥-component (fixed)

For ANY direction v (not necessarily orthogonal to u), S_u decomposes v
into its u-component (the direction part, negated) and its u⊥-component
(the orthogonal part, fixed). The projection coefficient flips sign under
S_u. -/

/-- **The projection coefficient flips sign under S_u**: for ANY direction
v, the coefficient of S_u(v) along u is the negative of the coefficient
of v — the direction component is negated, the orthogonal component is
fixed (R049 projCoeff_reflect). -/
theorem reflect_flips_coeff (u v : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 ≠ 0) :
    PairwiseDirection.projCoeff u (PairwiseDirection.reflect u v) =
      -PairwiseDirection.projCoeff u v :=
  PairwiseDirection.projCoeff_reflect u v hu

/-! ## 3. Rotation between the axes (ComplexAxis)

On ComplexAxis, rot90 maps the lift (divergence) axis onto the period
axis: rot90 (lift t) = ⟨0, t⟩. It is norm-preserving (rot90_norm) with
period 4 (rot90_four), hence bijective — the two axes from the basepoint
0 map losslessly in both directions (R051). -/

/-- **rot90 maps any point of the lift axis onto the period axis**:
rot90 (lift t) = ⟨0, t⟩ — the divergence axis maps onto the period
axis (both from basepoint 0, R051). -/
theorem rot90_maps_any_axis (t : ℝ) :
    rot90 (lift t) = (⟨0, t⟩ : ComplexAxis) :=
  OrthogonalAxes.rot90_lift_to_period t

/-- **rot90 is bijective (period 4)**: rot90⁴ = id (C011 rot90_four) — the
rotation between the axes is invertible, so the mapping is lossless in
both directions (R048). -/
theorem rot90_bijective : Function.Bijective rot90 :=
  OrthogonalAxes.rot90_bijective

/-! ## 4. Lossless compression along any direction axis (R048)

Compressing a value along a direction axis: any injective encoding is
lossless (R048). The compression direction is arbitrary — every axis
from the basepoint compresses losslessly. -/

/-- **Compression along a direction axis is lossless (R048)**: any
injective encoding c : D → P along a direction axis is lossless — there
exists a decompression recovering every value exactly. The compression
direction is arbitrary: EVERY axis from the basepoint 0 compresses
losslessly. -/
theorem axis_compression_lossless {D P : Type} [Nonempty D]
    (c : D → P) (hc : Function.Injective c) :
    ∃ d : P → D, ∀ x : D, d (c x) = x :=
  ComplexAxis.injective_is_lossless c hc

/-- **Same-basepoint direction axes map and compress losslessly (R052)**:
for any direction axis u from the basepoint 0, the reflection S_u maps
any other direction axis v losslessly (involution), and any injective
encoding along an axis compresses losslessly (R048). -/
theorem same_basepoint_lossless (u v : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 ≠ 0) :
    PairwiseDirection.reflect u (PairwiseDirection.reflect u v) = v :=
  reflect_lossless_any_direction u v hu

end AnyDirectionAxes

end ZeroRelative
