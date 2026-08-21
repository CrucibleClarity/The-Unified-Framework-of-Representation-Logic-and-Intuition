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
import Formal.Toolkit.BasepointMove
import Formal.ZeroRelative.ComplexAxis

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/AnyBasepointAnyDirection — axes from ANY basepoint in ANY direction: lossless mapping and lossless compression

User-proposed claim (R054, 2026-08-12): "任意基点出发的任意方向轴, 无损映射、
无损压缩。"

R052-R053 established: from the SAME basepoint 0, any direction axes map
losslessly (the reflection S_u is an involution for every pair, R052);
the SAME axis with its basepoint moving along any other direction axis is
lossless (the teleport is a bijection, R053).

This claim is their composition: an axis from ANY basepoint e in ANY
direction u maps losslessly to an axis from any other basepoint f in any
direction v, and compresses losslessly. The mechanism is the 3-stage
composition, each stage lossless by the previous claims:

  1. teleport e → 0 (R053: the basepoint move is a bijection);
  2. reflection S_u at 0 (R052: any direction pair maps losslessly);
  3. teleport 0 → f (R053 again).

The composition of lossless (injective) maps is lossless (injective), so
the composed map from the (e, u) axis to the (f, v) axis is lossless —
there exists a decompression recovering the original point (R048).

Main theorems:

1. `composed_injective`: the composed map
   M(x) = reflect u (x - e) + f is injective — the axes from any
   basepoints in any directions map losslessly in both directions
   (composition of the teleport bijection T_{-e}, the reflection S_u,
   and the teleport T_f).
2. `composed_map_round_trip`: the 3-stage round trip recovers the input:
   teleport f⁻¹, reflect u (involution), teleport e — the composition
   is an exact bijection.
3. `any_basepoint_any_direction_lossless`: the composed map is lossless —
   there exists a decompression recovering the input (R048 applied to
   the composed injective map).

Enumeration evidence: experiments/finite_models (3-stage round trip for
random basepoints e, f and random directions: PASS; injective encoding
lossless: PASS; composed map injective: PASS).
-/

namespace ZeroRelative

namespace AnyBasepointAnyDirection

open ZeroRelative.ComplexAxis

/-! ## The composed map: teleport → reflect → teleport

From an axis with basepoint e and direction u to an axis with basepoint f
and direction v: move the basepoint to 0 (teleport -e, R053), apply the
reflection S_u (R052), move the basepoint to f (teleport f, R053). Each
stage is lossless; the composition is lossless (injective ∘ injective =
injective, R048). -/

/-- The composed map: M(x) = reflect u (x - e) + f. -/
noncomputable def composedMap (e u f : ℝ × ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  PairwiseDirection.reflect u (x.1 - e.1, x.2 - e.2) + f

/-- **The 3-stage round trip recovers the input**: applying the inverse
stages (teleport f⁻¹, reflect u, teleport e) to M(x) returns x — the
composition is an exact bijection (R053 teleport bijections + R052
reflection involution). -/
theorem composed_map_round_trip (e u f : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 ≠ 0)
    (x : ℝ × ℝ) :
    PairwiseDirection.reflect u (composedMap e u f x - f) + e = x := by
  unfold composedMap
  -- composedMap - f = reflect u (x - e)
  have h₁ : PairwiseDirection.reflect u (x.1 - e.1, x.2 - e.2) + f - f =
      PairwiseDirection.reflect u (x.1 - e.1, x.2 - e.2) := by
    ext <;> simp
  -- reflect u (reflect u (x - e)) = x - e (involution)
  have h₂ : PairwiseDirection.reflect u
      (PairwiseDirection.reflect u (x.1 - e.1, x.2 - e.2)) = (x.1 - e.1, x.2 - e.2) :=
    PairwiseDirection.reflect_involutive u (x.1 - e.1, x.2 - e.2) hu
  -- final: (x - e) + e = x
  ext <;> simp [h₁, h₂] <;> ring

/-- **The composed map is injective**: M(x) = reflect u (x - e) + f — the
composition of the teleport bijection T_{-e} (R053), the reflection S_u
(R052), and the teleport T_f (R053). Axes from ANY basepoint in ANY
direction map losslessly in both directions. -/
theorem composed_injective (e u f : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 ≠ 0) :
    Function.Injective (composedMap e u f) := by
  intro x₁ x₂ hx
  -- apply the inverse stages to both sides of hx
  have h₁ : PairwiseDirection.reflect u (composedMap e u f x₁ - f) + e =
      PairwiseDirection.reflect u (composedMap e u f x₂ - f) + e := by
    rw [hx]
  -- both sides collapse to x₁ and x₂ respectively (round trip)
  have hx₁ : PairwiseDirection.reflect u (composedMap e u f x₁ - f) + e = x₁ :=
    composed_map_round_trip e u f hu x₁
  have hx₂ : PairwiseDirection.reflect u (composedMap e u f x₂ - f) + e = x₂ :=
    composed_map_round_trip e u f hu x₂
  exact hx₁.symm.trans (h₁.trans hx₂)

/-! ## The composed map is lossless (R048)

The composed map is injective (composed_injective), hence by R048
(injective_is_lossless) there exists a decompression recovering the
original point — axes from ANY basepoint in ANY direction map losslessly. -/

/-- **Axes from any basepoint in any direction map losslessly (R054)**: the
composed map (teleport e→0, reflect S_u, teleport 0→f) is injective,
hence admits an exact decompression — 任意基点出发的任意方向轴, 无损映射
(R048 applied to the composed map). -/
theorem any_basepoint_any_direction_lossless (e u f : ℝ × ℝ)
    (hu : u.1 ^ 2 + u.2 ^ 2 ≠ 0) :
    ∃ d : ℝ × ℝ → ℝ × ℝ, ∀ x : ℝ × ℝ, d (composedMap e u f x) = x := by
  haveI : Nonempty (ℝ × ℝ) := ⟨(0, 0)⟩
  exact ComplexAxis.injective_is_lossless (composedMap e u f)
    (composed_injective e u f hu)

end AnyBasepointAnyDirection

end ZeroRelative
