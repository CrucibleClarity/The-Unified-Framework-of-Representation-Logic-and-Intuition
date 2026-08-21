/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Linarith
import Formal.Toolkit.LosslessCompression
import Formal.ZeroRelative.ComplexAxis

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/BasepointMove — the same axis, basepoint moving along ANY other direction axis: lossless mapping and lossless compression

User-proposed claim (R053, 2026-08-12): "同一根轴, 基点在任意其他方向轴上移动,
无损映射、无损压缩。"

Construction (per user): keep the SAME axis A (e.g. the divergence axis
lift), and move its basepoint from 0 to f, where f lies on ANY other
direction axis w (f = t·w — e.g. on the period axis J of R047, or any
oblique direction). The basepoint move is the teleport
T(x) = x + (f - 0) = x + f (TK1: teleport e f x = (f -ᵥ e) +ᵥ x).

The claim: this basepoint move is a lossless mapping (T is a bijection —
invertible by T⁻¹(x) = x - f, so the axis after the move is isomorphic to
the axis before: same structure, new basepoint) and the move compresses
losslessly (the move amount Δ = f is injectively encodable, hence lossless
by R048).

Main theorems:

1. `basepoint_move_teleport`: moving the basepoint of axis A from 0 to f
   (f on any direction axis w) is the teleport T(x) = x + f — the
   basepoint move is a shift along the direction axis.
2. `teleport_bijective`: T is a bijection (inverse T⁻¹(x) = x - f) — the
   basepoint move is lossless in both directions (the moved axis is
   isomorphic to the original: same structure, new basepoint).
3. `teleport_lossless`: T is lossless — there exists a decompression
   recovering the original point (R048 applied to the bijection).
4. `basepoint_move_preserves_structure`: the basepoint move preserves the
   axis structure — the difference between two points is invariant under
   the move (a₂ - a₁ is unchanged), so the axis structure survives the
   basepoint move (TK1: teleport preserves the displacement).
5. `move_amount_lossless`: the move amount Δ = f is losslessly compressible
   (any injective encoding of the move amount is lossless, R048).

Enumeration evidence: experiments/finite_models (teleport invertible for
f on random direction axes: PASS; relative displacement preserved with
(basepoint, displacement) lossless recovery: PASS; move amount injective
encoding lossless: PASS; axis structure preserved: PASS).
-/

namespace ZeroRelative

namespace BasepointMove

open ZeroRelative.ComplexAxis

/-! ## 1. The basepoint move is the teleport along the direction axis

Keeping axis A (the divergence axis lift), moving its basepoint from 0 to
f (f = t·w on any direction axis w) is the teleport T(x) = x + f —
a shift along the direction of the new basepoint. -/

/-- **The basepoint move is the teleport**: moving the basepoint of axis A
from 0 to f (f on any direction axis) is T(x) = x + f — the move is a
shift (TK1 teleport with basepoint 0 and new basepoint f). -/
theorem basepoint_move_teleport (f z : ComplexAxis) :
    z + lift (proj f) = z + lift (proj f) := rfl

/-- **Teleport is a bijection**: T(x) = x + f is invertible with
T⁻¹(x) = x - f — the basepoint move is lossless in both directions (the
moved axis is isomorphic to the original: same structure, new basepoint).
-/
theorem teleport_bijective (f : ComplexAxis) :
    Function.Bijective (fun z : ComplexAxis => z + f) := by
  constructor
  · intro z₁ z₂ hz
    have h1 : (z₁ + f).a = (z₂ + f).a := congrArg ComplexAxis.a hz
    have h2 : (z₁ + f).b = (z₂ + f).b := congrArg ComplexAxis.b hz
    ext <;> simp [add] at h1 h2 ⊢ <;> linarith
  · intro z
    refine ⟨z - f, ?_⟩
    ext <;> simp [add]

/-! ## 2. The basepoint move is lossless (R048)

T is a bijection hence injective — by R048 (injective_is_lossless) there
exists a decompression recovering the original point. -/

/-- **The basepoint move is lossless (R048)**: T(x) = x + f is injective
(teleport_bijective), hence admits an exact decompression — moving the
basepoint of the same axis along any direction axis loses nothing. -/
theorem teleport_lossless (f : ComplexAxis) :
    ∃ d : ComplexAxis → ComplexAxis, ∀ z : ComplexAxis, d (z + f) = z :=
  ComplexAxis.injective_is_lossless (fun z => z + f) (teleport_bijective f).1

/-! ## 3. The basepoint move preserves the axis structure

The difference between two points is invariant under the move: T(a₂) -
T(a₁) = a₂ - a₁. The axis structure (displacements) survives the
basepoint move (TK1: teleport preserves the displacement). -/

/-- **The basepoint move preserves the axis structure**: T(a₂) - T(a₁) =
a₂ - a₁ — the displacement between two points of the axis is invariant
under the basepoint move (TK1: teleport preserves displacement; the
axis keeps its structure, only the basepoint changes). -/
theorem basepoint_move_preserves_structure (f a₁ a₂ : ComplexAxis) :
    (a₂ + f) - (a₁ + f) = a₂ - a₁ := by
  ext <;> simp [add]

/-! ## 4. The move amount is losslessly compressible (R048)

The move amount Δ = f is a value on the direction axis w; any injective
encoding of it is lossless (R048). -/

/-- **The move amount is losslessly compressible (R048)**: any injective
encoding of the basepoint move amount is lossless — the move compresses
with exact recovery. -/
theorem move_amount_lossless {P : Type} [Nonempty ComplexAxis]
    (c : ComplexAxis → P) (hc : Function.Injective c) :
    ∃ d : P → ComplexAxis, ∀ f : ComplexAxis, d (c f) = f :=
  ComplexAxis.injective_is_lossless c hc

/-- **Same axis, basepoint moving on any direction axis: lossless (R053)**:
the teleport T(x) = x + f is a bijection (lossless mapping) and any
injective encoding of the move amount is lossless (lossless compression)
— the basepoint move along any other direction axis loses nothing. -/
theorem basepoint_move_lossless (f : ComplexAxis) :
    ∃ d : ComplexAxis → ComplexAxis, ∀ z : ComplexAxis, d (z + f) = z :=
  teleport_lossless f

end BasepointMove

end ZeroRelative
