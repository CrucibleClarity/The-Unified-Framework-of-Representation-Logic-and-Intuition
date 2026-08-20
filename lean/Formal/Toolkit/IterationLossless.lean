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
# Toolkit/IterationLossless — the iteration-direction axis, its conjugate axis, and lossless iteration

User-proposed claim (R050, 2026-08-12): "构造迭代这个方向的轴, 然后这是个发散轴,
把他的共轭轴构造出来, 然后通过共轭映射关系证明, 共享基点的同方向轴的任意迭代
之间, 都可以无损压缩。"

Construction (per user):

1. **The iteration-direction axis** (a divergence axis): take the real line
   with basepoint e and the unit step σ(x) = x + 1. Iterating n times from
   the basepoint gives the point e + n — the iteration direction is a
   divergence axis (n grows without bound). On ComplexAxis this is the
   lift axis (divergence axis of R047): lift (e + n) = lift e + lift n
   (lift_add).

2. **Its conjugate axis**: the period axis of R047 — the J direction,
   related to the divergence axis by the conjugation symmetry
   S(z) = conj z (S fixes the divergence axis: conj_fixes_lift;
   S reflects the period axis: conj_reflects_J).

3. **Through the conjugation relation**: the conjugation is an additive
   homomorphism (conj_add), so it preserves the iteration direction:
   conj (lift x + lift n) = conj (lift x) + conj (lift n), and since the
   divergence axis is S-fixed, conj (lift (x+n)) = lift (x+n) — the
   iteration relation survives conjugation.

4. **Any iteration between two same-direction axes is lossless**: for any
   two iteration counts m, n, the map c(z) = z + lift (n - m) (the
   iteration-difference direction) is injective, hence lossless with
   decompression d(z) = z + lift (m - n) (R048: injective ⟹ lossless).
   Both axes share the basepoint 0 (the shared basepoint of the
   divergence/period pair, R047), and the iteration direction is exactly
   the divergence direction.

Main theorems:

1. `conj_add`: the conjugation S is an additive homomorphism — the
   iteration direction survives conjugation.
2. `conj_preserves_iterate`: conjugation preserves the n-fold iteration
   on the divergence axis: conj (lift (x + n)) = lift (x + n) (the
   iteration axis is S-fixed, R047 conj_fixes_lift + lift_add).
3. `iteration_axis_injective`: the iteration-direction map c(z) = z + lift n
   is injective — distinct points of the divergence axis never merge
   under iteration.
4. `iteration_direction_lossless`: the iteration direction is losslessly
   compressible — ∃ decompression d with d (z + lift n) = z (R048 applied
   to the iteration map).
5. `any_two_iterations_lossless`: between any two same-direction iteration
   counts m, n, the iteration-difference map z ↦ z + lift (n - m) is
   lossless — 任意迭代之间都可无损压缩.

Enumeration evidence: experiments/finite_models (conj additivity:
PASS 1000 cases; conj preserves iteration: PASS; iteration-difference
round trip for random (m, n): PASS; iteration map injective: PASS).
-/

namespace ZeroRelative

namespace IterationLossless

open ZeroRelative.ComplexAxis

/-! ## 1. The conjugation preserves the iteration direction

The conjugation S(z) = conj z (R047) is an additive homomorphism: it
commutes with addition, hence preserves the iteration direction z ↦ z + lift n. -/

/-- **Conjugation is additive**: S(z + w) = S(z) + S(w) — the conjugation
symmetry preserves the addition structure, so the iteration direction
survives conjugation. -/
theorem conj_add (z w : ComplexAxis) :
    conj (z + w) = conj z + conj w := by
  ext <;> simp [conj, add] <;> ring

/-! ## 2. The iteration axis is the S-fixed divergence axis

The divergence axis (lift) is the fixed-point set of S (R047
conj_fixes_lift). Iterating n times stays on the axis: lift (x + n), and
conjugation preserves it exactly. -/

/-- **Conjugation preserves the n-fold iteration**: conj (lift (x + n)) =
lift (x + n) — the iteration axis is S-fixed, so the n-fold iteration
survives conjugation (the iteration relation is invariant under the
conjugation symmetry). -/
theorem conj_preserves_iterate (x n : ℝ) :
    conj (lift (x + n)) = lift (x + n) := by
  -- lift (x+n) = lift x + lift n (lift_add), S additive (conj_add),
  -- S fixes lift (conj_fixes_lift)
  calc
    conj (lift (x + n)) = conj (lift x + lift n) := by rw [lift_add]
    _ = conj (lift x) + conj (lift n) := conj_add (lift x) (lift n)
    _ = lift x + lift n := by
      rw [conj_fixes_lift x, conj_fixes_lift n]
    _ = lift (x + n) := by rw [lift_add]

/-! ## 3. The iteration direction is injective

The iteration-direction map c(z) = z + lift n never merges two distinct
points: distinct points of the divergence axis land on distinct points
after n iterations. -/

/-- **The iteration-direction map is injective**: c(z) = z + lift n —
distinct points of the divergence axis never merge under iteration. -/
theorem iteration_axis_injective (n : ℝ) :
    Function.Injective (fun z : ComplexAxis => z + lift n) := by
  intro z₁ z₂ hz
  cases z₁ with
  | mk a₁ b₁ =>
    cases z₂ with
    | mk a₂ b₂ =>
      have ha : a₁ + n = a₂ + n := by
        have h := congrArg ComplexAxis.a hz
        simpa [lift, add] using h
      have hb : b₁ = b₂ := by
        have h := congrArg ComplexAxis.b hz
        simpa [lift, add] using h
      ext
      · linarith
      · exact hb

/-! ## 4. The iteration direction is losslessly compressible (R048)

The iteration-direction map is injective, so by R048
(injective_is_lossless) it admits an exact decompression: iterating n
times is lossless. -/

/-- **The iteration direction is losslessly compressible**: the map
c(z) = z + lift n (the iteration direction) is injective, hence admits an
exact decompression d with d (z + lift n) = z — the n-fold iteration
along the same direction is lossless (R048). -/
theorem iteration_direction_lossless (n : ℝ) :
    ∃ d : ComplexAxis → ComplexAxis,
      ∀ z : ComplexAxis, d (z + lift n) = z := by
  have hInj : Function.Injective (fun z : ComplexAxis => z + lift n) :=
    iteration_axis_injective n
  exact ComplexAxis.injective_is_lossless (fun z => z + lift n) hInj

/-! ## 5. Any iteration between two same-direction axes is lossless

For any two iteration counts m, n, the iteration-difference map
z ↦ z + lift (n - m) is injective, hence lossless with decompression
z ↦ z + lift (m - n). Both axes share the basepoint 0 (the shared
basepoint of the divergence/period pair, R047). -/

/-- **The explicit decompression**: d(z) = z - lift n is the exact inverse
of c(z) = z + lift n — the round trip through the iteration direction
recovers the original point exactly. -/
theorem iteration_direction_decompress (n : ℝ) (z : ComplexAxis) :
    (fun w : ComplexAxis => w + lift (-n)) (z + lift n) = z := by
  ext <;> simp [lift, add]

/-- **Any two same-direction iterations are losslessly compressible**:
for any two iteration counts m, n, the map between them (iteration
difference n - m) is lossless — 共享基点的同方向轴的任意迭代之间都可以
无损压缩 (R048: injective ⟹ lossless). -/
theorem any_two_iterations_lossless (m n : ℝ) :
    ∃ d : ComplexAxis → ComplexAxis,
      ∀ z : ComplexAxis, d (z + lift (n - m)) = z :=
  iteration_direction_lossless (n - m)

end IterationLossless

end ZeroRelative
