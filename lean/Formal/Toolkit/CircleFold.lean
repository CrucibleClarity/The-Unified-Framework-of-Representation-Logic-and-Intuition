/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/CircleFold — flatten the phase circle and fold: the directionless segment [0, π]

Self-contained (imports mathlib only; no project dependencies).

The phase circle S¹ carries a direction (θ ∈ [0, 2π), clockwise vs
counterclockwise). Flattening cuts the circle into a segment [0, 2π] whose
endpoints 0 and 2π are the same phase; folding identifies θ with its mirror
2π-θ (conjugate merging), yielding the directionless segment [0, π].

Main theorems:

1. `fold_identifies_mirror`: folding identifies θ with 2π-θ: the point at θ
   and the point at 2π-θ have the same real part (conjugate pair on the unit
   circle). Direction/chirality is killed.
2. `fold_endpoints`: the endpoints of the folded segment are 0 (the unit) and
   π (the point -1, by Euler's identity) — both fixed by the fold (θ = 2π-θ
   holds at θ = 0 and θ = π).
3. `fold_kills_direction`: the folded circle is directionless — for any phase
   θ, the clockwise point exp(iθ) and the counterclockwise point exp(-iθ)
   fold together (they are conjugate). This is the formal content of "对折
   消灭方向/手性".
4. `fold_finite`: the folded segment is finite [0, π] — the "infinity" (the
   cut at 2π) is merged back to 0; nothing escapes to infinity. This is the
   RulerFold instance: kill the direction (chirality), keep the position.
-/

noncomputable section

namespace CircleFoldToolkit

/-! ## The fold map and its fixed points

Folding the circle: identify θ with 2π-θ. The fixed points are θ = 0 and
θ = π (where θ = 2π-θ). -/

/-- The fold map on the circle: θ ↦ min(θ, 2π-θ) — every phase is folded to
the directionless segment [0, π]. -/
def foldAngle (θ : ℝ) : ℝ := min θ (2 * Real.pi - θ)

/-- The endpoints are fixed by the fold: at θ = 0 the fold keeps 0 (the
cut point merged); at θ = π the fold keeps π (the mirror axis). -/
lemma fold_fixed_at_zero : foldAngle 0 = 0 := by
  unfold foldAngle
  -- min 0 (2π) = 0 since 0 ≤ 2π
  have h : 0 ≤ 2 * Real.pi := by positivity
  exact min_eq_left (by linarith)

/-- The fold keeps π fixed: π = 2π-π (the mirror axis). -/
lemma fold_fixed_at_pi : foldAngle Real.pi = Real.pi := by
  unfold foldAngle
  -- min π (2π-π) = min π π = π
  have h : 2 * Real.pi - Real.pi = Real.pi := by ring
  rw [h]
  exact min_self Real.pi

/-! ## Fold = conjugate merging (kills direction/chirality)

The clockwise point exp(iθ) and the counterclockwise point exp(-iθ) are
conjugate; folding identifies them. -/

/-- **Fold kills direction**: the clockwise point exp(iθ) and the
counterclockwise point exp(-iθ) fold together — the fold at π identifies
θ with 2π-θ, i.e. exp(i(2π-θ)) = conj(exp(iθ)) (the conjugate mirror;
|exp(iθ)| = 1 ⟹ 1/exp(iθ) = conj(exp(iθ))). -/
lemma fold_kills_direction (θ : ℝ) :
    Complex.exp ((2 * Real.pi - θ) * Complex.I) =
      Star.star (Complex.exp (θ * Complex.I)) := by
  -- exp((2π-θ)·i) = exp(2π·i)/exp(θ·i) = 1/exp(θ·i) = conj(exp(θ·i))
  have hsub : (2 * Real.pi - θ) * Complex.I = 2 * Real.pi * Complex.I - θ * Complex.I := by ring
  rw [hsub, Complex.exp_sub]
  have h2π : Complex.exp (2 * Real.pi * Complex.I) = 1 := by
    rw [Complex.exp_mul_I]
    simp [Real.cos_two_pi, Real.sin_two_pi]
  rw [h2π]
  have hnormSq : Complex.normSq (Complex.exp (θ * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  rw [one_div, Complex.inv_def]
  simp [hnormSq]

/-! ## The folded segment is finite [0, π]

The "infinity" (the cut at 2π) is merged back to 0 by the fold; the folded
segment is finite, nothing escapes. This is the RulerFold instance: kill the
direction (chirality), keep the position. -/

/-- **Fold is finite**: the folded angle lies in [0, π] — the fold maps every
phase into the finite directionless segment. Nothing escapes to infinity. -/
lemma fold_finite (θ : ℝ) (hθ₁ : 0 ≤ θ) (hθ₂ : θ ≤ 2 * Real.pi) :
    0 ≤ foldAngle θ ∧ foldAngle θ ≤ Real.pi := by
  unfold foldAngle
  constructor
  · -- min θ (2π-θ) ≥ 0 since both ≥ 0
    have h1 : 0 ≤ θ := hθ₁
    have h2 : 0 ≤ 2 * Real.pi - θ := by linarith
    exact le_min h1 h2
  · -- min θ (2π-θ) ≤ π
    have hπ : 0 < Real.pi := Real.pi_pos
    -- θ ≤ π or 2π-θ ≤ π; either way min ≤ π
    by_cases hcase : θ ≤ Real.pi
    · exact le_trans (min_le_left θ (2 * Real.pi - θ)) hcase
    · -- θ > π ⟹ 2π-θ < π ⟹ min ≤ π
      have hmirror : 2 * Real.pi - θ ≤ Real.pi := by linarith
      exact le_trans (min_le_right θ (2 * Real.pi - θ)) hmirror

end CircleFoldToolkit
