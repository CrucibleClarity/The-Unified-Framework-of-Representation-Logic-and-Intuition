/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Toolkit/Compactification — self-contained one-point compactification and the unit circle

Self-contained (imports mathlib only; no project dependencies).

The "infinity" of a space is not a point in the space; drawing it into a finite
structure is *compactification*. We formalize:

1. The one-point compactification carrier: `Option X` — the space `X` together with
   a single point `infinity` (the point at infinity). The embedding `embed : X →
   Option X` is injective (each original point is a distinct finite point).

2. The unit circle `S¹ = Metric.sphere 0 1` in ℂ: the circular axis. On it, the
   structure constants π and e live (via `Complex.exp`), and Euler's identity
   `Complex.exp (π * I) = -1` is the meeting of the two basepoint clusters.

3. The covering/projection structure: `ℝ → S¹, t ↦ exp (t * I)` is periodic with
   period `2π`, so the even-circle basepoints `{2πk}` all project to `1`, and the
   odd-circle basepoints `{(2k+1)π}` all project to `-1` — multiple basepoints'
   unit elements meet at one point (C-META16).

The compactification removes infinity: `infinity` is a finite point (the ∞ that was
"not in the space" is now an element). The circle makes π and e finite structure
constants rather than "irrational/transcendental" coordinates on the line.
-/

noncomputable section

namespace CompactToolkit

/-! ## One-point compactification via Option

The carrier `Option X = X ∪ {infinity}` with `embed : X → Option X` the embedding
of the original points, `infinity` the single added point at infinity. -/

/-- The point at infinity in the one-point compactification. -/
def infinity {X : Type*} : Option X := none

/-- The embedding of the original space into its one-point compactification. -/
def embed {X : Type*} (x : X) : Option X := some x

/-- The embedding is injective: distinct original points stay distinct. -/
lemma embed_injective {X : Type*} : Function.Injective (@embed X) := by
  intro a b h
  exact Option.some.injEq a b |>.mp h

/-- The point at infinity is not in the image of the embedding: it is genuinely
new (the added compactifying point). -/
lemma infinity_not_in_image {X : Type*} (x : X) : infinity ≠ embed x := by
  simp [infinity, embed]

/-- Every element of the compactification is either an original point or infinity:
`Option X = X ∪ {infinity}` is exhaustive. -/
lemma compactification_cases {X : Type*} (p : Option X) :
    (∃ x : X, p = embed x) ∨ p = infinity := by
  cases p with
  | none =>
      right
      rfl
  | some x =>
      left
      exact ⟨x, rfl⟩

/-! ## The unit circle as the circular axis

The unit circle `S¹ = Metric.sphere 0 1` in ℂ is the circular axis: every point on
it is `exp (t * I)` for some real `t`. On this circle the structure constants π
and e live. -/

/-- The unit circle: `S¹ = {z : ℂ | ‖z‖ = 1}`. -/
def unitCircle : Set ℂ := Metric.sphere 0 1

/-- Every point on the unit circle has unit modulus. -/
lemma unitCircle_norm (z : ℂ) (hz : z ∈ unitCircle) : ‖z‖ = 1 := by
  unfold unitCircle at hz
  simpa using hz

/-- Euler's formula point on the circle: `exp (θ * I)` has unit modulus, so it
lies on the unit circle. -/
lemma exp_I_mem_unitCircle (θ : ℝ) : Complex.exp (θ * Complex.I) ∈ unitCircle := by
  unfold unitCircle
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  exact Complex.norm_exp_ofReal_mul_I θ

/-- **π and e meet on the circle**: Euler's identity `exp (π·I) = -1`. On the
circular axis this is the half-turn: the point at angle π is the antipode of the
point at angle 0 (which is 1). -/
lemma euler_identity : Complex.exp (Real.pi * Complex.I) = -1 := by
  rw [Complex.exp_mul_I]
  simp [Real.cos_pi, Real.sin_pi]

/-- The circle's basepoint at angle 0 is the unit 1. -/
lemma circle_unit : Complex.exp (0 * Complex.I) = 1 := by
  norm_num

/-! ## Basepoint clusters under the covering projection

The covering map `ℝ → S¹, t ↦ exp (t·I)` is `2π`-periodic. The even-circle
basepoints `{2πk}` all project to `1`, and the odd-circle basepoints `{(2k+1)π}`
all project to `-1`. The unit elements of many basepoints meet at one point — the
projection of a high-dimensional (covering) structure to the circle. -/

/-- The even-circle basepoints all meet at 1: `exp (2πk·I) = 1` for every integer
`k` (the covering projection collapses the winding number). -/
lemma exp_two_pi_I_eq_one : Complex.exp ((2 * Real.pi) * Complex.I) = 1 := by
  rw [Complex.exp_mul_I]
  simp [Real.cos_two_pi, Real.sin_two_pi]

lemma exp_pi_I_eq_neg_one : Complex.exp (Real.pi * Complex.I) = -1 := by
  rw [Complex.exp_mul_I]
  simp [Real.cos_pi, Real.sin_pi]

/-- The even-circle basepoints all meet at 1: `exp (2πk·I) = 1` for every `k : ℕ`
(the covering projection collapses the winding number). Layer 2 of the basepoint
cluster decomposition: `exp(2πk·I) = exp(2π·I)^k = 1^k = 1`. -/
lemma even_cluster_meets_one (k : ℕ) : Complex.exp ((2 * Real.pi * (k : ℝ)) * Complex.I) = 1 := by
  -- delta = 2πk 分解为 k 个 2π 单元: exp(2πk·I) = exp(2π·I)^k
  -- 先把参数统一: (2π·k)·I 与 k·(2π·I) 是同一数 (ring 处理)
  have harg : ((2 * Real.pi * (k : ℝ)) * Complex.I) = ((k : ℂ) * ((2 * Real.pi) * Complex.I)) := by
    norm_num
    ring
  rw [harg]
  rw [Complex.exp_nat_mul]
  simp [exp_two_pi_I_eq_one]

/-- The odd-circle basepoints all meet at -1: `exp ((2k+1)π·I) = -1` for every
`k : ℕ`. Layer 3: `exp((2k+1)π·I) = exp(π·I) * exp(2kπ·I) = -1 * 1 = -1`. -/
lemma odd_cluster_meets_neg_one (k : ℕ) :
    Complex.exp (((2 * k + 1) * Real.pi) * Complex.I) = -1 := by
  -- (2k+1)π·I = 2πk·I + π·I; exp(x+y) = exp x · exp y
  -- 组合: exp(2πk·I) · exp(π·I) = 1 · (-1) = -1
  have harg : (((2 * k + 1) * Real.pi) * Complex.I) =
      ((2 * Real.pi * (k : ℝ)) * Complex.I) + (Real.pi * Complex.I) := by
    norm_num
    ring
  rw [harg]
  rw [Complex.exp_add]
  rw [even_cluster_meets_one k]
  simp [exp_pi_I_eq_neg_one]

end CompactToolkit
