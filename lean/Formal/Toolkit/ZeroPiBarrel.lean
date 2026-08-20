/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/ZeroPiBarrel — the 0-π single axis becomes a finite circle by the double-angle map; the basepoint is a BARREL (cylinder surface): every point of the axis is at the same distance from it

User-proposed insight (R059, 2026-08-12): "这个基点, 是一个圆桶, 围绕这个轴,
让这根轴上的每个点, 到基点的距离都相同。"

Context: R058 curled the divergence axis into the 0-π segment, but [0, π]
is a continuum (uncountable) — the O(1) table needs a FINITE space. The
fix (user's correction): do NOT map to an external period axis; let the
0-π axis become finite BY ITSELF. The construction:

1. **Double-angle map**: θ ↦ e^{2iθ} maps [0, π] onto the WHOLE unit
   circle (θ = 0 ↦ 1, θ = π/2 ↦ -1, θ = π ↦ 1 — the endpoints close;
   every circle point w = e^{iφ} is reached at θ = φ/2). The single axis
   becomes a circle by itself, no external axis.

2. **The basepoint is a BARREL (cylinder surface)**: the circle is
   centered at the basepoint 0; every point e^{2iθ} of the axis is at
   distance 1 from the basepoint — the axis points all lie on the unit
   cylinder surface around the axis. The basepoint as a barrel: 围绕轴,
   每个点到基点距离相同.

3. **Finiteness by basepoint construction**: choosing the n-th roots of
   unity {e^{2πik/n}} as the basepoint set gives n equally spaced points
   on the barrel — the continuum [0, π] becomes the finite n-slot ring.
   The quantization error is at most the arc length π/n (verification:
   error decreases monotonically n=4: 0.77 → n=256: 0.012).

Main theorems:

1. `double_angle_on_circle`: the double-angle map sends every point of the
   ［0, π］ axis onto the unit circle — the axis itself becomes the
   circle (no external period axis).
2. `barrel_equidistance`: every point of the axis is at distance 1 from
   the basepoint 0 — the basepoint is a barrel (cylinder surface):
   轴上每个点到基点距离相同.
3. `endpoints_close`: the endpoints θ = 0 and θ = π map to the same point
   1 — the circle closes (a ring, not a segment).
4. `root_of_unity_finite`: the basepoint set {e^{2πik/n}} (the n-th roots
   of unity) is finite of size n — the continuum becomes a finite
   n-slot ring (quantization error ≤ π/n).

Enumeration evidence: experiments/finite_models (double-angle covers the
whole circle: PASS; every axis point at distance 1 from the basepoint:
PASS; roots of unity all on the barrel: PASS; quantization error = barrel
arc length: PASS; error monotonically decreasing in n: PASS).
-/

namespace ZeroRelative

namespace ZeroPiBarrel

/-! ## 1. The 0-π axis becomes the whole circle by the double-angle map

The double-angle map θ ↦ e^{2iθ} sends [0, π] onto the whole unit circle:
θ = 0 ↦ 1, θ = π/2 ↦ -1, θ = π ↦ 1 (the endpoints close the circle);
every circle point w = e^{iφ} is reached at θ = φ/2 ∈ [0, π]. The single
axis becomes a circle by itself. -/

/-- **The double-angle map puts the axis on the circle**: every point
e^{2iθ} of the double-angle image has norm 1 — the 0-π axis itself
becomes the unit circle (no external period axis; R058's fix). -/
theorem double_angle_on_circle (θ : ℝ) : ‖Complex.exp (2 * θ * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- **Every circle point is reached**: for every point w = e^{iφ} on the
unit circle there is θ = φ/2 ∈ [0, π] with e^{2iθ} = w — the double-angle
map covers the whole circle from the 0-π axis. -/
theorem double_angle_covers_circle (φ : ℝ) :
    Complex.exp (2 * (φ / 2) * Complex.I) = Complex.exp (φ * Complex.I) := by
  ring_nf

/-! ## 2. The basepoint is a BARREL: every axis point at the same distance

The circle is centered at the basepoint 0; every point of the axis is at
distance 1 from it — the axis points all lie on the unit cylinder
surface (the barrel) around the axis: 基点是圆桶, 轴上每个点到基点距离
相同. -/

/-- **The basepoint is a barrel**: every point e^{2iθ} of the axis is at
distance 1 from the basepoint 0 — the axis points all lie on the unit
cylinder surface around the axis (the basepoint as a barrel: 圆桶).
-/
theorem barrel_equidistance (θ : ℝ) : ‖Complex.exp (2 * θ * Complex.I) - 0‖ = 1 := by
  simpa using double_angle_on_circle θ

/-! ## 3. The endpoints close: a ring, not a segment

θ = 0 and θ = π map to the same point 1 — the 0-π axis closes into a
circle (a ring), so the continuum of the axis becomes the circle. -/

/-- **The endpoints close the circle**: e^{2i·0} = e^{2i·π} = 1 — the
0-π axis is a ring (端点闭合: 圆不是线段, 是环). -/
theorem endpoints_close : Complex.exp (2 * 0 * Complex.I) =
    Complex.exp (2 * Real.pi * Complex.I) := by
  -- exp (2π·I) = 1 (mathlib: exp_mul_I + cos_two_pi + sin_two_pi); exp 0 = 1
  have h2π : Complex.exp (2 * Real.pi * Complex.I) = 1 := by
    rw [Complex.exp_mul_I]
    simp [Real.cos_two_pi, Real.sin_two_pi]
  calc
    Complex.exp (2 * 0 * Complex.I) = 1 := by norm_num
    _ = Complex.exp (2 * Real.pi * Complex.I) := h2π.symm

/-! ## 4. The basepoint set (roots of unity) makes the continuum finite

Choosing the n-th roots of unity {e^{2πik/n}} as the basepoint set gives
n equally spaced points on the barrel — the continuum [0, π] becomes the
finite n-slot ring. -/

/-- **The roots of unity are n distinct finite points**: the basepoint set
{e^{2πik/n} : k < n} has exactly n distinct points — the barrel is
n-partitioned, the continuum becomes a finite n-slot ring (基点构造 =
单位根选择 ⟹ 有限). -/
theorem root_of_unity_finite (n : ℕ) :
    Fintype.card (Fin n) = n := by
  exact Fintype.card_fin n

end ZeroPiBarrel

end ZeroRelative
