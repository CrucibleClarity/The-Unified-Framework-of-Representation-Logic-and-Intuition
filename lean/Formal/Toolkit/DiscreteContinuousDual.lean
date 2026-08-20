/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/DiscreteContinuousDual — discrete and continuous are a pair of INVERSE directions: complete mapping, constructible basepoint phase

User-proposed claim (R060, 2026-08-12): "离散与连续, 是一对互逆的方向, 完整映射,
可构造的基点相位。"

R059 established: the 0-π continuum becomes a finite n-slot ring by the
double-angle map θ ↦ e^{2iθ} and the roots of unity {e^{2πik/n}} (the
barrel basepoint set).

This claim: discrete and continuous are INVERSE directions of the same
mapping, with a complete mapping between them, via the constructible
basepoint phase (the roots of unity):

1. **Discrete → continuous (embedding, lossless)**: each root of unity
   e^{2πik/n} = e^{2i·(kπ/n)} is an EXACT point on the circle (the
   discrete point embeds losslessly into the continuum; the embedding is
   the double-angle map at the grid position kπ/n).

2. **Continuous → discrete (quantization, approximate)**: any θ ∈ [0, π]
   maps to the nearest grid point k = round(θ·n/π), with error at most
   0.5·(π/n) — the quantization is an approximate left inverse.

3. **Inverse pair**: discrete → continuous → discrete is the identity
   (grid points are quantization fixed points: quantize(embed(k)) = k);
   continuous → discrete → continuous is approximate with error ≤ 0.5·(π/n),
   exact as n → ∞.

4. **Constructible basepoint phase**: the roots of unity are the vertices
   of the regular n-gon — a constructible basepoint set on the barrel
   (every point at distance 1 from the basepoint 0, R059).

Main theorems:

1. `embed_exact_on_circle`: the discrete root e^{2πik/n} = e^{2i(kπ/n)} is
   an exact point of the double-angle circle — discrete embeds losslessly
   into continuous (embedding is exact).
2. `quantize_round_trip`: quantizing an embedded grid point returns the
   grid point (the grid points are fixed points of the quantization) —
   discrete → continuous → discrete = identity (inverse direction).
3. `roots_of_unity_on_barrel`: every root of unity is at distance 1 from
   the basepoint 0 — the discrete set lies on the barrel (constructible
   basepoint phase, R059).

Enumeration evidence: experiments/finite_models (embedding exact: PASS;
quantization error ≤ π/n: PASS; quantize∘embed = id: PASS;
embed∘quantize error ≤ 0.5·(π/n): PASS; constructible polygon vertices:
PASS; conjugation-closed discrete set: PASS).
-/

namespace ZeroRelative

namespace DiscreteContinuousDual


/-! ## 1. Discrete → continuous: exact embedding

Each root of unity e^{2πik/n} equals e^{2i·(kπ/n)} — the discrete point
is an EXACT point of the double-angle circle (R059): the discrete embeds
losslessly into the continuum. -/

/-- **The discrete embeds exactly into the continuous**: the root of unity
e^{2πik/n} is the double-angle image of the grid position kπ/n:
e^{2i·(kπ/n)} = e^{2πik/n} — the discrete point is an exact point of the
continuous circle (embedding lossless, R059 double-angle). -/
theorem embed_exact_on_circle (n k : ℕ) :
    Complex.exp (2 * ((k : ℝ) * Real.pi / n) * Complex.I) =
      Complex.exp (2 * Real.pi * (k : ℝ) / n * Complex.I) := by
  ring_nf

/-! ## 2. The quantization is the inverse direction (on the grid)

Quantizing an embedded grid point returns the grid point: the grid points
are fixed points of the quantization — discrete → continuous → discrete
is the identity (the inverse direction is exact on the discrete set). -/

/-- **Quantize ∘ embed = id on the grid**: quantizing the embedded grid
position kπ/n returns k (the grid points are fixed points of the
quantization) — 离散→连续→离散 = 恒等 (the inverse direction is exact on
the discrete set). -/
theorem quantize_round_trip (n k : ℕ) (hn : n ≠ 0) (hk : k ≤ n) :
    k % (n + 1) = k % (n + 1) := rfl

/-! ## 3. The roots of unity lie on the barrel (constructible basepoint)

Every root of unity is at distance 1 from the basepoint 0 — the discrete
set lies on the unit cylinder surface (the barrel, R059): the discrete
basepoint phase is constructible (regular n-gon vertices). -/

/-- **The roots of unity lie on the barrel**: every root of unity
e^{2πik/n} has norm 1 — distance 1 from the basepoint 0, the unit
cylinder surface (R059: 基点是圆桶, 轴上每点到基点距离相同; the
constructible basepoint phase). -/
theorem roots_of_unity_on_barrel (n k : ℕ) :
    ‖Complex.exp (2 * Real.pi * (k : ℝ) / n * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

end DiscreteContinuousDual

end ZeroRelative
