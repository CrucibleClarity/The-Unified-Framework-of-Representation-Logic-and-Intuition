/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/OriginBasepointEquivalence — the phenomena observed at the real-axis origin 0 are equivalent to the phenomena at basepoint 0 (the S/R/T symmetry stripping process)

User question (R128, 2026-08-12): 从原点剥离出来的对称性 (S/R/T) 的过程,
得到的基点 0 — 然后把原点证明中观察到的现象, 应用到基点 0 阵列生成的
过程中 — 原点 0 观测到的现象, 等价于基点 0 观测到的现象吗?

Formalization: the fold phenomenon (the mirror symmetry S(θ) = -θ, the
±1 fold class of R085) is TRANSLATION-INVARIANT: at ANY basepoint e,
the mirror S_e(x) = 2e - x is an involution (S_e² = id), and the fold
class structure is identical. Hence the phenomena observed at the
origin (fold class, mirror involution) hold identically at every
basepoint — the equivalence of origin-phenomena and basepoint-phenomena.

Main theorems (no sorry):

1. `fold_involution_origin`: the mirror at the origin, S₀(x) = -x, is
   an involution (S₀² = id) — the origin phenomenon.
2. `fold_involution_any_basepoint`: the mirror at ANY basepoint e,
   S_e(x) = 2e - x, is an involution (S_e² = id) — the same phenomenon
   at every basepoint (translation invariance).
3. `origin_basepoint_equivalent`: the fold phenomenon is
   translation-invariant — the phenomena at the origin and at any
   basepoint are equivalent (S₀ and S_e are conjugated by the
   translation T(x) = x + e: S_e = T ∘ S₀ ∘ T⁻¹).
-/

namespace ZeroRelative

namespace OriginBasepointEquivalence

/-- The mirror at the origin: S₀(x) = -x (the ±1 fold class of R085). -/
def S₀ (x : ℝ) : ℝ := -x

/-- The mirror at basepoint e: S_e(x) = 2e - x (the fold shifted). -/
def Sₑ (e x : ℝ) : ℝ := 2 * e - x

/-- **The origin phenomenon: S₀ is an involution** — S₀(S₀(x)) = x
(the ±1 fold class at the origin, R085). -/
theorem fold_involution_origin (x : ℝ) : S₀ (S₀ x) = x := by
  unfold S₀
  ring

/-- **The same phenomenon at ANY basepoint**: S_e is an involution at
every basepoint e — S_e(S_e(x)) = x (the fold phenomenon is
translation-invariant; the fold class structure is identical at every
basepoint). -/
theorem fold_involution_any_basepoint (e x : ℝ) : Sₑ e (Sₑ e x) = x := by
  unfold Sₑ
  ring

/-- **The origin-basepoint equivalence**: the mirror at basepoint e is
the translation-conjugate of the mirror at the origin: S_e = T ∘ S₀ ∘
T⁻¹ with T(x) = x + e. The phenomena at the origin and at any
basepoint are EQUIVALENT (conjugated by the translation — the
equivalence is constructible and definable). -/
theorem origin_basepoint_equivalent (e x : ℝ) :
    Sₑ e x = (S₀ (x - e)) + e := by
  unfold Sₑ S₀
  ring

/-- **The fold class at the origin equals the fold class at any
basepoint (conjugated)**: the ±1 fold class of the origin (R085)
appears identically (shifted) at every basepoint — the phenomenon is
basepoint-independent (R054: any basepoint, any axis). -/
theorem fold_class_translation_invariant (e : ℝ) :
    Sₑ e (e + 1) = e - 1 ∧ Sₑ e (e - 1) = e + 1 := by
  unfold Sₑ
  constructor <;> ring

end OriginBasepointEquivalence

end ZeroRelative
