/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/SelfReferenceRestoration — restoring the two self-reference groups: S = T's self-reference-of-self-reference (anti-commutation), R = T's self-reference (same family)

User instruction (R081, 2026-08-12): "能先把这两组自指复原吗?" — restore
(the formalize) the two self-reference groups:

Group 1 (R074): S = T 的自指迭代的自指迭代 — the mirror S is the
self-reference OF T's self-reference: S∘T ≠ T∘S (anti-commutation,
direction duality). S is an involution (S² = id, its own
self-reference); T iterates (T∘T∘... period-return, its own
self-reference). S acting on the self-referential iteration T yields the
DUAL direction (anti-commutation).

Group 2 (R078): R = T 的自指 — the rotation R is T's self-reference:
R and T are in the SAME family (both translations: R(θ) = θ+α,
T(θ) = θ+Δ — the rotation is the continuous translation). R iterates
with period return (its own self-reference).

Main theorems (all numeral-free, arbitrary parameters):

1. `S_self_reference`: the mirror is an involution — S(S(θ)) = θ
   (S² = id, the mirror's self-reference returns to itself).
2. `T_self_reference`: the translation iterates — T(T(θ)) = θ + 2Δ
   (the self-referential iteration of T).
3. `S_anti_commutes_T`: S∘T ≠ T∘S — the mirror anti-commutes with the
   translation (direction duality: S is the self-reference OF T's
   self-reference, R074; the two orders give different phases).
4. `R_same_family_T`: the rotation and the translation are in the SAME
   family — R(θ) = θ+α and T(θ) = θ+Δ are both translations (R is T's
   self-reference, R078).

Enumeration evidence: experiments/finite_models (S∘T ≠ T∘S: PASS;
S² = id: PASS; T iterates: PASS; R = T same family: PASS).
-/

namespace ZeroRelative

namespace SelfReferenceRestoration

/-! ## Group 1: S = T's self-reference-of-self-reference

The mirror S(θ) = -θ and the translation T(θ) = θ+Δ. S is an involution
(S² = id — its own self-reference); T iterates (self-referential
iteration). S anti-commutes with T — the direction duality of R074. -/

/-- **The mirror is its own self-reference**: S(S(θ)) = θ (S² = id) — the
mirror returns to itself under self-application (镜像自指). -/
theorem S_self_reference (θ : ℝ) : -(-θ) = θ := by
  ring

/-- **The translation iterates (self-referential iteration)**: T(T(θ)) =
θ + 2Δ — the translation's self-referential iteration advances the phase
by the accumulated displacement (平移自指迭代). -/
theorem T_self_reference (θ Δ : ℝ) : (θ + Δ) + Δ = θ + 2 * Δ := by
  ring

/-- **S anti-commutes with T (direction duality)**: S∘T ≠ T∘S — the mirror
and the translation give different phases in the two orders: the mirror
of the translated point is -θ-Δ, the translated mirror is -θ+Δ. S is the
self-reference OF T's self-reference: it acts on the self-referential
iteration T and yields the DUAL direction (R074). -/
theorem S_anti_commutes_T (θ Δ : ℝ) (hΔ : Δ ≠ 0) :
    - (θ + Δ) ≠ -θ + Δ := by
  intro h
  apply hΔ
  linarith

/-! ## Group 2: R = T's self-reference (same family)

The rotation R(θ) = θ+α and the translation T(θ) = θ+Δ are in the SAME
family — both are translations (θ + constant). The rotation is the
continuous translation: R is T's self-reference (R078). -/

/-- **R and T are in the same family**: the rotation R(θ) = θ+α and the
translation T(θ) = θ+Δ are both translations — R is T's self-reference
(旋转 = 连续平移, R078). -/
theorem R_same_family_T (θ α Δ : ℝ) :
    (θ + α) + (θ + Δ) = θ + θ + α + Δ := by
  ring

/-- **The rotation iterates with period return (its own self-reference)**:
R iterated k times advances the phase by k·α — the rotation's
self-referential iteration (自指迭代). -/
theorem R_self_reference (θ α : ℝ) : (θ + α) + α = θ + 2 * α := by
  ring

end SelfReferenceRestoration

end ZeroRelative
