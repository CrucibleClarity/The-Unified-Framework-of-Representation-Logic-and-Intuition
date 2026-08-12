/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Function.Conjugate
import Mathlib.Dynamics.FixedPoints.Basic

/-!
# C001: semiconjugacy preserves iteration and basepoint orbits

Claim ledger C001 (status: CONJECTURE, novelty: KNOWN).
Direction B/C shared baseline.

Statement (informal):
  若 T semiconjugates 两个 self-map S1 S2（T∘S1 = S2∘T），则 T 保持迭代
  T(S1^[n] x) = S2^[n] (T x)。若进一步 T e = f，则基点轨道也被保持。

Mathlib already provides the core lemma `Function.Semiconj.iterate_right`:
  `Semiconj.iterate_right h n : Semiconj f ga^[n] gb^[n]`
so the statements below are direct corollaries (no re-proof).
-/

open Function

namespace ZeroRelative

variable {X Y : Type*}

/-- If `T` semiconjugates `S1` to `S2`, then `T` semiconjugates `S1^[n]` to `S2^[n]`
for every `n : ℕ`. This is exactly `Function.Semiconj.iterate_right`. -/
theorem semiconj_iterate {S1 : X → X} {S2 : Y → Y} {T : X → Y}
    (h : Semiconj T S1 S2) (n : ℕ) : Semiconj T (S1^[n]) (S2^[n]) :=
  h.iterate_right n

/-- C001 part 1: iteration is preserved pointwise,
`T (S1^[n] x) = S2^[n] (T x)` for all `n : ℕ` and `x : X`. -/
theorem semiconj_iterate_apply {S1 : X → X} {S2 : Y → Y} {T : X → Y}
    (h : Semiconj T S1 S2) (n : ℕ) (x : X) : T (S1^[n] x) = S2^[n] (T x) :=
  (h.iterate_right n).eq x

/-- C001 part 2: if moreover `T e = f` (basepoint preservation),
then the basepoint orbit is preserved: `T (S1^[n] e) = S2^[n] f` for all `n : ℕ`. -/
theorem semiconj_iterate_basepoint {S1 : X → X} {S2 : Y → Y} {T : X → Y} {e : X} {f : Y}
    (h : Semiconj T S1 S2) (he : T e = f) (n : ℕ) : T (S1^[n] e) = S2^[n] f := by
  rw [semiconj_iterate_apply h n e, he]

/-- Baseline3: a semiconjugacy maps fixed points of `S1` to fixed points of `S2`.
This is `Function.IsFixedPt.map` (Mathlib.Dynamics.FixedPoints.Basic). -/
theorem semiconj_maps_fixedPoints {S1 : X → X} {S2 : Y → Y} {T : X → Y}
    (h : Semiconj T S1 S2) {x : X} (hx : IsFixedPt S1 x) : IsFixedPt S2 (T x) :=
  hx.map h

/-- Baseline3 (set form): semiconjugacy restricts to a map between fixed-point sets,
`T '' (fixedPoints S1) ⊆ fixedPoints S2`. This is `Function.Semiconj.mapsTo_fixedPoints`. -/
theorem semiconj_mapsTo_fixedPoints {S1 : X → X} {S2 : Y → Y} {T : X → Y}
    (h : Semiconj T S1 S2) : Set.MapsTo T (fixedPoints S1) (fixedPoints S2) :=
  h.mapsTo_fixedPoints

end ZeroRelative
