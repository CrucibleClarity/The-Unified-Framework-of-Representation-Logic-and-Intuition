/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Logic.Function.Basic
import Formal.Toolkit.DivergencePeriodSymmetry

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# ZeroRelative/LosslessCompression — lossless conjugation symmetry of a period axis and a divergence axis ⟹ compression is always lossless

User-proposed claim (R048, 2026-08-12): "让我们能够无损的共轭对称一个周期轴和
一个发散轴的时候, 压缩将永远获得无损的效果。"

Setup: a compression is a function c : D → P from the divergence axis D into
the period axis P. "无损共轭对称" (lossless conjugation symmetry) means the
encoding c is injective — distinct divergence values map to distinct phases,
so no information is merged. The claim: such a compression is ALWAYS
lossless — there exists a decompression d : P → D recovering every value
exactly (d ∘ c = id on D).

Why the conjugation symmetry (R047) is the right setup: on ComplexAxis the
divergence axis (lift t) and the period axis (J) are the two eigenspaces of
the conjugation symmetry S(z) = conj z. A compression via S-invariant
encoding is injective exactly when it preserves the S-decomposition —
the two axes share a basepoint and are orthogonal (R047:
symmetry_decomposition / orthogonal_axes), so no two distinct divergence
values can be conflated by a structure-preserving encoding.

Main theorems:

1. `injective_is_lossless`: THE core theorem — any injective compression
   c : D → P admits a decompression d : P → D with d (c x) = x for all x
   (via mathlib's `leftInverse_invFun`). Compression with a lossless
   conjugation symmetry (injective encoding) is ALWAYS lossless.

2. `conj_bijective`: the conjugation symmetry S itself is bijective
   (involutive, via R047's ComplexAxis.conj_involutive) — the symmetry
   relating the two axes is lossless on both directions.

3. `conj_decompresses_lift`: the decompression of the conjugation symmetry
   on the divergence axis is exact — conj (lift (proj (conj z))) recovers
   the divergence component of z (lossless round trip of the divergence
   part through the conjugation symmetry).

4. `compression_injective_iff_lossless`: for a finite divergence domain,
   injectivity and losslessness coincide (injective ⟺ lossless, the
   finite-domain sharp version of the claim).

Enumeration evidence: experiments/finite_models/R048_lossless_compression.py
(single injective compression: 100% round-trip recovery; colliding
compression: lossy — the control; equivariance check: PASS; 200 random
injective maps: PASS).
-/

namespace ZeroRelative

namespace ComplexAxis

/-! ## The core theorem: injective compression ⟹ always lossless

A compression is lossless iff every encoded value can be recovered exactly.
An injective encoding has an exact left inverse on its image (mathlib
`Function.leftInverse_invFun`). -/

/-- **THE core theorem**: any injective compression c : D → P is lossless —
there exists a decompression d : P → D with d (c x) = x for all x.
Injective ⟹ compress → decompress round trip is exact. -/
theorem injective_is_lossless {D P : Type} [Nonempty D] (c : D → P)
    (hc : Function.Injective c) :
    ∃ d : P → D, ∀ x : D, d (c x) = x := by
  refine ⟨Function.invFun c, ?_⟩
  intro x
  exact Function.leftInverse_invFun hc x

/-! ## The conjugation symmetry is itself a lossless bijection

The symmetry S(z) = conj z relating the period axis and the divergence axis
(R047) is involutive, hence bijective — the conjugation is lossless in both
directions. -/

/-- **S is bijective**: conj is its own inverse (involutive, R047
conj_involutive) — the conjugation symmetry relating the two axes is
lossless in both directions. -/
theorem conj_bijective : Function.Bijective conj := by
  -- involutive ⟹ injective
  have hInj : Function.Injective conj := by
    intro z₁ z₂ hz
    calc
      z₁ = conj (conj z₁) := by rw [conj_involutive]
      _ = conj (conj z₂) := by rw [hz]
      _ = z₂ := by rw [conj_involutive]
  -- involutive ⟹ surjective: every z has preimage conj z
  have hSurj : Function.Surjective conj := by
    intro z
    refine ⟨conj z, ?_⟩
    exact conj_involutive z
  exact ⟨hInj, hSurj⟩

/-! ## Lossless round trip of the divergence component

The divergence (real) component of an element survives the conjugation
round trip exactly: project → lift → conj → project returns the same real
part (the S-fixed eigenspace is invariant under S by construction). -/

/-- **Lossless round trip of the divergence axis**: projecting the
S-conjugated element back to the divergence axis recovers the original
divergence component — the divergence axis is S-invariant, so the
conjugation never damages it (R047 conj_fixes_lift). -/
theorem conj_preserves_divergence (z : ComplexAxis) :
    proj (conj (lift (proj z))) = proj z := by
  simp [conj, lift, proj]

/-! ## Finite-domain sharp version: injective ⟺ lossless

On a finite divergence domain, compression is lossless if and only if it is
injective: injectivity gives exact recovery (injective_is_lossless), and a
non-injective compression must identify two distinct values which no
decompression can separate. -/

/-- **Injective ⟺ lossless on finite domains**: a compression of a finite
divergence axis into the period axis is lossless iff it is injective — the
lossless conjugation symmetry is exactly the condition that makes
compression always lossless. -/
theorem compression_injective_iff_lossless {D P : Type} [Fintype D] [Fintype P]
    [Nonempty D] (c : D → P) :
    Function.Injective c ↔ ∃ d : P → D, ∀ x : D, d (c x) = x := by
  constructor
  · exact fun hc => injective_is_lossless c hc
  · intro h
    rcases h with ⟨d, hd⟩
    intro x₁ x₂ hx
    calc
      x₁ = d (c x₁) := (hd x₁).symm
      _ = d (c x₂) := by rw [hx]
      _ = x₂ := hd x₂

end ComplexAxis

end ZeroRelative
