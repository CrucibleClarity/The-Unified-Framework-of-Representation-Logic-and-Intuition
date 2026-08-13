/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Data.ZMod.Basic

/-!
# R022 — Regeneration square: the obstruction is architectural, not observational

Fifth review (2026-08-07): R019/R020/R021 are all the "control layer" — they
establish research language and verification method, and their phenomena are
all EXPLAINED by existing theory:

  * un-eliminable information   — parametricity / representation independence
  * same reduct, diff expansion — Padoa / Beth (implicit definability)
  * new entity = definitional defn — definitional / Morita equivalence
                                  (Barrett–Halvorson)
  * minimal sufficient hidden state — statistics / realization theory /
                                  bisimulation / minimum realization
                                  (Observer-Based Realization, 2024)
  * canonical quotient from observable family — established paradigm

Hence R021 is CLOSED: "does context carry information?" is not the new problem.

The genuinely not-yet-covered object is REGENERATION: the context/basepoint
participates in PRODUCING the generation law itself:

    (e, E) ↦ Γ_{e,E}

A context change (e,E) → (f,E') is NOT "re-represent F", it is "regenerate the
law": Γ_{f,E'}.  The comparison is the regeneration square

    P ∘ Generate_{e,E}     vs     Generate_{f,E'} ∘ P

and we ask for the minimal residual R* making the extended square commute.

This file formalizes the ARCHITECTURAL obstruction: the square commutes (with
the pushed-forward law) iff the generation law Γ respects the projection's
kernel.  This condition is derivable from (P, Γ) alone — it is NOT a quotient
defined by an observable chosen afterwards.

Definitions:
  P : X → Y        layer projection (surjective)
  Γ : X → X        high-layer generation law (per-context)
  respectsKernel : Γ maps P-fibers into P-fibers
  pushforward     : the induced law on Y, well-defined iff respectsKernel
-/

namespace R022

/-- Γ respects the P-kernel: two states that P identifies must be mapped by Γ
to states that P still identifies.  This is well-definedness of the pushed-
forward law, and exactly the condition for the regeneration square to commute.
Derivable from the architecture (P, Γ); not chosen via an observable. -/
def respectsKernel {X Y : Type*} (P : X → Y) (Γ : X → X) : Prop :=
  ∀ x x' : X, P x = P x' → P (Γ x) = P (Γ x')

/-- Necessity: IF some low-layer law Γlow makes the regeneration square commute
(`P ∘ Γ = Γlow ∘ P`), THEN Γ respects the P-kernel.  So commutation forces the
architectural condition; failure of `respectsKernel` is a regeneration defect
that no low-layer law can hide. -/
theorem commutes_implies_respects {X Y : Type*} (P : X → Y)
    (Γ : X → X) (Γlow : Y → Y) (h : ∀ x : X, P (Γ x) = Γlow (P x)) :
    respectsKernel P Γ := by
  intro x x' hPxx'
  calc
    P (Γ x) = Γlow (P x) := h x
    _ = Γlow (P x') := by rw [hPxx']
    _ = P (Γ x') := (h x').symm

/-- The pushed-forward (regenerated) low-layer law: Γlow(y) := P(Γ(x)) for any
x with P x = y.  Well-defined precisely when Γ respects the P-kernel. -/
noncomputable def pushforward {X Y : Type*} (P : X → Y)
    (hP : Function.Surjective P) (Γ : X → X) (_h : respectsKernel P Γ) :
    Y → Y :=
  fun y => P (Γ (Classical.choose (hP y)))

/-- Sufficiency: IF Γ respects the P-kernel, THEN the regeneration square
commutes with the pushed-forward law:
`P ∘ Γ = pushforward(Γ) ∘ P`.  This is the well-definedness / naturality of
regeneration: the projection and the regenerated law fit into a commuting
square, with no extra information injected. -/
theorem pushforward_commutes {X Y : Type*} (P : X → Y)
    (hP : Function.Surjective P) (Γ : X → X) (h : respectsKernel P Γ) :
    ∀ x : X, P (Γ x) = pushforward P hP Γ h (P x) := by
  intro x
  unfold pushforward
  apply h x (Classical.choose (hP (P x)))
  exact (Classical.choose_spec (hP (P x))).symm

/-
R017 model (Z/8): P drops the second coordinate e₂ entirely.  The high-layer
generation law Γ(x) = x + e₂ depends on the dropped coordinate, so it does NOT
respect the P-kernel: two states equal under P (same first coordinate, any e₂)
are sent to different P-images by Γ.  Hence NO low-layer law can make the square
commute — this is the regeneration defect, located in the architecture (Γ's
dependence on e₂), not in any observable.
-/
namespace ZMod8

open ZMod

/-- High-layer generation law Γ4(s) = s + 4 (R017: e₂ = 4 enters the law as the
step). -/
def Γ4 (s : ZMod 8) : ZMod 8 := s + 4

/-- Faithful R017 projection: P(x,y) = x keeps the first coordinate.  Model it
on Z/8 by keeping the parity class: Ppar : Z/8 → Z/2, Ppar(s) = s % 2. -/
def Ppar (s : ZMod 8) : ZMod 2 :=
  ((s.val % 2) : Nat)

/-- Γ4 respects the parity kernel (the pushed-forward square commutes): the
parity kernel {0,2,4,6} is mapped by +4 to itself, and the odd coset {1,3,5,7}
also maps to itself.  Ppar(Γ4 s) = (s+4)%2 = s%2, so the step-e₂ law is
compatible with the parity projection. -/
example : ∀ s : ZMod 8, Ppar (Γ4 s) = Ppar s := by
  intro s
  fin_cases s <;> native_decide

/-
The regeneration defect is NOT in the law respecting the kernel here (it
does); it is in the low-layer STEP choice.  R017's low law used step 1 (full
closure size 8) while e₂ = 4 (closure size 2): the low law is NOT the
pushforward of the high law, so the square `P∘Γ` vs `Γlow∘P` fails even though
`respectsKernel` holds.  The architectural core is `commutes_implies_respects`:
if ANY Γlow makes the square commute, Γ respects the P-kernel.  Conversely a
law that moves a P-fiber out of its image forbids ANY commuting low law.
-/

end ZMod8

/-
The regeneration defect is ARCHITECTURAL: it is classified by whether Γ
respects the P-kernel, a condition read off (P, Γ) directly, not by any
observable.  When it fails, NO low-layer law makes the square commute
(`commutes_implies_respects`), so the minimal residual R* must re-encode
exactly the P-kernel structure that Γ does not preserve.
-/

end R022
