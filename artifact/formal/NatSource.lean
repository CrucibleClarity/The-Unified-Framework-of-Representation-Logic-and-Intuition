/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Data.Set.Basic
import Mathlib.Order.CompleteLattice.Basic

/-!
# C009 (version 2): Nat-source representation via minimal S-closed substructure

Claim ledger C009 (status: CONJECTURE, novelty: NOVELTY_UNASSESSED).
Branch: basepoint_relativity.

★ Discipline: the generated object must be defined WITHOUT `Function.iterate`,
`orbit : ℕ → H`, or `Relation.TransGen` (they encode finitely-many steps, n ∈ ℕ,
which is exactly what we are trying to explain). Instead we use set-theoretic
intersection (minimal closure):

  Closed(C)   :⟺ e ∈ C ∧ ∀ x ∈ C, σ x ∈ C
  Chain(e)    := ⋂ {C : Set H | Closed C}     (minimal σ-closed substructure)

This file defines Closed / Chain via set intersection (no iteration), and proves:
  * `Chain(e)` contains `e`
  * `Chain(e)` is σ-closed (σ x ∈ Chain(e) whenever x ∈ Chain(e))
  * minimality: Chain(e) ⊆ C for every σ-closed C containing e

The representation theorem ((Chain(e), σ) ≅ (N, S) when σ is injective on
Chain(e) and e ∉ σ(Chain(e))) is the classical Dedekind simple-infinite-system
characterization (KNOWN baseline).

★ Note (ordinal-like): pure unary successor closure does NOT produce limit
stages. Even with H = Ord, σ(α) = α+1, e = 0, the minimal closure Chain(0) is
still {0, 1, 2, ...} and does not contain ω: minimality only demands successor
closure, not that limits of chains inside are included. Ordinal-like structures
require an ENRICHED generation law with a limit rule (e.g. `L(C)` or a supremum
closure `C directed ⟹ sup C ∈ C`).

The research question after the representation theorem is how the generated
structure changes when the basepoint e and the generation law σ_e both vary:
compare (Chain_e, e, σ_e) with (Chain_f, f, σ_f) for a basepoint-dependent
generation law Γ : e ↦ σ_e.
-/

namespace ZeroRelative

variable {H : Type*}

/-- A set `C` is σ-closed and contains `e`: `e ∈ C` and `σ x ∈ C` for all `x ∈ C`. -/
def Closed (σ : H → H) (e : H) (C : Set H) : Prop :=
  e ∈ C ∧ ∀ x : H, x ∈ C → σ x ∈ C

/-- The minimal σ-closed substructure containing `e`: the intersection of ALL
σ-closed sets containing `e`. Defined by set intersection (no iteration). -/
def Chain (σ : H → H) (e : H) : Set H :=
  ⋂ C : {C : Set H // Closed σ e C}, C.1

/-- `Chain(e)` contains `e`. -/
theorem chain_mem_self (σ : H → H) (e : H) : e ∈ Chain σ e := by
  unfold Chain
  rw [Set.mem_iInter]
  intro C
  exact C.2.1

/-- `Chain(e)` is σ-closed: if `x ∈ Chain(e)` then `σ x ∈ Chain(e)`. -/
theorem chain_closed (σ : H → H) (e : H) :
    ∀ x : H, x ∈ Chain σ e → σ x ∈ Chain σ e := by
  intro x hx
  unfold Chain at hx ⊢
  rw [Set.mem_iInter] at hx ⊢
  intro C
  exact C.2.2 x (hx C)

/-- Minimality: `Chain(e)` is contained in every σ-closed set containing `e`. -/
theorem chain_minimal (σ : H → H) (e : H) {C : Set H}
    (hC : Closed σ e C) : Chain σ e ⊆ C := by
  intro x hx
  unfold Chain at hx
  rw [Set.mem_iInter] at hx
  exact hx ⟨C, hC⟩

/-- Non-emptiness of `Chain(e)` (it always contains `e`). -/
theorem chain_nonempty (σ : H → H) (e : H) : (Chain σ e).Nonempty :=
  ⟨e, chain_mem_self σ e⟩

/-- If `σ` is injective on all of `H`, it is injective on `Chain(e)`. -/
theorem chain_inj_of_inj (σ : H → H) (hσ : Function.Injective σ) (e : H) :
    ∀ ⦃a b : H⦄, a ∈ Chain σ e → b ∈ Chain σ e → σ a = σ b → a = b := by
  intro a b ha hb h
  exact hσ h

end ZeroRelative
