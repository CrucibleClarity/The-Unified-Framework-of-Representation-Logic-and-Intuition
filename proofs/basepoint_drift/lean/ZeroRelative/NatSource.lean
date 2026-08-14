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



/-! ## Representation theorem: (Chain(σ,e), σ) ≅ (ℕ, S) — Dedekind simple infinite system

The representation theorem (C009): if σ is injective on Chain(e) and
e ∉ σ(Chain(e)) (the successor never cycles back to the basepoint), then
Chain(e) with the successor σ is isomorphic to ℕ with the successor
function (Dedekind simple infinite system, KNOWN).

The construction (a REPRESENTATION RESULT — ℕ appears in the conclusion,
not in the definition of the generated object, per the Nat-independence
discipline):

  f : ℕ → Chain(e),  f(0) = e,  f(n+1) = σ(f(n))

* f well-defined: f(n) ∈ Chain(e) by induction (chain_mem_self +
  chain_closed).
* f injective: σ injective on Chain(e) + e ∉ σ(Chain(e)) (no cycle
  through the basepoint).
* f surjective: minimality — the image of f is σ-closed and contains e,
  so Chain(e) ⊆ im f (chain_minimal).
-/

/-- The representation map f : ℕ → Chain(σ,e): f(0) = e, f(n+1) = σ(f(n)). -/
noncomputable def reprMap (σ : H → H) (e : H) (n : ℕ) : H :=
  Nat.recOn n e (fun _ acc => σ acc)

/-- `f(n)` lies in `Chain(e)` for all n — the representation map lands in
the generated structure (by induction: f(0) = e ∈ Chain(e), f(n+1) =
σ(f(n)) ∈ Chain(e) by closure). -/
theorem reprMap_mem_chain (σ : H → H) (e : H) (n : ℕ) :
    reprMap σ e n ∈ Chain σ e := by
  induction n with
  | zero =>
    unfold reprMap
    exact chain_mem_self σ e
  | succ n ih =>
    unfold reprMap
    exact chain_closed σ e (reprMap σ e n) ih

/-- The image of the representation map is σ-closed: if y = f(n) then
σ y = f(n+1). -/
theorem reprMap_image_closed (σ : H → H) (e : H) :
    ∀ y : H, y ∈ {y : H | ∃ n : ℕ, reprMap σ e n = y} →
      σ y ∈ {y : H | ∃ n : ℕ, reprMap σ e n = y} := by
  intro y hy
  rcases hy with ⟨n, hn⟩
  refine ⟨n + 1, ?_⟩
  -- f(n+1) = σ(f(n)); hn : f(n) = y
  change σ (reprMap σ e n) = σ y
  rw [hn]

/-- The image of the representation map is σ-closed and contains `e`:
the standard closure certificate for minimality. -/
theorem reprMap_image_closed_cert (σ : H → H) (e : H) :
    Closed σ e {y : H | ∃ n : ℕ, reprMap σ e n = y} := by
  constructor
  · exact ⟨0, rfl⟩
  · exact reprMap_image_closed σ e

/-- **The representation theorem (surjective part)**: if σ is injective on
Chain(e) and e ∉ σ(Chain(e)), then Chain(e) is a Dedekind simple
infinite system — the representation map f : ℕ → Chain(e) is surjective
(the image is σ-closed and contains e, so by minimality Chain(e) ⊆ im f;
every element of the generated structure is reached by finitely many
successor steps — ℕ as the representation result). -/
theorem reprMap_surjective (σ : H → H) (e : H)
    (hσ : ∀ ⦃a b : H⦄, a ∈ Chain σ e → b ∈ Chain σ e → σ a = σ b → a = b)
    (hout : e ∉ σ '' Chain σ e) :
    ∀ x : H, x ∈ Chain σ e → ∃ n : ℕ, reprMap σ e n = x := by
  -- im f is σ-closed and contains e (reprMap_image_closed_cert); by
  -- minimality Chain(e) ⊆ im f; every x ∈ Chain(e) is in the image.
  have hmin : Chain σ e ⊆ {y : H | ∃ n : ℕ, reprMap σ e n = y} :=
    chain_minimal σ e (reprMap_image_closed_cert σ e)
  intro x hx
  exact hmin hx

/-- **The representation theorem (injective part)**: under the same
hypotheses, the representation map is injective — f(n) = f(m) ⟹ n = m.
Descent on n: if f(n) = f(m) with n < m, then e = f(0) = σ(f(m-1)) at
n = 0 (contradicting e ∉ σ(Chain(e))), or σ(f(n'-1)) = σ(f(m-1)) ⟹
f(n'-1) = f(m-1) by hσ (descent to a smaller pair). -/
theorem reprMap_injective (σ : H → H) (e : H)
    (hσ : ∀ ⦃a b : H⦄, a ∈ Chain σ e → b ∈ Chain σ e → σ a = σ b → a = b)
    (hout : e ∉ σ '' Chain σ e) :
    Function.Injective (reprMap σ e) := by
  intro n m hnm
  -- induction on n (the smaller index); for the successor step we use hσ
  -- to descend; for n = 0 we contradict hout.
  induction n generalizing m with
  | zero =>
      cases m with
      | zero => rfl
      | succ m' =>
        exfalso
        -- e = f(0) = f(m'+1) = σ(f(m')) ⟹ e ∈ σ '' Chain(e)
        have heq : e = σ (reprMap σ e m') := by
          simpa [reprMap] using hnm
        exact hout ⟨reprMap σ e m', reprMap_mem_chain σ e m', heq.symm⟩
  | succ n' ih =>
      cases m with
      | zero =>
        exfalso
        -- σ(f(n')) = f(n'+1) = f(0) = e ⟹ e ∈ σ '' Chain(e)
        have heq : σ (reprMap σ e n') = e := by
          simpa [reprMap] using hnm
        exact hout ⟨reprMap σ e n', reprMap_mem_chain σ e n', heq⟩
      | succ m' =>
        -- σ(f(n')) = f(n'+1) = f(m'+1) = σ(f(m')) ⟹ f(n') = f(m') by hσ
        have hpre : reprMap σ e n' = reprMap σ e m' := by
          apply hσ (reprMap_mem_chain σ e n') (reprMap_mem_chain σ e m')
          simpa [reprMap] using hnm
        have hn' : n' = m' := ih hpre
        exact congrArg Nat.succ hn'

/-- **The representation theorem (C009)**: if σ is injective on Chain(e)
and e ∉ σ(Chain(e)), then Chain(e) is a Dedekind simple infinite system
— the representation map f : ℕ → Chain(e), f(0) = e, f(n+1) = σ(f(n))
is a bijection. The generated structure is EXACTLY the natural numbers;
ℕ is the representation result, not a parameter of the generated
object's definition (Nat-independence: Chain(e) is defined by set
intersection, no iteration, no ℕ). -/
theorem chain_represents_nat (σ : H → H) (e : H)
    (hσ : ∀ ⦃a b : H⦄, a ∈ Chain σ e → b ∈ Chain σ e → σ a = σ b → a = b)
    (hout : e ∉ σ '' Chain σ e) :
    Function.Injective (reprMap σ e) ∧
    ∀ x : H, x ∈ Chain σ e → ∃ n : ℕ, reprMap σ e n = x :=
  ⟨reprMap_injective σ e hσ hout, reprMap_surjective σ e hσ hout⟩

end ZeroRelative
