# Basepoint-Relative Stability and Codomain Drift: A Heap-Theoretic Account of Relativity in Generated Structure

**Formalization of claims C001–C010 (Lean 4 / mathlib)**

*2026-08-12 · Internal research paper · Lean 4 / mathlib v4.32.2*

---

## Abstract

We develop a heap-theoretic account of how the choice of a basepoint stabilizes relative structure while drifting the codomain of generated objects. The starting point is the classical heap retract (C004): an abelian heap H, which carries no distinguished basepoint, recovers an abelian group G_e = (H, +_e, e) upon the choice of any basepoint e, where x +_e y := [x, e, y]. The choice is not unique: different basepoints e and f yield different groups G_e and G_f — the *codomain drifts*. Yet the drift is a structural isomorphism: the basepoint-change map T_{e→f}(x) := [x, e, f] is an automorphism on any heap (C006), transporting the step translation. The *relative* content is basepoint-independent: the displacement space D(H) of equivalence classes (e,a) ∼ (f,b) ⟺ b = [a, e, f] (C007) does not depend on any basepoint — *relative stability*. We then study endogenous generation (C008–C010): under a generation law Γ : e ↦ σ_e, the least fixed point / minimal closure Chain(σ_e, e) is *e-independent* for pure-heap terms (R011): any homomorphism T_{e→f} preserves the evaluation of terms, so Chain(σ_f, f) = T_{e→f}(Chain(σ_e, e)) — the generated structure is exactly transported, not changed. The paper's conclusion is a precise dichotomy: **basepoint choice stabilizes relative structure (transport-invariant) while drifting the codomain (different groups, isomorphic under T)**, and this dichotomy is the mechanism by which "natural-number-like" iterative structure can arise as a *conclusion* of basepoint-relative generation (C009), not as a presupposed input.

## 1. Introduction

### 1.1 Motivation
In mathematics, a structure often becomes a *pointed* object only after the choice of a basepoint: a set becomes a pointed set, a heap becomes a group after selecting an element, a torsor becomes a group action after choosing a base. The question behind this paper is not *whether* such choices matter, but *how* they matter: which properties are stable under basepoint change (relative), and which drift (codomain). We formalize this in the language of heaps — the unpointed algebra of a ternary operation [x, y, z] that satisfies the heap laws — because a heap carries no canonical basepoint, so the choice is a genuine, visible degree of freedom.

### 1.2 Contributions
1. **Heap retract baseline (C004)**: an abelian heap recovers an abelian group at any basepoint; different basepoints give *different* (isomorphic) groups.
2. **Transport under basepoint change (C006)**: T_{e→f}(x) = [x, e, f] is an automorphism on any heap (para-associativity + identities, no commutativity needed), transporting step translation.
3. **Displacement space (C007)**: the equivalence (e,a) ∼ (f,b) ⟺ b = [a, e, f] is an equivalence relation; its classes form a basepoint-independent space D(H), and D(H) ≅ G_e for any e — *relative stability*.
4. **Endogenous generation law (C008–C010)**: a generation law Γ : e ↦ σ_e on pure-heap terms yields a minimal closure Chain(σ_e, e) that is e-independent up to exact transport (R011) — the generated structure is stable under basepoint change, even though the *terms* σ_e differ.
5. **Nature of natural-number-like structure (C009)**: finitary reachability (TransGen) presupposes counting and is downgraded to a baseline; the representation of natural-number-like iteration must be a *conclusion* of basepoint-relative generation, not an input.

### 1.3 Honest boundary
All results are known in classical heap/torsor theory (novelty: KNOWN for C004; DIRECT_COROLLARY for C006; KNOWN-up-to-torsor for C007). The endogenous-generation part (C008–C010) is where the project's own contribution begins: it is the formal study of "how structure arises from basepoint choice," rather than the rediscovery of heap-theoretic facts. No claim is made that the Riemann hypothesis or any analytic assertion is proved; the present paper is purely algebraic.

## 2. Preliminaries: heaps and basepoint retraction

**Definition 2.1** (heap). A heap is a set H with a ternary operation [_,_,_] : H → H → H → H satisfying the heap laws (para-associativity, identity, commutation). A heap is *abelian* if it satisfies the additional commutation law.

**Theorem 2.2** (heap retract, C004, KNOWN). Let H be an abelian heap and e : H a chosen basepoint. Define x +_e y := [x, e, y]. Then (H, +_e, e) is an abelian group: +_e is associative and commutative, e is the identity, and every x has inverse [e, x, e] (given by the heap laws). Conversely, a group (G, +, 0) yields a heap [x, y, z] := x − y + z.

**Observation 2.3** (codomain drift). The choice of basepoint is not unique: for e ≠ f, the recovered groups G_e = (H, +_e, e) and G_f = (H, +_f, f) are *different* group structures on the same carrier H. This is the *codomain drift* of the title.

## 3. Transport under basepoint change (C006)

**Definition 3.1** (basepoint-change map). For a heap H and basepoints e, f : H, define
T_{e→f}(x) := [x, e, f].

**Theorem 3.2** (T is an automorphism, C006). On any heap H (not necessarily abelian), T_{e→f} is a bijection, and for all x, y, z,
T_{e→f}([x, y, z]) = [T_{e→f}(x), T_{e→f}(y), T_{e→f}(z)].
Proof: the middle para-associativity law of heaps makes the translation a homomorphism. Commutativity is not needed.

**Theorem 3.3** (transport of step translation, C006). For fixed endpoint a, the step translation τ_{e,a}(x) := [x, e, a] = x +_e a transports under basepoint change:
T_{e→f}(τ_{e,a}(x)) = τ_{f, T_{e→f}(a)}(T_{e→f}(x)).
The step at e with endpoint a, viewed from f, is the step at f with the transported endpoint T_{e→f}(a).

**Corollary 3.4** (group isomorphism). The basepoint change induces an isomorphism between the retract groups: G_e ≅ G_f. The codomain drifts, but the drift is a structural isomorphism.

## 4. Displacement space: relative stability (C007)

**Definition 4.1** (displacement equivalence). On H × H, define (e, a) ∼ (f, b) iff b = [a, e, f], i.e., b = T_{e→f}(a). Intuitively, (e,a) and (f,b) denote the "same relative displacement" viewed from different basepoints.

**Theorem 4.2** (equivalence, C007). ∼ is an equivalence relation on H × H (reflexive, symmetric, transitive), the transitivity relying on the associativity of heap composition.

**Definition 4.3** (displacement space). Let D(H) := (H × H)/∼ be the quotient. An element of D(H) is an equivalence class of basepoint-endpoint pairs under "same displacement".

**Theorem 4.4** (recovery, C007). Choosing any basepoint e gives a bijection [e, ·] : D(H) → G_e. Thus D(H) is *basepoint-independent* as an abstract object (relative stability), while each concrete presentation D(H) → G_e depends on e (codomain drift). In classical terms, D(H) is the translation group / acting group of the torsor.

**Corollary 4.5** (the dichotomy). **Basepoint choice stabilizes relative structure (D(H) is e-independent) while drifting the codomain (G_e varies with e).** This dichotomy is the precise content of "basepoint-relative stability and codomain drift."

## 5. Endogenous generation (C008–C010)

### 5.1 Methodological correction: no presupposed counting (C008, C009)

**Definition 5.1** (finitary reachability, C008, baseline). Relation.TransGen r a b means that b is reachable from a by a *finite number* of steps — a number n ∈ ℕ. Since counting is exactly the object to be explained, any construction using TransGen presupposes what the theory aims to derive. Hence finitary reachability is *downgraded to a baseline*: it documents the finite-reachability graph, but does not explain the origin of natural-number-like iteration.

**Definition 5.2** (minimal closure, C009, main version). For a generation law Γ with σ_e : H → H, define
Chain(σ_e, e) := ⋂ { C ⊆ H | e ∈ C ∧ σ_e(C) ⊆ C }.
This is the least fixed point / minimal S-closed substructure containing the basepoint, defined without any appeal to ℕ as an indexing set. The representation of natural-number-like structure (if any) is to be a *conclusion* of this construction, not an input.

### 5.2 The general theorem: generation is transport-covariant (C010, R011)

**Theorem 5.3** (R011, transport-covariance of pure-heap generation). Let Γ : H → (H → H) be a generation law on pure-heap terms: σ_e(x) is a term built only from [·,·,·], with leaves in {e, x}, containing no literal constant (in particular no literal 0). Then, for any basepoints e, f,
Chain(σ_f, f) = T_{e→f}(Chain(σ_e, e)).
Proof: T_{e→f} is a homomorphism (Theorem 3.2); every term t(e, x) satisfies T_{e→f}(t(e, x)) = t(f, T_{e→f}(x)); the minimal closure is transported exactly.

**Corollary 5.4** (closure-type independence, C010). The isomorphism type of Chain(σ_e, e) does not depend on the basepoint e: all generated structures from pure-heap laws are basepoint-independent up to isomorphism. This is a universal-algebraic principle (homomorphisms preserve evaluation of terms), not a new phenomenon — but its consequence here is substantive: *within the pure heap, no basepoint is privileged*.

**Remark 5.5** (the 0-dependence was spurious). An earlier family of laws σ_e(x) = [x, x, [x, e, 0]] = x − e contains the literal 0. In a pure heap, 0 is not endogenous — it is itself a basepoint choice. Using 0 secretly privileges a basepoint, violating "no privileged basepoint." Hence the observed basepoint-dependent branching of closure types is not a pure-heap phenomenon; it disappears once the law is restricted to pure-heap terms (R011).

## 6. Discussion: the dichotomy as a mechanism

The paper's claim is that "basepoint-relative stability and codomain drift" is not a defect but the *mechanism* by which relative structure is stabilized while concrete codomains vary:

- **Stability**: D(H), the displacement space, and Chain(σ_e, e), the generated structure, are basepoint-independent up to isomorphism. Relative content — displacement, generation type — is transport-invariant.
- **Drift**: G_e, the recovered group, and the concrete terms σ_e, vary with e. Concrete codomain — which group, which successor term — drifts under basepoint change.
- **Transport**: T_{e→f} is the bridge: it exhibits the drift as an isomorphism, making stability and drift compatible.

This dichotomy connects to the broader framework of the Unified Framework of Representation, Logic, and Intuition: the *form* of generated structure is basepoint-stable (relative), while its *construction* is basepoint-dependent (codomain drift) — and the intuition channel (the compiled fast path) is position-insensitive exactly because it operates on the stable relative content.

## 7. Conclusion

An abelian heap recovers a group at any basepoint (C004); different basepoints give different (isomorphic) groups — codomain drift (C006). The displacement space D(H) is basepoint-independent — relative stability (C007). Under endogenous generation restricted to pure-heap terms, the minimal closure is exactly transported by basepoint change (C010, R011), and the natural-number-like representation is a *conclusion*, not an input (C009). The precise dichotomy — *basepoint choice stabilizes relative structure while drifting the codomain, with T as the isomorphism bridge* — is formalized throughout in Lean 4 / mathlib, claims C001–C010, all PROVED, no sorry.

## Appendix A: theorem inventory (Lean)

- Heap.lean: heap laws, heap_retract_group_laws, IsHeapRetractGroup
- Displacement.lean: displacement equivalence, D(H) recovery
- Generation.lean: minimal closure Chain, R011 transport-covariance
- Semiconj.lean / TorsorHeap.lean: semiconjugacy and torsor-heap correspondence (C001–C003, C005)
- Build: `lake build` full pass, no sorry.

## Appendix B: claims

claims/ZeroRelative/C001.yaml .. C010.yaml (one YAML per claim, statement/formalization/novelty).
