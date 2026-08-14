# Three-Channel Equivalence in the Unified Framework of Representation, Logic, and Intuition — Construction Earns Intuition

# 统一框架 · 三通道等价 · 构造获得直觉

> **Draft v0.1 (English)** | 2026-08-11
> Target: TMLR / COLM / Cognition (theory + empirical)
> **Framework position**: Part of the *Unified Framework of Representation, Logic, and Intuition* (manifesto: `Unified_Framework_Representation_Logic_Intuition.md`). This paper establishes the **construction→intuition** cognition: construction, intuition, and formal rewriting are three equivalent execution channels of one system; intuition is compiled construction. Companion: P1 (form→construction, representation + generalization theory), P2 (construction→intuition method, compilation).
> Evidence: exp50 (three-channel consistency), exp41 (symbol permutation), exp80 (step-skipping), exp53 (convergence). Single official run_exp judge.

---

**Repository: [YuchenWang-ai/Three-Channel-Equivalence-Construction-Intuition-and-Formal-Rewriting-in-One-Neural-System](https://github.com/YuchenWang-ai/Three-Channel-Equivalence-Construction-Intuition-and-Formal-Rewriting-in-One-Neural-System)**

## Abstract

The century-old split in the foundations of mathematics — intuitionism (a mathematical object exists iff it can be constructed), structuralism (an object is its position in a structure), and formalism (mathematics is a sign game) — is mirrored in a single neural system as three execution channels for the same mathematical object. We show that, in a token-native representation, the *construction* channel (definition-driven unfolding), the *intuition* channel (compiled weight execution), and the *formal* channel (definition-driven rewriting) are pairwise semantically equivalent: on a 2000-digit carry chain all three produce identical results (1.000). We argue this is the neural implementation of Computational Trinitarianism (Curry–Howard: programs = proofs = types), with the crucial difference that the equivalence holds between *execution channels of one system* rather than between logics. We develop the epistemology: intuition is the reasoning fast path — hard to obtain (config-dependent epochs), but easy to generalize by skipping construction steps; symbol permutation invariance (0.987) and zero-decay step-skipping (2000 digits, radix 60, 100% anonymization) establish that the intuition channel carries structure, not symbol semantics. Stance: anti-Platonist — intuition is compiled construction, not innate. Within the Unified Framework, this paper is the **construction→intuition** cognition leg: correct construction yields intuition (compiled construction), and correct generalization compiles into flashing intuition (the fast reasoning path).

## 1 Introduction

**The split.** In the foundations of mathematics, three answers compete for the question "what is a mathematical object?" Brouwer's intuitionism: an object exists iff it can be *constructed*. Bourbaki's structuralism: an object is its *position in a structure*. Hilbert's formalism: mathematics is a *sign game*; an object is its role in a rewriting system. The dispute is usually presented as philosophical; in this paper we observe that it is also *architectural* — the three positions correspond to three ways a computing system can realize the same object.

**The unification.** A single neural system over a token-native representation (P1) exhibits all three channels:
- *Construction* (intuitionism): unfold the definition chain, step by step — existence by construction;
- *Intuition* (structuralism): compiled weights position the object directly — existence by location in the learned structure;
- *Formal* (formalism): the definition-driven rewriting engine — existence by the sign-manipulation rules.

We show experimentally that the three channels are pairwise semantically equivalent on the same inputs (exp50: construction = formal exactly; intuition 1.000 on a 2000-digit carry chain). This is the neural implementation of Computational Trinitarianism — Curry–Howard's programs = proofs = types — but with a decisive difference: the equivalence is *within one system's execution channels*, not between distinct logical systems.

**Why this matters.** If construction, intuition, and formal rewriting agree on the same object, then the philosophical positions are not alternatives to be argued about but *facets of a single realization*. The disagreement over "what an object is" becomes a disagreement over *which channel to look through* — and all channels answer the same way. The engineering content is the compilation relation: construction can be compiled into intuition (P2), and both agree with rewriting.

**Contributions.**

- **C1 (Epistemology) — Intuition is compiled construction.** The intuition channel is not a third mysterious faculty; it is the construction process compiled into weights. Anti-Platonist: no innate structure, no a priori object.
- **C2 (Empirics) — Three-channel equivalence.** Construction = formal exactly, and intuition 1.000 on the same inputs, including a 2000-digit carry chain (exp50).
- **C3 (Empirics) — Intuition carries structure, not symbols.** Symbol permutation invariance (0.987, exp41) and zero-decay step-skipping (exp80) show the intuition channel realizes the structure of the objects, not their signifiers.
- **C4 (Epistemology) — Acquisition and step-skipping are decoupled.** Intuition is hard to obtain (config-dependent epochs; 3 simple / 8 full, exp53) but easy to generalize by skipping construction steps — the two facts are not in tension.

## 2 Three Positions, Three Channels

| Position | Object is | Access | Our channel | Execution |
|---|---|---|---|---|
| Intuitionism (Brouwer) | a construction | construct it | Construction | unfold definition chain, step by step |
| Structuralism (Bourbaki) | a position | locate it | Intuition | compiled weights place it directly |
| Formalism (Hilbert) | a sign game | play it | Formal | definition-driven rewriting |

The three channels share a single definition source: the token-native representation (P1 §4). Construction and formal read the same definitions; intuition is a compiled image of the same definitions. Equivalence is therefore not a coincidence of three independent systems but a property of one system viewed through three channels.

**Computational Trinitarianism.** Curry–Howard identifies programs, proofs, and types as the same thing under three presentations. Our claim is analogous: construction, intuition, and formal rewriting are the same computation under three presentations — *within one system*. The difference from Curry–Howard is the locus of equivalence: not "program = proof = type" as distinct entities, but "one object's three execution paths agree."

## 3 Intuition as Compiled Construction

**The claim.** The intuition channel is the construction process compiled into weights. Training (P1 §5) supervises the model with judgment outcomes while *excluding answer traces*: the model cannot copy the unfolding; it must induce the computation from definitions and compile it. The compiled product is intuition — the reasoning fast path.

**Hard to obtain.** Compilation is not free. Acquisition is config-dependent: 3 epochs for the simple suite, 8 for the full logic-and-arithmetic suite (exp53). Until compilation completes, the intuition channel does not generalize (exp53: epochs 1–3 at 0.1–24%). This is the *obtain* side of the decoupling.

**Easy to generalize.** Once compiled, the intuition channel generalizes by *skipping construction steps*: it jumps from input to output over the intermediate unfolding. Zero decay out to 2000 digits, radix 60, and 100% digit anonymization (exp80). This is the *generalize* side.

**Decoupling (C4).** The two facts — hard to obtain, easy to skip — are not in tension. Obtaining requires compiling the structure (training); generalizing uses the compiled structure (inference). The theory of P1 explains both: definition completeness + relational sufficiency determine whether compilation succeeds; step-skipping is what compiled structure does on new inputs.

## 4 Experiments

All via the official run_exp judge path (full-sequence reconstruction). Model: exp02_supervised_s2 (2-layer, dim-64, <1 MB, judgment 1.000 on the full suite).

### 4.1 Three-channel equivalence (C2)

| Input | Construction | Formal | Intuition |
|---|---|---|---|
| 12+34 | ✓ | ✓ | ✓ |
| 123456789+987654321 | ✓ | ✓ | ✓ |
| 999…9 (20 digits)+1 | ✓ | ✓ | ✓ |
| **999…9 (2000 digits)+1** | ✓ | ✓ | **1.000** |

Construction = formal exactly on full output sequences (2/9/20/2000 digits). Intuition scores 1.000 on the same inputs. The three channels realize the same computation.

### 4.2 Intuition carries structure, not symbols (C3)

- **Symbol permutation (exp41)**: 26080 digit renamings during training, tested on original symbols — invariance 0.996→0.987. The intuition channel realizes structural relations (successor/iteration/carry), not digit signifiers.
- **Step-skipping zero decay (exp80)**: 2000 digits / radix 60 / 100% anonymization / joint, all 1.000. The compiled structure extrapolates without decay.
- **Machine form (exp90)**: 20-digit addition compiles 82 construction tokens into 5 intuition tokens — the skip is visible in the token stream. Honest caveat: the atomic token is outside the model vocab (pad id 0); measurement is the sequence-length effect, a lower bound.

### 4.3 Acquisition–generalization decoupling (C4)

| Epochs | 1 | 2 | 3 | 5 | 8 |
|---|---|---|---|---|---|
| Judgment acc (full suite) | 0.001 | 0.214 | 0.244 | 0.781 | 0.996 |

Acquisition is monotone but config-dependent (8 epochs for the full suite). The same converged model then extrapolates with zero decay (§4.2). The "hard to obtain" and "easy to skip" facts coexist; they describe obtain (training) and generalize (inference), respectively.

## 5 Discussion

**What the equivalence does not say.** We do not claim the three philosophical positions are identical in their epistemology; we claim they are equivalent as *execution channels of one system*. The historical disagreement concerned the nature of mathematical truth; our claim concerns the architecture of a computing system that realizes mathematical objects. The philosophical positions are models of what a mathematical object is; we show one system can realize all three models of the same object consistently.

**Anti-Platonism.** Intuition is compiled construction, not an a priori faculty. If mathematical structure were innate (Platonism / nativism), then definitionally-impoverished concepts would still generalize; they do not (P1 §8: an impoverished vocabulary requires an order of magnitude more training; genuinely under-defined tokens never generalize). The intuition channel's competence is earned by compilation, not endowed.

**Positional vs constructive content.** Structuralism says an object is its position; the intuition channel locates the object in the learned structure. Intuitionism says an object is its construction; the construction channel unfolds it. The equivalence of the channels shows the two descriptions coincide — for objects whose definitions are complete. This is the machine-level form of the old structuralist–intuitionist rapprochement.

## 6 Related Work

- **Computational Trinitarianism** (Curry–Howard): programs = proofs = types. We extend the three-way identification to execution channels of one neural system.
- **Constructive mathematics / type theory** (Martin-Löf 1984; Bishop): existence = constructibility. Our construction channel is its machine form.
- **Structuralism / Bourbaki; Gärdenfors conceptual spaces**: object = position in a structure/geometry. Our intuition channel is its neural realization.
- **Formalism / Hilbert; rewriting systems**: object = sign manipulation. Our formal channel is the definition-driven engine.
- **Dual-process cognition** (Kahneman): System 1/2. Our intuition/reasoning separation is the System 1/2 split with a compilation account of how System 1 is built.
- **Dual-systems in math cognition** (e.g. number sense / deliberate arithmetic): our three channels refine the two-system picture with a verifiable equivalence.

## 6.5 Mathematical-domain validation: the Riemann-direction case

The three-channel account is not confined to arithmetic. In a companion formalization
(Lean 4 / mathlib, claims C011–C025, all PROVED, novelty KNOWN, no sorry), the
intuition chain "the complex axis is a high-dimensional projection of −1; primes land
on translated integer points; 1/2 is the inversion–translation symmetry center; the
complex axis is curled" was carried through all three channels:

- **Construction** (definition-driven): the ComplexAxis algebra (a + bJ, J² = −1),
  projection proj⟨a,b⟩ = a, lifting, basepoint drift;
- **Formal** (rewriting): Lean 4 proofs of projection non-preservation, prime-circle
  structure (8 lattice points as a single orbit under rotation × conjugation, via
  Gaussian-integer UFD), Euler-product convergence (Re(s) > 1), and the critical-line
  geometry;
- **Intuition** (compiled structure): the same objects are reached directly by the
  intuition chain, skipping textbook derivation.

**Projection recovery theorem** (`proj_not_recoverable` / `proj_recoverable_symmetry`,
Lean-proved): *lost structure is not recoverable; symmetry directions are recoverable.*
Under projection, the imaginary-axis direction (i vs −i) is lost and cannot be recovered,
while the real-axis sign symmetry (r vs −r) is preserved. This is the mathematical
counterpart of EXP-61h (§4): the intuition channel is position-insensitive (it drops
positional detail like projection drops the J direction) yet preserves semantic symmetry —
matching "scrambled letters do not impede understanding; deliberate logic on the scramble
loses meaning" (G5b, P1). Projection is the mechanism of the fast path: dropping
irrelevant structure irrecoverably is what makes the direct route cheap.

**Token economy of intuition-guided formalization** (methodological data): the full
C011–C025 formalization consumed ≈700k tokens, of which 99.2% were context-cache
re-transmission; net new content < 1%. The intuition chain hit known structures directly
(heap/torsor, sums of two squares, circle inversion, functional-equation symmetry),
avoiding textbook derivation — an efficiency datum for G5 at the token level, independent
of the arithmetic experiments in §4.

## 7 Limitations

1. The equivalence is demonstrated on the supported calculus (formalized definitions), not on all of mathematics.
2. The intuition channel is statistical, not guaranteed; equivalence is verified (held-out) and falls back to construction, not proven.
3. The atomization result (exp90) is a sequence-length lower bound, not a claim of learned atomic semantics.

## 8 Conclusion

The three positions of the foundations dispute — construction, structure, sign — are realized as three equivalent execution channels of one neural system. Construction = formal exactly; intuition agrees at 1.000; the intuition channel carries structure, not symbols; and it is hard to obtain but easy to generalize by skipping steps. Intuition is compiled construction. A century-old split in the foundations of mathematics is, at least for a formalized calculus, an architectural fact about how many ways one system can realize the same object — and all of them agree.

## Appendix

- A. Full experiment tables: docs/paper_data/results.csv.
- B. Relation to P1 propositions (G0, G5, R) and P2 compilation.
- C. Formal-verification direction (Lean): construction ≡ intuition ≡ formal, for the supported calculus.

---

## Unified Conclusion (added 2026-08-11)

Once, under a unified formal attention-syntactic structure, a neural network ultimately,
inevitably, and necessarily clearly, intuitively, and interpretably observes the boundary
between intuition and construction, we can with full confidence use the unified
attention-formal language to direct logical construction, use precise synthetic-CoT
logical construction to earn *flashing intuition*, and use distilled intuitive context
to exhaustively search attention forms. Form, construction, and intuition co-adapt
within the unified framework, forming a feedback iteration pipeline of teaching, training,
and reasoning in which they are no longer distinct — perhaps one of the faster shortcuts
among the many paths toward ASI.


## Cross-References within the Unified Framework

This paper is one leg of the *Unified Framework of Representation, Logic, and Intuition*
(manifesto: `Unified_Framework_Representation_Logic_Intuition.md`). The three legs
co-adapt:

| Leg | Paper | Claim |
|---|---|---|
| form → construction | P1 (this paper) | correct syntax → extreme training speed; correct construction → extreme generalization |
| construction → intuition | P0 (three-channel equivalence) | construction = formal = intuition; intuition is compiled construction |
| construction → intuition (method) | P2 (neural macro compilation) | compile the slow construction path into the fast reasoning path |

Cyclic closure: form directs construction (P1), construction earns intuition (P0/P2),
intuition searches form (the fast path extrapolates and re-expresses in the unified form).
The unified conclusion — form directs logical construction, construction earns flashing
intuition, intuition exhaustively searches forms — is stated in the manifesto and in each
paper's Unified Conclusion.
