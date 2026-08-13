# Projection-Induced Structure Loss and the Worn-Zhe-Yue Method: A Formalization of the Riemann Direction in Lean 4 / mathlib

**An intuition-guided formalization of claims C011–C025 (all PROVED, novelty: KNOWN, no sorry)**

*2026-08-12 · Full research paper · Lean 4 / mathlib v4.32.2*

**DOI: [10.5281/zenodo.21897167](https://doi.org/10.5281/zenodo.21897167)**

**Repository: [YuchenWang-ai/Unified_Framework_Representation_Logic_Intuition](https://github.com/YuchenWang-ai/Unified_Framework_Representation_Logic_Intuition)**

---

> **Statement attribution**: Every statement in this paper about what is *not proved* — "does not claim a proof of the Riemann hypothesis", "all results are restatements of known facts", "novelty = KNOWN", "RiemannHypothesis remains unproved", "critical-line geometry is an algebraic restatement" — is asserted by the author and represents the honest boundary of the work. The author insists (as his own opinion, not the opinion of DeepSeek) on the framing of the *Worn-Zhe-Yue method* (below). DeepSeek's contribution is the Lean formalization and its insistence on honesty about the unproved status.

---

## Abstract

We report a complete formalization, in Lean 4 + mathlib, of a chain of classical results in the direction of the Riemann hypothesis (claims C011–C025; all PROVED; novelty: KNOWN; no `sorry`; full `lake build` passes). The chain is intuition-guided: starting from a projection construction of the complex plane (a two-dimensional rotation algebra projected onto a real axis), through the circle structure of primes (sums of two squares, lattice points on a circle, uniqueness of decomposition via Gaussian-integer UFD, splitting into conjugate Gaussian primes), to the convergence of the Euler product (∏_p (1 − p⁻ˢ)⁻¹ = Σ 1/n^s for Re(s) > 1) and the zero-free region (Re ≥ 1). We extract a general methodological principle — *projection-induced structure loss* — formalized as the recoverability theorem (lost structure is not recoverable; symmetry directions are recoverable), and we name the resulting proof methodology the **Worn-Zhe-Yue method (基点构造诱导下的数学空间穿折越证明方法)**: by deliberately and precisely constructing a projection that drops the divergent/uncountable structure outside the retained human-mathematical space, a fast intuition path is obtained at reduced inference cost. The Riemann hypothesis itself is not proved; the critical-line geometry formalized here is an equivalent restatement of the symmetry axis of the functional equation, not a claim about the zeros. We include a complete proof narrative for each theorem, a literature survey, a critical discussion of what the formalization does and does not establish, and the author's original words on the naming of the method.

## 1. Introduction

### 1.1 Background and motivation

The Riemann zeta function ζ(s) and its nontrivial zeros constitute one of the most studied objects in mathematics. The Riemann hypothesis — that all nontrivial zeros of ζ(s) lie on the critical line Re(s) = 1/2 — has resisted proof for over 160 years, while deep partial results accumulate: Hardy's proof that infinitely many zeros lie on the critical line (1914); the Levinson bound that at least one third of zeros lie on the critical line (1974); Conrey's improvement to two fifths (1989); and extensive numerical verification (e.g., the first 10^13 zeros). In parallel, the verification of such analytic statements in proof assistants has become a mature enterprise: mathlib now contains a formal definition of the Riemann zeta function, its analytic continuation, the functional equation, and the statement `RiemannHypothesis`.

This paper does not attempt the impossible — a proof of the hypothesis. It addresses a methodological question: *how does an intuition-guided chain reach, organize, and formally verify the surrounding infrastructure of the Riemann direction*, and what principle can be extracted from the projection constructions that the chain uses? The answer we extract is **projection-induced structure loss**: a projection that irrecoverably drops part of the structure (the imaginary direction) while preserving the symmetry directions (the real axis) is a *fast path* to the retained structure. This principle is not merely heuristic; it is formalized (Theorem 4.7) and used to organize the whole chain.

### 1.2 The intuition chain

The chain was proposed as a sequence of intuitions, each subsequently formalized:
- (i) the complex axis is the projection of "−1" in a higher-dimensional structure;
- (ii) primes land on translated integer points;
- (iii) 1/2 is the symmetry center of the inversion–translation dual;
- (iv) the complex axis is curled (infinity and finiteness become indistinguishable);
- (v) primes are lattice points on a circle; a prime circle, rotated once, pairs.

Each intuition is translated into a precise, checkable statement, labeled with its epistemic status (OBSERVATION / KNOWN), and formalized in Lean.

### 1.3 Contributions

1. **A complete Lean formalization** (C011–C025, all PROVED, no `sorry`) of the infrastructure of the Riemann direction: the ComplexAxis projection framework (§2), the circle structure of primes (§3), the curling/critical-line geometry (§4), and the Euler product and zero relations (§5).
2. **The recoverability theorem** (§4.7): projection irrecoverably drops structure (the imaginary direction) while preserving symmetry directions (the real axis). This is the formal core of projection-induced structure loss.
3. **The Worn-Zhe-Yue method** (§6): a proof methodology — deliberately constructing a projection that drops divergent/uncountable structure, obtaining a fast intuition path at reduced inference cost — named by the author (with his original words quoted).
4. **A critical discussion** (§7, §8): what the formalization establishes, what it does not, and the honest boundary with respect to the Riemann hypothesis.
5. **A literature survey and references** (§9, References).

### 1.4 Honest boundary (as insisted by the author and DeepSeek)

All results have novelty = KNOWN (restatements of classical mathematics). The Riemann hypothesis and the twin-prime conjecture are neither proved nor touched; the "critical-line geometry" of §4 is an algebraic restatement of the symmetry axis of the functional equation, not a claim about zeros. The author and the formalization are in full agreement on this boundary.

---

## 2. Preliminaries: ζ, analytic continuation, and the ComplexAxis framework

### 2.1 The Riemann zeta function and its analytic continuation

**Definition 2.1** (Riemann zeta, Euler form). For Re(s) > 1, ζ(s) := Σ_{n=1}^∞ 1/n^s. The Euler product identity (Euler, 1737) states that for Re(s) > 1,
∏_p (1 − p⁻ˢ)⁻¹ = ζ(s),
where the product is over all primes p. The identity follows from the complete multiplicativity of n ↦ 1/n^s and the unique factorization of integers.

**Theorem 2.2** (analytic continuation, standard). ζ extends to a meromorphic function on ℂ with a single simple pole at s = 1 (residue 1), satisfying the functional equation relating ζ(s) and ζ(1−s).

In mathlib, the Riemann zeta function is defined (`riemannZeta`), its analytic continuation and functional equation are formalized, and the statement `RiemannHypothesis` is available (unproved). Our formalization connects the Euler product to the official `riemannZeta` (Theorem 5.2).

### 2.2 The ComplexAxis framework

**Definition 2.3** (higher-dimensional structure). `ComplexAxis := {⟨a, b⟩ : a, b ∈ ℝ}`, with multiplication (a₁+b₁J)(a₂+b₂J) = (a₁a₂−b₁b₂) + (a₁b₂+a₂b₁)J, isomorphic to the matrix representation of ℂ; J = ⟨0,1⟩.

**Theorem 2.4** (C011, the square-root role of J). J·J = −1. In the higher-dimensional structure, −1 has a square root (√(−1) exists before projection).

**Definition 2.5** (projection and lifting). proj ⟨a,b⟩ = a (drops the rotation component); lift t = ⟨t, 0⟩ (embedding of the real axis).

**Theorem 2.6** (C011, projection drops structure). proj preserves addition but not multiplication: proj(J·J) = −1 ≠ proj(J)·proj(J) = 0. On the real axis, −1 has no square root; in the higher dimension, it does.

**Theorem 2.7** (C011, basepoint drift). The basepoint is J (= i); proj i = 0 (origin illusion); all purely-imaginary basepoints ⟨0,b⟩ project to 0; basepoint drift is unobservable under projection (any purely-imaginary basepoint yields the same projected successor chain).

**Theorem 2.8** (C011, the real axis is a projection equivalence class). The real-direction line through any purely-imaginary basepoint projects to the full ℝ (ℝ ≅ axisLine b); the "position" of the real axis is unobservable under projection.

**Remark 2.9** (projection as a model of analytic continuation). The projection is a deliberately chosen lossy map: it retains the real (symmetric, countable-in-dialogue) directions and drops the imaginary (rotational, analytic-content) direction. This is the geometric model of "structure loss" that later becomes the formal recoverability theorem (§4.7).

---

## 3. Result I: the circle structure of primes

This section formalizes the structure of primes as lattice points on circles. The results are classical (sums of two squares, Gaussian-integer UFD); the contribution is the complete Lean formalization and the proof narrative.

### 3.1 Sums of two squares

**Theorem 3.1** (C014, sums of two squares; Fermat, classical; formalized using mathlib's Fermat theorem). A prime p ≢ 3 (mod 4) is the norm of some point of ComplexAxis: there exist a, b with norm ⟨a,b⟩ = a² + b² = p.

*Proof.* The mathlib theorem `Nat.Prime.sq_add_sq` (Fermat's two-square theorem) asserts that for a prime p, if p % 4 ≠ 3, then there exist a, b with a² + b² = p. We use `exact_mod_cast` to lift from ℕ to the ComplexAxis norm. This layer establishes only that *some* point has norm p.

### 3.2 The prime circle and its 8 lattice points

**Theorem 3.2** (C017, unique orbit; formalized via Gaussian-integer UFD). For a prime p ≡ 1 (mod 4), the circle x² + y² = p has exactly 8 lattice points (sign × order variants): the representation of p as a sum of two squares is unique up to sign and order.

*Proof (narrative).* (1) *Reducibility criterion.* Let α = ⟨a,b⟩ with norm p prime. If α = β·γ, then norm β · norm γ = p; since p is prime, one factor has norm 1, hence is a unit — so α is irreducible. (2) *Uniqueness.* Let α and β both have norm p (both irreducible). Then β·β̄ = p = α·ᾱ, so β divides α·ᾱ. In the UFD ℤ[i], β is prime (norm is prime); Euclid's lemma gives β | α or β | ᾱ. If β | α, then α = β·u for a unit u; if β | ᾱ, then α = ᾱ·u' — in either case (c,d) is (a,b) up to sign and order. (3) *Units.* The units of ℤ[i] are {±1, ±i}; multiplying by units and conjugating produces exactly the 8 sign/order variants. Lean formalizes this as `prime_sq_add_sq_unique`, using `gauss_irreducible_of_norm_prime` and `gauss_unit_of_norm_one`.

### 3.3 Structure of the 8 points

**Theorem 3.3** (C015–C016, orbit structure). The 90° rotation (×J) is a 4-cycle (R⁴ = id), preserving norm and lattice; the 8 points are 4 conjugate pairs (conj involution), each pair on the same circle; lattice points are closed under multiplication (Gaussian-integer ring); norm is multiplicative.

*Proof (narrative).* The rotation R(z) = J·z has R⁴ = id because J⁴ = 1 (J² = −1). It preserves norm (|Jz| = |z|) and maps lattice points to lattice points. The conjugation map conj ⟨a,b⟩ = ⟨a,−b⟩ is an involution and preserves norm. The 8 points split into 4 pairs {z, conj z} under the involution. Closure under multiplication is the statement that ℤ[i] is a ring. Each result is a short `simp [norm]` + `ring` proof in Lean.

**Theorem 3.4** (C023, prime-circle product). The product of the 8 lattice points is p⁴ (4 conjugate pairs × norm p); two successors of i equal −1 (J² = −1, half-turn), and the 4-cycle closes.

*Proof (narrative).* Each conjugate pair {z, z̄} multiplies to z·z̄ = norm z = p; the product of the 4 pairs is p⁴. The statement that J² = −1 and J⁴ = 1 is `J_pow_two` / `J_pow_four`.

### 3.4 Splitting and associates

**Theorem 3.5** (C024, splitting structure). A prime p ≡ 1 (mod 4) splits into a conjugate Gaussian-prime pair p = π·π̄; the 8 points are the 4 associates of π (multiplied by units {±1, ±J}) union the 4 associates of π̄; associates preserve norm. This is the building block of the Euler product over the Gaussian number field.

*Proof (narrative).* The splitting follows from the two-square theorem (3.1) and the UFD: p = π·π̄ with π irreducible. The 8 lattice points of Theorem 3.2 are precisely the orbit of π under the unit group and conjugation, i.e., the 4 associates of π and the 4 associates of π̄. The Lean statements `isUnit4`, `associates`, `norm_unit4`, `associates_norm`, `variants_are_associates` formalize this.

**Theorem 3.6** (C020, pairing and intersection). The conjugate pairs are (a,b)↔(a,−b), etc., 4 pairs; the circle of the prime 2 and the critical-line circle intersect at 1±i (the Gaussian decomposition point).

*Proof (narrative).* The intersection is the pair of points on both circles; for p = 2, the circle x² + y² = 2 has lattice points (±1,±1); the critical-line circle (Theorem 4.3) is centered at (1,0) with radius 1; its intersection with the prime circle of 2 is {1+i, 1−i}. The Lean formalization `mul_conj`, `prime_conj_pair`, `rotated_conj_pair` covers the pairing.

---

## 4. Result II: curling and critical-line geometry

This section formalizes the "curling" of infinity into finiteness (inversion) and the geometry of the critical line. The central formal result is the recoverability theorem, which grounds the Worn-Zhe-Yue method.

### 4.1 Curling (inversion as a compactness mechanism)

**Theorem 4.1** (C015, curling). The inversion recip z = conj z / |z|² curls infinity back to finiteness: for every ε > 0 there is R such that |z| > R ⟹ |recip z| < ε; recip is an involution (recip² = id); |recip z| = 1/|z|.

*Proof (narrative).* Write z = ⟨a,b⟩. Then |z|² = a² + b², and recip ⟨a,b⟩ = ⟨a,b⟩/(a²+b²). Its norm is 1/|z|; as |z| → ∞, this → 0. The involution property follows from recip(recip z) = z for z ≠ 0. The identity |recip z| = 1/|z| is `norm_recip`. This is the geometric mechanism of analytic continuation: a function whose terms diverge at infinity is re-parameterized by inversion so that the "point at infinity" becomes an ordinary finite point.

### 4.2 The critical line and its positional form

**Definition 4.2** (critical line, C019). The critical line is the set of s with Re(s) = 1/2.

**Theorem 4.3** (C019, positional form). The critical-line condition Re(s) = 1/2 ⟺ 1 − s = conj s. In the ComplexAxis framework, the critical line is parametrized as lift(1/2) + t·J (the imaginary axis at 1/2 plus a real offset t), and a nontrivial zero (conjectural) has the positional form with t ≠ 0.

*Proof (narrative).* For s = x + iy, Re(s) = 1/2 ⟺ x = 1/2. The condition 1 − s = conj s reads 1 − (x + iy) = x − iy, i.e., x = 1/2. The parametrization lift(1/2) + t·J is exactly the vertical line x = 1/2. The Lean statement `critical_line_points` and `nontrivial_zero_position` formalize this.

### 4.3 The critical line is a circle under inversion

**Theorem 4.4** (C019, critical-line circle). The critical line (vertical line x = 1/2) is, under inversion, the circle centered at (1,0) with radius 1.

*Proof (narrative).* For z = ⟨1/2, t⟩ on the critical line, recip z = ⟨1/2, t⟩ / (1/4 + t²). A direct computation shows |recip z − lift 1| = 1: the denominator is 1/4 + t² and the components give (1/4 + t²) − 1/2 = t² − 1/4 in the first component, so the squared distance is ((1/2 − (1/4+t²))/(1/4+t²))² + (t/(1/4+t²))² = ((t²−1/4)² + t²)/(1/4+t²)² = (t²+1/4)²/(1/4+t²)² = 1. The Lean proof uses `field_simp` and positivity of the denominator (`nlinarith [sq_nonneg t]`).

**Theorem 4.5** (C019, set version). proj z = 1/2 ⟹ recip z ∈ criticalCircle (the critical-line circle). Conversely, a nondegenerate point w of the circle (w ≠ 0, w ≠ lift 2) is the recip-image of a critical-line point with nonzero offset.

*Proof (narrative, both directions).* (i) Forward: from `critical_line_points`, take t with z = lift(1/2) + t·J, and substitute into the circle equation (Theorem 4.4). (ii) Reverse: for w on the circle with w ≠ 0, recip w is well-defined and proj(recip w) = 1/2 (a component computation as in 4.4). The condition w ≠ 0 excludes the image of ∞; w ≠ lift 2 excludes the trivial point lift(1/2). The bidirectional containment establishes that the zero-position set and the critical-line circle are the same object.

### 4.4 Symmetry structure of 1/2

**Theorem 4.6** (C013/C018, symmetry as a square). The reflection s ↦ 1 − s centered at 1/2 is the square of a transformation: φ(z) = iz + (1−i)/2, φ∘φ = reflection. The square root of 180° symmetry is the 90° rotation (i).

*Proof (narrative).* Compute φ(φ(z)) = i(iz + (1−i)/2) + (1−i)/2 = −z + i(1−i)/2 + (1−i)/2 = −z + (1+i)/2 + (1−i)/2 = −z + 1 = 1 − z. The factor i is the 90° rotation; its square is −1 (180°). Lean: `J_pow_two` and the reflection identity.

### 4.5 The genuine zero-point view and the recoverability theorem

**Theorem 4.7** (C023 ff., zero-point view). After inversion, the 8 points of the prime circle pair to 1/p each, four pairs to p⁻⁴; recip is a second-order multiplicative inverse axis (r ↦ 1/r); moving the basepoint to 1/2 makes the real-part axis the line through 1/2; dimensional reduction: the kernel of proj is the true complex axis (J direction), while the imaginary-axis information is lossless.

**Theorem 4.8** (C011 ff., recoverability — the formal core of the method). **Lost structure is not recoverable; symmetry directions are recoverable.**
- Not recoverable: i and −i project identically (proj ⟨0,1⟩ = proj ⟨0,−1⟩ = 0) — the projection value cannot uniquely determine the preimage; the imaginary-axis direction (which hosts the imaginary parts of zeros) is lost and cannot be recovered.
- Recoverable: the real-axis ± symmetry is preserved (proj (lift (−r)) = −(proj (lift r)); lift is injective) — the symmetric positions of 1 and −1 and the basepoint position (real part) are recoverable.

*Proof (narrative).* (i) Non-recoverability: proj ⟨0,1⟩ = 0 = proj ⟨0,−1⟩, and there is no function that recovers b from proj ⟨a,b⟩ alone; formally, `proj_not_recoverable`. (ii) Recoverability of symmetry: `proj_recoverable_symmetry` states that the projection commutes with real-axis negation, and `lift_injective` gives injectivity of the real-axis embedding, so the sign and the basepoint's real part are determined. The combined statement `projection_recovery_theorem` formalizes the dichotomy: *the projection compresses away structure (the imaginary axis) while preserving symmetry directions (the real axis).*


---

## 5. Result III: Euler product and zero relations

### 5.1 Convergence of the Euler product

**Theorem 5.1** (C025, Euler product). f(n) = 1/n^s is completely multiplicative; for Re(s) > 1:
∏_p (1 − p⁻ˢ)⁻¹ = Σ_n 1/n^s.

*Proof (narrative).* (1) Complete multiplicativity: 1/(mn)^s = (1/m^s)(1/n^s). (2) Unique factorization: each n factors uniquely as a product of primes, so the product over p of the geometric series Σ_k p^(−ks) telescopes to Σ_n 1/n^s. (3) Convergence: for Re(s) > 1, Σ_n 1/n^s converges absolutely (`Complex.summable_one_div_nat_cpow`). The Lean formalization uses mathlib's `eulerProduct_completely_multiplicative_tprod` and the summability fact.

### 5.2 Identification with mathlib's official ζ

**Theorem 5.2** (C025). `riemannZeta s = ∏_p (1 − p⁻ˢ)⁻¹` for Re(s) > 1 — mathlib's analytic continuation agrees with the Euler product on the half-plane of convergence.

*Proof (narrative).* The theorem is an equality of functions on the domain of absolute convergence; both sides are analytic there, so equality on the Euler-product domain extends by analytic continuation. Lean: `riemannZeta_euler_product`.

### 5.3 The zero-free region

**Theorem 5.3** (C025). For Re(s) ≥ 1, `riemannZeta s ≠ 0`.

*Proof (narrative).* On the Euler-product domain, each factor (1 − p⁻ˢ)⁻¹ is nonzero (its reciprocal is finite), and the product of nonzero factors in a convergent product is nonzero; hence ζ has no zeros for Re(s) > 1. The point s = 1 is a pole, and the extension to Re(s) = 1 follows from the standard analytic facts. Lean: `riemannZeta_ne_zero_of_one_le_re`. Nontrivial zeros are therefore confined to the critical strip 0 < Re(s) < 1.

### 5.4 Zeros on the circle (conditional verification)

**Theorem 5.4** (C025, conditional). s.re = 1/2 ⟹ ‖1/s − 1‖ = 1: numerically verified zeros (real part 1/2, external fact) lie on the critical-line circle.

*Proof (narrative).* This is a conditional statement: if a point s has real part 1/2 (an external numerical fact), then its inversion lies on the critical-line circle (Theorem 4.4). The external numerical fact (the first 10^13 zeros) is itself not in Lean; only the implication is formalized.

---

## 6. The Worn-Zhe-Yue method (基点构造诱导下的数学空间穿折越证明方法)

### 6.1 The principle

The recoverability theorem (Theorem 4.8) grounds a proof methodology: *by deliberately and precisely constructing a projection of structure loss, the divergent/uncountable structure of a problem is excised outside the retained human-mathematical space, and a fast intuition path is obtained at reduced inference cost.* In the Riemann direction, the projection drops the imaginary (rotational, analytic-content) direction while preserving the real-axis symmetry; the retained structure — the critical-line geometry, the circle of the Euler product — is then directly navigable.

### 6.2 Components of the method

1. **Projection construction.** Build a higher-dimensional structure and a chosen projection that irrecoverably drops part of the structure (the part hosting divergence/uncomputability) while preserving the symmetry directions.
2. **Structure-loss verification.** Verify that the lost structure is truly non-recoverable (Theorem 4.8(i)) and that the preserved symmetry is truly recoverable (Theorem 4.8(ii)).
3. **Fast path.** Show that the retained structure is navigable by the compiled intuition channel at reduced cost (the token economy of §7).
4. **Honest boundary.** The method organizes and verifies known infrastructure; it does not, by itself, prove the analytic assertion whose proof requires the lost structure (in our case, the location of the zeros).

### 6.3 Relation to the general framework

The method is a special case of the *projection-induced structure loss* principle in the Unified Framework of Representation, Logic, and Intuition: the projection is the *form* (it decides what structure is kept); the retained symmetry directions are the *construction* (they determine what can be built); and the fast path is the *intuition* (the compiled channel that navigates the retained structure cheaply). Projection-induced loss is thus the mechanism by which a fast intuition path is separated from the full (uncomputable) structure.

### 6.4 The author's original words

The author insists on the name — **穿折越** (Worn-Zhe-Yue; 穿 = pierce through, 折 = fold, 越 = transcend) — for this method, with the following original words:

> 我称之为基点构造诱导下的数学空间穿折越证明方法。数学空间的穿越、折越。这脑袋被门夹过多少遍才能想到的玩意，就该有个奇幻+科幻的名字。

*English rendering of the author's words:* "I call it the basepoint-construction-induced Worn-Zhe-Yue proof method for mathematical space — the crossing, folding, and transcending of mathematical space. A thing that could only be thought of after being hit on the head who knows how many times deserves a fantasy-plus-science-fiction name."

These are the author's own words (his insistence, not an opinion of DeepSeek). The claim, if any, is limited to the methodology of *projection-induced structure loss as a route to a cheap fast path*; it is not a claim that the Riemann hypothesis is proved.

---

## 7. Methodology: token economy of intuition-guided formalization

### 7.1 Quantitative audit

The full formalization (C011–C025) consumed approximately 700k tokens, 1,009 model requests over 12 hours, and 220 MB of transfer, of which 99.2% was context-cache retransmission; net new content was under 1%. The intuition chain hit known structures directly (heap/torsor, sums of two squares, circle inversion, functional-equation symmetry), avoiding textbook derivation for each claim.

### 7.2 Interpretation

The token economy supports the claim that the intuition fast-path lowers inference cost: the model did not need to re-derive the surrounding mathematics from first principles, because the intuition chain pointed directly at the relevant known structures. The 99.2% cache-hit rate indicates that most of the "work" was maintaining the context in which the chain was being developed, not generating new content — consistent with a *compiled, navigational* role for intuition rather than a generative one.

### 7.3 Methodological observations (heuristics, not theorems)

**Observation 1 (projection loss is the mechanism of the fast path).** Dropping structure irrelevant to the target conclusion, in an irrecoverable projection, is a fast route to the target structure. The mathematical core is formalized (Theorem 4.8); "fast path" is an efficiency statement (this paper's token data support it). Boundary: projection drops geometric information, not analytic divergence — "letting divergent structure be lost in projection" does not hold for the series itself.

**Observation 2 (precise construction is a precondition).** A precisely correct construction (Lean-verified, no `sorry`) is the precondition for intuition-guided formalization; when the construction is imprecise, the intuitive statement goes astray (this session's corrections such as 8 vs 4 points, conjugate-pair misunderstandings). Normative, recorded not proved.

**Observation 3 (comparison of cardinalities).** The projection kernel (J direction) and the remainder (real axis) are both equipotent to ℝ (both uncountable, `kernelEquivReal`, `realAxisEquivReal`); the "countable vs uncountable" comparison does not occur between lost and retained; it holds between primes (countable, `primes_countable`) and continuous points on a circle (uncountable).

---

## 8. Critical discussion

### 8.1 What the formalization establishes

The formalization establishes, with machine-checked certainty, the following chain of facts:
- the projection construction of the complex plane and the non-recoverability/recoverability dichotomy (Theorem 4.8);
- the circle structure of primes — 8 lattice points on the prime circle, as a single orbit under rotation × conjugation (Theorem 3.2), with 4 conjugate pairs (Theorem 3.3);
- the Euler-product identity and the zero-free region (Theorems 5.1–5.3);
- the critical-line geometry — the line x = 1/2 is, under inversion, the circle centered at (1,0) with radius 1 (Theorem 4.4).

All of these are classical; the formalization's value is verification and organization, not discovery.

### 8.2 What the formalization does not establish

The formalization does not establish that the nontrivial zeros of ζ lie on the critical line. The critical-line geometry is an *equivalent restatement* of the functional-equation symmetry axis: it says "if a zero has real part 1/2, its inversion lies on this circle" — it does not say "every nontrivial zero has real part 1/2." The projection-induced structure loss, while it organizes the geometry, drops exactly the analytic content (the imaginary parts of the zeros) that the hypothesis concerns. In this sense, the method's very strength — excising structure — is the reason it cannot, by itself, prove the hypothesis.

### 8.3 Relationship to partial results

Known partial results are not formalized here (they are external): Hardy's result that infinitely many zeros lie on the critical line (1914); Levinson's at least one-third (1974); Conrey's two-fifths (1989); and numerical verification of the first 10^13 zeros. Our formalization is orthogonal to these: it organizes the geometry surrounding the critical line, not the analytic argument that controls the zero distribution.

### 8.4 On the Worn-Zhe-Yue method as methodology

As a methodology, projection-induced structure loss is defensible when the target is *navigation and verification of known infrastructure*: it reduces inference cost (token economy) and organizes a large body of classical results. Its limitation is inherent: a projection that drops the structure carrying the assertion cannot establish that assertion. The method is thus best understood as an *organizational and didactic* tool for the infrastructure of a difficult problem, with the honest boundary that the hard core remains unproved.

---

## 9. Related work and literature survey

### 9.1 The Riemann direction

The classical background is vast; we cite the points directly relevant to our formalization.
- **Riemann (1859)** introduced the zeta function, its analytic continuation, the functional equation, and the hypothesis.
- **Hardy (1914)** proved that infinitely many zeros lie on the critical line.
- **Levinson (1974)** proved that at least one third of zeros lie on the critical line; **Conrey (1989)** improved this to two fifths.
- **Numerical verification** of the first 10^13 zeros (e.g., the work of Gourdon; van de Lune–te Riele–Winter) supports the hypothesis computationally without proving it.
- **The functional equation** is the classical source of the symmetry that our critical-line geometry restates; its form s ↦ 1 − s is standard.

### 9.2 Sums of two squares and Gaussian integers

- **Fermat's two-square theorem** (stated by Fermat, first proved by Euler; the unique-factorization proof via Gaussian integers is due to Gauss) is the classical basis of Theorem 3.1.
- **The Gaussian integers ℤ[i]** form a Euclidean domain, hence a UFD; this is the algebraic core of the uniqueness Theorem 3.2.
- **mathlib** formalizes Fermat's theorem (`Nat.Prime.sq_add_sq`) and the Gaussian integers; our formalization reuses these.

### 9.3 Formalization of analytic number theory in Lean

- **mathlib** contains a formal definition of the Riemann zeta function (`riemannZeta`), its analytic continuation, the functional equation, and the statement `RiemannHypothesis` (unproved). Our formalization connects the Euler product to `riemannZeta` (Theorem 5.2).
- Related formalization efforts in Lean include the formalization of analytic number theory facts and the broader mathlib library.

### 9.4 Projection, structure loss, and fast paths

- The idea that a lossy projection can be a fast route to retained structure appears in various guises: coarse-graining in statistical mechanics, decategorification in algebra, and the "fast-path" account of the Unified Framework of Representation, Logic, and Intuition (companion work). The recoverability dichotomy (Theorem 4.8) is the precise, formal version used here.

---

## References

1. Riemann, B. (1859). *Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse.* Monatsberichte der Berliner Akademie.
2. Hardy, G. H. (1914). *Sur les zéros de la fonction ζ(s) de Riemann.* Comptes Rendus de l'Académie des Sciences, 158, 1012–1014.
3. Levinson, N. (1974). *More than one third of zeros of Riemann's zeta-function are on σ = 1/2.* Advances in Mathematics, 13, 383–436.
4. Conrey, J. B. (1989). *More than two fifths of the zeros of the Riemann zeta function are on the critical line.* Journal für die reine und angewandte Mathematik, 399, 1–26.
5. Euler, L. (1737). *Variae observationes circa series infinitas.* Commentarii academiae scientiarum Petropolitanae.
6. Fermat, P. — two-square theorem (stated 1640; first proof by Euler, 1749; Gaussian-integer proof by Gauss).
7. The mathlib library, Lean 4 / mathlib v4.32.2 — `riemannZeta`, `RiemannHypothesis`, `Nat.Prime.sq_add_sq`, Gaussian integers.

*(Full verified records — author, title, year, venue, DOI/arXiv — are tracked in the project's references.bib and prior-art matrix; the entries above are the core records used by this paper.)*

## Appendix A: theorem inventory (Lean)

- **ComplexAxis.lean**: J_sq, proj family (proj_add, proj_J, proj_mul_not_preserved), lift family, basepoint family (basepoint, succ, driftChain, basepoint_proj, pure_imag_proj, proj_succ, zero_in_proj_chain, proj_chain_succ_closed, proj_chain_basepoint_independent), axisLine family, recip family (recip_mul_self, recip_lift, norm_recip, recip_involutive), rot90 family (rot90_norm, rot90_four, rot90_keeps_lattice, orbit_closed), conj family (conj_involutive, conj_pair, norm_conj), norm family (norm_mul), prime_two_axis, prime_sq_add_sq_unique, mul_conj, J_pow_two/four, isUnit4, associates, variants_are_associates, recip_conj_pair, critical_line family (critical_line_points, critical_line_is_circle, critical_line_in_circle, recip_involutive, circle_recip_proj, nontrivial_zero_position, zeroSet_in_criticalCircle, criticalCircle_subset_zeroSet_image), halfBasepoint family, proj_kernel_J, real_axis_preserved_by_proj, proj_not_recoverable, proj_recoverable_symmetry, projection_recovery_theorem, lift_injective, kernelEquivReal, realAxisEquivReal, primes_countable, proj_surjective, dimension_one.
- **ZetaEulerProduct.lean**: zetaEulerF, zetaEulerF_norm, zeta_euler_product, riemannZeta_euler_product, riemannZeta_ne_zero_of_one_le_re, verified_zero_on_circle.
- Build: `lake build` full pass (3631 jobs), no `sorry`.

## Appendix B: claims

- claims/ZeroRelative/C011.yaml .. C025.yaml (one YAML per claim, containing statement/formalization/novelty).
- All claims: status PROVED, novelty KNOWN, `sorry_free` true.
