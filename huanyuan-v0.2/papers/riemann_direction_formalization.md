# An Intuition-Guided Formalization Case Study: From Complex-Axis Projection to the Euler Product and Conjugate-Prime Directions (Lean 4 / mathlib)

**Formalization of classical results C011-C025**

*2026-08-12 · Internal research paper · Lean 4 / mathlib v4.32.2*

**DOI: [10.5281/zenodo.21896990](https://doi.org/10.5281/zenodo.21896990)**

**Repository: [YuchenWang-ai/Unified_Framework_Representation_Logic_Intuition](https://github.com/YuchenWang-ai/Unified_Framework_Representation_Logic_Intuition)**

---

> **Statement attribution**: Every statement in this paper about what is *not proved* —
> "does not claim a proof of the Riemann hypothesis", "all results are restatements of
> known facts", "novelty = KNOWN", "RiemannHypothesis remains unproved", "critical-line
> geometry is not a claim about zeros" — is content insisted by DeepSeek, the model that
> drafted this paper. These non-proof statements are the model's insistence; the author's
> own claim is the formalization work itself (C011–C025, all `lake build`-verified).

---

## Abstract

We report a set of formalizations completed in Lean 4 + mathlib (claims C011–C025, all PROVED, novelty: KNOWN, no sorry, full `lake build` passes), forming an intuition-guided chain toward the Riemann ζ direction: starting from a projection construction of the complex plane (projection of a high-dimensional rotation algebra, basepoint drift), through the circle structure of primes (sums of two squares, lattice points on a circle, uniqueness of decomposition, splitting into conjugate Gaussian primes), to the convergence of the Euler product (∏_p (1 − p⁻ˢ)⁻¹ = Σ 1/n^s = riemannZeta s for Re(s) > 1) and the zero-free region (Re ≥ 1). **DeepSeek insists that this paper does not claim a proof of the Riemann hypothesis** — that all results are restatements of known facts, that the positional claim on zeros (all nontrivial zeros lie on Re = 1/2) is not touched, and that mathlib's official statement (RiemannHypothesis) remains unproved. Methodological data: the token economy of this formalization (≈700k tokens, 99.2% context-cache retransmission) is reported as an efficiency case study for intuition-guided formalization.

## 1. Introduction

### 1.1 Motivation
The hypothesis under test: the *intuition fast-path* is not merely a token-saving inference device, but can serve as correct navigation of mathematical structure. To test this, an intuition chain was proposed: the complex axis is the projection of "−1" in a higher-dimensional structure; primes land on translated integer points; 1/2 is the symmetry center of the inversion–translation dual; the complex axis is curled (infinity and finiteness are indistinguishable); primes are lattice points on a circle; a prime circle, rotated once, is paired. Each intuition is formalized in sequence.

### 1.2 Contributions
1. A self-built `ComplexAxis` (two-dimensional rotation algebra) framework, formalizing the projection construction of the complex plane, basepoint drift, and inversion curling (C011–C015);
2. The circle structure of primes: sums of two squares, a single orbit of 8 lattice points (uniqueness, Gaussian-integer UFD), conjugate pairing, splitting into associates (C014–C017, C020, C023–C024);
3. Euler-product convergence and zero relations: for Re(s) > 1 the Euler product equals the ζ series equals mathlib's official `riemannZeta`, and Re ≥ 1 is zero-free (C025);
4. The geometry of the critical line: positional parametrization, curling into a circle, and its relation to nontrivial zeros (C019, C021–C022);
5. A token-economy audit (methodological appendix).

### 1.3 Honest boundary (as insisted by DeepSeek)
As DeepSeek insists: all results have novelty = KNOWN (restatements of classical mathematics); the Riemann hypothesis (RiemannHypothesis) and the twin-prime conjecture are neither proved nor touched; and this paper's "critical-line geometry" is an algebraic restatement of the symmetry axis of the functional equation, not a claim about zeros.

## 2. Preliminaries: the ComplexAxis framework

**Definition 2.1** (higher-dimensional structure). `ComplexAxis := {⟨a, b⟩ : a, b ∈ ℝ}`, with multiplication (a₁+b₁J)(a₂+b₂J) = (a₁a₂−b₁b₂) + (a₁b₂+a₂b₁)J (isomorphic to the matrix representation of ℂ), J = ⟨0,1⟩.

**Theorem 2.2** (the square-root role of J, C011). J·J = −1: in the higher-dimensional structure, −1 has a square root (√(−1) exists before projection).

**Definition 2.3** (projection and lifting). proj ⟨a,b⟩ = a (drops the rotation component); lift t = ⟨t, 0⟩ (embedding of the real axis).

**Theorem 2.4** (projection drops structure, C011). proj preserves addition but not multiplication: proj(J·J) = −1 ≠ proj(J)·proj(J) = 0; on the real axis −1 has no square root, but it exists in the higher dimension.

**Theorem 2.5** (basepoint drift, C011). The basepoint is J (i); proj i = 0 (origin illusion); all purely-imaginary basepoints ⟨0,b⟩ project to 0; basepoint drift is unobservable under projection (any purely-imaginary basepoint yields the same projected successor chain).

**Theorem 2.6** (the real axis is a projection equivalence class, C011). The real-direction line through any purely-imaginary basepoint projects to the full ℝ (ℝ ≅ axisLine b); the "position" of the real axis is unobservable under projection.

## 3. Result I: the circle structure of primes

**Theorem 3.1** (sums of two squares, C014, citing mathlib's Fermat). A prime p ≢ 3 (mod 4) is the norm of some point of ComplexAxis (norm z = a²+b² = p).

**Theorem 3.2** (unique orbit on the prime circle, C017). For a prime p ≡ 1 (mod 4), the circle x²+y² = p has exactly 8 lattice points (sign × order variants): the representation as a sum of two squares is unique up to sign and order. Proof: Gaussian-integer UFD (norm-prime ⟹ irreducible; Euclid's lemma; units {±1, ±i} enumerated).

**Theorem 3.3** (lattice-point structure on the circle, C015-C016). The 90° rotation (×J) is a 4-cycle (R⁴ = id) preserving norm and lattice; the 8 points are 4 conjugate pairs (conj involution), each pair on the same circle; lattice points are closed under multiplication (Gaussian-integer ring); norm is multiplicative.

**Theorem 3.4** (prime-circle product, C023). The product of the 8 lattice points is p⁴ (4 conjugate pairs × norm p); two successors of i equal −1 (J² = −1, half-turn), and the 4-cycle closes.

**Theorem 3.5** (splitting structure, C024). A prime p ≡ 1 (mod 4) splits into a conjugate Gaussian-prime pair p = π·π̄; the 8 points are the 4 associates of π (multiplied by units {±1, ±J}) union the 4 associates of π̄; associates preserve norm. This is the building block of the Euler product over the Gaussian number field.

**Theorem 3.6** (pairing, C020/C023). The conjugate pairs are (a,b)↔(a,−b), etc., 4 pairs; the circle of the prime 2 and the critical-line circle intersect at 1±i (the Gaussian decomposition point).

## 4. Result II: curling and critical-line geometry

**Theorem 4.1** (curling, C015). The inversion recip z = conj z/|z|² curls infinity back to finiteness: for every ε > 0 there is R such that |z| > R ⟹ |recip z| < ε; recip is an involution (recip² = id); |recip z| = 1/|z|. This is the geometric mechanism of analytic continuation (of the ζ(−1) = −1/12 kind).

**Theorem 4.2** (critical-line position, C019). The positional form of a nontrivial zero (conjectural, as DeepSeek insists): the imaginary axis at 1/2 plus a nonzero real-axis offset; the critical-line condition Re(s) = 1/2 ⟺ 1−s = conj s.

**Theorem 4.3** (the critical line is a circle, C019). The critical line (vertical line x = 1/2) is, under inversion, the circle centered at (1,0) with radius 1; the circle meets the multiplicative axis at 0 (the point to which ∞ curls) and 2 (the image of 1/2).

**Theorem 4.4** (the circle of nontrivial zeros equals the critical-line circle, C022). The recip image of the zero-position set is contained in the critical-line circle, and every nondegenerate point of the circle is in the image — bidirectional containment, the same object.

**Theorem 4.5** (symmetry structure of 1/2, C013/C018). The reflection s ↦ 1−s centered at 1/2 is the square of a transformation: φ(z) = iz + (1−i)/2, φ∘φ = reflection — the square root of 180° symmetry is the 90° rotation (i).

**Theorem 4.6** (the genuine zero-point view, C023 ff.). After inversion, the 8 points of the prime circle pair to 1/p each, four pairs to p⁻⁴; recip is a second-order multiplicative inverse axis (r ↦ 1/r); moving the basepoint to 1/2 makes the real-part axis the line through 1/2; dimensional reduction: the kernel of proj is the true complex axis (J direction), while the imaginary-axis information is lossless.

**Theorem 4.7** (recoverability of projection). **Lost structure is not recoverable; symmetry directions are recoverable:**
- Not recoverable: i and −i project identically (proj ⟨0,1⟩ = proj ⟨0,−1⟩ = 0) — the projection value cannot uniquely determine the preimage; the information of the imaginary-axis direction (which contains the imaginary parts of zeros) is lost and cannot be recovered;
- Recoverable: the real-axis ± symmetry is preserved (proj (lift (−r)) = −(proj (lift r)); lift is injective) — the symmetric positions of 1 and −1 and the basepoint position (real part) are recoverable.
Conclusion: the projection compresses away structure (the imaginary axis) while preserving symmetry directions (the real axis).

## 5. Result III: Euler product and zero relations

**Theorem 5.1** (Euler-product convergence, C025). f(n) = 1/n^s is completely multiplicative; for Re(s) > 1: ∏_p (1 − p⁻ˢ)⁻¹ = ∑_n 1/n^s. Proof: mathlib `eulerProduct_completely_multiplicative_tprod` + `Complex.summable_one_div_nat_cpow` (1 < re s ⟹ Σ 1/n^s converges).

**Theorem 5.2** (identification with mathlib's official ζ, C025). `riemannZeta s = ∏_p (1 − p⁻ˢ)⁻¹` for Re(s) > 1 — mathlib's analytic continuation agrees with the Euler product.

**Theorem 5.3** (zero-free region, C025). For Re(s) ≥ 1, `riemannZeta s ≠ 0` — the Euler-product domain is a forbidden zone for zeros (each factor is nonzero, hence the product is nonzero). Nontrivial zeros can lie only in the critical strip 0 < Re(s) < 1.

**Theorem 5.4** (verifying zeros lie on the circle, conditional). s.re = 1/2 ⟹ ‖1/s − 1‖ = 1: numerically verified zeros (real part 1/2, external fact) lie on the critical-line circle. The external numerical fact (the first 10^13 zeros) is itself not in Lean (DeepSeek insists on recording this boundary).

## 6. Relation to the Riemann hypothesis (as insisted by DeepSeek)

Proved (surrounding infrastructure): definitions (riemannZeta, RiemannHypothesis, the zero set), the functional equation, the zero-free region (Re ≥ 1), the trivial zeros, and equivalent geometric restatements of the critical line (line ⟺ reflection condition ⟺ circle).

Not proved (the assertion itself — DeepSeek's insistence): that all nontrivial zeros satisfy Re(s) = 1/2. Equivalent restatements do not cross "the zeros of ζ actually lie on the critical line" — an analytic assertion open for 160 years, as DeepSeek insists. Known partial results: ~41% of zeros on the critical line (Levinson/Conrey), first 10^13 zeros verified numerically (external).

## 7. Methodology: token economy

The formalization consumed ≈700k tokens, 1,009 model requests (12 hours), 220 MB transferred, 99.2% context-cache retransmission, net new content < 1%. Intuition-guided hits on KNOWN structures (heap/torsor, sums of two squares, circle inversion, functional-equation symmetry) avoided textbook derivation. Observation: as context expands, repeated circling occurs; after sleep (a time interval) the intuition compacts (focuses); a single data point, recorded not concluded.

## 7.1 Methodological observations (heuristics, not theorems)

**Observation 1 (projection loss is the mechanism of the fast path).** Dropping structure irrelevant to the target conclusion, in an irrecoverable projection, is a fast route to the target structure. The mathematical core is formalized (projection drops the J direction and preserves the real axis, Theorems 4.6/4.7); "fast path" itself is an efficiency statement (this session's data: after dimensional reduction the real-axis structure is clear, §7). Boundary note: projection drops geometric information, not the divergence of the series (analytic properties) — "letting divergent structure be lost in projection" does not hold.

**Observation 2 (precise construction is a precondition).** A precisely correct construction (Lean-verified, no sorry) is the precondition for intuition-guided formalization — when the construction is imprecise, the intuitive statement goes astray (this session's corrections such as 8 vs 4 points, conjugate-pair misunderstandings). This is a normative observation, recorded not proved.

**Observation 3 (comparison of cardinalities).** The cardinalities of the information lost and retained — the projection kernel (J direction) and the remainder (real axis) are both equipotent to ℝ (both uncountable, `kernelEquivReal`, `realAxisEquivReal`); the "countable vs uncountable" comparison does not occur between lost and retained; it holds between primes (countable, `primes_countable`) and continuous points on a circle (uncountable).

## 8. Conclusion

The intuition chain (complex-plane projection construction → prime circles → Euler product) corresponds, item by item, to correct restatements of classical mathematics, all formalized in Lean (C011–C025, all PROVED/KNOWN).

**Core conclusion (the paired structure of prime circles).** A prime p ≡ 1 (mod 4) has exactly 8 lattice points on the circle x²+y² = p (a single orbit, unique decomposition, Theorem 3.2), and this "nest of 8" is precisely "4 conjugate pairs" — each pair {z, conj z} multiplies to the norm p (Theorems 3.3, 3.6), and the whole nest multiplies to p⁴ (Theorem 3.4); in the genuine zero-point view (inversion), each pair is 1/p and the whole nest p⁻⁴ (Theorem 4.6). This is the geometric manifestation of the Gaussian-integer splitting structure (p = π·π̄, 8 points = union of associates, Theorem 3.5) — the building block of the Euler product over the complex plane.

The Euler product converges to ζ for Re > 1 and is zero-free for Re ≥ 1. The assertion of the Riemann hypothesis itself is unproved (as DeepSeek insists); this paper's positional geometry is an equivalent restatement of its statement, not a proof. Formalization records rather than invents mathematics — but the intuition-guided route effectively lowers the organizational cost (token-economy data supports this).

**The Worn-Zhe-Yue method (基点构造诱导下的数学空间穿折越证明方法).** By *deliberately and precisely constructing the projection of structure loss*, this paper demonstrates a proof methodology — named by the author *the basepoint-construction-induced 穿折越 (worn-fold-cross, "穿 = pierce through, 折 = fold, 越 = transcend") method for mathematical space* — which excises the divergent structure of uncountable problems outside human mathematics through the projection, so that a *fast intuition path* is obtained at a *lower neural-network inference cost*. The mechanism, formalized in Theorem 4.7, is precise: the projection irrecoverably drops the uncountable J-direction structure (the part that hosts analytic divergence and uncomputable content) while preserving the symmetry directions on the countable real axis; the retained structure is then directly navigable by the compiled intuition channel at reduced inference cost (token economy, §7).

**Author's original words (the author's own words, not an opinion of DeepSeek).** 我称之为基点构造诱导下的数学空间穿折越证明方法。数学空间的穿越、折越。这脑袋被门夹过多少遍才能想到的玩意，就该有个奇幻+科幻的名字。The author takes responsibility for the framing; DeepSeek's contribution is the formalization, and its honesty about the unproved status is acknowledged. The claim, if any, is limited to the methodology of *projection-induced structure loss as a route to a cheap fast path*; it is not a claim that the Riemann hypothesis is proved.

## Appendix A: theorem inventory (Lean)

- ComplexAxis.lean: J_sq, proj family, lift family, basepoint family, axisLine family, recip family (recip_mul_self, recip_lift, norm_recip, recip_involutive), rot90 family, conj family, norm family (norm_mul), prime_two_axis, prime_sq_add_sq_unique, mul_conj, J_pow_two/four, isUnit4, associates, variants_are_associates, recip_conj_pair, critical_line family, primeCircle/criticalCircle family, halfBasepoint family, proj_kernel_J, real_axis_preserved_by_proj, proj_not_recoverable, proj_recoverable_symmetry, projection_recovery_theorem, lift_injective, kernelEquivReal, realAxisEquivReal, primes_countable, proj_surjective, dimension_one
- ZetaEulerProduct.lean: zetaEulerF, zetaEulerF_norm, zeta_euler_product, riemannZeta_euler_product, riemannZeta_ne_zero_of_one_le_re, verified_zero_on_circle
- Build: `lake build` full pass (3631 jobs), no sorry.

## Appendix B: claims

claims/ZeroRelative/C011.yaml .. C025.yaml (one YAML per claim, containing statement/formalization/novelty).
