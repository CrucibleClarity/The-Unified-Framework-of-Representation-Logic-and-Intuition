# Artifact — 0pat Exercise XXV: Orthogonal Euler Circles as an Observation Frame

## Build

```bash
# Lean 4.32.2 + mathlib v4.32.2
lean proof.lean   # 0 errors, 0 warnings, 0 sorry
```

## Theorems (7, all 0pat)

| Theorem | Statement |
|---|---|
| orthogonal_frame_crt | m.Coprime n ⟹ ZMod (m*n) ≃+* ZMod m × ZMod n (CRT, ZMod.chineseRemainder) |
| factor_observable_zero | p ∣ a ⟹ (a : ZMod p) = 0 (prime factor visible as zero projection) |
| distinct_primes_observable | p ≠ q ⟹ (p : ZMod q) ≠ 0 (distinct primes distinguished) |
| card_units_zmod_prime | Fintype.card (ZMod p)ˣ = p − 1 (reused from Ex. XXIV) |
| fermat_little | a.Coprime p ⟹ a^(p−1) ≡ 1 [MOD p] (reused from Ex. XXIV) |
| fermat_little_complete | ∀ a, a^p ≡ a [MOD p] (reused from Ex. XXIV) |
| prime_unit_on_other_circle | p ≠ q ⟹ p^(q−1) ≡ 1 [MOD q] (unit of foreign circle group) |

## Genealogy coordinate

(R23, C3) prime circle × analytic number theory — double-modulus
observation frame = CRT + Fermat. No complex plane: pure Z/nZ algebra.
Connects XXIII (composite = prime factorization) and XXIV (prime circle).

## Provenance

Original pat insight: src/pat-excercises/exercises/25_orthogonal_euler_circles/
(pat insight: observe the prime axis through two orthogonal Euler circles;
Euler-circle ↔ real-axis mapping already formalized in Stereographic.lean /
CircleCore.lean — coordinate legitimacy, not new structure).
0pat re-formalization: pure mathlib, no pat concepts.

## Double-blind

No author / affiliation / email / repository identifiers.
