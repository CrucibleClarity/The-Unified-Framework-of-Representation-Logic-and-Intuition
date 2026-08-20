# Artifact — 0pat Exercise XXIV: The Prime Axis as a Circle (Fermat's Little Theorem)

## Build

```bash
# Lean 4.32.2 + mathlib v4.32.2
lean proof.lean   # 0 errors, 0 warnings, 0 sorry
```

## Theorems (4, all 0pat)

| Theorem | Statement |
|---|---|
| card_units_zmod_prime | Fintype.card (ZMod p)ˣ = p − 1 (explicit bijection {x ≠ 0} ≃ Fin (p−1)) |
| fermat_little | a.Coprime p ⟹ a^(p−1) ≡ 1 [MOD p] (Lagrange: orderOf_dvd_card + pow_orderOf_eq_one) |
| fermat_little_complete | ∀ a, a^p ≡ a [MOD p] (non-coprime: p ∣ a ⟹ both sides ≡ 0, via Nat.ModEq.pow) |
| infinitely_many_primes | ∀ n, ∃ p ≥ n, Nat.Prime p (mathlib: Nat.exists_infinite_primes) |

## Genealogy coordinate

(R23, C3) prime circle × analytic number theory — multiplicative circle
group (Z/pZ)^×, Fermat's little theorem. No complex plane: pure Z/pZ algebra.

## Provenance

Original pat exercise: src/pat-excercises/exercises/24_prime_circle/
(pat insight: prime axis periodized = circle, Euler-circle observation method,
Riemann-direction implementation without complex plane).
0pat re-formalization: pure mathlib, no pat concepts.

## Double-blind

No author / affiliation / email / repository identifiers.
