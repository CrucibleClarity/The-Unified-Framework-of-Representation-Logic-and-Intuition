# Artifact — 0pat Exercise XXIII: Composite Numbers as Prime Factorization

## Build

```bash
# Lean 4.32.2 + mathlib v4.32.2
lean proof.lean   # 0 errors, 0 sorry
```

## Theorems (4, all 0pat)

| Theorem | Statement |
|---|---|
| factorization_represents | n ≠ 0 ⟹ ∏ p^(n.factorization p) = n |
| factorization_support_prime | p ∈ supp ⟹ prime p |
| factorization_unique | prime support ∧ product = n ⟹ f = n.factorization |
| composite_has_prime_factor | 1 < n ∧ ¬prime n ⟹ ∃ p prime, p ∣ n ∧ p < n |

## Genealogy coordinate

(R23, C3) prime circle × analytic number theory — fundamental theorem of arithmetic.

## Provenance

Original pat exercise: src/pat-excercises/exercises/23_composite_projection/
(pat claim R234: composite = multiple projection superpositions of primes).
0pat re-formalization: pure mathlib, no pat concepts.

## Double-blind

No author / affiliation / email / repository identifiers.
