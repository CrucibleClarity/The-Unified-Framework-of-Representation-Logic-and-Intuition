/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

/-!
# R020 theorems: projective probe structure of the observable-family residual

Review (2026-08-07): the probe q_γ(D) = [γ ∈ ker D] satisfies q_γ = q_{λγ} for
λ ≠ 0, so the effective probe parameter space is the projective space
P^1(F_3) with (3^2-1)/(3-1) = 4 directions. Two consequences:

  T1: q_γ = q_{λγ} (λ ≠ 0) — probes are projective, so there are exactly
      (q^n-1)/(q-1) independent directions.
  T2: the response vector over all projective directions uniquely determines
      ker D (verified: 6 response classes = 6 kernel classes, 0 conflicts).
  T3 (minimality, hypothesis refined in the follow-up review): IF the
      realizable kernel family K_realizable contains {0} AND every one-dim
      subspace (i.e. {0} ∪ Gr(1, F_q^k) ⊆ K_realizable), THEN any zero-test
      separating family must query every projective direction, so needs
      (q^n-1)/(q-1) directions; fewer leaves K={0} and K=L (a skipped line)
      indistinguishable. In the unrestricted-linear-model (D : F_q^k → V
      arbitrary) dim V >= k-1 is a SUFFICIENT condition for that inclusion,
      but the theorem states only the realizability hypothesis — later
      restricted generation models do not force a change to the theorem.
      Without the hypothesis the problem is a separating/hitting problem on
      the realizable kernel family (not a universal minimum).

  Third review note: the sequence 2 -> 2 -> 4 -> 5 -> 6 is one PATH in the
  partition lattice {Q_P : P ⊆ P^(k-1)}, refinement Q_P ⪯ Q_P'; not canonical.

T1 is the algebraic core (domain: nonzero scalar cancellation).
-/

namespace R020

/-- T1 (general field): in a field K, a nonzero scalar l satisfies
l * b = 0  iff  b = 0.  Hence q_γ = q_{λγ} for λ ≠ 0: scaling the probe by a
nonzero scalar does not change the zero-test. -/
theorem probe_scalar_inv_general {K : Type*} [Field K] (l b : K) (hl : l ≠ 0) :
    (l * b = 0) ↔ (b = 0) := by
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hl
  · intro h
    simp [h]

/-- T1 specialized: the probe value at gamma = (g1,g2) on configuration (d1,d2)
is unchanged under nonzero scalar scaling of gamma. -/
theorem probe_scalar_inv_projective {K : Type*} [Field K] (g1 g2 d1 d2 l : K)
    (hl : l ≠ 0) :
    (l * (g1 * d1 + g2 * d2) = 0) ↔ (g1 * d1 + g2 * d2 = 0) := by
  exact probe_scalar_inv_general l (g1 * d1 + g2 * d2) hl

-- T2/T3 (statement; numeric verification in R020_probe_family.py):
--   number of projective directions for F_q^n is (q^n - 1)/(q - 1);
--   F_3^2 gives 4 directions, kernel types 1 + 4 + 1 = 6;
--   fewer directions cannot separate the zero kernel from a skipped one,
--   GIVEN the hypothesis {0} ∪ Gr(1, F_q^k) ⊆ K_realizable (realizable kernel
--   family contains 0 and all 1-dim subspaces; dim V >= k-1 is a sufficient
--   condition for it in the unrestricted-linear-model). Otherwise:
--   separating/hitting problem on realizable kernels.

end R020
