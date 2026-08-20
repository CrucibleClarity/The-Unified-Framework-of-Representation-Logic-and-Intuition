# CPP 2027 Submission — 0pat Exercise XXXVII: The Riemann Direction, Unified

## Paper

- Exercise_XXXVII_Riemann_Direction_Unified.tex — acmart, anonymous
- refs.bib

Compile: `tectonic Exercise_XXXVII_Riemann_Direction_Unified.tex`

## Content

Unified machine-checked development of the Riemann direction
(13 exercises XXIV–XXXVI merged + new theorems), 101 declarations
(89 theorems + 12 lemmas), 0 errors, 0 sorry:

- prime structure: infinitely many primes, Fermat's little theorem,
  unit groups of prime residue rings
- observation frame: split-complex plane, orthogonal Euler circles
  (radius 1 and radius i), transposition
- intersections: axes × critical circle × prime circles
  (prime circle meets critical circle iff p ∈ {2,3})
- compression of the imaginary part: coefficient axes, product leak
  with sign = unit square
- divergence–period structure of the zeta series: modulus split,
  mirror pairs, conjugation, functional equation (mathlib
  riemannZeta_one_sub), convergence region
- zeta conjugation: conj(ζ(s)) = ζ(conj s) on Re s > 1 (series form)
  and Re s < 0 (functional-equation conjugation + cancellation),
  χ-conjugation (conj(χ(s)) = χ(conj s))
- zero structure: zero reflection, prime-factor zeros on the
  imaginary axis (1−p^{−s} = 0 ⟺ s·ln p = 2πik), trivial zero
  condition (cos(πs/2) = 0 ⟺ s = 2k+1), critical-line observation
  (Re s = 1/2 ⟺ ‖n^s‖ = n^{1/2})
- the real axis as iteration of i: i^i = e^{−π/2}, ticks (i^i)^n,
  prime ticks = undecomposable iterations
- completed zeta structure: Λ(1−s) = Λ(s), Λ₀ entire
  (mathlib completedRiemannZeta_one_sub, differentiable_completedZeta₀)

Honest boundary: the Riemann hypothesis is not claimed; the artifact
records twelve numerical observations (critical strip, zero locations,
base-point shift, phase projection, exhaustive radius searches).

## Artifact

- artifact/formal/proof.lean — the 101-declaration proof
- artifact/observation.md — 12 numerical observation records
- artifact/README.md — build + theorem inventory + provenance

## Double-blind note

No author / affiliation / email / DOI / repository identifiers.
