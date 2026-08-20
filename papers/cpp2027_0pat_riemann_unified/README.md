# CPP 2027 Submission — 0pat Exercise XXXVII: The Riemann Direction, Unified

## Paper

- Exercise_XXXVII_Riemann_Direction_Unified.tex — acmart, anonymous
- refs.bib

Compile: `tectonic Exercise_XXXVII_Riemann_Direction_Unified.tex`

## Content

Unified machine-checked development of the Riemann direction
(13 exercises XXIV–XXXVI merged + new theorems), 138 declarations
(122 theorems + 15 lemmas + 1 def), 0 errors, 0 sorry:

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
- conjugation symmetry: conj(ζ(s)) = ζ(conj s) on the critical strip
  (Re/Im split: even real part, odd imaginary part; zero = common zero
  of both parts)
- p-adic split (base point p): ζ = O_p + E_p, zero = common zero of
  both parts; odd-part extra zeros lie on the imaginary axis (p = 2)
- Euler-circle split norm: zeros avoid both orthogonal Euler circles
  (Re²−Im² = 0, between radius-1 and radius-i circles)
- affine base-point shifts keep the critical line a line
  (the circle view comes only from the 1/z inversion)
- base point 1 (center of the critical-line circle): on-line ⟺
  equidistance ‖w‖ = ‖1+w‖ (vertical bisector; circle = unit circle)
- base point i (origin of the observation frame): the critical line is
  the perpendicular bisector of i and 1+i; T(z) = 1/(z−i) − 1 sends it
  to the unit circle (one base point resolves circle image + translation/
  inversion cancellation)
- explicit phase of χ (non-Γ part): arg 2^(1/2+it) = t·ln 2,
  arg π^(−1/2+it) = t·ln π, sin(π/4+iπt/2) = sin(π/4)cosh + i·cos(π/4)sinh
  — the whole multiplier winding except Gamma (Stirling) is explicit
- multi-axis phase superposition: each term n^−(1/2+it) = n^{−1/2}·(cos(t·ln n) − i·sin(t·ln n))
  (every frequency axis ln n explicit; arg ζ net winding ≈ 0 — the small S(T) term)
- Gamma phase reduction by symmetry: Legendre doubling + reflection + conjugation
  eliminate the Gamma phase combination in N(T)−N₀(T) (no Stirling);
  the doubling multiplier 2^{1/2−it} has explicit linear phase −t·ln 2
- Gamma modulus by symmetry: |Γ(1/2+it)|² = π/cosh(πt) exactly
  (reflection Γ(s)Γ(1−s) = π/sin(πs) + conjugation + sin explicit —
  the Stirling modulus is replaced by symmetry, no asymptotics)
- zero region: ζ has no zeros on Re ≥ 1 (mathlib) nor on Re ≤ 0
  (functional-equation mirror) — nontrivial zeros lie in 0 < Re < 1
- orbit counting: zeros form conjugate orbits of 2 points (on the
  critical line) or 4 points (off it); RH ⟺ all orbits degenerate

Honest boundary: the Riemann hypothesis is not claimed; the artifact
records thirty-five observation records (critical strip, zero locations,
base-point shift, phase projection, conjugation counts) and a
machine-checked conjugation/orbit development (117 declarations,
0 errors, 0 sorry).

## Artifact

- artifact/formal/proof.lean — the 138-declaration proof
- artifact/observation.md — 35 observation records
- artifact/README.md — build + theorem inventory + provenance

## Double-blind note

No author / affiliation / email / DOI / repository identifiers.
