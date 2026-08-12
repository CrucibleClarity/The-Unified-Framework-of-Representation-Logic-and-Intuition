# CPP 2026 Submission — Basepoint-Relative Stability and Codomain Drift

## Submission metadata (double-blind)

- **Track**: CPP (Certified Programs and Proofs) 2026, formalization track
- **Anonymous**: paper + artifact contain no author / affiliation / email / DOI / repository identifiers
- **Novelty**: original transport theorem (C006) and generation transport-covariance (R011); classical heap/torsor baseline KNOWN
- **Claims**: C001–C010, all PROVED, no `sorry`, full `lake build` passes

## Content

```
paper.tex              ACM acmart [sigconf,anonymous] paper (8 sections + appendix inventory)
refs.bib               bibliography (4 entries)
artifact/
  README.md            artifact build + theorem inventory + double-blind note
  formal/              11 Lean files under Formal/ZeroRelative/, lakefile.toml, lean-toolchain (mathlib v4.32.2)
  claims/              C001–C010 claim ledger (YAML)
```

## Build

1. Paper: `pdflatex paper && bibtex paper && pdflatex paper && pdflatex paper`
2. Artifact:
   ```bash
   cd artifact/formal
   lake build           # no errors
   grep -r "sorry" .    # no output
   ```

## Theorem inventory

- C001–C003: semiconjugacy of heap endomorphisms (KNOWN baseline)
- C004: heap retract recovers abelian group at any basepoint (KNOWN)
- C005: torsor–heap correspondence (KNOWN)
- C006: basepoint-change map $T_{e\to f}$ is an automorphism; transports step translation (`transport_is_aut`, `step_transport`) (ORIGINAL)
- C007: displacement space $D(H)$ is basepoint-independent (relative stability) (`dispRel_is_equivalence`, `displacement_coord_bijective`) (KNOWN + formalized)
- C008: finitary reachability downgraded to baseline (presupposes $\mathbb{N}$)
- C009: minimal closure defined without $\mathbb{N}$ indexing
- C010/R011: pure-heap generation is transport-covariant, $\mathrm{Chain}(\sigma_f,f) = T_{e\to f}(\mathrm{Chain}(\sigma_e,e))$ (`chain_transport_eq`) (ORIGINAL)

## Honest boundary

The paper does not claim to resolve the Riemann Hypothesis or any analytic question.
It formalizes the heap-theoretic algebra of basepoint relativity. RH-related
material is out of scope for this submission.

## Reviewer guidance

The key checkable claims are the Lean theorems in `artifact/formal/`: rerun
`lake build`, inspect `transport_is_aut` (C006) and `chain_transport_covariant`
(C010/R011). The paper's conclusion is exactly the dichotomy:

> Basepoint choice stabilizes relative structure while drifting the codomain,
> with $T$ as the isomorphism bridge.
