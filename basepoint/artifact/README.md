# CPP 2026 Artifact — Basepoint-Relative Stability and Codomain Drift

## Overview

Machine-checked Lean 4 / mathlib formalization of heap-theoretic basepoint-relative
structure. Claims C001–C010 are PROVED, no `sorry`, full `lake build` passes.

## Content

```
Formal/
  ZeroRelative/
    Heap.lean          heap laws, retract group (add_at e, neg_at e, group laws)
    Displacement.lean  displacement equivalence, D(H) recovery
    Generation.lean    reachability Reach (TransGen) and successor uniqueness
    Semiconj.lean      semiconjugacy (C001–C003)
    TorsorHeap.lean    torsor–heap correspondence (C005)
    StepTranslation.lean  step translation transport (C006)
    BasepointGen.lean  pure-heap generation, chain transport (R011)
    NatSource.lean / OmegaType.lean / FixedPoint.lean / GaloisInsertion.lean
    ... (11 files)
claims/
  C001.yaml .. C010.yaml   claim ledger
lakefile.toml              build configuration (mathlib v4.32.2)
lean-toolchain             Lean version pin
```

## Build

```bash
cd Formal/..
lake build          # full build, no errors, no sorry
grep -r "sorry" .    # expected: no output
```

## Theorem highlights

| Theorem | Lean name |
|---|---|
| heap retract group laws | `heap_retract_group_laws`, `add_assoc/comm/left_id/right_id/left_neg/right_neg` |
| T is an automorphism | `transport_is_aut`, `transport_heap` |
| step translation transport | `step_transport` |
| displacement equivalence | `dispRel_is_equivalence` (refl/symm/trans) |
| D(H) recovery | `displacement_coord_bijective` |
| minimal closure | `Chain` (least fixed point) |
| R011 transport-covariance | `chain_transport_eq`, `generated_structure_iso` |
| semiconjugacy | `semiconj_*` |
| torsor–heap | `torsor_heap_*` |

## Honest boundary

Classical heap/torsor facts (C004, C007) are KNOWN. The transport theorem (C006)
and the generation transport-covariance (C010/R011) are original, machine-checked
contributions.

## Double-blind note

This artifact contains no author, affiliation, DOI, or repository identifiers.
