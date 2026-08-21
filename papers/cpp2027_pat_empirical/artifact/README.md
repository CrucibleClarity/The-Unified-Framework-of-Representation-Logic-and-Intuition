# Artifact — Empirical Foundations of Pat: Transformer OOD Observations, Structural Laws, and Machine-Checked Theorems

## Structure

```
artifact/
├── formal/        Lean 4 formalization (26-file minimal dependency closure)
│   ├── Formal/Toolkit/*.lean     source files
│   ├── lakefile.toml             build config (mathlib v4.32.2)
│   ├── lean-toolchain            Lean 4.32.2
│   └── claims/                   claim ledger (R136/R138/R143/R149/R150/R151/R163
│                                 YAML + R031 completeness document)
└── evidence/      Training experiment (E12 succ-matrix, reproducible)
    ├── run_all.py                one-command reproduction (5 groups × 3 seeds)
    ├── succ_matrix_exp.py        the E12 experiment itself
    ├── configs.json              full task configuration
    ├── runtime/                  self-contained training runtime snapshot
    │                             (tokenizer/train/synth/lab, no build cache)
    └── results/                  all recorded outputs + results report
```

## Build

### Formalization (Lean)

```bash
# Lean 4.32.2 + mathlib v4.32.2 (pinned by lean-toolchain)
cd formal
lake build        # builds the six target modules, 0 errors, 0 sorry
grep -r "sorry" Formal | wc -l   # 0
```

The six build targets are the six theorem modules of the paper:
`Formal.Toolkit.MutualLocking`, `Formal.Toolkit.Pat4Phase`,
`Formal.Toolkit.PatCountableInfinitPhaseUnification`,
`Formal.Toolkit.ContinuumPatGrid`, `Formal.Toolkit.ContinuumConstructible`,
`Formal.Toolkit.MappingJudgmentTheorems`. The 26-file closure in
`Formal/Toolkit/` is exactly the transitive import dependency of these
six modules (computed by import-chain analysis); no other files are
needed.

### Training experiment (Python)

```bash
# Python >= 3.12 + PyTorch >= 2.0 (CPU works, ~5x slower); numpy via torch
cd evidence
python3 run_all.py        # output → results/run_all_out.txt
# if the shell's python3 is hijacked, set PYTHON=/path/to/venv/bin/python3
```

Expected outcome (reproduced in three independent executions):
training accuracy 1.000 in all 45 runs (5 groups × 3 seeds × 3 runs);
OOD 1a (same notation) 32/32, 1b (same-basepoint zero-shot, other
notation) 0/32, 2 (equivalence bridging) 32/32, 2' (control) 32/32,
4 (symmetry-special) 32/32. Judgment: full-sequence token-by-token
reconstruction (end-truth), not positional accuracy.

## Theorems (22, all PROVED, 0 sorry)

| Claim | File | Theorems |
|---|---|---|
| R143 interlock | `MutualLocking.lean` | `magnitude_locks_phase_round_trip`, `mutual_lock_invertible` (det = θ·(r+1/r) ≠ 0), `magnitude_pair_log_mirror` |
| R149 four-phase | `Pat4Phase.lean` | `quadriphase_interlock`, `axis_pair_orthogonal`, `extrapolation_to_pat_circle`, `infinite_isomorphic_extrapolation` |
| R150 countable grid + density | `PatCountableInfinitPhaseUnification.lean` | `pat_grid_countable`, `pat_phase_unification` (∀ε ∃x∈patGrid, |θ−x| ≤ ε), `infinite_isomorphic_extrapolation`, `pat_countable_infinite_phase_unification_law`, `wang_phase_locking_consistency` |
| R151 continuum closure | `ContinuumPatGrid.lean` | `continuum_in_pat_grid_closure` ([0,2π] ⊆ closure(patGrid)) |
| R163 endogenous closure | `ContinuumConstructible.lean` | `InPat_dyadic`, `dyadic_InPat`, `patGrid'_dense`, `continuum_in_constructible_closure` (two basepoints + midpoint reduction, zero-Nat definition layer) |
| mapping judgments | `MappingJudgmentTheorems.lean` | `context_convergence_resolvable`, `equivalence_bridge_judgment`, `conflict_declared_resolvable`, `round_trip_precise_injective`, `polar_judgment_separated` |

The main theorem chain: interlock nonsingularity → four-phase
interlock → countable grid + density → continuum = closure of the pat
grid → endogenous (paired-basepoint, midpoint-reduction) closure.

## Provenance

- Original full package: `src/repo_v5/lab/paper_repro/selfcontained_zh/`
  (Chinese self-contained package; training runtime snapshot, all
  experiment scripts and results, full Lean Toolkit with claims ledger,
  2026-08-16, 3631-job lake build).
- Claim ledger entries: `formal/claims/R*.yaml` (R136 paired
  declaration, R138 phase locking, R143 interlock, R149 four-phase,
  R150 Wang phase-unification, R151 continuum closure, R163 endogenous
  symmetry-reduction closure) and `formal/claims/R031_Completeness.md`
  (the decoupling-operator completeness criterion).
- The formalization was checked with `lake build` against mathlib
  v4.32.2 (0 sorry). Axioms are the standard Lean/mathlib set
  (`propext`, `Classical.choice`, `Quot.sound`); reviewers may rerun
  `#print axioms <theorem>` to verify.

## Honest boundary

- The empirical → framework mapping is an observational correspondence,
  not a deductive implication (no theorem states training behavior
  implies a framework claim).
- Novelty annotations: classical components (density, closure,
  nonsingularity) are KNOWN; claims carry `novelty_status` in the
  ledger (KNOWN / NOVELTY_UNASSESSED).
- Training results are observations with a reproducible pipeline, not
  machine-checked statements.

## Double-blind

No author / affiliation / email / DOI / repository identifiers appear
in this artifact.
