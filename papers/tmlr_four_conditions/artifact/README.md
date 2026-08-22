# Artifact — Four Theorems from Experiments

## Build

```bash
# Lean 4.32.2 + mathlib v4.32.2
cd formal
lake build        # MappingJudgmentTheorems, 0 errors, 0 sorry
```

## Theorems (5, all 0 sorry)

| Theorem | Statement (informal) |
|---|---|
| `context_convergence_resolvable` | Context convergence implies the existence of a resolution verdict for the symbol mapping (symbol-norm judgment) |
| `equivalence_bridge_judgment` | An equivalence declaration yields a bridge verdict (presentation-legality, direction A) |
| `conflict_declared_resolvable` | A declared conflict yields an injective resolvability verdict (presentation-legality, direction B) |
| `round_trip_precise_injective` | A lossless round trip (B∘A = id) implies the assembly map is injective (symbols→presentation completing judgment) |
| `polar_judgment_separated` | The two-pole judgment separates: in-representation truth and cross-representation falsity judged by the same verdict structure (intuition-precision) |

## Evidence

- `evidence/report.md` — E12 succ-matrix results report (45 runs, two poles)
- `evidence/run_all_out.txt`, `succ_matrix_repro_20260816.out.txt` — E12 outputs
- `evidence/E14/E15/E16/E17_*.out.txt` — supporting experiment outputs
- `evidence/model_viewpoint_phase_record.md` — the phase-classification record
  (4,068 messages; 1,795 negative/leaning-negative vs 114 affirmative/leaning-
  affirmative among stance-taking) that produced the intuition-precision judgment

## Provenance

- Claims: `claims/R031_Completeness.md` (the completeness judgment: decoupling
  operator D = exclusion + cancellation + layering), `claims/R136.yaml`
  (paired direction declaration), `claims/R143.yaml` (symmetric-pair reduction /
  interlock). Full ledger in the series' self-contained package.
- The four judgments were extracted from the program's process: token-system
  debugging (symbol-norm), two-pole training observations (presentation-legality),
  model-viewpoint rejection records (intuition-precision), completeness
  verification project (completeness).

## Double-blind

No author / affiliation / email / DOI / repository identifiers appear in this
artifact (identity terms anonymized; "DeepSeek" appears only inside quoted
conversation records as the name of a third-party company, not as authorship).
