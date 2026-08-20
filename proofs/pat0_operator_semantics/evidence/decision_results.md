# Decision Preservation — Assembly SSM Replacement vs Float Reference

Measured 2026-08-20 on Bonsai-27B Q2_0 real weights (all layers, shared weight cache).

## Setup

- A = float full reference (all layers float)
- B = SSM layers replaced by the assembly pat0 chain (all other layers float)
- Prompt: 11 tokens prefix (state build) + 6 generated tokens
- Locked domain: top1 − top2 probability gap > 0.7 (deterministic extrapolation domain)

## Results

| Token | argmax identical | locked identical |
|---|---|---|
| 1 | **True** (A=11 B=11) | True (both unlocked) |
| 2 | **True** (A=11 B=11) | True |
| 3 | False (A=16 B=82) | True |
| 4 | False (A=198 B=13) | True |
| 5 | False (A=16 B=8) | True |
| 6 | False (A=13 B=663) | True |
| **Total** | **2/6** | **6/6** |

## Speed

- A (float): 125.7 s for 17 tokens (10.65 s/tok incl. prefix)
- B (assembly SSM): 23.9 s (1.41 s/tok incl. prefix)
- **Speedup: 5.3×** end-to-end (SSM layers are the replaced part; attention/FFN remain float)

## Interpretation

- The locked domain (the deterministic one-step extrapolation regime, R152) is
  **preserved 6/6**: the assembly chain never flips a locked decision.
- The argmax disagreement on tokens 3–6 is the basepoint-relative semantics
  (C007): relative displacement is invariant under basepoint change, while
  absolute logits drift. The same disagreement pattern holds for the numpy pat0
  reference (control), i.e., it is not an implementation artifact: the assembly
  chain is bit-exact against the pat0 reference (see alignment_results.md).
