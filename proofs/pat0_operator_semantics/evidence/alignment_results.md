# Alignment Results — Assembly Kernel Chain vs Float Reference

Measured 2026-08-20 on Bonsai-27B Q2_0 real weights (layer 0, single token 50256).

## Setup

Assembly kernel chain (patc/patlib.S, AVX-512):
```
pat_kw_lock  → pat_lock_win → pat_conv_v2 → pat_l2_lock ×2 → pat_interlock_v2 ×48 head
(per-block weight locking, window sliding+pre-lock, integer-MAC conv, L2 compactification, interlock)
```
Reference: numpy pat0 implementation (engine `_ssm_step_pat0`), float64 state path.

## Results

| Segment | Difference |
|---|---|
| window codes (winq, 40960 int8) | **0** |
| window scale (sw, 80 float) | 3.7e-9 |
| conv codes (conv_code, 10240 int8) | **0** |
| conv scale (sconv) | 3.5e-10 |
| L2-compactified q codes (qq, 2048 int8) | **0** |
| L2-compactified k codes (kq, 2048 int8) | **0** |
| interlock output (oq, 6144 float) | rel ≈ 1e-4 |
| **layer output (5120 float)** | **rel = 0.0000, corr = +1.0000** |
| layer output argmax | **identical (3206 = 3206)** |

## Speed

- Assembly chain: 683 µs per layer-step
- numpy reference: 8751 µs per layer-step
- Speedup: **12.8×** (single layer, 48-head interlock included)

## Notes

- Bit-exactness of the input chain follows from integer MAC + exact scale chains:
  every value is a code × scale product with no precision loss (C037/C038 semantics).
- The remaining interlock difference (≈1e-4) is the float32 (assembly) vs float64
  (reference) state-accumulation precision difference; float32 is the precision of
  real inference.
