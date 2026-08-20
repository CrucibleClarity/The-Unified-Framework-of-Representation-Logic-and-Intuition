# Q2_0 Grid ↔ Four-Phase Encoding

The GGUF Q2_0 quantization format (2 bits per element, dequantization
`(code − 1) · d` with per-block scale `d`) uses the grid `{-1, 0, 1, 2}`.
Claim C037 formalizes this grid as a **symbol encoding** of the four phases
`{1, -1, i, -i}` of the complex plane.

## The sign encoding φ (C037)

| phase | φ | code | meaning |
|---|---|---|---|
| 1    | +1 | 2 | real positive → multiplicative basepoint |
| −1   | −1 | 0 | real negative → reflection basepoint |
| i    | +2 | 3 | imaginary positive → basepoint iteration (1+1 = 2·1) |
| −i   | 0  | 1 | imaginary negative → fold center (folds into the origin) |

2 bits = 2 sign axes (real sign × imaginary sign):

| | iteration axis: base {−1, +1} | iteration axis: iterated {0, +2} |
|---|---|---|
| direction axis: negative {−1, 0} | −1 (code 0) | 0 (code 1) |
| direction axis: positive {+1, +2} | +1 (code 2) | +2 (code 3) |

## pat three-grid vs Q2_0 four-grid

- pat numeric grid `{-1, 0, 1}` = the four phases projected onto the real axis
  (C029): Re(±i) = 0, imaginary sign dropped → 3 values.
- Q2_0 grid `{-1, 0, 1, 2}` = the four phases quantized by **both** sign axes
  (imaginary sign preserved) → 4 values.

## Structure properties (verified in Lean, no sorry)

- Four-phase sum = 0: 1 + i + (−1) + (−i) = 0 (projection cancellation, C030).
- J² = −I: i·i = −1 (symplectic, C030).
- The grid is **not multiplicatively closed**: 2·2 = 4 ∉ {-1,0,1,2}
  ⟹ φ is a symbol encoding, **not** a homomorphism.

## In the wild (Bonsai-27B Q2_0)

The Bonsai-27B weights use the Q2_0 grid with per-block scales; the dequantized
values fall on the basepoint cluster {−1, 0, 1, 2} (C028 reading: each weight is
quantized to the nearest basepoint or basepoint iteration).
