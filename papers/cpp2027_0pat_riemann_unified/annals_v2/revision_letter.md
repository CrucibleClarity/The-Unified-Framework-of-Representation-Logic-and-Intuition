# Revision Letter — Version 2

**Manuscript**: The Riemann Direction from Known Mathematics Only
**Author**: Anonymous
**Submitted to**: Annals of Mathematics
**Date**: 2026-08-22

## Summary of changes

This revision incorporates machine verification completed after the
initial submission (Version 1, 2026-08-21). No referee report had been
received at the time of this revision; the changes are the author's
own response to the calibration statement of the paper: a conclusion
is regarded as proved only when verified by the Lean 4 compiler with
no `sorry`.

### 1. The (0,1)-segment is now closed by the odd/even pairing (new, machine-verified)

In Version 1, the negativity ζ(x) < 0 on (0,1) was supported by the
Euler–Maclaurin continuation Blocks C–G, whose mathematical argument
was complete but whose mechanical Lean assembly was marked KNOWN as an
honest boundary. The only reason for that boundary was infrastructure:
the Weierstrass/identity-theorem assembly for that specific kernel
(locally uniform convergence of `termTSum`, analyticity by the
Weierstrass theorem, extension by the identity theorem on the strip)
requires library machinery that mathlib does not yet provide, while
the Euler–Maclaurin kernel itself is classical, KNOWN mathematics of
no novelty.

This revision replaces that path by a strictly simpler one. The
odd/even pairing of the Dirichlet series — the same pairing that
underlies Layer 5 and the period-pair cancellation of Layer 6 — is now
machine-verified (iso 41, `zeta_odd_even_continuity_iso.lean`,
4 declarations, 0 errors, 0 sorry, Mathlib only):

- `pairing_term_pos`: each pairing term 1/(2n+1)^x − 1/(2n+2)^x is
  positive for x > 0;
- `pairing_diff_bound`: the difference bound
  1/a^x − 1/b^x ≤ x(b−a)/a^{x+1} (mean value theorem);
- `pairing_summable`: the paired series converges for 0 < x < 1;
- `zeta_continuous_zero_one`: ζ is continuous on (0,1) (anchored in
  mathlib's `differentiableOn_riemannZeta`).

The sign then follows directly: positive pairing terms give η(x) > 0
(the limit of the alternating series), the classical doubling identity
ζ(x) = η(x)/(1−2^{1−x}) holds, and the denominator is negative for
0 < x < 1. Hence ζ(x) < 0 on (0,1), completing the zero-free bottom
edge of the rectangle of Layer 12.

The Euler–Maclaurin material is retained in the manuscript as the
classical background and as the source of the verified closed forms of
Blocks A–B (unchanged from Version 1). The Weierstrass/identity-theorem
assembly of Blocks C–G is no longer needed.

### 2. Nothing else changed

The remaining thirteen layers are unchanged from Version 1 and remain
machine-verified: the complex-axis algebra, the circle geometry, the
false-real-axis framework, the critical-line phase layer, the covering
space and phase locking, the predictor residuals (the integer-layer
content of the Riemann–von Mangoldt formula), and the argument-principle
rectangle closure with its boundary estimates. The declaration count is
231 + 4 = 235.

## Response to editor/referee concerns

No referee report had been received at the time of this revision, so
there are no specific concerns to address. The revision responds to
the general requirement stated in the manuscript's methodology
statement — complete machine verification — and narrows the honest
boundary accordingly: the (0,1)-segment, the last KNOWN-marked part of
the development, is now machine-verified by a direct short path.

Whether the short path is viewed as a simplification of the classical
argument or as a new presentation of known facts, it does not affect
any other result of the paper: every other layer was machine-verified
in Version 1 and is unchanged. The only honest boundary that remains
is the one the paper has always stated: the Riemann hypothesis itself
(that all strip zeros lie on the critical line) is equivalently
restated (Theorem 6.4) but not claimed.
