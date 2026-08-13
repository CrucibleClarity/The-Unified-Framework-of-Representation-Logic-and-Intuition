/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Formal.ZeroRelative.BasepointGen
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.NumberTheory.Real.Irrational

/-!
# Prime positions observed through the basepoint-drift frame

Motivation (docs/关于黎曼猜想的思考.md): in the drift frame, the successor of
the drifted basepoint is the drift vector as seen from our frame; when the
drifted basepoint iterates along its drift direction, primes land on the
integer positions of the translation axis. Each OBSERVATION below is an
instance of known facts on the group model ℤ (resp. ℚ, ℝ) — novelty: KNOWN.

Position 1 — the drift vector is the successor of the new basepoint
  (relative-coordinate observation, instance of PureGen.relcoord_equiv).
Position 2 — the n-th successor position in the drift frame is e + (n+1)·d.
Position 3 — on the drift axis of a prime p, the only prime position is the
  basepoint step itself: n·p prime ⟺ n = 1.
Position 4 — the inversion-dual position: 1/(1/a + 1/b) = ab/(a+b).
Position 5 — the symmetric position of a prime p is p/2, never an integer
  (the duality "1 ↔ 1/a+1/b" misses the integers for odd primes).
Position 6 — an irrational drift axis has no nonzero integer positions
  ("going back": irrationals never land on integer positions by forward
  iteration along the drift axis).
-/

namespace ZeroRelative

/-! ## Position 1 — drift vector = successor of the new basepoint

In the group model ℤ with [x,y,z] = x - y + z, the basepoint e drifts by d to
the new basepoint f = e + d. The relative-coordinate observation
O_{e+d}(x) := x - (e + d) of the transported point T_{e→e+d}(e + d) is the
drift vector d: the successor of the new basepoint (in its own frame) is
exactly the drift vector as seen from our frame. -/
theorem drift_vector_is_successor (e d : ℤ) :
    PureGen.transport e (e + d) (e + d) - (e + d) = d := by
  unfold PureGen.transport
  change ((e + d) - e + (e + d)) - (e + d) = d
  ring

/-! ## Position 2 — successor positions in the drift frame

Iterating the drift (the basepoint keeps moving along the drift direction d),
the n-th successor position of the new basepoint f = e + d is
e + (n + 1)·d: each step advances by the drift vector d, so the frame's
successor ladder {e + n·d} is exactly the translation axis of the drift. -/
theorem successor_positions_in_drift_frame (e d n : ℤ) :
    PureGen.transport e (e + d) (e + n * d) = e + (n + 1) * d := by
  unfold PureGen.transport
  change (e + n * d) - e + (e + d) = e + (n + 1) * d
  ring

/-! ## Position 3 — prime positions on the drift axis

With basepoint 0 drifting along the direction of a prime p, the integer
positions of the translation axis are {n·p}. A prime lands on these positions
exactly once — at the basepoint step n = 1. All other positions are composite.
(OBSERVATION: this is the integer factorization of n·p; KNOWN.) -/
theorem prime_positions_on_drift_axis (p n : ℕ) (hp : Nat.Prime p) :
    Nat.Prime (n * p) ↔ n = 1 := by
  constructor
  · intro hprime
    have hp_dvd : p ∣ n * p := ⟨n, by rw [Nat.mul_comm]⟩
    have hpm : p = n * p := by
      rcases hprime.eq_one_or_self_of_dvd p hp_dvd with h1 | h
      · exact False.elim (Nat.Prime.ne_one hp h1)
      · exact h
    have hp0 : 0 < p := lt_of_lt_of_le (by decide : 0 < 2) (Nat.Prime.two_le hp)
    have : p * n = p * 1 := by
      calc
        p * n = n * p := Nat.mul_comm p n
        _ = p := hpm.symm
        _ = p * 1 := by rw [Nat.mul_one]
    exact Nat.mul_left_cancel hp0 this
  · intro hn
    simpa [hn]

/-! ## Position 4 — the inversion-dual position

The pair "1 ↔ 1/a + 1/b" (translation vs inversion duality of the thinking
note) is witnessed by the dual position 1/(1/a + 1/b) = ab/(a+b). (KNOWN:
harmonic-mean duality; here over ℚ.) -/
theorem inversion_dual_position (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hsum : a + b ≠ 0) :
    1 / (1 / a + 1 / b) = a * b / (a + b) := by
  field_simp [ha, hb, hsum]
  rw [add_comm b a]
  field_simp [hsum]

/-! ## Position 5 — the symmetric position of a prime misses the integers

The symmetric (dual) position of p under the inversion duality is p/2
(instance of Position 4 with a = b = p). For any odd prime p this is never an
integer: the "symmetric position" is a half-integer, i.e. the duality lands
outside the integer axis. (OBSERVATION; KNOWN.) -/
theorem prime_inversion_misses_integers (p : ℕ) (hp : Nat.Prime p)
    (hp2 : p ≠ 2) :
    ∀ n : ℕ, (p : ℚ) / 2 ≠ (n : ℚ) := by
  intro n hn
  have hq : (p : ℚ) = (2 : ℚ) * (n : ℚ) := by
    field_simp at hn
    exact hn
  have hz : p = 2 * n := by
    exact_mod_cast hq
  have htwo : 2 ∣ p := ⟨n, hz⟩
  have hp_eq : p = 2 := (Nat.Prime.dvd_iff_eq (p := p) (a := 2) hp (by decide : 2 ≠ 1)).1 htwo
  exact hp2 hp_eq

/-! ## Position 6 — an irrational drift axis has no integer positions

If the drift vector d is irrational, the translation axis {n·d} contains no
nonzero integer position: forward iteration along an irrational drift never
lands on an integer of our number axis. This formalizes "the irrational needs
to go back" — the integer axis is reachable from the irrational drift axis
only by leaving the drift direction. (OBSERVATION; KNOWN.) -/
theorem irrational_drift_axis_no_int_points (d : ℝ) (hd : Irrational d) :
    ∀ n m : ℤ, (n : ℝ) * d = (m : ℝ) → n = 0 := by
  intro n m h
  by_contra hn0
  have hd' : d = (m : ℝ) / (n : ℝ) := by
    field_simp [hn0]
    simpa [mul_comm] using h
  have hq : (((m : ℚ) / (n : ℚ)) : ℝ) = d := by
    calc
      (((m : ℚ) / (n : ℚ)) : ℝ) = (m : ℝ) / (n : ℝ) := by
        simp
      _ = d := hd'.symm
  exact hd ⟨(m : ℚ) / (n : ℚ), by
    rw [Rat.cast_div]
    exact hq⟩

end ZeroRelative
