import GenMarkoff.General.FiberDynamics
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Signed heterogeneous parabolic fibers

At trace `t = 2` and `t = -2`, the ordered affine center does not exist.
Moreover, the two signs see different combinations of the adjacent
coefficients.  This file records the division-free fixed-locus calculation
that any subsequent parabolic orbit count must respect.
-/

namespace GenMarkoff.General

universe u

section Ring

variable {R : Type u} [CommRing R]

/-- Explicit positive-parabolic heterogeneous rotation. -/
theorem affineRotation_two_apply (B C u : R) (v : R × R) :
    affineRotation B C u 2 v =
      (2 * v.2 - v.1 - C * u,
        3 * v.2 - 2 * v.1 - (2 * C + B) * u) := by
  rw [affineRotation_apply]
  apply Prod.ext
  · simp only
  · simp only
    ring

/-- Explicit negative-parabolic heterogeneous rotation. -/
theorem affineRotation_neg_two_apply (B C u : R) (v : R × R) :
    affineRotation B C u (-2) v =
      (-2 * v.2 - v.1 - C * u,
        3 * v.2 + 2 * v.1 + (2 * C - B) * u) := by
  rw [affineRotation_apply]
  apply Prod.ext
  · simp only
  · simp only
    ring

/-- At trace `2`, a fixed point can exist only on the signed coefficient
locus `(B + C) * u = 0`.  The other equation describes the fixed affine
line. -/
theorem affineRotation_two_eq_self_iff (B C u : R) (v : R × R) :
    affineRotation B C u 2 v = v ↔
      2 * (v.2 - v.1) = C * u ∧ (B + C) * u = 0 := by
  rw [affineRotation_two_apply]
  constructor
  · intro h
    have hfirst := congrArg Prod.fst h
    have hsecond := congrArg Prod.snd h
    simp only at hfirst hsecond
    have hfirst' : 2 * v.2 - 2 * v.1 - C * u = 0 := by
      linear_combination hfirst
    have hsecond' :
        2 * v.2 - 2 * v.1 - (2 * C + B) * u = 0 := by
      linear_combination hsecond
    constructor
    · linear_combination hfirst
    · linear_combination hfirst' - hsecond'
  · rintro ⟨hline, hsigned⟩
    apply Prod.ext
    · simp only
      linear_combination hline
    · simp only
      linear_combination hline - hsigned

/-- At trace `-2`, the coefficient condition changes from a sum to a
difference.  This is the sign condition missing from the printed uniform
parabolic count. -/
theorem affineRotation_neg_two_eq_self_iff (B C u : R) (v : R × R) :
    affineRotation B C u (-2) v = v ↔
      2 * (v.1 + v.2) = -C * u ∧ (B - C) * u = 0 := by
  rw [affineRotation_neg_two_apply]
  constructor
  · intro h
    have hfirst := congrArg Prod.fst h
    have hsecond := congrArg Prod.snd h
    simp only at hfirst hsecond
    have hfirst' : 2 * (v.1 + v.2) + C * u = 0 := by
      linear_combination -hfirst
    have hsecond' :
        2 * (v.1 + v.2) + (2 * C - B) * u = 0 := by
      linear_combination hsecond
    constructor
    · linear_combination -hfirst
    · linear_combination hfirst' - hsecond'
  · rintro ⟨hline, hsigned⟩
    apply Prod.ext
    · simp only
      linear_combination -hline
    · simp only
      linear_combination hline - hsigned

theorem affineRotation_two_ne_self_of_signed_ne_zero
    (B C u : R) (v : R × R) (h : (B + C) * u ≠ 0) :
    affineRotation B C u 2 v ≠ v := by
  intro hfixed
  exact h ((affineRotation_two_eq_self_iff B C u v).mp hfixed).2

theorem affineRotation_neg_two_ne_self_of_signed_ne_zero
    (B C u : R) (v : R × R) (h : (B - C) * u ≠ 0) :
    affineRotation B C u (-2) v ≠ v := by
  intro hfixed
  exact h ((affineRotation_neg_two_eq_self_iff B C u v).mp hfixed).2

/-- Closed positive-parabolic iterate formula.  The quadratic term is the
accumulated heterogeneous translation in the unipotent direction. -/
theorem iterate_affineRotation_two (B C u : R) (v : R × R) (n : ℕ) :
    ((affineRotation B C u 2)^[n]) v =
      (v.1 + (n : R) * (2 * (v.2 - v.1) - C * u) -
          2 * (n.choose 2 : R) * (B + C) * u,
        v.2 + (n : R) *
            (2 * (v.2 - v.1) - (2 * C + B) * u) -
          2 * (n.choose 2 : R) * (B + C) * u) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, affineRotation_two_apply]
      simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add,
        Nat.cast_succ]
      apply Prod.ext <;> simp only <;> ring

/-- Closed negative-parabolic iterate formula.  Its unipotent and translation
directions have opposite signs in the two moving coordinates. -/
theorem iterate_affineRotation_neg_two (B C u : R) (v : R × R) (n : ℕ) :
    ((affineRotation B C u (-2))^[n]) v =
      (v.1 + (n : R) * (-2 * (v.1 + v.2) - C * u) +
          2 * (n.choose 2 : R) * (B - C) * u,
        v.2 + (n : R) *
            (2 * (v.1 + v.2) + (2 * C - B) * u) -
          2 * (n.choose 2 : R) * (B - C) * u) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, affineRotation_neg_two_apply]
      simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add,
        Nat.cast_succ]
      apply Prod.ext <;> simp only <;> ring

end Ring

section PrimeCharacteristic

variable {R : Type u} [CommRing R]

/-- In odd prime characteristic, every positive-parabolic affine orbit has
period dividing `p`. -/
theorem iterate_affineRotation_two_prime
    (p : ℕ) [CharP R p] (hp : p.Prime) (hpTwo : p ≠ 2)
    (B C u : R) (v : R × R) :
    ((affineRotation B C u 2)^[p]) v = v := by
  have hTwoLt : 2 < p := by
    have := hp.two_le
    omega
  have hchooseDvd : p ∣ p.choose 2 :=
    hp.dvd_choose_self (by norm_num) hTwoLt
  have hchooseCast : (p.choose 2 : R) = 0 :=
    (CharP.cast_eq_zero_iff R p (p.choose 2)).2 hchooseDvd
  rw [iterate_affineRotation_two]
  simp [hchooseCast]

/-- In odd prime characteristic, every negative-parabolic affine orbit also
has period dividing `p`. -/
theorem iterate_affineRotation_neg_two_prime
    (p : ℕ) [CharP R p] (hp : p.Prime) (hpTwo : p ≠ 2)
    (B C u : R) (v : R × R) :
    ((affineRotation B C u (-2))^[p]) v = v := by
  have hTwoLt : 2 < p := by
    have := hp.two_le
    omega
  have hchooseDvd : p ∣ p.choose 2 :=
    hp.dvd_choose_self (by norm_num) hTwoLt
  have hchooseCast : (p.choose 2 : R) = 0 :=
    (CharP.cast_eq_zero_iff R p (p.choose 2)).2 hchooseDvd
  rw [iterate_affineRotation_neg_two]
  simp [hchooseCast]

/-- Away from the positive signed fixed locus, the parabolic affine cycle has
exact period `p`. -/
theorem minimalPeriod_affineRotation_two_eq_prime
    (p : ℕ) [Fact p.Prime] [CharP R p] (hpTwo : p ≠ 2)
    (B C u : R) (v : R × R) (hSigned : (B + C) * u ≠ 0) :
    Function.minimalPeriod (affineRotation B C u 2) v = p := by
  apply Function.minimalPeriod_eq_prime
  · exact iterate_affineRotation_two_prime
      p Fact.out hpTwo B C u v
  · exact affineRotation_two_ne_self_of_signed_ne_zero
      B C u v hSigned

/-- Away from the negative signed fixed locus, the negative-parabolic affine
cycle likewise has exact period `p`. -/
theorem minimalPeriod_affineRotation_neg_two_eq_prime
    (p : ℕ) [Fact p.Prime] [CharP R p] (hpTwo : p ≠ 2)
    (B C u : R) (v : R × R) (hSigned : (B - C) * u ≠ 0) :
    Function.minimalPeriod (affineRotation B C u (-2)) v = p := by
  apply Function.minimalPeriod_eq_prime
  · exact iterate_affineRotation_neg_two_prime
      p Fact.out hpTwo B C u v
  · exact affineRotation_neg_two_ne_self_of_signed_ne_zero
      B C u v hSigned

end PrimeCharacteristic

end GenMarkoff.General
