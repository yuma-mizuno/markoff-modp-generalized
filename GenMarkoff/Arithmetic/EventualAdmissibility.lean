import GenMarkoff.Divisibility.GenericMartin
import Mathlib.Data.ZMod.Basic

/-!
# Eventual admissibility of integral coefficients

For a fixed integrally nondegenerate integral coefficient triple, the generic
hypotheses in the generalized Martin divisibility theorem fail modulo only
finitely many primes.  This file makes that explicit: the cutoff
`genericAdmissibilityCutoff a` is one more than the largest absolute value of
the multiplier and the three integers `aᵢ ^ 2 - 4`, and is also at least `5`
so that it can be fed directly into `generalizedMartinGenericDivisibility`.
The main result is
`IntegrallyNondegenerate.genericAdmissibleAt_of_cutoff_le`.
-/

namespace GenMarkoff

/-- The largest absolute value of an integer whose vanishing modulo `p` would
violate generic admissibility. -/
def integralBadReductionHeight (a : Coefficients ℤ) : ℕ :=
  max a.multiplier.natAbs
    (max (a.a1 ^ 2 - 4).natAbs
      (max (a.a2 ^ 2 - 4).natAbs (a.a3 ^ 2 - 4).natAbs))

/-- An explicit cutoff after which an integrally nondegenerate coefficient
triple has generic reduction.  The `5` also matches the lower bound in
`GeneralizedMartinGenericDivisibilityStatement`. -/
def genericAdmissibilityCutoff (a : Coefficients ℤ) : ℕ :=
  max 5 (integralBadReductionHeight a + 1)

private theorem intCast_ne_zero_of_natAbs_lt
    {n : ℤ} {p : ℕ} (hn : n ≠ 0) (hbound : n.natAbs < p) :
    (n : ZMod p) ≠ 0 := by
  intro hzero
  have hdvd : (p : ℤ) ∣ n :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp hzero
  have hle : p ≤ n.natAbs := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hdvd hn
  exact (Nat.not_le_of_gt hbound) hle

private theorem multiplier_natAbs_lt_of_cutoff_le
    (a : Coefficients ℤ) {p : ℕ} (hcut : genericAdmissibilityCutoff a ≤ p) :
    a.multiplier.natAbs < p := by
  have hheight : a.multiplier.natAbs ≤ integralBadReductionHeight a := by
    exact le_max_left _ _
  have hsucc : a.multiplier.natAbs < integralBadReductionHeight a + 1 :=
    Nat.lt_succ_of_le hheight
  exact lt_of_lt_of_le hsucc (le_trans (le_max_right _ _) hcut)

private theorem a1Discriminant_natAbs_lt_of_cutoff_le
    (a : Coefficients ℤ) {p : ℕ} (hcut : genericAdmissibilityCutoff a ≤ p) :
    (a.a1 ^ 2 - 4).natAbs < p := by
  have hheight : (a.a1 ^ 2 - 4).natAbs ≤ integralBadReductionHeight a := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hsucc : (a.a1 ^ 2 - 4).natAbs < integralBadReductionHeight a + 1 :=
    Nat.lt_succ_of_le hheight
  exact lt_of_lt_of_le hsucc (le_trans (le_max_right _ _) hcut)

private theorem a2Discriminant_natAbs_lt_of_cutoff_le
    (a : Coefficients ℤ) {p : ℕ} (hcut : genericAdmissibilityCutoff a ≤ p) :
    (a.a2 ^ 2 - 4).natAbs < p := by
  have hheight : (a.a2 ^ 2 - 4).natAbs ≤ integralBadReductionHeight a := by
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hsucc : (a.a2 ^ 2 - 4).natAbs < integralBadReductionHeight a + 1 :=
    Nat.lt_succ_of_le hheight
  exact lt_of_lt_of_le hsucc (le_trans (le_max_right _ _) hcut)

private theorem a3Discriminant_natAbs_lt_of_cutoff_le
    (a : Coefficients ℤ) {p : ℕ} (hcut : genericAdmissibilityCutoff a ≤ p) :
    (a.a3 ^ 2 - 4).natAbs < p := by
  have hheight : (a.a3 ^ 2 - 4).natAbs ≤ integralBadReductionHeight a := by
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hsucc : (a.a3 ^ 2 - 4).natAbs < integralBadReductionHeight a + 1 :=
    Nat.lt_succ_of_le hheight
  exact lt_of_lt_of_le hsucc (le_trans (le_max_right _ _) hcut)

/-- Above the explicit cutoff, an integrally nondegenerate integral
coefficient triple has generic reduction modulo `p`.  Primality is not needed
for this finite-bad-reduction step. -/
theorem IntegrallyNondegenerate.genericAdmissibleAt_of_cutoff_le
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    {p : ℕ} (hcut : genericAdmissibilityCutoff a ≤ p) :
    GenericAdmissibleAt a p := by
  rcases ha with ⟨hmul, ha1, ha2, ha3⟩
  have hmulCast : (a.multiplier : ZMod p) ≠ 0 :=
    intCast_ne_zero_of_natAbs_lt hmul
      (multiplier_natAbs_lt_of_cutoff_le a hcut)
  have ha1Cast : ((a.a1 ^ 2 - 4 : ℤ) : ZMod p) ≠ 0 :=
    intCast_ne_zero_of_natAbs_lt (sub_ne_zero.mpr ha1)
      (a1Discriminant_natAbs_lt_of_cutoff_le a hcut)
  have ha2Cast : ((a.a2 ^ 2 - 4 : ℤ) : ZMod p) ≠ 0 :=
    intCast_ne_zero_of_natAbs_lt (sub_ne_zero.mpr ha2)
      (a2Discriminant_natAbs_lt_of_cutoff_le a hcut)
  have ha3Cast : ((a.a3 ^ 2 - 4 : ℤ) : ZMod p) ≠ 0 :=
    intCast_ne_zero_of_natAbs_lt (sub_ne_zero.mpr ha3)
      (a3Discriminant_natAbs_lt_of_cutoff_le a hcut)
  unfold GenericAdmissibleAt GenericAdmissible
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [modCoefficients, Coefficients.intCast, Coefficients.multiplier] using hmulCast
  · intro h
    apply ha1Cast
    have h' : (a.a1 : ZMod p) ^ 2 = 4 := by
      simpa [modCoefficients, Coefficients.intCast] using h
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat, sub_eq_zero] using h'
  · intro h
    apply ha2Cast
    have h' : (a.a2 : ZMod p) ^ 2 = 4 := by
      simpa [modCoefficients, Coefficients.intCast] using h
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat, sub_eq_zero] using h'
  · intro h
    apply ha3Cast
    have h' : (a.a3 : ZMod p) ^ 2 = 4 := by
      simpa [modCoefficients, Coefficients.intCast] using h
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat, sub_eq_zero] using h'

end GenMarkoff
