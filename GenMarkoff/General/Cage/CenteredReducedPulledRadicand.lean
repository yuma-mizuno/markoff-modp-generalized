import GenMarkoff.General.Cage.ConnectingPulledRadicands
import GenMarkoff.General.Cage.ConnectingQuartic

/-!
# Removing the forced squares from the centered connecting radicand

The power pullback of the centered-norm cover acquires a forced square
factor at a parabolic split trace precisely when the moving coefficient
pair satisfies `B = C` or `B = -C`.  This file removes that factor and
records that the resulting polynomial has the same square class in the
rational function field.

The remaining polynomial is squarefree under the usual nonparabolic
coefficient hypotheses and the tame power-pullback hypothesis.
-/

namespace GenMarkoff.General.Cage

open Polynomial

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- The degree-`2d` pullback of the monic quadratic
`Y² + A Y + 1`. -/
def monicQuadraticPowerPulledRadicand
    (A : K) (d : ℕ) : K[X] :=
  X ^ (2 * d) + C A * X ^ d + 1

@[simp]
theorem eval_monicQuadraticPowerPulledRadicand
    (A t : K) (d : ℕ) :
    eval t (monicQuadraticPowerPulledRadicand A d) =
      (t ^ d) ^ 2 + A * t ^ d + 1 := by
  simp only [monicQuadraticPowerPulledRadicand, eval_add, eval_pow,
    eval_X, eval_mul, eval_C, eval_one, ← pow_mul]
  simp only [Nat.mul_comm]

/-- The square factor forced by a collision with a parabolic split trace. -/
def centeredNormForcedFactor (B C0 : K) (d : ℕ) : K[X] :=
  by
    classical
    exact
      if B = C0 then
        X ^ d + 1
      else if B = -C0 then
        X ^ d - 1
      else
        1

/-- The centered-norm pullback after deleting its forced parabolic square.

When both equalities can hold (in characteristic two), the first branch is
used; the two displayed factors and reduced polynomials then coincide. -/
def centeredNormReducedPulledRadicand
    (B C0 : K) (d : ℕ) : K[X] :=
  by
    classical
    exact
      if B = C0 then
        monicQuadraticPowerPulledRadicand (B ^ 2 - 2) d
      else if B = -C0 then
        monicQuadraticPowerPulledRadicand (2 - B ^ 2) d
      else
        centeredNormPulledRadicand B C0 d

/-- At `B = C`, the positive-parabolic factor `X^d + 1` occurs twice. -/
theorem centeredNormPulledRadicand_eq_of_eq
    (B : K) (d : ℕ) :
    centeredNormPulledRadicand B B d =
      (X ^ d + 1) ^ 2 *
        monicQuadraticPowerPulledRadicand (B ^ 2 - 2) d := by
  simp only [centeredNormPulledRadicand,
    monicQuadraticPowerPulledRadicand]
  rw [show X ^ (4 * d) = (X ^ d) ^ 4 by
      rw [show 4 * d = d * 4 by omega, pow_mul]]
  rw [show X ^ (3 * d) = (X ^ d) ^ 3 by
      rw [show 3 * d = d * 3 by omega, pow_mul]]
  rw [show X ^ (2 * d) = (X ^ d) ^ 2 by
      rw [show 2 * d = d * 2 by omega, pow_mul]]
  simp only [map_add, map_mul, map_pow, map_sub, map_ofNat]
  ring

/-- At `B = -C`, the negative-parabolic factor `X^d - 1` occurs twice. -/
theorem centeredNormPulledRadicand_eq_of_eq_neg
    (B : K) (d : ℕ) :
    centeredNormPulledRadicand B (-B) d =
      (X ^ d - 1) ^ 2 *
        monicQuadraticPowerPulledRadicand (2 - B ^ 2) d := by
  simp only [centeredNormPulledRadicand,
    monicQuadraticPowerPulledRadicand]
  rw [show X ^ (4 * d) = (X ^ d) ^ 4 by
      rw [show 4 * d = d * 4 by omega, pow_mul]]
  rw [show X ^ (3 * d) = (X ^ d) ^ 3 by
      rw [show 3 * d = d * 3 by omega, pow_mul]]
  rw [show X ^ (2 * d) = (X ^ d) ^ 2 by
      rw [show 2 * d = d * 2 by omega, pow_mul]]
  simp only [map_add, map_mul, map_pow, map_sub, map_neg, map_ofNat]
  ring

/-- The unreduced centered pullback is the square of the forced factor
times the reduced pullback. -/
theorem centeredNormPulledRadicand_eq_forcedFactor_sq_mul_reduced
    (B C0 : K) (d : ℕ) :
    centeredNormPulledRadicand B C0 d =
      centeredNormForcedFactor B C0 d ^ 2 *
        centeredNormReducedPulledRadicand B C0 d := by
  classical
  by_cases hEq : B = C0
  · subst C0
    simp only [centeredNormForcedFactor,
      centeredNormReducedPulledRadicand, if_pos]
    exact centeredNormPulledRadicand_eq_of_eq B d
  · by_cases hNeg : B = -C0
    · simp only [centeredNormForcedFactor,
        centeredNormReducedPulledRadicand, if_neg hEq, if_pos hNeg]
      rw [hNeg]
      simpa only [neg_sq, neg_neg] using
        centeredNormPulledRadicand_eq_of_eq_neg (-C0) d
    · simp only [centeredNormForcedFactor,
        centeredNormReducedPulledRadicand, if_neg hEq, if_neg hNeg,
        one_pow, one_mul]

/-- For a positive pullback exponent, the forced factor is nonzero. -/
theorem centeredNormForcedFactor_ne_zero
    (B C0 : K) {d : ℕ} (hd : 0 < d) :
    centeredNormForcedFactor B C0 d ≠ 0 := by
  classical
  by_cases hEq : B = C0
  · simp only [centeredNormForcedFactor, if_pos hEq]
    simpa only [C_1] using
      (X_pow_add_C_ne_zero (R := K) hd (1 : K))
  · by_cases hNeg : B = -C0
    · simp only [centeredNormForcedFactor, if_neg hEq, if_pos hNeg]
      simpa only [C_1] using
        (X_pow_sub_C_ne_zero (R := K) hd (1 : K))
    · simp only [centeredNormForcedFactor, if_neg hEq, if_neg hNeg]
      exact one_ne_zero

/-- Removing the forced polynomial square does not change the square class
in the rational function field. -/
theorem centeredNormPulledRadicand_isSquare_ratFunc_iff_reduced
    (B C0 : K) {d : ℕ} (hd : 0 < d) :
    IsSquare
        (algebraMap K[X] (RatFunc K)
          (centeredNormPulledRadicand B C0 d)) ↔
      IsSquare
        (algebraMap K[X] (RatFunc K)
          (centeredNormReducedPulledRadicand B C0 d)) := by
  rw [centeredNormPulledRadicand_eq_forcedFactor_sq_mul_reduced]
  simp only [map_mul, map_pow]
  exact isSquare_sq_mul_iff
    (algebraMap K[X] (RatFunc K) (centeredNormForcedFactor B C0 d))
    (algebraMap K[X] (RatFunc K)
      (centeredNormReducedPulledRadicand B C0 d))
    ((map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (centeredNormForcedFactor_ne_zero B C0 hd))

/-- Scalar extension commutes with the monic quadratic power pullback. -/
theorem map_monicQuadraticPowerPulledRadicand
    {L : Type*} [Field L] (phi : K →+* L)
    (A : K) (d : ℕ) :
    (monicQuadraticPowerPulledRadicand A d).map phi =
      monicQuadraticPowerPulledRadicand (phi A) d := by
  simp [monicQuadraticPowerPulledRadicand]

/-- The power chain rule for the monic quadratic pullback. -/
theorem mul_eval_derivative_monicQuadraticPowerPulledRadicand
    (A t : K) (d : ℕ) (hd : 0 < d) :
    t * eval t (monicQuadraticPowerPulledRadicand A d).derivative =
      (d : K) * t ^ d * (2 * t ^ d + A) := by
  have hpow (n : ℕ) (hn : 0 < n) :
      t * t ^ (n - 1) = t ^ n := by
    rw [← pow_succ']
    congr
    omega
  calc
    _ = (2 * d : ℕ) * (t * t ^ (2 * d - 1)) +
        A * (d : K) * (t * t ^ (d - 1)) := by
      simp only [monicQuadraticPowerPulledRadicand, derivative_add,
        derivative_pow, derivative_X, mul_one, derivative_mul, derivative_C,
        zero_mul, zero_add, derivative_one, eval_add, eval_mul, eval_C,
        eval_pow, eval_X, add_zero]
      ring
    _ = (2 * d : ℕ) * t ^ (2 * d) +
        A * (d : K) * t ^ d := by
      rw [hpow (2 * d) (by omega), hpow d hd]
    _ = (d : K) * t ^ d * (2 * t ^ d + A) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      rw [show 2 * d = d * 2 by omega, pow_mul]
      ring

/-- A tame power pullback of `Y² + A Y + 1` is separable when the
quadratic discriminant is nonzero. -/
theorem monicQuadraticPowerPulledRadicand_separable
    {A : K} (hdisc : A ^ 2 ≠ 4)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    (monicQuadraticPowerPulledRadicand A d).Separable := by
  rw [separable_def]
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (k := K) (AlgebraicClosure K)
      (monicQuadraticPowerPulledRadicand A d)
      (monicQuadraticPowerPulledRadicand A d).derivative).2
  intro t
  let phi : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  by_contra hcommon
  push Not at hcommon
  rcases hcommon with ⟨hroot, hderivative⟩
  have hrootMapped :
      eval t (monicQuadraticPowerPulledRadicand (phi A) d) = 0 := by
    rw [← map_monicQuadraticPowerPulledRadicand phi A d]
    simpa only [aeval_def, eval₂_eq_eval_map, phi] using hroot
  have hderivativeMapped :
      eval t
          (monicQuadraticPowerPulledRadicand (phi A) d).derivative = 0 := by
    rw [← map_monicQuadraticPowerPulledRadicand phi A d,
      derivative_map]
    simpa only [aeval_def, eval₂_eq_eval_map, phi] using hderivative
  have ht : t ≠ 0 := by
    intro ht
    subst t
    simpa [eval_monicQuadraticPowerPulledRadicand,
      Nat.ne_of_gt hd] using hrootMapped
  have hu : t ^ d ≠ 0 := pow_ne_zero d ht
  have hdegreeMapped : phi (d : K) ≠ 0 :=
    (map_ne_zero_iff phi phi.injective).mpr hdegree
  have hlinear : 2 * t ^ d + phi A = 0 := by
    have hchain :=
      mul_eval_derivative_monicQuadraticPowerPulledRadicand
        (phi A) t d hd
    rw [hderivativeMapped, mul_zero] at hchain
    exact (mul_eq_zero.mp hchain.symm).resolve_left
      (mul_ne_zero hdegreeMapped hu)
  have hquadratic :
      (t ^ d) ^ 2 + phi A * t ^ d + 1 = 0 := by
    simpa only [eval_monicQuadraticPowerPulledRadicand] using hrootMapped
  have hdiscMapped : phi (A ^ 2 - 4) = 0 := by
    simp only [map_sub, map_pow, map_ofNat]
    linear_combination
      (2 * t ^ d + phi A) * hlinear - 4 * hquadratic
  have hdiscNe : A ^ 2 - 4 ≠ 0 := sub_ne_zero.mpr hdisc
  exact (map_ne_zero_iff phi phi.injective).mpr hdiscNe hdiscMapped

/-- A tame monic quadratic pullback is not a polynomial unit. -/
theorem monicQuadraticPowerPulledRadicand_not_isUnit
    (A : K) {d : ℕ} (hd : 0 < d) :
    ¬ IsUnit (monicQuadraticPowerPulledRadicand A d) := by
  apply not_isUnit_of_natDegree_pos
  have hcoeff :
      (monicQuadraticPowerPulledRadicand A d).coeff (2 * d) = 1 := by
    rw [monicQuadraticPowerPulledRadicand, coeff_add, coeff_add,
      coeff_X_pow, coeff_C_mul_X_pow, coeff_one]
    simp only [if_pos, if_neg (show 2 * d ≠ d by omega),
      if_neg (show 2 * d ≠ 0 by omega), add_zero]
  have hle :=
    Polynomial.le_natDegree_of_ne_zero
      (show
        (monicQuadraticPowerPulledRadicand A d).coeff (2 * d) ≠ 0 by
        rw [hcoeff]
        exact one_ne_zero)
  omega

/-- Formal derivative of the centered-norm reciprocal quartic. -/
def centeredNormReciprocalQuarticDerivative
    (B C0 u : K) : K :=
  4 * u ^ 3 + 3 * (B * C0) * u ^ 2 +
    2 * (B ^ 2 + C0 ^ 2 - 2) * u + B * C0

/-- The derivative identity separating the two parabolic points from the
critical point of the centered-norm quadratic. -/
theorem centeredNormReciprocalQuartic_derivative_identity
    (B C0 u : K) :
    u * centeredNormReciprocalQuarticDerivative B C0 u -
        2 * centeredNormReciprocalQuartic B C0 u =
      (u ^ 2 - 1) * (2 * u ^ 2 + B * C0 * u + 2) := by
  simp only [centeredNormReciprocalQuarticDerivative,
    centeredNormReciprocalQuartic]
  ring

/-- Completing the square in the centered-norm quadratic gives the product
of the two coefficient discriminants. -/
theorem centeredNorm_completion_identity
    (B C0 middle : K) :
    (2 * middle + B * C0) ^ 2 -
        4 * centeredNorm B C0 middle =
      (B ^ 2 - 4) * (C0 ^ 2 - 4) := by
  simp only [centeredNorm, discriminant]
  ring

/-- Scalar extension commutes with the centered-norm pulled radicand. -/
theorem map_centeredNormPulledRadicand
    {L : Type*} [Field L] (phi : K →+* L)
    (B C0 : K) (d : ℕ) :
    (centeredNormPulledRadicand B C0 d).map phi =
      centeredNormPulledRadicand (phi B) (phi C0) d := by
  simp [centeredNormPulledRadicand, map_ofNat]

/-- The power chain rule for the centered reciprocal quartic. -/
theorem mul_eval_derivative_centeredNormPulledRadicand
    (B C0 t : K) (d : ℕ) (hd : 0 < d) :
    t * eval t (centeredNormPulledRadicand B C0 d).derivative =
      (d : K) * t ^ d *
        centeredNormReciprocalQuarticDerivative B C0 (t ^ d) := by
  have hpow (n : ℕ) (hn : 0 < n) :
      t * t ^ (n - 1) = t ^ n := by
    rw [← pow_succ']
    congr
    omega
  calc
    _ = (4 * d : ℕ) * (t * t ^ (4 * d - 1)) +
          B * C0 * ((3 * d : ℕ) * (t * t ^ (3 * d - 1))) +
          (B ^ 2 + C0 ^ 2 - 2) *
            ((2 * d : ℕ) * (t * t ^ (2 * d - 1))) +
          B * C0 * ((d : K) * (t * t ^ (d - 1))) := by
      simp only [centeredNormPulledRadicand, derivative_add,
        derivative_pow, derivative_X, mul_one, derivative_mul, derivative_C,
        zero_mul, zero_add, derivative_one, eval_add, eval_mul, eval_C,
        eval_pow, eval_X, add_zero]
      ring
    _ = (4 * d : ℕ) * t ^ (4 * d) +
          B * C0 * ((3 * d : ℕ) * t ^ (3 * d)) +
          (B ^ 2 + C0 ^ 2 - 2) *
            ((2 * d : ℕ) * t ^ (2 * d)) +
          B * C0 * ((d : K) * t ^ d) := by
      rw [hpow (4 * d) (by omega), hpow (3 * d) (by omega),
        hpow (2 * d) (by omega), hpow d hd]
    _ = (d : K) * t ^ d *
        centeredNormReciprocalQuarticDerivative B C0 (t ^ d) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat,
        centeredNormReciprocalQuarticDerivative]
      rw [show 4 * d = d * 4 by omega, show 3 * d = d * 3 by omega,
        show 2 * d = d * 2 by omega]
      simp only [pow_mul]
      ring

@[simp]
theorem eval_centeredNormPulledRadicand_zero
    (B C0 : K) {d : ℕ} (hd : 0 < d) :
    eval 0 (centeredNormPulledRadicand B C0 d) = 1 := by
  simp [centeredNormPulledRadicand, Nat.ne_of_gt hd]

/-- Away from both parabolic collisions, the full centered-norm pullback is
separable. -/
theorem centeredNormPulledRadicand_separable_of_ne_eq_ne_neg
    {B C0 : K}
    (hB : B ^ 2 ≠ 4) (hC : C0 ^ 2 ≠ 4)
    (hEq : B ≠ C0) (hNeg : B ≠ -C0)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    (centeredNormPulledRadicand B C0 d).Separable := by
  rw [separable_def]
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (k := K) (AlgebraicClosure K)
      (centeredNormPulledRadicand B C0 d)
      (centeredNormPulledRadicand B C0 d).derivative).2
  intro t
  let phi : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  by_contra hcommon
  push Not at hcommon
  rcases hcommon with ⟨hroot, hderivative⟩
  have hrootMapped :
      eval t (centeredNormPulledRadicand (phi B) (phi C0) d) = 0 := by
    rw [← map_centeredNormPulledRadicand phi B C0 d]
    simpa only [aeval_def, eval₂_eq_eval_map, phi] using hroot
  have hderivativeMapped :
      eval t
          (centeredNormPulledRadicand (phi B) (phi C0) d).derivative = 0 := by
    rw [← map_centeredNormPulledRadicand phi B C0 d, derivative_map]
    simpa only [aeval_def, eval₂_eq_eval_map, phi] using hderivative
  have ht : t ≠ 0 := by
    intro ht
    subst t
    simpa only [eval_centeredNormPulledRadicand_zero (phi B) (phi C0) hd,
      one_ne_zero] using hrootMapped
  have hu : t ^ d ≠ 0 := pow_ne_zero d ht
  have hdegreeMapped : phi (d : K) ≠ 0 :=
    (map_ne_zero_iff phi phi.injective).mpr hdegree
  have hquartic :
      centeredNormReciprocalQuartic (phi B) (phi C0) (t ^ d) = 0 := by
    simpa only [eval_centeredNormPulledRadicand] using hrootMapped
  have hquarticDerivative :
      centeredNormReciprocalQuarticDerivative
        (phi B) (phi C0) (t ^ d) = 0 := by
    have hchain :=
      mul_eval_derivative_centeredNormPulledRadicand
        (phi B) (phi C0) t d hd
    rw [hderivativeMapped, mul_zero] at hchain
    exact (mul_eq_zero.mp hchain.symm).resolve_left
      (mul_ne_zero hdegreeMapped hu)
  have hcritical :
      (t ^ d) ^ 2 - 1 = 0 ∨
        2 * (t ^ d) ^ 2 + phi B * phi C0 * t ^ d + 2 = 0 := by
    have hidentity :=
      centeredNormReciprocalQuartic_derivative_identity
        (phi B) (phi C0) (t ^ d)
    rw [hquarticDerivative, hquartic] at hidentity
    have hproduct :
        ((t ^ d) ^ 2 - 1) *
          (2 * (t ^ d) ^ 2 + phi B * phi C0 * t ^ d + 2) = 0 := by
      simpa using hidentity.symm
    exact mul_eq_zero.mp hproduct
  rcases hcritical with hparabolic | hstationary
  · have hfactor :
        (t ^ d - 1) * (t ^ d + 1) = 0 := by
      calc
        (t ^ d - 1) * (t ^ d + 1) = (t ^ d) ^ 2 - 1 := by ring
        _ = 0 := hparabolic
    rcases mul_eq_zero.mp hfactor with hone | hnegOne
    · have huOne : t ^ d = 1 := sub_eq_zero.mp hone
      have hsumK : B + C0 ≠ 0 := by
        intro hsum
        apply hNeg
        linear_combination hsum
      have hsum :
          phi B + phi C0 ≠ 0 := by
        have hmap :=
          (map_ne_zero_iff phi phi.injective).mpr hsumK
        simpa only [map_add] using hmap
      have hvalue :
          centeredNormReciprocalQuartic (phi B) (phi C0) 1 =
            (phi B + phi C0) ^ 2 := by
        simp only [centeredNormReciprocalQuartic]
        ring
      rw [huOne] at hquartic
      exact (pow_ne_zero 2 hsum) (hvalue.symm.trans hquartic)
    · have huNegOne : t ^ d = -1 := by
        linear_combination hnegOne
      have hdiffK : B - C0 ≠ 0 := sub_ne_zero.mpr hEq
      have hdiff :
          phi B - phi C0 ≠ 0 := by
        have hmap :=
          (map_ne_zero_iff phi phi.injective).mpr hdiffK
        simpa only [map_sub] using hmap
      have hvalue :
          centeredNormReciprocalQuartic (phi B) (phi C0) (-1) =
            (phi B - phi C0) ^ 2 := by
        simp only [centeredNormReciprocalQuartic]
        ring
      rw [huNegOne] at hquartic
      exact (pow_ne_zero 2 hdiff) (hvalue.symm.trans hquartic)
  · have hlinear :
        2 * (t ^ d + (t ^ d)⁻¹) + phi B * phi C0 = 0 := by
      field_simp [hu]
      linear_combination hstationary
    have hcenter :
        centeredNorm (phi B) (phi C0)
          (t ^ d + (t ^ d)⁻¹) = 0 := by
      have hidentity :=
        centeredNormReciprocalQuartic_eq_mul_centeredNorm
          (phi B) (phi C0) (t ^ d) hu
      rw [hquartic] at hidentity
      exact (mul_eq_zero.mp hidentity.symm).resolve_left
        (pow_ne_zero 2 hu)
    have hcompletion :=
      centeredNorm_completion_identity
        (phi B) (phi C0) (t ^ d + (t ^ d)⁻¹)
    rw [hlinear, hcenter] at hcompletion
    have hdiscZero :
        ((phi B) ^ 2 - 4) * ((phi C0) ^ 2 - 4) = 0 := by
      simpa using hcompletion.symm
    have hBMap : (phi B) ^ 2 ≠ 4 := by
      have hmap :=
        (map_ne_zero_iff phi phi.injective).mpr
          (sub_ne_zero.mpr hB)
      apply sub_ne_zero.mp
      simpa only [map_sub, map_pow, map_ofNat] using hmap
    have hCMap : (phi C0) ^ 2 ≠ 4 := by
      have hmap :=
        (map_ne_zero_iff phi phi.injective).mpr
          (sub_ne_zero.mpr hC)
      apply sub_ne_zero.mp
      simpa only [map_sub, map_pow, map_ofNat] using hmap
    exact mul_ne_zero (sub_ne_zero.mpr hBMap)
      (sub_ne_zero.mpr hCMap) hdiscZero

/-- The full centered-norm pullback is not a polynomial unit. -/
theorem centeredNormPulledRadicand_not_isUnit
    (B C0 : K) {d : ℕ} (hd : 0 < d) :
    ¬ IsUnit (centeredNormPulledRadicand B C0 d) := by
  apply not_isUnit_of_natDegree_pos
  have hcoeff :
      (centeredNormPulledRadicand B C0 d).coeff (4 * d) = 1 := by
    rw [centeredNormPulledRadicand, coeff_add, coeff_add, coeff_add,
      coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
      coeff_C_mul_X_pow, coeff_one]
    simp only [if_pos, if_neg (show 4 * d ≠ 3 * d by omega),
      if_neg (show 4 * d ≠ 2 * d by omega),
      if_neg (show 4 * d ≠ d by omega),
      if_neg (show 4 * d ≠ 0 by omega), add_zero]
  have hle :=
    Polynomial.le_natDegree_of_ne_zero
      (show (centeredNormPulledRadicand B C0 d).coeff (4 * d) ≠ 0 by
        rw [hcoeff]
        exact one_ne_zero)
  omega

/-- Under a nonzero moving coefficient pair, the reduced centered pullback
is separable in all three collision cases. -/
theorem centeredNormReducedPulledRadicand_separable
    {B C0 : K}
    (hB : B ^ 2 ≠ 4) (hC : C0 ^ 2 ≠ 4)
    (hpair : (B, C0) ≠ (0, 0))
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    (centeredNormReducedPulledRadicand B C0 d).Separable := by
  classical
  by_cases hEq : B = C0
  · have hB0 : B ≠ 0 := by
      intro hzero
      apply hpair
      simp only [Prod.mk.injEq]
      exact ⟨hzero, hEq ▸ hzero⟩
    have hfactor :
        (B ^ 2 - 2) ^ 2 - 4 = B ^ 2 * (B ^ 2 - 4) := by
      ring
    have hdisc : (B ^ 2 - 2) ^ 2 ≠ 4 := by
      apply sub_ne_zero.mp
      rw [hfactor]
      exact mul_ne_zero (pow_ne_zero 2 hB0) (sub_ne_zero.mpr hB)
    simp only [centeredNormReducedPulledRadicand, if_pos hEq]
    exact monicQuadraticPowerPulledRadicand_separable hdisc hd hdegree
  · by_cases hNeg : B = -C0
    · have hB0 : B ≠ 0 := by
        intro hzero
        apply hpair
        have hC0 : C0 = 0 := by
          have hnegC : -C0 = 0 := by
            calc
              -C0 = B := hNeg.symm
              _ = 0 := hzero
          exact neg_eq_zero.mp hnegC
        exact Prod.ext hzero hC0
      have hfactor :
          (2 - B ^ 2) ^ 2 - 4 = B ^ 2 * (B ^ 2 - 4) := by
        ring
      have hdisc : (2 - B ^ 2) ^ 2 ≠ 4 := by
        apply sub_ne_zero.mp
        rw [hfactor]
        exact mul_ne_zero (pow_ne_zero 2 hB0) (sub_ne_zero.mpr hB)
      simp only [centeredNormReducedPulledRadicand,
        if_neg hEq, if_pos hNeg]
      exact monicQuadraticPowerPulledRadicand_separable hdisc hd hdegree
    · simp only [centeredNormReducedPulledRadicand,
        if_neg hEq, if_neg hNeg]
      exact centeredNormPulledRadicand_separable_of_ne_eq_ne_neg
        hB hC hEq hNeg hd hdegree

/-- The reduced centered pullback is never a polynomial unit for a positive
pullback exponent. -/
theorem centeredNormReducedPulledRadicand_not_isUnit
    (B C0 : K) {d : ℕ} (hd : 0 < d) :
    ¬ IsUnit (centeredNormReducedPulledRadicand B C0 d) := by
  classical
  by_cases hEq : B = C0
  · simp only [centeredNormReducedPulledRadicand, if_pos hEq]
    exact monicQuadraticPowerPulledRadicand_not_isUnit _ hd
  · by_cases hNeg : B = -C0
    · simp only [centeredNormReducedPulledRadicand,
        if_neg hEq, if_pos hNeg]
      exact monicQuadraticPowerPulledRadicand_not_isUnit _ hd
    · simp only [centeredNormReducedPulledRadicand,
        if_neg hEq, if_neg hNeg]
      exact centeredNormPulledRadicand_not_isUnit B C0 hd

/-- The reduced centered pullback is squarefree. -/
theorem centeredNormReducedPulledRadicand_squarefree
    {B C0 : K}
    (hB : B ^ 2 ≠ 4) (hC : C0 ^ 2 ≠ 4)
    (hpair : (B, C0) ≠ (0, 0))
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    Squarefree (centeredNormReducedPulledRadicand B C0 d) :=
  (centeredNormReducedPulledRadicand_separable
    hB hC hpair hd hdegree).squarefree

/-- The reduced centered pullback represents a nonsquare in the rational
function field. -/
theorem centeredNormReducedPulledRadicand_not_isSquare_ratFunc
    {B C0 : K}
    (hB : B ^ 2 ≠ 4) (hC : C0 ^ 2 ≠ 4)
    (hpair : (B, C0) ≠ (0, 0))
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    ¬ IsSquare
      (algebraMap K[X] (RatFunc K)
        (centeredNormReducedPulledRadicand B C0 d)) :=
  BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
    (centeredNormReducedPulledRadicand_squarefree
      hB hC hpair hd hdegree)
    (centeredNormReducedPulledRadicand_not_isUnit B C0 hd)

end

end GenMarkoff.General.Cage
