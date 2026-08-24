import GenMarkoff.General.Cage.ConnectingIncidenceAlgebra
import GenMarkoff.General.MiddleGame.ActualOrderGrowth
import BGS.CorvajaZannier.BivariateResultant
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Power pullbacks for the unequal connecting cage

Substituting the split trace `u + u⁻¹` into either an unequal incidence
quadratic or the middle-axis centered-norm quadratic and clearing `u²`
produces a reciprocal quartic.  Pulling back further along `u = t^d` gives
the polynomial radicands used by the connecting-cage plane counts.

This file first records the exact algebraic identities.  Separability,
square-class independence, and the seven plane models are developed at the
next proof boundary.
-/

namespace GenMarkoff.General.Cage

open Polynomial

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- Middle coefficient after clearing denominators in the unequal incidence
quadratic at `middle = u + u⁻¹`. -/
def incidencePulledMiddleCoefficient
    (a : Coefficients K) (xi : K) : K :=
  2 * incidenceLeadingCoefficient xi +
    incidenceConstantCoefficient a xi

/-- The reciprocal quartic
`u² * incidenceDiscriminant a xi (u + u⁻¹)`. -/
def incidenceReciprocalQuartic
    (a : Coefficients K) (xi u : K) : K :=
  incidenceLeadingCoefficient xi * u ^ 4 +
    incidenceLinearCoefficient a xi * u ^ 3 +
    incidencePulledMiddleCoefficient a xi * u ^ 2 +
    incidenceLinearCoefficient a xi * u +
    incidenceLeadingCoefficient xi

/-- Formal derivative of the unequal incidence reciprocal quartic. -/
def incidenceReciprocalQuarticDerivative
    (a : Coefficients K) (xi u : K) : K :=
  4 * incidenceLeadingCoefficient xi * u ^ 3 +
    3 * incidenceLinearCoefficient a xi * u ^ 2 +
    2 * incidencePulledMiddleCoefficient a xi * u +
    incidenceLinearCoefficient a xi

/-- Pullback of the unequal incidence reciprocal quartic along
`u = t^d`. -/
def incidencePulledRadicand
    (a : Coefficients K) (xi : K) (d : ℕ) : K[X] :=
  C (incidenceLeadingCoefficient xi) * X ^ (4 * d) +
    C (incidenceLinearCoefficient a xi) * X ^ (3 * d) +
    C (incidencePulledMiddleCoefficient a xi) * X ^ (2 * d) +
    C (incidenceLinearCoefficient a xi) * X ^ d +
    C (incidenceLeadingCoefficient xi)

@[simp]
theorem eval_incidencePulledRadicand
    (a : Coefficients K) (xi t : K) (d : ℕ) :
    eval t (incidencePulledRadicand a xi d) =
      incidenceReciprocalQuartic a xi (t ^ d) := by
  simp only [incidencePulledRadicand, incidenceReciprocalQuartic,
    eval_add, eval_mul, eval_C, eval_pow, eval_X]
  simp only [← pow_mul]
  ring

theorem incidenceReciprocalQuartic_eq_mul_discriminant
    (a : Coefficients K) (xi u : K) (hu : u ≠ 0) :
    incidenceReciprocalQuartic a xi u =
      u ^ 2 * incidenceDiscriminant a xi (u + u⁻¹) := by
  simp only [incidenceReciprocalQuartic,
    incidencePulledMiddleCoefficient, incidenceLeadingCoefficient,
    incidenceLinearCoefficient, incidenceConstantCoefficient,
    incidenceDiscriminant]
  field_simp [hu]
  ring

theorem incidenceReciprocalQuartic_derivative_identity
    (a : Coefficients K) (xi u : K) (hu : u ≠ 0) :
    u * incidenceReciprocalQuarticDerivative a xi u -
        2 * incidenceReciprocalQuartic a xi u =
      u * (u ^ 2 - 1) *
        (2 * incidenceLeadingCoefficient xi * (u + u⁻¹) +
          incidenceLinearCoefficient a xi) := by
  simp only [incidenceReciprocalQuarticDerivative,
    incidenceReciprocalQuartic, incidencePulledMiddleCoefficient]
  field_simp [hu]
  ring

/-- At the negative parabolic middle trace, the candidate-regular
`even-minus` factor is the remaining obstruction. -/
theorem incidenceDiscriminant_neg_two
    (a : Coefficients K) (xi : K) :
    incidenceDiscriminant a xi (-2) =
      -(a.a2 - 2) *
        eval xi
          (orderedTraceEvenMinusPolynomial a.a1 a.a2 a.a3) := by
  simp only [incidenceDiscriminant, traceLinearCoefficient1,
    traceLinearCoefficient2, traceLinearCoefficient3, traceConstant,
    eval_orderedTraceEvenMinusPolynomial]
  ring

/-- At the positive parabolic middle trace, the candidate-regular
`even-plus` factor is the remaining obstruction. -/
theorem incidenceDiscriminant_two
    (a : Coefficients K) (xi : K) :
    incidenceDiscriminant a xi 2 =
      -(a.a2 + 2) *
        eval xi
          (orderedTraceEvenPlusPolynomial a.a1 a.a2 a.a3) := by
  simp only [incidenceDiscriminant, traceLinearCoefficient1,
    traceLinearCoefficient2, traceLinearCoefficient3, traceConstant,
    eval_orderedTraceEvenPlusPolynomial]
  ring

/-- Completing the square in the incidence quadratic recovers its scalar
quadratic discriminant. -/
theorem incidenceQuadratic_completion_identity
    (a : Coefficients K) (xi middle : K) :
    (2 * incidenceLeadingCoefficient xi * middle +
        incidenceLinearCoefficient a xi) ^ 2 -
      4 * incidenceLeadingCoefficient xi *
        incidenceDiscriminant a xi middle =
      incidenceQuadraticDiscriminant a xi := by
  simp only [incidenceLeadingCoefficient, incidenceLinearCoefficient,
    incidenceDiscriminant, incidenceQuadraticDiscriminant,
    incidenceConstantCoefficient]
  ring

/-- A field homomorphism commutes with the scalar unequal incidence
discriminant. -/
theorem map_incidenceDiscriminant
    {L : Type*} [Field L] (phi : K →+* L)
    (a : Coefficients K) (xi middle : K) :
    phi (incidenceDiscriminant a xi middle) =
      incidenceDiscriminant
        (MiddleGame.mapCoefficients phi a) (phi xi) (phi middle) := by
  have hTwo : phi (2 : K) = (2 : L) := by
    exact map_ofNat phi 2
  have hFour : phi (4 : K) = (4 : L) := by
    exact map_ofNat phi 4
  simp [incidenceDiscriminant, traceLinearCoefficient1,
    traceLinearCoefficient2, traceLinearCoefficient3, traceConstant,
    MiddleGame.mapCoefficients, hTwo, hFour]

/-- A field homomorphism commutes with the scalar discriminant of the
unequal incidence quadratic. -/
theorem map_incidenceQuadraticDiscriminant
    {L : Type*} [Field L] (phi : K →+* L)
    (a : Coefficients K) (xi : K) :
    phi (incidenceQuadraticDiscriminant a xi) =
      incidenceQuadraticDiscriminant
        (MiddleGame.mapCoefficients phi a) (phi xi) := by
  have hTwo : phi (2 : K) = (2 : L) := by
    exact map_ofNat phi 2
  have hFour : phi (4 : K) = (4 : L) := by
    exact map_ofNat phi 4
  simp [incidenceQuadraticDiscriminant, incidenceLeadingCoefficient,
    incidenceLinearCoefficient, incidenceConstantCoefficient,
    traceLinearCoefficient1, traceLinearCoefficient2,
    traceLinearCoefficient3, traceConstant,
    MiddleGame.mapCoefficients, hTwo, hFour]

/-- A field homomorphism commutes with the unequal incidence-discriminant
polynomial. -/
theorem map_incidenceDiscriminantPolynomial
    {L : Type*} [Field L] (phi : K →+* L)
    (a : Coefficients K) (xi : K) :
    (incidenceDiscriminantPolynomial a xi).map phi =
      incidenceDiscriminantPolynomial
        (MiddleGame.mapCoefficients phi a) (phi xi) := by
  have hTwo : phi (2 : K) = (2 : L) := by
    exact map_ofNat phi 2
  simp [incidenceDiscriminantPolynomial, traceLinearCoefficient1,
    traceLinearCoefficient2, traceLinearCoefficient3, traceConstant,
    MiddleGame.mapCoefficients, hTwo]

/-- Ordered candidate regularity makes the unequal incidence polynomial
genuinely quadratic. -/
theorem incidenceDiscriminantPolynomial_natDegree
    {a : Coefficients K} {xi : K}
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi) :
    (incidenceDiscriminantPolynomial a xi).natDegree = 2 := by
  have hLeading : incidenceLeadingCoefficient xi ≠ 0 := by
    simpa only [incidenceLeadingCoefficient,
      eval_orderedTraceDiscriminantPolynomial] using hregular.1
  rw [incidenceDiscriminantPolynomial_eq_quadratic]
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · compute_degree
  · simp [hLeading]

/-- Candidate regularity excludes the negative parabolic middle trace.
Unlike the symmetric specialization, the remaining even-minus factor
depends on the fixed outer trace. -/
theorem incidenceDiscriminant_neg_two_ne_zero
    {a : Coefficients K} {xi : K}
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi) :
    incidenceDiscriminant a xi (-2) ≠ 0 := by
  rw [incidenceDiscriminant_neg_two]
  apply mul_ne_zero
  · apply neg_ne_zero.mpr
    apply sub_ne_zero.mpr
    intro hA2Two
    apply hA2
    rw [hA2Two]
    norm_num
  · exact hregular.2.2.2.2.1

/-- Candidate regularity excludes the positive parabolic middle trace. -/
theorem incidenceDiscriminant_two_ne_zero
    {a : Coefficients K} {xi : K}
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi) :
    incidenceDiscriminant a xi 2 ≠ 0 := by
  rw [incidenceDiscriminant_two]
  apply mul_ne_zero
  · apply neg_ne_zero.mpr
    intro hA2NegTwo
    apply hA2
    have hA2' : a.a2 = -2 := by linear_combination hA2NegTwo
    rw [hA2']
    norm_num
  · exact hregular.2.2.2.2.2

/-- The formal derivative of the pulled radicand obeys the expected power
chain rule after multiplication by the parameter. -/
theorem mul_eval_derivative_incidencePulledRadicand
    (a : Coefficients K) (xi t : K) (d : ℕ) (hd : 0 < d) :
    t * eval t (incidencePulledRadicand a xi d).derivative =
      (d : K) * t ^ d *
        incidenceReciprocalQuarticDerivative a xi (t ^ d) := by
  simp only [incidencePulledRadicand, derivative_add, derivative_mul,
    derivative_C, zero_mul, zero_add, derivative_pow, derivative_X,
    mul_one, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    add_zero, incidenceReciprocalQuarticDerivative]
  have hpow (k : ℕ) (hk : 0 < k) :
      t * t ^ (k - 1) = t ^ k := by
    rw [← pow_succ']
    congr
    omega
  calc
    _ = incidenceLeadingCoefficient xi * ((4 * d : ℕ) : K) *
              (t * t ^ (4 * d - 1)) +
          incidenceLinearCoefficient a xi * ((3 * d : ℕ) : K) *
              (t * t ^ (3 * d - 1)) +
          incidencePulledMiddleCoefficient a xi * ((2 * d : ℕ) : K) *
              (t * t ^ (2 * d - 1)) +
          incidenceLinearCoefficient a xi * (d : K) *
              (t * t ^ (d - 1)) := by ring
    _ =
        incidenceLeadingCoefficient xi * ((4 * d : ℕ) : K) * t ^ (4 * d) +
          incidenceLinearCoefficient a xi * ((3 * d : ℕ) : K) * t ^ (3 * d) +
          incidencePulledMiddleCoefficient a xi * ((2 * d : ℕ) : K) *
            t ^ (2 * d) +
          incidenceLinearCoefficient a xi * (d : K) * t ^ d := by
      rw [hpow (4 * d) (by omega), hpow (3 * d) (by omega),
        hpow (2 * d) (by omega), hpow d hd]
    _ = (d : K) * t ^ d *
        incidenceReciprocalQuarticDerivative a xi (t ^ d) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat,
        incidenceReciprocalQuarticDerivative]
      rw [show 4 * d = d * 4 by omega, show 3 * d = d * 3 by omega,
        show 2 * d = d * 2 by omega]
      simp only [pow_mul]
      ring

@[simp]
theorem eval_incidencePulledRadicand_zero
    (a : Coefficients K) (xi : K) {d : ℕ} (hd : 0 < d) :
    eval 0 (incidencePulledRadicand a xi d) =
      incidenceLeadingCoefficient xi := by
  simp [incidencePulledRadicand, Nat.ne_of_gt hd]

/-- Scalar extension commutes with the unequal pulled incidence
radicand. -/
theorem map_incidencePulledRadicand
    {L : Type*} [Field L] (phi : K →+* L)
    (a : Coefficients K) (xi : K) (d : ℕ) :
    (incidencePulledRadicand a xi d).map phi =
      incidencePulledRadicand
        (MiddleGame.mapCoefficients phi a) (phi xi) d := by
  have hTwo : phi (2 : K) = (2 : L) := by
    exact map_ofNat phi 2
  have hFour : phi (4 : K) = (4 : L) := by
    exact map_ofNat phi 4
  have hLeading :
      phi (incidenceLeadingCoefficient xi) =
        incidenceLeadingCoefficient (phi xi) := by
    simp [incidenceLeadingCoefficient, hFour]
  have hLinear :
      phi (incidenceLinearCoefficient a xi) =
        incidenceLinearCoefficient
          (MiddleGame.mapCoefficients phi a) (phi xi) := by
    simp [incidenceLinearCoefficient, traceLinearCoefficient2,
      traceLinearCoefficient3, MiddleGame.mapCoefficients, hTwo, hFour]
  have hMiddle :
      phi (incidencePulledMiddleCoefficient a xi) =
        incidencePulledMiddleCoefficient
          (MiddleGame.mapCoefficients phi a) (phi xi) := by
    simp [incidencePulledMiddleCoefficient,
      incidenceLeadingCoefficient, incidenceConstantCoefficient,
      traceLinearCoefficient1, traceLinearCoefficient3, traceConstant,
      MiddleGame.mapCoefficients, hTwo, hFour]
  simp only [incidencePulledRadicand, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, hLeading, hLinear, hMiddle]

/-- The power-pulled unequal incidence radicand has no repeated geometric
root.

A repeated root would either lie over one of the parabolic middle traces
`±2`, or give a repeated root of the original incidence quadratic.
Ordered candidate regularity excludes all three alternatives. -/
theorem incidencePulledRadicand_separable
    (h2 : (2 : K) ≠ 0)
    {a : Coefficients K} {xi : K}
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    (incidencePulledRadicand a xi d).Separable := by
  rw [separable_def]
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (k := K) (AlgebraicClosure K) (incidencePulledRadicand a xi d)
      (incidencePulledRadicand a xi d).derivative).2
  intro t
  let phi : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  by_contra hcommon
  push Not at hcommon
  rcases hcommon with ⟨hroot, hderivative⟩
  have hLeadingK : incidenceLeadingCoefficient xi ≠ 0 := by
    simpa only [incidenceLeadingCoefficient,
      eval_orderedTraceDiscriminantPolynomial] using hregular.1
  have hLeading :
      incidenceLeadingCoefficient (phi xi) ≠ 0 := by
    have hmap :=
      (map_ne_zero_iff phi phi.injective).mpr hLeadingK
    simpa only [incidenceLeadingCoefficient, map_sub, map_pow,
      map_ofNat] using hmap
  have hDegree :
      phi (d : K) ≠ 0 :=
    (map_ne_zero_iff phi phi.injective).mpr hdegree
  have hrootMapped :
      eval t
          (incidencePulledRadicand
            (MiddleGame.mapCoefficients phi a) (phi xi) d) = 0 := by
    rw [← map_incidencePulledRadicand phi a xi d]
    simpa only [aeval_def, eval₂_eq_eval_map, phi] using hroot
  have hderivativeMapped :
      eval t
          (incidencePulledRadicand
            (MiddleGame.mapCoefficients phi a) (phi xi) d).derivative = 0 := by
    rw [← map_incidencePulledRadicand phi a xi d,
      derivative_map]
    simpa only [aeval_def, eval₂_eq_eval_map, phi] using hderivative
  have ht : t ≠ 0 := by
    intro ht
    subst t
    apply hLeading
    simpa only [eval_incidencePulledRadicand_zero
      (MiddleGame.mapCoefficients phi a) (phi xi) hd] using hrootMapped
  have hu : t ^ d ≠ 0 := pow_ne_zero d ht
  have hquartic :
      incidenceReciprocalQuartic
        (MiddleGame.mapCoefficients phi a) (phi xi) (t ^ d) = 0 := by
    simpa only [eval_incidencePulledRadicand] using hrootMapped
  have hincidence :
      incidenceDiscriminant
        (MiddleGame.mapCoefficients phi a) (phi xi)
        (t ^ d + (t ^ d)⁻¹) = 0 := by
    have hidentity :=
      incidenceReciprocalQuartic_eq_mul_discriminant
        (MiddleGame.mapCoefficients phi a) (phi xi) (t ^ d) hu
    rw [hquartic] at hidentity
    exact (mul_eq_zero.mp hidentity.symm).resolve_left
      (pow_ne_zero 2 hu)
  have hquarticDerivative :
      incidenceReciprocalQuarticDerivative
        (MiddleGame.mapCoefficients phi a) (phi xi) (t ^ d) = 0 := by
    have hchain :=
      mul_eval_derivative_incidencePulledRadicand
        (MiddleGame.mapCoefficients phi a) (phi xi) t d hd
    rw [hderivativeMapped, mul_zero] at hchain
    exact (mul_eq_zero.mp hchain.symm).resolve_left
      (mul_ne_zero hDegree hu)
  have hcritical :
      (t ^ d) ^ 2 - 1 = 0 ∨
        2 * incidenceLeadingCoefficient (phi xi) *
              (t ^ d + (t ^ d)⁻¹) +
            incidenceLinearCoefficient
              (MiddleGame.mapCoefficients phi a) (phi xi) = 0 := by
    have hidentity :=
      incidenceReciprocalQuartic_derivative_identity
        (MiddleGame.mapCoefficients phi a) (phi xi) (t ^ d) hu
    rw [hquarticDerivative, hquartic] at hidentity
    have hproductFull :
        t ^ d *
          (((t ^ d) ^ 2 - 1) *
            (2 * incidenceLeadingCoefficient (phi xi) *
                  (t ^ d + (t ^ d)⁻¹) +
                incidenceLinearCoefficient
                  (MiddleGame.mapCoefficients phi a) (phi xi))) = 0 := by
      calc
        t ^ d *
            (((t ^ d) ^ 2 - 1) *
              (2 * incidenceLeadingCoefficient (phi xi) *
                    (t ^ d + (t ^ d)⁻¹) +
                  incidenceLinearCoefficient
                    (MiddleGame.mapCoefficients phi a) (phi xi))) =
            t ^ d * ((t ^ d) ^ 2 - 1) *
              (2 * incidenceLeadingCoefficient (phi xi) *
                    (t ^ d + (t ^ d)⁻¹) +
                  incidenceLinearCoefficient
                    (MiddleGame.mapCoefficients phi a) (phi xi)) := by ring
        _ = t ^ d * 0 - 2 * 0 := hidentity.symm
        _ = 0 := by ring
    have hproduct :
        ((t ^ d) ^ 2 - 1) *
          (2 * incidenceLeadingCoefficient (phi xi) *
                (t ^ d + (t ^ d)⁻¹) +
              incidenceLinearCoefficient
                (MiddleGame.mapCoefficients phi a) (phi xi)) = 0 := by
      exact (mul_eq_zero.mp hproductFull).resolve_left hu
    exact mul_eq_zero.mp hproduct
  rcases hcritical with hparabolic | hlinear
  · have hfactor :
        (t ^ d - 1) * (t ^ d + 1) = 0 := by
      calc
        (t ^ d - 1) * (t ^ d + 1) = (t ^ d) ^ 2 - 1 := by ring
        _ = 0 := hparabolic
    rcases mul_eq_zero.mp hfactor with hone | hnegOne
    · have huOne : t ^ d = 1 := sub_eq_zero.mp hone
      have hmiddleOne :
          (1 : AlgebraicClosure K) +
              (1 : AlgebraicClosure K)⁻¹ = 2 := by
        norm_num
      have hzero :
          incidenceDiscriminant
            (MiddleGame.mapCoefficients phi a) (phi xi) 2 = 0 := by
        rw [huOne, hmiddleOne] at hincidence
        exact hincidence
      have hnonzeroK :=
        incidenceDiscriminant_two_ne_zero hA2 hregular
      have hnonzeroMap :=
        (map_ne_zero_iff phi phi.injective).mpr hnonzeroK
      have hnonzero :
          incidenceDiscriminant
            (MiddleGame.mapCoefficients phi a) (phi xi) 2 ≠ 0 := by
        simpa only [map_incidenceDiscriminant, map_ofNat] using hnonzeroMap
      exact hnonzero hzero
    · have huNegOne : t ^ d = -1 := by
        linear_combination hnegOne
      have hmiddleNegOne :
          (-1 : AlgebraicClosure K) +
              (-1 : AlgebraicClosure K)⁻¹ = -2 := by
        norm_num
      have hzero :
          incidenceDiscriminant
            (MiddleGame.mapCoefficients phi a) (phi xi) (-2) = 0 := by
        rw [huNegOne, hmiddleNegOne] at hincidence
        exact hincidence
      have hnonzeroK :=
        incidenceDiscriminant_neg_two_ne_zero hA2 hregular
      have hnonzeroMap :=
        (map_ne_zero_iff phi phi.injective).mpr hnonzeroK
      have hnonzero :
          incidenceDiscriminant
            (MiddleGame.mapCoefficients phi a) (phi xi) (-2) ≠ 0 := by
        simpa only [map_incidenceDiscriminant, map_neg, map_ofNat]
          using hnonzeroMap
      exact hnonzero hzero
  · have hcompletion :=
      incidenceQuadratic_completion_identity
        (MiddleGame.mapCoefficients phi a) (phi xi)
        (t ^ d + (t ^ d)⁻¹)
    rw [hlinear, hincidence] at hcompletion
    have hdiscriminantZero :
        incidenceQuadraticDiscriminant
          (MiddleGame.mapCoefficients phi a) (phi xi) = 0 := by
      simpa using hcompletion.symm
    have hdiscriminantK :=
      incidenceQuadraticDiscriminant_ne_zero_of_candidateRegular
        a xi h2 hregular
    have hdiscriminantMap :=
      (map_ne_zero_iff phi phi.injective).mpr hdiscriminantK
    have hdiscriminant :
        incidenceQuadraticDiscriminant
          (MiddleGame.mapCoefficients phi a) (phi xi) ≠ 0 := by
      simpa only [map_incidenceQuadraticDiscriminant]
        using hdiscriminantMap
    exact hdiscriminant hdiscriminantZero

/-- The leading coefficient survives at degree `4d`. -/
theorem incidencePulledRadicand_coeff_four_mul
    (a : Coefficients K) (xi : K) {d : ℕ} (hd : 0 < d) :
    (incidencePulledRadicand a xi d).coeff (4 * d) =
      incidenceLeadingCoefficient xi := by
  rw [incidencePulledRadicand]
  rw [coeff_add, coeff_add, coeff_add, coeff_add,
    coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
    coeff_C_mul_X_pow, coeff_C]
  simp only [if_true, if_neg (show 4 * d ≠ 3 * d by omega),
    if_neg (show 4 * d ≠ 2 * d by omega),
    if_neg (show 4 * d ≠ d by omega),
    if_neg (show 4 * d ≠ 0 by omega), add_zero]

/-- A candidate-regular unequal pulled radicand is not a polynomial unit. -/
theorem incidencePulledRadicand_not_isUnit
    {a : Coefficients K} {xi : K}
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    {d : ℕ} (hd : 0 < d) :
    ¬ IsUnit (incidencePulledRadicand a xi d) := by
  apply not_isUnit_of_natDegree_pos
  have hLeading : incidenceLeadingCoefficient xi ≠ 0 := by
    simpa only [incidenceLeadingCoefficient,
      eval_orderedTraceDiscriminantPolynomial] using hregular.1
  have hcoeff :
      (incidencePulledRadicand a xi d).coeff (4 * d) ≠ 0 := by
    simpa only [incidencePulledRadicand_coeff_four_mul a xi hd]
      using hLeading
  have hle := Polynomial.le_natDegree_of_ne_zero hcoeff
  omega

/-- The two unequal incidence pullbacks have disjoint geometric zero sets
when their formal quadratic resultant is nonzero. -/
theorem incidencePulledRadicand_isCoprime
    {a : Coefficients K} {xi eta : K}
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hpair : IsConnectingIncidencePair a xi eta)
    {d : ℕ} (hd : 0 < d) :
    IsCoprime (incidencePulledRadicand a xi d)
      (incidencePulledRadicand a eta d) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (k := K) (AlgebraicClosure K)
      (incidencePulledRadicand a xi d)
      (incidencePulledRadicand a eta d)).2
  intro t
  let phi : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  by_contra hcommon
  push Not at hcommon
  rcases hcommon with ⟨hxiRoot, hetaRoot⟩
  have hxiRootMapped :
      eval t
          (incidencePulledRadicand
            (MiddleGame.mapCoefficients phi a) (phi xi) d) = 0 := by
    rw [← map_incidencePulledRadicand phi a xi d]
    simpa only [aeval_def, eval₂_eq_eval_map, phi] using hxiRoot
  have hetaRootMapped :
      eval t
          (incidencePulledRadicand
            (MiddleGame.mapCoefficients phi a) (phi eta) d) = 0 := by
    rw [← map_incidencePulledRadicand phi a eta d]
    simpa only [aeval_def, eval₂_eq_eval_map, phi] using hetaRoot
  have hLeadingK : incidenceLeadingCoefficient xi ≠ 0 := by
    simpa only [incidenceLeadingCoefficient,
      eval_orderedTraceDiscriminantPolynomial] using hxi.1
  have hLeading :
      incidenceLeadingCoefficient (phi xi) ≠ 0 := by
    have hmap :=
      (map_ne_zero_iff phi phi.injective).mpr hLeadingK
    simpa only [incidenceLeadingCoefficient, map_sub, map_pow,
      map_ofNat] using hmap
  have ht : t ≠ 0 := by
    intro ht
    subst t
    apply hLeading
    simpa only [eval_incidencePulledRadicand_zero
      (MiddleGame.mapCoefficients phi a) (phi xi) hd] using hxiRootMapped
  have hu : t ^ d ≠ 0 := pow_ne_zero d ht
  have hxiQuartic :
      incidenceReciprocalQuartic
        (MiddleGame.mapCoefficients phi a) (phi xi) (t ^ d) = 0 := by
    simpa only [eval_incidencePulledRadicand] using hxiRootMapped
  have hetaQuartic :
      incidenceReciprocalQuartic
        (MiddleGame.mapCoefficients phi a) (phi eta) (t ^ d) = 0 := by
    simpa only [eval_incidencePulledRadicand] using hetaRootMapped
  have hxiIncidence :
      incidenceDiscriminant
        (MiddleGame.mapCoefficients phi a) (phi xi)
        (t ^ d + (t ^ d)⁻¹) = 0 := by
    have hidentity :=
      incidenceReciprocalQuartic_eq_mul_discriminant
        (MiddleGame.mapCoefficients phi a) (phi xi) (t ^ d) hu
    rw [hxiQuartic] at hidentity
    exact (mul_eq_zero.mp hidentity.symm).resolve_left
      (pow_ne_zero 2 hu)
  have hetaIncidence :
      incidenceDiscriminant
        (MiddleGame.mapCoefficients phi a) (phi eta)
        (t ^ d + (t ^ d)⁻¹) = 0 := by
    have hidentity :=
      incidenceReciprocalQuartic_eq_mul_discriminant
        (MiddleGame.mapCoefficients phi a) (phi eta) (t ^ d) hu
    rw [hetaQuartic] at hidentity
    exact (mul_eq_zero.mp hidentity.symm).resolve_left
      (pow_ne_zero 2 hu)
  let middle : AlgebraicClosure K := t ^ d + (t ^ d)⁻¹
  have hxiPolynomial :
      eval middle ((incidenceDiscriminantPolynomial a xi).map phi) = 0 := by
    rw [map_incidenceDiscriminantPolynomial,
      eval_incidenceDiscriminantPolynomial]
    exact hxiIncidence
  have hetaPolynomial :
      eval middle ((incidenceDiscriminantPolynomial a eta).map phi) = 0 := by
    rw [map_incidenceDiscriminantPolynomial,
      eval_incidenceDiscriminantPolynomial]
    exact hetaIncidence
  have hxiDegree :
      ((incidenceDiscriminantPolynomial a xi).map phi).natDegree ≤ 2 := by
    calc
      ((incidenceDiscriminantPolynomial a xi).map phi).natDegree ≤
          (incidenceDiscriminantPolynomial a xi).natDegree :=
        Polynomial.natDegree_map_le
      _ = 2 := incidenceDiscriminantPolynomial_natDegree hxi
  have hetaDegree :
      ((incidenceDiscriminantPolynomial a eta).map phi).natDegree ≤ 2 := by
    calc
      ((incidenceDiscriminantPolynomial a eta).map phi).natDegree ≤
          (incidenceDiscriminantPolynomial a eta).natDegree :=
        Polynomial.natDegree_map_le
      _ = 2 := incidenceDiscriminantPolynomial_natDegree heta
  have hresultantMapped :
      Polynomial.resultant
          ((incidenceDiscriminantPolynomial a xi).map phi)
          ((incidenceDiscriminantPolynomial a eta).map phi) 2 2 = 0 :=
    BGS.CorvajaZannier.resultant_eq_zero_of_common_root
      ((incidenceDiscriminantPolynomial a xi).map phi)
      ((incidenceDiscriminantPolynomial a eta).map phi)
      2 2 hxiDegree hetaDegree (by left; norm_num)
      middle hxiPolynomial hetaPolynomial
  rw [Polynomial.resultant_map_map] at hresultantMapped
  have hresultant :
      incidencePairResultant a xi eta ≠ 0 :=
    hpair.incidenceResultant_ne_zero hA2
  have hresultantImage :
      phi (incidencePairResultant a xi eta) ≠ 0 :=
    (map_ne_zero_iff phi phi.injective).mpr hresultant
  exact hresultantImage hresultantMapped

/-- The two unequal incidence radicands and their product are squarefree. -/
theorem incidencePulledRadicand_squarefree_and_product
    (h2 : (2 : K) ≠ 0)
    {a : Coefficients K} {xi eta : K}
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hpair : IsConnectingIncidencePair a xi eta)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    Squarefree (incidencePulledRadicand a xi d) ∧
      Squarefree (incidencePulledRadicand a eta d) ∧
      Squarefree
        (incidencePulledRadicand a xi d *
          incidencePulledRadicand a eta d) := by
  have hsepXi :=
    incidencePulledRadicand_separable h2 hA2 hxi hd hdegree
  have hsepEta :=
    incidencePulledRadicand_separable h2 hA2 heta hd hdegree
  have hcoprime :=
    incidencePulledRadicand_isCoprime hA2 hxi heta hpair hd
  exact ⟨hsepXi.squarefree, hsepEta.squarefree,
    (hsepXi.mul hsepEta hcoprime).squarefree⟩

/-- The reciprocal quartic obtained from the middle-axis centered norm with
moving coefficient pair `(B,C)`. -/
def centeredNormReciprocalQuartic (B C u : K) : K :=
  u ^ 4 + B * C * u ^ 3 +
    (B ^ 2 + C ^ 2 - 2) * u ^ 2 +
    B * C * u + 1

/-- Pullback of the centered-norm reciprocal quartic along `u = t^d`. -/
def centeredNormPulledRadicand
    (B C0 : K) (d : ℕ) : K[X] :=
  X ^ (4 * d) +
    C (B * C0) * X ^ (3 * d) +
    C (B ^ 2 + C0 ^ 2 - 2) * X ^ (2 * d) +
    C (B * C0) * X ^ d + 1

@[simp]
theorem eval_centeredNormPulledRadicand
    (B C t : K) (d : ℕ) :
    eval t (centeredNormPulledRadicand B C d) =
      centeredNormReciprocalQuartic B C (t ^ d) := by
  simp only [centeredNormPulledRadicand, centeredNormReciprocalQuartic,
    eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one]
  simp only [← pow_mul]
  ring

theorem centeredNormReciprocalQuartic_eq_mul_centeredNorm
    (B C u : K) (hu : u ≠ 0) :
    centeredNormReciprocalQuartic B C u =
      u ^ 2 * centeredNorm B C (u + u⁻¹) := by
  simp only [centeredNormReciprocalQuartic, centeredNorm, discriminant]
  field_simp [hu]
  ring

/-- The two parabolic values expose the possible trace-map ramification
collisions of the connecting-character cover. -/
theorem centeredNorm_neg_two (B C : K) :
    centeredNorm B C (-2) = (B - C) ^ 2 := by
  simp [centeredNorm, discriminant]
  ring

theorem centeredNorm_two (B C : K) :
    centeredNorm B C 2 = (B + C) ^ 2 := by
  simp [centeredNorm, discriminant]
  ring

/-- The residual centered-norm quadratic is separable under the two generic
coefficient hypotheses. -/
theorem orderedTraceCenteredNormPolynomial_separable
    (B C : K)
    (hB : B ^ 2 ≠ 4)
    (hC : C ^ 2 ≠ 4) :
    (orderedTraceCenteredNormPolynomial B C).Separable := by
  rw [separable_def]
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (k := K) (AlgebraicClosure K)
    (orderedTraceCenteredNormPolynomial B C)
    (orderedTraceCenteredNormPolynomial B C).derivative).2
  intro x
  by_contra hcommon
  push Not at hcommon
  rcases hcommon with ⟨hroot, hderivative⟩
  let phi : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  have hroot' :
      x ^ 2 + phi (B * C) * x + phi (B ^ 2 + C ^ 2 - 4) = 0 := by
    simpa only [orderedTraceCenteredNormPolynomial, aeval_def,
      eval₂_eq_eval_map, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_mul, Polynomial.map_C,
      eval_add, eval_pow, eval_X, eval_mul, eval_C] using hroot
  have hderivative' :
      2 * x + phi (B * C) = 0 := by
    have hderivativePolynomial :
        (orderedTraceCenteredNormPolynomial B C).derivative =
          Polynomial.C 2 * X + Polynomial.C (B * C) := by
      rw [orderedTraceCenteredNormPolynomial]
      simp only [derivative_add, derivative_pow, derivative_X,
        derivative_mul, derivative_C, zero_mul, zero_add, mul_one,
        Nat.cast_ofNat]
      norm_num
    rw [hderivativePolynomial] at hderivative
    have htwoEval :
        eval x (2 : Polynomial (AlgebraicClosure K)) = 2 :=
      eval_natCast
    simpa only [aeval_def, eval₂_eq_eval_map, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_ofNat, eval_add, eval_mul, eval_C, eval_X,
      htwoEval, map_ofNat] using hderivative
  have hdiscMap :
      phi ((B * C) ^ 2 - 4 * (B ^ 2 + C ^ 2 - 4)) = 0 := by
    simp only [map_sub, map_add, map_pow, map_mul, map_ofNat] at hroot' hderivative' ⊢
    linear_combination
      (2 * x + phi B * phi C) * hderivative' - 4 * hroot'
  have hfactor :
      (B * C) ^ 2 - 4 * (B ^ 2 + C ^ 2 - 4) =
        (B ^ 2 - 4) * (C ^ 2 - 4) := by
    ring
  have hdisc :
      (B * C) ^ 2 - 4 * (B ^ 2 + C ^ 2 - 4) ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero (sub_ne_zero.mpr hB) (sub_ne_zero.mpr hC)
  exact (map_ne_zero_iff phi phi.injective).mpr hdisc hdiscMap

end

end GenMarkoff.General.Cage
