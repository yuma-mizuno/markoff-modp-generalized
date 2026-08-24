import GenMarkoff.Symmetric.Cage.IncidenceGeometry
import BGS.Markoff.Cage.BiquadraticPrimitiveQuartic
import BGS.CorvajaZannier.BivariateResultant
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Power pullbacks of the symmetric incidence discriminants

Substituting the split-torus trace `u + u⁻¹` into an incidence
discriminant and clearing the denominator gives a palindromic quartic in
`u`.  Pulling `u` back along `t ↦ t^d` produces the polynomial used by the
generalized cage Hasse--Weil argument.
-/

namespace GenMarkoff.Symmetric.Cage

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The middle coefficient of the reciprocal quartic obtained by clearing
the split-trace denominator. -/
def incidencePulledMiddleCoefficient (c xi : K) : K :=
  2 * incidenceLeadingCoefficient xi +
    incidenceConstantCoefficient c xi

/-- The reciprocal quartic `u² Δ_{c,xi}(u+u⁻¹)`. -/
def incidenceReciprocalQuartic (c xi u : K) : K :=
  incidenceLeadingCoefficient xi * u ^ 4 +
    incidenceLinearCoefficient c xi * u ^ 3 +
    incidencePulledMiddleCoefficient c xi * u ^ 2 +
    incidenceLinearCoefficient c xi * u +
    incidenceLeadingCoefficient xi

/-- Formal derivative of the reciprocal quartic, evaluated at `u`. -/
def incidenceReciprocalQuarticDerivative (c xi u : K) : K :=
  4 * incidenceLeadingCoefficient xi * u ^ 3 +
    3 * incidenceLinearCoefficient c xi * u ^ 2 +
    2 * incidencePulledMiddleCoefficient c xi * u +
    incidenceLinearCoefficient c xi

/-- Pullback of the reciprocal quartic along `t ↦ t^d`. -/
def incidencePulledRadicand (c xi : K) (d : ℕ) : K[X] :=
  C (incidenceLeadingCoefficient xi) * X ^ (4 * d) +
    C (incidenceLinearCoefficient c xi) * X ^ (3 * d) +
    C (incidencePulledMiddleCoefficient c xi) * X ^ (2 * d) +
    C (incidenceLinearCoefficient c xi) * X ^ d +
    C (incidenceLeadingCoefficient xi)

@[simp]
theorem eval_incidencePulledRadicand
    (c xi t : K) (d : ℕ) :
    eval t (incidencePulledRadicand c xi d) =
      incidenceReciprocalQuartic c xi (t ^ d) := by
  simp only [incidencePulledRadicand, incidenceReciprocalQuartic,
    eval_add, eval_mul, eval_C, eval_pow, eval_X]
  simp only [← pow_mul]
  ring

theorem incidenceReciprocalQuartic_eq_mul_discriminant
    (c xi u : K) (hu : u ≠ 0) :
    incidenceReciprocalQuartic c xi u =
      u ^ 2 * incidenceDiscriminant c xi (u + u⁻¹) := by
  simp only [incidenceReciprocalQuartic,
    incidencePulledMiddleCoefficient, incidenceLeadingCoefficient,
    incidenceLinearCoefficient, incidenceConstantCoefficient,
    incidenceDiscriminant, traceSurfaceA, traceSurfaceB]
  field_simp [hu]
  ring

theorem incidenceReciprocalQuartic_derivative_identity
    (c xi u : K) (hu : u ≠ 0) :
    u * incidenceReciprocalQuarticDerivative c xi u -
        2 * incidenceReciprocalQuartic c xi u =
      u * (u ^ 2 - 1) *
        (2 * incidenceLeadingCoefficient xi * (u + u⁻¹) +
          incidenceLinearCoefficient c xi) := by
  simp only [incidenceReciprocalQuarticDerivative,
    incidenceReciprocalQuartic, incidencePulledMiddleCoefficient]
  field_simp [hu]
  ring

/-- At the negative parabolic split trace, the incidence discriminant is a
coefficient-only nonzero factor. -/
theorem incidenceDiscriminant_neg_two (c xi : K) :
    incidenceDiscriminant c xi (-2) =
      (c ^ 2 - 4) * (c - 2) ^ 2 := by
  simp only [incidenceDiscriminant, traceSurfaceA, traceSurfaceB]
  ring

/-- At the positive parabolic split trace, the remaining factor is exactly
the nonconstant common-even obstruction from candidate regularity. -/
theorem incidenceDiscriminant_two (c xi : K) :
    incidenceDiscriminant c xi 2 =
      -(c + 2) *
        eval xi (orderedTraceEvenPlusPolynomial c c c) := by
  simp only [incidenceDiscriminant, traceSurfaceA, traceSurfaceB,
    eval_orderedTraceEvenPlusPolynomial]
  ring

/-- Completing the square in the incidence quadratic recovers its scalar
quadratic discriminant. -/
theorem incidenceQuadratic_completion_identity
    (c xi middle : K) :
    (2 * incidenceLeadingCoefficient xi * middle +
        incidenceLinearCoefficient c xi) ^ 2 -
      4 * incidenceLeadingCoefficient xi *
        incidenceDiscriminant c xi middle =
      incidenceQuadraticDiscriminant c xi := by
  simp only [incidenceLeadingCoefficient, incidenceLinearCoefficient,
    incidenceDiscriminant, incidenceQuadraticDiscriminant,
    incidenceConstantCoefficient, traceSurfaceA, traceSurfaceB]
  ring

/-- A field homomorphism commutes with the scalar incidence
discriminant. -/
theorem map_incidenceDiscriminant
    {L : Type*} [Field L] (phi : K →+* L) (c xi middle : K) :
    phi (incidenceDiscriminant c xi middle) =
      incidenceDiscriminant (phi c) (phi xi) (phi middle) := by
  simp only [incidenceDiscriminant, traceSurfaceA, traceSurfaceB,
    map_sub, map_pow, map_mul, map_add, map_ofNat]

/-- A field homomorphism commutes with the scalar discriminant of the
incidence quadratic. -/
theorem map_incidenceQuadraticDiscriminant
    {L : Type*} [Field L] (phi : K →+* L) (c xi : K) :
    phi (incidenceQuadraticDiscriminant c xi) =
      incidenceQuadraticDiscriminant (phi c) (phi xi) := by
  simp only [incidenceQuadraticDiscriminant, incidenceLeadingCoefficient,
    incidenceLinearCoefficient, incidenceConstantCoefficient,
    traceSurfaceA, traceSurfaceB, map_sub, map_pow, map_mul, map_add,
    map_neg, map_ofNat]

/-- A field homomorphism commutes with the incidence discriminant
polynomial. -/
theorem map_incidenceDiscriminantPolynomial
    {L : Type*} [Field L] (phi : K →+* L) (c xi : K) :
    (incidenceDiscriminantPolynomial c xi).map phi =
      incidenceDiscriminantPolynomial (phi c) (phi xi) := by
  have hA : phi (traceSurfaceA c) = traceSurfaceA (phi c) := by
    simp only [traceSurfaceA, map_mul, map_add, map_ofNat]
  have hB : phi (traceSurfaceB c) = traceSurfaceB (phi c) := by
    simp only [traceSurfaceB, map_mul, map_add, map_pow, map_ofNat]
  have hFour : (4 : K[X]).map phi = (4 : L[X]) := by
    exact map_ofNat (Polynomial.mapRingHom phi) 4
  simp only [incidenceDiscriminantPolynomial, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, hA, hB, map_pow, hFour]

/-- Candidate regularity makes the incidence polynomial genuinely
quadratic. -/
theorem incidenceDiscriminantPolynomial_natDegree
    {c xi : K} (hregular : OrderedTraceCandidateRegular c c c xi) :
    (incidenceDiscriminantPolynomial c xi).natDegree = 2 := by
  have hLeading : incidenceLeadingCoefficient xi ≠ 0 := by
    simpa only [incidenceLeadingCoefficient,
      eval_orderedTraceDiscriminantPolynomial] using hregular.1
  rw [incidenceDiscriminantPolynomial_eq_quadratic]
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · compute_degree
  · simp [hLeading]

/-- The two parabolic middle traces are excluded by the coefficient and
candidate-regularity hypotheses. -/
theorem incidenceDiscriminant_neg_two_ne_zero
    {c xi : K} (hc : c ^ 2 ≠ 4) :
    incidenceDiscriminant c xi (-2) ≠ 0 := by
  rw [incidenceDiscriminant_neg_two]
  apply mul_ne_zero (sub_ne_zero.mpr hc)
  apply pow_ne_zero
  intro hcTwo
  apply hc
  rw [sub_eq_zero.mp hcTwo]
  norm_num

theorem incidenceDiscriminant_two_ne_zero
    {c xi : K} (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c xi) :
    incidenceDiscriminant c xi 2 ≠ 0 := by
  rw [incidenceDiscriminant_two]
  apply mul_ne_zero
  · apply neg_ne_zero.mpr
    intro hcNegTwo
    apply hc
    have hc' : c = -2 := by linear_combination hcNegTwo
    rw [hc']
    norm_num
  · exact hregular.2.2.2.2.2

theorem mul_eval_derivative_incidencePulledRadicand
    (c xi t : K) (d : ℕ) (hd : 0 < d) :
    t * eval t (incidencePulledRadicand c xi d).derivative =
      (d : K) * t ^ d *
        incidenceReciprocalQuarticDerivative c xi (t ^ d) := by
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
          incidenceLinearCoefficient c xi * ((3 * d : ℕ) : K) *
              (t * t ^ (3 * d - 1)) +
          incidencePulledMiddleCoefficient c xi * ((2 * d : ℕ) : K) *
              (t * t ^ (2 * d - 1)) +
          incidenceLinearCoefficient c xi * (d : K) *
              (t * t ^ (d - 1)) := by ring
    _ =
        incidenceLeadingCoefficient xi * ((4 * d : ℕ) : K) * t ^ (4 * d) +
          incidenceLinearCoefficient c xi * ((3 * d : ℕ) : K) * t ^ (3 * d) +
          incidencePulledMiddleCoefficient c xi * ((2 * d : ℕ) : K) *
            t ^ (2 * d) +
          incidenceLinearCoefficient c xi * (d : K) * t ^ d := by
      rw [hpow (4 * d) (by omega), hpow (3 * d) (by omega),
        hpow (2 * d) (by omega), hpow d hd]
    _ = (d : K) * t ^ d *
        incidenceReciprocalQuarticDerivative c xi (t ^ d) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat,
        incidenceReciprocalQuarticDerivative]
      rw [show 4 * d = d * 4 by omega, show 3 * d = d * 3 by omega,
        show 2 * d = d * 2 by omega]
      simp only [pow_mul]
      ring

@[simp]
theorem eval_incidencePulledRadicand_zero
    (c xi : K) {d : ℕ} (hd : 0 < d) :
    eval 0 (incidencePulledRadicand c xi d) =
      incidenceLeadingCoefficient xi := by
  simp [incidencePulledRadicand, Nat.ne_of_gt hd]

theorem map_incidencePulledRadicand
    {L : Type*} [Field L] (phi : K →+* L)
    (c xi : K) (d : ℕ) :
    (incidencePulledRadicand c xi d).map phi =
      incidencePulledRadicand (phi c) (phi xi) d := by
  have hLeading :
      phi (incidenceLeadingCoefficient xi) =
        incidenceLeadingCoefficient (phi xi) := by
    simp only [incidenceLeadingCoefficient, map_sub, map_pow, map_ofNat]
  have hLinear :
      phi (incidenceLinearCoefficient c xi) =
        incidenceLinearCoefficient (phi c) (phi xi) := by
    simp only [incidenceLinearCoefficient, traceSurfaceA, map_neg,
      map_mul, map_add, map_ofNat]
  have hMiddle :
      phi (incidencePulledMiddleCoefficient c xi) =
        incidencePulledMiddleCoefficient (phi c) (phi xi) := by
    simp only [incidencePulledMiddleCoefficient, incidenceLeadingCoefficient,
      incidenceConstantCoefficient, traceSurfaceA, traceSurfaceB,
      map_add, map_sub, map_mul, map_pow, map_ofNat]
  simp only [incidencePulledRadicand, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, hLeading, hLinear, hMiddle]

/-- The power-pulled incidence radicand has no repeated geometric root.

The proof isolates the only new issue introduced by the power map:
a repeated root would either lie over the parabolic traces `±2`, or give a
repeated root of the original incidence quadratic.  Candidate regularity
excludes all three alternatives. -/
theorem incidencePulledRadicand_separable
    (h2 : (2 : K) ≠ 0) {c xi : K} (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c xi)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    (incidencePulledRadicand c xi d).Separable := by
  rw [separable_def]
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (k := K) (AlgebraicClosure K) (incidencePulledRadicand c xi d)
      (incidencePulledRadicand c xi d).derivative).2
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
      eval t (incidencePulledRadicand (phi c) (phi xi) d) = 0 := by
    rw [← map_incidencePulledRadicand phi c xi d]
    simpa only [aeval_def, eval₂_eq_eval_map, phi] using hroot
  have hderivativeMapped :
      eval t (incidencePulledRadicand (phi c) (phi xi) d).derivative = 0 := by
    rw [← map_incidencePulledRadicand phi c xi d,
      derivative_map]
    simpa only [aeval_def, eval₂_eq_eval_map, phi] using hderivative
  have ht : t ≠ 0 := by
    intro ht
    subst t
    apply hLeading
    simpa only [eval_incidencePulledRadicand_zero (phi c) (phi xi) hd]
      using hrootMapped
  have hu : t ^ d ≠ 0 := pow_ne_zero d ht
  have hquartic :
      incidenceReciprocalQuartic (phi c) (phi xi) (t ^ d) = 0 := by
    simpa only [eval_incidencePulledRadicand] using hrootMapped
  have hincidence :
      incidenceDiscriminant (phi c) (phi xi)
        (t ^ d + (t ^ d)⁻¹) = 0 := by
    have hidentity :=
      incidenceReciprocalQuartic_eq_mul_discriminant
        (phi c) (phi xi) (t ^ d) hu
    rw [hquartic] at hidentity
    exact (mul_eq_zero.mp hidentity.symm).resolve_left
      (pow_ne_zero 2 hu)
  have hquarticDerivative :
      incidenceReciprocalQuarticDerivative
        (phi c) (phi xi) (t ^ d) = 0 := by
    have hchain :=
      mul_eval_derivative_incidencePulledRadicand
        (phi c) (phi xi) t d hd
    rw [hderivativeMapped, mul_zero] at hchain
    exact (mul_eq_zero.mp hchain.symm).resolve_left
      (mul_ne_zero hDegree hu)
  have hcritical :
      (t ^ d) ^ 2 - 1 = 0 ∨
        2 * incidenceLeadingCoefficient (phi xi) *
              (t ^ d + (t ^ d)⁻¹) +
            incidenceLinearCoefficient (phi c) (phi xi) = 0 := by
    have hidentity :=
      incidenceReciprocalQuartic_derivative_identity
        (phi c) (phi xi) (t ^ d) hu
    rw [hquarticDerivative, hquartic] at hidentity
    have hproductFull :
        t ^ d *
          (((t ^ d) ^ 2 - 1) *
            (2 * incidenceLeadingCoefficient (phi xi) *
                  (t ^ d + (t ^ d)⁻¹) +
                incidenceLinearCoefficient (phi c) (phi xi))) = 0 := by
      calc
        t ^ d *
            (((t ^ d) ^ 2 - 1) *
              (2 * incidenceLeadingCoefficient (phi xi) *
                    (t ^ d + (t ^ d)⁻¹) +
                  incidenceLinearCoefficient (phi c) (phi xi))) =
            t ^ d * ((t ^ d) ^ 2 - 1) *
              (2 * incidenceLeadingCoefficient (phi xi) *
                    (t ^ d + (t ^ d)⁻¹) +
                  incidenceLinearCoefficient (phi c) (phi xi)) := by ring
        _ = t ^ d * 0 - 2 * 0 := hidentity.symm
        _ = 0 := by ring
    have hproduct :
        ((t ^ d) ^ 2 - 1) *
          (2 * incidenceLeadingCoefficient (phi xi) *
                (t ^ d + (t ^ d)⁻¹) +
              incidenceLinearCoefficient (phi c) (phi xi)) = 0 := by
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
          (1 : AlgebraicClosure K) + (1 : AlgebraicClosure K)⁻¹ = 2 := by
        norm_num
      have hzero :
          incidenceDiscriminant (phi c) (phi xi) 2 = 0 := by
        rw [huOne, hmiddleOne] at hincidence
        exact hincidence
      have hnonzeroK :=
        incidenceDiscriminant_two_ne_zero hc hregular
      have hnonzeroMap :=
        (map_ne_zero_iff phi phi.injective).mpr hnonzeroK
      have hnonzero :
          incidenceDiscriminant (phi c) (phi xi) 2 ≠ 0 := by
        simpa only [map_incidenceDiscriminant, map_ofNat] using hnonzeroMap
      exact hnonzero hzero
    · have huNegOne : t ^ d = -1 := by
        linear_combination hnegOne
      have hmiddleNegOne :
          (-1 : AlgebraicClosure K) +
              (-1 : AlgebraicClosure K)⁻¹ = -2 := by
        norm_num
      have hzero :
          incidenceDiscriminant (phi c) (phi xi) (-2) = 0 := by
        rw [huNegOne, hmiddleNegOne] at hincidence
        exact hincidence
      have hnonzeroK :=
        incidenceDiscriminant_neg_two_ne_zero (xi := xi) hc
      have hnonzeroMap :=
        (map_ne_zero_iff phi phi.injective).mpr hnonzeroK
      have hnonzero :
          incidenceDiscriminant (phi c) (phi xi) (-2) ≠ 0 := by
        simpa only [map_incidenceDiscriminant, map_neg, map_ofNat]
          using hnonzeroMap
      exact hnonzero hzero
  · have hcompletion :=
      incidenceQuadratic_completion_identity
        (phi c) (phi xi) (t ^ d + (t ^ d)⁻¹)
    rw [hlinear, hincidence] at hcompletion
    have hdiscriminantZero :
        incidenceQuadraticDiscriminant (phi c) (phi xi) = 0 := by
      simpa using hcompletion.symm
    have hdiscriminantK :=
      incidenceQuadraticDiscriminant_ne_zero_of_candidateRegular
        c xi h2 hregular
    have hdiscriminantMap :=
      (map_ne_zero_iff phi phi.injective).mpr hdiscriminantK
    have hdiscriminant :
        incidenceQuadraticDiscriminant (phi c) (phi xi) ≠ 0 := by
      simpa only [map_incidenceQuadraticDiscriminant]
        using hdiscriminantMap
    exact hdiscriminant hdiscriminantZero

/-- The leading coefficient survives at degree `4d`. -/
theorem incidencePulledRadicand_coeff_four_mul
    (c xi : K) {d : ℕ} (hd : 0 < d) :
    (incidencePulledRadicand c xi d).coeff (4 * d) =
      incidenceLeadingCoefficient xi := by
  rw [incidencePulledRadicand]
  rw [coeff_add, coeff_add, coeff_add, coeff_add,
    coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
    coeff_C_mul_X_pow, coeff_C]
  simp only [if_true, if_neg (show 4 * d ≠ 3 * d by omega),
    if_neg (show 4 * d ≠ 2 * d by omega),
    if_neg (show 4 * d ≠ d by omega),
    if_neg (show 4 * d ≠ 0 by omega), add_zero]

/-- A nonparabolic pulled radicand is not a polynomial unit. -/
theorem incidencePulledRadicand_not_isUnit
    {c xi : K} (hregular : OrderedTraceCandidateRegular c c c xi)
    {d : ℕ} (hd : 0 < d) :
    ¬ IsUnit (incidencePulledRadicand c xi d) := by
  apply not_isUnit_of_natDegree_pos
  have hLeading : incidenceLeadingCoefficient xi ≠ 0 := by
    simpa only [incidenceLeadingCoefficient,
      eval_orderedTraceDiscriminantPolynomial] using hregular.1
  have hcoeff :
      (incidencePulledRadicand c xi d).coeff (4 * d) ≠ 0 := by
    simpa only [incidencePulledRadicand_coeff_four_mul c xi hd]
      using hLeading
  have hle := Polynomial.le_natDegree_of_ne_zero hcoeff
  omega

/-- Off the diagonal obstruction locus, two pulled incidence radicands have
disjoint geometric zero sets. -/
theorem incidencePulledRadicand_isCoprime
    {c xi eta : K} (hc : c ^ 2 ≠ 4)
    (hxi : OrderedTraceCandidateRegular c c c xi)
    (heta : OrderedTraceCandidateRegular c c c eta)
    (hpair : IsHasseWeilReadyIncidencePair c xi eta)
    {d : ℕ} (hd : 0 < d) :
    IsCoprime (incidencePulledRadicand c xi d)
      (incidencePulledRadicand c eta d) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (k := K) (AlgebraicClosure K)
      (incidencePulledRadicand c xi d)
      (incidencePulledRadicand c eta d)).2
  intro t
  let phi : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  by_contra hcommon
  push Not at hcommon
  rcases hcommon with ⟨hxiRoot, hetaRoot⟩
  have hxiRootMapped :
      eval t (incidencePulledRadicand (phi c) (phi xi) d) = 0 := by
    rw [← map_incidencePulledRadicand phi c xi d]
    simpa only [aeval_def, eval₂_eq_eval_map, phi] using hxiRoot
  have hetaRootMapped :
      eval t (incidencePulledRadicand (phi c) (phi eta) d) = 0 := by
    rw [← map_incidencePulledRadicand phi c eta d]
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
    simpa only [eval_incidencePulledRadicand_zero (phi c) (phi xi) hd]
      using hxiRootMapped
  have hu : t ^ d ≠ 0 := pow_ne_zero d ht
  have hxiQuartic :
      incidenceReciprocalQuartic (phi c) (phi xi) (t ^ d) = 0 := by
    simpa only [eval_incidencePulledRadicand] using hxiRootMapped
  have hetaQuartic :
      incidenceReciprocalQuartic (phi c) (phi eta) (t ^ d) = 0 := by
    simpa only [eval_incidencePulledRadicand] using hetaRootMapped
  have hxiIncidence :
      incidenceDiscriminant (phi c) (phi xi)
        (t ^ d + (t ^ d)⁻¹) = 0 := by
    have hidentity :=
      incidenceReciprocalQuartic_eq_mul_discriminant
        (phi c) (phi xi) (t ^ d) hu
    rw [hxiQuartic] at hidentity
    exact (mul_eq_zero.mp hidentity.symm).resolve_left
      (pow_ne_zero 2 hu)
  have hetaIncidence :
      incidenceDiscriminant (phi c) (phi eta)
        (t ^ d + (t ^ d)⁻¹) = 0 := by
    have hidentity :=
      incidenceReciprocalQuartic_eq_mul_discriminant
        (phi c) (phi eta) (t ^ d) hu
    rw [hetaQuartic] at hidentity
    exact (mul_eq_zero.mp hidentity.symm).resolve_left
      (pow_ne_zero 2 hu)
  let middle : AlgebraicClosure K := t ^ d + (t ^ d)⁻¹
  have hxiPolynomial :
      eval middle ((incidenceDiscriminantPolynomial c xi).map phi) = 0 := by
    rw [map_incidenceDiscriminantPolynomial,
      eval_incidenceDiscriminantPolynomial]
    exact hxiIncidence
  have hetaPolynomial :
      eval middle ((incidenceDiscriminantPolynomial c eta).map phi) = 0 := by
    rw [map_incidenceDiscriminantPolynomial,
      eval_incidenceDiscriminantPolynomial]
    exact hetaIncidence
  have hxiDegree :
      ((incidenceDiscriminantPolynomial c xi).map phi).natDegree ≤ 2 := by
    calc
      ((incidenceDiscriminantPolynomial c xi).map phi).natDegree ≤
          (incidenceDiscriminantPolynomial c xi).natDegree :=
        Polynomial.natDegree_map_le
      _ = 2 := incidenceDiscriminantPolynomial_natDegree hxi
  have hetaDegree :
      ((incidenceDiscriminantPolynomial c eta).map phi).natDegree ≤ 2 := by
    calc
      ((incidenceDiscriminantPolynomial c eta).map phi).natDegree ≤
          (incidenceDiscriminantPolynomial c eta).natDegree :=
        Polynomial.natDegree_map_le
      _ = 2 := incidenceDiscriminantPolynomial_natDegree heta
  have hresultantMapped :
      Polynomial.resultant
          ((incidenceDiscriminantPolynomial c xi).map phi)
          ((incidenceDiscriminantPolynomial c eta).map phi) 2 2 = 0 :=
    BGS.CorvajaZannier.resultant_eq_zero_of_common_root
      ((incidenceDiscriminantPolynomial c xi).map phi)
      ((incidenceDiscriminantPolynomial c eta).map phi)
      2 2 hxiDegree hetaDegree (by left; norm_num)
      middle hxiPolynomial hetaPolynomial
  rw [Polynomial.resultant_map_map] at hresultantMapped
  have hresultant :
      incidencePairResultant c xi eta ≠ 0 :=
    hpair.resultant_ne_zero hc
  have hresultantImage :
      phi (incidencePairResultant c xi eta) ≠ 0 :=
    (map_ne_zero_iff phi phi.injective).mpr hresultant
  exact hresultantImage hresultantMapped

/-- The two admissible off-diagonal radicands, and their product, are
squarefree. -/
theorem incidencePulledRadicand_squarefree_and_product
    (h2 : (2 : K) ≠ 0) {c xi eta : K} (hc : c ^ 2 ≠ 4)
    (hxi : OrderedTraceCandidateRegular c c c xi)
    (heta : OrderedTraceCandidateRegular c c c eta)
    (hpair : IsHasseWeilReadyIncidencePair c xi eta)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    Squarefree (incidencePulledRadicand c xi d) ∧
      Squarefree (incidencePulledRadicand c eta d) ∧
      Squarefree
        (incidencePulledRadicand c xi d *
          incidencePulledRadicand c eta d) := by
  have hsepXi :=
    incidencePulledRadicand_separable h2 hc hxi hd hdegree
  have hsepEta :=
    incidencePulledRadicand_separable h2 hc heta hd hdegree
  have hcoprime :=
    incidencePulledRadicand_isCoprime hc hxi heta hpair hd
  exact ⟨hsepXi.squarefree, hsepEta.squarefree,
    (hsepXi.mul hsepEta hcoprime).squarefree⟩

/-- The admissible off-diagonal pulled radicands define independent
quadratic square classes in the rational function field. -/
theorem incidencePulledRadicand_squareClasses_independent_ratFunc
    (h2 : (2 : K) ≠ 0) {c xi eta : K} (hc : c ^ 2 ≠ 4)
    (hxi : OrderedTraceCandidateRegular c c c xi)
    (heta : OrderedTraceCandidateRegular c c c eta)
    (hpair : IsHasseWeilReadyIncidencePair c xi eta)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    ¬ IsSquare
        (algebraMap K[X] (RatFunc K)
          (incidencePulledRadicand c xi d)) ∧
      ¬ IsSquare
        (algebraMap K[X] (RatFunc K)
          (incidencePulledRadicand c eta d)) ∧
      ¬ IsSquare
        (algebraMap K[X] (RatFunc K)
          (incidencePulledRadicand c xi d *
            incidencePulledRadicand c eta d)) := by
  obtain ⟨hsqXi, hsqEta, hsqProduct⟩ :=
    incidencePulledRadicand_squarefree_and_product
      h2 hc hxi heta hpair hd hdegree
  exact
    ⟨BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        hsqXi (incidencePulledRadicand_not_isUnit hxi hd),
      BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        hsqEta (incidencePulledRadicand_not_isUnit heta hd),
      BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        hsqProduct (by
          intro hunit
          exact incidencePulledRadicand_not_isUnit hxi hd
            (IsUnit.mul_iff.mp hunit).1)⟩

/-- The primitive quartic of the two pulled square roots is irreducible over
the rational function field.  This is the exact algebraic boundary used by
the off-diagonal affine-plane model. -/
theorem incidenceBiquadraticPrimitiveQuartic_irreducible_ratFunc
    (h2 : (2 : K) ≠ 0) {c xi eta : K} (hc : c ^ 2 ≠ 4)
    (hxi : OrderedTraceCandidateRegular c c c xi)
    (heta : OrderedTraceCandidateRegular c c c eta)
    (hpair : IsHasseWeilReadyIncidencePair c xi eta)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    Irreducible
      (BGS.Markoff.biquadraticPrimitiveQuartic
        (algebraMap K[X] (RatFunc K)
          (incidencePulledRadicand c xi d))
        (algebraMap K[X] (RatFunc K)
          (incidencePulledRadicand c eta d))) := by
  obtain ⟨hxiSquare, hetaSquare, hproductSquare⟩ :=
    incidencePulledRadicand_squareClasses_independent_ratFunc
      h2 hc hxi heta hpair hd hdegree
  have h2RatFunc : (2 : RatFunc K) ≠ 0 := by
    let phi : K →+* RatFunc K := algebraMap K (RatFunc K)
    have hmap := (map_ne_zero_iff phi phi.injective).mpr h2
    simpa only [map_ofNat] using hmap
  apply BGS.Markoff.biquadraticPrimitiveQuartic_irreducible
    h2RatFunc hxiSquare hetaSquare
  simpa only [map_mul] using hproductSquare

end

end GenMarkoff.Symmetric.Cage
