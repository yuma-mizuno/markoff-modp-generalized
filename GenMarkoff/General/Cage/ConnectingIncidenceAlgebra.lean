import GenMarkoff.General.Cage.IncidenceAlgebra

/-!
# Incidence versus connecting-fiber branch loci

For a fixed first-axis trace `xi`, the incidence discriminant is a quadratic
in the shared second-axis trace.  Requiring that second-axis fiber to be
connecting introduces the centered-norm quadratic

`orderedTraceCenteredNormPolynomial a.a3 a.a1`.

The two quadratic covers are independent away from the roots of one explicit
quadratic in `xi`.  This is an additional obstruction beyond the pair
resultant in `IncidenceAlgebra`: that older resultant separates two incidence
covers, whereas the resultant here separates one incidence cover from the
connecting-character cover.
-/

namespace GenMarkoff.General.Cage

open Polynomial

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- The remaining factor in the resultant of a first-to-second incidence
quadratic and the centered-norm quadratic for the second axis. -/
def incidenceCenteredNormObstruction
    (a : Coefficients K) (xi : K) : K :=
  (a.a3 ^ 2 - a.a1 ^ 2) * xi ^ 2 +
    ((4 - a.a1 ^ 2) * a.a2 * a.a3 +
      2 * a.a1 * (a.a3 ^ 2 - 4)) * xi +
    (4 - a.a1 ^ 2) * a.a2 ^ 2 +
      4 * (a.a3 ^ 2 - 4)

/-- The incidence/centered-norm obstruction as a polynomial in the fixed
outer trace. -/
def incidenceCenteredNormObstructionPolynomial
    (a : Coefficients K) : K[X] :=
  C (a.a3 ^ 2 - a.a1 ^ 2) * X ^ 2 +
    C ((4 - a.a1 ^ 2) * a.a2 * a.a3 +
      2 * a.a1 * (a.a3 ^ 2 - 4)) * X +
    C ((4 - a.a1 ^ 2) * a.a2 ^ 2 +
      4 * (a.a3 ^ 2 - 4))

@[simp]
theorem eval_incidenceCenteredNormObstructionPolynomial
    (a : Coefficients K) (xi : K) :
    eval xi (incidenceCenteredNormObstructionPolynomial a) =
      incidenceCenteredNormObstruction a xi := by
  simp [incidenceCenteredNormObstructionPolynomial,
    incidenceCenteredNormObstruction]
  ring

set_option maxHeartbeats 800000 in
/-- Exact factorization of the formal-degree-two resultant.  Its square form
is useful because nonvanishing of the displayed obstruction is precisely the
independence condition for the two quadratic branch loci. -/
theorem resultant_incidenceDiscriminant_centeredNorm_factor
    (a : Coefficients K) (xi : K) :
    Polynomial.resultant
        (incidenceDiscriminantPolynomial a xi)
        (orderedTraceCenteredNormPolynomial a.a3 a.a1) 2 2 =
      incidenceCenteredNormObstruction a xi ^ 2 := by
  have hcenter :
      orderedTraceCenteredNormPolynomial a.a3 a.a1 =
        C (1 : K) * X ^ 2 + C (a.a3 * a.a1) * X +
          C (a.a3 ^ 2 + a.a1 ^ 2 - 4) := by
    rw [orderedTraceCenteredNormPolynomial]
    simp
  rw [incidenceDiscriminantPolynomial_eq_quadratic, hcenter,
    GenMarkoff.Cage.resultant_quadratic_quadratic]
  simp only [incidenceLeadingCoefficient, incidenceLinearCoefficient,
    incidenceConstantCoefficient, traceLinearCoefficient1,
    traceLinearCoefficient2, traceLinearCoefficient3, traceConstant,
    incidenceCenteredNormObstruction]
  set_option maxRecDepth 100000 in
    ring_nf

@[simp]
theorem coeff_two_incidenceCenteredNormObstructionPolynomial
    (a : Coefficients K) :
    (incidenceCenteredNormObstructionPolynomial a).coeff 2 =
      a.a3 ^ 2 - a.a1 ^ 2 := by
  rw [incidenceCenteredNormObstructionPolynomial]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num

@[simp]
theorem coeff_zero_incidenceCenteredNormObstructionPolynomial
    (a : Coefficients K) :
    (incidenceCenteredNormObstructionPolynomial a).coeff 0 =
      (4 - a.a1 ^ 2) * a.a2 ^ 2 +
        4 * (a.a3 ^ 2 - 4) := by
  rw [incidenceCenteredNormObstructionPolynomial]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num

/-- Generic coefficient admissibility prevents the obstruction polynomial
from vanishing identically.  If its quadratic coefficient vanishes, its
constant coefficient becomes
`(4 - a.a1^2) * (a.a2^2 - 4)`. -/
theorem incidenceCenteredNormObstructionPolynomial_ne_zero
    (a : Coefficients K)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4) :
    incidenceCenteredNormObstructionPolynomial a ≠ 0 := by
  intro hzero
  have htwo := congrArg (fun f : K[X] => f.coeff 2) hzero
  simp only [coeff_two_incidenceCenteredNormObstructionPolynomial,
    coeff_zero] at htwo
  have h31 : a.a3 ^ 2 = a.a1 ^ 2 := sub_eq_zero.mp htwo
  have hzeroCoeff := congrArg (fun f : K[X] => f.coeff 0) hzero
  simp only [coeff_zero_incidenceCenteredNormObstructionPolynomial,
    coeff_zero] at hzeroCoeff
  rw [h31] at hzeroCoeff
  have hfactor :
      (4 - a.a1 ^ 2) * a.a2 ^ 2 +
          4 * (a.a1 ^ 2 - 4) =
        (4 - a.a1 ^ 2) * (a.a2 ^ 2 - 4) := by
    ring
  rw [hfactor] at hzeroCoeff
  exact
    (mul_ne_zero
      (sub_ne_zero.mpr hA1.symm)
      (sub_ne_zero.mpr hA2)) hzeroCoeff

theorem incidenceCenteredNormObstructionPolynomial_natDegree_le
    (a : Coefficients K) :
    (incidenceCenteredNormObstructionPolynomial a).natDegree ≤ 2 := by
  simp only [incidenceCenteredNormObstructionPolynomial]
  compute_degree

/-- At most two outer traces make the incidence and connecting-character
quadratics share a branch point. -/
theorem incidenceCenteredNormObstructionPolynomial_roots_card_le_two
    (a : Coefficients K) [DecidableEq K] :
    (incidenceCenteredNormObstructionPolynomial a).roots.toFinset.card ≤ 2 := by
  calc
    (incidenceCenteredNormObstructionPolynomial a).roots.toFinset.card ≤
        (incidenceCenteredNormObstructionPolynomial a).roots.card :=
      Multiset.toFinset_card_le _
    _ ≤ (incidenceCenteredNormObstructionPolynomial a).natDegree :=
      Polynomial.card_roots' _
    _ ≤ 2 :=
      incidenceCenteredNormObstructionPolynomial_natDegree_le a

/-- The finite set of outer traces where the incidence and connecting
centered-norm covers have a common branch point. -/
def incidenceCenteredNormObstructionBadTraces
    (a : Coefficients K) : Finset K := by
  classical
  exact (incidenceCenteredNormObstructionPolynomial a).roots.toFinset

theorem mem_incidenceCenteredNormObstructionBadTraces_iff
    (a : Coefficients K) (xi : K)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4) :
    xi ∈ incidenceCenteredNormObstructionBadTraces a ↔
      incidenceCenteredNormObstruction a xi = 0 := by
  classical
  rw [incidenceCenteredNormObstructionBadTraces, Multiset.mem_toFinset,
    Polynomial.mem_roots
      (incidenceCenteredNormObstructionPolynomial_ne_zero a hA1 hA2),
    Polynomial.IsRoot.def,
    eval_incidenceCenteredNormObstructionPolynomial]

theorem incidenceCenteredNormObstructionBadTraces_card_le_two
    (a : Coefficients K) :
    (incidenceCenteredNormObstructionBadTraces a).card ≤ 2 := by
  classical
  exact incidenceCenteredNormObstructionPolynomial_roots_card_le_two a

/-- Away from the explicit two-root locus, the incidence quadratic and the
middle-axis centered-norm quadratic have nonzero formal resultant. -/
theorem resultant_incidenceDiscriminant_centeredNorm_ne_zero
    (a : Coefficients K) (xi : K)
    (hobstruction : incidenceCenteredNormObstruction a xi ≠ 0) :
    Polynomial.resultant
        (incidenceDiscriminantPolynomial a xi)
        (orderedTraceCenteredNormPolynomial a.a3 a.a1) 2 2 ≠ 0 := by
  rw [resultant_incidenceDiscriminant_centeredNorm_factor]
  exact pow_ne_zero 2 hobstruction

/-- The three branch-separation conditions needed by the connecting cage:
the two incidence covers are distinct, and neither one shares a branch point
with the middle-axis centered-norm cover. -/
def IsConnectingIncidencePair
    (a : Coefficients K) (xi eta : K) : Prop :=
  IsOffDiagonalObstructionRegularIncidencePair a xi eta ∧
    incidenceCenteredNormObstruction a xi ≠ 0 ∧
    incidenceCenteredNormObstruction a eta ≠ 0

theorem IsConnectingIncidencePair.incidenceResultant_ne_zero
    {a : Coefficients K} {xi eta : K}
    (h : IsConnectingIncidencePair a xi eta)
    (hA2 : a.a2 ^ 2 ≠ 4) :
    incidencePairResultant a xi eta ≠ 0 :=
  h.1.resultant_ne_zero hA2

theorem IsConnectingIncidencePair.firstCenteredNormResultant_ne_zero
    {a : Coefficients K} {xi eta : K}
    (h : IsConnectingIncidencePair a xi eta) :
    Polynomial.resultant
        (incidenceDiscriminantPolynomial a xi)
        (orderedTraceCenteredNormPolynomial a.a3 a.a1) 2 2 ≠ 0 :=
  resultant_incidenceDiscriminant_centeredNorm_ne_zero a xi h.2.1

theorem IsConnectingIncidencePair.secondCenteredNormResultant_ne_zero
    {a : Coefficients K} {xi eta : K}
    (h : IsConnectingIncidencePair a xi eta) :
    Polynomial.resultant
        (incidenceDiscriminantPolynomial a eta)
        (orderedTraceCenteredNormPolynomial a.a3 a.a1) 2 2 ≠ 0 :=
  resultant_incidenceDiscriminant_centeredNorm_ne_zero a eta h.2.2

end

end GenMarkoff.General.Cage
