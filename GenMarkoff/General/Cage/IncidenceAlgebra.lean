import GenMarkoff.Cage.QuadraticResultant
import GenMarkoff.General.Cage.IncidenceGeometry

/-!
# Pair resultants for the unequal incidence quadratics

For fixed first-axis traces `xi` and `eta`, the two incidence discriminants
are quadratics in their shared second-axis trace.  Their formal resultant
factors as

`(a₂² - 4) * (eta - xi)² * incidencePairObstruction a xi eta`.

The remaining obstruction is symmetric of bidegree at most `(2,2)`.  A key
new fact is that, when it is viewed as a polynomial in `eta`, its leading
coefficient is exactly

`orderedTraceEvenMinus(a₁,a₂,a₃,xi) *
 orderedTraceEvenPlus(a₁,a₂,a₃,xi)`.

Thus the already established ordered candidate-regularity of `xi` makes
this obstruction a nonzero quadratic.  At most two prospective outer traces
are therefore excluded by obstruction degeneracy.  The additional diagonal
factor `(eta - xi)²` is kept separate and is handled explicitly by the relay
lemmas.  This is the coefficient-ordered replacement for the symmetric
two-bad-label lemma.

No parity-sensitive incidence point count is asserted here.
-/

namespace GenMarkoff.General.Cage

open Polynomial

universe u

noncomputable section

variable {K : Type u} [Field K]

private def pairObstructionCoefficientZero
    (a : Coefficients K) : K :=
  16 * a.a1 ^ 2 *
    (-a.a1 ^ 2 * a.a2 ^ 2 +
      4 * a.a2 ^ 2 + 4 * a.a3 ^ 2 - 16)

private def pairObstructionCoefficientSum
    (a : Coefficients K) : K :=
  8 * a.a1 *
    (-a.a1 ^ 3 * a.a2 * a.a3 -
      2 * a.a1 ^ 2 * a.a2 ^ 2 +
      2 * a.a1 ^ 2 * a.a3 ^ 2 +
      4 * a.a1 * a.a2 * a.a3 -
      8 * a.a1 ^ 2 + 8 * a.a2 ^ 2 +
      8 * a.a3 ^ 2 - 32)

private def pairObstructionCoefficientSumSq
    (a : Coefficients K) : K :=
  (-a.a1 ^ 2 * a.a2 - 2 * a.a1 ^ 2 +
      4 * a.a1 * a.a3 + 4 * a.a2 - 8) *
    (-a.a1 ^ 2 * a.a2 + 2 * a.a1 ^ 2 +
      4 * a.a1 * a.a3 + 4 * a.a2 + 8)

private def pairObstructionCoefficientProduct
    (a : Coefficients K) : K :=
  4 *
    (-a.a1 ^ 4 * a.a2 ^ 2 +
      4 * a.a1 ^ 2 * a.a2 ^ 2 +
      4 * a.a1 ^ 2 * a.a3 ^ 2 -
      32 * a.a1 ^ 2 + 16 * a.a3 ^ 2)

private def pairObstructionCoefficientProductSum
    (a : Coefficients K) : K :=
  8 *
    (-a.a1 ^ 2 * a.a2 * a.a3 -
      2 * a.a1 ^ 3 + 4 * a.a1 * a.a3 ^ 2 +
      4 * a.a2 * a.a3 - 8 * a.a1)

private def pairObstructionCoefficientProductSq
    (a : Coefficients K) : K :=
  -16 * (a.a1 - a.a3) * (a.a1 + a.a3)

/-- The off-diagonal obstruction remaining after removing the middle
coefficient and diagonal factors from the pair resultant. -/
def incidencePairObstruction
    (a : Coefficients K) (xi eta : K) : K :=
  let s := xi + eta
  let r := xi * eta
  pairObstructionCoefficientZero a +
    pairObstructionCoefficientSum a * s +
    pairObstructionCoefficientSumSq a * s ^ 2 +
    pairObstructionCoefficientProduct a * r +
    pairObstructionCoefficientProductSum a * r * s +
    pairObstructionCoefficientProductSq a * r ^ 2

/-- The pair obstruction is symmetric in its two trace arguments. -/
theorem incidencePairObstruction_comm
    (a : Coefficients K) (xi eta : K) :
    incidencePairObstruction a xi eta =
      incidencePairObstruction a eta xi := by
  simp only [incidencePairObstruction]
  ring

/-- The obstruction as a polynomial in the second outer trace. -/
def incidencePairObstructionPolynomial
    (a : Coefficients K) (xi : K) : K[X] :=
  C (pairObstructionCoefficientZero a +
      pairObstructionCoefficientSum a * xi +
      pairObstructionCoefficientSumSq a * xi ^ 2) +
    C (pairObstructionCoefficientSum a +
        2 * pairObstructionCoefficientSumSq a * xi +
        pairObstructionCoefficientProduct a * xi +
        pairObstructionCoefficientProductSum a * xi ^ 2) * X +
    C (pairObstructionCoefficientSumSq a +
        pairObstructionCoefficientProductSum a * xi +
        pairObstructionCoefficientProductSq a * xi ^ 2) * X ^ 2

@[simp]
theorem eval_incidencePairObstructionPolynomial
    (a : Coefficients K) (xi eta : K) :
    eval eta (incidencePairObstructionPolynomial a xi) =
      incidencePairObstruction a xi eta := by
  simp [incidencePairObstructionPolynomial, incidencePairObstruction]
  ring

/-- The formal-degree-two resultant of the two incidence quadratics. -/
def incidencePairResultant
    (a : Coefficients K) (xi eta : K) : K :=
  Polynomial.resultant
    (incidenceDiscriminantPolynomial a xi)
    (incidenceDiscriminantPolynomial a eta) 2 2

/-- Exact factorization of the unequal pair resultant. -/
theorem incidencePairResultant_factor
    (a : Coefficients K) (xi eta : K) :
    incidencePairResultant a xi eta =
      (a.a2 ^ 2 - 4) * (eta - xi) ^ 2 *
        incidencePairObstruction a xi eta := by
  rw [incidencePairResultant,
    incidenceDiscriminantPolynomial_eq_quadratic a xi,
    incidenceDiscriminantPolynomial_eq_quadratic a eta,
    GenMarkoff.Cage.resultant_quadratic_quadratic]
  simp only [incidenceLeadingCoefficient, incidenceLinearCoefficient,
    incidenceConstantCoefficient, traceLinearCoefficient1,
    traceLinearCoefficient2, traceLinearCoefficient3, traceConstant,
    incidencePairObstruction, pairObstructionCoefficientZero,
    pairObstructionCoefficientSum, pairObstructionCoefficientSumSq,
    pairObstructionCoefficientProduct,
    pairObstructionCoefficientProductSum,
    pairObstructionCoefficientProductSq]
  set_option maxRecDepth 100000 in
    ring_nf

/-- Off the diagonal and the explicit obstruction locus, the two incidence
quadratics have nonzero formal resultant. -/
theorem incidencePairResultant_ne_zero
    (a : Coefficients K) (xi eta : K)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hxiEta : xi ≠ eta)
    (hobstruction : incidencePairObstruction a xi eta ≠ 0) :
    incidencePairResultant a xi eta ≠ 0 := by
  have hA2' : a.a2 ^ 2 - 4 ≠ 0 := sub_ne_zero.mpr hA2
  have hetaXi : eta - xi ≠ 0 := sub_ne_zero.mpr hxiEta.symm
  rw [incidencePairResultant_factor]
  exact mul_ne_zero
    (mul_ne_zero hA2' (pow_ne_zero 2 hetaXi)) hobstruction

/-- Leading coefficient of the pair obstruction in its second trace.  The
two factors are precisely the common-even factors already present in
ordered candidate regularity. -/
theorem coeff_two_incidencePairObstructionPolynomial
    (a : Coefficients K) (xi : K) :
    (incidencePairObstructionPolynomial a xi).coeff 2 =
      eval xi (orderedTraceEvenMinusPolynomial a.a1 a.a2 a.a3) *
        eval xi (orderedTraceEvenPlusPolynomial a.a1 a.a2 a.a3) := by
  have hcoeff :
      (incidencePairObstructionPolynomial a xi).coeff 2 =
        pairObstructionCoefficientSumSq a +
          pairObstructionCoefficientProductSum a * xi +
          pairObstructionCoefficientProductSq a * xi ^ 2 := by
    rw [incidencePairObstructionPolynomial]
    simp only [coeff_add, coeff_C, coeff_C_mul_X,
      coeff_C_mul_X_pow]
    norm_num
  rw [hcoeff]
  simp only [pairObstructionCoefficientSumSq,
    pairObstructionCoefficientProductSum,
    pairObstructionCoefficientProductSq,
    eval_orderedTraceEvenMinusPolynomial,
    eval_orderedTraceEvenPlusPolynomial]
  ring

/-- Candidate regularity of the first outer trace makes the pair obstruction
a nonzero polynomial in the second outer trace. -/
theorem incidencePairObstructionPolynomial_ne_zero_of_candidateRegular
    (a : Coefficients K) (xi : K)
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi) :
    incidencePairObstructionPolynomial a xi ≠ 0 := by
  have hminus :
      eval xi (orderedTraceEvenMinusPolynomial a.a1 a.a2 a.a3) ≠ 0 :=
    hregular.2.2.2.2.1
  have hplus :
      eval xi (orderedTraceEvenPlusPolynomial a.a1 a.a2 a.a3) ≠ 0 :=
    hregular.2.2.2.2.2
  intro hzero
  have hcoeff :=
    congrArg (fun f : K[X] ↦ f.coeff 2) hzero
  rw [coeff_two_incidencePairObstructionPolynomial] at hcoeff
  simp only [coeff_zero] at hcoeff
  exact (mul_ne_zero hminus hplus) hcoeff

/-- The pair obstruction has degree at most two in either outer trace. -/
theorem incidencePairObstructionPolynomial_natDegree_le
    (a : Coefficients K) (xi : K) :
    (incidencePairObstructionPolynomial a xi).natDegree ≤ 2 := by
  simp only [incidencePairObstructionPolynomial]
  compute_degree

/-- At most two second outer traces make the pair obstruction vanish. -/
theorem incidencePairObstructionPolynomial_roots_card_le_two
    (a : Coefficients K) (xi : K) [DecidableEq K] :
    (incidencePairObstructionPolynomial a xi).roots.toFinset.card ≤ 2 := by
  calc
    (incidencePairObstructionPolynomial a xi).roots.toFinset.card ≤
        (incidencePairObstructionPolynomial a xi).roots.card :=
      Multiset.toFinset_card_le _
    _ ≤
        (incidencePairObstructionPolynomial a xi).natDegree :=
      Polynomial.card_roots' _
    _ ≤ 2 :=
      incidencePairObstructionPolynomial_natDegree_le a xi

/-- The finite set of second outer traces excluded by pair-resultant
degeneracy for a fixed first outer trace. -/
def incidencePairObstructionBadTraces
    (a : Coefficients K) (xi : K) : Finset K := by
  classical
  exact (incidencePairObstructionPolynomial a xi).roots.toFinset

theorem mem_incidencePairObstructionBadTraces_iff
    (a : Coefficients K) (xi eta : K)
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi) :
    eta ∈ incidencePairObstructionBadTraces a xi ↔
      incidencePairObstruction a xi eta = 0 := by
  classical
  rw [incidencePairObstructionBadTraces, Multiset.mem_toFinset,
    Polynomial.mem_roots
      (incidencePairObstructionPolynomial_ne_zero_of_candidateRegular
        a xi hregular),
    Polynomial.IsRoot.def,
    eval_incidencePairObstructionPolynomial]

theorem incidencePairObstructionBadTraces_card_le_two
    (a : Coefficients K) (xi : K) :
    (incidencePairObstructionBadTraces a xi).card ≤ 2 := by
  classical
  exact incidencePairObstructionPolynomial_roots_card_le_two a xi

/-- The off-diagonal and quadratic-obstruction hypotheses exposed to the
later resultant, geometric, and parity layers.  This name deliberately does
not claim absolute irreducibility or a Hasse--Weil estimate. -/
def IsOffDiagonalObstructionRegularIncidencePair
    (a : Coefficients K) (xi eta : K) : Prop :=
  xi ≠ eta ∧ incidencePairObstruction a xi eta ≠ 0

theorem IsOffDiagonalObstructionRegularIncidencePair.resultant_ne_zero
    {a : Coefficients K} {xi eta : K}
    (h : IsOffDiagonalObstructionRegularIncidencePair a xi eta)
    (hA2 : a.a2 ^ 2 ≠ 4) :
    incidencePairResultant a xi eta ≠ 0 :=
  incidencePairResultant_ne_zero a xi eta hA2 h.1 h.2

end

end GenMarkoff.General.Cage
