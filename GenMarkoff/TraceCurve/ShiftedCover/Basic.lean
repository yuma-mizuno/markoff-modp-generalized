module

public import BGS.Markoff.TraceCurve.Kummer

@[expose] public section

/-!
# Shifted trace power covers

The affine centers of the rotation fibers of a generalized Markoff surface add
a constant term `gamma` to the weighted trace equation.  This file defines the
cleared power cover `shiftedTraceCoverPolynomial` of
`alpha * h + beta * h⁻¹ + gamma = k + k⁻¹` with `k = x ^ d` and `h = y ^ e`,
the even obstruction `shiftedTraceEvenObstruction` that governs its absolute
irreducibility, and the root norm of the shifted base quadratic used in the
Kummer argument of `TraceCurve.ShiftedCover.Irreducibility`.

The variables are ordered as in `BGS.Markoff.splitTraceCoverPolynomial`, the
unshifted cover: variable `0` is the adjacent eigenvalue parameter and
variable `1` is the fiber parameter.
-/

namespace GenMarkoff

open Polynomial

noncomputable section

section ExactCover

variable {K : Type*} [Field K]

/-- The cleared power cover for
`alpha * h + beta * h⁻¹ + gamma = k + k⁻¹`, after replacing
`k` by `x ^ d` and `h` by `y ^ e`. -/
def shiftedTraceCoverPolynomial
    (alpha beta gamma : K) (d e : ℕ) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C alpha * MvPolynomial.X 0 ^ d * MvPolynomial.X 1 ^ (2 * e) +
    MvPolynomial.C beta * MvPolynomial.X 0 ^ d +
    MvPolynomial.C gamma * MvPolynomial.X 0 ^ d * MvPolynomial.X 1 ^ e -
    MvPolynomial.X 0 ^ (2 * d) * MvPolynomial.X 1 ^ e -
    MvPolynomial.X 1 ^ e

theorem eval_shiftedTraceCoverPolynomial
    (alpha beta gamma : K) (d e : ℕ) (x y : K) :
    MvPolynomial.eval ![x, y] (shiftedTraceCoverPolynomial alpha beta gamma d e) =
      alpha * x ^ d * y ^ (2 * e) + beta * x ^ d +
        gamma * x ^ d * y ^ e - x ^ (2 * d) * y ^ e - y ^ e := by
  simp [shiftedTraceCoverPolynomial]

/-- The common-even-exponent obstruction
`(gamma ^ 2 - 4 * (sigma + 1)) ^ 2 - 64 * sigma`; it factors as
`((gamma - 2) ^ 2 - 4 * sigma) * ((gamma + 2) ^ 2 - 4 * sigma)`
(`shiftedTraceEvenObstruction_factorization`). -/
def shiftedTraceEvenObstruction (sigma gamma : K) : K :=
  (gamma ^ 2 - 4 * (sigma + 1)) ^ 2 - 64 * sigma

theorem shiftedTraceEvenObstruction_factorization
    (sigma gamma : K) :
    shiftedTraceEvenObstruction sigma gamma =
      ((gamma - 2) ^ 2 - 4 * sigma) *
        ((gamma + 2) ^ 2 - 4 * sigma) := by
  simp only [shiftedTraceEvenObstruction]
  ring

end ExactCover

section NormDegrees

variable {K : Type*} [Field K]

/-- Numerator of the product of the two roots of the shifted quadratic base
equation. -/
def shiftedTraceRootNormNumerator (sigma : K) : K[X] :=
  C sigma * X - 1

/-- Denominator of the product of the two roots of the shifted quadratic base
equation. -/
def shiftedTraceRootNormDenominator : K[X] :=
  X * (1 - X)

/-- The product of the two roots of the shifted quadratic base equation,
viewed as a rational function of `u`.  It is independent of the shift
`gamma`. -/
def shiftedTraceRootNorm (sigma : K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (shiftedTraceRootNormNumerator sigma) /
    algebraMap K[X] (RatFunc K) shiftedTraceRootNormDenominator

lemma shiftedTraceRootNormNumerator_natDegree
    (sigma : K) (hsigma : sigma ≠ 0) :
    (shiftedTraceRootNormNumerator sigma).natDegree = 1 := by
  rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 1)]
  rw [shiftedTraceRootNormNumerator]
  compute_degree!

lemma shiftedTraceRootNormDenominator_natDegree :
    (shiftedTraceRootNormDenominator : K[X]).natDegree = 2 := by
  rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 2)]
  rw [shiftedTraceRootNormDenominator]
  compute_degree!

lemma shiftedTraceRootNormNumerator_ne_zero
    (sigma : K) (hsigma : sigma ≠ 0) :
    shiftedTraceRootNormNumerator sigma ≠ 0 := by
  intro h
  have hdegree := congrArg Polynomial.natDegree h
  simp [shiftedTraceRootNormNumerator_natDegree sigma hsigma] at hdegree

lemma shiftedTraceRootNormDenominator_ne_zero :
    (shiftedTraceRootNormDenominator : K[X]) ≠ 0 := by
  intro h
  have hdegree := congrArg Polynomial.natDegree h
  simp [shiftedTraceRootNormDenominator_natDegree (K := K)] at hdegree

lemma shiftedTraceRootNorm_ne_zero (sigma : K) (hsigma : sigma ≠ 0) :
    shiftedTraceRootNorm sigma ≠ 0 := by
  apply div_ne_zero
  · exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (shiftedTraceRootNormNumerator_ne_zero sigma hsigma)
  · exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (shiftedTraceRootNormDenominator_ne_zero (K := K))

/-- For `sigma ≠ 0`, the root norm has degree `-1` at infinity. -/
theorem shiftedTraceRootNorm_intDegree (sigma : K) (hsigma : sigma ≠ 0) :
    (shiftedTraceRootNorm sigma).intDegree = -1 := by
  rw [shiftedTraceRootNorm, RatFunc.intDegree_div]
  · rw [RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial,
      shiftedTraceRootNormNumerator_natDegree sigma hsigma,
      shiftedTraceRootNormDenominator_natDegree]
    norm_num
  · exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (shiftedTraceRootNormNumerator_ne_zero sigma hsigma)
  · exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (shiftedTraceRootNormDenominator_ne_zero (K := K))

end NormDegrees

end

end GenMarkoff
