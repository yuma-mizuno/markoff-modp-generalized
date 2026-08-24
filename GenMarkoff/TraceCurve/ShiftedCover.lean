import Mathlib

/-!
# Shifted trace power covers

The affine centers in the generalized Markoff rotations add a constant term
to the weighted trace equation.  This file records the resulting power-cover
polynomial and isolates the first exceptional parameter before any
irreducibility claim is made.

The two variables are ordered as in the BGS reference formalization: variable
`0` is the adjacent eigenvalue parameter and variable `1` is the current
fiber parameter.
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

/-- If the normalized weight product is one and the affine shift vanishes,
the cover splits for every pair of exponents.  Thus this locus must be
excluded before absolute irreducibility can be true. -/
theorem shiftedTraceCoverPolynomial_degenerate_factorization
    (alpha beta : K) (d e : ℕ) (hproduct : alpha * beta = 1) :
    shiftedTraceCoverPolynomial alpha beta 0 d e =
      (MvPolynomial.X 1 ^ e - MvPolynomial.C beta * MvPolynomial.X 0 ^ d) *
        (MvPolynomial.C alpha * MvPolynomial.X 0 ^ d * MvPolynomial.X 1 ^ e - 1) := by
  have hproductC :
      MvPolynomial.C alpha * MvPolynomial.C beta =
        (1 : MvPolynomial (Fin 2) K) := by
    rw [← MvPolynomial.C_mul, hproduct, MvPolynomial.C_1]
  simp only [shiftedTraceCoverPolynomial, MvPolynomial.C_0, zero_mul, add_zero]
  linear_combination
    (MvPolynomial.X 0 ^ (2 * d) * MvPolynomial.X 1 ^ e) * hproductC

/-- The normalized shifted base equation after the birational substitution
`u = x / y`. -/
def normalizedShiftedTraceBirationalEquation
    (sigma gamma u v : K) : K :=
  u * (1 - u) * v ^ 2 + gamma * u * v + sigma * u - 1

/-- The two Kummer root relations land on the shifted cover polynomial.
This is the exact algebraic bridge between the function-field tower and the
cleared bivariate equation. -/
theorem eval_shiftedTraceCoverPolynomial_of_powerRootRelations
    (sigma gamma u v xi eta : K) (d e : ℕ)
    (hbase : normalizedShiftedTraceBirationalEquation sigma gamma u v = 0)
    (heta : eta ^ e = v) (hxi : xi ^ d = u * v) :
    MvPolynomial.eval ![xi, eta]
      (shiftedTraceCoverPolynomial 1 sigma gamma d e) = 0 := by
  rw [eval_shiftedTraceCoverPolynomial]
  have hetaTwo : eta ^ (2 * e) = (eta ^ e) ^ 2 := by
    simpa [Nat.mul_comm] using (pow_mul eta e 2)
  have hxiTwo : xi ^ (2 * d) = (xi ^ d) ^ 2 := by
    simpa [Nat.mul_comm] using (pow_mul xi d 2)
  rw [hetaTwo, hxiTwo, heta, hxi]
  rw [normalizedShiftedTraceBirationalEquation] at hbase
  linear_combination v * hbase

/-- The normalized cleared cover is the birational base equation times the
invertible coordinate `y`. -/
theorem normalizedShiftedTrace_birational_change
    (sigma gamma x y : K) (hy : y ≠ 0) :
    x * y ^ 2 + sigma * x + gamma * x * y - x ^ 2 * y - y =
      y * normalizedShiftedTraceBirationalEquation sigma gamma (x / y) y := by
  change x * y ^ 2 + sigma * x + gamma * x * y - x ^ 2 * y - y =
    y * ((x / y) * (1 - x / y) * y ^ 2 +
      gamma * (x / y) * y + sigma * (x / y) - 1)
  field_simp [hy]
  ring

@[simp]
theorem normalizedShiftedTraceBirationalEquation_at_one
    (sigma gamma v : K) :
    normalizedShiftedTraceBirationalEquation sigma gamma 1 v =
      gamma * v + sigma - 1 := by
  simp [normalizedShiftedTraceBirationalEquation]

/-- The only parameter for which the entire vertical fiber `u = 1` is a
component of the normalized base equation. -/
theorem normalizedShiftedTrace_verticalFiber_iff
    (sigma gamma : K) :
    (∀ v : K, normalizedShiftedTraceBirationalEquation sigma gamma 1 v = 0) ↔
      sigma = 1 ∧ gamma = 0 := by
  constructor
  · intro h
    have hsigma : sigma = 1 := by
      exact sub_eq_zero.mp (by simpa using h 0)
    have hgamma : gamma = 0 := by
      simpa [hsigma] using h 1
    exact ⟨hsigma, hgamma⟩
  · rintro ⟨rfl, rfl⟩ v
    simp

/-- The numerator of the discriminant after completing the square in the
shifted birational base equation. -/
def shiftedTraceDiscriminantNumerator (sigma gamma u : K) : K :=
  u * (4 * sigma * u ^ 2 + (gamma ^ 2 - 4 * sigma - 4) * u + 4)

/-- Completing the square converts the shifted base equation to a quadratic
cover of the `u`-line. -/
theorem normalizedShiftedTrace_completeSquare
    (sigma gamma u v : K) :
    (2 * u * (1 - u) * v + gamma * u) ^ 2 =
      shiftedTraceDiscriminantNumerator sigma gamma u +
        4 * u * (1 - u) *
          normalizedShiftedTraceBirationalEquation sigma gamma u v := by
  simp only [normalizedShiftedTraceBirationalEquation,
    shiftedTraceDiscriminantNumerator]
  ring

theorem normalizedShiftedTrace_completeSquare_of_eq_zero
    (sigma gamma u v : K)
    (hbase : normalizedShiftedTraceBirationalEquation sigma gamma u v = 0) :
    (2 * u * (1 - u) * v + gamma * u) ^ 2 =
      shiftedTraceDiscriminantNumerator sigma gamma u := by
  rw [normalizedShiftedTrace_completeSquare, hbase]
  ring

@[simp]
theorem shiftedTraceDiscriminantNumerator_at_one
    (sigma gamma : K) :
    shiftedTraceDiscriminantNumerator sigma gamma 1 = gamma ^ 2 := by
  simp [shiftedTraceDiscriminantNumerator]
  ring

theorem shiftedTraceDiscriminantNumerator_degenerate
    (u : K) :
    shiftedTraceDiscriminantNumerator 1 0 u = 4 * u * (u - 1) ^ 2 := by
  simp [shiftedTraceDiscriminantNumerator]
  ring

/-- The common-even-exponent obstruction.  Its two factors are the two
singular branches of the shifted base curve. -/
def shiftedTraceEvenObstruction (sigma gamma : K) : K :=
  (gamma ^ 2 - 4 * (sigma + 1)) ^ 2 - 64 * sigma

theorem shiftedTraceEvenObstruction_factorization
    (sigma gamma : K) :
    shiftedTraceEvenObstruction sigma gamma =
      ((gamma - 2) ^ 2 - 4 * sigma) *
        ((gamma + 2) ^ 2 - 4 * sigma) := by
  simp only [shiftedTraceEvenObstruction]
  ring

/-- A one-parameter family on the first singular branch of the common-even
obstruction. -/
@[simp]
theorem shiftedTraceEvenObstruction_singularFamily (a : K) :
    shiftedTraceEvenObstruction (a ^ 2) (2 * (a + 1)) = 0 := by
  rw [shiftedTraceEvenObstruction_factorization]
  ring

/-- On the singular family `sigma = a²`, `gamma = 2(a+1)`, the `(2,2)`
power cover splits as a difference of squares.  In particular, irreducibility
of the shifted base curve alone cannot justify every cover required by the
endgame. -/
theorem shiftedTraceCoverPolynomial_evenSingular_factorization (a : K) :
    shiftedTraceCoverPolynomial 1 (a ^ 2) (2 * (a + 1)) 2 2 =
      (MvPolynomial.X 0 * (MvPolynomial.X 1 ^ 2 + MvPolynomial.C a) -
          MvPolynomial.X 1 * (MvPolynomial.X 0 ^ 2 - 1)) *
        (MvPolynomial.X 0 * (MvPolynomial.X 1 ^ 2 + MvPolynomial.C a) +
          MvPolynomial.X 1 * (MvPolynomial.X 0 ^ 2 - 1)) := by
  simp [shiftedTraceCoverPolynomial, map_ofNat]
  ring

/-- The smallest integral counterexample to the naive shifted-cover
generalization: the base weights are nonzero and the shift is nonzero, but
the `(2,2)` cover still factors. -/
theorem shiftedTraceCoverPolynomial_one_one_four_two_two_factorization :
    shiftedTraceCoverPolynomial (1 : K) 1 4 2 2 =
      (MvPolynomial.X 0 * (MvPolynomial.X 1 ^ 2 + 1) -
          MvPolynomial.X 1 * (MvPolynomial.X 0 ^ 2 - 1)) *
        (MvPolynomial.X 0 * (MvPolynomial.X 1 ^ 2 + 1) +
          MvPolynomial.X 1 * (MvPolynomial.X 0 ^ 2 - 1)) := by
  have hfour : (2 : K) * (1 + 1) = 4 := by ring
  simpa [hfour] using
    shiftedTraceCoverPolynomial_evenSingular_factorization (K := K) 1

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

/-- The first Kummer radicand retains degree `-1` after adding the affine
shift. -/
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

lemma RatFunc.intDegree_pow
    (z : RatFunc K) (hz : z ≠ 0) (n : ℕ) :
    (z ^ n).intDegree = (n : ℤ) * z.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hz) hz, ih]
      push_cast
      ring

/-- Multiplying the shifted quadratic root by `u` changes the norm degree
from `-1` to `+1`, exactly as in the unshifted BGS Kummer tower. -/
theorem shiftedTraceCoordinateProductNorm_intDegree
    (sigma : K) (hsigma : sigma ≠ 0) :
    (RatFunc.X ^ 2 * shiftedTraceRootNorm sigma).intDegree = 1 := by
  rw [RatFunc.intDegree_mul]
  · rw [RatFunc.intDegree_pow RatFunc.X RatFunc.X_ne_zero,
      RatFunc.intDegree_X, shiftedTraceRootNorm_intDegree sigma hsigma]
    norm_num
  · exact pow_ne_zero 2 RatFunc.X_ne_zero
  · exact shiftedTraceRootNorm_ne_zero sigma hsigma

end NormDegrees

end

end GenMarkoff
