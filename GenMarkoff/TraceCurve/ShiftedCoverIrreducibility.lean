import GenMarkoff.TraceCurve.ShiftedCover
import BGS.Markoff.Incidence.Geometry
import BGS.Markoff.TraceCurve.OddCommonPrimeIndependence
import BGS.Markoff.TraceCurve.PositiveCoprimeIrreducibility

/-!
# The quadratic obstruction for shifted trace covers

This file starts the absolute-irreducibility proof for the generalized
shifted trace cover.  It isolates the two square classes that are required by
the quadratic base extension:

* `X * shiftedTraceDiscriminantQuadratic sigma gamma` is the discriminant
  class of the base quadratic over `K(X)`;
* `shiftedTraceDiscriminantQuadratic sigma gamma` is the class which decides
  whether `X` becomes a square in that quadratic extension.

The single coefficient obstruction controlling both calculations is exactly
`shiftedTraceEvenObstruction sigma gamma`.
-/

namespace GenMarkoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The quadratic factor of the completed-square branch polynomial. -/
def shiftedTraceDiscriminantQuadratic (sigma gamma : K) : K[X] :=
  C (4 * sigma) * X ^ 2 + C (gamma ^ 2 - 4 * sigma - 4) * X + C 4

theorem eval_shiftedTraceDiscriminantQuadratic (sigma gamma u : K) :
    (shiftedTraceDiscriminantQuadratic sigma gamma).eval u =
      4 * sigma * u ^ 2 + (gamma ^ 2 - 4 * sigma - 4) * u + 4 := by
  simp [shiftedTraceDiscriminantQuadratic]

/-- The branch numerator is `u` times its quadratic factor. -/
theorem shiftedTraceDiscriminantNumerator_eq_mul_quadratic
    (sigma gamma u : K) :
    shiftedTraceDiscriminantNumerator sigma gamma u =
      u * (shiftedTraceDiscriminantQuadratic sigma gamma).eval u := by
  simp [shiftedTraceDiscriminantNumerator,
    eval_shiftedTraceDiscriminantQuadratic]

/-- The ordinary discriminant of the quadratic branch factor is `D₂`. -/
theorem shiftedTraceDiscriminantQuadratic_discriminant
    (sigma gamma : K) :
    (gamma ^ 2 - 4 * sigma - 4) ^ 2 - 4 * (4 * sigma) * 4 =
      shiftedTraceEvenObstruction sigma gamma := by
  simp [shiftedTraceEvenObstruction]
  ring

lemma shiftedTraceDiscriminantQuadratic_natDegree
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    (shiftedTraceDiscriminantQuadratic sigma gamma).natDegree = 2 := by
  rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 2)]
  rw [shiftedTraceDiscriminantQuadratic]
  compute_degree!
  constructor
  · rw [show (4 : K) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 h2
  · exact hsigma

lemma shiftedTraceDiscriminantQuadratic_not_isUnit
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    ¬ IsUnit (shiftedTraceDiscriminantQuadratic sigma gamma) :=
  not_isUnit_of_natDegree_pos _ <| by
    rw [shiftedTraceDiscriminantQuadratic_natDegree sigma gamma h2 hsigma]
    norm_num

/-- Nonvanishing of `D₂` is precisely the separability condition for the
quadratic branch factor (under the standing nonzero-leading-coefficient
hypotheses). -/
theorem shiftedTraceDiscriminantQuadratic_separable
    (sigma gamma : K) (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0) :
    (shiftedTraceDiscriminantQuadratic sigma gamma).Separable := by
  rw [Polynomial.separable_def']
  let a : K := 4 * sigma
  let b : K := gamma ^ 2 - 4 * sigma - 4
  let delta : K := b ^ 2 - 4 * a * 4
  have hdelta : delta ≠ 0 := by
    simpa [a, b, delta, shiftedTraceDiscriminantQuadratic_discriminant]
      using hD2
  have hderivative :
      (shiftedTraceDiscriminantQuadratic sigma gamma).derivative =
        C (2 * a) * X + C b := by
    rw [shiftedTraceDiscriminantQuadratic]
    simp only [derivative_add, derivative_mul, derivative_pow, derivative_X,
      derivative_C, derivative_ofNat, map_ofNat, zero_mul, zero_add, mul_one]
    dsimp [a, b]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    ring
  have hbezout :
      C (-4 * a) * shiftedTraceDiscriminantQuadratic sigma gamma +
          (shiftedTraceDiscriminantQuadratic sigma gamma).derivative *
            (shiftedTraceDiscriminantQuadratic sigma gamma).derivative =
        C delta := by
    rw [hderivative, shiftedTraceDiscriminantQuadratic]
    dsimp [a, b, delta]
    simp only [map_sub, map_mul, map_pow, map_neg, map_ofNat]
    ring
  refine ⟨C delta⁻¹ * C (-4 * a),
    C delta⁻¹ * (shiftedTraceDiscriminantQuadratic sigma gamma).derivative, ?_⟩
  calc
    (C delta⁻¹ * C (-4 * a)) *
          shiftedTraceDiscriminantQuadratic sigma gamma +
        (C delta⁻¹ *
            (shiftedTraceDiscriminantQuadratic sigma gamma).derivative) *
          (shiftedTraceDiscriminantQuadratic sigma gamma).derivative =
        C delta⁻¹ *
          (C (-4 * a) * shiftedTraceDiscriminantQuadratic sigma gamma +
            (shiftedTraceDiscriminantQuadratic sigma gamma).derivative *
              (shiftedTraceDiscriminantQuadratic sigma gamma).derivative) := by ring
    _ = C delta⁻¹ * C delta := by rw [hbezout]
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hdelta, C_1]

/-- The branch factor itself is a nontrivial square class in `K(X)`. -/
theorem shiftedTraceDiscriminantQuadratic_not_isSquare
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0) :
    ¬ IsSquare
      (algebraMap K[X] (RatFunc K)
        (shiftedTraceDiscriminantQuadratic sigma gamma)) := by
  apply BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
  · exact (shiftedTraceDiscriminantQuadratic_separable sigma gamma hD2).squarefree
  · exact shiftedTraceDiscriminantQuadratic_not_isUnit sigma gamma h2 hsigma

/-- The coordinate prime `X` is coprime to the branch factor because the
factor has constant term `4`. -/
theorem isCoprime_X_shiftedTraceDiscriminantQuadratic
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) :
    IsCoprime (X : K[X]) (shiftedTraceDiscriminantQuadratic sigma gamma) := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 h2
  let a : K := 4 * sigma
  let b : K := gamma ^ 2 - 4 * sigma - 4
  refine ⟨-(C (4⁻¹) * (C a * X + C b)), C (4⁻¹), ?_⟩
  calc
    -(C (4⁻¹) * (C a * X + C b)) * X +
        C (4⁻¹) * shiftedTraceDiscriminantQuadratic sigma gamma =
      C (4⁻¹) * C 4 := by
        simp only [shiftedTraceDiscriminantQuadratic, a, b]
        ring
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ h4, C_1]

/-- The discriminant square class of the base quadratic is also nontrivial.
The extra factor `X` records the odd valuation at the origin. -/
theorem X_mul_shiftedTraceDiscriminantQuadratic_not_isSquare
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (_hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0) :
    ¬ IsSquare
      (algebraMap K[X] (RatFunc K)
        (X * shiftedTraceDiscriminantQuadratic sigma gamma)) := by
  apply BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
  · exact ((Polynomial.separable_X.mul
      (shiftedTraceDiscriminantQuadratic_separable sigma gamma hD2)
      (isCoprime_X_shiftedTraceDiscriminantQuadratic sigma gamma h2))).squarefree
  · intro hunit
    have hxUnit : IsUnit (X : K[X]) := (IsUnit.mul_iff.mp hunit).1
    exact Polynomial.not_isUnit_X hxUnit

section BaseQuadratic

/-- Numerator of the discriminant of the shifted quadratic over `K(X)`. -/
def shiftedTraceBaseDiscriminantNumerator (sigma gamma : K) : K[X] :=
  shiftedTraceDiscriminantQuadratic sigma gamma

/-- Denominator of the discriminant of the shifted quadratic over `K(X)`. -/
def shiftedTraceBaseDiscriminantDenominator : K[X] :=
  X * (1 - X) ^ 2

/-- Discriminant of the shifted quadratic base equation over `K(X)`. -/
def shiftedTraceBaseDiscriminant (sigma gamma : K) : RatFunc K :=
  algebraMap K[X] (RatFunc K)
      (shiftedTraceBaseDiscriminantNumerator sigma gamma) /
    algebraMap K[X] (RatFunc K) shiftedTraceBaseDiscriminantDenominator

lemma shiftedTraceBaseDiscriminantNumerator_natDegree
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    (shiftedTraceBaseDiscriminantNumerator sigma gamma).natDegree = 2 := by
  exact shiftedTraceDiscriminantQuadratic_natDegree sigma gamma h2 hsigma

lemma shiftedTraceBaseDiscriminantDenominator_natDegree :
    (shiftedTraceBaseDiscriminantDenominator : K[X]).natDegree = 3 := by
  rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 3)]
  rw [shiftedTraceBaseDiscriminantDenominator]
  compute_degree!

lemma shiftedTraceBaseDiscriminantNumerator_ne_zero
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    shiftedTraceBaseDiscriminantNumerator sigma gamma ≠ 0 := by
  intro hzero
  have hdegree := congrArg Polynomial.natDegree hzero
  simp [shiftedTraceBaseDiscriminantNumerator_natDegree
    sigma gamma h2 hsigma] at hdegree

lemma shiftedTraceBaseDiscriminantDenominator_ne_zero :
    (shiftedTraceBaseDiscriminantDenominator : K[X]) ≠ 0 := by
  intro hzero
  have hdegree := congrArg Polynomial.natDegree hzero
  simp [shiftedTraceBaseDiscriminantDenominator_natDegree (K := K)] at hdegree

lemma shiftedTraceBaseDiscriminant_ne_zero
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    shiftedTraceBaseDiscriminant sigma gamma ≠ 0 := by
  apply div_ne_zero
  · exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (shiftedTraceBaseDiscriminantNumerator_ne_zero sigma gamma h2 hsigma)
  · exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (shiftedTraceBaseDiscriminantDenominator_ne_zero (K := K))

/-- The discriminant has odd degree at infinity, so it is not a square. -/
theorem shiftedTraceBaseDiscriminant_intDegree
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    (shiftedTraceBaseDiscriminant sigma gamma).intDegree = -1 := by
  rw [shiftedTraceBaseDiscriminant, RatFunc.intDegree_div]
  · rw [RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial,
      shiftedTraceBaseDiscriminantNumerator_natDegree sigma gamma h2 hsigma,
      shiftedTraceBaseDiscriminantDenominator_natDegree]
    norm_num
  · exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (shiftedTraceBaseDiscriminantNumerator_ne_zero sigma gamma h2 hsigma)
  · exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (shiftedTraceBaseDiscriminantDenominator_ne_zero (K := K))

theorem shiftedTraceBaseDiscriminant_not_isSquare
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    ¬ IsSquare (shiftedTraceBaseDiscriminant sigma gamma) := by
  rintro ⟨z, hz⟩
  have hdiscriminant : shiftedTraceBaseDiscriminant sigma gamma ≠ 0 :=
    shiftedTraceBaseDiscriminant_ne_zero sigma gamma h2 hsigma
  have hz0 : z ≠ 0 := by
    intro hzero
    apply hdiscriminant
    simpa [hzero] using hz
  have hpow : z ^ 2 = shiftedTraceBaseDiscriminant sigma gamma := by
    simpa [pow_two] using hz.symm
  have hdegree := congrArg RatFunc.intDegree hpow
  rw [RatFunc.intDegree_pow z hz0 2,
    shiftedTraceBaseDiscriminant_intDegree sigma gamma h2 hsigma] at hdegree
  omega

/-- Linear coefficient of the monic shifted base quadratic. -/
def shiftedTraceBaseLinearCoefficient (gamma : K) : RatFunc K :=
  RatFunc.C gamma / (1 - RatFunc.X)

/-- The monic quadratic defining the shifted base function field. -/
def shiftedTraceBasePolynomial (sigma gamma : K) : Polynomial (RatFunc K) :=
  X ^ 2 + C (shiftedTraceBaseLinearCoefficient gamma) * X +
    C (shiftedTraceRootNorm sigma)

/-- A reusable irreducibility criterion for a monic quadratic with a linear
term. -/
theorem monicQuadratic_irreducible_of_discriminant_not_isSquare
    {R : Type*} [CommRing R] [IsDomain R] (b c : R)
    (hdisc : ¬ IsSquare (b ^ 2 - 4 * c)) :
    Irreducible (X ^ 2 + C b * X + C c : R[X]) := by
  have hmonic : (X ^ 2 + C b * X + C c : R[X]).Monic := by
    simpa using (isMonicOfDegree_sub_add_two (-b) c).monic
  have hdegree : (X ^ 2 + C b * X + C c : R[X]).natDegree = 2 := by
    simpa using (isMonicOfDegree_sub_add_two (-b) c).natDegree_eq
  rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro root hroot
    have heval := (mem_roots hmonic.ne_zero).mp hroot
    have heq : root ^ 2 + b * root + c = 0 := by
      simpa using heval
    apply hdisc
    refine ⟨2 * root + b, ?_⟩
    calc
      b ^ 2 - 4 * c =
          (2 * root + b) * (2 * root + b) -
            4 * (root ^ 2 + b * root + c) := by ring
      _ = (2 * root + b) * (2 * root + b) := by rw [heq]; ring
  · rw [hdegree]
  · rw [hdegree]
    norm_num

private lemma one_sub_ratFuncX_ne_zero : (1 - RatFunc.X : RatFunc K) ≠ 0 := by
  intro hzero
  have honeX : (1 : RatFunc K) = RatFunc.X := sub_eq_zero.mp hzero
  have hdegree := congrArg RatFunc.intDegree honeX
  norm_num at hdegree

theorem shiftedTraceBaseLinearCoefficient_cleared (gamma : K) :
    RatFunc.X * (1 - RatFunc.X) *
        shiftedTraceBaseLinearCoefficient gamma =
      RatFunc.C gamma * RatFunc.X := by
  have hOneSubX : (1 - RatFunc.X : RatFunc K) ≠ 0 :=
    one_sub_ratFuncX_ne_zero
  rw [shiftedTraceBaseLinearCoefficient]
  field_simp [hOneSubX]

theorem shiftedTraceRootNorm_cleared (sigma : K) :
    RatFunc.X * (1 - RatFunc.X) * shiftedTraceRootNorm sigma =
      RatFunc.C sigma * RatFunc.X - 1 := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hOneSubX : (1 - RatFunc.X : RatFunc K) ≠ 0 :=
    one_sub_ratFuncX_ne_zero
  simp only [shiftedTraceRootNorm, shiftedTraceRootNormNumerator,
    shiftedTraceRootNormDenominator, map_sub, map_mul, map_one,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  field_simp [hX, hOneSubX]

theorem RatFunc.X_mul_shiftedTraceRootNorm_eq_neg_residualRatio
    (sigma : K) :
    RatFunc.X * shiftedTraceRootNorm sigma =
      -((1 - RatFunc.C sigma * RatFunc.X) / (1 - RatFunc.X)) := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hOneSubX : (1 - RatFunc.X : RatFunc K) ≠ 0 :=
    one_sub_ratFuncX_ne_zero
  simp only [shiftedTraceRootNorm, shiftedTraceRootNormNumerator,
    shiftedTraceRootNormDenominator, map_sub, map_mul, map_one,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  field_simp [hX, hOneSubX]
  ring

/-- The abstract quadratic discriminant agrees with the explicit rational
function whose infinity degree is `-1`. -/
theorem shiftedTraceBasePolynomial_discriminant
    (sigma gamma : K) :
    shiftedTraceBaseLinearCoefficient gamma ^ 2 -
        4 * shiftedTraceRootNorm sigma =
      shiftedTraceBaseDiscriminant sigma gamma := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hOneSubX : (1 - RatFunc.X : RatFunc K) ≠ 0 :=
    one_sub_ratFuncX_ne_zero
  simp only [shiftedTraceBaseLinearCoefficient, shiftedTraceRootNorm,
    shiftedTraceRootNormNumerator, shiftedTraceRootNormDenominator,
    shiftedTraceBaseDiscriminant, shiftedTraceBaseDiscriminantNumerator,
    shiftedTraceBaseDiscriminantDenominator,
    shiftedTraceDiscriminantQuadratic, map_mul, map_add, map_sub, map_pow,
    map_one, map_ofNat, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  field_simp [hX, hOneSubX]
  ring

/-- The shifted quadratic base equation is irreducible over `K(X)`.  This
part uses the odd degree at infinity; `D₂` is only needed at the next
quadratic square-class step. -/
theorem shiftedTraceBasePolynomial_irreducible
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    Irreducible (shiftedTraceBasePolynomial sigma gamma) := by
  rw [shiftedTraceBasePolynomial]
  apply monicQuadratic_irreducible_of_discriminant_not_isSquare
  rw [shiftedTraceBasePolynomial_discriminant sigma gamma]
  exact shiftedTraceBaseDiscriminant_not_isSquare sigma gamma h2 hsigma

lemma shiftedTraceBasePolynomial_monic (sigma gamma : K) :
    (shiftedTraceBasePolynomial sigma gamma).Monic := by
  simpa [shiftedTraceBasePolynomial] using
    (isMonicOfDegree_sub_add_two
      (-shiftedTraceBaseLinearCoefficient gamma)
      (shiftedTraceRootNorm sigma)).monic

@[simp]
lemma shiftedTraceBasePolynomial_natDegree (sigma gamma : K) :
    (shiftedTraceBasePolynomial sigma gamma).natDegree = 2 := by
  simpa [shiftedTraceBasePolynomial] using
    (isMonicOfDegree_sub_add_two
      (-shiftedTraceBaseLinearCoefficient gamma)
      (shiftedTraceRootNorm sigma)).natDegree_eq

/-- The shifted quadratic function field. -/
abbrev ShiftedTraceBaseFunctionField (sigma gamma : K) :=
  AdjoinRoot (shiftedTraceBasePolynomial sigma gamma)

/-- The rational parameter in the shifted quadratic function field. -/
def shiftedTraceBaseU (sigma gamma : K) :
    ShiftedTraceBaseFunctionField sigma gamma :=
  algebraMap (RatFunc K) _ RatFunc.X

/-- The quadratic coordinate in the shifted quadratic function field. -/
def shiftedTraceBaseV (sigma gamma : K) :
    ShiftedTraceBaseFunctionField sigma gamma :=
  AdjoinRoot.root (shiftedTraceBasePolynomial sigma gamma)

/-- The adjoined coordinate satisfies its monic shifted quadratic. -/
theorem shiftedTraceBaseV_quadraticEquation
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
      ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
    shiftedTraceBaseV sigma gamma ^ 2 +
        algebraMap (RatFunc K) (ShiftedTraceBaseFunctionField sigma gamma)
          (shiftedTraceBaseLinearCoefficient gamma) *
          shiftedTraceBaseV sigma gamma +
        algebraMap (RatFunc K) (ShiftedTraceBaseFunctionField sigma gamma)
          (shiftedTraceRootNorm sigma) = 0 := by
  let hIrred := shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) := ⟨hIrred⟩
  have h := AdjoinRoot.eval₂_root (shiftedTraceBasePolynomial sigma gamma)
  rw [shiftedTraceBasePolynomial] at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] at h
  rw [← AdjoinRoot.algebraMap_eq] at h
  exact h

/-- The two coordinates satisfy the normalized shifted trace equation. -/
theorem shiftedTraceBaseU_V_equation
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
      ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
    shiftedTraceBaseU sigma gamma * (1 - shiftedTraceBaseU sigma gamma) *
          shiftedTraceBaseV sigma gamma ^ 2 +
        algebraMap (RatFunc K) (ShiftedTraceBaseFunctionField sigma gamma)
            (RatFunc.C gamma) *
          shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma +
        algebraMap (RatFunc K) (ShiftedTraceBaseFunctionField sigma gamma)
            (RatFunc.C sigma) *
          shiftedTraceBaseU sigma gamma - 1 = 0 := by
  let hIrred := shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) := ⟨hIrred⟩
  let mapBase := algebraMap (RatFunc K)
    (ShiftedTraceBaseFunctionField sigma gamma)
  have hquadratic := shiftedTraceBaseV_quadraticEquation
    sigma gamma h2 hsigma
  have hlinearMap := congrArg mapBase
    (shiftedTraceBaseLinearCoefficient_cleared (K := K) gamma)
  have hconstantMap := congrArg mapBase
    (shiftedTraceRootNorm_cleared (K := K) sigma)
  simp only [map_mul, map_sub, map_one] at hlinearMap hconstantMap
  change shiftedTraceBaseU sigma gamma * (1 - shiftedTraceBaseU sigma gamma) *
      algebraMap (RatFunc K) (ShiftedTraceBaseFunctionField sigma gamma)
        (shiftedTraceBaseLinearCoefficient gamma) =
      algebraMap (RatFunc K) (ShiftedTraceBaseFunctionField sigma gamma)
        (RatFunc.C gamma) * shiftedTraceBaseU sigma gamma at hlinearMap
  change shiftedTraceBaseU sigma gamma * (1 - shiftedTraceBaseU sigma gamma) *
      algebraMap (RatFunc K) (ShiftedTraceBaseFunctionField sigma gamma)
        (shiftedTraceRootNorm sigma) =
      algebraMap (RatFunc K) (ShiftedTraceBaseFunctionField sigma gamma)
        (RatFunc.C sigma) * shiftedTraceBaseU sigma gamma - 1 at hconstantMap
  linear_combination
    (shiftedTraceBaseU sigma gamma *
      (1 - shiftedTraceBaseU sigma gamma)) * hquadratic -
    shiftedTraceBaseV sigma gamma * hlinearMap - hconstantMap

/-- The quadratic coordinate has norm equal to the product of the two roots,
namely the already-defined shifted root norm. -/
theorem norm_shiftedTraceBaseV
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
      ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
    Algebra.norm (RatFunc K) (shiftedTraceBaseV sigma gamma) =
      shiftedTraceRootNorm sigma := by
  let hIrred := shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) := ⟨hIrred⟩
  let pb := AdjoinRoot.powerBasis hIrred.ne_zero
  change Algebra.norm (RatFunc K) pb.gen = shiftedTraceRootNorm sigma
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
    AdjoinRoot.minpoly_powerBasis_gen_of_monic]
  · have hdim : pb.dim = 2 := by
      change (shiftedTraceBasePolynomial sigma gamma).natDegree = 2
      exact shiftedTraceBasePolynomial_natDegree sigma gamma
    rw [hdim]
    simp [shiftedTraceBasePolynomial]
  · exact shiftedTraceBasePolynomial_monic sigma gamma

/-- No nontrivial prime power in the quadratic base field can equal the
coordinate `V`; its norm has degree `-1`. -/
theorem shiftedTraceBaseV_not_primePower
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (q : ℕ) (hq : q.Prime)
    (z : ShiftedTraceBaseFunctionField sigma gamma) :
    letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
      ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
    z ^ q ≠ shiftedTraceBaseV sigma gamma := by
  let hIrred := shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) := ⟨hIrred⟩
  intro hpow
  have hnorm := congrArg (Algebra.norm (RatFunc K)) hpow
  rw [map_pow, norm_shiftedTraceBaseV sigma gamma h2 hsigma] at hnorm
  have hrootNorm : shiftedTraceRootNorm sigma ≠ 0 :=
    shiftedTraceRootNorm_ne_zero sigma hsigma
  have hnormz : Algebra.norm (RatFunc K) z ≠ 0 := by
    intro hzero
    apply hrootNorm
    simpa [hzero, hq.ne_zero] using hnorm.symm
  have hdegree := congrArg RatFunc.intDegree hnorm
  rw [RatFunc.intDegree_pow _ hnormz q,
    shiftedTraceRootNorm_intDegree sigma hsigma] at hdegree
  have hqdvd : (q : ℤ) ∣ (-1 : ℤ) := ⟨(Algebra.norm (RatFunc K) z).intDegree,
    hdegree.symm⟩
  rw [Int.natCast_dvd] at hqdvd
  exact hq.ne_one (Nat.eq_one_of_dvd_one hqdvd)

theorem shiftedTraceBaseFunctionField_finrank
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
      ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
    Module.finrank (RatFunc K)
      (ShiftedTraceBaseFunctionField sigma gamma) = 2 := by
  let hIrred := shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) := ⟨hIrred⟩
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis hIrred.ne_zero)]
  exact shiftedTraceBasePolynomial_natDegree sigma gamma

theorem norm_shiftedTraceBaseU_mul_V
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
      ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
    Algebra.norm (RatFunc K)
        (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma) =
      RatFunc.X ^ 2 * shiftedTraceRootNorm sigma := by
  let hIrred := shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) := ⟨hIrred⟩
  rw [map_mul]
  rw [shiftedTraceBaseU, Algebra.norm_algebraMap,
    shiftedTraceBaseFunctionField_finrank sigma gamma h2 hsigma]
  rw [norm_shiftedTraceBaseV sigma gamma h2 hsigma]

/-- The norm of `U*V` has degree one, the second boundary valuation needed
by the Kummer argument. -/
theorem norm_shiftedTraceBaseU_mul_V_intDegree
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
      ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
    (Algebra.norm (RatFunc K)
      (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma)).intDegree = 1 := by
  let hIrred := shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) := ⟨hIrred⟩
  rw [norm_shiftedTraceBaseU_mul_V sigma gamma h2 hsigma,
    RatFunc.intDegree_mul]
  · rw [RatFunc.intDegree_pow RatFunc.X RatFunc.X_ne_zero,
      RatFunc.intDegree_X, shiftedTraceRootNorm_intDegree sigma hsigma]
    norm_num
  · exact pow_ne_zero 2 RatFunc.X_ne_zero
  · exact shiftedTraceRootNorm_ne_zero sigma hsigma

/-- First Kummer polynomial, adjoining `eta` with `eta^e = V`. -/
def shiftedTraceEtaKummerPolynomial (sigma gamma : K) (e : ℕ) :
    Polynomial (ShiftedTraceBaseFunctionField sigma gamma) :=
  X ^ e - C (shiftedTraceBaseV sigma gamma)

/-- The first Kummer extension of the shifted quadratic function field. -/
abbrev ShiftedTraceEtaFunctionField (sigma gamma : K) (e : ℕ) :=
  AdjoinRoot (shiftedTraceEtaKummerPolynomial sigma gamma e)

/-- Every positive first exponent gives an irreducible Kummer polynomial
once the constant field contains a square root of `-1`. -/
theorem shiftedTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (i : K) (hi : i ^ 2 = -1) (e : ℕ) (he : 0 < e) :
    letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
      ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
    Irreducible (shiftedTraceEtaKummerPolynomial sigma gamma e) := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  apply BGS.Markoff.X_pow_sub_C_irreducible_of_sqrt_neg_one
    (algebraMap K (ShiftedTraceBaseFunctionField sigma gamma) i)
  · rw [← map_pow, hi, map_neg, map_one]
  · exact he.ne'
  · intro q hq _ z
    exact shiftedTraceBaseV_not_primePower
      sigma gamma h2 hsigma q hq z

theorem shiftedTraceEtaFunctionField_finrank_of_sqrt_neg_one
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (i : K) (hi : i ^ 2 = -1) (e : ℕ) (he : 0 < e) :
    letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
      ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
    letI : Fact (Irreducible
        (shiftedTraceEtaKummerPolynomial sigma gamma e)) :=
      ⟨shiftedTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
        sigma gamma h2 hsigma i hi e he⟩
    Module.finrank (ShiftedTraceBaseFunctionField sigma gamma)
      (ShiftedTraceEtaFunctionField sigma gamma e) = e := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  let hEtaIrred :=
    shiftedTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
      sigma gamma h2 hsigma i hi e he
  letI : Fact (Irreducible
      (shiftedTraceEtaKummerPolynomial sigma gamma e)) := ⟨hEtaIrred⟩
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis hEtaIrred.ne_zero)]
  simp [shiftedTraceEtaKummerPolynomial]

/-- Second Kummer radicand, corresponding to `xi^d = U*V`. -/
def shiftedTraceXiRadicand (sigma gamma : K) (e : ℕ) :
    ShiftedTraceEtaFunctionField sigma gamma e :=
  algebraMap (ShiftedTraceBaseFunctionField sigma gamma) _
    (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma)

/-- Second Kummer polynomial, adjoining `xi` with `xi^d = U*V`. -/
def shiftedTraceXiKummerPolynomial (sigma gamma : K) (e d : ℕ) :
    Polynomial (ShiftedTraceEtaFunctionField sigma gamma e) :=
  X ^ d - C (shiftedTraceXiRadicand sigma gamma e)

/-- A prime which does not divide the first exponent cannot occur as a
power of the second radicand.  The two successive norms force it to divide
that exponent. -/
theorem shiftedTraceXiRadicand_not_primePower_of_not_dvd
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (i : K) (hi : i ^ 2 = -1) (e : ℕ) (he : 0 < e)
    (q : ℕ) (hq : q.Prime) (hqe : ¬ q ∣ e)
    (z : letI : Fact
          (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
          ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
        letI : Fact (Irreducible
          (shiftedTraceEtaKummerPolynomial sigma gamma e)) :=
          ⟨shiftedTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
            sigma gamma h2 hsigma i hi e he⟩
        ShiftedTraceEtaFunctionField sigma gamma e) :
    letI : Fact (Irreducible
        (shiftedTraceBasePolynomial sigma gamma)) :=
      ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
    letI : Fact (Irreducible
        (shiftedTraceEtaKummerPolynomial sigma gamma e)) :=
      ⟨shiftedTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
        sigma gamma h2 hsigma i hi e he⟩
    z ^ q ≠ shiftedTraceXiRadicand sigma gamma e := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  let hEtaIrred := shiftedTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    sigma gamma h2 hsigma i hi e he
  letI : Fact (Irreducible
      (shiftedTraceEtaKummerPolynomial sigma gamma e)) := ⟨hEtaIrred⟩
  let baseField := ShiftedTraceBaseFunctionField sigma gamma
  let etaField := ShiftedTraceEtaFunctionField sigma gamma e
  letI : Module.Finite (RatFunc K) baseField :=
    (shiftedTraceBasePolynomial_monic sigma gamma).finite_adjoinRoot
  letI : Module.Finite baseField etaField :=
    (monic_X_pow_sub_C _ he.ne').finite_adjoinRoot
  have hBaseV : shiftedTraceBaseV sigma gamma ≠ 0 := by
    intro hzero
    have hquadratic := shiftedTraceBaseV_quadraticEquation
      sigma gamma h2 hsigma
    rw [hzero] at hquadratic
    have hrootNormZero : shiftedTraceRootNorm sigma = 0 :=
      (algebraMap (RatFunc K) baseField).injective (by simpa using hquadratic)
    exact shiftedTraceRootNorm_ne_zero sigma hsigma hrootNormZero
  have hBaseU : shiftedTraceBaseU sigma gamma ≠ 0 := by
    exact (map_ne_zero_iff _
      (algebraMap (RatFunc K) baseField).injective).mpr RatFunc.X_ne_zero
  have hBaseUV : shiftedTraceBaseU sigma gamma *
      shiftedTraceBaseV sigma gamma ≠ 0 := mul_ne_zero hBaseU hBaseV
  have hXiRadicand : shiftedTraceXiRadicand sigma gamma e ≠ 0 := by
    exact (map_ne_zero_iff _
      (algebraMap baseField etaField).injective).mpr hBaseUV
  intro hpow
  have hz : z ≠ 0 := by
    intro hzero
    apply hXiRadicand
    simpa [hzero, hq.ne_zero] using hpow.symm
  have hFirstNorm := congrArg (Algebra.norm baseField) hpow
  rw [map_pow, shiftedTraceXiRadicand, Algebra.norm_algebraMap,
    shiftedTraceEtaFunctionField_finrank_of_sqrt_neg_one
      sigma gamma h2 hsigma i hi e he] at hFirstNorm
  have hSecondNorm := congrArg (Algebra.norm (RatFunc K)) hFirstNorm
  rw [map_pow, map_pow] at hSecondNorm
  have hNormZNe : Algebra.norm baseField z ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hz
  have hDoubleNormZNe :
      Algebra.norm (RatFunc K) (Algebra.norm baseField z) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hNormZNe
  have hNormBaseUVNe : Algebra.norm (RatFunc K)
      (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hBaseUV
  have hDegree := congrArg RatFunc.intDegree hSecondNorm
  rw [RatFunc.intDegree_pow _ hDoubleNormZNe,
    RatFunc.intDegree_pow _ hNormBaseUVNe,
    norm_shiftedTraceBaseU_mul_V_intDegree sigma gamma h2 hsigma] at hDegree
  apply hqe
  rw [← Int.natCast_dvd_natCast]
  exact ⟨_, by simpa using hDegree.symm⟩

/-- Odd-prime independence of the two shifted trace-coordinate classes.  The
affine shift disappears after taking norms; the remaining residual ratio is
the same height-one-prime obstruction as in the pinned BGS argument. -/
theorem shiftedTraceBaseCoordinates_mixedPower_ne_oddPrimePower
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hsigmaOne : sigma ≠ 1)
    (q a b : ℕ) (hq : q.Prime) (hqTwo : q ≠ 2)
    (haq : a < q) (hbq : b < q) (hab : a ≠ 0 ∨ b ≠ 0)
    (z : ShiftedTraceBaseFunctionField sigma gamma) :
    letI : Fact (Irreducible
        (shiftedTraceBasePolynomial sigma gamma)) :=
      ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
    z ^ q ≠
      (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma) ^ a *
        shiftedTraceBaseV sigma gamma ^ b := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  let baseField := ShiftedTraceBaseFunctionField sigma gamma
  let U : baseField := shiftedTraceBaseU sigma gamma
  let V : baseField := shiftedTraceBaseV sigma gamma
  have hV : V ≠ 0 := by
    intro hzero
    change shiftedTraceBaseV sigma gamma = 0 at hzero
    have hquadratic := shiftedTraceBaseV_quadraticEquation
      sigma gamma h2 hsigma
    rw [hzero] at hquadratic
    have hrootNormZero : shiftedTraceRootNorm sigma = 0 :=
      (algebraMap (RatFunc K) baseField).injective (by simpa using hquadratic)
    exact shiftedTraceRootNorm_ne_zero sigma hsigma hrootNormZero
  have hU : U ≠ 0 := by
    exact (map_ne_zero_iff _
      (algebraMap (RatFunc K) baseField).injective).mpr RatFunc.X_ne_zero
  have hUV : U * V ≠ 0 := mul_ne_zero hU hV
  have hrightNonzero : (U * V) ^ a * V ^ b ≠ 0 :=
    mul_ne_zero (pow_ne_zero a hUV) (pow_ne_zero b hV)
  intro hpow
  have hz : z ≠ 0 := by
    intro hzero
    apply hrightNonzero
    simpa [hzero, hq.ne_zero] using hpow.symm
  letI : Module.Finite (RatFunc K) baseField :=
    (shiftedTraceBasePolynomial_monic sigma gamma).finite_adjoinRoot
  have hnorm := congrArg (Algebra.norm (RatFunc K)) hpow
  rw [map_pow, map_mul, map_pow, map_pow] at hnorm
  have hnormZNe : Algebra.norm (RatFunc K) z ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hz
  have hnormUVNe : Algebra.norm (RatFunc K) (U * V) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hUV
  have hnormVNe : Algebra.norm (RatFunc K) V ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hV
  have hdegree := congrArg RatFunc.intDegree hnorm
  rw [RatFunc.intDegree_pow _ hnormZNe,
    RatFunc.intDegree_mul (pow_ne_zero a hnormUVNe) (pow_ne_zero b hnormVNe),
    RatFunc.intDegree_pow _ hnormUVNe,
    RatFunc.intDegree_pow _ hnormVNe,
    norm_shiftedTraceBaseU_mul_V_intDegree sigma gamma h2 hsigma] at hdegree
  have hnormV : Algebra.norm (RatFunc K) V = shiftedTraceRootNorm sigma := by
    simpa [V, baseField] using norm_shiftedTraceBaseV sigma gamma h2 hsigma
  have hnormVIntDegree :
      (Algebra.norm (RatFunc K) V).intDegree = -1 := by
    rw [hnormV, shiftedTraceRootNorm_intDegree sigma hsigma]
  rw [hnormVIntDegree] at hdegree
  have hdiv : (q : ℤ) ∣ (a : ℤ) - (b : ℤ) := by
    refine ⟨(Algebra.norm (RatFunc K) z).intDegree, ?_⟩
    simpa [sub_eq_add_neg, mul_add] using hdegree.symm
  have habEq : a = b := by
    rcases le_total b a with hba | hab'
    · have hdivNat : q ∣ a - b := by
        rw [← Int.natCast_dvd_natCast]
        simpa [Nat.cast_sub hba] using hdiv
      have hzero : a - b = 0 :=
        Nat.eq_zero_of_dvd_of_lt hdivNat
          (lt_of_le_of_lt (Nat.sub_le a b) haq)
      exact Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hzero) hba
    · have hdivNeg : (q : ℤ) ∣ (b : ℤ) - (a : ℤ) := by
        simpa only [neg_sub] using (dvd_neg.mpr hdiv)
      have hdivNat : q ∣ b - a := by
        rw [← Int.natCast_dvd_natCast]
        simpa [Nat.cast_sub hab'] using hdivNeg
      have hzero : b - a = 0 :=
        Nat.eq_zero_of_dvd_of_lt hdivNat
          (lt_of_le_of_lt (Nat.sub_le b a) hbq)
      exact Nat.le_antisymm hab' (Nat.sub_eq_zero_iff_le.mp hzero)
  subst b
  have haPositive : 0 < a := by
    rcases hab with ha | ha <;> exact Nat.pos_of_ne_zero ha
  have hqNotDvdA : ¬ q ∣ a := Nat.not_dvd_of_pos_of_lt haPositive haq
  have hqNotDvdTwoA : ¬ q ∣ 2 * a := by
    intro h
    rcases hq.dvd_mul.mp h with hqDvdTwo | hqDvdA
    · exact hqTwo ((Nat.dvd_prime Nat.prime_two).mp hqDvdTwo |>.resolve_left hq.ne_one)
    · exact hqNotDvdA hqDvdA
  have hnormUV : Algebra.norm (RatFunc K) (U * V) =
      RatFunc.X ^ 2 * shiftedTraceRootNorm sigma := by
    simpa [U, V, baseField] using
      norm_shiftedTraceBaseU_mul_V sigma gamma h2 hsigma
  have hnormResidual :
      (Algebra.norm (RatFunc K) z) ^ q =
        (RatFunc.X * shiftedTraceRootNorm sigma) ^ (2 * a) := by
    calc
      (Algebra.norm (RatFunc K) z) ^ q =
          (Algebra.norm (RatFunc K) (U * V)) ^ a *
            (Algebra.norm (RatFunc K) V) ^ a := hnorm
      _ = (RatFunc.X ^ 2 * shiftedTraceRootNorm sigma) ^ a *
            shiftedTraceRootNorm sigma ^ a := by rw [hnormUV, hnormV]
      _ = (RatFunc.X ^ 2 * shiftedTraceRootNorm sigma ^ 2) ^ a := by
        rw [← mul_pow]
        congr 1
        ring
      _ = ((RatFunc.X * shiftedTraceRootNorm sigma) ^ 2) ^ a := by
        congr 1
        ring
      _ = (RatFunc.X * shiftedTraceRootNorm sigma) ^ (2 * a) :=
        (pow_mul _ 2 a).symm
  apply BGS.Markoff.splitTrace_X_mul_radicand_pow_ne_primePower_of_not_dvd
    sigma hsigma hsigmaOne q (2 * a) hq hqNotDvdTwoA
      (Algebra.norm (RatFunc K) z)
  rw [BGS.Markoff.RatFunc.X_mul_splitTraceRadicand_eq_residualRatio]
  rw [RatFunc.X_mul_shiftedTraceRootNorm_eq_neg_residualRatio] at hnormResidual
  simpa [pow_mul] using hnormResidual

section QuadraticSquareClass

/-- In a quadratic extension defined by `T²+bT+c`, a base element `g` can
become a square only if `g` or `(b²-4c)g` was already a square. -/
theorem not_isSquare_algebraMap_adjoinMonicQuadratic_of_independent
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (b c g : F)
    (hdisc : ¬ IsSquare (b ^ 2 - 4 * c))
    (hg : ¬ IsSquare g)
    (hdiscg : ¬ IsSquare ((b ^ 2 - 4 * c) * g)) :
    ¬ IsSquare
      (algebraMap F (AdjoinRoot (X ^ 2 + C b * X + C c)) g) := by
  let q : Polynomial F := X ^ 2 + C b * X + C c
  have hqIrreducible : Irreducible q :=
    monicQuadratic_irreducible_of_discriminant_not_isSquare b c hdisc
  letI : Fact (Irreducible q) := ⟨hqIrreducible⟩
  have hqMonic : q.Monic := by
    simpa [q] using (isMonicOfDegree_sub_add_two (-b) c).monic
  have hqNatDegree : q.natDegree = 2 := by
    simpa [q] using (isMonicOfDegree_sub_add_two (-b) c).natDegree_eq
  change ¬ IsSquare (algebraMap F (AdjoinRoot q) g)
  let basis : Module.Basis (Fin 2) F (AdjoinRoot q) :=
    (AdjoinRoot.powerBasis' hqMonic).basis.reindex (finCongr hqNatDegree)
  rintro ⟨z, hzSquare⟩
  let x : F := basis.repr z 0
  let y : F := basis.repr z 1
  have hb0 : basis 0 = 1 := by
    simp [basis, PowerBasis.coe_basis]
  have hb1 : basis 1 = AdjoinRoot.root q := by
    simp [basis, PowerBasis.coe_basis]
  have hz : z = algebraMap F (AdjoinRoot q) x +
      algebraMap F (AdjoinRoot q) y * AdjoinRoot.root q := by
    have hsum := basis.sum_repr z
    rw [Fin.sum_univ_two] at hsum
    simpa [hb0, hb1, x, y, Algebra.smul_def] using hsum.symm
  have hroot : (AdjoinRoot.root q) ^ 2 =
      -algebraMap F (AdjoinRoot q) b * AdjoinRoot.root q -
        algebraMap F (AdjoinRoot q) c := by
    have h := AdjoinRoot.eval₂_root q
    simp only [q] at h
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] at h
    rw [← AdjoinRoot.algebraMap_eq] at h
    linear_combination h
  have hexpand :
      algebraMap F (AdjoinRoot q) g =
        algebraMap F (AdjoinRoot q) (x ^ 2 - c * y ^ 2) +
          algebraMap F (AdjoinRoot q) (2 * x * y - b * y ^ 2) *
            AdjoinRoot.root q := by
    rw [hzSquare, hz]
    rw [show (algebraMap F (AdjoinRoot q) x +
          algebraMap F (AdjoinRoot q) y * AdjoinRoot.root q) *
        (algebraMap F (AdjoinRoot q) x +
          algebraMap F (AdjoinRoot q) y * AdjoinRoot.root q) =
        algebraMap F (AdjoinRoot q) (x ^ 2) +
          algebraMap F (AdjoinRoot q) (2 * x * y) * AdjoinRoot.root q +
          algebraMap F (AdjoinRoot q) (y ^ 2) *
            (AdjoinRoot.root q) ^ 2 by
      simp only [map_mul, map_pow, map_ofNat]; ring]
    rw [hroot]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    ring
  have hbasisExpression :
      g • basis 0 = (x ^ 2 - c * y ^ 2) • basis 0 +
        (2 * x * y - b * y ^ 2) • basis 1 := by
    simpa [hb0, hb1, Algebra.smul_def] using hexpand
  have hconstant := congrArg (basis.coord 0) hbasisExpression
  have hlinear := congrArg (basis.coord 1) hbasisExpression
  have hgExpression : g = x ^ 2 - c * y ^ 2 := by
    simpa using hconstant
  have hyFactor : y * (2 * x - b * y) = 0 := by
    have : 2 * x * y - b * y ^ 2 = 0 := by
      simpa using hlinear.symm
    linear_combination this
  rcases mul_eq_zero.mp hyFactor with hy | hrelation
  · apply hg
    refine ⟨x, ?_⟩
    rw [hgExpression, hy]
    ring
  · apply hdiscg
    refine ⟨(b ^ 2 - 4 * c) * y / 2, ?_⟩
    rw [hgExpression]
    have hrelation' : 2 * x - b * y = 0 := hrelation
    field_simp [h2]
    linear_combination
      (b ^ 2 - 4 * c) * (2 * x + b * y) * hrelation'

theorem ratFuncX_not_isSquare : ¬ IsSquare (RatFunc.X : RatFunc K) := by
  rintro ⟨z, hz⟩
  have hz0 : z ≠ 0 := by
    intro hzero
    have hxzero : (RatFunc.X : RatFunc K) = 0 := by
      simpa [hzero] using hz
    exact (RatFunc.X_ne_zero (K := K)) hxzero
  have hpow : z ^ 2 = (RatFunc.X : RatFunc K) := by
    simpa [pow_two] using hz.symm
  have hdegree := congrArg RatFunc.intDegree hpow
  rw [RatFunc.intDegree_pow z hz0 2, RatFunc.intDegree_X] at hdegree
  omega

theorem shiftedTraceBaseDiscriminant_mul_X
    (sigma gamma : K) :
    shiftedTraceBaseDiscriminant sigma gamma * RatFunc.X =
      algebraMap K[X] (RatFunc K)
          (shiftedTraceDiscriminantQuadratic sigma gamma) /
        (1 - RatFunc.X) ^ 2 := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hOneSubX : (1 - RatFunc.X : RatFunc K) ≠ 0 :=
    one_sub_ratFuncX_ne_zero
  simp only [shiftedTraceBaseDiscriminant,
    shiftedTraceBaseDiscriminantNumerator,
    shiftedTraceBaseDiscriminantDenominator, map_mul, map_sub, map_pow,
    map_one, RatFunc.algebraMap_X]
  field_simp [hX, hOneSubX]

theorem shiftedTraceBaseDiscriminant_mul_X_not_isSquare
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0) :
    ¬ IsSquare (shiftedTraceBaseDiscriminant sigma gamma * RatFunc.X) := by
  intro hsquare
  apply shiftedTraceDiscriminantQuadratic_not_isSquare
    sigma gamma h2 hsigma hD2
  rcases hsquare with ⟨z, hz⟩
  refine ⟨z * (1 - RatFunc.X), ?_⟩
  have hOneSubX : (1 - RatFunc.X : RatFunc K) ≠ 0 :=
    one_sub_ratFuncX_ne_zero
  have hidentity := shiftedTraceBaseDiscriminant_mul_X sigma gamma
  have hcleared :
      algebraMap K[X] (RatFunc K)
          (shiftedTraceDiscriminantQuadratic sigma gamma) =
        (shiftedTraceBaseDiscriminant sigma gamma * RatFunc.X) *
          (1 - RatFunc.X) ^ 2 := by
    field_simp [hOneSubX] at hidentity
    exact hidentity.symm
  rw [hcleared, hz]
  ring

/-- The common-even obstruction `D₂` prevents the rational coordinate `U`
from becoming a square in the shifted quadratic function field. -/
theorem shiftedTraceBaseU_not_isSquare
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0) :
    letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
      ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
    ¬ IsSquare (shiftedTraceBaseU sigma gamma) := by
  let hIrred := shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) := ⟨hIrred⟩
  change ¬ IsSquare
    (algebraMap (RatFunc K) (ShiftedTraceBaseFunctionField sigma gamma)
      RatFunc.X)
  apply not_isSquare_algebraMap_adjoinMonicQuadratic_of_independent
    (F := RatFunc K)
    (show (2 : RatFunc K) ≠ 0 by
      intro hzero
      apply h2
      apply RatFunc.C_injective (K := K)
      change algebraMap K (RatFunc K) (2 : K) =
        algebraMap K (RatFunc K) (0 : K)
      simpa only [map_ofNat, map_zero] using hzero)
    (shiftedTraceBaseLinearCoefficient gamma)
    (shiftedTraceRootNorm sigma) RatFunc.X
  · rw [shiftedTraceBasePolynomial_discriminant sigma gamma]
    exact shiftedTraceBaseDiscriminant_not_isSquare sigma gamma h2 hsigma
  · exact ratFuncX_not_isSquare
  · rw [shiftedTraceBasePolynomial_discriminant sigma gamma]
    exact shiftedTraceBaseDiscriminant_mul_X_not_isSquare
      sigma gamma h2 hsigma hD2

end QuadraticSquareClass

end BaseQuadratic

end

end GenMarkoff
