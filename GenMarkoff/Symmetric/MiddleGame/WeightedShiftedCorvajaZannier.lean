import GenMarkoff.Symmetric.MiddleGame.ShiftedCorvajaZannier

/-!
# Arbitrary-weight shifted Corvaja--Zannier

The concrete one-step orbit parameter need not start in the normalized
coordinate used by `ShiftedCorvajaZannier`.  Its adjacent trace has the form

`alpha * h + beta * h⁻¹ + gamma`.

Scaling `h` by `alpha` normalizes the equation and replaces the two weights
by their product `sigma = alpha * beta`.  That scaling sends a subgroup to a
coset, so it cannot be used to replace the finite solution set by the monic
one.  Instead this file transports only the geometric proof across the
scaling and applies the general Corvaja--Zannier theorem directly to the
original subgroup coordinates.
-/

namespace GenMarkoff.Symmetric.MiddleGame

open BGS.Markoff Polynomial

noncomputable section

section GeometricPolynomial

variable {K : Type*} [Field K]

/-- The degree-one shifted trace curve with both weights retained, in torus
coordinate order `(k,h)`. -/
def weightedShiftedTraceTorusClosurePolynomial
    (alpha beta gamma : K) : MvPolynomial (Fin 2) K :=
  shiftedTraceCoverPolynomial alpha beta gamma 1 1

/-- On nonzero coordinates, the arbitrary-weight cleared polynomial is
exactly the shifted trace equation. -/
theorem eval_weightedShiftedTraceTorusClosurePolynomial_eq_zero_iff
    (alpha beta gamma : K) (k h : Kˣ) :
    MvPolynomial.eval ![(k : K), (h : K)]
        (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma) = 0 ↔
      weightedSplitTorusTrace alpha beta h + gamma = splitTorusTrace k := by
  rw [weightedShiftedTraceTorusClosurePolynomial,
    eval_shiftedTraceCoverPolynomial]
  simp only [pow_one, weightedSplitTorusTrace, splitTorusTrace,
    Units.val_inv_eq_inv_val]
  have hk : (k : K) ≠ 0 := Units.ne_zero k
  have hh : (h : K) ≠ 0 := Units.ne_zero h
  field_simp [hk, hh]
  constructor <;> intro heq <;> linear_combination heq

/-- The arbitrary-weight degree-one cover in iterated-polynomial form, with
the right torus coordinate outermost. -/
def weightedShiftedTraceDegreeOneIteratedPolynomial
    (alpha beta gamma : K) : Polynomial K[X] :=
  monomial 2 (-X) +
    monomial 1 (C alpha * X ^ 2 + C gamma * X + C beta) + C (-X)

theorem finTwoToIteratedPolynomial_weightedShiftedTraceDegreeOne
    (alpha beta gamma : K) :
    BGS.Markoff.finTwoToIteratedPolynomial
        (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma) =
      weightedShiftedTraceDegreeOneIteratedPolynomial alpha beta gamma := by
  simp only [weightedShiftedTraceTorusClosurePolynomial,
    shiftedTraceCoverPolynomial, map_add, map_sub, map_mul, map_pow,
    BGS.Markoff.finTwoToIteratedPolynomial_C,
    BGS.Markoff.finTwoToIteratedPolynomial_X_zero,
    BGS.Markoff.finTwoToIteratedPolynomial_X_one]
  simp only [pow_one, weightedShiftedTraceDegreeOneIteratedPolynomial,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [Polynomial.C_mul, Polynomial.C_add,
    Polynomial.C_neg, Polynomial.C_pow]
  ring

/-- Scaling the coefficient variable by `alpha` sends the monic shifted
polynomial with `sigma = alpha * beta` to `alpha` times the original weighted
polynomial. -/
theorem mapAlgEquiv_scale_shiftedTraceDegreeOneIteratedPolynomial
    (alpha beta gamma : K) (halpha : alpha ≠ 0) :
    Polynomial.mapAlgEquiv
        (BGS.Markoff.polynomialVariableScaleEquiv (Units.mk0 alpha halpha))
        (shiftedTraceDegreeOneIteratedPolynomial (alpha * beta) gamma) =
      C (C alpha) *
        weightedShiftedTraceDegreeOneIteratedPolynomial alpha beta gamma := by
  simp [BGS.Markoff.polynomialVariableScaleEquiv,
    shiftedTraceDegreeOneIteratedPolynomial,
    weightedShiftedTraceDegreeOneIteratedPolynomial,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

/-- Irreducibility of the arbitrary-weight degree-one curve follows from the
monic shifted curve by the invertible coefficient-variable scaling. -/
theorem weightedShiftedTraceDegreeOneIteratedPolynomial_irreducible
    (alpha beta gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : alpha * beta ≠ 0)
    (hD2 : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0) :
    Irreducible
      (weightedShiftedTraceDegreeOneIteratedPolynomial alpha beta gamma) := by
  have halpha : alpha ≠ 0 := left_ne_zero_of_mul hsigma
  let alphaUnit : Kˣ := Units.mk0 alpha halpha
  have hmonic :=
    shiftedTraceDegreeOneIteratedPolynomial_irreducible
      (alpha * beta) gamma h2 hsigma hD2
  have hscaled := hmonic.map
    (Polynomial.mapAlgEquiv
      (BGS.Markoff.polynomialVariableScaleEquiv alphaUnit))
  have hscale :
      Polynomial.mapAlgEquiv
          (BGS.Markoff.polynomialVariableScaleEquiv alphaUnit)
          (shiftedTraceDegreeOneIteratedPolynomial (alpha * beta) gamma) =
        C (C alpha) *
          weightedShiftedTraceDegreeOneIteratedPolynomial alpha beta gamma := by
    simpa [alphaUnit] using
      mapAlgEquiv_scale_shiftedTraceDegreeOneIteratedPolynomial
        alpha beta gamma halpha
  rw [hscale] at hscaled
  have hinnerUnit : IsUnit (C alpha : K[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr halpha)
  have houterUnit : IsUnit (C (C alpha) : Polynomial K[X]) :=
    Polynomial.isUnit_C.mpr hinnerUnit
  exact (irreducible_isUnit_mul houterUnit).mp hscaled

/-- The arbitrary-weight degree-one shifted cover is irreducible over its
ground field under the exact normalized branch-discriminant conditions. -/
theorem weightedShiftedTraceTorusClosurePolynomial_irreducible
    (alpha beta gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : alpha * beta ≠ 0)
    (hD2 : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0) :
    Irreducible
      (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma) := by
  have himage :=
    finTwoToIteratedPolynomial_weightedShiftedTraceDegreeOne
      alpha beta gamma
  have hiterated :=
    weightedShiftedTraceDegreeOneIteratedPolynomial_irreducible
      alpha beta gamma h2 hsigma hD2
  rw [← himage] at hiterated
  have hback := hiterated.map
    (BGS.Markoff.finTwoToIteratedPolynomial (K := K)).symm
  simpa using hback

/-- The arbitrary-weight shifted curve stays irreducible over the algebraic
closure.  Its normalized parameter is precisely `sigma = alpha * beta`. -/
theorem weightedShiftedTraceTorusClosurePolynomial_absolutelyIrreducible
    (alpha beta gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : alpha * beta ≠ 0)
    (hD2 : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma)) := by
  let phi : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  rw [weightedShiftedTraceTorusClosurePolynomial,
    map_shiftedTraceCoverPolynomial phi alpha beta gamma 1 1]
  have h2L : (2 : AlgebraicClosure K) ≠ 0 := by
    change phi (2 : K) ≠ 0
    exact (map_ne_zero_iff phi phi.injective).mpr h2
  have hsigmaL : phi alpha * phi beta ≠ 0 := by
    simpa only [map_mul] using
      (map_ne_zero_iff phi phi.injective).mpr hsigma
  have hD2L :
      shiftedTraceEvenObstruction (phi alpha * phi beta) (phi gamma) ≠ 0 := by
    have hmap : phi (shiftedTraceEvenObstruction
        (alpha * beta) gamma) ≠ 0 :=
      (map_ne_zero_iff phi phi.injective).mpr hD2
    simpa [shiftedTraceEvenObstruction, map_ofNat] using hmap
  exact weightedShiftedTraceTorusClosurePolynomial_irreducible
    (phi alpha) (phi beta) (phi gamma) h2L hsigmaL hD2L

/-- Arbitrary-weight degree-one irreducibility under the sharp non-toric
hypothesis.  The common-even discriminant is unnecessary at exponent
`(1,1)`. -/
theorem
    weightedShiftedTraceDegreeOneIteratedPolynomial_irreducible_of_not_toric
    (alpha beta gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : alpha * beta ≠ 0)
    (hnotToric : ¬ (alpha * beta = 1 ∧ gamma = 0)) :
    Irreducible
      (weightedShiftedTraceDegreeOneIteratedPolynomial alpha beta gamma) := by
  have halpha : alpha ≠ 0 := left_ne_zero_of_mul hsigma
  let alphaUnit : Kˣ := Units.mk0 alpha halpha
  have hmonic :=
    shiftedTraceDegreeOneIteratedPolynomial_irreducible_of_not_toric
      (alpha * beta) gamma h2 hsigma hnotToric
  have hscaled := hmonic.map
    (Polynomial.mapAlgEquiv
      (BGS.Markoff.polynomialVariableScaleEquiv alphaUnit))
  have hscale :
      Polynomial.mapAlgEquiv
          (BGS.Markoff.polynomialVariableScaleEquiv alphaUnit)
          (shiftedTraceDegreeOneIteratedPolynomial (alpha * beta) gamma) =
        C (C alpha) *
          weightedShiftedTraceDegreeOneIteratedPolynomial alpha beta gamma := by
    simpa [alphaUnit] using
      mapAlgEquiv_scale_shiftedTraceDegreeOneIteratedPolynomial
        alpha beta gamma halpha
  rw [hscale] at hscaled
  have hinnerUnit : IsUnit (C alpha : K[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr halpha)
  have houterUnit : IsUnit (C (C alpha) : Polynomial K[X]) :=
    Polynomial.isUnit_C.mpr hinnerUnit
  exact (irreducible_isUnit_mul houterUnit).mp hscaled

/-- Ground-field irreducibility of the arbitrary-weight degree-one curve
outside the unique normalized toric pair. -/
theorem
    weightedShiftedTraceTorusClosurePolynomial_irreducible_of_not_toric
    (alpha beta gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : alpha * beta ≠ 0)
    (hnotToric : ¬ (alpha * beta = 1 ∧ gamma = 0)) :
    Irreducible
      (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma) := by
  have himage :=
    finTwoToIteratedPolynomial_weightedShiftedTraceDegreeOne
      alpha beta gamma
  have hiterated :=
    weightedShiftedTraceDegreeOneIteratedPolynomial_irreducible_of_not_toric
      alpha beta gamma h2 hsigma hnotToric
  rw [← himage] at hiterated
  have hback := hiterated.map
    (BGS.Markoff.finTwoToIteratedPolynomial (K := K)).symm
  simpa using hback

/-- Absolute irreducibility of the arbitrary-weight degree-one curve outside
the normalized toric pair. -/
theorem
    weightedShiftedTraceTorusClosurePolynomial_absolutelyIrreducible_of_not_toric
    (alpha beta gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : alpha * beta ≠ 0)
    (hnotToric : ¬ (alpha * beta = 1 ∧ gamma = 0)) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma)) := by
  let phi : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  rw [weightedShiftedTraceTorusClosurePolynomial,
    map_shiftedTraceCoverPolynomial phi alpha beta gamma 1 1]
  have h2L : (2 : AlgebraicClosure K) ≠ 0 := by
    change phi (2 : K) ≠ 0
    exact (map_ne_zero_iff phi phi.injective).mpr h2
  have hsigmaL : phi alpha * phi beta ≠ 0 := by
    simpa only [map_mul] using
      (map_ne_zero_iff phi phi.injective).mpr hsigma
  have hnotToricL :
      ¬ (phi alpha * phi beta = 1 ∧ phi gamma = 0) := by
    rintro ⟨hsigmaOne, hgammaZero⟩
    apply hnotToric
    constructor
    · apply phi.injective
      simpa only [map_mul, map_one] using hsigmaOne
    · apply phi.injective
      simpa only [map_zero] using hgammaZero
  exact
    weightedShiftedTraceTorusClosurePolynomial_irreducible_of_not_toric
      (phi alpha) (phi beta) (phi gamma)
        h2L hsigmaL hnotToricL

end GeometricPolynomial

section NonSubtorus

variable {K : Type*} [Field K]

/-- Scaling the left coordinate transports the monic non-subtorus theorem
back to the original arbitrary-weight equation.  The target character
constant is adjusted by `alpha ^ b`; no subgroup is scaled here. -/
theorem weightedShiftedTraceCurve_notSubtorusTranslate
    (alpha beta gamma : K) (hsigma : alpha * beta ≠ 0) :
    ∀ (a b : ℤ), (a ≠ 0 ∨ b ≠ 0) →
      ∀ c : (AlgebraicClosure K)ˣ,
        ∃ k h : (AlgebraicClosure K)ˣ,
          weightedSplitTorusTrace
              (algebraMap K (AlgebraicClosure K) alpha)
              (algebraMap K (AlgebraicClosure K) beta) h +
              algebraMap K (AlgebraicClosure K) gamma = splitTorusTrace k ∧
          k ^ a * h ^ b ≠ c := by
  let phi : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let alphaL : AlgebraicClosure K := phi alpha
  let betaL : AlgebraicClosure K := phi beta
  let gammaL : AlgebraicClosure K := phi gamma
  have halpha : alpha ≠ 0 := left_ne_zero_of_mul hsigma
  have halphaL : alphaL ≠ 0 :=
    (map_ne_zero_iff phi phi.injective).mpr halpha
  let q : (AlgebraicClosure K)ˣ := Units.mk0 alphaL halphaL
  intro a b hab c
  obtain ⟨k, h, hcurve, hcharacter⟩ :=
    shiftedWeightedTraceCurve_notSubtorusTranslate
      (alpha * beta) gamma hsigma a b hab (q ^ b * c)
  have hcurve' :
      weightedSplitTorusTrace 1 (alphaL * betaL) h + gammaL =
        splitTorusTrace k := by
    simpa only [alphaL, betaL, gammaL, phi, map_mul] using hcurve
  refine ⟨k, q⁻¹ * h, ?_, ?_⟩
  · have hscale :
        weightedSplitTorusTrace alphaL betaL (q⁻¹ * h) =
          weightedSplitTorusTrace 1 (alphaL * betaL) h := by
      simp only [weightedSplitTorusTrace, Units.val_mul,
        Units.val_inv_eq_inv_val, Units.val_mk0, q]
      field_simp [halphaL, Units.ne_zero h]
    rw [hscale]
    exact hcurve'
  · intro hbad
    apply hcharacter
    calc
      k ^ a * h ^ b = q ^ b * (k ^ a * (q⁻¹ * h) ^ b) := by
        calc
          k ^ a * h ^ b =
              (q ^ b * (q ^ b)⁻¹) * (k ^ a * h ^ b) := by simp
          _ = q ^ b * (k ^ a * ((q ^ b)⁻¹ * h ^ b)) := by
            rw [mul_assoc]
            congr 1
            rw [← mul_assoc, mul_comm (q ^ b)⁻¹ (k ^ a), mul_assoc]
          _ = q ^ b * (k ^ a * ((q⁻¹) ^ b * h ^ b)) := by
            rw [inv_zpow]
          _ = q ^ b * (k ^ a * (q⁻¹ * h) ^ b) := by
            rw [mul_zpow]
      _ = q ^ b * c := by rw [hbad]

/-- The scaled equation-level theorem supplies the general plane-curve
non-subtorus condition for the polynomial in the original coordinates. -/
theorem weightedShiftedTraceTorusClosurePolynomial_notSubtorusTranslate
    (alpha beta gamma : K) (hsigma : alpha * beta ≠ 0) :
    BGS.External.TorusCurveNotSubtorusTranslate
      (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma) := by
  intro a b hab c
  obtain ⟨k, h, hcurve, hcharacter⟩ :=
    weightedShiftedTraceCurve_notSubtorusTranslate
      alpha beta gamma hsigma a b hab c
  refine ⟨k, h, ?_, hcharacter⟩
  rw [weightedShiftedTraceTorusClosurePolynomial,
    map_shiftedTraceCoverPolynomial]
  exact
    (eval_weightedShiftedTraceTorusClosurePolynomial_eq_zero_iff
      (algebraMap K (AlgebraicClosure K) alpha)
      (algebraMap K (AlgebraicClosure K) beta)
      (algebraMap K (AlgebraicClosure K) gamma) k h).2 hcurve

end NonSubtorus

section PlaneCurveHypotheses

variable {K : Type*} [Field K]

theorem weightedShiftedTraceTorusClosurePolynomial_pderiv_first_ne_zero
    (alpha beta gamma : K) (hbeta : beta ≠ 0) :
    MvPolynomial.pderiv 0
      (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma) ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval ![(0 : K), (0 : K)]) hzero
  simp [weightedShiftedTraceTorusClosurePolynomial,
    shiftedTraceCoverPolynomial] at heval
  exact hbeta heval

theorem weightedShiftedTraceTorusClosurePolynomial_pderiv_second_ne_zero
    (alpha beta gamma : K) :
    MvPolynomial.pderiv 1
      (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma) ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval ![(0 : K), (0 : K)]) hzero
  simp [weightedShiftedTraceTorusClosurePolynomial,
    shiftedTraceCoverPolynomial] at heval

private theorem weightedShiftedTraceShiftMonomial_degreeOf_first_le_two
    (gamma : K) :
    MvPolynomial.degreeOf (0 : Fin 2)
        (MvPolynomial.C gamma * MvPolynomial.X 0 * MvPolynomial.X 1) ≤ 2 := by
  calc
    _ ≤ MvPolynomial.degreeOf (0 : Fin 2)
          (MvPolynomial.C gamma * MvPolynomial.X 0) +
        MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 1) :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ (MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.C gamma) +
          MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 0)) +
        MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 1) := by
      gcongr
      exact MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ 2 := by
      rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X,
        MvPolynomial.degreeOf_X]
      norm_num

private theorem weightedShiftedTraceShiftMonomial_degreeOf_second_le_two
    (gamma : K) :
    MvPolynomial.degreeOf (1 : Fin 2)
        (MvPolynomial.C gamma * MvPolynomial.X 0 * MvPolynomial.X 1) ≤ 2 := by
  calc
    _ ≤ MvPolynomial.degreeOf (1 : Fin 2)
          (MvPolynomial.C gamma * MvPolynomial.X 0) +
        MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 1) :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ (MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.C gamma) +
          MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 0)) +
        MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 1) := by
      gcongr
      exact MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ 2 := by
      rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X,
        MvPolynomial.degreeOf_X]
      norm_num

private theorem weightedShiftedTraceTorusClosurePolynomial_eq_unshifted_add
    (alpha beta gamma : K) :
    weightedShiftedTraceTorusClosurePolynomial alpha beta gamma =
      splitTraceCoverPolynomial alpha beta 1 1 +
        MvPolynomial.C gamma * MvPolynomial.X 0 * MvPolynomial.X 1 := by
  simp [weightedShiftedTraceTorusClosurePolynomial,
    shiftedTraceCoverPolynomial, splitTraceCoverPolynomial]
  ring

theorem weightedShiftedTraceTorusClosurePolynomial_hasBidegreeAtMost
    (alpha beta gamma : K) :
    BGS.External.HasBidegreeAtMost
      (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma) 2 2 := by
  have hfirst : MvPolynomial.degreeOf (0 : Fin 2)
      (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma) ≤ 2 := by
    rw [weightedShiftedTraceTorusClosurePolynomial_eq_unshifted_add]
    refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
    · simpa using
        (splitTraceCoverPolynomial_degreeOf_first_le alpha beta 1 1)
    · exact weightedShiftedTraceShiftMonomial_degreeOf_first_le_two gamma
  have hsecond : MvPolynomial.degreeOf (1 : Fin 2)
      (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma) ≤ 2 := by
    rw [weightedShiftedTraceTorusClosurePolynomial_eq_unshifted_add]
    refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
    · simpa using
        (splitTraceCoverPolynomial_degreeOf_second_le alpha beta 1 1)
    · exact weightedShiftedTraceShiftMonomial_degreeOf_second_le_two gamma
  intro monomial hmonomial
  exact ⟨
    (MvPolynomial.degreeOf_le_iff.mp hfirst) monomial hmonomial,
    (MvPolynomial.degreeOf_le_iff.mp hsecond) monomial hmonomial⟩

/-- All general Corvaja--Zannier hypotheses for the arbitrary-weight shifted
curve, expressed through the normalized product `sigma = alpha * beta`. -/
theorem weightedShiftedTraceCurve_isCorvajaZannierPlaneCurve
    (alpha beta gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : alpha * beta ≠ 0)
    (hD2 : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0) :
    BGS.External.IsCorvajaZannierPlaneCurve
      (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma) := by
  have hbeta : beta ≠ 0 := right_ne_zero_of_mul hsigma
  exact ⟨
    weightedShiftedTraceTorusClosurePolynomial_absolutelyIrreducible
      alpha beta gamma h2 hsigma hD2,
    weightedShiftedTraceTorusClosurePolynomial_notSubtorusTranslate
      alpha beta gamma hsigma,
    weightedShiftedTraceTorusClosurePolynomial_pderiv_first_ne_zero
      alpha beta gamma hbeta,
    weightedShiftedTraceTorusClosurePolynomial_pderiv_second_ne_zero
      alpha beta gamma⟩

/-- Sharp degree-one Corvaja--Zannier package.  Only the genuinely toric
normalized pair is excluded; a vanishing common-even discriminant alone is
harmless in the middle game. -/
theorem weightedShiftedTraceCurve_isCorvajaZannierPlaneCurve_of_not_toric
    (alpha beta gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : alpha * beta ≠ 0)
    (hnotToric : ¬ (alpha * beta = 1 ∧ gamma = 0)) :
    BGS.External.IsCorvajaZannierPlaneCurve
      (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma) := by
  have hbeta : beta ≠ 0 := right_ne_zero_of_mul hsigma
  exact ⟨
    weightedShiftedTraceTorusClosurePolynomial_absolutelyIrreducible_of_not_toric
      alpha beta gamma h2 hsigma hnotToric,
    weightedShiftedTraceTorusClosurePolynomial_notSubtorusTranslate
      alpha beta gamma hsigma,
    weightedShiftedTraceTorusClosurePolynomial_pderiv_first_ne_zero
      alpha beta gamma hbeta,
    weightedShiftedTraceTorusClosurePolynomial_pderiv_second_ne_zero
      alpha beta gamma⟩

end PlaneCurveHypotheses

section FiniteSubgroupSolutions

variable {E : Type*} [Field E] [Fintype E] [DecidableEq E]

/-- An arbitrary-weight shifted subgroup solution, with coordinates swapped
to geometric order `(k,h)`, belongs to the corresponding torsion
intersection. -/
theorem weightedShiftedTraceSubgroupSolutionToCurvePoint_mem_torsionIntersection
    (alpha beta gamma : E) (H₁ H₂ : Subgroup Eˣ) (z : H₁ × H₂)
    (hz : z ∈
      shiftedWeightedTraceEquationSolutions alpha beta gamma H₁ H₂) :
    weightedTraceSubgroupSolutionToCurvePoint H₁ H₂ z ∈
      BGS.External.torusCurveTorsionIntersection E
        (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma)
        (Nat.card H₂) (Nat.card H₁) := by
  letI := Fintype.ofFinite H₁
  letI := Fintype.ofFinite H₂
  rw [BGS.External.mem_torusCurveTorsionIntersection_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply
      (eval_weightedShiftedTraceTorusClosurePolynomial_eq_zero_iff
        alpha beta gamma z.2 z.1).2
    exact mem_shiftedWeightedTraceEquationSolutions_iff.mp hz
  · have hpow : z.2 ^ Fintype.card H₂ = 1 := pow_card_eq_one
    have hval := congrArg (fun u : H₂ ↦ (u : Eˣ)) hpow
    change ((z.2 : Eˣ) ^ Fintype.card H₂) = 1 at hval
    simpa only [weightedTraceSubgroupSolutionToCurvePoint,
      Fintype.card_eq_nat_card] using hval
  · have hpow : z.1 ^ Fintype.card H₁ = 1 := pow_card_eq_one
    have hval := congrArg (fun u : H₁ ↦ (u : Eˣ)) hpow
    change ((z.1 : Eˣ) ^ Fintype.card H₁) = 1 at hval
    simpa only [weightedTraceSubgroupSolutionToCurvePoint,
      Fintype.card_eq_nat_card] using hval

/-- The original-coordinate shifted solution set injects into the general
torsion intersection without scaling either subgroup. -/
theorem weightedShiftedTraceEquationSolutions_card_le_torsionIntersection
    (alpha beta gamma : E) (H₁ H₂ : Subgroup Eˣ) :
    (shiftedWeightedTraceEquationSolutions
      alpha beta gamma H₁ H₂).card ≤
      (BGS.External.torusCurveTorsionIntersection E
        (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma)
        (Nat.card H₂) (Nat.card H₁)).card := by
  classical
  exact Finset.card_le_card_of_injOn
    (weightedTraceSubgroupSolutionToCurvePoint H₁ H₂)
    (fun z hz ↦
      weightedShiftedTraceSubgroupSolutionToCurvePoint_mem_torsionIntersection
        alpha beta gamma H₁ H₂ z hz)
    (weightedTraceSubgroupSolutionToCurvePoint_injective H₁ H₂).injOn

end FiniteSubgroupSolutions

section CorvajaZannierBound

/-- The general Corvaja--Zannier theorem gives the coefficient-`48` envelope
for the arbitrary-weight shifted curve.  Geometric nondegeneracy depends
only on `sigma = alpha * beta` and `gamma`. -/
theorem weightedShiftedTraceTorsionIntersection_card_cast_le
    (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] [Fintype E] [DecidableEq E] [CharP E p]
    (alpha beta gamma : E) (firstOrder secondOrder : ℕ)
    (hpTwo : p ≠ 2) (hsigma : alpha * beta ≠ 0)
    (hD2 : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0)
    (hfirstPositive : 0 < firstOrder)
    (hsecondPositive : 0 < secondOrder)
    (hfirstPrime : ¬ p ∣ firstOrder)
    (hsecondPrime : ¬ p ∣ secondOrder) :
    ((BGS.External.torusCurveTorsionIntersection E
      (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma)
      firstOrder secondOrder).card : ℝ) ≤
        corvajaZannierTraceUpperBound p secondOrder firstOrder := by
  have hRingChar : ringChar E ≠ 2 := by
    rw [ringChar.eq E p]
    exact hpTwo
  have h2 : (2 : E) ≠ 0 := Ring.two_ne_zero hRingChar
  have hsource :=
    BGS.CorvajaZannier.generalCorvajaZannierPlaneCurveTheorem p E
      (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma)
      2 2 firstOrder secondOrder (by norm_num) (by norm_num)
      (weightedShiftedTraceTorusClosurePolynomial_hasBidegreeAtMost
        alpha beta gamma)
      (weightedShiftedTraceCurve_isCorvajaZannierPlaneCurve
        alpha beta gamma h2 hsigma hD2)
      hfirstPositive hsecondPositive hfirstPrime hsecondPrime
  rw [show BGS.External.planeTorusEulerCharacteristicBound 2 2 = 8 by
    norm_num [BGS.External.planeTorusEulerCharacteristicBound]] at hsource
  exact hsource.trans <| by
    simpa [corvajaZannierTraceUpperBound,
      mul_comm, mul_left_comm, mul_assoc] using
      (corvajaZannierCorollaryTwoNumericalBound_bidegree_two_euler_eight_le
        p firstOrder secondOrder)

/-- Sharp degree-one version of
`weightedShiftedTraceTorsionIntersection_card_cast_le`: the middle-game curve
only has to avoid the genuinely toric normalized pair. -/
theorem weightedShiftedTraceTorsionIntersection_card_cast_le_of_not_toric
    (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] [Fintype E] [DecidableEq E] [CharP E p]
    (alpha beta gamma : E) (firstOrder secondOrder : ℕ)
    (hpTwo : p ≠ 2) (hsigma : alpha * beta ≠ 0)
    (hnotToric : ¬ (alpha * beta = 1 ∧ gamma = 0))
    (hfirstPositive : 0 < firstOrder)
    (hsecondPositive : 0 < secondOrder)
    (hfirstPrime : ¬ p ∣ firstOrder)
    (hsecondPrime : ¬ p ∣ secondOrder) :
    ((BGS.External.torusCurveTorsionIntersection E
      (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma)
      firstOrder secondOrder).card : ℝ) ≤
        corvajaZannierTraceUpperBound p secondOrder firstOrder := by
  have hRingChar : ringChar E ≠ 2 := by
    rw [ringChar.eq E p]
    exact hpTwo
  have h2 : (2 : E) ≠ 0 := Ring.two_ne_zero hRingChar
  have hsource :=
    BGS.CorvajaZannier.generalCorvajaZannierPlaneCurveTheorem p E
      (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma)
      2 2 firstOrder secondOrder (by norm_num) (by norm_num)
      (weightedShiftedTraceTorusClosurePolynomial_hasBidegreeAtMost
        alpha beta gamma)
      (weightedShiftedTraceCurve_isCorvajaZannierPlaneCurve_of_not_toric
        alpha beta gamma h2 hsigma hnotToric)
      hfirstPositive hsecondPositive hfirstPrime hsecondPrime
  rw [show BGS.External.planeTorusEulerCharacteristicBound 2 2 = 8 by
    norm_num [BGS.External.planeTorusEulerCharacteristicBound]] at hsource
  exact hsource.trans <| by
    simpa [corvajaZannierTraceUpperBound,
      mul_comm, mul_left_comm, mul_assoc] using
      (corvajaZannierCorollaryTwoNumericalBound_bidegree_two_euler_eight_le
        p firstOrder secondOrder)

/-- Coefficient-`48` Corvaja--Zannier bound for the actual, unscaled
subgroups in the equation
`alpha*h + beta*h⁻¹ + gamma = k + k⁻¹`.

The exact geometric hypotheses are characteristic different from two,
`sigma = alpha * beta ≠ 0`, and
`shiftedTraceEvenObstruction sigma gamma ≠ 0`. -/
theorem weightedShiftedTraceEquationSolutions_card_cast_le_corvajaZannier
    (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] [Fintype E] [DecidableEq E] [CharP E p]
    (alpha beta gamma : E) (H₁ H₂ : Subgroup Eˣ)
    (hpTwo : p ≠ 2) (hsigma : alpha * beta ≠ 0)
    (hD2 : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0) :
    ((shiftedWeightedTraceEquationSolutions
      alpha beta gamma H₁ H₂).card : ℝ) ≤
        corvajaZannierTraceUpperBound p (Nat.card H₁) (Nat.card H₂) := by
  have hfinite :
      ((shiftedWeightedTraceEquationSolutions
        alpha beta gamma H₁ H₂).card : ℝ) ≤
        ((BGS.External.torusCurveTorsionIntersection E
          (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma)
          (Nat.card H₂) (Nat.card H₁)).card : ℝ) := by
    exact_mod_cast
      weightedShiftedTraceEquationSolutions_card_le_torsionIntersection
        alpha beta gamma H₁ H₂
  obtain ⟨hH₁Prime, hH₂Prime⟩ :=
    weightedTraceCurveTorsionIntersection_orders_primeToCharacteristic
      p H₁ H₂
  have htorus := weightedShiftedTraceTorsionIntersection_card_cast_le
    p E alpha beta gamma (Nat.card H₂) (Nat.card H₁)
      hpTwo hsigma hD2 Nat.card_pos Nat.card_pos hH₂Prime hH₁Prime
  exact hfinite.trans htorus

/-- Sharp degree-one Corvaja--Zannier bound for the actual subgroups.  In
contrast with the power-cover endgame, a singular branch quadratic is harmless
unless the normalized shifted trace equation is exactly toric. -/
theorem weightedShiftedTraceEquationSolutions_card_cast_le_corvajaZannier_of_not_toric
    (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] [Fintype E] [DecidableEq E] [CharP E p]
    (alpha beta gamma : E) (H₁ H₂ : Subgroup Eˣ)
    (hpTwo : p ≠ 2) (hsigma : alpha * beta ≠ 0)
    (hnotToric : ¬ (alpha * beta = 1 ∧ gamma = 0)) :
    ((shiftedWeightedTraceEquationSolutions
      alpha beta gamma H₁ H₂).card : ℝ) ≤
        corvajaZannierTraceUpperBound p (Nat.card H₁) (Nat.card H₂) := by
  have hfinite :
      ((shiftedWeightedTraceEquationSolutions
        alpha beta gamma H₁ H₂).card : ℝ) ≤
        ((BGS.External.torusCurveTorsionIntersection E
          (weightedShiftedTraceTorusClosurePolynomial alpha beta gamma)
          (Nat.card H₂) (Nat.card H₁)).card : ℝ) := by
    exact_mod_cast
      weightedShiftedTraceEquationSolutions_card_le_torsionIntersection
        alpha beta gamma H₁ H₂
  obtain ⟨hH₁Prime, hH₂Prime⟩ :=
    weightedTraceCurveTorsionIntersection_orders_primeToCharacteristic
      p H₁ H₂
  have htorus :=
    weightedShiftedTraceTorsionIntersection_card_cast_le_of_not_toric
      p E alpha beta gamma (Nat.card H₂) (Nat.card H₁)
        hpTwo hsigma hnotToric Nat.card_pos Nat.card_pos hH₂Prime hH₁Prime
  exact hfinite.trans htorus

end CorvajaZannierBound

end

end GenMarkoff.Symmetric.MiddleGame
