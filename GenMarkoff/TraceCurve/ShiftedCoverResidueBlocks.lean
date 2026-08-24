import GenMarkoff.TraceCurve.ShiftedCoverAbsoluteIrreducibility

/-!
# Residue-block division for shifted trace covers

The affine shift changes the degree-one base curve, but it does not change
the rectangular reduction of powers of the two Kummer coordinates.  This
module proves the missing source-kernel inclusion by combining:

* the exact degree-one kernel at the generic point `(U * V, V)`;
* residue classes of the two source exponents modulo `d` and `e`;
* linear independence of the bounded Kummer monomials.

Unlike the unshifted odd-coprime proof, no coprimality or parity assumption is
used.  The needed independence is supplied by the already-proved
irreducibility of both shifted Kummer polynomials.
-/

namespace GenMarkoff

open Polynomial AdjoinRoot IntermediateField

noncomputable section

variable {K : Type*} [Field K]

section DegreeOneKernel

/-- The shifted quadratic coordinate is transcendental over the constant
field.  If it were algebraic, the shifted base equation would make the
rational parameter algebraic over the field it generates, contradicting the
transcendence of `RatFunc.X`. -/
theorem shiftedTraceBaseV_transcendental
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    Transcendental K (shiftedTraceBaseV sigma gamma) := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible
    sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  let U : ShiftedTraceBaseFunctionField sigma gamma :=
    shiftedTraceBaseU sigma gamma
  let V : ShiftedTraceBaseFunctionField sigma gamma :=
    shiftedTraceBaseV sigma gamma
  have hUTrans : Transcendental K U := by
    exact (transcendental_algebraMap_iff
      (algebraMap (RatFunc K)
        (ShiftedTraceBaseFunctionField sigma gamma)).injective).2
          RatFunc.transcendental_X
  intro hVAlg
  let E : IntermediateField K (ShiftedTraceBaseFunctionField sigma gamma) :=
    IntermediateField.adjoin K {V}
  let vE : E := ⟨V, by
    exact IntermediateField.subset_adjoin K {V} (Set.mem_singleton V)⟩
  let p : Polynomial E :=
    C (-(vE ^ 2)) * X ^ 2 +
      C (vE ^ 2 + algebraMap K E gamma * vE + algebraMap K E sigma) * X - 1
  have hpne : p ≠ 0 := by
    intro hpzero
    have hcoeff := congrArg (fun q : Polynomial E => q.coeff 0) hpzero
    simp [p] at hcoeff
  have hUAlgE : IsAlgebraic E U := by
    refine ⟨p, hpne, ?_⟩
    have hbase := shiftedTraceBaseU_V_equation sigma gamma h2 hsigma
    change U * (1 - U) * V ^ 2 +
      algebraMap K (ShiftedTraceBaseFunctionField sigma gamma) gamma * U * V +
      algebraMap K (ShiftedTraceBaseFunctionField sigma gamma) sigma * U - 1 = 0 at hbase
    simp [p, vE]
    linear_combination hbase
  letI : Algebra.IsAlgebraic K E := by
    apply IntermediateField.isAlgebraic_adjoin
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact hVAlg.isIntegral
  have hUAlgK : IsAlgebraic K U := hUAlgE.restrictScalars K
  exact hUTrans hUAlgK

/-- Evaluate source coordinates at the generic shifted base point
`(U * V, V)`. -/
def shiftedTraceBaseResidueEvaluation
    (sigma gamma : K) :
    MvPolynomial (Fin 2) K →ₐ[K]
      ShiftedTraceBaseFunctionField sigma gamma :=
  MvPolynomial.aeval
    ![shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma,
      shiftedTraceBaseV sigma gamma]

private def shiftedTraceBaseVPolynomialEvaluation
    (sigma gamma : K) :
    K[X] →ₐ[K] ShiftedTraceBaseFunctionField sigma gamma :=
  Polynomial.aeval (shiftedTraceBaseV sigma gamma)

private theorem shiftedTraceBaseVPolynomialEvaluation_injective
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    Function.Injective
      (shiftedTraceBaseVPolynomialEvaluation sigma gamma) := by
  exact transcendental_iff_injective.mp
    (shiftedTraceBaseV_transcendental sigma gamma h2 hsigma)

private def shiftedTraceBaseVRatFuncEvaluation
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    RatFunc K →ₐ[K] ShiftedTraceBaseFunctionField sigma gamma := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible
    sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  exact RatFunc.liftAlgHom (K := K) (S := K)
    (L := ShiftedTraceBaseFunctionField sigma gamma)
    (shiftedTraceBaseVPolynomialEvaluation sigma gamma)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (shiftedTraceBaseVPolynomialEvaluation_injective
        sigma gamma h2 hsigma))

private theorem shiftedTraceBaseVRatFuncEvaluation_algebraMap
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (q : K[X]) :
    shiftedTraceBaseVRatFuncEvaluation sigma gamma h2 hsigma
        (algebraMap K[X] (RatFunc K) q) =
      shiftedTraceBaseVPolynomialEvaluation sigma gamma q := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible
    sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  exact RatFunc.liftRingHom_algebraMap _ _ q

/-- Iterated-polynomial evaluation through the rational coefficient field is
the same as evaluation at the generic shifted base point. -/
theorem shiftedTraceBaseResidueIteratedFractionEvaluation
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (p : MvPolynomial (Fin 2) K) :
    Polynomial.eval₂
        (shiftedTraceBaseVRatFuncEvaluation sigma gamma h2 hsigma).toRingHom
        (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma)
        ((BGS.Markoff.finTwoToIteratedPolynomial (K := K) p).map
          (algebraMap K[X] (RatFunc K))) =
      shiftedTraceBaseResidueEvaluation sigma gamma p := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible
    sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  rw [Polynomial.eval₂_map]
  have hcomp :
      (shiftedTraceBaseVRatFuncEvaluation sigma gamma h2 hsigma).toRingHom.comp
          (algebraMap K[X] (RatFunc K)) =
        (shiftedTraceBaseVPolynomialEvaluation sigma gamma).toRingHom := by
    apply DFunLike.ext _ _
    intro q
    exact shiftedTraceBaseVRatFuncEvaluation_algebraMap
      sigma gamma h2 hsigma q
  rw [hcomp]
  exact BGS.Markoff.finTwoToIteratedPolynomial_aeval p
    (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma)
    (shiftedTraceBaseV sigma gamma)

/-- The shifted degree-one cover vanishes at its generic base point. -/
theorem shiftedTraceBaseResidueEvaluation_cover_eq_zero
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    shiftedTraceBaseResidueEvaluation sigma gamma
      (shiftedTraceCoverPolynomial (1 : K) sigma gamma 1 1) = 0 := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible
    sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  have hbase := shiftedTraceBaseU_V_equation sigma gamma h2 hsigma
  have hcover := shiftedTraceCoverRelation_of_powerRootRelations
    (algebraMap K (ShiftedTraceBaseFunctionField sigma gamma) sigma)
    (algebraMap K (ShiftedTraceBaseFunctionField sigma gamma) gamma)
    (shiftedTraceBaseU sigma gamma)
    (shiftedTraceBaseV sigma gamma)
    (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma)
    (shiftedTraceBaseV sigma gamma) 1 1
    (by
      change shiftedTraceBaseU sigma gamma *
          (1 - shiftedTraceBaseU sigma gamma) *
            shiftedTraceBaseV sigma gamma ^ 2 +
        algebraMap K (ShiftedTraceBaseFunctionField sigma gamma) gamma *
            shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma +
        algebraMap K (ShiftedTraceBaseFunctionField sigma gamma) sigma *
            shiftedTraceBaseU sigma gamma - 1 = 0
      exact hbase)
    (by simp) (by simp)
  simpa [shiftedTraceBaseResidueEvaluation,
    shiftedTracePolynomialToKummerTop, MvPolynomial.aeval_def,
    shiftedTraceCoverPolynomial] using hcover

/-- Exact degree-one generic-point kernel.  The proof uses the shifted
degree-one irreducibility theorem and Gauss descent from `K(V)[x]`. -/
theorem shiftedTraceBaseResiduePolynomial_mem_baseCover
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0)
    (p : MvPolynomial (Fin 2) K)
    (hp : shiftedTraceBaseResidueEvaluation sigma gamma p = 0) :
    p ∈ Ideal.span
      {shiftedTraceCoverPolynomial (1 : K) sigma gamma 1 1} := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible
    sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  let q : Polynomial K[X] :=
    shiftedTraceDegreeOneIteratedPolynomial sigma gamma
  let r : Polynomial K[X] :=
    BGS.Markoff.finTwoToIteratedPolynomial (K := K) p
  have hqIrred : Irreducible q :=
    shiftedTraceDegreeOneIteratedPolynomial_irreducible
      sigma gamma h2 hsigma hD2
  have hqPrimitive : q.IsPrimitive :=
    shiftedTraceDegreeOneIteratedPolynomial_isPrimitive sigma gamma hsigma
  have hqFractionIrred :
      Irreducible (q.map (algebraMap K[X] (RatFunc K))) :=
    hqPrimitive.irreducible_iff_irreducible_map_fraction_map.mp hqIrred
  let phi : RatFunc K →ₐ[K] ShiftedTraceBaseFunctionField sigma gamma :=
    shiftedTraceBaseVRatFuncEvaluation sigma gamma h2 hsigma
  letI : Algebra (RatFunc K) (ShiftedTraceBaseFunctionField sigma gamma) :=
    phi.toRingHom.toAlgebra
  have hqRoot : Polynomial.aeval
      (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma)
      (q.map (algebraMap K[X] (RatFunc K))) = 0 := by
    rw [Polynomial.aeval_def]
    change Polynomial.eval₂ phi.toRingHom
      (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma)
      (q.map (algebraMap K[X] (RatFunc K))) = 0
    simpa [phi, q, finTwoToIteratedPolynomial_shiftedTraceDegreeOne] using
      (shiftedTraceBaseResidueIteratedFractionEvaluation
        sigma gamma h2 hsigma
          (shiftedTraceCoverPolynomial (1 : K) sigma gamma 1 1)).trans
            (shiftedTraceBaseResidueEvaluation_cover_eq_zero
              sigma gamma h2 hsigma)
  have hpRoot : Polynomial.aeval
      (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma)
      (r.map (algebraMap K[X] (RatFunc K))) = 0 := by
    rw [Polynomial.aeval_def]
    change Polynomial.eval₂ phi.toRingHom
      (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma)
      (r.map (algebraMap K[X] (RatFunc K))) = 0
    simpa [phi, r] using
      (shiftedTraceBaseResidueIteratedFractionEvaluation
        sigma gamma h2 hsigma p).trans hp
  have hminpoly :
      q.map (algebraMap K[X] (RatFunc K)) *
          C (q.map (algebraMap K[X] (RatFunc K))).leadingCoeff⁻¹ =
        minpoly (RatFunc K)
          (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma) :=
    minpoly.eq_of_irreducible hqFractionIrred hqRoot
  have hqDvdMinpoly :
      q.map (algebraMap K[X] (RatFunc K)) ∣
        minpoly (RatFunc K)
          (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma) :=
    ⟨C (q.map (algebraMap K[X] (RatFunc K))).leadingCoeff⁻¹,
      hminpoly.symm⟩
  have hminpolyDvd :
      minpoly (RatFunc K)
          (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma) ∣
        r.map (algebraMap K[X] (RatFunc K)) :=
    minpoly.dvd (RatFunc K)
      (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma) hpRoot
  have hqDvdFraction :
      q.map (algebraMap K[X] (RatFunc K)) ∣
        r.map (algebraMap K[X] (RatFunc K)) :=
    hqDvdMinpoly.trans hminpolyDvd
  have hqDvd : q ∣ r :=
    hqPrimitive.dvd_of_fraction_map_dvd_fraction_map hqDvdFraction
  rw [Ideal.mem_span_singleton]
  rcases hqDvd with ⟨s, hs⟩
  refine ⟨(BGS.Markoff.finTwoToIteratedPolynomial (K := K)).symm s, ?_⟩
  apply (BGS.Markoff.finTwoToIteratedPolynomial (K := K)).injective
  simpa [q, r, finTwoToIteratedPolynomial_shiftedTraceDegreeOne] using hs

end DegreeOneKernel

section KummerNormalForm

variable (sigma gamma : K) (e d : ℕ) (he : 0 < e) (hd : 0 < d)

theorem shiftedTraceEtaKummerPolynomial_natDegree
    (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    (shiftedTraceEtaKummerPolynomial sigma gamma e).natDegree = e := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible
    sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  change (X ^ e - C (shiftedTraceBaseV sigma gamma)).natDegree = e
  exact natDegree_X_pow_sub_C

theorem shiftedTraceXiKummerPolynomial_natDegree
    (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) (he' : 0 < e) :
    (shiftedTraceXiKummerPolynomial sigma gamma e d).natDegree = d := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible
    sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  letI : Nontrivial (ShiftedTraceEtaFunctionField sigma gamma e) :=
    AdjoinRoot.nontrivial (shiftedTraceEtaKummerPolynomial sigma gamma e) (by
      have hmonic :
          (shiftedTraceEtaKummerPolynomial sigma gamma e).Monic := by
        rw [shiftedTraceEtaKummerPolynomial]
        exact monic_X_pow_sub_C _ (Nat.ne_of_gt he')
      rw [Polynomial.degree_eq_natDegree
        hmonic.ne_zero,
        shiftedTraceEtaKummerPolynomial_natDegree
          sigma gamma e h2 hsigma]
      exact_mod_cast Nat.ne_of_gt he')
  change (X ^ d - C (shiftedTraceXiRadicand sigma gamma e)).natDegree = d
  exact natDegree_X_pow_sub_C

lemma shiftedTraceEtaKummerPolynomial_monic (he' : 0 < e) :
    (shiftedTraceEtaKummerPolynomial sigma gamma e).Monic := by
  letI : CommRing (ShiftedTraceBaseFunctionField sigma gamma) :=
    AdjoinRoot.instCommRing _
  rw [shiftedTraceEtaKummerPolynomial]
  exact monic_X_pow_sub_C _ (Nat.ne_of_gt he')

lemma shiftedTraceXiKummerPolynomial_monic (hd' : 0 < d) :
    (shiftedTraceXiKummerPolynomial sigma gamma e d).Monic := by
  letI : CommRing (ShiftedTraceBaseFunctionField sigma gamma) :=
    AdjoinRoot.instCommRing _
  letI : CommRing (ShiftedTraceEtaFunctionField sigma gamma e) :=
    AdjoinRoot.instCommRing _
  rw [shiftedTraceXiKummerPolynomial]
  exact monic_X_pow_sub_C _ (Nat.ne_of_gt hd')

/-- The residue index of a source monomial `xi^a * eta^b`. -/
def shiftedTraceMonomialNormalIndex (a b : ℕ) :
    Fin e × Fin d :=
  (⟨b % e, Nat.mod_lt _ he⟩, ⟨a % d, Nat.mod_lt _ hd⟩)

@[simp]
theorem shiftedTraceMonomialNormalIndex_fst_val (a b : ℕ) :
    (shiftedTraceMonomialNormalIndex e d he hd a b).1.val =
      b % e := by
  rfl

@[simp]
theorem shiftedTraceMonomialNormalIndex_snd_val (a b : ℕ) :
    (shiftedTraceMonomialNormalIndex e d he hd a b).2.val =
      a % d := by
  rfl

/-- The base-field coefficient left after reducing a source monomial modulo
the two Kummer equations. -/
def shiftedTraceMonomialNormalCoefficient (a b : ℕ) :
    ShiftedTraceBaseFunctionField sigma gamma :=
  shiftedTraceBaseU sigma gamma ^ (a / d) *
    shiftedTraceBaseV sigma gamma ^ (a / d + b / e)

/-- Evaluate a rectangular coefficient vector in the top Kummer algebra. -/
def shiftedTraceExplicitNormalFormEvaluation
    (c : (Fin e × Fin d) →₀
        ShiftedTraceBaseFunctionField sigma gamma) :
    ShiftedTraceXiFunctionField sigma gamma e d := by
  letI : CommRing (ShiftedTraceBaseFunctionField sigma gamma) :=
    AdjoinRoot.instCommRing _
  letI : CommRing (ShiftedTraceEtaFunctionField sigma gamma e) :=
    AdjoinRoot.instCommRing _
  letI : CommRing (ShiftedTraceXiFunctionField sigma gamma e d) :=
    AdjoinRoot.instCommRing _
  exact Finsupp.linearCombination (ShiftedTraceBaseFunctionField sigma gamma)
    (fun ji ↦ shiftedTraceEtaRootInXiField sigma gamma e d ^ (ji.1 : ℕ) *
      shiftedTraceXiRoot sigma gamma e d ^ (ji.2 : ℕ)) c

/-- The bounded shifted Kummer monomials are linearly independent over the
quadratic base field. -/
theorem shiftedTraceEtaXiNormalMonomials_linearIndependent
    (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (he' : 0 < e) (hd' : 0 < d) :
    LinearIndependent (ShiftedTraceBaseFunctionField sigma gamma)
      (fun ji : Fin e × Fin d ↦
        shiftedTraceEtaRootInXiField sigma gamma e d ^ (ji.1 : ℕ) *
          shiftedTraceXiRoot sigma gamma e d ^ (ji.2 : ℕ)) := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible
    sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  letI : CommRing (ShiftedTraceEtaFunctionField sigma gamma e) :=
    AdjoinRoot.instCommRing _
  letI : CommRing (ShiftedTraceXiFunctionField sigma gamma e d) :=
    AdjoinRoot.instCommRing _
  letI : Nontrivial (ShiftedTraceEtaFunctionField sigma gamma e) :=
    AdjoinRoot.nontrivial (shiftedTraceEtaKummerPolynomial sigma gamma e) (by
      rw [Polynomial.degree_eq_natDegree
        (shiftedTraceEtaKummerPolynomial_monic
          sigma gamma e he').ne_zero,
        shiftedTraceEtaKummerPolynomial_natDegree
          sigma gamma e h2 hsigma]
      exact_mod_cast Nat.ne_of_gt he')
  have hetaDegree := shiftedTraceEtaKummerPolynomial_natDegree
    sigma gamma e h2 hsigma
  have hxiDegree := shiftedTraceXiKummerPolynomial_natDegree
    sigma gamma e d h2 hsigma he'
  have hnormal :=
    BGS.Markoff.adjoinRootTower_normalMonomials_linearIndependent
      (shiftedTraceEtaKummerPolynomial sigma gamma e)
      (shiftedTraceEtaKummerPolynomial_monic sigma gamma e he')
      (shiftedTraceXiKummerPolynomial sigma gamma e d)
      (shiftedTraceXiKummerPolynomial_monic sigma gamma e d hd')
  rw [hetaDegree, hxiDegree] at hnormal
  simpa [shiftedTraceEtaRootInXiField, shiftedTraceXiRoot, map_pow] using hnormal

/-- Reduction of a single shifted Kummer monomial. -/
theorem shiftedTraceKummer_monomial_reduction (a b : ℕ) :
    shiftedTraceXiRoot sigma gamma e d ^ a *
        shiftedTraceEtaRootInXiField sigma gamma e d ^ b =
      shiftedTraceBaseElementInXiField sigma gamma e d
          (shiftedTraceMonomialNormalCoefficient sigma gamma e d a b) *
        (shiftedTraceEtaRootInXiField sigma gamma e d ^ (b % e) *
          shiftedTraceXiRoot sigma gamma e d ^ (a % d)) := by
  rw [BGS.Markoff.pow_eq_pow_div_mul_pow_mod _ a d,
    BGS.Markoff.pow_eq_pow_div_mul_pow_mod _ b e,
    shiftedTraceXiRoot_pow, shiftedTraceEtaRootInXiField_pow]
  simp only [shiftedTraceMonomialNormalCoefficient,
    shiftedTraceBaseElementInXiField, map_mul, map_pow]
  ring

/-- Evaluation of the singleton normal form of one monomial recovers that
monomial. -/
theorem shiftedTraceExplicitNormalFormEvaluation_single_monomial
    (a b : ℕ) :
    shiftedTraceExplicitNormalFormEvaluation sigma gamma e d
        (Finsupp.single
          (shiftedTraceMonomialNormalIndex e d he hd a b)
          (shiftedTraceMonomialNormalCoefficient sigma gamma e d a b)) =
      shiftedTraceXiRoot sigma gamma e d ^ a *
        shiftedTraceEtaRootInXiField sigma gamma e d ^ b := by
  letI : CommRing (ShiftedTraceBaseFunctionField sigma gamma) :=
    AdjoinRoot.instCommRing _
  letI : CommRing (ShiftedTraceEtaFunctionField sigma gamma e) :=
    AdjoinRoot.instCommRing _
  letI : CommRing (ShiftedTraceXiFunctionField sigma gamma e d) :=
    AdjoinRoot.instCommRing _
  rw [shiftedTraceExplicitNormalFormEvaluation,
    Finsupp.linearCombination_single]
  simp only [Algebra.smul_def, shiftedTraceMonomialNormalIndex_fst_val,
    shiftedTraceMonomialNormalIndex_snd_val]
  rw [IsScalarTower.algebraMap_apply
    (ShiftedTraceBaseFunctionField sigma gamma)
    (ShiftedTraceEtaFunctionField sigma gamma e)
    (ShiftedTraceXiFunctionField sigma gamma e d)]
  simpa [shiftedTraceBaseElementInXiField] using
    (shiftedTraceKummer_monomial_reduction
      sigma gamma e d a b).symm

/-- The source-side rectangular normal form. -/
def shiftedTracePolynomialSyntacticNormalForm
    (p : MvPolynomial (Fin 2) K) :
    (Fin e × Fin d) →₀
        ShiftedTraceBaseFunctionField sigma gamma :=
  (AddMonoidAlgebra.coeff p).sum fun ex c ↦
    Finsupp.single
      (shiftedTraceMonomialNormalIndex e d he hd (ex 0) (ex 1))
      (algebraMap K (ShiftedTraceBaseFunctionField sigma gamma) c *
        shiftedTraceMonomialNormalCoefficient
          sigma gamma e d (ex 0) (ex 1))

@[simp]
theorem shiftedTracePolynomialSyntacticNormalForm_zero :
    shiftedTracePolynomialSyntacticNormalForm
      sigma gamma e d he hd 0 = 0 := by
  simp [shiftedTracePolynomialSyntacticNormalForm]

theorem shiftedTracePolynomialSyntacticNormalForm_add
    (p q : MvPolynomial (Fin 2) K) :
    shiftedTracePolynomialSyntacticNormalForm
        sigma gamma e d he hd (p + q) =
      shiftedTracePolynomialSyntacticNormalForm sigma gamma e d he hd p +
        shiftedTracePolynomialSyntacticNormalForm sigma gamma e d he hd q := by
  classical
  simp only [shiftedTracePolynomialSyntacticNormalForm]
  apply Finsupp.sum_add_index
  · intro ex
    simp
  · intro ex _ a b
    simp only [map_add, add_mul, Finsupp.single_add]

@[simp]
theorem shiftedTracePolynomialSyntacticNormalForm_monomial
    (ex : Fin 2 →₀ ℕ) (c : K) :
    shiftedTracePolynomialSyntacticNormalForm sigma gamma e d he hd
        (MvPolynomial.monomial ex c) =
      Finsupp.single
        (shiftedTraceMonomialNormalIndex e d he hd (ex 0) (ex 1))
        (algebraMap K (ShiftedTraceBaseFunctionField sigma gamma) c *
          shiftedTraceMonomialNormalCoefficient
            sigma gamma e d (ex 0) (ex 1)) := by
  rw [shiftedTracePolynomialSyntacticNormalForm]
  apply MvPolynomial.sum_monomial_eq
  simp

theorem shiftedTraceExplicitNormalFormEvaluation_single_scaled_monomial
    (c : K) (a b : ℕ) :
    shiftedTraceExplicitNormalFormEvaluation sigma gamma e d
        (Finsupp.single
          (shiftedTraceMonomialNormalIndex e d he hd a b)
          (algebraMap K (ShiftedTraceBaseFunctionField sigma gamma) c *
            shiftedTraceMonomialNormalCoefficient sigma gamma e d a b)) =
      algebraMap K (ShiftedTraceXiFunctionField sigma gamma e d) c *
        (shiftedTraceXiRoot sigma gamma e d ^ a *
          shiftedTraceEtaRootInXiField sigma gamma e d ^ b) := by
  letI : CommRing (ShiftedTraceBaseFunctionField sigma gamma) :=
    AdjoinRoot.instCommRing _
  letI : CommRing (ShiftedTraceEtaFunctionField sigma gamma e) :=
    AdjoinRoot.instCommRing _
  letI : CommRing (ShiftedTraceXiFunctionField sigma gamma e d) :=
    AdjoinRoot.instCommRing _
  rw [shiftedTraceExplicitNormalFormEvaluation,
    Finsupp.linearCombination_single]
  simp only [Algebra.smul_def, shiftedTraceMonomialNormalIndex_fst_val,
    shiftedTraceMonomialNormalIndex_snd_val, map_mul]
  have hred := (shiftedTraceKummer_monomial_reduction
    sigma gamma e d a b).symm
  rw [← hred]
  simp only [shiftedTraceBaseElementInXiField]
  simp_rw [IsScalarTower.algebraMap_apply K
    (ShiftedTraceBaseFunctionField sigma gamma)
    (ShiftedTraceXiFunctionField sigma gamma e d)]
  simp_rw [IsScalarTower.algebraMap_apply
    (ShiftedTraceBaseFunctionField sigma gamma)
    (ShiftedTraceEtaFunctionField sigma gamma e)
    (ShiftedTraceXiFunctionField sigma gamma e d)]
  ring

@[simp]
theorem shiftedTracePolynomialToKummerTop_monomial
    (ex : Fin 2 →₀ ℕ) (c : K) :
    shiftedTracePolynomialToKummerTop sigma gamma e d
        (MvPolynomial.monomial ex c) =
      algebraMap K (ShiftedTraceXiFunctionField sigma gamma e d) c *
        (shiftedTraceXiRoot sigma gamma e d ^ (ex 0) *
          shiftedTraceEtaRootInXiField sigma gamma e d ^ (ex 1)) := by
  simp [shiftedTracePolynomialToKummerTop, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_monomial, Fin.prod_univ_two]

/-- The explicit rectangular normal form evaluates to the original source
polynomial in the Kummer top. -/
theorem shiftedTracePolynomialSyntacticNormalForm_evaluation
    (p : MvPolynomial (Fin 2) K) :
    shiftedTraceExplicitNormalFormEvaluation sigma gamma e d
        (shiftedTracePolynomialSyntacticNormalForm
          sigma gamma e d he hd p) =
      shiftedTracePolynomialToKummerTop sigma gamma e d p := by
  induction p using MvPolynomial.induction_on' with
  | monomial ex c =>
      rw [shiftedTracePolynomialSyntacticNormalForm_monomial,
        shiftedTraceExplicitNormalFormEvaluation_single_scaled_monomial,
        shiftedTracePolynomialToKummerTop_monomial]
  | add p q hp hq =>
      rw [shiftedTracePolynomialSyntacticNormalForm_add]
      change Finsupp.linearCombination
          (ShiftedTraceBaseFunctionField sigma gamma)
          (fun ji ↦ shiftedTraceEtaRootInXiField sigma gamma e d ^
                (ji.1 : ℕ) *
              shiftedTraceXiRoot sigma gamma e d ^ (ji.2 : ℕ))
          (shiftedTracePolynomialSyntacticNormalForm
              sigma gamma e d he hd p +
            shiftedTracePolynomialSyntacticNormalForm
              sigma gamma e d he hd q) = _
      change Finsupp.linearCombination
          (ShiftedTraceBaseFunctionField sigma gamma)
          (fun ji ↦ shiftedTraceEtaRootInXiField sigma gamma e d ^
                (ji.1 : ℕ) *
              shiftedTraceXiRoot sigma gamma e d ^ (ji.2 : ℕ))
          (shiftedTracePolynomialSyntacticNormalForm
            sigma gamma e d he hd p) = _ at hp
      change Finsupp.linearCombination
          (ShiftedTraceBaseFunctionField sigma gamma)
          (fun ji ↦ shiftedTraceEtaRootInXiField sigma gamma e d ^
                (ji.1 : ℕ) *
              shiftedTraceXiRoot sigma gamma e d ^ (ji.2 : ℕ))
          (shiftedTracePolynomialSyntacticNormalForm
            sigma gamma e d he hd q) = _ at hq
      rw [map_add, hp, hq, map_add]

/-- Vanishing in the Kummer top is equivalent to vanishing of every
rectangular source coefficient. -/
theorem shiftedTracePolynomialSyntacticNormalForm_eq_zero_iff
    (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (p : MvPolynomial (Fin 2) K) :
    shiftedTracePolynomialSyntacticNormalForm
          sigma gamma e d he hd p = 0 ↔
      shiftedTracePolynomialToKummerTop sigma gamma e d p = 0 := by
  rw [← shiftedTracePolynomialSyntacticNormalForm_evaluation
    sigma gamma e d he hd p]
  constructor
  · intro h
    rw [h]
    simp [shiftedTraceExplicitNormalFormEvaluation]
  · intro h
    apply shiftedTraceEtaXiNormalMonomials_linearIndependent
      sigma gamma e d h2 hsigma he hd
    simpa [shiftedTraceExplicitNormalFormEvaluation] using h

end KummerNormalForm

section ResidueBlocks

variable (sigma gamma : K) (e d : ℕ) (he : 0 < e) (hd : 0 < d)

/-- Polynomial coefficients in each pair of exponent residue classes. -/
def shiftedTracePolynomialResidueBlocks
    (p : MvPolynomial (Fin 2) K) :
    (Fin e × Fin d) →₀ MvPolynomial (Fin 2) K :=
  (AddMonoidAlgebra.coeff p).sum fun ex c ↦
    Finsupp.single
      (shiftedTraceMonomialNormalIndex e d he hd (ex 0) (ex 1))
      (MvPolynomial.monomial
        (BGS.Markoff.finTwoExponent (ex 0 / d) (ex 1 / e)) c)

@[simp]
theorem shiftedTracePolynomialResidueBlocks_zero :
    shiftedTracePolynomialResidueBlocks e d he hd
      (0 : MvPolynomial (Fin 2) K) = 0 := by
  simp [shiftedTracePolynomialResidueBlocks]

theorem shiftedTracePolynomialResidueBlocks_add
    (p q : MvPolynomial (Fin 2) K) :
    shiftedTracePolynomialResidueBlocks e d he hd (p + q) =
      shiftedTracePolynomialResidueBlocks e d he hd p +
        shiftedTracePolynomialResidueBlocks e d he hd q := by
  classical
  simp only [shiftedTracePolynomialResidueBlocks]
  apply Finsupp.sum_add_index
  · intro ex
    simp
  · intro ex _ a b
    simp only [map_add, Finsupp.single_add]

@[simp]
theorem shiftedTracePolynomialResidueBlocks_monomial
    (ex : Fin 2 →₀ ℕ) (c : K) :
    shiftedTracePolynomialResidueBlocks e d he hd
        (MvPolynomial.monomial ex c) =
      Finsupp.single
        (shiftedTraceMonomialNormalIndex e d he hd (ex 0) (ex 1))
        (MvPolynomial.monomial
          (BGS.Markoff.finTwoExponent (ex 0 / d) (ex 1 / e)) c) := by
  rw [shiftedTracePolynomialResidueBlocks]
  apply MvPolynomial.sum_monomial_eq
  simp

/-- Reassemble residue blocks after substituting `x^d,y^e`. -/
def shiftedTraceRecomposeResidueBlocks
    (q : (Fin e × Fin d) →₀ MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 2) K :=
  q.sum fun ji a ↦
    MvPolynomial.X 0 ^ (ji.2 : ℕ) *
      MvPolynomial.X 1 ^ (ji.1 : ℕ) *
        BGS.Markoff.splitTracePowerSubstitution (K := K) e d a

theorem shiftedTraceRecomposeResidueBlocks_add
    (q r : (Fin e × Fin d) →₀ MvPolynomial (Fin 2) K) :
    shiftedTraceRecomposeResidueBlocks e d (q + r) =
      shiftedTraceRecomposeResidueBlocks e d q +
        shiftedTraceRecomposeResidueBlocks e d r := by
  classical
  simp only [shiftedTraceRecomposeResidueBlocks]
  apply Finsupp.sum_add_index
  · intro ji
    simp
  · intro ji _ a b
    simp [map_add, mul_add]

theorem shiftedTraceRecomposeResidueBlocks_single_monomial
    (a b : ℕ) (c : K) :
    shiftedTraceRecomposeResidueBlocks e d
        (Finsupp.single
          (shiftedTraceMonomialNormalIndex e d he hd a b)
          (MvPolynomial.monomial
            (BGS.Markoff.finTwoExponent (a / d) (b / e)) c)) =
      MvPolynomial.monomial (BGS.Markoff.finTwoExponent a b) c := by
  rw [shiftedTraceRecomposeResidueBlocks, Finsupp.sum_single_index]
  · rw [BGS.Markoff.splitTracePowerSubstitution_monomial]
    simp only [shiftedTraceMonomialNormalIndex_fst_val,
      shiftedTraceMonomialNormalIndex_snd_val]
    rw [BGS.Markoff.monomial_finTwoExponent]
    have ha : a % d + d * (a / d) = a := Nat.mod_add_div a d
    have hb : b % e + e * (b / e) = b := Nat.mod_add_div b e
    calc
      MvPolynomial.X (0 : Fin 2) ^ (a % d) *
            MvPolynomial.X 1 ^ (b % e) *
          (MvPolynomial.C c *
              MvPolynomial.X (0 : Fin 2) ^ (d * (a / d)) *
            MvPolynomial.X (1 : Fin 2) ^ (e * (b / e))) =
          MvPolynomial.C c *
            (MvPolynomial.X (0 : Fin 2) ^ (a % d) *
              MvPolynomial.X (0 : Fin 2) ^ (d * (a / d))) *
            (MvPolynomial.X (1 : Fin 2) ^ (b % e) *
              MvPolynomial.X (1 : Fin 2) ^ (e * (b / e))) := by
                ring
      _ = MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ a *
          MvPolynomial.X (1 : Fin 2) ^ b := by
        rw [← pow_add, ← pow_add, ha, hb]
  · simp

/-- Exact reconstruction from all shifted residue blocks. -/
theorem shiftedTraceRecomposeResidueBlocks_polynomial
    (p : MvPolynomial (Fin 2) K) :
    shiftedTraceRecomposeResidueBlocks e d
        (shiftedTracePolynomialResidueBlocks e d he hd p) = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial ex c =>
      rw [shiftedTracePolynomialResidueBlocks_monomial,
        shiftedTraceRecomposeResidueBlocks_single_monomial]
      rw [BGS.Markoff.finTwoExponent_of_finsupp]
  | add p q hp hq =>
      rw [shiftedTracePolynomialResidueBlocks_add,
        shiftedTraceRecomposeResidueBlocks_add, hp, hq]

theorem shiftedTraceBaseResidueEvaluation_monomial
    (a b : ℕ) (c : K) :
    shiftedTraceBaseResidueEvaluation sigma gamma
        (MvPolynomial.monomial (BGS.Markoff.finTwoExponent a b) c) =
      algebraMap K (ShiftedTraceBaseFunctionField sigma gamma) c *
        shiftedTraceBaseU sigma gamma ^ a *
          shiftedTraceBaseV sigma gamma ^ (a + b) := by
  rw [BGS.Markoff.monomial_finTwoExponent]
  simp only [map_mul, map_pow]
  simp only [shiftedTraceBaseResidueEvaluation, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_pow, pow_add]
  ring

/-- Every syntactic Kummer coefficient is the generic-base evaluation of
the corresponding residue-block polynomial. -/
theorem shiftedTraceBaseResidueEvaluation_residueBlock
    (p : MvPolynomial (Fin 2) K) (ji : Fin e × Fin d) :
    shiftedTraceBaseResidueEvaluation sigma gamma
        (shiftedTracePolynomialResidueBlocks e d he hd p ji) =
      shiftedTracePolynomialSyntacticNormalForm
        sigma gamma e d he hd p ji := by
  induction p using MvPolynomial.induction_on' with
  | monomial ex c =>
      rw [shiftedTracePolynomialResidueBlocks_monomial,
        shiftedTracePolynomialSyntacticNormalForm_monomial]
      by_cases hindex :
          shiftedTraceMonomialNormalIndex e d he hd (ex 0) (ex 1) = ji
      · subst ji
        simp only [Finsupp.single_eq_same]
        rw [shiftedTraceBaseResidueEvaluation_monomial]
        simp only [shiftedTraceMonomialNormalCoefficient, mul_assoc]
      · simp [hindex]
  | add p q hp hq =>
      rw [shiftedTracePolynomialResidueBlocks_add,
        shiftedTracePolynomialSyntacticNormalForm_add]
      simp only [Finsupp.add_apply, map_add, hp, hq]

end ResidueBlocks

section SourceDivision

variable (sigma gamma : K) (e d : ℕ) (he : 0 < e) (hd : 0 < d)

/-- Power substitution carries the degree-one shifted cover to the exact
`(d,e)` shifted cover. -/
theorem shiftedTracePowerSubstitution_baseCover :
    BGS.Markoff.splitTracePowerSubstitution (K := K) e d
        (shiftedTraceCoverPolynomial (1 : K) sigma gamma 1 1) =
      shiftedTraceCoverPolynomial (1 : K) sigma gamma d e := by
  simp only [shiftedTraceCoverPolynomial, map_add, map_sub, map_mul, map_pow,
    BGS.Markoff.splitTracePowerSubstitution_C,
    BGS.Markoff.splitTracePowerSubstitution_X_zero,
    BGS.Markoff.splitTracePowerSubstitution_X_one]
  simp only [pow_one, ← pow_mul]
  rw [Nat.mul_comm e 2, Nat.mul_comm d 2]

/-- A residue-block term whose coefficient vanishes on the degree-one base
curve belongs to the full shifted-cover ideal. -/
theorem shiftedTraceResidueBlockTerm_mem_coverIdeal
    (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0)
    (ji : Fin e × Fin d) (q : MvPolynomial (Fin 2) K)
    (hq : shiftedTraceBaseResidueEvaluation sigma gamma q = 0) :
    MvPolynomial.X 0 ^ (ji.2 : ℕ) *
          MvPolynomial.X 1 ^ (ji.1 : ℕ) *
        BGS.Markoff.splitTracePowerSubstitution (K := K) e d q ∈
      Ideal.span {shiftedTraceCoverPolynomial (1 : K) sigma gamma d e} := by
  rw [Ideal.mem_span_singleton]
  have hbase :
      shiftedTraceCoverPolynomial (1 : K) sigma gamma 1 1 ∣ q := by
    rw [← Ideal.mem_span_singleton]
    exact shiftedTraceBaseResiduePolynomial_mem_baseCover
      sigma gamma h2 hsigma hD2 q hq
  have hmapped := map_dvd
    (BGS.Markoff.splitTracePowerSubstitution (K := K) e d) hbase
  rw [shiftedTracePowerSubstitution_baseCover] at hmapped
  exact dvd_mul_of_dvd_right hmapped
    (MvPolynomial.X 0 ^ (ji.2 : ℕ) *
      MvPolynomial.X 1 ^ (ji.1 : ℕ))

/-- Source division for every pair of positive shifted-cover exponents. -/
theorem shiftedTracePolynomialSyntacticNormalForm_division
    (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0)
    (p : MvPolynomial (Fin 2) K)
    (hnormal : shiftedTracePolynomialSyntacticNormalForm
      sigma gamma e d he hd p = 0) :
    p ∈ Ideal.span
      {shiftedTraceCoverPolynomial (1 : K) sigma gamma d e} := by
  rw [← shiftedTraceRecomposeResidueBlocks_polynomial e d he hd p]
  rw [shiftedTraceRecomposeResidueBlocks, Finsupp.sum]
  apply Ideal.sum_mem
  intro ji hji
  apply shiftedTraceResidueBlockTerm_mem_coverIdeal
    sigma gamma e d h2 hsigma hD2 ji
  rw [shiftedTraceBaseResidueEvaluation_residueBlock]
  rw [hnormal]
  rfl

/-- The full arbitrary-positive-exponent source-kernel inclusion needed by
the shifted Kummer-tower irreducibility reduction.  It has no parity or
coprimality hypothesis. -/
theorem shiftedTracePolynomialToKummerTop_ker_le_coverIdeal
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0)
    (e d : ℕ) (he : 0 < e) (hd : 0 < d) :
    RingHom.ker
        (shiftedTracePolynomialToKummerTop sigma gamma e d).toRingHom ≤
      Ideal.span
        {shiftedTraceCoverPolynomial (1 : K) sigma gamma d e} := by
  intro p hp
  apply shiftedTracePolynomialSyntacticNormalForm_division
    sigma gamma e d he hd h2 hsigma hD2 p
  apply (shiftedTracePolynomialSyntacticNormalForm_eq_zero_iff
    sigma gamma e d he hd h2 hsigma p).2
  exact hp

end SourceDivision

section Irreducibility

/-- The normalized shifted cover is irreducible for arbitrary positive
exponents once the explicit Kummer hypotheses hold.  There is no parity or
coprimality condition. -/
theorem shiftedTraceCoverPolynomial_irreducible_of_primitiveRoot
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hsigmaOne : sigma ≠ 1)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0)
    (i : K) (hi : i ^ 2 = -1)
    (e d : ℕ) (he : 0 < e) (heChar : (e : K) ≠ 0) (hd : 0 < d)
    (zeta : K) (hzeta : IsPrimitiveRoot zeta e) :
    Irreducible
      (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e) := by
  apply shiftedTraceCoverPolynomial_irreducible_of_primitiveRoot_of_kernel_le
    sigma gamma h2 hsigma hsigmaOne hD2 i hi e d he heChar hd zeta hzeta
  simpa using shiftedTracePolynomialToKummerTop_ker_le_coverIdeal
    sigma gamma h2 hsigma hD2 e d he hd

/-- Absolute irreducibility of every positive shifted cover under the exact
nondegeneracy and characteristic hypotheses.  Passing to the algebraic
closure supplies a square root of `-1` and a primitive `e`-th root of unity. -/
theorem shiftedTraceCoverPolynomial_absolutelyIrreducible_of_positiveExponents
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hsigmaOne : sigma ≠ 1)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0)
    (e d : ℕ) (he : 0 < e) (heChar : (e : K) ≠ 0) (hd : 0 < d) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e)) := by
  let phi : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  rw [map_shiftedTraceCoverPolynomial phi (1 : K) sigma gamma d e]
  simp only [map_one]
  have h2L : (2 : AlgebraicClosure K) ≠ 0 := by
    change phi (2 : K) ≠ 0
    exact (map_ne_zero_iff phi phi.injective).mpr h2
  have hsigmaL : phi sigma ≠ 0 :=
    (map_ne_zero_iff phi phi.injective).mpr hsigma
  have hsigmaOneL : phi sigma ≠ 1 := by
    intro h
    apply hsigmaOne
    apply phi.injective
    simpa using h
  have hD2L :
      shiftedTraceEvenObstruction (phi sigma) (phi gamma) ≠ 0 := by
    have hmap : phi (shiftedTraceEvenObstruction sigma gamma) ≠ 0 :=
      (map_ne_zero_iff phi phi.injective).mpr hD2
    simpa [shiftedTraceEvenObstruction, map_ofNat] using hmap
  have heCharL : (e : AlgebraicClosure K) ≠ 0 := by
    change phi (e : K) ≠ 0
    exact (map_ne_zero_iff phi phi.injective).mpr heChar
  letI : NeZero e := ⟨Nat.ne_of_gt he⟩
  letI : NeZero (e : AlgebraicClosure K) := ⟨heCharL⟩
  obtain ⟨zeta, hzeta⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) e
  obtain ⟨sqrtNegOne, hsqrtNegOne⟩ :=
    IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure K) zero_lt_two
  exact shiftedTraceCoverPolynomial_irreducible_of_primitiveRoot
    (phi sigma) (phi gamma) h2L hsigmaL hsigmaOneL hD2L
      sqrtNegOne hsqrtNegOne e d he heCharL hd zeta hzeta

end Irreducibility

end


end GenMarkoff
