import GenMarkoff.TraceCurve.ShiftedCoverCommonPrime
import BGS.Markoff.TraceCurve.WeightedIrreducibility

/-!
# Reduction of shifted-cover irreducibility to the source kernel

The Kummer tower constructed for the shifted trace equation gives a prime
target in which the cleared bivariate cover vanishes.  This module records
that evaluation map and isolates the one remaining source-side statement:
every polynomial killed by the tower evaluation must be divisible by the
shifted cover polynomial.

This is the exact analogue of the residue-block division boundary in the
pinned BGS split-cover proof.  No unshifted division theorem is reused here,
because its base residue equation omits the affine `gamma` term.

For the base-cover specialization `d = e = 1`, the module also proves absolute
irreducibility directly.  Its birational quadratic has branch discriminant
`((y^2 + gamma*y + sigma)^2 - 4*y^2)`; the `D₂` hypothesis makes the two
quadratic factors separable and coprime, so the discriminant is not a square
in `K(y)`.  This supplies the base-cover milestone, while the residue-block
division boundary remains explicit for arbitrary positive exponents.
-/

namespace GenMarkoff

open Polynomial AdjoinRoot

noncomputable section

variable {K : Type*} [Field K]

/-- The top field obtained after adjoining the second shifted Kummer root. -/
abbrev ShiftedTraceXiFunctionField
    (sigma gamma : K) (e d : ℕ) :=
  AdjoinRoot (shiftedTraceXiKummerPolynomial sigma gamma e d)

/-- Embed a shifted-base element into the top of the Kummer tower. -/
def shiftedTraceBaseElementInXiField
    (sigma gamma : K) (e d : ℕ)
    (z : ShiftedTraceBaseFunctionField sigma gamma) :
    ShiftedTraceXiFunctionField sigma gamma e d :=
  algebraMap (ShiftedTraceEtaFunctionField sigma gamma e)
      (ShiftedTraceXiFunctionField sigma gamma e d)
    (algebraMap (ShiftedTraceBaseFunctionField sigma gamma)
      (ShiftedTraceEtaFunctionField sigma gamma e) z)

/-- The first Kummer root, viewed in the top field. -/
def shiftedTraceEtaRootInXiField
    (sigma gamma : K) (e d : ℕ) :
    ShiftedTraceXiFunctionField sigma gamma e d :=
  algebraMap (ShiftedTraceEtaFunctionField sigma gamma e)
      (ShiftedTraceXiFunctionField sigma gamma e d)
    (AdjoinRoot.root (shiftedTraceEtaKummerPolynomial sigma gamma e))

/-- The second Kummer root. -/
def shiftedTraceXiRoot (sigma gamma : K) (e d : ℕ) :
    ShiftedTraceXiFunctionField sigma gamma e d :=
  AdjoinRoot.root (shiftedTraceXiKummerPolynomial sigma gamma e d)

/-- Evaluate a bivariate polynomial at `(xi, eta)` in the shifted tower. -/
def shiftedTracePolynomialToKummerTop
    (sigma gamma : K) (e d : ℕ) :
    MvPolynomial (Fin 2) K →ₐ[K]
      ShiftedTraceXiFunctionField sigma gamma e d :=
  MvPolynomial.aeval
    ![shiftedTraceXiRoot sigma gamma e d,
      shiftedTraceEtaRootInXiField sigma gamma e d]

/-- The first Kummer root satisfies `eta^e = V` in the top field. -/
theorem shiftedTraceEtaRootInXiField_pow
    (sigma gamma : K) (e d : ℕ) :
    shiftedTraceEtaRootInXiField sigma gamma e d ^ e =
      shiftedTraceBaseElementInXiField sigma gamma e d
        (shiftedTraceBaseV sigma gamma) := by
  have hroot :
      AdjoinRoot.root
          (shiftedTraceEtaKummerPolynomial sigma gamma e) ^ e =
        algebraMap (ShiftedTraceBaseFunctionField sigma gamma)
          (ShiftedTraceEtaFunctionField sigma gamma e)
          (shiftedTraceBaseV sigma gamma) := by
    apply sub_eq_zero.mp
    have h := AdjoinRoot.eval₂_root
      (shiftedTraceEtaKummerPolynomial sigma gamma e)
    rw [shiftedTraceEtaKummerPolynomial] at h
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C] at h
    rw [← AdjoinRoot.algebraMap_eq] at h
    exact h
  change
    (algebraMap (ShiftedTraceEtaFunctionField sigma gamma e)
      (ShiftedTraceXiFunctionField sigma gamma e d)
      (AdjoinRoot.root
        (shiftedTraceEtaKummerPolynomial sigma gamma e))) ^ e =
    algebraMap (ShiftedTraceEtaFunctionField sigma gamma e)
      (ShiftedTraceXiFunctionField sigma gamma e d)
      (algebraMap (ShiftedTraceBaseFunctionField sigma gamma)
        (ShiftedTraceEtaFunctionField sigma gamma e)
        (shiftedTraceBaseV sigma gamma))
  rw [← map_pow, hroot]

/-- The second Kummer root satisfies `xi^d = U*V`. -/
theorem shiftedTraceXiRoot_pow
    (sigma gamma : K) (e d : ℕ) :
    shiftedTraceXiRoot sigma gamma e d ^ d =
      shiftedTraceBaseElementInXiField sigma gamma e d
        (shiftedTraceBaseU sigma gamma *
          shiftedTraceBaseV sigma gamma) := by
  have h := AdjoinRoot.eval₂_root
    (shiftedTraceXiKummerPolynomial sigma gamma e d)
  rw [shiftedTraceXiKummerPolynomial] at h
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C] at h
  rw [← AdjoinRoot.algebraMap_eq] at h
  change AdjoinRoot.root
      (shiftedTraceXiKummerPolynomial sigma gamma e d) ^ d =
    algebraMap (ShiftedTraceEtaFunctionField sigma gamma e)
      (ShiftedTraceXiFunctionField sigma gamma e d)
      (shiftedTraceXiRadicand sigma gamma e)
  exact sub_eq_zero.mp h

/-- Pure algebraic form of the shifted cover relation. -/
theorem shiftedTraceCoverRelation_of_powerRootRelations
    {R : Type*} [CommRing R]
    (sigma gamma U V xi eta : R) (d e : ℕ)
    (hbase : U * (1 - U) * V ^ 2 + gamma * U * V + sigma * U - 1 = 0)
    (hxi : xi ^ d = U * V) (heta : eta ^ e = V) :
    xi ^ d * eta ^ (2 * e) + sigma * xi ^ d +
        gamma * xi ^ d * eta ^ e - xi ^ (2 * d) * eta ^ e - eta ^ e = 0 := by
  rw [Nat.mul_comm 2 e, Nat.mul_comm 2 d, pow_mul, pow_mul, hxi, heta]
  linear_combination V * hbase

/-- The roots of the shifted Kummer tower satisfy the exact cleared cover
equation. -/
theorem shiftedTraceKummerTower_cover_maps_to_zero_of_primitiveRoot
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hsigmaOne : sigma ≠ 1)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0)
    (i : K) (hi : i ^ 2 = -1)
    (e d : ℕ) (he : 0 < e) (heChar : (e : K) ≠ 0) (hd : 0 < d)
    (zeta : K) (hzeta : IsPrimitiveRoot zeta e) :
    letI : Fact (Irreducible
        (shiftedTraceBasePolynomial sigma gamma)) :=
      ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
    letI : Fact (Irreducible
        (shiftedTraceEtaKummerPolynomial sigma gamma e)) :=
      ⟨shiftedTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
        sigma gamma h2 hsigma i hi e he⟩
    letI : Fact (Irreducible
        (shiftedTraceXiKummerPolynomial sigma gamma e d)) :=
      ⟨shiftedTraceXiKummerPolynomial_irreducible_of_primitiveRoot
        sigma gamma h2 hsigma hsigmaOne hD2 i hi e d he heChar hd
          zeta hzeta⟩
    shiftedTracePolynomialToKummerTop sigma gamma e d
      (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e) = 0 := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible
    sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  let hEtaIrred := shiftedTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    sigma gamma h2 hsigma i hi e he
  letI : Fact (Irreducible
      (shiftedTraceEtaKummerPolynomial sigma gamma e)) := ⟨hEtaIrred⟩
  let hXiIrred := shiftedTraceXiKummerPolynomial_irreducible_of_primitiveRoot
    sigma gamma h2 hsigma hsigmaOne hD2 i hi e d he heChar hd zeta hzeta
  letI : Fact (Irreducible
      (shiftedTraceXiKummerPolynomial sigma gamma e d)) := ⟨hXiIrred⟩
  let baseField := ShiftedTraceBaseFunctionField sigma gamma
  let etaField := ShiftedTraceEtaFunctionField sigma gamma e
  let xiField := ShiftedTraceXiFunctionField sigma gamma e d
  let baseToXi : baseField →+* xiField :=
    (algebraMap etaField xiField).comp (algebraMap baseField etaField)
  have hBase := shiftedTraceBaseU_V_equation sigma gamma h2 hsigma
  have hBaseTop := congrArg baseToXi hBase
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero] at hBaseTop
  have hEtaTop := shiftedTraceEtaRootInXiField_pow sigma gamma e d
  have hXiTop := shiftedTraceXiRoot_pow sigma gamma e d
  change shiftedTraceXiRoot sigma gamma e d ^ d =
    algebraMap etaField xiField
      (algebraMap baseField etaField
        (shiftedTraceBaseU sigma gamma *
          shiftedTraceBaseV sigma gamma)) at hXiTop
  rw [map_mul, map_mul] at hXiTop
  change shiftedTraceEtaRootInXiField sigma gamma e d ^ e =
    algebraMap etaField xiField
      (algebraMap baseField etaField
        (shiftedTraceBaseV sigma gamma)) at hEtaTop
  have hsigmaTop :
      baseToXi
          (algebraMap (RatFunc K) baseField (RatFunc.C sigma)) =
        algebraMap K xiField sigma := by
    change algebraMap etaField xiField
      (algebraMap baseField etaField
        (algebraMap (RatFunc K) baseField
          (algebraMap K (RatFunc K) sigma))) = _
    rw [← IsScalarTower.algebraMap_apply K (RatFunc K) baseField]
    rw [← IsScalarTower.algebraMap_apply K baseField etaField]
    rw [← IsScalarTower.algebraMap_apply K etaField xiField]
  have hgammaTop :
      baseToXi
          (algebraMap (RatFunc K) baseField (RatFunc.C gamma)) =
        algebraMap K xiField gamma := by
    change algebraMap etaField xiField
      (algebraMap baseField etaField
        (algebraMap (RatFunc K) baseField
          (algebraMap K (RatFunc K) gamma))) = _
    rw [← IsScalarTower.algebraMap_apply K (RatFunc K) baseField]
    rw [← IsScalarTower.algebraMap_apply K baseField etaField]
    rw [← IsScalarTower.algebraMap_apply K etaField xiField]
  rw [hsigmaTop, hgammaTop] at hBaseTop
  have hCover := shiftedTraceCoverRelation_of_powerRootRelations
    (algebraMap K xiField sigma) (algebraMap K xiField gamma)
    (baseToXi (shiftedTraceBaseU sigma gamma))
    (baseToXi (shiftedTraceBaseV sigma gamma))
    (shiftedTraceXiRoot sigma gamma e d)
    (shiftedTraceEtaRootInXiField sigma gamma e d) d e hBaseTop
    (by exact hXiTop) (by exact hEtaTop)
  simpa [shiftedTracePolynomialToKummerTop, MvPolynomial.aeval_def,
    shiftedTraceCoverPolynomial] using hCover

/-- The normalized shifted cover is visibly nonzero for positive `d`. -/
theorem shiftedTraceCoverPolynomial_ne_zero
    (sigma gamma : K) (d e : ℕ) (hd : 0 < d) :
    shiftedTraceCoverPolynomial (1 : K) sigma gamma d e ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval ![(0 : K), (1 : K)]) hzero
  rw [eval_shiftedTraceCoverPolynomial] at heval
  norm_num [hd.ne'] at heval

/-- Exact source-kernel reduction for shifted-cover irreducibility.  Once the
kernel of tower evaluation is contained in the principal cover ideal, the
cover polynomial is irreducible. -/
theorem shiftedTraceCoverPolynomial_irreducible_of_primitiveRoot_of_kernel_le
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hsigmaOne : sigma ≠ 1)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0)
    (i : K) (hi : i ^ 2 = -1)
    (e d : ℕ) (he : 0 < e) (heChar : (e : K) ≠ 0) (hd : 0 < d)
    (zeta : K) (hzeta : IsPrimitiveRoot zeta e)
    (hker : letI : Fact (Irreducible
          (shiftedTraceBasePolynomial sigma gamma)) :=
        ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
      letI : Fact (Irreducible
          (shiftedTraceEtaKummerPolynomial sigma gamma e)) :=
        ⟨shiftedTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
          sigma gamma h2 hsigma i hi e he⟩
      letI : Fact (Irreducible
          (shiftedTraceXiKummerPolynomial sigma gamma e d)) :=
        ⟨shiftedTraceXiKummerPolynomial_irreducible_of_primitiveRoot
          sigma gamma h2 hsigma hsigmaOne hD2 i hi e d he heChar hd
            zeta hzeta⟩
      RingHom.ker
          (shiftedTracePolynomialToKummerTop sigma gamma e d).toRingHom ≤
        Ideal.span
          {shiftedTraceCoverPolynomial (1 : K) sigma gamma d e}) :
    Irreducible
      (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e) := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible
    sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  let hEtaIrred := shiftedTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    sigma gamma h2 hsigma i hi e he
  letI : Fact (Irreducible
      (shiftedTraceEtaKummerPolynomial sigma gamma e)) := ⟨hEtaIrred⟩
  let hXiIrred := shiftedTraceXiKummerPolynomial_irreducible_of_primitiveRoot
    sigma gamma h2 hsigma hsigmaOne hD2 i hi e d he heChar hd zeta hzeta
  letI : Fact (Irreducible
      (shiftedTraceXiKummerPolynomial sigma gamma e d)) := ⟨hXiIrred⟩
  letI : IsDomain (ShiftedTraceXiFunctionField sigma gamma e d) :=
    AdjoinRoot.isDomain_of_prime hXiIrred.prime
  let f : MvPolynomial (Fin 2) K →+*
      ShiftedTraceXiFunctionField sigma gamma e d :=
    (shiftedTracePolynomialToKummerTop sigma gamma e d).toRingHom
  let I : Ideal (MvPolynomial (Fin 2) K) :=
    Ideal.span {shiftedTraceCoverPolynomial (1 : K) sigma gamma d e}
  have hCoverZero : shiftedTracePolynomialToKummerTop sigma gamma e d
      (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e) = 0 :=
    shiftedTraceKummerTower_cover_maps_to_zero_of_primitiveRoot
      sigma gamma h2 hsigma hsigmaOne hD2 i hi e d he heChar hd
        zeta hzeta
  have hI_le : I ≤ RingHom.ker f := by
    change Ideal.span
      {shiftedTraceCoverPolynomial (1 : K) sigma gamma d e} ≤ RingHom.ker f
    rw [Ideal.span_le]
    intro p hp
    simp only [Set.mem_singleton_iff] at hp
    subst p
    exact hCoverZero
  have hker_le : RingHom.ker f ≤ I := by
    simpa [f, I] using hker
  let quotientToTop : MvPolynomial (Fin 2) K ⧸ I →+*
      ShiftedTraceXiFunctionField sigma gamma e d :=
    Ideal.Quotient.lift I f hI_le
  have hInjective : Function.Injective quotientToTop :=
    RingHom.lift_injective_of_ker_le_ideal I hI_le hker_le
  letI : IsDomain (MvPolynomial (Fin 2) K ⧸ I) :=
    hInjective.isDomain quotientToTop
  have hprimeIdeal : I.IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
  have hprimeElement : Prime
      (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e) :=
    (Ideal.span_singleton_prime
      (shiftedTraceCoverPolynomial_ne_zero sigma gamma d e hd)).1 (by
        simpa [I] using hprimeIdeal)
  exact irreducible_iff_prime.mpr hprimeElement

/-- The shifted cover commutes with scalar extension. -/
theorem map_shiftedTraceCoverPolynomial
    {L : Type*} [Field L] (phi : K →+* L)
    (alpha beta gamma : K) (d e : ℕ) :
    MvPolynomial.map phi
        (shiftedTraceCoverPolynomial alpha beta gamma d e) =
      shiftedTraceCoverPolynomial (phi alpha) (phi beta) (phi gamma) d e := by
  simp [shiftedTraceCoverPolynomial]

section DegreeOneCover

/-- A monic quadratic with nonzero discriminant is separable. -/
theorem monicQuadratic_separable_of_discriminant_ne_zero
    (b c : K) (hdisc : b ^ 2 - 4 * c ≠ 0) :
    (X ^ 2 + C b * X + C c : K[X]).Separable := by
  rw [Polynomial.separable_def']
  let delta : K := b ^ 2 - 4 * c
  have hdelta : delta ≠ 0 := by simpa [delta] using hdisc
  have hderivative :
      (X ^ 2 + C b * X + C c : K[X]).derivative =
        C 2 * X + C b := by
    simp only [derivative_add, derivative_mul, derivative_pow, derivative_X,
      derivative_C, map_ofNat, zero_mul, zero_add, mul_one]
    rw [← Polynomial.C_ofNat]
    ring_nf
  have hbezout :
      C (-4 : K) * (X ^ 2 + C b * X + C c) +
          (X ^ 2 + C b * X + C c : K[X]).derivative *
            (X ^ 2 + C b * X + C c : K[X]).derivative =
        C delta := by
    rw [hderivative]
    simp only [delta, map_sub, map_mul, map_pow, Polynomial.C_neg,
      Polynomial.C_ofNat]
    ring
  refine ⟨C delta⁻¹ * C (-4 : K),
    C delta⁻¹ * (X ^ 2 + C b * X + C c : K[X]).derivative, ?_⟩
  calc
    (C delta⁻¹ * C (-4 : K)) * (X ^ 2 + C b * X + C c) +
        (C delta⁻¹ * (X ^ 2 + C b * X + C c : K[X]).derivative) *
          (X ^ 2 + C b * X + C c : K[X]).derivative =
      C delta⁻¹ *
        (C (-4 : K) * (X ^ 2 + C b * X + C c) +
          (X ^ 2 + C b * X + C c : K[X]).derivative *
            (X ^ 2 + C b * X + C c : K[X]).derivative) := by ring
    _ = C delta⁻¹ * C delta := by rw [hbezout]
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hdelta, C_1]

/-- The two quadratic factors of the degree-one branch discriminant. -/
def shiftedTraceDegreeOneBranchFactor (sigma gamma epsilon : K) : K[X] :=
  X ^ 2 + C (gamma + epsilon * 2) * X + C sigma

/-- The branch discriminant of the degree-one shifted cover. -/
def shiftedTraceDegreeOneBranchPolynomial (sigma gamma : K) : K[X] :=
  (X ^ 2 + C gamma * X + C sigma) ^ 2 - C 4 * X ^ 2

theorem shiftedTraceDegreeOneBranchPolynomial_factorization
    (sigma gamma : K) :
    shiftedTraceDegreeOneBranchPolynomial sigma gamma =
      shiftedTraceDegreeOneBranchFactor sigma gamma (-1) *
        shiftedTraceDegreeOneBranchFactor sigma gamma 1 := by
  simp [shiftedTraceDegreeOneBranchPolynomial,
    shiftedTraceDegreeOneBranchFactor]
  simp only [Polynomial.C_ofNat]
  ring

lemma shiftedTraceDegreeOneBranchFactor_natDegree
    (sigma gamma epsilon : K) :
    (shiftedTraceDegreeOneBranchFactor sigma gamma epsilon).natDegree = 2 := by
  rw [shiftedTraceDegreeOneBranchFactor]
  compute_degree!

lemma shiftedTraceDegreeOneBranchFactor_not_isUnit
    (sigma gamma epsilon : K) :
    ¬ IsUnit (shiftedTraceDegreeOneBranchFactor sigma gamma epsilon) :=
  not_isUnit_of_natDegree_pos _ <| by
    rw [shiftedTraceDegreeOneBranchFactor_natDegree]
    norm_num

theorem shiftedTraceDegreeOneBranchFactors_isCoprime
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) :
    IsCoprime
      (shiftedTraceDegreeOneBranchFactor sigma gamma (-1))
      (shiftedTraceDegreeOneBranchFactor sigma gamma 1) := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 h2
  let qMinus := shiftedTraceDegreeOneBranchFactor sigma gamma (-1)
  let qPlus := shiftedTraceDegreeOneBranchFactor sigma gamma 1
  have hdiff : qPlus - qMinus = C (4 : K) * X := by
    simp [qMinus, qPlus, shiftedTraceDegreeOneBranchFactor]
    simp only [Polynomial.C_ofNat]
    ring
  have hconstant : qMinus - (X + C (gamma - 2)) * X = C sigma := by
    simp [qMinus, shiftedTraceDegreeOneBranchFactor]
    ring
  let t : K[X] := C sigma⁻¹ * (X + C (gamma - 2)) * C (4 : K)⁻¹
  refine ⟨C sigma⁻¹ + t, -t, ?_⟩
  calc
    (C sigma⁻¹ + t) * qMinus + -t * qPlus =
        C sigma⁻¹ * qMinus - t * (qPlus - qMinus) := by ring
    _ = C sigma⁻¹ * qMinus -
        (C sigma⁻¹ * (X + C (gamma - 2)) * C (4 : K)⁻¹) *
          (C (4 : K) * X) := by rw [hdiff]
    _ = C sigma⁻¹ * qMinus -
        C sigma⁻¹ * (X + C (gamma - 2)) *
          (C (4 : K)⁻¹ * C (4 : K)) * X := by ring
    _ = C sigma⁻¹ * (qMinus - (X + C (gamma - 2)) * X) := by
      rw [← C_mul, inv_mul_cancel₀ h4, C_1]
      simp only [mul_one]
      ring
    _ = C sigma⁻¹ * C sigma := by rw [hconstant]
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hsigma, C_1]

theorem shiftedTraceDegreeOneBranchPolynomial_separable
    (sigma gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0) :
    (shiftedTraceDegreeOneBranchPolynomial sigma gamma).Separable := by
  have hfactor := shiftedTraceEvenObstruction_factorization sigma gamma
  have hminus : (gamma - 2) ^ 2 - 4 * sigma ≠ 0 := by
    intro hzero
    apply hD2
    rw [hfactor, hzero]
    simp
  have hplus : (gamma + 2) ^ 2 - 4 * sigma ≠ 0 := by
    intro hzero
    apply hD2
    rw [hfactor, hzero]
    simp
  have hsepMinus :
      (shiftedTraceDegreeOneBranchFactor sigma gamma (-1)).Separable := by
    simpa [shiftedTraceDegreeOneBranchFactor, sub_eq_add_neg] using
      monicQuadratic_separable_of_discriminant_ne_zero
        (gamma - 2) sigma hminus
  have hsepPlus :
      (shiftedTraceDegreeOneBranchFactor sigma gamma 1).Separable := by
    simpa [shiftedTraceDegreeOneBranchFactor] using
      monicQuadratic_separable_of_discriminant_ne_zero
        (gamma + 2) sigma hplus
  rw [shiftedTraceDegreeOneBranchPolynomial_factorization]
  exact hsepMinus.mul hsepPlus
    (shiftedTraceDegreeOneBranchFactors_isCoprime sigma gamma h2 hsigma)

theorem shiftedTraceDegreeOneBranchPolynomial_not_isSquare
    (sigma gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0) :
    ¬ IsSquare
      (algebraMap K[X] (RatFunc K)
        (shiftedTraceDegreeOneBranchPolynomial sigma gamma)) := by
  apply BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
  · exact (shiftedTraceDegreeOneBranchPolynomial_separable
      sigma gamma h2 hsigma hD2).squarefree
  · rw [shiftedTraceDegreeOneBranchPolynomial_factorization]
    intro hunit
    exact shiftedTraceDegreeOneBranchFactor_not_isUnit sigma gamma (-1)
      (IsUnit.mul_iff.mp hunit).1

/-- For the degree-one cover, the common-even discriminant is stronger than
necessary.  The branch polynomial fails to be a square unless the shifted
trace equation is the genuinely toric pair `(sigma, gamma) = (1, 0)`.

This is the key middle-game refinement: a single singular quadratic branch
contributes a square factor, but the other coprime quadratic remains a
non-square.  Only when both branches are singular do the two equations force
`gamma = 0` and `sigma = 1`. -/
theorem shiftedTraceDegreeOneBranchPolynomial_not_isSquare_of_not_toric
    (sigma gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : sigma ≠ 0)
    (hnotToric : ¬ (sigma = 1 ∧ gamma = 0)) :
    ¬ IsSquare
      (algebraMap K[X] (RatFunc K)
        (shiftedTraceDegreeOneBranchPolynomial sigma gamma)) := by
  let qMinus := shiftedTraceDegreeOneBranchFactor sigma gamma (-1)
  let qPlus := shiftedTraceDegreeOneBranchFactor sigma gamma 1
  let f : K[X] →+* RatFunc K := algebraMap K[X] (RatFunc K)
  have hfactor :
      shiftedTraceDegreeOneBranchPolynomial sigma gamma =
        qMinus * qPlus := by
    simpa [qMinus, qPlus] using
      shiftedTraceDegreeOneBranchPolynomial_factorization sigma gamma
  have hqMinusNonzero : qMinus ≠ 0 := by
    intro hzero
    have hdegree : qMinus.natDegree = 2 := by
      simpa [qMinus] using
        shiftedTraceDegreeOneBranchFactor_natDegree sigma gamma (-1)
    rw [hzero] at hdegree
    simp at hdegree
  have hqPlusNonzero : qPlus ≠ 0 := by
    intro hzero
    have hdegree : qPlus.natDegree = 2 := by
      simpa [qPlus] using
        shiftedTraceDegreeOneBranchFactor_natDegree sigma gamma 1
    rw [hzero] at hdegree
    simp at hdegree
  let dMinus : K := (gamma - 2) ^ 2 - 4 * sigma
  let dPlus : K := (gamma + 2) ^ 2 - 4 * sigma
  by_cases hMinus : dMinus = 0
  · by_cases hPlus : dPlus = 0
    · have h8 : (8 : K) ≠ 0 := by
        rw [show (8 : K) = 2 ^ 3 by norm_num]
        exact pow_ne_zero 3 h2
      have hgamma : gamma = 0 := by
        have h8gamma : (8 : K) * gamma = 0 := by
          dsimp [dMinus, dPlus] at hMinus hPlus
          linear_combination hPlus - hMinus
        exact (mul_eq_zero.mp h8gamma).resolve_left h8
      have h4 : (4 : K) ≠ 0 := by
        rw [show (4 : K) = 2 ^ 2 by norm_num]
        exact pow_ne_zero 2 h2
      have hsigmaOne : sigma = 1 := by
        dsimp [dMinus] at hMinus
        rw [hgamma] at hMinus
        apply (mul_left_cancel₀ h4)
        linear_combination -hMinus
      exact (hnotToric ⟨hsigmaOne, hgamma⟩).elim
    · have hPlusNe : (gamma + 2) ^ 2 - 4 * sigma ≠ 0 := by
        simpa [dPlus] using hPlus
      have hqPlusNotSquare :
          ¬ IsSquare (f qPlus) := by
        apply BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        · simpa [qPlus, shiftedTraceDegreeOneBranchFactor] using
            (monicQuadratic_separable_of_discriminant_ne_zero
              (gamma + 2) sigma hPlusNe).squarefree
        · exact shiftedTraceDegreeOneBranchFactor_not_isUnit
            sigma gamma 1
      have hqMinusSquare : IsSquare (f qMinus) := by
        let r : K[X] := X + C ((gamma - 2) / 2)
        have hsigmaEq : sigma = ((gamma - 2) / 2) ^ 2 := by
          dsimp [dMinus] at hMinus
          have h4sigma : 4 * sigma = (gamma - 2) ^ 2 := by
            linear_combination -hMinus
          field_simp [h2]
          calc
            sigma * 2 ^ 2 = 4 * sigma := by ring
            _ = (gamma - 2) ^ 2 := h4sigma
        have hq : qMinus = r ^ 2 := by
          dsimp [qMinus, r]
          rw [shiftedTraceDegreeOneBranchFactor]
          rw [hsigmaEq]
          have hlin :
              gamma + (-1 : K) * 2 = 2 * ((gamma - 2) / 2) := by
            field_simp [h2]
            ring
          rw [hlin]
          simp only [pow_two, C_mul]
          have htwoPoly : C (2 : K) = (2 : K[X]) :=
            Polynomial.C_ofNat 2
          rw [htwoPoly]
          ring
        refine ⟨f r, ?_⟩
        rw [hq, map_pow]
        simp [pow_two]
      intro hSquare
      apply hqPlusNotSquare
      have hqMinusMap : f qMinus ≠ 0 := by
        exact RatFunc.algebraMap_ne_zero hqMinusNonzero
      rw [hfactor, map_mul] at hSquare
      have hQuotient := hSquare.div hqMinusSquare
      change IsSquare ((f qMinus * f qPlus) / f qMinus) at hQuotient
      convert hQuotient using 1
      field_simp [hqMinusMap]
  · have hMinusNe : (gamma - 2) ^ 2 - 4 * sigma ≠ 0 := by
      simpa [dMinus] using hMinus
    by_cases hPlus : dPlus = 0
    · have hqMinusNotSquare :
          ¬ IsSquare (f qMinus) := by
        apply BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        · simpa [qMinus, shiftedTraceDegreeOneBranchFactor,
            sub_eq_add_neg] using
            (monicQuadratic_separable_of_discriminant_ne_zero
              (gamma - 2) sigma hMinusNe).squarefree
        · exact shiftedTraceDegreeOneBranchFactor_not_isUnit
            sigma gamma (-1)
      have hqPlusSquare : IsSquare (f qPlus) := by
        let r : K[X] := X + C ((gamma + 2) / 2)
        have hsigmaEq : sigma = ((gamma + 2) / 2) ^ 2 := by
          dsimp [dPlus] at hPlus
          have h4sigma : 4 * sigma = (gamma + 2) ^ 2 := by
            linear_combination -hPlus
          field_simp [h2]
          calc
            sigma * 2 ^ 2 = 4 * sigma := by ring
            _ = (gamma + 2) ^ 2 := h4sigma
        have hq : qPlus = r ^ 2 := by
          dsimp [qPlus, r]
          rw [shiftedTraceDegreeOneBranchFactor]
          rw [hsigmaEq]
          have hlin :
              gamma + (1 : K) * 2 = 2 * ((gamma + 2) / 2) := by
            field_simp [h2]
          rw [hlin]
          simp only [pow_two, C_mul]
          have htwoPoly : C (2 : K) = (2 : K[X]) :=
            Polynomial.C_ofNat 2
          rw [htwoPoly]
          ring
        refine ⟨f r, ?_⟩
        rw [hq, map_pow]
        simp [pow_two]
      intro hSquare
      apply hqMinusNotSquare
      have hqPlusMap : f qPlus ≠ 0 := by
        exact RatFunc.algebraMap_ne_zero hqPlusNonzero
      rw [hfactor, map_mul] at hSquare
      have hQuotient := hSquare.div hqPlusSquare
      change IsSquare ((f qMinus * f qPlus) / f qPlus) at hQuotient
      convert hQuotient using 1
      field_simp [hqPlusMap]
    · have hPlusNe : (gamma + 2) ^ 2 - 4 * sigma ≠ 0 := by
        simpa [dPlus] using hPlus
      apply shiftedTraceDegreeOneBranchPolynomial_not_isSquare
        sigma gamma h2 hsigma
      rw [shiftedTraceEvenObstruction_factorization]
      exact mul_ne_zero hMinusNe hPlusNe

/-- The degree-one shifted cover in iterated-polynomial form, with variable
`0` outermost. -/
def shiftedTraceDegreeOneIteratedPolynomial
    (sigma gamma : K) : Polynomial K[X] :=
  monomial 2 (-X) +
    monomial 1 (X ^ 2 + C gamma * X + C sigma) + C (-X)

theorem finTwoToIteratedPolynomial_shiftedTraceDegreeOne
    (sigma gamma : K) :
    BGS.Markoff.finTwoToIteratedPolynomial
        (shiftedTraceCoverPolynomial (1 : K) sigma gamma 1 1) =
      shiftedTraceDegreeOneIteratedPolynomial sigma gamma := by
  simp only [shiftedTraceCoverPolynomial, map_add, map_sub, map_mul, map_pow,
    BGS.Markoff.finTwoToIteratedPolynomial_C,
    BGS.Markoff.finTwoToIteratedPolynomial_X_zero,
    BGS.Markoff.finTwoToIteratedPolynomial_X_one, map_one]
  simp only [pow_one, shiftedTraceDegreeOneIteratedPolynomial,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [Polynomial.C_mul, Polynomial.C_add,
    Polynomial.C_neg, Polynomial.C_pow]
  ring

theorem shiftedTraceDegreeOneIteratedPolynomial_isPrimitive
    (sigma gamma : K) (hsigma : sigma ≠ 0) :
    (shiftedTraceDegreeOneIteratedPolynomial sigma gamma).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  have hcoeff := (Polynomial.C_dvd_iff_dvd_coeff r
    (shiftedTraceDegreeOneIteratedPolynomial sigma gamma)).mp hr
  have hrY : r ∣ X := by
    have h := hcoeff 0
    have hrNegY : r ∣ -X := by
      simpa [shiftedTraceDegreeOneIteratedPolynomial] using h
    exact dvd_neg.mp hrNegY
  have hrMiddle : r ∣ X ^ 2 + C gamma * X + C sigma := by
    have hcoeffOne :
        (shiftedTraceDegreeOneIteratedPolynomial sigma gamma).coeff 1 =
          X ^ 2 + C gamma * X + C sigma := by
      norm_num [shiftedTraceDegreeOneIteratedPolynomial,
        Polynomial.coeff_monomial]
    rw [← hcoeffOne]
    exact hcoeff 1
  rcases hrY with ⟨q, hq⟩
  rcases hrMiddle with ⟨s, hs⟩
  have hrSigma : r ∣ C sigma := by
    refine ⟨s - (q * X + C gamma * q), ?_⟩
    calc
      C sigma = (X ^ 2 + C gamma * X + C sigma) -
          (X + C gamma) * X := by ring
      _ = r * s - (X + C gamma) * (r * q) := by rw [hs, hq]
      _ = r * (s - (q * X + C gamma * q)) := by ring
  exact isUnit_of_dvd_unit hrSigma
    (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hsigma))

/-- The degree-one shifted cover after the birational substitution `x = u y`
and removal of the invertible factor `y`. -/
def shiftedTraceDegreeOneBirationalPolynomial
    (sigma gamma : K) : Polynomial K[X] :=
  monomial 2 (-(X ^ 2)) +
    monomial 1 (X ^ 2 + C gamma * X + C sigma) + C (-1)

/-- The linear coefficient of the monic degree-one birational quadratic over
the rational function field `K(y)`. -/
def shiftedTraceDegreeOneRationalLinearCoefficient
    (sigma gamma : K) : RatFunc K :=
  -((RatFunc.X ^ 2 + RatFunc.C gamma * RatFunc.X + RatFunc.C sigma) /
    RatFunc.X ^ 2)

/-- The constant coefficient of the monic degree-one birational quadratic. -/
def shiftedTraceDegreeOneRationalConstant : RatFunc K :=
  1 / RatFunc.X ^ 2

/-- The monic normalization of the degree-one birational quadratic over
`K(y)`. -/
def shiftedTraceDegreeOneRationalMonicPolynomial
    (sigma gamma : K) : Polynomial (RatFunc K) :=
  X ^ 2 + C (shiftedTraceDegreeOneRationalLinearCoefficient sigma gamma) * X +
    C shiftedTraceDegreeOneRationalConstant

theorem shiftedTraceDegreeOneRationalDiscriminant
    (sigma gamma : K) :
    shiftedTraceDegreeOneRationalLinearCoefficient sigma gamma ^ 2 -
        4 * shiftedTraceDegreeOneRationalConstant =
      algebraMap K[X] (RatFunc K)
          (shiftedTraceDegreeOneBranchPolynomial sigma gamma) /
        RatFunc.X ^ 4 := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  simp only [shiftedTraceDegreeOneRationalLinearCoefficient,
    shiftedTraceDegreeOneRationalConstant,
    shiftedTraceDegreeOneBranchPolynomial, map_sub, map_mul, map_pow,
    map_add, map_ofNat, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  field_simp [hX]

theorem shiftedTraceDegreeOneRationalDiscriminant_not_isSquare
    (sigma gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0) :
    ¬ IsSquare
      (shiftedTraceDegreeOneRationalLinearCoefficient sigma gamma ^ 2 -
        4 * shiftedTraceDegreeOneRationalConstant) := by
  intro hSquare
  apply shiftedTraceDegreeOneBranchPolynomial_not_isSquare
    sigma gamma h2 hsigma hD2
  have hX4 : IsSquare (RatFunc.X ^ 4 : RatFunc K) := by
    refine ⟨RatFunc.X ^ 2, ?_⟩
    ring
  have hProduct := hSquare.mul hX4
  rw [shiftedTraceDegreeOneRationalDiscriminant sigma gamma] at hProduct
  simpa [RatFunc.X_ne_zero] using hProduct

theorem shiftedTraceDegreeOneRationalMonicPolynomial_irreducible
    (sigma gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0) :
    Irreducible
      (shiftedTraceDegreeOneRationalMonicPolynomial sigma gamma) := by
  rw [shiftedTraceDegreeOneRationalMonicPolynomial]
  exact monicQuadratic_irreducible_of_discriminant_not_isSquare
    (shiftedTraceDegreeOneRationalLinearCoefficient sigma gamma)
    shiftedTraceDegreeOneRationalConstant
    (shiftedTraceDegreeOneRationalDiscriminant_not_isSquare
      sigma gamma h2 hsigma hD2)

/-- Clearing the monic normalization multiplies by the nonzero rational
coefficient `-y^2` and recovers the birational polynomial. -/
theorem map_shiftedTraceDegreeOneBirationalPolynomial
    (sigma gamma : K) :
    (shiftedTraceDegreeOneBirationalPolynomial sigma gamma).map
        (algebraMap K[X] (RatFunc K)) =
      C (-(RatFunc.X ^ 2)) *
        shiftedTraceDegreeOneRationalMonicPolynomial sigma gamma := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hLinear :
      -(RatFunc.X ^ 2) *
          shiftedTraceDegreeOneRationalLinearCoefficient sigma gamma =
        RatFunc.X ^ 2 + RatFunc.C gamma * RatFunc.X + RatFunc.C sigma := by
    simp only [shiftedTraceDegreeOneRationalLinearCoefficient]
    field_simp [hX]
  have hConstant :
      -(RatFunc.X ^ 2) *
          shiftedTraceDegreeOneRationalConstant (K := K) = -1 := by
    simp only [shiftedTraceDegreeOneRationalConstant]
    field_simp [hX]
  have hLinearC :
      (C (-(RatFunc.X ^ 2)) : Polynomial (RatFunc K)) *
          C (shiftedTraceDegreeOneRationalLinearCoefficient sigma gamma) =
        C (RatFunc.X ^ 2 + RatFunc.C gamma * RatFunc.X +
          RatFunc.C sigma) := by
    rw [← C_mul, hLinear]
  have hConstantC :
      (C (-(RatFunc.X ^ 2)) : Polynomial (RatFunc K)) *
          C (shiftedTraceDegreeOneRationalConstant (K := K)) = C (-1) := by
    rw [← C_mul, hConstant]
  calc
    (shiftedTraceDegreeOneBirationalPolynomial sigma gamma).map
        (algebraMap K[X] (RatFunc K)) =
      C (-(RatFunc.X ^ 2)) * X ^ 2 +
        C (RatFunc.X ^ 2 + RatFunc.C gamma * RatFunc.X +
          RatFunc.C sigma) * X + C (-1) := by
      simp [shiftedTraceDegreeOneBirationalPolynomial,
        ← Polynomial.C_mul_X_pow_eq_monomial]
    _ = C (-(RatFunc.X ^ 2)) *
        shiftedTraceDegreeOneRationalMonicPolynomial sigma gamma := by
      rw [shiftedTraceDegreeOneRationalMonicPolynomial, mul_add, mul_add,
        ← mul_assoc, hLinearC, hConstantC]

theorem map_shiftedTraceDegreeOneBirationalPolynomial_irreducible
    (sigma gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0) :
    Irreducible
      ((shiftedTraceDegreeOneBirationalPolynomial sigma gamma).map
        (algebraMap K[X] (RatFunc K))) := by
  rw [map_shiftedTraceDegreeOneBirationalPolynomial]
  have hCoefficient : IsUnit
      (C (-(RatFunc.X ^ 2)) : Polynomial (RatFunc K)) :=
    Polynomial.isUnit_C.mpr <| isUnit_iff_ne_zero.mpr <| by
      exact neg_ne_zero.mpr (pow_ne_zero 2 RatFunc.X_ne_zero)
  exact (irreducible_isUnit_mul hCoefficient).2
    (shiftedTraceDegreeOneRationalMonicPolynomial_irreducible
      sigma gamma h2 hsigma hD2)

/-- The coefficient variable `y`, viewed as a unit in `K(y)`. -/
noncomputable def shiftedTraceDegreeOneFractionScaleUnit : (RatFunc K)ˣ :=
  Units.mk0 RatFunc.X RatFunc.X_ne_zero

@[simp]
theorem shiftedTraceDegreeOneFractionScaleUnit_val :
    (shiftedTraceDegreeOneFractionScaleUnit (K := K) : RatFunc K) =
      RatFunc.X := by
  rfl

/-- Substitution `x = u y` turns the degree-one cover into `y` times its
birational quadratic. -/
theorem polynomialVariableScaleEquiv_map_shiftedTraceDegreeOne
    (sigma gamma : K) :
    BGS.Markoff.polynomialVariableScaleEquiv
        (shiftedTraceDegreeOneFractionScaleUnit (K := K))
        ((shiftedTraceDegreeOneIteratedPolynomial sigma gamma).map
          (algebraMap K[X] (RatFunc K))) =
      C RatFunc.X *
        (shiftedTraceDegreeOneBirationalPolynomial sigma gamma).map
          (algebraMap K[X] (RatFunc K)) := by
  simp [BGS.Markoff.polynomialVariableScaleEquiv,
    shiftedTraceDegreeOneIteratedPolynomial,
    shiftedTraceDegreeOneBirationalPolynomial,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

theorem shiftedTraceDegreeOneIteratedPolynomial_irreducible
    (sigma gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0) :
    Irreducible (shiftedTraceDegreeOneIteratedPolynomial sigma gamma) := by
  have hBirational : Irreducible
      ((shiftedTraceDegreeOneBirationalPolynomial sigma gamma).map
        (algebraMap K[X] (RatFunc K))) :=
    map_shiftedTraceDegreeOneBirationalPolynomial_irreducible
      sigma gamma h2 hsigma hD2
  have hyUnit : IsUnit (C RatFunc.X : Polynomial (RatFunc K)) :=
    Polynomial.isUnit_C.mpr <| isUnit_iff_ne_zero.mpr RatFunc.X_ne_zero
  have hScaled : Irreducible
      (BGS.Markoff.polynomialVariableScaleEquiv
        (shiftedTraceDegreeOneFractionScaleUnit (K := K))
        ((shiftedTraceDegreeOneIteratedPolynomial sigma gamma).map
          (algebraMap K[X] (RatFunc K)))) := by
    rw [polynomialVariableScaleEquiv_map_shiftedTraceDegreeOne]
    exact (irreducible_isUnit_mul hyUnit).2 hBirational
  have hFraction : Irreducible
      ((shiftedTraceDegreeOneIteratedPolynomial sigma gamma).map
        (algebraMap K[X] (RatFunc K))) := by
    have hback := hScaled.map
      (BGS.Markoff.polynomialVariableScaleEquiv
        (shiftedTraceDegreeOneFractionScaleUnit (K := K))).symm
    simpa using hback
  exact (shiftedTraceDegreeOneIteratedPolynomial_isPrimitive
    sigma gamma hsigma).irreducible_iff_irreducible_map_fraction_map.mpr hFraction

/-- The normalized degree-one shifted cover is irreducible. -/
theorem shiftedTraceDegreeOneCoverPolynomial_irreducible
    (sigma gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0) :
    Irreducible (shiftedTraceCoverPolynomial (1 : K) sigma gamma 1 1) := by
  have hImage := finTwoToIteratedPolynomial_shiftedTraceDegreeOne sigma gamma
  have hIterated := shiftedTraceDegreeOneIteratedPolynomial_irreducible
    sigma gamma h2 hsigma hD2
  rw [← hImage] at hIterated
  have hback := hIterated.map
    (BGS.Markoff.finTwoToIteratedPolynomial (K := K)).symm
  simpa using hback

/-- The degree-one shifted cover stays irreducible after passage to the
algebraic closure.  Thus it provides the absolutely irreducible base equation
needed by a shifted residue-block proof. -/
theorem shiftedTraceDegreeOneCoverPolynomial_absolutelyIrreducible
    (sigma gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (shiftedTraceCoverPolynomial (1 : K) sigma gamma 1 1)) := by
  let phi : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  rw [map_shiftedTraceCoverPolynomial phi (1 : K) sigma gamma 1 1]
  simp only [map_one]
  have h2L : (2 : AlgebraicClosure K) ≠ 0 := by
    change phi (2 : K) ≠ 0
    exact (map_ne_zero_iff phi phi.injective).mpr h2
  have hsigmaL : phi sigma ≠ 0 :=
    (map_ne_zero_iff phi phi.injective).mpr hsigma
  have hD2L :
      shiftedTraceEvenObstruction (phi sigma) (phi gamma) ≠ 0 := by
    have hmap : phi (shiftedTraceEvenObstruction sigma gamma) ≠ 0 :=
      (map_ne_zero_iff phi phi.injective).mpr hD2
    simpa [shiftedTraceEvenObstruction, map_ofNat] using hmap
  exact shiftedTraceDegreeOneCoverPolynomial_irreducible
    (phi sigma) (phi gamma) h2L hsigmaL hD2L

/-- The rational discriminant remains a non-square under the sharp
non-toric hypothesis. -/
theorem
    shiftedTraceDegreeOneRationalDiscriminant_not_isSquare_of_not_toric
    (sigma gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : sigma ≠ 0)
    (hnotToric : ¬ (sigma = 1 ∧ gamma = 0)) :
    ¬ IsSquare
      (shiftedTraceDegreeOneRationalLinearCoefficient sigma gamma ^ 2 -
        4 * shiftedTraceDegreeOneRationalConstant) := by
  intro hSquare
  apply shiftedTraceDegreeOneBranchPolynomial_not_isSquare_of_not_toric
    sigma gamma h2 hsigma hnotToric
  have hX4 : IsSquare (RatFunc.X ^ 4 : RatFunc K) := by
    refine ⟨RatFunc.X ^ 2, ?_⟩
    ring
  have hProduct := hSquare.mul hX4
  rw [shiftedTraceDegreeOneRationalDiscriminant sigma gamma] at hProduct
  simpa [RatFunc.X_ne_zero] using hProduct

/-- Sharp non-toric irreducibility of the birational monic quadratic. -/
theorem
    shiftedTraceDegreeOneRationalMonicPolynomial_irreducible_of_not_toric
    (sigma gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : sigma ≠ 0)
    (hnotToric : ¬ (sigma = 1 ∧ gamma = 0)) :
    Irreducible
      (shiftedTraceDegreeOneRationalMonicPolynomial sigma gamma) := by
  rw [shiftedTraceDegreeOneRationalMonicPolynomial]
  exact monicQuadratic_irreducible_of_discriminant_not_isSquare
    (shiftedTraceDegreeOneRationalLinearCoefficient sigma gamma)
    shiftedTraceDegreeOneRationalConstant
    (shiftedTraceDegreeOneRationalDiscriminant_not_isSquare_of_not_toric
      sigma gamma h2 hsigma hnotToric)

/-- Sharp non-toric irreducibility after clearing the birational
denominator. -/
theorem
    map_shiftedTraceDegreeOneBirationalPolynomial_irreducible_of_not_toric
    (sigma gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : sigma ≠ 0)
    (hnotToric : ¬ (sigma = 1 ∧ gamma = 0)) :
    Irreducible
      ((shiftedTraceDegreeOneBirationalPolynomial sigma gamma).map
        (algebraMap K[X] (RatFunc K))) := by
  rw [map_shiftedTraceDegreeOneBirationalPolynomial]
  have hCoefficient : IsUnit
      (C (-(RatFunc.X ^ 2)) : Polynomial (RatFunc K)) :=
    Polynomial.isUnit_C.mpr <| isUnit_iff_ne_zero.mpr <| by
      exact neg_ne_zero.mpr (pow_ne_zero 2 RatFunc.X_ne_zero)
  exact (irreducible_isUnit_mul hCoefficient).2
    (shiftedTraceDegreeOneRationalMonicPolynomial_irreducible_of_not_toric
      sigma gamma h2 hsigma hnotToric)

/-- Sharp non-toric irreducibility of the degree-one iterated polynomial. -/
theorem shiftedTraceDegreeOneIteratedPolynomial_irreducible_of_not_toric
    (sigma gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : sigma ≠ 0)
    (hnotToric : ¬ (sigma = 1 ∧ gamma = 0)) :
    Irreducible (shiftedTraceDegreeOneIteratedPolynomial sigma gamma) := by
  have hBirational : Irreducible
      ((shiftedTraceDegreeOneBirationalPolynomial sigma gamma).map
        (algebraMap K[X] (RatFunc K))) :=
    map_shiftedTraceDegreeOneBirationalPolynomial_irreducible_of_not_toric
      sigma gamma h2 hsigma hnotToric
  have hyUnit : IsUnit (C RatFunc.X : Polynomial (RatFunc K)) :=
    Polynomial.isUnit_C.mpr <| isUnit_iff_ne_zero.mpr RatFunc.X_ne_zero
  have hScaled : Irreducible
      (BGS.Markoff.polynomialVariableScaleEquiv
        (shiftedTraceDegreeOneFractionScaleUnit (K := K))
        ((shiftedTraceDegreeOneIteratedPolynomial sigma gamma).map
          (algebraMap K[X] (RatFunc K)))) := by
    rw [polynomialVariableScaleEquiv_map_shiftedTraceDegreeOne]
    exact (irreducible_isUnit_mul hyUnit).2 hBirational
  have hFraction : Irreducible
      ((shiftedTraceDegreeOneIteratedPolynomial sigma gamma).map
        (algebraMap K[X] (RatFunc K))) := by
    have hback := hScaled.map
      (BGS.Markoff.polynomialVariableScaleEquiv
        (shiftedTraceDegreeOneFractionScaleUnit (K := K))).symm
    simpa using hback
  exact (shiftedTraceDegreeOneIteratedPolynomial_isPrimitive
    sigma gamma hsigma).irreducible_iff_irreducible_map_fraction_map.mpr hFraction

/-- The normalized degree-one cover is irreducible outside the unique toric
pair. -/
theorem shiftedTraceDegreeOneCoverPolynomial_irreducible_of_not_toric
    (sigma gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : sigma ≠ 0)
    (hnotToric : ¬ (sigma = 1 ∧ gamma = 0)) :
    Irreducible (shiftedTraceCoverPolynomial (1 : K) sigma gamma 1 1) := by
  have hImage := finTwoToIteratedPolynomial_shiftedTraceDegreeOne sigma gamma
  have hIterated :=
    shiftedTraceDegreeOneIteratedPolynomial_irreducible_of_not_toric
      sigma gamma h2 hsigma hnotToric
  rw [← hImage] at hIterated
  have hback := hIterated.map
    (BGS.Markoff.finTwoToIteratedPolynomial (K := K)).symm
  simpa using hback

/-- The degree-one cover is absolutely irreducible away from the unique toric
pair `(sigma, gamma) = (1, 0)`.  In particular, the common-even obstruction
is not required by the middle-game Corvaja--Zannier application. -/
theorem
    shiftedTraceDegreeOneCoverPolynomial_absolutelyIrreducible_of_not_toric
    (sigma gamma : K) (h2 : (2 : K) ≠ 0)
    (hsigma : sigma ≠ 0)
    (hnotToric : ¬ (sigma = 1 ∧ gamma = 0)) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (shiftedTraceCoverPolynomial (1 : K) sigma gamma 1 1)) := by
  let phi : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  rw [map_shiftedTraceCoverPolynomial phi (1 : K) sigma gamma 1 1]
  simp only [map_one]
  have h2L : (2 : AlgebraicClosure K) ≠ 0 := by
    change phi (2 : K) ≠ 0
    exact (map_ne_zero_iff phi phi.injective).mpr h2
  have hsigmaL : phi sigma ≠ 0 :=
    (map_ne_zero_iff phi phi.injective).mpr hsigma
  have hnotToricL : ¬ (phi sigma = 1 ∧ phi gamma = 0) := by
    rintro ⟨hsigmaOne, hgammaZero⟩
    apply hnotToric
    constructor
    · apply phi.injective
      simpa using hsigmaOne
    · apply phi.injective
      simpa using hgammaZero
  exact shiftedTraceDegreeOneCoverPolynomial_irreducible_of_not_toric
    (phi sigma) (phi gamma) h2L hsigmaL hnotToricL

end DegreeOneCover

end

end GenMarkoff
