import BGS.Markoff.Assembly.ExplicitPuncturedTransitivity
import GenMarkoff.General.Assembly.ReasonableUnifiedEndgame
import GenMarkoff.General.Assembly.StrongApproximation

/-!
# Explicit cutoff for fixed-coefficient strong approximation

The analytic part of the generalized proof is uniform in the coefficient
triple.  A genuinely coefficient-independent cutoff for the integral theorem
is impossible: a fixed nonzero integral coefficient, or one of the finitely
many discriminants defining generic reduction, may be divisible by an
arbitrarily large prime.  Accordingly this file separates:

* `universalStrongApproximationCutoff`, a closed coefficient-independent
  constant covering every analytic estimate and the classical BGS branch;
* `explicitStrongApproximationCutoff a`, which also includes the finite
  bad-reduction and coefficient-survival bounds for the three cyclic
  orientations of the fixed triple `a`.
-/

namespace GenMarkoff.General.Assembly

open GenMarkoff.General.Cage

noncomputable section

/-- The elementary preliminary cutoff in the pinned BGS formalization of the
classical all-zero surface. -/
def classicalStrongApproximationCutoff : ℕ :=
  BGS.Markoff.preliminaryStrongApproximationCutoff

theorem classicalStrongApproximationCutoff_eq :
    classicalStrongApproximationCutoff =
      2 ^ 1833 * (48 ^ 3 + 1) ^ 10 + 1 := by
  exact BGS.Markoff.preliminaryStrongApproximationCutoff_eq

/-- One coefficient-independent constant covering both the generalized
analytic estimates and the classical all-zero branch. -/
def universalStrongApproximationCutoff : ℕ :=
  GenMarkoff.General.Explicit.reasonableAnalyticCutoff

theorem universalStrongApproximationCutoff_eq_reasonable :
    universalStrongApproximationCutoff =
      GenMarkoff.General.Explicit.reasonableAnalyticCutoff :=
  rfl

theorem universalStrongApproximationCutoff_lt_ten_pow_oneThousand :
    universalStrongApproximationCutoff < 10 ^ 1000 := by
  rw [universalStrongApproximationCutoff_eq_reasonable]
  exact
    GenMarkoff.General.Explicit.reasonableAnalyticCutoff_lt_ten_pow_oneThousand

/-- The finite arithmetic cutoff needed after choosing one coefficient as
the first coefficient. -/
def orientedArithmeticCutoff (a : Coefficients ℤ) : ℕ :=
  max
    (max 5
      (max a.multiplier.natAbs
        (max (a.a1 ^ 2 - 4).natAbs
          (max (a.a2 ^ 2 - 4).natAbs
            (a.a3 ^ 2 - 4).natAbs)) + 1))
    (a.a1.natAbs + 1)

/-- Explicit cutoff for a fixed integral coefficient triple.  All three
cyclic orientations occur because cyclic transport is simultaneous on
coefficients and coordinates. -/
def explicitStrongApproximationCutoff (a : Coefficients ℤ) : ℕ :=
  max universalStrongApproximationCutoff
    (max (orientedArithmeticCutoff a)
      (max
        (orientedArithmeticCutoff (directedCycleLeftCoefficients a))
        (orientedArithmeticCutoff (directedCycleRightCoefficients a))))

/-- The coefficient triple singled out in the running generalized example. -/
def oneThreeThreeCoefficients : Coefficients ℤ :=
  ⟨1, 3, 3⟩

theorem orientedArithmeticCutoff_oneThreeThree :
    orientedArithmeticCutoff oneThreeThreeCoefficients = 11 := by
  norm_num [orientedArithmeticCutoff, genericAdmissibilityCutoff,
    integralBadReductionHeight, firstCoefficientNonzeroCutoff,
    oneThreeThreeCoefficients, Coefficients.multiplier]

theorem orientedArithmeticCutoff_cycleLeft_oneThreeThree :
    orientedArithmeticCutoff
        (directedCycleLeftCoefficients oneThreeThreeCoefficients) = 11 := by
  norm_num [orientedArithmeticCutoff, genericAdmissibilityCutoff,
    integralBadReductionHeight, firstCoefficientNonzeroCutoff,
    oneThreeThreeCoefficients, Coefficients.multiplier,
    directedCycleLeftCoefficients]

theorem orientedArithmeticCutoff_cycleRight_oneThreeThree :
    orientedArithmeticCutoff
        (directedCycleRightCoefficients oneThreeThreeCoefficients) = 11 := by
  norm_num [orientedArithmeticCutoff, genericAdmissibilityCutoff,
    integralBadReductionHeight, firstCoefficientNonzeroCutoff,
    oneThreeThreeCoefficients, Coefficients.multiplier,
    directedCycleRightCoefficients]

/-- For `a = (1,3,3)`, the coefficient-dependent arithmetic maximum is
negligible, so the full strong-approximation cutoff is the 627-digit
reasonable analytic constant. -/
theorem explicitStrongApproximationCutoff_oneThreeThree_eq_reasonable :
    explicitStrongApproximationCutoff oneThreeThreeCoefficients =
      GenMarkoff.General.Explicit.reasonableAnalyticCutoff := by
  rw [explicitStrongApproximationCutoff,
    universalStrongApproximationCutoff_eq_reasonable,
    orientedArithmeticCutoff_oneThreeThree,
    orientedArithmeticCutoff_cycleLeft_oneThreeThree,
    orientedArithmeticCutoff_cycleRight_oneThreeThree]
  simp only [max_self]
  apply max_eq_left
  rw [GenMarkoff.General.Explicit.reasonableAnalyticCutoff_eq,
    GenMarkoff.General.Explicit.reasonableAnalyticOpenCutoff,
    GenMarkoff.General.Explicit.reasonableFrontierCoefficient]
  have hpow : 1 ≤ 2 ^ 1828 :=
    Nat.one_le_pow 1828 2 (by norm_num)
  have hcoefficient : 11 ≤ (32 * 193 ^ 6) ^ 5 := by
    norm_num
  have hmul :=
    Nat.mul_le_mul_left ((32 * 193 ^ 6) ^ 5) hpow
  norm_num only [mul_one] at hmul
  omega

theorem explicitStrongApproximationCutoff_oneThreeThree_lt_ten_pow_oneThousand :
    explicitStrongApproximationCutoff oneThreeThreeCoefficients <
      10 ^ 1000 := by
  rw [explicitStrongApproximationCutoff_oneThreeThree_eq_reasonable]
  exact
    GenMarkoff.General.Explicit.reasonableAnalyticCutoff_lt_ten_pow_oneThousand

/-- The pinned classical branch at its displayed closed cutoff. -/
theorem classicalZero_vietaStrongApproximationAt_of_explicitCutoff
    (p : ℕ) (hp : p.Prime)
    (hpCutoff : classicalStrongApproximationCutoff ≤ p) :
    VietaStrongApproximationAt (classicalZeroCoefficients ℤ) p hp := by
  have hpConcrete :
      2 ^ 1833 * (48 ^ 3 + 1) ^ 10 + 1 ≤ p := by
    simpa only [classicalStrongApproximationCutoff_eq] using hpCutoff
  apply classicalZero_vietaStrongApproximationAt_of_BGS p hp
  apply
    (BGS.Markoff.puncturedMarkoffTransitiveAt_iff_strongApproximationAt
      p hp).mp
  exact
    BGS.Markoff.puncturedMarkoffTransitiveAt_of_concretePreliminaryBound
      p hp hpConcrete

/-- Explicit fixed-orientation generalized branch. -/
theorem
    IntegrallyNondegenerate.vietaStrongApproximationAt_of_a1_ne_zero_of_explicitCutoffs
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (ha1 : a.a1 ≠ 0)
    (p : ℕ) (hp : p.Prime)
    (hpAnalytic :
      GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    (hpArithmetic : orientedArithmeticCutoff a ≤ p) :
    VietaStrongApproximationAt a p hp := by
  have hpGeneric : genericAdmissibilityCutoff a ≤ p :=
    (Nat.le_max_left _ _).trans hpArithmetic
  have hpFirst : firstCoefficientNonzeroCutoff a ≤ p :=
    (Nat.le_max_right _ _).trans hpArithmetic
  have hgeneric : GenericAdmissibleAt a p :=
    ha.genericAdmissibleAt_of_cutoff_le hpGeneric
  have hA1 : (modCoefficients a p).a1 ^ 2 ≠ 4 := hgeneric.2.1
  have hA2 : (modCoefficients a p).a2 ^ 2 ≠ 4 := hgeneric.2.2.1
  have hA3 : (modCoefficients a p).a3 ^ 2 ≠ 4 := hgeneric.2.2.2
  have ha1Mod : (modCoefficients a p).a1 ≠ 0 :=
    modCoefficients_a1_ne_zero_of_firstCoefficientNonzeroCutoff_le
      ha1 hpFirst
  have hnormalizationMoving :
      ((modCoefficients a p).a3, (modCoefficients a p).a1) ≠
        (0, 0) := by
    intro hzero
    exact ha1Mod (congrArg Prod.snd hzero)
  have hrelayMoving :
      ((modCoefficients a p).a1, (modCoefficients a p).a2) ≠
        (0, 0) := by
    intro hzero
    exact ha1Mod (congrArg Prod.fst hzero)
  letI : Fact p.Prime := ⟨hp⟩
  exact
    vietaStrongApproximationAt_of_componentwise_canonicalFirstAxisPrimitiveSplit
      a p hp
      (IntegrallyNondegenerate.every_puncturedRotationComponent_reaches_canonicalFirstAxisPrimitiveSplit_of_reasonableCutoff
        ha p hp hpAnalytic hpGeneric)
      (canonicalFirstAxisPrimitiveSplitVietaCage_of_reasonableCutoff
        p hpAnalytic (modCoefficients a p)
          hgeneric.1 hA1 hA2 hA3
          hnormalizationMoving hrelayMoving)

/-- Full-Vieta strong approximation at every prime beyond the explicit
cutoff attached to the fixed coefficient triple. -/
theorem IntegrallyNondegenerate.vietaStrongApproximationAt_of_explicitCutoff
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (p : ℕ) (hp : p.Prime)
    (hpCutoff : explicitStrongApproximationCutoff a ≤ p) :
    VietaStrongApproximationAt a p hp := by
  have hparts :
      universalStrongApproximationCutoff ≤ p ∧
        orientedArithmeticCutoff a ≤ p ∧
        orientedArithmeticCutoff (directedCycleLeftCoefficients a) ≤ p ∧
        orientedArithmeticCutoff (directedCycleRightCoefficients a) ≤ p := by
    simpa only [explicitStrongApproximationCutoff, max_le_iff] using hpCutoff
  obtain ⟨hpUniversal, hpA, hpLeft, hpRight⟩ := hparts
  have hpAnalytic :
      GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p :=
    hpUniversal
  have hpClassical : classicalStrongApproximationCutoff ≤ p := by
    have hclassical :
        classicalStrongApproximationCutoff ≤
          GenMarkoff.General.Explicit.reasonableAnalyticCutoff := by
      simpa [classicalStrongApproximationCutoff] using
        GenMarkoff.General.Explicit.preliminaryStrongApproximationCutoff_le_reasonableAnalyticCutoff
    exact hclassical.trans hpUniversal
  by_cases ha1 : a.a1 ≠ 0
  · exact
      IntegrallyNondegenerate.vietaStrongApproximationAt_of_a1_ne_zero_of_explicitCutoffs
        ha ha1 p hp hpAnalytic hpA
  by_cases ha2 : a.a2 ≠ 0
  · have hcycled :
        IntegrallyNondegenerate (directedCycleLeftCoefficients a) :=
      (integrallyNondegenerate_directedCycleLeft_iff a).2 ha
    have hcycledA1 :
        (directedCycleLeftCoefficients a).a1 ≠ 0 := by
      simpa [directedCycleLeftCoefficients] using ha2
    apply vietaStrongApproximationAt_of_directedCycleLeft a p hp
    exact
      IntegrallyNondegenerate.vietaStrongApproximationAt_of_a1_ne_zero_of_explicitCutoffs
        hcycled hcycledA1 p hp hpAnalytic hpLeft
  by_cases ha3 : a.a3 ≠ 0
  · have hcycled :
        IntegrallyNondegenerate (directedCycleRightCoefficients a) :=
      (integrallyNondegenerate_directedCycleRight_iff a).2 ha
    have hcycledA1 :
        (directedCycleRightCoefficients a).a1 ≠ 0 := by
      simpa [directedCycleRightCoefficients] using ha3
    apply vietaStrongApproximationAt_of_directedCycleRight a p hp
    exact
      IntegrallyNondegenerate.vietaStrongApproximationAt_of_a1_ne_zero_of_explicitCutoffs
        hcycled hcycledA1 p hp hpAnalytic hpRight
  · have ha1Zero : a.a1 = 0 := not_ne_iff.mp ha1
    have ha2Zero : a.a2 = 0 := not_ne_iff.mp ha2
    have ha3Zero : a.a3 = 0 := not_ne_iff.mp ha3
    have hzero : a = classicalZeroCoefficients ℤ := by
      ext <;>
        simp [classicalZeroCoefficients, ha1Zero, ha2Zero, ha3Zero]
    rw [hzero]
    exact
      classicalZero_vietaStrongApproximationAt_of_explicitCutoff
        p hp hpClassical

/-- Rotation-group strong approximation at the same explicit cutoff. -/
theorem IntegrallyNondegenerate.rotationStrongApproximationAt_of_explicitCutoff
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (p : ℕ) (hp : p.Prime)
    (hpCutoff : explicitStrongApproximationCutoff a ≤ p) :
    RotationStrongApproximationAt a p hp := by
  have hpUniversal : universalStrongApproximationCutoff ≤ p :=
    (Nat.le_max_left _ _).trans hpCutoff
  have hpAnalytic :
      GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p :=
    hpUniversal
  have hpGeneric : genericAdmissibilityCutoff a ≤ p := by
    have hpOriented : orientedArithmeticCutoff a ≤ p :=
      (Nat.le_max_left _ _).trans
        ((Nat.le_max_right _ _).trans hpCutoff)
    exact (Nat.le_max_left _ _).trans hpOriented
  exact
    rotationStrongApproximationAt_of_vietaStrongApproximationAt
      a p hp
      (GenMarkoff.General.Explicit.seven_le_reasonableAnalyticCutoff.trans
        hpAnalytic)
      (ha.genericAdmissibleAt_of_cutoff_le hpGeneric)
      (IntegrallyNondegenerate.vietaStrongApproximationAt_of_explicitCutoff
        ha p hp hpCutoff)

/-- Surjectivity of coordinatewise reduction at the same explicit cutoff. -/
theorem IntegrallyNondegenerate.reduction_surjective_of_explicitCutoff
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (p : ℕ) (hp : p.Prime)
    (hpCutoff : explicitStrongApproximationCutoff a ≤ p) :
    Function.Surjective
      ((fixedIntegralCoefficientSurfaceFunctor a).map
        (CommRingCat.ofHom (Int.castRingHom (ZMod p)))) :=
  reduction_surjective_of_vietaStrongApproximationAt
    a p hp
      (IntegrallyNondegenerate.vietaStrongApproximationAt_of_explicitCutoff
        ha p hp hpCutoff)

/-- Comparator-facing form of explicit reduction surjectivity.  The cutoff
uses the displayed analytic constant and the public one-orientation arithmetic
cutoff directly in the hypothesis. -/
theorem IntegrallyNondegenerate.reduction_surjective_of_concreteExplicitCutoff
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (p : ℕ) (hp : p.Prime)
    (hpCutoff :
      max ((32 * 193 ^ 6) ^ 5 * 2 ^ 1828 + 1)
        (max (orientedArithmeticCutoff a)
          (max (orientedArithmeticCutoff ⟨a.a2, a.a3, a.a1⟩)
            (orientedArithmeticCutoff ⟨a.a3, a.a1, a.a2⟩))) ≤ p) :
    Function.Surjective
      ((fixedIntegralCoefficientSurfaceFunctor a).map
        (CommRingCat.ofHom (Int.castRingHom (ZMod p)))) := by
  apply IntegrallyNondegenerate.reduction_surjective_of_explicitCutoff
    ha p hp
  simpa only [explicitStrongApproximationCutoff,
    universalStrongApproximationCutoff,
    GenMarkoff.General.Explicit.reasonableAnalyticCutoff_eq,
    GenMarkoff.General.Explicit.reasonableAnalyticOpenCutoff,
    GenMarkoff.General.Explicit.reasonableFrontierCoefficient,
    orientedArithmeticCutoff, genericAdmissibilityCutoff,
    integralBadReductionHeight, firstCoefficientNonzeroCutoff,
    directedCycleLeftCoefficients, directedCycleRightCoefficients] using
      hpCutoff

end

end GenMarkoff.General.Assembly
