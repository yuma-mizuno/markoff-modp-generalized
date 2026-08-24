import GenMarkoff.General.Cage.ConnectingDirectedRelay
import GenMarkoff.General.Cage.ConnectingSevenPlaneEstimates
import GenMarkoff.General.Endgame.CageReadyPrimitiveCount
import BGS.NumberTheory.OneSidedPrimitiveWitness

/-!
# A two-root bridge from a connecting first-axis fiber

Once the source first-axis fiber is already primitive and connecting, no
rotation coset has to be retained.  A common adjacent axis therefore needs
only two simultaneous square roots:

* one root of the incidence discriminant from the fixed source trace;
* one nonzero root of a fixed nonsquare multiple of the target centered
  norm.

The coefficient order remains explicit throughout.  The first construction
targets the second axis.  A later wrapper targets the third axis by swapping
the second and third coefficients together with the second and third
coordinates; it never treats a coordinate swap as a symmetry of a fixed
unequal-coefficient surface.
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff
open Polynomial
open GenMarkoff.General.Assembly
open GenMarkoff.General.Endgame
open scoped ArithmeticFunction.Moebius BigOperators

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- The three nonempty products of two coprime squarefree nonunits are
nonsquares in the rational function field. -/
theorem twoRadicandProducts_not_isSquare_ratFunc
    {f g : K[X]}
    (hf : Squarefree f) (hg : Squarefree g)
    (hfg : IsCoprime f g)
    (hfUnit : ¬ IsUnit f) (hgUnit : ¬ IsUnit g) :
    (¬ IsSquare (algebraMap K[X] (RatFunc K) f)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) g)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g))) := by
  have hfgSquarefree :
      Squarefree (f * g) :=
    squarefree_mul_iff.mpr ⟨hfg.isRelPrime, hf, hg⟩
  exact
    ⟨BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        hf hfUnit,
      BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        hg hgUnit,
      BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        hfgSquarefree (by
          intro hunit
          exact hfUnit (IsUnit.mul_iff.mp hunit).1)⟩

/-- The incidence pullback and the reduced target-centered-norm pullback
give three nontrivial square classes. -/
theorem connectingTwoRadicandProducts_not_isSquare_ratFunc
    (h2 : (2 : K) ≠ 0)
    {a : Coefficients K} {xi : K}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hobstruction : incidenceCenteredNormObstruction a xi ≠ 0)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    let f := incidencePulledRadicand a xi d
    let g := centeredNormReducedPulledRadicand a.a3 a.a1 d
    (¬ IsSquare (algebraMap K[X] (RatFunc K) f)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) g)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g))) := by
  dsimp only
  have hf :
      Squarefree (incidencePulledRadicand a xi d) :=
    (incidencePulledRadicand_separable
      h2 hA2 hxi hd hdegree).squarefree
  have hg :
      Squarefree
        (centeredNormReducedPulledRadicand a.a3 a.a1 d) :=
    centeredNormReducedPulledRadicand_squarefree
      hA3 hA1 hmoving hd hdegree
  have hcoprimeFull :
      IsCoprime (incidencePulledRadicand a xi d)
        (centeredNormPulledRadicand a.a3 a.a1 d) :=
    incidencePulledRadicand_isCoprime_centeredNormPulledRadicand
      hxi hobstruction hd
  have hcoprime :
      IsCoprime (incidencePulledRadicand a xi d)
        (centeredNormReducedPulledRadicand a.a3 a.a1 d) :=
    IsCoprime.of_isCoprime_of_dvd_right hcoprimeFull
      (centeredNormReducedPulledRadicand_dvd a.a3 a.a1 d)
  exact
    twoRadicandProducts_not_isSquare_ratFunc
      hf hg hcoprime
      (incidencePulledRadicand_not_isUnit hxi hd)
      (centeredNormReducedPulledRadicand_not_isUnit
        a.a3 a.a1 hd)

/-- Multiplying the second radicand by a nonzero polynomial square preserves
all three relevant nonsquare classes. -/
theorem three_not_isSquare_replace_second_by_square_mul
    {f q g : K[X]}
    (hq : q ≠ 0)
    (hs :
      (¬ IsSquare (algebraMap K[X] (RatFunc K) f)) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) g)) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g)))) :
    (¬ IsSquare (algebraMap K[X] (RatFunc K) f)) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K) (q ^ 2 * g))) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K) (f * (q ^ 2 * g)))) := by
  let i : K[X] →+* RatFunc K := algebraMap K[X] (RatFunc K)
  have hiq : i q ≠ 0 :=
    (map_ne_zero_iff i (RatFunc.algebraMap_injective K)).2 hq
  refine ⟨hs.1, ?_, ?_⟩
  · rw [map_mul, map_pow]
    exact fun hsquare =>
      hs.2.1 ((isSquare_sq_mul_iff (i q) (i g) hiq).1 hsquare)
  · rw [show f * (q ^ 2 * g) = q ^ 2 * (f * g) by ring,
      map_mul, map_pow]
    exact fun hsquare =>
      hs.2.2
        ((isSquare_sq_mul_iff (i q) (i (f * g)) hiq).1 hsquare)

/-- The original incidence and centered-norm pullbacks retain all three
nonsquare classes after extension to the algebraic closure. -/
theorem
    connectingTwoOriginalRadicandProducts_not_isSquare_algebraicClosure
    (h2 : (2 : K) ≠ 0)
    {a : Coefficients K} {xi : K}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hobstruction : incidenceCenteredNormObstruction a xi ≠ 0)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    let phi : K →+* AlgebraicClosure K :=
      algebraMap K (AlgebraicClosure K)
    let f := (incidencePulledRadicand a xi d).map phi
    let g :=
      (centeredNormPulledRadicand a.a3 a.a1 d).map phi
    (¬ IsSquare
      (algebraMap (AlgebraicClosure K)[X]
        (RatFunc (AlgebraicClosure K)) f)) ∧
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) g)) ∧
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) (f * g))) := by
  dsimp only
  let phi : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  let aE : Coefficients (AlgebraicClosure K) :=
    GenMarkoff.General.MiddleGame.mapCoefficients phi a
  have hphi : Function.Injective phi := phi.injective
  have h2E : (2 : AlgebraicClosure K) ≠ 0 := by
    simpa only [← map_ofNat phi] using
      (map_ne_zero_iff phi hphi).2 h2
  have hA1E : aE.a1 ^ 2 ≠ 4 := by
    change (phi a.a1) ^ 2 ≠ 4
    intro heq
    apply hA1
    apply hphi
    simpa only [map_pow, map_ofNat] using heq
  have hA2E : aE.a2 ^ 2 ≠ 4 := by
    change (phi a.a2) ^ 2 ≠ 4
    intro heq
    apply hA2
    apply hphi
    simpa only [map_pow, map_ofNat] using heq
  have hA3E : aE.a3 ^ 2 ≠ 4 := by
    change (phi a.a3) ^ 2 ≠ 4
    intro heq
    apply hA3
    apply hphi
    simpa only [map_pow, map_ofNat] using heq
  have hmovingE : (aE.a3, aE.a1) ≠ (0, 0) := by
    simpa only [aE,
      GenMarkoff.General.MiddleGame.mapCoefficients_a1,
      GenMarkoff.General.MiddleGame.mapCoefficients_a3] using
      movingCoefficientPair_ne_zero_map phi hphi hmoving
  have hxiE :
      OrderedTraceCandidateRegular aE.a1 aE.a2 aE.a3 (phi xi) := by
    simpa only [aE,
      GenMarkoff.General.MiddleGame.mapCoefficients_a1,
      GenMarkoff.General.MiddleGame.mapCoefficients_a2,
      GenMarkoff.General.MiddleGame.mapCoefficients_a3] using
      GenMarkoff.General.MiddleGame.orderedTraceCandidateRegular_map
        phi hphi hxi
  have hobstructionE :
      incidenceCenteredNormObstruction aE (phi xi) ≠ 0 := by
    rw [← map_incidenceCenteredNormObstruction]
    exact (map_ne_zero_iff phi hphi).2 hobstruction
  have hdegreeE : (d : AlgebraicClosure K) ≠ 0 := by
    have hdegreeMap : phi (d : K) ≠ 0 :=
      (map_ne_zero_iff phi hphi).2 hdegree
    simpa only [map_natCast] using hdegreeMap
  let fE := incidencePulledRadicand aE (phi xi) d
  let rE := centeredNormReducedPulledRadicand aE.a3 aE.a1 d
  let qE := centeredNormForcedFactor aE.a3 aE.a1 d
  have hsReduced :
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) fE)) ∧
        (¬ IsSquare
          (algebraMap (AlgebraicClosure K)[X]
            (RatFunc (AlgebraicClosure K)) rE)) ∧
        (¬ IsSquare
          (algebraMap (AlgebraicClosure K)[X]
            (RatFunc (AlgebraicClosure K)) (fE * rE))) :=
    connectingTwoRadicandProducts_not_isSquare_ratFunc
      h2E hA1E hA2E hA3E hmovingE hxiE hobstructionE
      hd hdegreeE
  have hqE : qE ≠ 0 :=
    centeredNormForcedFactor_ne_zero aE.a3 aE.a1 hd
  have hsFull :
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) fE)) ∧
        (¬ IsSquare
          (algebraMap (AlgebraicClosure K)[X]
            (RatFunc (AlgebraicClosure K))
            (centeredNormPulledRadicand aE.a3 aE.a1 d))) ∧
        (¬ IsSquare
          (algebraMap (AlgebraicClosure K)[X]
            (RatFunc (AlgebraicClosure K))
            (fE *
              centeredNormPulledRadicand aE.a3 aE.a1 d))) := by
    rw [centeredNormPulledRadicand_eq_forcedFactor_sq_mul_reduced]
    exact
      three_not_isSquare_replace_second_by_square_mul hqE hsReduced
  simpa only [fE, aE, phi,
    GenMarkoff.General.MiddleGame.mapCoefficients_a1,
    GenMarkoff.General.MiddleGame.mapCoefficients_a3,
    ← map_incidencePulledRadicand,
    ← map_centeredNormPulledRadicand] using hsFull

/-- Arbitrary nonzero constants, including the inverse-character scalar on
the centered radicand, preserve the three geometric nonsquare classes. -/
theorem
    connectingTwoOriginalRadicandProducts_scalarMultiples_not_isSquare_algebraicClosure
    (h2 : (2 : K) ≠ 0)
    {a : Coefficients K} {xi : K}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hobstruction : incidenceCenteredNormObstruction a xi ≠ 0)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0)
    {cf cg cfg : AlgebraicClosure K}
    (hcf : cf ≠ 0) (hcg : cg ≠ 0) (hcfg : cfg ≠ 0) :
    let phi : K →+* AlgebraicClosure K :=
      algebraMap K (AlgebraicClosure K)
    let f := (incidencePulledRadicand a xi d).map phi
    let g :=
      (centeredNormPulledRadicand a.a3 a.a1 d).map phi
    (¬ IsSquare
      (algebraMap (AlgebraicClosure K)[X]
        (RatFunc (AlgebraicClosure K)) (C cf * f))) ∧
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) (C cg * g))) ∧
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) (C cfg * (f * g)))) := by
  dsimp only
  obtain ⟨hf, hg, hfg⟩ :=
    connectingTwoOriginalRadicandProducts_not_isSquare_algebraicClosure
      h2 hA1 hA2 hA3 hmoving hxi hobstruction hd hdegree
  exact
    ⟨not_isSquare_C_mul_of_not_isSquare_of_isAlgClosed hcf hf,
      not_isSquare_C_mul_of_not_isSquare_of_isAlgClosed hcg hg,
      not_isSquare_C_mul_of_not_isSquare_of_isAlgClosed hcfg hfg⟩

/-- Two square roots above a fixed affine parameter. -/
structure TwoSquareRootFiber
    (f g : K[X]) (parameter : K) where
  firstRoot : K
  secondRoot : K
  firstEquation : firstRoot ^ 2 = f.eval parameter
  secondEquation : secondRoot ^ 2 = g.eval parameter

@[ext]
theorem TwoSquareRootFiber.ext
    {f g : K[X]} {parameter : K}
    {x y : TwoSquareRootFiber f g parameter}
    (hfirst : x.firstRoot = y.firstRoot)
    (hsecond : x.secondRoot = y.secondRoot) :
    x = y := by
  cases x
  cases y
  simp_all

instance twoSquareRootFiberFinite
    [Finite K] (f g : K[X]) (parameter : K) :
    Finite (TwoSquareRootFiber f g parameter) :=
  Finite.of_injective
    (fun z => (z.firstRoot, z.secondRoot))
    (by
      intro x y h
      exact TwoSquareRootFiber.ext
        (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- The affine two-root cover, including the zero parameter. -/
structure TwoRootPowerCover (f g : K[X]) where
  parameter : K
  firstRoot : K
  secondRoot : K
  firstEquation : firstRoot ^ 2 = f.eval parameter
  secondEquation : secondRoot ^ 2 = g.eval parameter

@[ext]
theorem TwoRootPowerCover.ext
    {f g : K[X]} {x y : TwoRootPowerCover f g}
    (hparameter : x.parameter = y.parameter)
    (hfirst : x.firstRoot = y.firstRoot)
    (hsecond : x.secondRoot = y.secondRoot) :
    x = y := by
  cases x
  cases y
  simp_all

instance twoRootPowerCoverFinite
    [Finite K] (f g : K[X]) :
    Finite (TwoRootPowerCover f g) :=
  Finite.of_injective
    (fun z => (z.parameter, z.firstRoot, z.secondRoot))
    (by
      intro x y h
      exact TwoRootPowerCover.ext
        (congrArg (fun z => z.1) h)
        (congrArg (fun z => z.2.1) h)
        (congrArg (fun z => z.2.2) h))

/-- The two-root cover with nonzero parameter. -/
structure UnitTwoRootPowerCover (f g : K[X]) where
  parameter : Kˣ
  firstRoot : K
  secondRoot : K
  firstEquation : firstRoot ^ 2 = f.eval (parameter : K)
  secondEquation : secondRoot ^ 2 = g.eval (parameter : K)

@[ext]
theorem UnitTwoRootPowerCover.ext
    {f g : K[X]} {x y : UnitTwoRootPowerCover f g}
    (hparameter : x.parameter = y.parameter)
    (hfirst : x.firstRoot = y.firstRoot)
    (hsecond : x.secondRoot = y.secondRoot) :
    x = y := by
  cases x
  cases y
  simp_all

instance unitTwoRootPowerCoverFinite
    [Finite K] (f g : K[X]) :
    Finite (UnitTwoRootPowerCover f g) :=
  Finite.of_injective
    (fun z => (z.parameter, z.firstRoot, z.secondRoot))
    (by
      intro x y h
      exact UnitTwoRootPowerCover.ext
        (congrArg (fun z => z.1) h)
        (congrArg (fun z => z.2.1) h)
        (congrArg (fun z => z.2.2) h))

/-- Unit-cover points whose centered-norm root is nonzero. -/
def GoodUnitTwoRootPowerCover (f g : K[X]) :=
  {z : UnitTwoRootPowerCover f g // z.secondRoot ≠ 0}

/-- The complementary centered-root-zero locus. -/
def SecondRootZeroUnitTwoRootPowerCover (f g : K[X]) :=
  {z : UnitTwoRootPowerCover f g // z.secondRoot = 0}

instance goodUnitTwoRootPowerCoverFinite
    [Finite K] (f g : K[X]) :
    Finite (GoodUnitTwoRootPowerCover f g) :=
  Finite.of_injective Subtype.val Subtype.val_injective

instance secondRootZeroUnitTwoRootPowerCoverFinite
    [Finite K] (f g : K[X]) :
    Finite (SecondRootZeroUnitTwoRootPowerCover f g) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- Forget the fixed-parameter packaging in favor of two scalar root
subtypes. -/
def twoSquareRootFiberEquivRootProduct
    (f g : K[X]) (parameter : K) :
    TwoSquareRootFiber f g parameter ≃
      {r : K // r ^ 2 = f.eval parameter} ×
        {r : K // r ^ 2 = g.eval parameter} where
  toFun z :=
    (⟨z.firstRoot, z.firstEquation⟩,
      ⟨z.secondRoot, z.secondEquation⟩)
  invFun z :=
    { firstRoot := z.1.1
      secondRoot := z.2.1
      firstEquation := z.1.2
      secondEquation := z.2.2 }
  left_inv z := by ext <;> rfl
  right_inv z := by
    rcases z with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    rfl

/-- The affine cover is the sigma type of its fixed-parameter fibers. -/
def twoRootPowerCoverEquivSigma
    (f g : K[X]) :
    TwoRootPowerCover f g ≃
      Σ parameter : K, TwoSquareRootFiber f g parameter where
  toFun z :=
    ⟨z.parameter,
      { firstRoot := z.firstRoot
        secondRoot := z.secondRoot
        firstEquation := z.firstEquation
        secondEquation := z.secondEquation }⟩
  invFun z :=
    { parameter := z.1
      firstRoot := z.2.firstRoot
      secondRoot := z.2.secondRoot
      firstEquation := z.2.firstEquation
      secondEquation := z.2.secondEquation }
  left_inv z := by ext <;> rfl
  right_inv z := by
    rcases z with ⟨parameter, roots⟩
    cases roots
    rfl

/-- Split the affine parameter into its nonzero and zero cases. -/
def twoRootPowerCoverEquivUnitSumZero
    [DecidableEq K] (f g : K[X]) :
    TwoRootPowerCover f g ≃
      UnitTwoRootPowerCover f g ⊕
        TwoSquareRootFiber f g 0 where
  toFun z :=
    if hparameter : z.parameter = 0 then
      Sum.inr
        { firstRoot := z.firstRoot
          secondRoot := z.secondRoot
          firstEquation := by
            simpa only [hparameter] using z.firstEquation
          secondEquation := by
            simpa only [hparameter] using z.secondEquation }
    else
      Sum.inl
        { parameter := Units.mk0 z.parameter hparameter
          firstRoot := z.firstRoot
          secondRoot := z.secondRoot
          firstEquation := z.firstEquation
          secondEquation := z.secondEquation }
  invFun z :=
    match z with
    | Sum.inl z =>
        { parameter := (z.parameter : K)
          firstRoot := z.firstRoot
          secondRoot := z.secondRoot
          firstEquation := z.firstEquation
          secondEquation := z.secondEquation }
    | Sum.inr z =>
        { parameter := 0
          firstRoot := z.firstRoot
          secondRoot := z.secondRoot
          firstEquation := z.firstEquation
          secondEquation := z.secondEquation }
  left_inv z := by
    by_cases hparameter : z.parameter = 0
    · cases z
      simp_all
    · simp [hparameter]
  right_inv z := by
    rcases z with z | z <;> simp [Units.ne_zero]

/-- Split the unit cover according to whether the centered-norm root
vanishes. -/
def unitTwoRootPowerCoverEquivGoodSumSecondRootZero
    [DecidableEq K] (f g : K[X]) :
    UnitTwoRootPowerCover f g ≃
      GoodUnitTwoRootPowerCover f g ⊕
        SecondRootZeroUnitTwoRootPowerCover f g where
  toFun z :=
    if hsecond : z.secondRoot = 0 then
      Sum.inr ⟨z, hsecond⟩
    else
      Sum.inl ⟨z, hsecond⟩
  invFun z :=
    match z with
    | Sum.inl z => z.1
    | Sum.inr z => z.1
  left_inv z := by
    by_cases hsecond : z.secondRoot = 0 <;> simp [hsecond]
  right_inv z := by
    rcases z with ⟨z, hz⟩ | ⟨z, hz⟩
    · simp [hz]
    · simp [hz]

section FiniteField

variable [Fintype K] [DecidableEq K]

/-- A fixed two-root fiber realizes the product of the two scalar root
counts. -/
theorem natCard_twoSquareRootFiber_eq
    (f g : K[X]) (parameter : K) :
    (Nat.card (TwoSquareRootFiber f g parameter) : ℤ) =
      squareRootCount (f.eval parameter) *
        squareRootCount (g.eval parameter) := by
  rw [Nat.card_congr
    (twoSquareRootFiberEquivRootProduct f g parameter),
    Nat.card_prod]
  simp only [Nat.cast_mul]
  rw [natCard_squareRootFiber_eq_squareRootCount,
    natCard_squareRootFiber_eq_squareRootCount]

/-- The affine cover realizes the integer-valued two-root fiber-product
count. -/
theorem natCard_twoRootPowerCover_eq_pointCount
    (f g : K[X]) :
    (Nat.card (TwoRootPowerCover f g) : ℤ) =
      twoSquareRootFiberProductPointCount
        (fun parameter => f.eval parameter)
        (fun parameter => g.eval parameter) := by
  rw [Nat.card_congr (twoRootPowerCoverEquivSigma f g),
    Nat.card_sigma]
  simp only [Nat.cast_sum]
  simp_rw [natCard_twoSquareRootFiber_eq]
  rfl

/-- Removing the zero parameter is an exact cardinal subtraction. -/
theorem natCard_unitTwoRootPowerCover_eq_pointCount_sub_zeroFiber
    (f g : K[X]) :
    (Nat.card (UnitTwoRootPowerCover f g) : ℤ) =
      twoSquareRootFiberProductPointCount
          (fun parameter => f.eval parameter)
          (fun parameter => g.eval parameter) -
        Nat.card (TwoSquareRootFiber f g 0) := by
  have hsplit :
      Nat.card (TwoRootPowerCover f g) =
        Nat.card (UnitTwoRootPowerCover f g) +
          Nat.card (TwoSquareRootFiber f g 0) := by
    calc
      Nat.card (TwoRootPowerCover f g) =
          Nat.card
            (UnitTwoRootPowerCover f g ⊕
              TwoSquareRootFiber f g 0) :=
        Nat.card_congr (twoRootPowerCoverEquivUnitSumZero f g)
      _ = _ := Nat.card_sum
  have htotal := natCard_twoRootPowerCover_eq_pointCount f g
  have hsplitInt :
      (Nat.card (TwoRootPowerCover f g) : ℤ) =
        Nat.card (UnitTwoRootPowerCover f g) +
          Nat.card (TwoSquareRootFiber f g 0) := by
    exact_mod_cast hsplit
  linarith

/-- The good and second-root-zero loci partition the unit cover. -/
theorem natCard_good_add_secondRootZero_eq_unit
    (f g : K[X]) :
    Nat.card (GoodUnitTwoRootPowerCover f g) +
        Nat.card (SecondRootZeroUnitTwoRootPowerCover f g) =
      Nat.card (UnitTwoRootPowerCover f g) := by
  rw [← Nat.card_sum,
    ← Nat.card_congr
      (unitTwoRootPowerCoverEquivGoodSumSecondRootZero f g)]

/-- Removing the zero parameter and the vanishing centered root is an exact
cardinal subtraction. -/
theorem natCard_goodUnitTwoRootPowerCover_eq_pointCount_sub_bad
    (f g : K[X]) :
    (Nat.card (GoodUnitTwoRootPowerCover f g) : ℤ) =
      twoSquareRootFiberProductPointCount
          (fun parameter => f.eval parameter)
          (fun parameter => g.eval parameter) -
        Nat.card (TwoSquareRootFiber f g 0) -
        Nat.card (SecondRootZeroUnitTwoRootPowerCover f g) := by
  have hunit :=
    natCard_unitTwoRootPowerCover_eq_pointCount_sub_zeroFiber f g
  have hpartition := natCard_good_add_secondRootZero_eq_unit f g
  have hpartitionInt :
      (Nat.card (GoodUnitTwoRootPowerCover f g) : ℤ) +
          Nat.card (SecondRootZeroUnitTwoRootPowerCover f g) =
        Nat.card (UnitTwoRootPowerCover f g) := by
    exact_mod_cast hpartition
  linarith

end FiniteField

/-- Absolute irreducibility of the three hyperelliptic planes attached to
two radicands. -/
def TwoRootHyperellipticPlanesAbsolutelyIrreducible
    (f g : K[X]) : Prop :=
  let phi : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  Irreducible
      (MvPolynomial.map phi (hyperellipticPlanePolynomial f)) ∧
    Irreducible
      (MvPolynomial.map phi (hyperellipticPlanePolynomial g)) ∧
    Irreducible
      (MvPolynomial.map phi
        (hyperellipticPlanePolynomial (f * g)))

/-- The incidence and scaled centered-norm two-root planes, and their
product plane, are absolutely irreducible. -/
theorem
    connectingScaledTwoRootHyperellipticPlanes_absolutelyIrreducible
    (h2 : (2 : K) ≠ 0)
    {a : Coefficients K} {xi omegaInv : K}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hobstruction : incidenceCenteredNormObstruction a xi ≠ 0)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0)
    (homegaInv : omegaInv ≠ 0) :
    let f := incidencePulledRadicand a xi d
    let g :=
      C omegaInv *
        centeredNormPulledRadicand a.a3 a.a1 d
    TwoRootHyperellipticPlanesAbsolutelyIrreducible f g := by
  dsimp only
  let phi : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  have homegaInvMap : phi omegaInv ≠ 0 :=
    (map_ne_zero_iff phi phi.injective).2 homegaInv
  obtain ⟨hf, hg, hfg⟩ :=
    connectingTwoOriginalRadicandProducts_scalarMultiples_not_isSquare_algebraicClosure
      h2 hA1 hA2 hA3 hmoving hxi hobstruction hd hdegree
      (cf := 1) (cg := phi omegaInv) (cfg := phi omegaInv)
      one_ne_zero homegaInvMap homegaInvMap
  unfold TwoRootHyperellipticPlanesAbsolutelyIrreducible
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply
      hyperellipticPlanePolynomial_absolutelyIrreducible_of_not_isSquare_map
    apply not_isSquare_fractionRing_of_not_isSquare_ratFunc
    simpa [map_mul, map_C, mul_assoc, mul_left_comm, mul_comm] using hf
  · apply
      hyperellipticPlanePolynomial_absolutelyIrreducible_of_not_isSquare_map
    apply not_isSquare_fractionRing_of_not_isSquare_ratFunc
    simpa [map_mul, map_C, mul_assoc, mul_left_comm, mul_comm] using hg
  · apply
      hyperellipticPlanePolynomial_absolutelyIrreducible_of_not_isSquare_map
    apply not_isSquare_fractionRing_of_not_isSquare_ratFunc
    simpa [map_mul, map_C, mul_assoc, mul_left_comm, mul_comm] using hfg

section TwoRootFiniteFieldCount

variable [Fintype K] [DecidableEq K]

/-- The two-root identity turns the affine error into the sum of the three
signed hyperelliptic-cover errors. -/
theorem twoSquareRootFiberProductPointCount_error_le_sum_three
    (hchar : ringChar K ≠ 2) (f g : K[X]) :
    abs (((twoSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter) : ℤ) : ℝ) -
        (Fintype.card K : ℝ)) ≤
      |squareRootCoverPointCountError f| +
        |squareRootCoverPointCountError g| +
        |squareRootCoverPointCountError (f * g)| := by
  have hidentity :
      twoSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter) =
        squareRootCoverPointCount
            (fun parameter : K => f.eval parameter) +
          squareRootCoverPointCount
            (fun parameter : K => g.eval parameter) +
          squareRootCoverPointCount
            (fun parameter : K => (f * g).eval parameter) -
          2 * Fintype.card K := by
    simpa only [eval_mul] using
      twoSquareRootFiberProductPointCount_eq_three_covers
        hchar
        (fun parameter : K => f.eval parameter)
        (fun parameter : K => g.eval parameter)
  have htriangle :=
    calc
      |squareRootCoverPointCountError f +
          squareRootCoverPointCountError g +
          squareRootCoverPointCountError (f * g)| ≤
          |squareRootCoverPointCountError f +
            squareRootCoverPointCountError g| +
            |squareRootCoverPointCountError (f * g)| :=
        abs_add_le _ _
      _ ≤
          |squareRootCoverPointCountError f| +
            |squareRootCoverPointCountError g| +
            |squareRootCoverPointCountError (f * g)| := by
        gcongr
        exact abs_add_le _ _
  unfold squareRootCoverPointCountError at htriangle ⊢
  rw [hidentity]
  push_cast
  convert htriangle using 1
  all_goals (try ring_nf)
  all_goals rfl

/-- The affine unequal two-root count has error at most
`256 d sqrt(|K|)`. -/
theorem connectingScaledTwoRootPowerCover_card_error_le
    (hchar : ringChar K ≠ 2)
    {a : Coefficients K} {xi omegaInv : K}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hobstruction : incidenceCenteredNormObstruction a xi ≠ 0)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0)
    (homegaInv : omegaInv ≠ 0) :
    let f := incidencePulledRadicand a xi d
    let g :=
      C omegaInv *
        centeredNormPulledRadicand a.a3 a.a1 d
    |((Nat.card (TwoRootPowerCover f g) : ℤ) : ℝ) -
        (Fintype.card K : ℝ)| ≤
      256 * d * Real.sqrt (Fintype.card K : ℝ) := by
  dsimp only
  let f := incidencePulledRadicand a xi d
  let g :=
    C omegaInv *
      centeredNormPulledRadicand a.a3 a.a1 d
  have habsolute :
      TwoRootHyperellipticPlanesAbsolutelyIrreducible f g := by
    simpa [f, g] using
      (connectingScaledTwoRootHyperellipticPlanes_absolutelyIrreducible
        (Ring.two_ne_zero hchar) hA1 hA2 hA3 hmoving hxi hobstruction
        hd hdegree homegaInv)
  have hfDegree : f.natDegree ≤ 4 * d := by
    simpa [f] using incidencePulledRadicand_natDegree_le a xi d
  have hgDegree : g.natDegree ≤ 4 * d := by
    simpa [g] using
      scaledCenteredNormPulledRadicand_natDegree_le
        omegaInv a.a3 a.a1 d
  have hfgDegree : (f * g).natDegree ≤ 8 * d := by
    exact natDegree_mul_le.trans (by omega)
  unfold TwoRootHyperellipticPlanesAbsolutelyIrreducible at habsolute
  dsimp only at habsolute
  have hfError :=
    squareRootCoverPointCount_error_le_of_absolutelyIrreducible
      habsolute.1 (D := 4 * d) (by omega) hfDegree
  have hgError :=
    squareRootCoverPointCount_error_le_of_absolutelyIrreducible
      habsolute.2.1 (D := 4 * d) (by omega) hgDegree
  have hfgError :=
    squareRootCoverPointCount_error_le_of_absolutelyIrreducible
      habsolute.2.2 (D := 8 * d) (by omega) hfgDegree
  have hpoint :=
    twoSquareRootFiberProductPointCount_error_le_sum_three
      hchar f g
  have hcount := natCard_twoRootPowerCover_eq_pointCount f g
  have hcountReal :
      ((Nat.card (TwoRootPowerCover f g) : ℤ) : ℝ) =
        ((twoSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter) : ℤ) : ℝ) := by
    exact_mod_cast hcount
  rw [hcountReal]
  unfold SquareRootCoverPointCountErrorAtMost at hfError hgError hfgError
  have hsum :=
    add_le_add (add_le_add hfError hgError) hfgError
  apply hpoint.trans
  convert hsum using 1
  push_cast
  ring

/-- A scalar has at most two square roots in a field. -/
private theorem natCard_twoRootSquareRootFiber_le_two (b : K) :
    Nat.card {x : K // x ^ 2 = b} ≤ 2 := by
  let P : K[X] := X ^ 2 - C b
  have hP : P ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun q : K[X] => q.coeff 2) hzero
    simp [P] at hcoeff
  let rootEmbedding :
      {x : K // x ^ 2 = b} ↪ P.roots.toFinset :=
    { toFun := fun x => ⟨x, by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
        simpa [P, sub_eq_zero] using x.2⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg
          (fun z : P.roots.toFinset => (z : K)) h }
  calc
    Nat.card {x : K // x ^ 2 = b} ≤
        Nat.card ↥P.roots.toFinset :=
      Nat.card_le_card_of_injective
        rootEmbedding.toFun rootEmbedding.injective
    _ = P.roots.toFinset.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ = 2 := by simp [P]

/-- Every fixed affine parameter contributes at most four pairs of roots. -/
theorem natCard_twoSquareRootFiber_le_four
    (f g : K[X]) (parameter : K) :
    Nat.card (TwoSquareRootFiber f g parameter) ≤ 4 := by
  rw [Nat.card_congr
    (twoSquareRootFiberEquivRootProduct f g parameter),
    Nat.card_prod]
  exact
    (Nat.mul_le_mul
      (natCard_twoRootSquareRootFiber_le_two (f.eval parameter))
      (natCard_twoRootSquareRootFiber_le_two
        (g.eval parameter))).trans (by norm_num)

/-- A vanishing centered root embeds into a root of the centered radicand
and one incidence square-root choice. -/
private def secondRootZeroUnitTwoRootPowerCoverEmbedding
    (f g : K[X]) :
    SecondRootZeroUnitTwoRootPowerCover f g ↪
      Σ parameter : {t : K // g.eval t = 0},
        {r : K // r ^ 2 = f.eval parameter.1} where
  toFun z :=
    ⟨⟨(z.1.parameter : K), by
        simpa [z.2] using z.1.secondEquation.symm⟩,
      ⟨z.1.firstRoot, z.1.firstEquation⟩⟩
  inj' := by
    intro z w hzw
    apply Subtype.ext
    apply UnitTwoRootPowerCover.ext
    · apply Units.ext
      exact congrArg (fun q => (q.1.1 : K)) hzw
    · exact congrArg (fun q => (q.2.1 : K)) hzw
    · exact z.2.trans w.2.symm

/-- The centered-root-zero unit locus has at most twice the degree of the
centered radicand. -/
theorem
    natCard_secondRootZeroUnitTwoRootPowerCover_le_two_mul_natDegree
    (f g : K[X]) (hg : g ≠ 0) :
    Nat.card (SecondRootZeroUnitTwoRootPowerCover f g) ≤
      2 * g.natDegree := by
  let base := {t : K // g.eval t = 0}
  let fiber : base → Type u := fun t =>
    {r : K // r ^ 2 = f.eval t.1}
  have hinj :=
    Nat.card_le_card_of_injective
      (secondRootZeroUnitTwoRootPowerCoverEmbedding f g).toFun
      (secondRootZeroUnitTwoRootPowerCoverEmbedding f g).injective
  change
    Nat.card (SecondRootZeroUnitTwoRootPowerCover f g) ≤
      Nat.card (Σ t : base, fiber t) at hinj
  rw [Nat.card_sigma] at hinj
  have hfiber : ∀ t : base, Nat.card (fiber t) ≤ 2 := by
    intro t
    exact natCard_twoRootSquareRootFiber_le_two _
  have hsum :
      ∑ t : base, Nat.card (fiber t) ≤
        ∑ _t : base, 2 :=
    Finset.sum_le_sum fun t _ => hfiber t
  have hbase : Nat.card base ≤ g.natDegree := by
    classical
    let rootEmbedding : base ↪ g.roots.toFinset :=
      { toFun := fun x => ⟨x, by
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hg]
          exact x.2⟩
        inj' := by
          intro x y h
          apply Subtype.ext
          exact congrArg
            (fun z : g.roots.toFinset => (z : K)) h }
    calc
      Nat.card base ≤ Nat.card ↥g.roots.toFinset :=
        Nat.card_le_card_of_injective
          rootEmbedding.toFun rootEmbedding.injective
      _ = g.roots.toFinset.card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ ≤ g.roots.card := Multiset.toFinset_card_le _
      _ ≤ g.natDegree := Polynomial.card_roots' g
  have hsum' :
      ∑ t : base, Nat.card (fiber t) ≤ Nat.card base * 2 := by
    simpa using hsum
  omega

omit [Fintype K] [DecidableEq K] in
/-- A nonzero scalar multiple of the centered-norm pullback is nonzero. -/
theorem scaledCenteredNormPulledRadicand_ne_zero_twoRoot
    {omegaInv B C0 : K} (homegaInv : omegaInv ≠ 0)
    {d : ℕ} (hd : 0 < d) :
    C omegaInv * centeredNormPulledRadicand B C0 d ≠ 0 := by
  intro hzero
  have heval := congrArg (Polynomial.eval 0) hzero
  apply homegaInv
  simpa [eval_centeredNormPulledRadicand_zero B C0 hd] using heval

/-- For the scaled centered radicand the excluded zero-root locus has
cardinality at most `8d`. -/
theorem connectingScaledSecondRootZeroUnitTwoRootPowerCover_card_le
    (a : Coefficients K) (xi : K)
    {omegaInv : K} (homegaInv : omegaInv ≠ 0)
    {d : ℕ} (hd : 0 < d) :
    let f := incidencePulledRadicand a xi d
    let g :=
      C omegaInv * centeredNormPulledRadicand a.a3 a.a1 d
    Nat.card (SecondRootZeroUnitTwoRootPowerCover f g) ≤ 8 * d := by
  dsimp only
  have hbad :=
    natCard_secondRootZeroUnitTwoRootPowerCover_le_two_mul_natDegree
      (incidencePulledRadicand a xi d)
      (C omegaInv *
        centeredNormPulledRadicand a.a3 a.a1 d)
      (scaledCenteredNormPulledRadicand_ne_zero_twoRoot
        homegaInv hd)
  have hdegreeBound :=
    scaledCenteredNormPulledRadicand_natDegree_le
      omegaInv a.a3 a.a1 d
  omega

/-- Removing the zero parameter and zero centered root gives a good-unit
error `256 d sqrt(|K|) + 4 + 8d`. -/
theorem connectingScaledGoodUnitTwoRootPowerCover_card_error_le
    (hchar : ringChar K ≠ 2)
    {a : Coefficients K} {xi omegaInv : K}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hobstruction : incidenceCenteredNormObstruction a xi ≠ 0)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0)
    (homegaInv : omegaInv ≠ 0) :
    let f := incidencePulledRadicand a xi d
    let g :=
      C omegaInv * centeredNormPulledRadicand a.a3 a.a1 d
    |(Nat.card (GoodUnitTwoRootPowerCover f g) : ℝ) -
        (Fintype.card K : ℝ)| ≤
      256 * d * Real.sqrt (Fintype.card K : ℝ) +
        4 + 8 * d := by
  dsimp only
  let f := incidencePulledRadicand a xi d
  let g :=
    C omegaInv * centeredNormPulledRadicand a.a3 a.a1 d
  have htotal :
      |((Nat.card (TwoRootPowerCover f g) : ℤ) : ℝ) -
          (Fintype.card K : ℝ)| ≤
        256 * d * Real.sqrt (Fintype.card K : ℝ) := by
    simpa [f, g] using
      connectingScaledTwoRootPowerCover_card_error_le
        hchar hA1 hA2 hA3 hmoving hxi hobstruction
        hd hdegree homegaInv
  have hcastTotal :
      (((Nat.card (TwoRootPowerCover f g) : ℤ) : ℝ)) =
        (Nat.card (TwoRootPowerCover f g) : ℝ) := by
    norm_num
  rw [hcastTotal] at htotal
  have hzero :
      Nat.card (TwoSquareRootFiber f g 0) ≤ 4 :=
    natCard_twoSquareRootFiber_le_four f g 0
  have hbad :
      Nat.card (SecondRootZeroUnitTwoRootPowerCover f g) ≤
        8 * d := by
    simpa [f, g] using
      connectingScaledSecondRootZeroUnitTwoRootPowerCover_card_le
        a xi homegaInv hd
  have hcardIdentity :=
    natCard_goodUnitTwoRootPowerCover_eq_pointCount_sub_bad f g
  have htotalIdentity :=
    natCard_twoRootPowerCover_eq_pointCount f g
  have hgoodIdentity :
      (Nat.card (GoodUnitTwoRootPowerCover f g) : ℤ) =
        Nat.card (TwoRootPowerCover f g) -
          Nat.card (TwoSquareRootFiber f g 0) -
          Nat.card (SecondRootZeroUnitTwoRootPowerCover f g) := by
    rw [← htotalIdentity] at hcardIdentity
    exact hcardIdentity
  have hgoodIdentityReal :
      (Nat.card (GoodUnitTwoRootPowerCover f g) : ℝ) =
        (Nat.card (TwoRootPowerCover f g) : ℝ) -
          Nat.card (TwoSquareRootFiber f g 0) -
          Nat.card (SecondRootZeroUnitTwoRootPowerCover f g) := by
    exact_mod_cast hgoodIdentity
  rw [hgoodIdentityReal]
  have hzeroReal :
      (Nat.card (TwoSquareRootFiber f g 0) : ℝ) ≤ 4 := by
    exact_mod_cast hzero
  have hbadReal :
      (Nat.card (SecondRootZeroUnitTwoRootPowerCover f g) : ℝ) ≤
        8 * d := by
    exact_mod_cast hbad
  have hzeroNonneg :
      (0 : ℝ) ≤ Nat.card (TwoSquareRootFiber f g 0) := by
    positivity
  have hbadNonneg :
      (0 : ℝ) ≤
        Nat.card (SecondRootZeroUnitTwoRootPowerCover f g) := by
    positivity
  calc
    |(Nat.card (TwoRootPowerCover f g) : ℝ) -
          Nat.card (TwoSquareRootFiber f g 0) -
          Nat.card (SecondRootZeroUnitTwoRootPowerCover f g) -
        (Fintype.card K : ℝ)| ≤
        |(Nat.card (TwoRootPowerCover f g) : ℝ) -
          (Fintype.card K : ℝ)| +
          Nat.card (TwoSquareRootFiber f g 0) +
          Nat.card (SecondRootZeroUnitTwoRootPowerCover f g) := by
      have htriangle :=
        abs_add_le
          ((Nat.card (TwoRootPowerCover f g) : ℝ) -
            (Fintype.card K : ℝ))
          (-((Nat.card (TwoSquareRootFiber f g 0) : ℝ) +
            Nat.card
              (SecondRootZeroUnitTwoRootPowerCover f g)))
      rw [abs_neg,
        abs_of_nonneg (add_nonneg hzeroNonneg hbadNonneg)] at htriangle
      have hreorder :
          (Nat.card (TwoRootPowerCover f g) : ℝ) -
                Nat.card (TwoSquareRootFiber f g 0) -
                Nat.card
                  (SecondRootZeroUnitTwoRootPowerCover f g) -
              (Fintype.card K : ℝ) =
            ((Nat.card (TwoRootPowerCover f g) : ℝ) -
                (Fintype.card K : ℝ)) +
              -((Nat.card (TwoSquareRootFiber f g 0) : ℝ) +
                Nat.card
                  (SecondRootZeroUnitTwoRootPowerCover f g)) := by
        ring
      rw [hreorder]
      simpa only [add_assoc] using htriangle
    _ ≤
        256 * d * Real.sqrt (Fintype.card K : ℝ) +
          4 + 8 * d := by
      linarith

end TwoRootFiniteFieldCount

end

end GenMarkoff.General.Cage
