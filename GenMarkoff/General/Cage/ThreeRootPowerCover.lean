import GenMarkoff.General.Cage.ThreeSquareRootCount
import GenMarkoff.General.Cage.ConnectingPulledRadicands
import BGS.NumberTheory.OneSidedPrimitiveWitness

/-!
# Unit power covers for three simultaneous square roots

The seven-plane estimate counts three simultaneous square roots over every
affine parameter.  Primitive extraction instead uses a nonzero parameter in
the multiplicative group and then quotients by the fibers of a power map.
This file supplies the exact bridge.

The generic counting layer removes the zero parameter and, in the good
variant, removes precisely the locus where the third root vanishes.  The
specialized layer identifies the remaining unit cover for the unequal
connecting radicands with the witness-bearing one-sided power cover of
`BGS.NumberTheory.OneSidedPrimitiveWitness`.
-/

namespace GenMarkoff.General.Cage

open Polynomial

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- Three square roots above a fixed affine parameter. -/
structure ThreeSquareRootFiber
    (f g h : K[X]) (parameter : K) where
  firstRoot : K
  secondRoot : K
  thirdRoot : K
  firstEquation : firstRoot ^ 2 = f.eval parameter
  secondEquation : secondRoot ^ 2 = g.eval parameter
  thirdEquation : thirdRoot ^ 2 = h.eval parameter

@[ext]
theorem ThreeSquareRootFiber.ext
    {f g h : K[X]} {parameter : K}
    {x y : ThreeSquareRootFiber f g h parameter}
    (hfirst : x.firstRoot = y.firstRoot)
    (hsecond : x.secondRoot = y.secondRoot)
    (hthird : x.thirdRoot = y.thirdRoot) :
    x = y := by
  cases x
  cases y
  simp_all

instance threeSquareRootFiberFinite
    [Finite K] (f g h : K[X]) (parameter : K) :
    Finite (ThreeSquareRootFiber f g h parameter) :=
  Finite.of_injective
    (fun z => (z.firstRoot, z.secondRoot, z.thirdRoot))
    (by
      intro x y h
      exact ThreeSquareRootFiber.ext
        (congrArg (fun z => z.1) h)
        (congrArg (fun z => z.2.1) h)
        (congrArg (fun z => z.2.2) h))

/-- The affine three-root cover, including the zero parameter. -/
structure ThreeRootPowerCover (f g h : K[X]) where
  parameter : K
  firstRoot : K
  secondRoot : K
  thirdRoot : K
  firstEquation : firstRoot ^ 2 = f.eval parameter
  secondEquation : secondRoot ^ 2 = g.eval parameter
  thirdEquation : thirdRoot ^ 2 = h.eval parameter

@[ext]
theorem ThreeRootPowerCover.ext
    {f g h : K[X]} {x y : ThreeRootPowerCover f g h}
    (hparameter : x.parameter = y.parameter)
    (hfirst : x.firstRoot = y.firstRoot)
    (hsecond : x.secondRoot = y.secondRoot)
    (hthird : x.thirdRoot = y.thirdRoot) :
    x = y := by
  cases x
  cases y
  simp_all

instance threeRootPowerCoverFinite
    [Finite K] (f g h : K[X]) :
    Finite (ThreeRootPowerCover f g h) :=
  Finite.of_injective
    (fun z => (z.parameter, z.firstRoot, z.secondRoot, z.thirdRoot))
    (by
      intro x y h
      exact ThreeRootPowerCover.ext
        (congrArg (fun z => z.1) h)
        (congrArg (fun z => z.2.1) h)
        (congrArg (fun z => z.2.2.1) h)
        (congrArg (fun z => z.2.2.2) h))

/-- The same cover with its parameter restricted to the unit group. -/
structure UnitThreeRootPowerCover (f g h : K[X]) where
  parameter : Kˣ
  firstRoot : K
  secondRoot : K
  thirdRoot : K
  firstEquation : firstRoot ^ 2 = f.eval (parameter : K)
  secondEquation : secondRoot ^ 2 = g.eval (parameter : K)
  thirdEquation : thirdRoot ^ 2 = h.eval (parameter : K)

@[ext]
theorem UnitThreeRootPowerCover.ext
    {f g h : K[X]} {x y : UnitThreeRootPowerCover f g h}
    (hparameter : x.parameter = y.parameter)
    (hfirst : x.firstRoot = y.firstRoot)
    (hsecond : x.secondRoot = y.secondRoot)
    (hthird : x.thirdRoot = y.thirdRoot) :
    x = y := by
  cases x
  cases y
  simp_all

instance unitThreeRootPowerCoverFinite
    [Finite K] (f g h : K[X]) :
    Finite (UnitThreeRootPowerCover f g h) :=
  Finite.of_injective
    (fun z => (z.parameter, z.firstRoot, z.secondRoot, z.thirdRoot))
    (by
      intro x y h
      exact UnitThreeRootPowerCover.ext
        (congrArg (fun z => z.1) h)
        (congrArg (fun z => z.2.1) h)
        (congrArg (fun z => z.2.2.1) h)
        (congrArg (fun z => z.2.2.2) h))

/-- Unit-cover points whose third square root is nonzero. -/
def GoodUnitThreeRootPowerCover (f g h : K[X]) :=
  {z : UnitThreeRootPowerCover f g h // z.thirdRoot ≠ 0}

/-- The complementary third-root-zero locus. -/
def ThirdRootZeroUnitPowerCover (f g h : K[X]) :=
  {z : UnitThreeRootPowerCover f g h // z.thirdRoot = 0}

instance goodUnitThreeRootPowerCoverFinite
    [Finite K] (f g h : K[X]) :
    Finite (GoodUnitThreeRootPowerCover f g h) :=
  Finite.of_injective Subtype.val Subtype.val_injective

instance thirdRootZeroUnitPowerCoverFinite
    [Finite K] (f g h : K[X]) :
    Finite (ThirdRootZeroUnitPowerCover f g h) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- Forget the fixed-parameter packaging in favor of three root subtypes. -/
def threeSquareRootFiberEquivRootProduct
    (f g h : K[X]) (parameter : K) :
    ThreeSquareRootFiber f g h parameter ≃
      {r : K // r ^ 2 = f.eval parameter} ×
        {r : K // r ^ 2 = g.eval parameter} ×
          {r : K // r ^ 2 = h.eval parameter} where
  toFun z :=
    (⟨z.firstRoot, z.firstEquation⟩,
      ⟨z.secondRoot, z.secondEquation⟩,
      ⟨z.thirdRoot, z.thirdEquation⟩)
  invFun z :=
    { firstRoot := z.1.1
      secondRoot := z.2.1.1
      thirdRoot := z.2.2.1
      firstEquation := z.1.2
      secondEquation := z.2.1.2
      thirdEquation := z.2.2.2 }
  left_inv z := by ext <;> rfl
  right_inv z := by
    rcases z with ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩
    rfl

/-- The affine cover is the sigma type of its fixed-parameter fibers. -/
def threeRootPowerCoverEquivSigma
    (f g h : K[X]) :
    ThreeRootPowerCover f g h ≃
      Σ parameter : K, ThreeSquareRootFiber f g h parameter where
  toFun z :=
    ⟨z.parameter,
      { firstRoot := z.firstRoot
        secondRoot := z.secondRoot
        thirdRoot := z.thirdRoot
        firstEquation := z.firstEquation
        secondEquation := z.secondEquation
        thirdEquation := z.thirdEquation }⟩
  invFun z :=
    { parameter := z.1
      firstRoot := z.2.firstRoot
      secondRoot := z.2.secondRoot
      thirdRoot := z.2.thirdRoot
      firstEquation := z.2.firstEquation
      secondEquation := z.2.secondEquation
      thirdEquation := z.2.thirdEquation }
  left_inv z := by ext <;> rfl
  right_inv z := by
    rcases z with ⟨parameter, roots⟩
    cases roots
    rfl

/-- Splitting the affine parameter into its nonzero and zero cases. -/
def threeRootPowerCoverEquivUnitSumZero
    [DecidableEq K] (f g h : K[X]) :
    ThreeRootPowerCover f g h ≃
      UnitThreeRootPowerCover f g h ⊕
        ThreeSquareRootFiber f g h 0 where
  toFun z :=
    if hparameter : z.parameter = 0 then
      Sum.inr
        { firstRoot := z.firstRoot
          secondRoot := z.secondRoot
          thirdRoot := z.thirdRoot
          firstEquation := by
            simpa only [hparameter] using z.firstEquation
          secondEquation := by
            simpa only [hparameter] using z.secondEquation
          thirdEquation := by
            simpa only [hparameter] using z.thirdEquation }
    else
      Sum.inl
        { parameter := Units.mk0 z.parameter hparameter
          firstRoot := z.firstRoot
          secondRoot := z.secondRoot
          thirdRoot := z.thirdRoot
          firstEquation := z.firstEquation
          secondEquation := z.secondEquation
          thirdEquation := z.thirdEquation }
  invFun z :=
    match z with
    | Sum.inl z =>
        { parameter := (z.parameter : K)
          firstRoot := z.firstRoot
          secondRoot := z.secondRoot
          thirdRoot := z.thirdRoot
          firstEquation := z.firstEquation
          secondEquation := z.secondEquation
          thirdEquation := z.thirdEquation }
    | Sum.inr z =>
        { parameter := 0
          firstRoot := z.firstRoot
          secondRoot := z.secondRoot
          thirdRoot := z.thirdRoot
          firstEquation := z.firstEquation
          secondEquation := z.secondEquation
          thirdEquation := z.thirdEquation }
  left_inv z := by
    by_cases hparameter : z.parameter = 0
    · cases z
      simp_all
    · simp [hparameter]
  right_inv z := by
    rcases z with z | z <;> simp [Units.ne_zero]

/-- Splitting a unit cover according to whether the third root vanishes. -/
def unitThreeRootPowerCoverEquivGoodSumThirdRootZero
    [DecidableEq K] (f g h : K[X]) :
    UnitThreeRootPowerCover f g h ≃
      GoodUnitThreeRootPowerCover f g h ⊕
        ThirdRootZeroUnitPowerCover f g h where
  toFun z :=
    if hthird : z.thirdRoot = 0 then
      Sum.inr ⟨z, hthird⟩
    else
      Sum.inl ⟨z, hthird⟩
  invFun z :=
    match z with
    | Sum.inl z => z.1
    | Sum.inr z => z.1
  left_inv z := by
    by_cases hthird : z.thirdRoot = 0 <;> simp [hthird]
  right_inv z := by
    rcases z with ⟨z, hz⟩ | ⟨z, hz⟩
    · simp [hz]
    · simp [hz]

section FiniteField

variable [Fintype K] [DecidableEq K]

/-- A scalar square-root fiber has the cardinality used by
`squareRootCount`. -/
theorem natCard_squareRootFiber_eq_squareRootCount
    (a : K) :
    (Nat.card {r : K // r ^ 2 = a} : ℤ) = squareRootCount a := by
  change (Nat.card {r : K // r ^ 2 = a} : ℤ) =
    ((({r : K | r ^ 2 = a} : Set K).toFinset.card : ℕ) : ℤ)
  have hset :=
    Nat.card_eq_card_toFinset ({r : K | r ^ 2 = a} : Set K)
  let e :
      {r : K // r ^ 2 = a} ≃
        ↥({r : K | r ^ 2 = a} : Set K) :=
    Equiv.subtypeEquiv (Equiv.refl K) (by simp)
  have hcard :
      Nat.card {r : K // r ^ 2 = a} =
        ({r : K | r ^ 2 = a} : Set K).toFinset.card := by
    exact (Nat.card_congr e).trans hset
  exact_mod_cast hcard

/-- A fixed fiber has the product of the three scalar root counts. -/
theorem natCard_threeSquareRootFiber_eq
    (f g h : K[X]) (parameter : K) :
    (Nat.card (ThreeSquareRootFiber f g h parameter) : ℤ) =
      squareRootCount (f.eval parameter) *
        squareRootCount (g.eval parameter) *
          squareRootCount (h.eval parameter) := by
  rw [Nat.card_congr
    (threeSquareRootFiberEquivRootProduct f g h parameter),
    Nat.card_prod, Nat.card_prod]
  simp only [Nat.cast_mul]
  rw [natCard_squareRootFiber_eq_squareRootCount,
    natCard_squareRootFiber_eq_squareRootCount,
    natCard_squareRootFiber_eq_squareRootCount]
  ring

/-- The affine cover type realizes the integer-valued fiber-product count. -/
theorem natCard_threeRootPowerCover_eq_pointCount
    (f g h : K[X]) :
    (Nat.card (ThreeRootPowerCover f g h) : ℤ) =
      threeSquareRootFiberProductPointCount
        (fun parameter => f.eval parameter)
        (fun parameter => g.eval parameter)
        (fun parameter => h.eval parameter) := by
  rw [Nat.card_congr (threeRootPowerCoverEquivSigma f g h),
    Nat.card_sigma]
  simp only [Nat.cast_sum]
  simp_rw [natCard_threeSquareRootFiber_eq]
  rfl

/-- Removing the zero parameter is an exact cardinal subtraction. -/
theorem natCard_unitThreeRootPowerCover_eq_pointCount_sub_zeroFiber
    (f g h : K[X]) :
    (Nat.card (UnitThreeRootPowerCover f g h) : ℤ) =
      threeSquareRootFiberProductPointCount
          (fun parameter => f.eval parameter)
          (fun parameter => g.eval parameter)
          (fun parameter => h.eval parameter) -
        Nat.card (ThreeSquareRootFiber f g h 0) := by
  have hsplit :
      Nat.card (ThreeRootPowerCover f g h) =
        Nat.card (UnitThreeRootPowerCover f g h) +
          Nat.card (ThreeSquareRootFiber f g h 0) := by
    calc
      Nat.card (ThreeRootPowerCover f g h) =
          Nat.card
            (UnitThreeRootPowerCover f g h ⊕
              ThreeSquareRootFiber f g h 0) :=
        Nat.card_congr (threeRootPowerCoverEquivUnitSumZero f g h)
      _ = _ := Nat.card_sum
  have htotal := natCard_threeRootPowerCover_eq_pointCount f g h
  have hsplitInt :
      (Nat.card (ThreeRootPowerCover f g h) : ℤ) =
        Nat.card (UnitThreeRootPowerCover f g h) +
          Nat.card (ThreeSquareRootFiber f g h 0) := by
    exact_mod_cast hsplit
  linarith

/-- The good and third-root-zero loci partition the unit cover exactly. -/
theorem natCard_good_add_thirdRootZero_eq_unit
    (f g h : K[X]) :
    Nat.card (GoodUnitThreeRootPowerCover f g h) +
        Nat.card (ThirdRootZeroUnitPowerCover f g h) =
      Nat.card (UnitThreeRootPowerCover f g h) := by
  rw [← Nat.card_sum,
    ← Nat.card_congr
      (unitThreeRootPowerCoverEquivGoodSumThirdRootZero f g h)]

/-- Removing both the zero parameter and the third-root-zero locus is an
exact cardinal subtraction. -/
theorem natCard_goodUnitThreeRootPowerCover_eq_pointCount_sub_bad
    (f g h : K[X]) :
    (Nat.card (GoodUnitThreeRootPowerCover f g h) : ℤ) =
      threeSquareRootFiberProductPointCount
          (fun parameter => f.eval parameter)
          (fun parameter => g.eval parameter)
          (fun parameter => h.eval parameter) -
        Nat.card (ThreeSquareRootFiber f g h 0) -
        Nat.card (ThirdRootZeroUnitPowerCover f g h) := by
  have hunit :=
    natCard_unitThreeRootPowerCover_eq_pointCount_sub_zeroFiber f g h
  have hpartition := natCard_good_add_thirdRootZero_eq_unit f g h
  have hpartitionInt :
      (Nat.card (GoodUnitThreeRootPowerCover f g h) : ℤ) +
          Nat.card (ThirdRootZeroUnitPowerCover f g h) =
        Nat.card (UnitThreeRootPowerCover f g h) := by
    exact_mod_cast hpartition
  linarith

end FiniteField

section ConnectingPowerCover

/-- Clearing the reciprocal-trace denominator in one unequal incidence
equation gives its pulled radicand. -/
theorem scaled_incidenceDiscriminant_iff_pulledRadicand
    (a : Coefficients K) (xi u root : K) (hu : u ≠ 0) (d : ℕ) :
    root ^ 2 =
        incidenceDiscriminant a xi (u ^ d + (u ^ d)⁻¹) ↔
      (u ^ d * root) ^ 2 =
        eval u (incidencePulledRadicand a xi d) := by
  have hud : u ^ d ≠ 0 := pow_ne_zero d hu
  rw [eval_incidencePulledRadicand,
    incidenceReciprocalQuartic_eq_mul_discriminant a xi (u ^ d) hud]
  constructor
  · intro h
    calc
      (u ^ d * root) ^ 2 = (u ^ d) ^ 2 * root ^ 2 := by ring
      _ = (u ^ d) ^ 2 *
          incidenceDiscriminant a xi (u ^ d + (u ^ d)⁻¹) := by
        rw [h]
  · intro h
    apply (mul_left_cancel₀ (pow_ne_zero 2 hud))
    calc
      (u ^ d) ^ 2 * root ^ 2 =
          (u ^ d * root) ^ 2 := by ring
      _ = (u ^ d) ^ 2 *
          incidenceDiscriminant a xi (u ^ d + (u ^ d)⁻¹) := h

/-- The same denominator clearing for the scaled centered-norm radicand. -/
theorem scaled_centeredNorm_iff_pulledRadicand
    (B C0 omegaInv u root : K) (hu : u ≠ 0) (d : ℕ) :
    root ^ 2 =
        omegaInv * centeredNorm B C0 (u ^ d + (u ^ d)⁻¹) ↔
      (u ^ d * root) ^ 2 =
        eval u
          (C omegaInv * centeredNormPulledRadicand B C0 d) := by
  have hud : u ^ d ≠ 0 := pow_ne_zero d hu
  rw [eval_mul, eval_C, eval_centeredNormPulledRadicand,
    centeredNormReciprocalQuartic_eq_mul_centeredNorm B C0 (u ^ d) hud]
  constructor
  · intro h
    calc
      (u ^ d * root) ^ 2 = (u ^ d) ^ 2 * root ^ 2 := by ring
      _ = omegaInv * ((u ^ d) ^ 2 *
          centeredNorm B C0 (u ^ d + (u ^ d)⁻¹)) := by
        rw [h]
        ring
  · intro h
    apply (mul_left_cancel₀ (pow_ne_zero 2 hud))
    calc
      (u ^ d) ^ 2 * root ^ 2 =
          (u ^ d * root) ^ 2 := by ring
      _ = omegaInv * ((u ^ d) ^ 2 *
          centeredNorm B C0 (u ^ d + (u ^ d)⁻¹)) := h
      _ = (u ^ d) ^ 2 *
          (omegaInv * centeredNorm B C0
            (u ^ d + (u ^ d)⁻¹)) := by ring

/-- Three simultaneous square-root witnesses over one middle trace.  The
third equation records the scaled centered norm needed by the connecting
construction. -/
structure ConnectingThreeRootWitness
    (a : Coefficients K) (xi eta omegaInv : K) where
  middle : K
  firstRoot : K
  secondRoot : K
  thirdRoot : K
  firstEquation :
    firstRoot ^ 2 = incidenceDiscriminant a xi middle
  secondEquation :
    secondRoot ^ 2 = incidenceDiscriminant a eta middle
  thirdEquation :
    thirdRoot ^ 2 = omegaInv * centeredNorm a.a3 a.a1 middle

@[ext]
theorem ConnectingThreeRootWitness.ext
    {a : Coefficients K} {xi eta omegaInv : K}
    {x y : ConnectingThreeRootWitness a xi eta omegaInv}
    (hmiddle : x.middle = y.middle)
    (hfirst : x.firstRoot = y.firstRoot)
    (hsecond : x.secondRoot = y.secondRoot)
    (hthird : x.thirdRoot = y.thirdRoot) :
    x = y := by
  cases x
  cases y
  simp_all

instance connectingThreeRootWitnessFinite
    [Finite K] (a : Coefficients K) (xi eta omegaInv : K) :
    Finite (ConnectingThreeRootWitness a xi eta omegaInv) :=
  Finite.of_injective
    (fun z => (z.middle, z.firstRoot, z.secondRoot, z.thirdRoot))
    (by
      intro x y h
      exact ConnectingThreeRootWitness.ext
        (congrArg (fun z => z.1) h)
        (congrArg (fun z => z.2.1) h)
        (congrArg (fun z => z.2.2.1) h)
        (congrArg (fun z => z.2.2.2) h))

/-- The unit three-root cover for the two incidence radicands and the scaled
centered-norm radicand. -/
abbrev ConnectingUnitThreeRootPowerCover
    (a : Coefficients K) (xi eta omegaInv : K) (d : ℕ) :=
  UnitThreeRootPowerCover
    (incidencePulledRadicand a xi d)
    (incidencePulledRadicand a eta d)
    (C omegaInv * centeredNormPulledRadicand a.a3 a.a1 d)

/-- The witness-bearing one-sided power cover whose left trace is the common
middle trace of the three square-root equations. -/
abbrev connectingThreeRootPowerCoverSolutions
    (a : Coefficients K) (xi eta omegaInv : K) (d : ℕ) :=
  BGS.rightPowerTraceCoverSolutions
    (fun w : ConnectingThreeRootWitness a xi eta omegaInv => w.middle)
    (BGS.Markoff.splitTorusTrace : Kˣ → K) d

/-- The corresponding power-range quotient. -/
abbrev connectingThreeRootPowerRangeSolutions
    (a : Coefficients K) (xi eta omegaInv : K) (d : ℕ) :=
  BGS.rightPowerTraceRangeSolutions
    (fun w : ConnectingThreeRootWitness a xi eta omegaInv => w.middle)
    (BGS.Markoff.splitTorusTrace : Kˣ → K) d

/-- Scale all three witness roots by the common reciprocal-trace
denominator. -/
def connectingThreeRootPowerCoverToPulled
    (a : Coefficients K) (xi eta omegaInv : K) (d : ℕ) :
    connectingThreeRootPowerCoverSolutions a xi eta omegaInv d →
      ConnectingUnitThreeRootPowerCover a xi eta omegaInv d := fun z => by
  let witness := z.1.1
  let parameter := z.1.2
  have hmiddle :
      witness.middle =
        BGS.Markoff.splitTorusTrace (parameter ^ d) := z.2
  refine
    { parameter := parameter
      firstRoot := (parameter : K) ^ d * witness.firstRoot
      secondRoot := (parameter : K) ^ d * witness.secondRoot
      thirdRoot := (parameter : K) ^ d * witness.thirdRoot
      firstEquation := ?_
      secondEquation := ?_
      thirdEquation := ?_ }
  · apply
      (scaled_incidenceDiscriminant_iff_pulledRadicand
        a xi (parameter : K) witness.firstRoot
          parameter.ne_zero d).mp
    have htrace :
        (parameter : K) ^ d + ((parameter : K) ^ d)⁻¹ =
          BGS.Markoff.splitTorusTrace (parameter ^ d) := by
      simp [BGS.Markoff.splitTorusTrace]
    rw [htrace, ← hmiddle]
    exact witness.firstEquation
  · apply
      (scaled_incidenceDiscriminant_iff_pulledRadicand
        a eta (parameter : K) witness.secondRoot
          parameter.ne_zero d).mp
    have htrace :
        (parameter : K) ^ d + ((parameter : K) ^ d)⁻¹ =
          BGS.Markoff.splitTorusTrace (parameter ^ d) := by
      simp [BGS.Markoff.splitTorusTrace]
    rw [htrace, ← hmiddle]
    exact witness.secondEquation
  · apply
      (scaled_centeredNorm_iff_pulledRadicand
        a.a3 a.a1 omegaInv (parameter : K) witness.thirdRoot
          parameter.ne_zero d).mp
    have htrace :
        (parameter : K) ^ d + ((parameter : K) ^ d)⁻¹ =
          BGS.Markoff.splitTorusTrace (parameter ^ d) := by
      simp [BGS.Markoff.splitTorusTrace]
    rw [htrace, ← hmiddle]
    exact witness.thirdEquation

/-- Divide all three pulled roots by the common nonzero denominator. -/
def connectingPulledToThreeRootPowerCover
    (a : Coefficients K) (xi eta omegaInv : K) (d : ℕ) :
    ConnectingUnitThreeRootPowerCover a xi eta omegaInv d →
      connectingThreeRootPowerCoverSolutions a xi eta omegaInv d := fun z => by
  let q : K := (z.parameter : K) ^ d
  have hq : q ≠ 0 := pow_ne_zero d z.parameter.ne_zero
  let witness : ConnectingThreeRootWitness a xi eta omegaInv :=
    { middle := BGS.Markoff.splitTorusTrace (z.parameter ^ d)
      firstRoot := q⁻¹ * z.firstRoot
      secondRoot := q⁻¹ * z.secondRoot
      thirdRoot := q⁻¹ * z.thirdRoot
      firstEquation := by
        have h :=
          (scaled_incidenceDiscriminant_iff_pulledRadicand
            a xi (z.parameter : K) (q⁻¹ * z.firstRoot)
              z.parameter.ne_zero d).mpr (by
            simpa [q, hq] using z.firstEquation)
        simpa [q, BGS.Markoff.splitTorusTrace] using h
      secondEquation := by
        have h :=
          (scaled_incidenceDiscriminant_iff_pulledRadicand
            a eta (z.parameter : K) (q⁻¹ * z.secondRoot)
              z.parameter.ne_zero d).mpr (by
            simpa [q, hq] using z.secondEquation)
        simpa [q, BGS.Markoff.splitTorusTrace] using h
      thirdEquation := by
        have h :=
          (scaled_centeredNorm_iff_pulledRadicand
            a.a3 a.a1 omegaInv (z.parameter : K)
              (q⁻¹ * z.thirdRoot) z.parameter.ne_zero d).mpr (by
            simpa [q, hq] using z.thirdEquation)
        simpa [q, BGS.Markoff.splitTorusTrace] using h }
  refine ⟨(witness, z.parameter), ?_⟩
  rfl

/-- The witness-bearing one-sided cover is exactly the three pulled-radicand
equations over a unit parameter. -/
def connectingThreeRootPowerCoverEquivPulled
    (a : Coefficients K) (xi eta omegaInv : K) (d : ℕ) :
    connectingThreeRootPowerCoverSolutions a xi eta omegaInv d ≃
      ConnectingUnitThreeRootPowerCover a xi eta omegaInv d where
  toFun := connectingThreeRootPowerCoverToPulled a xi eta omegaInv d
  invFun := connectingPulledToThreeRootPowerCover a xi eta omegaInv d
  left_inv := by
    intro z
    apply Subtype.ext
    apply Prod.ext
    · apply ConnectingThreeRootWitness.ext
      · simpa [connectingThreeRootPowerCoverToPulled,
          connectingPulledToThreeRootPowerCover] using z.2.symm
      · simp [connectingThreeRootPowerCoverToPulled,
          connectingPulledToThreeRootPowerCover]
      · simp [connectingThreeRootPowerCoverToPulled,
          connectingPulledToThreeRootPowerCover]
      · simp [connectingThreeRootPowerCoverToPulled,
          connectingPulledToThreeRootPowerCover]
    · rfl
  right_inv := by
    intro z
    apply UnitThreeRootPowerCover.ext
    · rfl
    · simp [connectingThreeRootPowerCoverToPulled,
        connectingPulledToThreeRootPowerCover]
    · simp [connectingThreeRootPowerCoverToPulled,
        connectingPulledToThreeRootPowerCover]
    · simp [connectingThreeRootPowerCoverToPulled,
        connectingPulledToThreeRootPowerCover]

/-- Exact `d`-fold multiplicity of the connecting pulled cover over the
power-map range. -/
theorem natCard_connectingUnitThreeRootPowerCover_eq_mul_powerRange
    [Finite K] [IsCyclic Kˣ]
    (a : Coefficients K) (xi eta omegaInv : K) (d : ℕ)
    (hd : d ∣ Nat.card Kˣ) :
    Nat.card (ConnectingUnitThreeRootPowerCover
        a xi eta omegaInv d) =
      d * Nat.card
        (connectingThreeRootPowerRangeSolutions
          a xi eta omegaInv d) := by
  calc
    Nat.card (ConnectingUnitThreeRootPowerCover
        a xi eta omegaInv d) =
        Nat.card
          (connectingThreeRootPowerCoverSolutions
            a xi eta omegaInv d) :=
      Nat.card_congr
        (connectingThreeRootPowerCoverEquivPulled
          a xi eta omegaInv d).symm
    _ = d * Nat.card
        (connectingThreeRootPowerRangeSolutions
          a xi eta omegaInv d) := by
      simpa [connectingThreeRootPowerCoverSolutions,
        connectingThreeRootPowerRangeSolutions] using
          (BGS.natCard_rightPowerTraceCoverSolutions_of_dvd
            (fun w : ConnectingThreeRootWitness
              a xi eta omegaInv => w.middle)
            (BGS.Markoff.splitTorusTrace : Kˣ → K) d hd)

end ConnectingPowerCover

end

end GenMarkoff.General.Cage
