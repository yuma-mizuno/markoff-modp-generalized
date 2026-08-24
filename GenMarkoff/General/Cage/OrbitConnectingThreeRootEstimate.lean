import GenMarkoff.General.Cage.ConnectingThreeRootEstimate
import GenMarkoff.General.Cage.OrbitConnectingPulledRadicands

/-!
# Three-root cover estimate for orbit-component connecting data

The orbit-coset postprocessing uses the two coset-corrected component
pullbacks

`X^d * orbitComponentPlusPulledRadicand alpha gamma k d`,
`X^d * orbitComponentMinusPulledRadicand alpha gamma k d`,

together with a nonzero scalar multiple of the centered-norm pullback.
This file packages the counting consequences of geometric irreducibility of
the seven associated hyperelliptic planes.

The two orbit-component radicands have degree at most `3d`, while the
centered-norm radicand has degree at most `4d`.  Using `4d` as a common
degree bound gives affine error `768 d sqrt(|K|)`.  Removing the zero
parameter costs at most `8`, and removing the third-root-zero locus costs at
most `16d`.

Geometric irreducibility is deliberately an explicit hypothesis here.  It is
the square-class input supplied by the separate orbit-connecting geometry
layer.
-/

namespace GenMarkoff.General.Cage

open Polynomial
open scoped ArithmeticFunction.Moebius BigOperators

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- The denominator-cleared positive component pullback with the extra
`X^d` factor that turns the unit evaluation factor into a square. -/
def orbitComponentPlusCosetPulledRadicand
    (alpha gamma k : K) (d : ℕ) : K[X] :=
  X ^ d * orbitComponentPlusPulledRadicand alpha gamma k d

/-- The denominator-cleared negative component pullback with the extra
`X^d` factor that turns the unit evaluation factor into a square. -/
def orbitComponentMinusCosetPulledRadicand
    (alpha gamma k : K) (d : ℕ) : K[X] :=
  X ^ d * orbitComponentMinusPulledRadicand alpha gamma k d

/-- Exact evaluation of the coset-corrected positive component pullback. -/
@[simp]
theorem eval_orbitComponentPlusCosetPulledRadicand_unit
    (alpha gamma k : K) (t : Kˣ) (d : ℕ) :
    eval (t : K)
        (orbitComponentPlusCosetPulledRadicand alpha gamma k d) =
      ((t : K) ^ d) ^ 2 *
        orbitComponentRadicand alpha k
          (BGS.Markoff.splitTorusTrace (t ^ d) - gamma) := by
  rw [orbitComponentPlusCosetPulledRadicand, eval_mul, eval_pow, eval_X,
    eval_orbitComponentPlusPulledRadicand_unit]
  ring

/-- Exact evaluation of the coset-corrected negative component pullback. -/
@[simp]
theorem eval_orbitComponentMinusCosetPulledRadicand_unit
    (alpha gamma k : K) (t : Kˣ) (d : ℕ) :
    eval (t : K)
        (orbitComponentMinusCosetPulledRadicand alpha gamma k d) =
      ((t : K) ^ d) ^ 2 *
        orbitOppositeComponentRadicand alpha k
          (BGS.Markoff.splitTorusTrace (t ^ d) - gamma) := by
  rw [orbitComponentMinusCosetPulledRadicand, eval_mul, eval_pow, eval_X,
    eval_orbitComponentMinusPulledRadicand_unit]
  ring

/-- The coset-corrected positive component pullback has degree at most
`3d`. -/
theorem orbitComponentPlusCosetPulledRadicand_natDegree_le
    (alpha gamma k : K) (d : ℕ) :
    (orbitComponentPlusCosetPulledRadicand alpha gamma k d).natDegree ≤
      3 * d := by
  unfold orbitComponentPlusCosetPulledRadicand
  exact natDegree_mul_le.trans (by
    have hcomponent :=
      orbitComponentPlusPulledRadicand_natDegree_le
        alpha gamma k d
    have hpower := natDegree_X_pow_le (R := K) d
    omega)

/-- The coset-corrected negative component pullback has degree at most
`3d`. -/
theorem orbitComponentMinusCosetPulledRadicand_natDegree_le
    (alpha gamma k : K) (d : ℕ) :
    (orbitComponentMinusCosetPulledRadicand alpha gamma k d).natDegree ≤
      3 * d := by
  unfold orbitComponentMinusCosetPulledRadicand
  exact natDegree_mul_le.trans (by
    have hcomponent :=
      orbitComponentMinusPulledRadicand_natDegree_le
        alpha gamma k d
    have hpower := natDegree_X_pow_le (R := K) d
    omega)

/-- Scaling a positive-component square root by `t^d` is equivalent to the
coset-corrected pulled equation. -/
theorem scaled_orbitComponentPlus_iff_cosetPulledRadicand
    (alpha gamma k root : K) (t : Kˣ) (d : ℕ) :
    root ^ 2 =
        orbitComponentRadicand alpha k
          (BGS.Markoff.splitTorusTrace (t ^ d) - gamma) ↔
      ((t : K) ^ d * root) ^ 2 =
        eval (t : K)
          (orbitComponentPlusCosetPulledRadicand
            alpha gamma k d) := by
  rw [eval_orbitComponentPlusCosetPulledRadicand_unit]
  constructor
  · intro h
    calc
      ((t : K) ^ d * root) ^ 2 =
          ((t : K) ^ d) ^ 2 * root ^ 2 := by ring
      _ = ((t : K) ^ d) ^ 2 *
          orbitComponentRadicand alpha k
            (BGS.Markoff.splitTorusTrace (t ^ d) - gamma) := by
        rw [h]
  · intro h
    apply
      (mul_left_cancel₀
        (pow_ne_zero 2 (pow_ne_zero d t.ne_zero)))
    calc
      ((t : K) ^ d) ^ 2 * root ^ 2 =
          ((t : K) ^ d * root) ^ 2 := by ring
      _ = ((t : K) ^ d) ^ 2 *
          orbitComponentRadicand alpha k
            (BGS.Markoff.splitTorusTrace (t ^ d) - gamma) := h

/-- Scaling a negative-component square root by `t^d` is equivalent to the
coset-corrected pulled equation. -/
theorem scaled_orbitComponentMinus_iff_cosetPulledRadicand
    (alpha gamma k root : K) (t : Kˣ) (d : ℕ) :
    root ^ 2 =
        orbitOppositeComponentRadicand alpha k
          (BGS.Markoff.splitTorusTrace (t ^ d) - gamma) ↔
      ((t : K) ^ d * root) ^ 2 =
        eval (t : K)
          (orbitComponentMinusCosetPulledRadicand
            alpha gamma k d) := by
  rw [eval_orbitComponentMinusCosetPulledRadicand_unit]
  constructor
  · intro h
    calc
      ((t : K) ^ d * root) ^ 2 =
          ((t : K) ^ d) ^ 2 * root ^ 2 := by ring
      _ = ((t : K) ^ d) ^ 2 *
          orbitOppositeComponentRadicand alpha k
            (BGS.Markoff.splitTorusTrace (t ^ d) - gamma) := by
        rw [h]
  · intro h
    apply
      (mul_left_cancel₀
        (pow_ne_zero 2 (pow_ne_zero d t.ne_zero)))
    calc
      ((t : K) ^ d) ^ 2 * root ^ 2 =
          ((t : K) ^ d * root) ^ 2 := by ring
      _ = ((t : K) ^ d) ^ 2 *
          orbitOppositeComponentRadicand alpha k
            (BGS.Markoff.splitTorusTrace (t ^ d) - gamma) := h

/-- Three square-root witnesses over a middle trace that retain both
orbit-component square classes and the connecting centered-norm class. -/
structure OrbitConnectingThreeRootWitness
    (alpha gamma k omegaInv B C0 : K) where
  middle : K
  plusRoot : K
  minusRoot : K
  thirdRoot : K
  plusEquation :
    plusRoot ^ 2 =
      orbitComponentRadicand alpha k (middle - gamma)
  minusEquation :
    minusRoot ^ 2 =
      orbitOppositeComponentRadicand alpha k (middle - gamma)
  thirdEquation :
    thirdRoot ^ 2 = omegaInv * centeredNorm B C0 middle

@[ext]
theorem OrbitConnectingThreeRootWitness.ext
    {alpha gamma k omegaInv B C0 : K}
    {x y :
      OrbitConnectingThreeRootWitness
        alpha gamma k omegaInv B C0}
    (hmiddle : x.middle = y.middle)
    (hplus : x.plusRoot = y.plusRoot)
    (hminus : x.minusRoot = y.minusRoot)
    (hthird : x.thirdRoot = y.thirdRoot) :
    x = y := by
  cases x
  cases y
  simp_all

instance orbitConnectingThreeRootWitnessFinite
    [Finite K] (alpha gamma k omegaInv B C0 : K) :
    Finite
      (OrbitConnectingThreeRootWitness
        alpha gamma k omegaInv B C0) :=
  Finite.of_injective
    (fun z => (z.middle, z.plusRoot, z.minusRoot, z.thirdRoot))
    (by
      intro x y h
      exact OrbitConnectingThreeRootWitness.ext
        (congrArg (fun z => z.1) h)
        (congrArg (fun z => z.2.1) h)
        (congrArg (fun z => z.2.2.1) h)
        (congrArg (fun z => z.2.2.2) h))

/-- Orbit-connecting witnesses with nonzero centered-norm square root. -/
def OrbitConnectingGoodThreeRootWitness
    (alpha gamma k omegaInv B C0 : K) :=
  {w :
      OrbitConnectingThreeRootWitness
        alpha gamma k omegaInv B C0 //
    w.thirdRoot ≠ 0}

instance orbitConnectingGoodThreeRootWitnessFinite
    [Finite K] (alpha gamma k omegaInv B C0 : K) :
    Finite
      (OrbitConnectingGoodThreeRootWitness
        alpha gamma k omegaInv B C0) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- The witness-bearing one-sided orbit-connecting power cover. -/
abbrev orbitConnectingThreeRootPowerCoverSolutions
    (alpha gamma k omegaInv B C0 : K) (d : ℕ) :=
  BGS.rightPowerTraceCoverSolutions
    (fun w :
      OrbitConnectingThreeRootWitness
        alpha gamma k omegaInv B C0 => w.middle)
    (BGS.Markoff.splitTorusTrace : Kˣ → K) d

/-- The corresponding one-sided power-range quotient. -/
abbrev orbitConnectingThreeRootPowerRangeSolutions
    (alpha gamma k omegaInv B C0 : K) (d : ℕ) :=
  BGS.rightPowerTraceRangeSolutions
    (fun w :
      OrbitConnectingThreeRootWitness
        alpha gamma k omegaInv B C0 => w.middle)
    (BGS.Markoff.splitTorusTrace : Kˣ → K) d

/-- The one-sided power cover formed from good orbit-connecting witnesses. -/
abbrev orbitConnectingGoodThreeRootPowerCoverSolutions
    (alpha gamma k omegaInv B C0 : K) (d : ℕ) :=
  BGS.rightPowerTraceCoverSolutions
    (fun w :
      OrbitConnectingGoodThreeRootWitness
        alpha gamma k omegaInv B C0 => w.1.middle)
    (BGS.Markoff.splitTorusTrace : Kˣ → K) d

/-- The good-witness power-range quotient. -/
abbrev orbitConnectingGoodThreeRootPowerRangeSolutions
    (alpha gamma k omegaInv B C0 : K) (d : ℕ) :=
  BGS.rightPowerTraceRangeSolutions
    (fun w :
      OrbitConnectingGoodThreeRootWitness
        alpha gamma k omegaInv B C0 => w.1.middle)
    (BGS.Markoff.splitTorusTrace : Kˣ → K) d

/-- Scale all three orbit-connecting witness roots by the common unit power. -/
def orbitConnectingThreeRootPowerCoverToPulled
    (alpha gamma k omegaInv B C0 : K) (d : ℕ) :
    orbitConnectingThreeRootPowerCoverSolutions
        alpha gamma k omegaInv B C0 d →
      UnitThreeRootPowerCover
        (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
        (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
        (C omegaInv * centeredNormPulledRadicand B C0 d) := fun z => by
  let witness := z.1.1
  let parameter := z.1.2
  have hmiddle :
      witness.middle =
        BGS.Markoff.splitTorusTrace (parameter ^ d) := z.2
  refine
    { parameter := parameter
      firstRoot := (parameter : K) ^ d * witness.plusRoot
      secondRoot := (parameter : K) ^ d * witness.minusRoot
      thirdRoot := (parameter : K) ^ d * witness.thirdRoot
      firstEquation := ?_
      secondEquation := ?_
      thirdEquation := ?_ }
  · apply
      (scaled_orbitComponentPlus_iff_cosetPulledRadicand
        alpha gamma k witness.plusRoot parameter d).mp
    rw [← hmiddle]
    exact witness.plusEquation
  · apply
      (scaled_orbitComponentMinus_iff_cosetPulledRadicand
        alpha gamma k witness.minusRoot parameter d).mp
    rw [← hmiddle]
    exact witness.minusEquation
  · apply
      (scaled_centeredNorm_iff_pulledRadicand
        B C0 omegaInv (parameter : K) witness.thirdRoot
          parameter.ne_zero d).mp
    have htrace :
        (parameter : K) ^ d + ((parameter : K) ^ d)⁻¹ =
          BGS.Markoff.splitTorusTrace (parameter ^ d) := by
      simp [BGS.Markoff.splitTorusTrace]
    rw [htrace, ← hmiddle]
    exact witness.thirdEquation

/-- Divide a pulled orbit-connecting cover point by its common nonzero unit
power. -/
def orbitConnectingPulledToThreeRootPowerCover
    (alpha gamma k omegaInv B C0 : K) (d : ℕ) :
    UnitThreeRootPowerCover
        (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
        (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
        (C omegaInv * centeredNormPulledRadicand B C0 d) →
      orbitConnectingThreeRootPowerCoverSolutions
        alpha gamma k omegaInv B C0 d := fun z => by
  let q : K := (z.parameter : K) ^ d
  have hq : q ≠ 0 := pow_ne_zero d z.parameter.ne_zero
  let witness :
      OrbitConnectingThreeRootWitness
        alpha gamma k omegaInv B C0 :=
    { middle := BGS.Markoff.splitTorusTrace (z.parameter ^ d)
      plusRoot := q⁻¹ * z.firstRoot
      minusRoot := q⁻¹ * z.secondRoot
      thirdRoot := q⁻¹ * z.thirdRoot
      plusEquation := by
        have h :=
          (scaled_orbitComponentPlus_iff_cosetPulledRadicand
            alpha gamma k (q⁻¹ * z.firstRoot)
              z.parameter d).mpr (by
            simpa [q, hq] using z.firstEquation)
        simpa [q] using h
      minusEquation := by
        have h :=
          (scaled_orbitComponentMinus_iff_cosetPulledRadicand
            alpha gamma k (q⁻¹ * z.secondRoot)
              z.parameter d).mpr (by
            simpa [q, hq] using z.secondEquation)
        simpa [q] using h
      thirdEquation := by
        have h :=
          (scaled_centeredNorm_iff_pulledRadicand
            B C0 omegaInv (z.parameter : K)
              (q⁻¹ * z.thirdRoot) z.parameter.ne_zero d).mpr (by
            simpa [q, hq] using z.thirdEquation)
        simpa [q, BGS.Markoff.splitTorusTrace] using h }
  refine ⟨(witness, z.parameter), ?_⟩
  rfl

/-- The witness-bearing one-sided cover is exactly the coset-corrected
three-root unit cover. -/
def orbitConnectingThreeRootPowerCoverEquivPulled
    (alpha gamma k omegaInv B C0 : K) (d : ℕ) :
    orbitConnectingThreeRootPowerCoverSolutions
        alpha gamma k omegaInv B C0 d ≃
      UnitThreeRootPowerCover
        (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
        (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
        (C omegaInv * centeredNormPulledRadicand B C0 d) where
  toFun :=
    orbitConnectingThreeRootPowerCoverToPulled
      alpha gamma k omegaInv B C0 d
  invFun :=
    orbitConnectingPulledToThreeRootPowerCover
      alpha gamma k omegaInv B C0 d
  left_inv := by
    intro z
    apply Subtype.ext
    apply Prod.ext
    · apply OrbitConnectingThreeRootWitness.ext
      · simpa [orbitConnectingThreeRootPowerCoverToPulled,
          orbitConnectingPulledToThreeRootPowerCover] using z.2.symm
      · simp [orbitConnectingThreeRootPowerCoverToPulled,
          orbitConnectingPulledToThreeRootPowerCover]
      · simp [orbitConnectingThreeRootPowerCoverToPulled,
          orbitConnectingPulledToThreeRootPowerCover]
      · simp [orbitConnectingThreeRootPowerCoverToPulled,
          orbitConnectingPulledToThreeRootPowerCover]
    · rfl
  right_inv := by
    intro z
    apply UnitThreeRootPowerCover.ext
    · rfl
    · simp [orbitConnectingThreeRootPowerCoverToPulled,
        orbitConnectingPulledToThreeRootPowerCover]
    · simp [orbitConnectingThreeRootPowerCoverToPulled,
        orbitConnectingPulledToThreeRootPowerCover]
    · simp [orbitConnectingThreeRootPowerCoverToPulled,
        orbitConnectingPulledToThreeRootPowerCover]

/-- Repackage a good witness power-cover point as a restricted unrestricted
witness-cover point. -/
private def orbitConnectingGoodPowerCoverEquivRestrictedCover
    (alpha gamma k omegaInv B C0 : K) (d : ℕ) :
    orbitConnectingGoodThreeRootPowerCoverSolutions
        alpha gamma k omegaInv B C0 d ≃
      {z :
          orbitConnectingThreeRootPowerCoverSolutions
            alpha gamma k omegaInv B C0 d //
        z.1.1.thirdRoot ≠ 0} where
  toFun z := ⟨⟨(z.1.1.1, z.1.2), z.2⟩, z.1.1.2⟩
  invFun z := ⟨(⟨z.1.1.1, z.2⟩, z.1.1.2), z.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The unrestricted pulled-cover equivalence preserves nonvanishing of the
third root. -/
private def orbitConnectingRestrictedPowerCoverEquivGoodPulled
    (alpha gamma k omegaInv B C0 : K) (d : ℕ) :
    {z :
        orbitConnectingThreeRootPowerCoverSolutions
          alpha gamma k omegaInv B C0 d //
      z.1.1.thirdRoot ≠ 0} ≃
      GoodUnitThreeRootPowerCover
        (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
        (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
        (C omegaInv * centeredNormPulledRadicand B C0 d) :=
  Equiv.subtypeEquiv
    (p := fun z => z.1.1.thirdRoot ≠ 0)
    (q := fun z => z.thirdRoot ≠ 0)
    (orbitConnectingThreeRootPowerCoverEquivPulled
      alpha gamma k omegaInv B C0 d) fun z => by
    change z.1.1.thirdRoot ≠ 0 ↔
      (z.1.2 : K) ^ d * z.1.1.thirdRoot ≠ 0
    constructor
    · exact fun hthird =>
        mul_ne_zero (pow_ne_zero d z.1.2.ne_zero) hthird
    · intro hscaled hzero
      apply hscaled
      simp [hzero]

/-- Good orbit-connecting witness power-cover points are exactly the good
coset-corrected pulled-cover points. -/
def orbitConnectingGoodThreeRootPowerCoverEquivPulled
    (alpha gamma k omegaInv B C0 : K) (d : ℕ) :
    orbitConnectingGoodThreeRootPowerCoverSolutions
        alpha gamma k omegaInv B C0 d ≃
      GoodUnitThreeRootPowerCover
        (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
        (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
        (C omegaInv * centeredNormPulledRadicand B C0 d) :=
  (orbitConnectingGoodPowerCoverEquivRestrictedCover
      alpha gamma k omegaInv B C0 d).trans
    (orbitConnectingRestrictedPowerCoverEquivGoodPulled
      alpha gamma k omegaInv B C0 d)

/-- Exact `d`-fold multiplicity of the good coset-corrected pulled cover
over its good-witness power-map range. -/
theorem
    natCard_orbitConnectingGoodUnitThreeRootPowerCover_eq_mul_powerRange
    [Finite K] [IsCyclic Kˣ]
    (alpha gamma k omegaInv B C0 : K) (d : ℕ)
    (hd : d ∣ Nat.card Kˣ) :
    Nat.card
        (GoodUnitThreeRootPowerCover
          (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
          (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
          (C omegaInv * centeredNormPulledRadicand B C0 d)) =
      d * Nat.card
        (orbitConnectingGoodThreeRootPowerRangeSolutions
          alpha gamma k omegaInv B C0 d) := by
  calc
    Nat.card
        (GoodUnitThreeRootPowerCover
          (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
          (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
          (C omegaInv * centeredNormPulledRadicand B C0 d)) =
        Nat.card
          (orbitConnectingGoodThreeRootPowerCoverSolutions
            alpha gamma k omegaInv B C0 d) :=
      Nat.card_congr
        (orbitConnectingGoodThreeRootPowerCoverEquivPulled
          alpha gamma k omegaInv B C0 d).symm
    _ = d * Nat.card
        (orbitConnectingGoodThreeRootPowerRangeSolutions
          alpha gamma k omegaInv B C0 d) := by
      simpa [orbitConnectingGoodThreeRootPowerCoverSolutions,
        orbitConnectingGoodThreeRootPowerRangeSolutions] using
          (BGS.natCard_rightPowerTraceCoverSolutions_of_dvd
            (fun w :
              OrbitConnectingGoodThreeRootWitness
                alpha gamma k omegaInv B C0 => w.1.middle)
            (BGS.Markoff.splitTorusTrace : Kˣ → K) d hd)

/-- The two orbit-component pullbacks and the scaled centered-norm pullback
have the seven product-degree bounds obtained from the common bound `4d`. -/
theorem orbitConnectingSevenScaledRadicandProducts_natDegree_le
    (alpha gamma k omegaInv B C0 : K) (d : ℕ) :
    let f := orbitComponentPlusCosetPulledRadicand alpha gamma k d
    let g := orbitComponentMinusCosetPulledRadicand alpha gamma k d
    let h := C omegaInv * centeredNormPulledRadicand B C0 d
    SevenRadicandProductNatDegreeBounds f g h (4 * d) := by
  dsimp only
  apply sevenRadicandProductNatDegreeBounds_of_le
  · exact
      (orbitComponentPlusCosetPulledRadicand_natDegree_le
        alpha gamma k d).trans (by omega)
  · exact
      (orbitComponentMinusCosetPulledRadicand_natDegree_le
        alpha gamma k d).trans (by omega)
  · exact
      scaledCenteredNormPulledRadicand_natDegree_le
        omegaInv B C0 d

section FiniteField

variable [Fintype K] [DecidableEq K]

/-- Conditional seven-plane error package for the orbit-component
radicands.  The hypothesis is precisely the geometric square-class input
that must be proved by the orbit-connecting geometry layer. -/
theorem orbitConnectingSevenScaledSquareRootCoverPointCount_errors_le
    {alpha gamma k omegaInv B C0 : K}
    {d : ℕ} (hd : 0 < d)
    (habsolute :
      SevenHyperellipticPlanesAbsolutelyIrreducible
        (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
        (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
        (C omegaInv * centeredNormPulledRadicand B C0 d)) :
    SevenSquareRootCoverPointCountErrorsAtMost
      (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
      (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
      (C omegaInv * centeredNormPulledRadicand B C0 d)
      (4 * d) := by
  apply sevenSquareRootCoverPointCountErrorsAtMost_of_degreeBounds
    (by omega)
  · exact orbitConnectingSevenScaledRadicandProducts_natDegree_le
      alpha gamma k omegaInv B C0 d
  · exact habsolute

/-- The seven signed cover errors for the orbit-component radicands have
total absolute value at most `768 d sqrt(|K|)`. -/
theorem
    orbitConnectingSevenScaledSquareRootCoverPointCount_sum_abs_error_le
    {alpha gamma k omegaInv B C0 : K}
    {d : ℕ} (hd : 0 < d)
    (habsolute :
      SevenHyperellipticPlanesAbsolutelyIrreducible
        (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
        (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
        (C omegaInv * centeredNormPulledRadicand B C0 d)) :
    let f := orbitComponentPlusCosetPulledRadicand alpha gamma k d
    let g := orbitComponentMinusCosetPulledRadicand alpha gamma k d
    let h := C omegaInv * centeredNormPulledRadicand B C0 d
    |squareRootCoverPointCountError f| +
        |squareRootCoverPointCountError g| +
        |squareRootCoverPointCountError h| +
        |squareRootCoverPointCountError (f * g)| +
        |squareRootCoverPointCountError (f * h)| +
        |squareRootCoverPointCountError (g * h)| +
        |squareRootCoverPointCountError (f * g * h)| ≤
      768 * d * Real.sqrt (Fintype.card K : ℝ) := by
  dsimp only
  have herrors :=
    orbitConnectingSevenScaledSquareRootCoverPointCount_errors_le
      hd habsolute
  calc
    |squareRootCoverPointCountError
          (orbitComponentPlusCosetPulledRadicand alpha gamma k d)| +
        |squareRootCoverPointCountError
          (orbitComponentMinusCosetPulledRadicand alpha gamma k d)| +
        |squareRootCoverPointCountError
          (C omegaInv * centeredNormPulledRadicand B C0 d)| +
        |squareRootCoverPointCountError
          (orbitComponentPlusCosetPulledRadicand alpha gamma k d *
            orbitComponentMinusCosetPulledRadicand alpha gamma k d)| +
        |squareRootCoverPointCountError
          (orbitComponentPlusCosetPulledRadicand alpha gamma k d *
            (C omegaInv * centeredNormPulledRadicand B C0 d))| +
        |squareRootCoverPointCountError
          (orbitComponentMinusCosetPulledRadicand alpha gamma k d *
            (C omegaInv * centeredNormPulledRadicand B C0 d))| +
        |squareRootCoverPointCountError
          (orbitComponentPlusCosetPulledRadicand alpha gamma k d *
            orbitComponentMinusCosetPulledRadicand alpha gamma k d *
              (C omegaInv *
                centeredNormPulledRadicand B C0 d))| ≤
        192 * ((4 * d : ℕ) : ℝ) *
          Real.sqrt (Fintype.card K : ℝ) :=
      sevenSquareRootCoverPointCount_sum_abs_error_le herrors
    _ = 768 * d * Real.sqrt (Fintype.card K : ℝ) := by
      push_cast
      ring

/-- Conditional affine point-count estimate for the three simultaneous
orbit-component/centered-norm square roots. -/
theorem
    orbitConnectingScaledThreeSquareRootFiberProductPointCount_error_le
    (hchar : ringChar K ≠ 2)
    {alpha gamma k omegaInv B C0 : K}
    {d : ℕ} (hd : 0 < d)
    (habsolute :
      SevenHyperellipticPlanesAbsolutelyIrreducible
        (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
        (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
        (C omegaInv * centeredNormPulledRadicand B C0 d)) :
    let f := orbitComponentPlusCosetPulledRadicand alpha gamma k d
    let g := orbitComponentMinusCosetPulledRadicand alpha gamma k d
    let h := C omegaInv * centeredNormPulledRadicand B C0 d
    |((threeSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter)
          (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
        (Fintype.card K : ℝ)| ≤
      768 * d * Real.sqrt (Fintype.card K : ℝ) := by
  dsimp only
  exact
    (threeSquareRootFiberProductPointCount_error_le_sum_seven
      hchar
      (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
      (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
      (C omegaInv * centeredNormPulledRadicand B C0 d)).trans
      (orbitConnectingSevenScaledSquareRootCoverPointCount_sum_abs_error_le
        hd habsolute)

/-- The affine three-root cover type realizes the same
`768 d sqrt(|K|)` error estimate. -/
theorem orbitConnectingScaledThreeRootPowerCover_card_error_le
    (hchar : ringChar K ≠ 2)
    {alpha gamma k omegaInv B C0 : K}
    {d : ℕ} (hd : 0 < d)
    (habsolute :
      SevenHyperellipticPlanesAbsolutelyIrreducible
        (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
        (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
        (C omegaInv * centeredNormPulledRadicand B C0 d)) :
    let f := orbitComponentPlusCosetPulledRadicand alpha gamma k d
    let g := orbitComponentMinusCosetPulledRadicand alpha gamma k d
    let h := C omegaInv * centeredNormPulledRadicand B C0 d
    |((Nat.card (ThreeRootPowerCover f g h) : ℕ) : ℝ) -
        (Fintype.card K : ℝ)| ≤
      768 * d * Real.sqrt (Fintype.card K : ℝ) := by
  dsimp only
  have hcount :=
    natCard_threeRootPowerCover_eq_pointCount
      (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
      (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
      (C omegaInv * centeredNormPulledRadicand B C0 d)
  have hcountReal :
      ((Nat.card
        (ThreeRootPowerCover
          (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
          (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
          (C omegaInv *
            centeredNormPulledRadicand B C0 d)) : ℕ) : ℝ) =
        ((threeSquareRootFiberProductPointCount
          (fun parameter : K =>
            (orbitComponentPlusCosetPulledRadicand
              alpha gamma k d).eval parameter)
          (fun parameter : K =>
            (orbitComponentMinusCosetPulledRadicand
              alpha gamma k d).eval parameter)
          (fun parameter : K =>
            (C omegaInv *
              centeredNormPulledRadicand B C0 d).eval
                parameter) : ℤ) : ℝ) := by
    exact_mod_cast hcount
  rw [hcountReal]
  exact
    orbitConnectingScaledThreeSquareRootFiberProductPointCount_error_le
      hchar hd habsolute

/-- The zero-parameter affine fiber contributes at most eight points. -/
theorem orbitConnectingScaledZeroParameterFiber_card_le_eight
    (alpha gamma k omegaInv B C0 : K) (d : ℕ) :
    Nat.card
      (ThreeSquareRootFiber
        (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
        (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
        (C omegaInv * centeredNormPulledRadicand B C0 d)
        0) ≤ 8 :=
  natCard_threeSquareRootFiber_le_eight
    (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
    (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
    (C omegaInv * centeredNormPulledRadicand B C0 d)
    0

/-- If the centered-norm scalar is nonzero, the third-root-zero unit locus
has cardinality at most `16d`. -/
theorem
    orbitConnectingScaledThirdRootZeroUnitPowerCover_card_le
    (alpha gamma k B C0 : K)
    {omegaInv : K} (homegaInv : omegaInv ≠ 0)
    {d : ℕ} (hd : 0 < d) :
    Nat.card
      (ThirdRootZeroUnitPowerCover
        (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
        (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
        (C omegaInv * centeredNormPulledRadicand B C0 d)) ≤
      16 * d := by
  have hbad :=
    natCard_thirdRootZeroUnitPowerCover_le_four_mul_natDegree
      (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
      (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
      (C omegaInv * centeredNormPulledRadicand B C0 d)
      (scaledCenteredNormPulledRadicand_ne_zero homegaInv hd)
  have hdegreeBound :=
    scaledCenteredNormPulledRadicand_natDegree_le
      omegaInv B C0 d
  omega

/-- Conditional good-unit cover estimate with both finite corrections made
explicit:

`768 d sqrt(|K|) + 8 + 16d`.
-/
theorem orbitConnectingScaledGoodUnitThreeRootPowerCover_card_error_le
    (hchar : ringChar K ≠ 2)
    {alpha gamma k omegaInv B C0 : K}
    (homegaInv : omegaInv ≠ 0)
    {d : ℕ} (hd : 0 < d)
    (habsolute :
      SevenHyperellipticPlanesAbsolutelyIrreducible
        (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
        (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
        (C omegaInv * centeredNormPulledRadicand B C0 d)) :
    let f := orbitComponentPlusCosetPulledRadicand alpha gamma k d
    let g := orbitComponentMinusCosetPulledRadicand alpha gamma k d
    let h := C omegaInv * centeredNormPulledRadicand B C0 d
    |((Nat.card (GoodUnitThreeRootPowerCover f g h) : ℕ) : ℝ) -
        (Fintype.card K : ℝ)| ≤
      768 * d * Real.sqrt (Fintype.card K : ℝ) +
        8 + 16 * d := by
  dsimp only
  let f := orbitComponentPlusCosetPulledRadicand alpha gamma k d
  let g := orbitComponentMinusCosetPulledRadicand alpha gamma k d
  let h := C omegaInv * centeredNormPulledRadicand B C0 d
  have hbridge :=
    natCard_goodUnitThreeRootPowerCover_eq_pointCount_sub_bad
      f g h
  have hbridgeReal :
      ((Nat.card (GoodUnitThreeRootPowerCover f g h) : ℕ) : ℝ) =
        ((threeSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter)
          (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
        (Nat.card (ThreeSquareRootFiber f g h 0) : ℝ) -
        (Nat.card (ThirdRootZeroUnitPowerCover f g h) : ℝ) := by
    exact_mod_cast hbridge
  have herrorRewrite :
      ((Nat.card (GoodUnitThreeRootPowerCover f g h) : ℕ) : ℝ) -
          (Fintype.card K : ℝ) =
        (((threeSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter)
          (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
            (Fintype.card K : ℝ)) -
          (Nat.card (ThreeSquareRootFiber f g h 0) : ℝ) -
          (Nat.card (ThirdRootZeroUnitPowerCover f g h) : ℝ) := by
    rw [hbridgeReal]
    ring
  have haffine :
      abs (((threeSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter)
          (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
        (Fintype.card K : ℝ)) ≤
          768 * d * Real.sqrt (Fintype.card K : ℝ) := by
    exact
      orbitConnectingScaledThreeSquareRootFiberProductPointCount_error_le
        hchar hd habsolute
  have hzeroNat :
      Nat.card (ThreeSquareRootFiber f g h 0) ≤ 8 := by
    exact natCard_threeSquareRootFiber_le_eight f g h 0
  have hzero :
      (Nat.card (ThreeSquareRootFiber f g h 0) : ℝ) ≤ 8 := by
    exact_mod_cast hzeroNat
  have hbadNat :
      Nat.card (ThirdRootZeroUnitPowerCover f g h) ≤ 16 * d := by
    exact
      orbitConnectingScaledThirdRootZeroUnitPowerCover_card_le
        alpha gamma k B C0 homegaInv hd
  have hbad :
      (Nat.card (ThirdRootZeroUnitPowerCover f g h) : ℝ) ≤
        16 * d := by
    exact_mod_cast hbadNat
  rw [herrorRewrite]
  calc
    |(((threeSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter)
          (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
          (Fintype.card K : ℝ)) -
        (Nat.card (ThreeSquareRootFiber f g h 0) : ℝ) -
        (Nat.card (ThirdRootZeroUnitPowerCover f g h) : ℝ)| ≤
      |(((threeSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter)
          (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
          (Fintype.card K : ℝ))| +
        |(Nat.card (ThreeSquareRootFiber f g h 0) : ℝ)| +
        |(Nat.card
          (ThirdRootZeroUnitPowerCover f g h) : ℝ)| := by
      have hfirst :=
        abs_sub
          ((((threeSquareRootFiberProductPointCount
            (fun parameter : K => f.eval parameter)
            (fun parameter : K => g.eval parameter)
            (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
            (Fintype.card K : ℝ)) -
            (Nat.card (ThreeSquareRootFiber f g h 0) : ℝ))
          (Nat.card
            (ThirdRootZeroUnitPowerCover f g h) : ℝ)
      have hsecond :=
        abs_sub
          (((threeSquareRootFiberProductPointCount
            (fun parameter : K => f.eval parameter)
            (fun parameter : K => g.eval parameter)
            (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
            (Fintype.card K : ℝ))
          (Nat.card (ThreeSquareRootFiber f g h 0) : ℝ)
      linarith
    _ =
      |(((threeSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter)
          (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
          (Fintype.card K : ℝ))| +
        (Nat.card (ThreeSquareRootFiber f g h 0) : ℝ) +
        (Nat.card (ThirdRootZeroUnitPowerCover f g h) : ℝ) := by
      rw [abs_of_nonneg
          (show 0 ≤
            (Nat.card (ThreeSquareRootFiber f g h 0) : ℝ) by
            positivity),
        abs_of_nonneg
          (show 0 ≤
            (Nat.card
              (ThirdRootZeroUnitPowerCover f g h) : ℝ) by
            positivity)]
    _ ≤
      768 * d * Real.sqrt (Fintype.card K : ℝ) +
        8 + 16 * d :=
      add_le_add (add_le_add haffine hzero) hbad

end FiniteField

/-- After exact division by the `d`-fold power-map fibers, the good
orbit-connecting range has a uniform square-root error. -/
theorem orbitConnectingGoodThreeRootPowerRangeSolutions_card_error_le
    (p : ℕ) [Fact p.Prime]
    (hchar : ringChar (ZMod p) ≠ 2)
    {alpha gamma k omegaInv B C0 : ZMod p}
    (d : ℕ) (hdvd : d ∣ Nat.card (ZMod p)ˣ) (hd : 0 < d)
    (homegaInv : omegaInv ≠ 0)
    (habsolute :
      SevenHyperellipticPlanesAbsolutelyIrreducible
        (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
        (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
        (C omegaInv * centeredNormPulledRadicand B C0 d)) :
    |(Nat.card
        (orbitConnectingGoodThreeRootPowerRangeSolutions
          alpha gamma k omegaInv B C0 d) : ℝ) -
        (p : ℝ) / d| ≤
      792 * Real.sqrt (p : ℝ) := by
  let goodCover :=
    GoodUnitThreeRootPowerCover
      (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
      (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
      (C omegaInv * centeredNormPulledRadicand B C0 d)
  let goodRange :=
    orbitConnectingGoodThreeRootPowerRangeSolutions
      alpha gamma k omegaInv B C0 d
  have hcover :
      |(Nat.card goodCover : ℝ) - (p : ℝ)| ≤
        768 * d * Real.sqrt (p : ℝ) + 8 + 16 * d := by
    simpa [goodCover, ZMod.card] using
      (orbitConnectingScaledGoodUnitThreeRootPowerCover_card_error_le
        hchar homegaInv hd habsolute)
  have hmulNat :
      Nat.card goodCover = d * Nat.card goodRange := by
    simpa [goodCover, goodRange] using
      (natCard_orbitConnectingGoodUnitThreeRootPowerCover_eq_mul_powerRange
        alpha gamma k omegaInv B C0 d hdvd)
  have hmulReal :
      (Nat.card goodCover : ℝ) =
        (d : ℝ) * (Nat.card goodRange : ℝ) := by
    exact_mod_cast hmulNat
  rw [hmulReal] at hcover
  have hdReal : (0 : ℝ) < d := by
    exact_mod_cast hd
  have hrewrite :
      (d : ℝ) * (Nat.card goodRange : ℝ) - (p : ℝ) =
        (d : ℝ) *
          ((Nat.card goodRange : ℝ) - (p : ℝ) / d) := by
    field_simp
  rw [hrewrite, abs_mul, abs_of_pos hdReal] at hcover
  have hdOne : (1 : ℝ) ≤ d := by
    exact_mod_cast hd
  have hpOne : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hpOneReal : (1 : ℝ) ≤ p := by
    exact_mod_cast hpOne
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hpOneReal
  nlinarith

/-- If the explicit divisor error is smaller than the Möbius main term, a
primitive split-torus parameter exists together with a good
orbit-connecting witness. -/
theorem
    exists_primitive_orbitConnectingGoodThreeRootWitness_of_explicitInequality
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (alpha gamma k omegaInv B C0 : ZMod p)
    (homegaInv : omegaInv ≠ 0)
    (habsolute :
      ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
        SevenHyperellipticPlanesAbsolutelyIrreducible
          (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
          (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
          (C omegaInv * centeredNormPulledRadicand B C0 d))
    (hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          (792 * Real.sqrt (p : ℝ)) < p) :
    ∃ q : (ZMod p)ˣ,
      ∃ w :
          OrbitConnectingGoodThreeRootWitness
            alpha gamma k omegaInv B C0,
        w.1.middle = BGS.Markoff.splitTorusTrace q ∧
          orderOf q = p - 1 := by
  let leftTrace :
      OrbitConnectingGoodThreeRootWitness
          alpha gamma k omegaInv B C0 →
        ZMod p :=
    fun w => w.1.middle
  let rightTrace : (ZMod p)ˣ → ZMod p :=
    BGS.Markoff.splitTorusTrace
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hRange :
      ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
        |(Nat.card
            (BGS.rightPowerTraceRangeSolutions
              leftTrace rightTrace d) : ℝ) -
            (p : ℝ) / d| ≤
          792 * Real.sqrt (p : ℝ) := by
    intro d hdvd hd
    simpa [leftTrace, rightTrace,
      orbitConnectingGoodThreeRootPowerRangeSolutions] using
      (orbitConnectingGoodThreeRootPowerRangeSolutions_card_error_le
        p hchar d hdvd hd homegaInv
          (habsolute d hdvd hd))
  have hpositive :=
    BGS.Markoff.divisorsError_lt_primitiveTraceMoebiusMainTerm_of_explicitInequality
      (Nat.card (ZMod p)ˣ) p 1 792
      Nat.card_pos (by norm_num) (by
        simpa using hexplicit)
  obtain ⟨z, hz⟩ :=
    BGS.rightTraceExactOrderSolutions_nonempty_of_divisorsError_lt_moebiusMain
      leftTrace rightTrace (fun d => (p : ℝ) / d)
      (792 * Real.sqrt (p : ℝ)) hRange (by
        simpa [BGS.Markoff.primitiveTraceMoebiusMainTerm] using hpositive)
  rcases z with ⟨w, q⟩
  have hz' :=
    (BGS.mem_rightTraceExactOrderSolutions_iff
      leftTrace rightTrace (Nat.card (ZMod p)ˣ) (w, q)).mp hz
  refine ⟨q, w, ?_, ?_⟩
  · simpa [leftTrace, rightTrace] using hz'.1
  · rw [Nat.card_units, Nat.card_zmod] at hz'
    exact hz'.2

/-- Uniformly for sufficiently large primes, the geometric
orbit-connecting hypotheses yield a good witness above a primitive
split-torus trace. -/
theorem exists_threshold_primitive_orbitConnectingGoodThreeRootWitness :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
      ∀ (alpha gamma k omegaInv B C0 : ZMod p),
        omegaInv ≠ 0 →
        (∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
          SevenHyperellipticPlanesAbsolutelyIrreducible
            (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
            (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
            (C omegaInv * centeredNormPulledRadicand B C0 d)) →
          ∃ q : (ZMod p)ˣ,
            ∃ w :
                OrbitConnectingGoodThreeRootWitness
                  alpha gamma k omegaInv B C0,
              w.1.middle = BGS.Markoff.splitTorusTrace q ∧
                orderOf q = p - 1 := by
  obtain ⟨inequalityThreshold, hInequality⟩ :=
    BGS.Markoff.exists_threshold_endgamePrimitiveTrace_explicitInequality
      792 (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨max inequalityThreshold 5, ?_⟩
  intro p hp _ alpha gamma k omegaInv B C0
    homegaInv habsolute
  have hpInequality : inequalityThreshold ≤ p :=
    (le_max_left inequalityThreshold 5).trans hp
  have hpFive : 5 ≤ p :=
    (le_max_right inequalityThreshold 5).trans hp
  have hpOne : 1 ≤ p := by omega
  have hpOneReal : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hpOne
  have honeLe :
      ((1 : ℕ) : ℝ) ≤
        (p : ℝ) ^ ((1 : ℝ) / 2 - 1 / 4) := by
    simpa using
      (Real.one_le_rpow hpOneReal
        (show (0 : ℝ) ≤ 1 / 2 - 1 / 4 by norm_num))
  have hexplicit :=
    hInequality p hpInequality 1 honeLe
  apply
    exists_primitive_orbitConnectingGoodThreeRootWitness_of_explicitInequality
      p hpFive alpha gamma k omegaInv B C0
      homegaInv habsolute
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  rw [hcard]
  simpa using hexplicit

end

end GenMarkoff.General.Cage
