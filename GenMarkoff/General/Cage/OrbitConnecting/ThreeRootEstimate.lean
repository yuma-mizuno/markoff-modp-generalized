import GenMarkoff.General.Cage.Connecting.ThreeRootEstimate
import GenMarkoff.General.Cage.OrbitConnecting.PulledRadicands

/-!
# Three-root cover estimate for orbit-component connecting data

The orbit-coset connecting step uses the two coset-corrected component
pullbacks

`X^d * orbitComponentPlusPulledRadicand alpha gamma k d`,
`X^d * orbitComponentMinusPulledRadicand alpha gamma k d`,

together with a nonzero scalar multiple of the centered-norm pullback.  The
extra `X^d` makes the value at a unit `t` equal to `(t^d)^2` times the
component radicand at `U = splitTorusTrace (t^d) - gamma`, so a point of the
unit cover is an
`OrbitConnectingThreeRootWitness` together with a power parameter
(`orbitConnectingThreeRootPowerCoverEquivPulled`).  This file records the
counting consequences of absolute irreducibility of the seven associated
hyperelliptic planes.

The two orbit-component radicands have degree at most `3d`, while the
centered-norm radicand has degree at most `4d`.  Using `4d` as a common
degree bound gives affine error `768 d sqrt(|K|)`.  Removing the zero
parameter costs at most `8`, and removing the third-root-zero locus costs at
most `16d`.  Over `ZMod p`, dividing by the `d`-fold power-map fibers gives
the uniform error `792 * sqrt p` for the good-witness power range
(`orbitConnectingGoodThreeRootPowerRangeSolutions_card_error_le`).

Absolute irreducibility of the seven planes is an explicit hypothesis here;
it is proved in `GenMarkoff.General.Cage.OrbitConnecting.SquareClasses`.
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

/-- Repackage a good-witness power-cover point as a point of the
all-witness power cover whose third root is nonzero. -/
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
    -- The third root of the image under
    -- `orbitConnectingThreeRootPowerCoverToPulled` is by definition the
    -- witness root scaled by `parameter ^ d`; restate the transported
    -- predicate in this form so that both directions follow from
    -- `mul_ne_zero` and `simp`.
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

/-- If the seven hyperelliptic planes of the orbit-component radicands and
the scaled centered-norm radicand are absolutely irreducible, their cover
point-count errors satisfy the degree-`4d` bounds
`SevenSquareRootCoverPointCountErrorsAtMost`. -/
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

/-- If the seven planes are absolutely irreducible, the affine count of
simultaneous square roots of the two orbit-component radicands and the scaled
centered-norm radicand differs from `|K|` by at most `768 d sqrt(|K|)`. -/
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

/-- If the seven planes are absolutely irreducible and `omegaInv ≠ 0`, the
good unit cover differs from `|K|` by at most

`768 d sqrt(|K|) + 8 + 16d`,

the last two terms accounting for the zero parameter and the
third-root-zero locus.
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
  -- The good unit count is the affine count minus the zero-parameter fiber
  -- and the third-root-zero locus.
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
  -- Bound the affine error, the zero fiber, and the third-root-zero locus.
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
  -- Combine the three bounds with the triangle inequality.
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

/-- For odd `p` and positive `d ∣ p - 1`, the good-witness power range over
`ZMod p` has cardinality within `792 * sqrt p` of `p / d`, provided the seven
planes are absolutely irreducible and `omegaInv ≠ 0`. -/
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
  -- The good cover has exactly `d` points over each point of the range.
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
  -- Divide by `d ≥ 1`; then `8 / d + 16 ≤ 24 ≤ 24 * sqrt p`.
  have hdOne : (1 : ℝ) ≤ d := by
    exact_mod_cast hd
  have hpOne : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hpOneReal : (1 : ℝ) ≤ p := by
    exact_mod_cast hpOne
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hpOneReal
  nlinarith

end

end GenMarkoff.General.Cage
