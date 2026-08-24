import GenMarkoff.General.Cage.ThreeRootPowerCover

/-!
# Good connecting three-root power covers

The connecting three-root cover has an exact power-map multiplicity before
the third-root-zero locus is removed.  This file restricts the witness type
itself to nonzero third roots.  Scaling by a nonzero power of the unit
parameter preserves that condition, so the restricted witness cover is
equivalent to the good pulled-radicand cover and inherits the same exact
power-map multiplicity.
-/

namespace GenMarkoff.General.Cage

open Polynomial

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- Connecting three-root witnesses whose centered-norm square root is
nonzero. -/
def ConnectingGoodThreeRootWitness
    (a : Coefficients K) (xi eta omegaInv : K) :=
  {w : ConnectingThreeRootWitness a xi eta omegaInv //
    w.thirdRoot ≠ 0}

instance connectingGoodThreeRootWitnessFinite
    [Finite K] (a : Coefficients K) (xi eta omegaInv : K) :
    Finite (ConnectingGoodThreeRootWitness a xi eta omegaInv) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- The one-sided power cover formed from good connecting witnesses. -/
abbrev connectingGoodThreeRootPowerCoverSolutions
    (a : Coefficients K) (xi eta omegaInv : K) (d : ℕ) :=
  BGS.rightPowerTraceCoverSolutions
    (fun w : ConnectingGoodThreeRootWitness a xi eta omegaInv =>
      w.1.middle)
    (BGS.Markoff.splitTorusTrace : Kˣ → K) d

/-- The power-range quotient formed from good connecting witnesses. -/
abbrev connectingGoodThreeRootPowerRangeSolutions
    (a : Coefficients K) (xi eta omegaInv : K) (d : ℕ) :=
  BGS.rightPowerTraceRangeSolutions
    (fun w : ConnectingGoodThreeRootWitness a xi eta omegaInv =>
      w.1.middle)
    (BGS.Markoff.splitTorusTrace : Kˣ → K) d

/-- Repackage a cover whose witness type is already restricted as a subtype
of the unrestricted witness cover. -/
private def connectingGoodPowerCoverEquivRestrictedCover
    (a : Coefficients K) (xi eta omegaInv : K) (d : ℕ) :
    connectingGoodThreeRootPowerCoverSolutions
        a xi eta omegaInv d ≃
      {z : connectingThreeRootPowerCoverSolutions
          a xi eta omegaInv d //
        z.1.1.thirdRoot ≠ 0} where
  toFun z :=
    ⟨⟨(z.1.1.1, z.1.2), z.2⟩, z.1.1.2⟩
  invFun z :=
    ⟨(⟨z.1.1.1, z.2⟩, z.1.1.2), z.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The unrestricted pulled-cover equivalence preserves nonvanishing of the
third root because its scaling factor is a nonzero power of a unit. -/
private def connectingRestrictedPowerCoverEquivGoodPulled
    (a : Coefficients K) (xi eta omegaInv : K) (d : ℕ) :
    {z : connectingThreeRootPowerCoverSolutions
        a xi eta omegaInv d //
      z.1.1.thirdRoot ≠ 0} ≃
      GoodUnitThreeRootPowerCover
        (incidencePulledRadicand a xi d)
        (incidencePulledRadicand a eta d)
        (C omegaInv *
          centeredNormPulledRadicand a.a3 a.a1 d) :=
  Equiv.subtypeEquiv
    (p := fun z => z.1.1.thirdRoot ≠ 0)
    (q := fun z => z.thirdRoot ≠ 0)
    (connectingThreeRootPowerCoverEquivPulled
      a xi eta omegaInv d) fun z => by
    change z.1.1.thirdRoot ≠ 0 ↔
      (z.1.2 : K) ^ d * z.1.1.thirdRoot ≠ 0
    constructor
    · exact fun hthird =>
        mul_ne_zero (pow_ne_zero d z.1.2.ne_zero) hthird
    · intro hscaled hzero
      apply hscaled
      simp [hzero]

/-- Good witness-bearing power-cover points are exactly good points of the
pulled-radicand unit cover. -/
def connectingGoodThreeRootPowerCoverEquivPulled
    (a : Coefficients K) (xi eta omegaInv : K) (d : ℕ) :
    connectingGoodThreeRootPowerCoverSolutions
        a xi eta omegaInv d ≃
      GoodUnitThreeRootPowerCover
        (incidencePulledRadicand a xi d)
        (incidencePulledRadicand a eta d)
        (C omegaInv *
          centeredNormPulledRadicand a.a3 a.a1 d) :=
  (connectingGoodPowerCoverEquivRestrictedCover
      a xi eta omegaInv d).trans
    (connectingRestrictedPowerCoverEquivGoodPulled
      a xi eta omegaInv d)

/-- Exact `d`-fold multiplicity of the good connecting pulled cover over its
good-witness power-map range. -/
theorem natCard_connectingGoodUnitThreeRootPowerCover_eq_mul_powerRange
    [Finite K] [IsCyclic Kˣ]
    (a : Coefficients K) (xi eta omegaInv : K) (d : ℕ)
    (hd : d ∣ Nat.card Kˣ) :
    Nat.card
        (GoodUnitThreeRootPowerCover
          (incidencePulledRadicand a xi d)
          (incidencePulledRadicand a eta d)
          (C omegaInv *
            centeredNormPulledRadicand a.a3 a.a1 d)) =
      d * Nat.card
        (connectingGoodThreeRootPowerRangeSolutions
          a xi eta omegaInv d) := by
  calc
    Nat.card
        (GoodUnitThreeRootPowerCover
          (incidencePulledRadicand a xi d)
          (incidencePulledRadicand a eta d)
          (C omegaInv *
            centeredNormPulledRadicand a.a3 a.a1 d)) =
        Nat.card
          (connectingGoodThreeRootPowerCoverSolutions
            a xi eta omegaInv d) :=
      Nat.card_congr
        (connectingGoodThreeRootPowerCoverEquivPulled
          a xi eta omegaInv d).symm
    _ = d * Nat.card
        (connectingGoodThreeRootPowerRangeSolutions
          a xi eta omegaInv d) := by
      simpa [connectingGoodThreeRootPowerCoverSolutions,
        connectingGoodThreeRootPowerRangeSolutions] using
          (BGS.natCard_rightPowerTraceCoverSolutions_of_dvd
            (fun w : ConnectingGoodThreeRootWitness
              a xi eta omegaInv => w.1.middle)
            (BGS.Markoff.splitTorusTrace : Kˣ → K) d hd)

end

end GenMarkoff.General.Cage
