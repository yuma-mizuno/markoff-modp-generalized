import GenMarkoff.Symmetric.Cage.PlaneCountComparison
import GenMarkoff.Symmetric.Cage.PlaneHasseWeil
import BGS.Markoff.Cage.PlaneHasseWeil

/-!
# Transferring incidence-plane estimates to the raw witness count

This file combines:

* the generalized incidence-plane Hasse--Weil estimates;
* the explicit diagonal and off-diagonal count comparisons;
* the exact `d`-fold one-sided power-cover multiplicity.

The output is the unfiltered range estimate consumed by
`RegularWitnessFilter`.
-/

namespace GenMarkoff.Symmetric.Cage

noncomputable section

/-- The diagonal plane estimate gives the raw incidence range estimate with
geometric multiplicity two. -/
theorem rawDiagonalIncidenceRangeEstimate
    (planeCoefficient : Nat)
    (hPlane : IncidencePlanePointEstimate planeCoefficient)
    (p : Nat) [Fact p.Prime] (hpFive : 5 ≤ p)
    (c xi : ZMod p) (hc : c ^ 2 ≠ 4)
    (hxi : OrderedTraceCandidateRegular c c c xi)
    (d : Nat) (hd : d ∣ Nat.card (ZMod p)ˣ)
    (hdPositive : 0 < d) :
    |(Nat.card
          (rawIncidenceWitnessPowerRangeSolutions
            p c xi xi d) : Real) -
        (2 : Real) * p / d| ≤
      ((2 * planeCoefficient + 8 : Nat) : Real) *
        Real.sqrt p := by
  have hpTwo : p ≠ 2 := by omega
  have hcomparisonInt :=
    incidencePulledRootPair_diagonal_card_comparison
      p hpTwo c xi hdPositive hxi
  have hcomparison :
      |(Nat.card
            (IncidencePulledRootPair p c xi xi d) : Real) -
          2 *
            (BGS.External.affinePlaneCurveZeros (ZMod p)
              (incidenceDiagonalPlanePolynomial c xi d)).card| ≤
        (4 * d + 4 : Real) := by
    exact_mod_cast hcomparisonInt
  have hHasse :=
    (hPlane p hpFive c xi xi hc hxi hxi
      d hd hdPositive).1
  have hsqrt : (1 : Real) ≤ Real.sqrt p := by
    have hpNonnegative : (0 : Real) ≤ p := by positivity
    have hsquare := Real.sq_sqrt hpNonnegative
    have hsqrtNonnegative : (0 : Real) ≤ Real.sqrt p :=
      Real.sqrt_nonneg (p : Real)
    have hpFiveReal : (5 : Real) ≤ p := by
      exact_mod_cast hpFive
    nlinarith
  have hdOne : (1 : Real) ≤ d := by
    exact_mod_cast hdPositive
  have hexception :
      ((4 * d + 4 : Nat) : Real) ≤
        8 * Real.sqrt p * d := by
    push_cast
    nlinarith
  have hcoverError :
      |(Nat.card
            (IncidencePulledRootPair p c xi xi d) : Real) -
          (2 : Real) * p| ≤
        (((2 * planeCoefficient + 8 : Nat) : Real) *
          Real.sqrt p) * d := by
    let planeCard :=
      (BGS.External.affinePlaneCurveZeros (ZMod p)
        (incidenceDiagonalPlanePolynomial c xi d)).card
    have hcomparisonPlane :
        |(Nat.card
              (IncidencePulledRootPair p c xi xi d) : Real) -
            2 * planeCard| ≤
          ((4 * d + 4 : Nat) : Real) := by
      simpa [planeCard] using hcomparison
    have hHassePlane :
        |(planeCard : Real) - p| ≤
          (planeCoefficient : Real) * Real.sqrt p * d := by
      simpa only [planeCard] using hHasse
    calc
      |(Nat.card
            (IncidencePulledRootPair p c xi xi d) : Real) -
          (2 : Real) * p| =
          |((Nat.card
              (IncidencePulledRootPair p c xi xi d) : Real) -
              2 * planeCard) +
            2 * ((planeCard : Real) - p)| := by
              congr 1
              ring
      _ ≤
          |(Nat.card
              (IncidencePulledRootPair p c xi xi d) : Real) -
              2 * planeCard| +
            |2 * ((planeCard : Real) - p)| :=
        abs_add_le _ _
      _ =
          |(Nat.card
              (IncidencePulledRootPair p c xi xi d) : Real) -
              2 * planeCard| +
            2 * |(planeCard : Real) - p| := by
        rw [abs_mul]
        norm_num
      _ ≤
          ((4 * d + 4 : Nat) : Real) +
            2 *
              ((planeCoefficient : Real) *
                Real.sqrt p * d) := by
        exact add_le_add hcomparisonPlane
          (mul_le_mul_of_nonneg_left hHassePlane (by norm_num))
      _ ≤
          8 * Real.sqrt p * d +
            2 *
              ((planeCoefficient : Real) *
                Real.sqrt p * d) := by
        gcongr
      _ =
          (((2 * planeCoefficient + 8 : Nat) : Real) *
            Real.sqrt p) * d := by
        push_cast
        ring
  apply BGS.Markoff.range_count_error_of_exact_cover
    hdPositive
    (natCard_incidencePulledRootPair_eq_mul_rawPowerRange
      p c xi xi d hd)
  simpa only [Nat.cast_ofNat] using hcoverError

/-- Off the diagonal, the primitive quartic plane model gives multiplicity
one and an explicit `16 sqrt(p)` comparison allowance. -/
theorem rawOffDiagonalIncidenceRangeEstimate
    (planeCoefficient : Nat)
    (hPlane : IncidencePlanePointEstimate planeCoefficient)
    (p : Nat) [Fact p.Prime] (hpFive : 5 ≤ p)
    (c xi eta : ZMod p) (hc : c ^ 2 ≠ 4)
    (hxi : OrderedTraceCandidateRegular c c c xi)
    (heta : OrderedTraceCandidateRegular c c c eta)
    (hpair : IsHasseWeilReadyIncidencePair c xi eta)
    (d : Nat) (hd : d ∣ Nat.card (ZMod p)ˣ)
    (hdPositive : 0 < d) :
    |(Nat.card
          (rawIncidenceWitnessPowerRangeSolutions
            p c xi eta d) : Real) -
        (p : Real) / d| ≤
      ((planeCoefficient + 16 : Nat) : Real) *
        Real.sqrt p := by
  have hpTwo : p ≠ 2 := by omega
  have hcomparisonInt :=
    incidencePulledRootPair_offDiagonal_card_comparison
      p hpTwo c xi eta hdPositive hc hxi heta hpair
  have hcomparison :
      |(Nat.card
            (IncidencePulledRootPair p c xi eta d) : Real) -
          (BGS.External.affinePlaneCurveZeros (ZMod p)
            (incidenceOffDiagonalPlanePolynomial
              c xi eta d)).card| ≤
        (12 * d + 4 : Real) := by
    exact_mod_cast hcomparisonInt
  have hHasse :=
    (hPlane p hpFive c xi eta hc hxi heta
      d hd hdPositive).2 hpair
  have hsqrt : (1 : Real) ≤ Real.sqrt p := by
    have hpNonnegative : (0 : Real) ≤ p := by positivity
    have hsquare := Real.sq_sqrt hpNonnegative
    have hsqrtNonnegative : (0 : Real) ≤ Real.sqrt p :=
      Real.sqrt_nonneg (p : Real)
    have hpFiveReal : (5 : Real) ≤ p := by
      exact_mod_cast hpFive
    nlinarith
  have hdOne : (1 : Real) ≤ d := by
    exact_mod_cast hdPositive
  have hexception :
      ((12 * d + 4 : Nat) : Real) ≤
        16 * Real.sqrt p * d := by
    push_cast
    nlinarith
  have hcoverError :
      |(Nat.card
            (IncidencePulledRootPair p c xi eta d) : Real) -
          (p : Real)| ≤
        (((planeCoefficient + 16 : Nat) : Real) *
          Real.sqrt p) * d := by
    let planeCard :=
      (BGS.External.affinePlaneCurveZeros (ZMod p)
        (incidenceOffDiagonalPlanePolynomial c xi eta d)).card
    have hcomparisonPlane :
        |(Nat.card
              (IncidencePulledRootPair p c xi eta d) : Real) -
            planeCard| ≤
          ((12 * d + 4 : Nat) : Real) := by
      simpa [planeCard] using hcomparison
    have hHassePlane :
        |(planeCard : Real) - p| ≤
          (planeCoefficient : Real) * Real.sqrt p * d := by
      simpa only [planeCard] using hHasse
    calc
      |(Nat.card
            (IncidencePulledRootPair p c xi eta d) : Real) -
          (p : Real)| =
          |((Nat.card
              (IncidencePulledRootPair p c xi eta d) : Real) -
              planeCard) +
            ((planeCard : Real) - p)| := by
              congr 1
              ring
      _ ≤
          |(Nat.card
              (IncidencePulledRootPair p c xi eta d) : Real) -
              planeCard| +
            |(planeCard : Real) - p| :=
        abs_add_le _ _
      _ ≤
          ((12 * d + 4 : Nat) : Real) +
            ((planeCoefficient : Real) *
              Real.sqrt p * d) := by
        exact add_le_add hcomparisonPlane hHassePlane
      _ ≤
          16 * Real.sqrt p * d +
            ((planeCoefficient : Real) *
              Real.sqrt p * d) := by
        gcongr
      _ =
          (((planeCoefficient + 16 : Nat) : Real) *
            Real.sqrt p) * d := by
        push_cast
        ring
  have hrange :=
    BGS.Markoff.range_count_error_of_exact_cover
      (coverCard :=
        Nat.card (IncidencePulledRootPair p c xi eta d))
      (rangeCard :=
        Nat.card
          (rawIncidenceWitnessPowerRangeSolutions
            p c xi eta d))
      (p := p) (d := d) (multiplicity := 1)
      (error :=
        ((planeCoefficient + 16 : Nat) : Real) *
          Real.sqrt p)
      hdPositive
      (natCard_incidencePulledRootPair_eq_mul_rawPowerRange
        p c xi eta d hd)
      (by simpa only [Nat.cast_one, one_mul] using hcoverError)
  simpa only [Nat.cast_one, one_mul] using hrange

/-- A uniform incidence-plane estimate supplies the complete unfiltered
witness estimate.  The diagonal branch uses multiplicity two; the
off-diagonal branch uses multiplicity one. -/
theorem rawIncidenceWitnessPointEstimate_of_plane
    (planeCoefficient : Nat)
    (hPlane : IncidencePlanePointEstimate planeCoefficient) :
    RawIncidenceWitnessPointEstimate
      (2 * planeCoefficient + 16) := by
  intro p _ hpFive c xi eta hc hxi heta hpair
  rcases hpair with hdiagonal | hoffDiagonal
  · subst eta
    refine ⟨2, by norm_num, ?_⟩
    intro d hd hdPositive
    calc
      |(Nat.card
            (rawIncidenceWitnessPowerRangeSolutions
              p c xi xi d) : Real) -
          (2 : Real) * p / d| ≤
          ((2 * planeCoefficient + 8 : Nat) : Real) *
            Real.sqrt p :=
        rawDiagonalIncidenceRangeEstimate
          planeCoefficient hPlane p hpFive c xi hc hxi.1
          d hd hdPositive
      _ ≤
          ((2 * planeCoefficient + 16 : Nat) : Real) *
            Real.sqrt p := by
        have hsqrt : 0 ≤ Real.sqrt (p : Real) :=
          Real.sqrt_nonneg _
        push_cast
        nlinarith
  · refine ⟨1, by norm_num, ?_⟩
    intro d hd hdPositive
    norm_num only [Nat.cast_one, one_mul]
    calc
      |(Nat.card
            (rawIncidenceWitnessPowerRangeSolutions
              p c xi eta d) : Real) -
          (p : Real) / d| ≤
          ((planeCoefficient + 16 : Nat) : Real) *
            Real.sqrt p :=
        rawOffDiagonalIncidenceRangeEstimate
          planeCoefficient hPlane p hpFive c xi eta hc
          hxi.1 heta.1 hoffDiagonal d hd hdPositive
      _ ≤
          ((2 * planeCoefficient + 16 : Nat) : Real) *
            Real.sqrt p := by
        have hsqrt : 0 ≤ Real.sqrt (p : Real) :=
          Real.sqrt_nonneg _
        have hcoefficient : (0 : Real) ≤ planeCoefficient := by
          positivity
        push_cast
        nlinarith

/-- The in-repository general affine Hasse--Weil theorem supplies a positive
unfiltered incidence-witness coefficient. -/
theorem exists_rawIncidenceWitnessPointEstimate_of_generalHasseWeil
    (hHasse :
      BGS.External.GeneralBivariateAffineHasseWeilTheorem) :
    ∃ coefficient : Nat,
      0 < coefficient ∧
        RawIncidenceWitnessPointEstimate coefficient := by
  obtain ⟨planeCoefficient, hplanePositive, hPlane⟩ :=
    exists_incidencePlanePointEstimate_of_generalHasseWeil
      hHasse
  refine ⟨2 * planeCoefficient + 16, by omega, ?_⟩
  exact rawIncidenceWitnessPointEstimate_of_plane
    planeCoefficient hPlane

/-- Composing the raw plane estimate with the uniform deletion bound gives
the exact regular estimate required by the cage connectivity theorem. -/
theorem exists_regularIncidenceWitnessPointEstimate_of_generalHasseWeil
    (hHasse :
      BGS.External.GeneralBivariateAffineHasseWeilTheorem) :
    ∃ coefficient : Nat,
      0 < coefficient ∧
        RegularIncidenceWitnessPointEstimate coefficient :=
  exists_regularIncidenceWitnessPointEstimate_of_raw
    (exists_rawIncidenceWitnessPointEstimate_of_generalHasseWeil
      hHasse)

end

end GenMarkoff.Symmetric.Cage
