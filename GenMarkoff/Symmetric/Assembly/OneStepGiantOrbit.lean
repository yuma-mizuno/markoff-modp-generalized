import GenMarkoff.Symmetric.Assembly.StartupRouting
import GenMarkoff.Symmetric.Assembly.RegularMiddleThenEndgame
import GenMarkoff.Symmetric.Assembly.GiantOrbitBasics
import GenMarkoff.Symmetric.Cage.BasePoint
import GenMarkoff.Symmetric.Cage.PairRelay
import GenMarkoff.Arithmetic.EventualAdmissibility

/-!
# Conditional giant orbit for the symmetric one-step action

This file assembles the actual startup routing, candidate-regular middle
game, split/nonsplit endgame, and connected regular split cage.  The three
specialized geometric estimates remain explicit hypotheses.  All other
steps, including finite bad-reduction removal and the complement count, are
internal Lean theorems.
-/

namespace GenMarkoff.Symmetric.Assembly

open BGS.Markoff Filter
open GenMarkoff.Symmetric.Cage

noncomputable section

/-- Membership in a punctured one-step orbit is exactly membership in the
corresponding component relation on the underlying solution surface. -/
theorem mem_puncturedOneStepOrbit_iff_sameOneStepComponent
    {R : Type*} [CommRing R] (c : R)
    (x y : PuncturedSolutionSurface (coefficients c)) :
    y ∈ puncturedOneStepOrbit x ↔
      SameOneStepComponent c x.1 y.1 := by
  constructor
  · intro hy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
    refine ⟨g, ?_⟩
    exact congrArg Subtype.val hg
  · rintro ⟨g, hg⟩
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact hg

private theorem rpow_lt_bufferedPowerBound
    (p : ℕ) (δ : ℝ) :
    (p : ℝ) ^ δ < (bufferedPowerBound p δ : ℝ) := by
  rw [bufferedPowerBound]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hceil :
      (p : ℝ) ^ δ ≤ (Nat.ceil ((p : ℝ) ^ δ) : ℝ) :=
    Nat.le_ceil ((p : ℝ) ^ δ)
  linarith

private theorem halfStepOrder_traceAt_le_maximal_of_candidateRegular
    {R : Type*} [Field R] (c : R) (x : Point R) (axis : Axis)
    (hregular :
      OrderedTraceCandidateRegular c c c (traceAt c axis x)) :
    halfStepOrder (traceAt c axis x) ≤
      maximalCandidateRegularHalfStepOrder c x := by
  cases axis with
  | first =>
      calc
        halfStepOrder (traceAt c .first x) =
            candidateRegularHalfStepOrder c (trace c x.x1) := by
          rw [candidateRegularHalfStepOrder_eq_halfStepOrder]
          · rfl
          · simpa [traceAt, coordinateAt] using hregular
        _ ≤ maximalCandidateRegularHalfStepOrder c x :=
          candidateRegularHalfStepOrder_first_le_maximal c x
  | second =>
      calc
        halfStepOrder (traceAt c .second x) =
            candidateRegularHalfStepOrder c (trace c x.x2) := by
          rw [candidateRegularHalfStepOrder_eq_halfStepOrder]
          · rfl
          · simpa [traceAt, coordinateAt] using hregular
        _ ≤ maximalCandidateRegularHalfStepOrder c x :=
          candidateRegularHalfStepOrder_second_le_maximal c x
  | third =>
      calc
        halfStepOrder (traceAt c .third x) =
            candidateRegularHalfStepOrder c (trace c x.x3) := by
          rw [candidateRegularHalfStepOrder_eq_halfStepOrder]
          · rfl
          · simpa [traceAt, coordinateAt] using hregular
        _ ≤ maximalCandidateRegularHalfStepOrder c x :=
          candidateRegularHalfStepOrder_third_le_maximal c x

/-- Conditional symmetric giant-orbit theorem from the three specialized
geometric estimates used by the endgame and cage. -/
theorem eventuallyHasGiantOneStepOrbit_of_specializedEstimates
    (splitCoefficient : ℕ)
    (hSplit : WeightedShiftedTraceWeilBoundAssumption splitCoefficient)
    (nonsplitCoefficient : ℕ)
    (hNonsplit :
      Endgame.Nonsplit.ShiftedSeededNonsplitTraceWeilBoundAssumption
        nonsplitCoefficient)
    (incidenceCoefficient : ℕ)
    (hIncidence :
      RegularIncidenceWitnessPointEstimate incidenceCoefficient)
    (c : ℤ)
    (hcIntegral : IntegrallyNondegenerate (coefficients c)) :
    EventuallyHasGiantOneStepOrbit c := by
  intro epsilon hepsilon
  let eta : ℝ := min (epsilon / 20) ((1 : ℝ) / 4)
  let delta : ℝ := eta / 3
  have hetaPositive : 0 < eta := by
    dsimp [eta]
    exact lt_min
      (div_pos hepsilon (by norm_num))
      (by norm_num)
  have hetaLeQuarter : eta ≤ (1 : ℝ) / 4 := by
    dsimp [eta]
    exact min_le_right _ _
  have hetaLtOne : eta < 1 :=
    hetaLeQuarter.trans_lt (by norm_num)
  have hdeltaPositive : 0 < delta := by
    dsimp [delta]
    positivity
  have htwoDelta : 2 * delta < eta := by
    dsimp [delta]
    linarith
  have hdeltaQuarter : delta ≤ (1 : ℝ) / 4 := by
    dsimp [delta]
    linarith
  have hetaLtEpsilonTenth : eta < epsilon / 10 := by
    have hetaLe : eta ≤ epsilon / 20 := by
      dsimp [eta]
      exact min_le_left _ _
    linarith
  obtain ⟨admissibilityThreshold, hAdmissibility⟩ :=
    hcIntegral.eventually_genericAdmissibleAt
  obtain ⟨startupThreshold, hStartup⟩ :=
    exists_threshold_smallFirstTwo_or_mem_centeredExceptional
      hdeltaPositive htwoDelta hetaLtOne
  obtain ⟨middleThreshold, hMiddle⟩ :=
    exists_threshold_regularMiddleGame_to_regularSplitCage
      splitCoefficient hSplit nonsplitCoefficient hNonsplit
        hdeltaPositive hdeltaQuarter
  obtain ⟨baseThreshold, hBase⟩ :=
    exists_threshold_puncturedPoint_in_regularSplitCage
  obtain ⟨cageThreshold, hCage⟩ :=
    exists_threshold_regularSplitCage_connected_via_relay
      incidenceCoefficient hIncidence
  obtain ⟨bufferThreshold, hBuffer⟩ :=
    eventually_atTop.mp
      (eventually_bufferedPowerBound_cast_le_rpow
        hetaPositive hetaLtEpsilonTenth)
  obtain ⟨smallThreshold, hSmall⟩ :=
    eventually_atTop.mp
      (eventually_smallOrderPointBound_add_three_le_rpow hepsilon)
  refine
    ⟨admissibilityThreshold + startupThreshold + middleThreshold +
      baseThreshold + cageThreshold + bufferThreshold + smallThreshold + 3, ?_⟩
  intro p hpPrime hpLarge
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hpAdmissibility : admissibilityThreshold ≤ p := by omega
  have hpStartup : startupThreshold ≤ p := by omega
  have hpMiddle : middleThreshold ≤ p := by omega
  have hpBase : baseThreshold ≤ p := by omega
  have hpCage : cageThreshold ≤ p := by omega
  have hpBuffer : bufferThreshold ≤ p := by omega
  have hpSmall : smallThreshold ≤ p := by omega
  have hGeneric :
      GenericAdmissible (coefficients (c : ZMod p)) := by
    have h :=
      hAdmissibility p hpPrime hpAdmissibility
    simpa [GenericAdmissibleAt] using h
  have hmultiplier : multiplier (c : ZMod p) ≠ 0 := by
    simpa only [multiplier_eq_coefficients_multiplier] using hGeneric.1
  have hcResidue : (c : ZMod p) ^ 2 ≠ 4 := by
    simpa using hGeneric.2.1
  obtain ⟨base, hbaseCage⟩ :=
    hBase p hpBase (c : ZMod p) hcResidue hmultiplier
  have hescape :
      ∀ y : SolutionSurface (coefficients (c : ZMod p)),
        HasRegularTraceOfOrderAtLeast p (c : ZMod p)
            (bufferedPowerBound p delta) y.1 →
          SameOneStepComponent (c : ZMod p) base.1 y := by
    intro y hyRegular
    obtain ⟨axis, hregular, horder⟩ := hyRegular
    have haxisLe :
        halfStepOrder (traceAt (c : ZMod p) axis y.1) ≤
          maximalCandidateRegularHalfStepOrder (c : ZMod p) y.1 :=
      halfStepOrder_traceAt_le_maximal_of_candidateRegular
        (c : ZMod p) y.1 axis hregular
    have hlarge :
        (p : ℝ) ^ delta <
          maximalCandidateRegularHalfStepOrder (c : ZMod p) y.1 := by
      have horderReal :
          (bufferedPowerBound p delta : ℝ) ≤
            (halfStepOrder (traceAt (c : ZMod p) axis y.1) : ℝ) := by
        exact_mod_cast horder
      have haxisLeReal :
          (halfStepOrder (traceAt (c : ZMod p) axis y.1) : ℝ) ≤
            (maximalCandidateRegularHalfStepOrder
              (c : ZMod p) y.1 : ℝ) := by
        exact_mod_cast haxisLe
      exact (rpow_lt_bufferedPowerBound p delta).trans_le
        (horderReal.trans haxisLeReal)
    obtain ⟨z, hyz, hzCage⟩ :=
      hMiddle p hpMiddle (c : ZMod p) y hcResidue hlarge
    have hbaseZ :
        SameOneStepComponent (c : ZMod p) base.1 z :=
      hCage p hpCage (c : ZMod p) hcResidue hmultiplier
        base.1 z hbaseCage hzCage
    exact sameOneStepComponent_trans hbaseZ
      (sameOneStepComponent_symm hyz)
  let bound : ℕ := bufferedPowerBound p eta
  let badPoints : Finset (Point (ZMod p)) :=
    pointsWithSmallFirstTwoHalfStepOrders p (c : ZMod p) bound ∪
      firstTwoCenteredExceptionalSet (c : ZMod p)
  let bad :
      Finset
        (PuncturedSolutionSurface (coefficients (c : ZMod p))) :=
    puncturedPointsIn badPoints
  have hcomplement :
      Set.univ \ puncturedOneStepOrbit base ⊆ (bad : Set _) := by
    intro x hx
    have hnotComponent :
        ¬ SameOneStepComponent (c : ZMod p) base.1 x.1 := by
      intro hcomponent
      apply hx.2
      exact
        (mem_puncturedOneStepOrbit_iff_sameOneStepComponent
          (c : ZMod p) base x).2 hcomponent
    have hclassification :=
      hStartup p hpStartup (c : ZMod p) hmultiplier hcResidue
        base.1 x hescape hnotComponent
    apply mem_puncturedPointsIn_iff.mpr
    rcases hclassification with hsmall | hexceptional
    · apply Finset.mem_union_left
      exact mem_pointsWithSmallFirstTwoHalfStepOrders_iff.mpr
        ⟨x.1.2, hsmall.1, hsmall.2⟩
    · exact Finset.mem_union_right _ hexceptional
  have hbadCard :
      bad.card ≤ 2 * (2 + 2 * bound ^ 2) ^ 2 + 3 := by
    calc
      bad.card ≤ badPoints.card := by
        exact puncturedPointsIn_card_le badPoints
      _ ≤
          (pointsWithSmallFirstTwoHalfStepOrders
              p (c : ZMod p) bound).card +
            (firstTwoCenteredExceptionalSet (c : ZMod p)).card :=
        Finset.card_union_le _ _
      _ ≤ 2 * (2 + 2 * bound ^ 2) ^ 2 + 2 := by
        exact Nat.add_le_add
          (pointsWithSmallFirstTwoHalfStepOrders_card_le
            p (by omega) (c : ZMod p) hmultiplier bound)
          (firstTwoCenteredExceptionalSet_card_le_two (c : ZMod p))
      _ ≤ 2 * (2 + 2 * bound ^ 2) ^ 2 + 3 := by omega
  have hbound :
      (bound : ℝ) ≤ (p : ℝ) ^ (epsilon / 10) := by
    simpa [bound] using hBuffer p hpBuffer
  have hpolynomial :
      ((2 * (2 + 2 * bound ^ 2) ^ 2 + 3 : ℕ) : ℝ) ≤
        (p : ℝ) ^ epsilon :=
    hSmall p hpSmall bound hbound
  have hbadReal : (bad.card : ℝ) ≤ (p : ℝ) ^ epsilon := by
    have hbadCast :
        (bad.card : ℝ) ≤
          ((2 * (2 + 2 * bound ^ 2) ^ 2 + 3 : ℕ) : ℝ) := by
      exact_mod_cast hbadCard
    exact hbadCast.trans hpolynomial
  exact hasGiantOneStepOrbitAt_of_complement_subset_finset
    c p hpPrime epsilon base bad hcomplement hbadReal

end

end GenMarkoff.Symmetric.Assembly
