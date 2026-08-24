import BGS.HasseWeil.GeneralBivariateAffineHasseWeil
import GenMarkoff.Symmetric.Assembly.OneStepGiantOrbit
import GenMarkoff.Symmetric.Cage.RawEstimateFromPlane
import GenMarkoff.TraceCurve.WeightedShiftedCoverCounting
import GenMarkoff.Symmetric.Endgame.Nonsplit.ShiftedHasseFromGeneral
import GenMarkoff.General.Assembly.StrongApproximation
import GenMarkoff.Symmetric.Statements

/-!
# Strong approximation for the symmetric one-step action

This module first exposes the specialized geometric inputs of the symmetric
one-step argument and then discharges all three from the in-repository general
affine Hasse--Weil theorem.
-/

namespace GenMarkoff.Symmetric.Assembly

/-- Existential split, nonsplit, and incidence estimates imply the symmetric
one-step giant-orbit statement.  The integral coefficient hypotheses are
converted to `IntegrallyNondegenerate` before invoking the assembled
prime-by-prime theorem. -/
theorem oneStepGiantOrbitStatement_of_specializedEstimates
    (hSplit :
      ∃ coefficient : ℕ,
        GenMarkoff.WeightedShiftedTraceWeilBoundAssumption coefficient)
    (hNonsplit :
      ∃ coefficient : ℕ,
        Endgame.Nonsplit.ShiftedSeededNonsplitTraceWeilBoundAssumption
          coefficient)
    (hIncidence :
      ∃ coefficient : ℕ,
        Cage.RegularIncidenceWitnessPointEstimate coefficient) :
    OneStepGiantOrbitStatement := by
  obtain ⟨splitCoefficient, hSplit⟩ := hSplit
  obtain ⟨nonsplitCoefficient, hNonsplit⟩ := hNonsplit
  obtain ⟨incidenceCoefficient, hIncidence⟩ := hIncidence
  intro c hs hc
  have hcIntegral : IntegrallyNondegenerate (coefficients c) :=
    (integrallyNondegenerate_coefficients_iff c).2 ⟨hs, hc⟩
  exact eventuallyHasGiantOneStepOrbit_of_specializedEstimates
    splitCoefficient hSplit nonsplitCoefficient hNonsplit
      incidenceCoefficient hIncidence c hcIntegral

/-- The same three specialized estimates imply the public eventual
one-step strong-approximation statement via the existing giant-orbit and
rotation-divisibility bridge. -/
theorem eventualOneStepStrongApproximationStatement_of_specializedEstimates
    (hSplit :
      ∃ coefficient : ℕ,
        GenMarkoff.WeightedShiftedTraceWeilBoundAssumption coefficient)
    (hNonsplit :
      ∃ coefficient : ℕ,
        Endgame.Nonsplit.ShiftedSeededNonsplitTraceWeilBoundAssumption
          coefficient)
    (hIncidence :
      ∃ coefficient : ℕ,
        Cage.RegularIncidenceWitnessPointEstimate coefficient) :
    EventualOneStepStrongApproximationStatement := by
  apply
    GenMarkoff.Symmetric.eventualOneStepStrongApproximationStatement_of_giantOrbit
  exact oneStepGiantOrbitStatement_of_specializedEstimates
    hSplit hNonsplit hIncidence

/-- General affine Hasse--Weil supplies both shifted trace-cover estimates;
an existential regular-incidence estimate is the remaining input for the
giant-orbit statement. -/
theorem oneStepGiantOrbitStatement_of_generalHasseWeil_and_incidenceEstimate
    (hHasse : BGS.External.GeneralBivariateAffineHasseWeilTheorem)
    (hIncidence :
      ∃ coefficient : ℕ,
        Cage.RegularIncidenceWitnessPointEstimate coefficient) :
    OneStepGiantOrbitStatement := by
  apply oneStepGiantOrbitStatement_of_specializedEstimates
  · exact
      GenMarkoff.exists_weightedShiftedTraceWeilBoundAssumption_of_generalHasseWeil
        hHasse
  · exact
      Endgame.Nonsplit.exists_shiftedSeededNonsplitTraceWeilBoundAssumption_of_generalHasseWeil
        hHasse
  · exact hIncidence

/-- General affine Hasse--Weil together with the remaining regular-incidence
estimate implies eventual one-step strong approximation. -/
theorem eventualOneStepStrongApproximationStatement_of_generalHasseWeil_and_incidenceEstimate
    (hHasse : BGS.External.GeneralBivariateAffineHasseWeilTheorem)
    (hIncidence :
      ∃ coefficient : ℕ,
        Cage.RegularIncidenceWitnessPointEstimate coefficient) :
    EventualOneStepStrongApproximationStatement := by
  apply
    GenMarkoff.Symmetric.eventualOneStepStrongApproximationStatement_of_giantOrbit
  exact oneStepGiantOrbitStatement_of_generalHasseWeil_and_incidenceEstimate
    hHasse hIncidence

/-- General affine Hasse--Weil supplies the split, nonsplit, and incidence
estimates, and hence the symmetric one-step giant-orbit statement. -/
theorem oneStepGiantOrbitStatement_of_generalHasseWeil
    (hHasse : BGS.External.GeneralBivariateAffineHasseWeilTheorem) :
    OneStepGiantOrbitStatement := by
  apply oneStepGiantOrbitStatement_of_generalHasseWeil_and_incidenceEstimate
    hHasse
  obtain ⟨coefficient, _, hIncidence⟩ :=
    Cage.exists_regularIncidenceWitnessPointEstimate_of_generalHasseWeil
      hHasse
  exact ⟨coefficient, hIncidence⟩

/-- General affine Hasse--Weil implies eventual one-step strong approximation
for every admissible integral coefficient in the symmetric family. -/
theorem eventualOneStepStrongApproximationStatement_of_generalHasseWeil
    (hHasse : BGS.External.GeneralBivariateAffineHasseWeilTheorem) :
    EventualOneStepStrongApproximationStatement :=
  GenMarkoff.Symmetric.eventualOneStepStrongApproximationStatement_of_giantOrbit
    (oneStepGiantOrbitStatement_of_generalHasseWeil hHasse)

/-- Unconditional symmetric one-step giant-orbit theorem, using the pinned
in-repository general affine Hasse--Weil theorem. -/
theorem oneStepGiantOrbitStatement :
    OneStepGiantOrbitStatement :=
  oneStepGiantOrbitStatement_of_generalHasseWeil
    BGS.HasseWeil.generalBivariateAffineHasseWeilTheorem

/-- For every integral `c` with `3 * (1 + c) ≠ 0` and `c ^ 2 ≠ 4`, the
symmetric one-step group is transitive on the punctured surface modulo every
sufficiently large prime. -/
theorem eventualOneStepStrongApproximationStatement :
    EventualOneStepStrongApproximationStatement :=
  eventualOneStepStrongApproximationStatement_of_generalHasseWeil
    BGS.HasseWeil.generalBivariateAffineHasseWeilTheorem

/-- The rotation-group giant-orbit statement for the symmetric family follows
from the completed general rotation-transitivity theorem.  This does not use
the optional direct parity-aware symmetric rotation cage. -/
theorem giantOrbitStatement :
    GiantOrbitStatement := by
  intro c hs hc
  exact
    GenMarkoff.General.Assembly.generalizedGiantOrbitStatement
      (coefficients c)
      ((integrallyNondegenerate_coefficients_iff c).2 ⟨hs, hc⟩)

end GenMarkoff.Symmetric.Assembly
