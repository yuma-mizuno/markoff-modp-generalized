import GenMarkoff.General.Assembly.StartupRegularThreshold
import GenMarkoff.General.Assembly.RegularMiddleThreshold
import GenMarkoff.General.Assembly.RegularNonsplitEndgame

/-!
# Unified unequal-coefficient route to the canonical regular endgame

This file composes the proved fixed-coefficient stages, without adding a cage
connectivity claim:

1. the integral startup theorem produces an alternating regular state with
   actual order larger than `p ^ (1 / 32)`;
2. the regular middle iterator reaches actual order at least
   `p ^ (1 / 2 + 1 / 32)`;
3. the nonparabolic trace classification places the fixed trace in either the
   split torus or the quadratic norm-one torus;
4. the corresponding split- or nonsplit-source endgame reaches a canonical
   first-axis primitive split trace in the same rotation component.

## New composition considerations

* The middle-game quantity is the order of the **actual** rotation.  In both
  trace-classification branches it equals `orderOf(q ^ 2)`, rather than
  `orderOf q`.  The square-nontriviality proof returned by the dichotomy is
  retained explicitly in the two order bridges below.
* The startup theorem internally enforces good reduction, but its existential
  threshold does not expose that numerical lower bound.  The unified
  threshold therefore includes `genericAdmissibilityCutoff a` explicitly
  before extracting the two coefficient-square hypotheses needed downstream.
* The split and nonsplit affine estimates may be supplied with different
  constants.  Both assumptions are monotone in their coefficient, so the
  route uses their maximum only at the common endgame interface.
* The conclusion is componentwise: every punctured rotation component reaches
  a canonical first-axis primitive split point.  No assertion of cage
  connectivity, component uniqueness, or global transitivity is made.
-/

namespace GenMarkoff.General.Assembly

open BGS.Markoff
open GenMarkoff.General.Endgame
open GenMarkoff.General.MiddleGame
open GenMarkoff.Symmetric.Endgame.Nonsplit

noncomputable section

private theorem weightedShiftedTraceWeilBoundAssumption_mono
    {coefficient largerCoefficient : ℕ}
    (hle : coefficient ≤ largerCoefficient)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient) :
    WeightedShiftedTraceWeilBoundAssumption largerCoefficient := by
  refine ⟨hWeil.1.trans_le hle, ?_⟩
  intro K _ _ _ alpha beta gamma d e halpha hbeta hd he hirreducible
  exact
    (hWeil.2 K alpha beta gamma d e halpha hbeta hd he
      hirreducible).trans (by
        gcongr)

private theorem shiftedSeededNonsplitTraceWeilBoundAssumption_mono
    {coefficient largerCoefficient : ℕ}
    (hle : coefficient ≤ largerCoefficient)
    (hWeil :
      ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient) :
    ShiftedSeededNonsplitTraceWeilBoundAssumption largerCoefficient := by
  refine ⟨hWeil.1.trans_le hle, ?_⟩
  intro p _ hpTwo k hk s gamma d e hd he hirreducible
  exact
    (hWeil.2 p hpTwo k hk s gamma d e hd he hirreducible).trans (by
      gcongr)

/-- In the split branch of the nonparabolic trace dichotomy, the actual
rotation order carried by an alternating state is the order of the squared
split eigenvalue. -/
theorem alternatingActualOrder_eq_orderOf_sq_of_splitTrace
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (state : AlternatingRegularState a)
    (q : (ZMod p)ˣ)
    (htrace :
      traceAt a state.direction.fixed state.point.1 =
        splitTorusTrace q)
    (hq : (q : ZMod p) ^ 2 ≠ 1) :
    alternatingActualOrder state = orderOf (q ^ 2) := by
  change
    rotationLinearOrder
        (traceAt a state.direction.fixed state.point.1) =
      orderOf (q ^ 2)
  rw [Opening.rotationLinearOrder_eq_bgsRotationOrder_div_gcd,
    htrace, rotationOrder_splitTorusTrace q hq, orderOf_pow]

/-- In the nonsplit branch, the same actual-order quantity is the order of
the squared quadratic norm-one eigenvalue. -/
theorem alternatingActualOrder_eq_orderOf_sq_of_quadraticNormOneTrace
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (state : AlternatingRegularState a)
    (w : quadraticNormOneTorus p)
    (htrace :
      traceAt a state.direction.fixed state.point.1 =
        quadraticNormOneTrace p w)
    (hw :
      (((w : (quadraticFiniteField p)ˣ) :
          quadraticFiniteField p) ^ 2 ≠ 1)) :
    alternatingActualOrder state = orderOf (w ^ 2) := by
  change
    rotationLinearOrder
        (traceAt a state.direction.fixed state.point.1) =
      orderOf (w ^ 2)
  rw [Opening.rotationLinearOrder_eq_bgsRotationOrder_div_gcd,
    htrace, rotationOrder_quadraticNormOneTrace p w hw, orderOf_pow]

/-- Strongest assembled unequal-coefficient endpoint currently supported by
the proved stages.

For a fixed integrally nondegenerate coefficient triple, every punctured
rotation component modulo every sufficiently large prime reaches a
candidate-regular primitive split trace on the first axis.  The proof uses
startup exponent `1 / 32`, the regular middle threshold, and the exact
split/nonsplit eigenvalue dichotomy.  It does not identify distinct rotation
components or assert cage connectivity. -/
theorem
    IntegrallyNondegenerate.exists_threshold_every_puncturedRotationComponent_reaches_canonicalFirstAxisPrimitiveSplit
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (splitCoefficient : ℕ)
    (hSplit :
      WeightedShiftedTraceWeilBoundAssumption splitCoefficient)
    (nonsplitCoefficient : ℕ)
    (hNonsplit :
      ShiftedSeededNonsplitTraceWeilBoundAssumption
        nonsplitCoefficient) :
    ∃ threshold : ℕ,
      ∀ (p : ℕ) (hp : p.Prime), threshold ≤ p →
        letI : Fact p.Prime := ⟨hp⟩
        ∀ x : PuncturedSolutionSurface (modCoefficients a p),
          ∃ finish : SolutionSurface (modCoefficients a p),
            SameRotationComponent x.1 finish ∧
              IsCanonicalFirstAxisPrimitiveSplit
                p (modCoefficients a p) finish := by
  let commonCoefficient := max splitCoefficient nonsplitCoefficient
  have hSplitCommon :
      WeightedShiftedTraceWeilBoundAssumption commonCoefficient :=
    weightedShiftedTraceWeilBoundAssumption_mono
      (Nat.le_max_left splitCoefficient nonsplitCoefficient) hSplit
  have hNonsplitCommon :
      ShiftedSeededNonsplitTraceWeilBoundAssumption commonCoefficient :=
    shiftedSeededNonsplitTraceWeilBoundAssumption_mono
      (Nat.le_max_right splitCoefficient nonsplitCoefficient) hNonsplit
  obtain ⟨startupThreshold, hstartup⟩ :=
    GenMarkoff.General.Assembly.IntegrallyNondegenerate.exists_threshold_every_rotationOrbit_has_powerLowerBound_alternatingRegularState
      ha
  obtain ⟨splitThreshold, hsplit⟩ :=
    exists_threshold_alternatingRegularState_reaches_canonicalFirstAxisPrimitiveSplit
      commonCoefficient hSplitCommon startupRegularExponent_pos
  obtain ⟨nonsplitThreshold, hnonsplit⟩ :=
    exists_threshold_alternatingRegularNonsplitState_reaches_canonicalFirstAxisPrimitiveSplit
      commonCoefficient hNonsplitCommon hSplitCommon
        startupRegularExponent_pos
  let threshold :=
    max startupThreshold
      (max GenMarkoff.General.Explicit.analyticCutoff
        (max splitThreshold
          (max nonsplitThreshold
            (max (genericAdmissibilityCutoff a) 3))))
  refine ⟨threshold, ?_⟩
  intro p hp hpLarge
  letI : Fact p.Prime := ⟨hp⟩
  intro x
  have hpBounds :
      startupThreshold ≤ p ∧
        GenMarkoff.General.Explicit.analyticCutoff ≤ p ∧
          splitThreshold ≤ p ∧
            nonsplitThreshold ≤ p ∧
              genericAdmissibilityCutoff a ≤ p ∧ 3 ≤ p := by
    simpa only [threshold, max_le_iff] using hpLarge
  have hpTwo : p ≠ 2 := by omega
  have hgeneric : GenericAdmissibleAt a p :=
    ha.genericAdmissibleAt_of_cutoff_le hpBounds.2.2.2.2.1
  have hA1 : (modCoefficients a p).a1 ^ 2 ≠ 4 :=
    hgeneric.2.1
  have hA2 : (modCoefficients a p).a2 ^ 2 ≠ 4 :=
    hgeneric.2.2.1
  obtain ⟨start, hxStart, hstartOrder⟩ :=
    hstartup p hp hpBounds.1 x
  obtain ⟨middle, hstartMiddle, hmiddleOrder⟩ :=
    alternatingRegularMiddleGame_reaches_endgame_of_analyticCutoff
      hpBounds.2.1
        (modCoefficients a p) hA1 hA2 start
        (by
          simpa [startupRegularExponent] using hstartOrder)
  let t :=
    traceAt (modCoefficients a p)
      middle.direction.fixed middle.point.1
  have hD : discriminant t ≠ 0 := by
    cases hdirection : middle.direction with
    | firstSecond =>
        have hregular :
            OrderedTraceCandidateRegular
              (modCoefficients a p).a1
              (modCoefficients a p).a2
              (modCoefficients a p).a3
              (traceAt (modCoefficients a p) .first middle.point.1) := by
          simpa [alternatingTraceRegular, hdirection] using
            middle.regular
        simpa [t, hdirection, AlternatingDirectedAxis.fixed,
          discriminant] using hregular.1
    | secondFirst =>
        have hregular :
            OrderedTraceCandidateRegular
              (modCoefficients a p).a2
              (modCoefficients a p).a1
              (modCoefficients a p).a3
              (traceAt (modCoefficients a p) .second middle.point.1) := by
          simpa [alternatingTraceRegular, hdirection] using
            middle.regular
        simpa [t, hdirection, AlternatingDirectedAxis.fixed,
          discriminant] using hregular.1
  have ht : t ^ 2 ≠ 4 :=
    sub_ne_zero.mp (by simpa [discriminant] using hD)
  rcases exists_split_or_quadraticNormOneTrace p hpTwo t ht with
      ⟨q, htraceQ, hq⟩ | ⟨w, htraceW, hw⟩
  · have hmiddleTrace :
        traceAt (modCoefficients a p)
            middle.direction.fixed middle.point.1 =
          splitTorusTrace q := by
      simpa [t] using htraceQ.symm
    have hlargeQ :
        (p : ℝ) ^
            ((1 : ℝ) / 2 + startupRegularExponent) ≤
          orderOf (q ^ 2) := by
      calc
        (p : ℝ) ^
              ((1 : ℝ) / 2 + startupRegularExponent) ≤
            alternatingActualOrder middle :=
          by
            convert hmiddleOrder using 1 ;
              norm_num [startupRegularExponent]
        _ = orderOf (q ^ 2) :=
          by
            exact_mod_cast
              alternatingActualOrder_eq_orderOf_sq_of_splitTrace
                p (modCoefficients a p) middle q hmiddleTrace hq
    obtain ⟨finish, hmiddleFinish, hcanonical⟩ :=
      hsplit p hpBounds.2.2.1
        (modCoefficients a p) hA1 hA2 middle q
          hmiddleTrace hlargeQ
    exact
      ⟨finish,
        sameRotationComponent_trans hxStart
          (sameRotationComponent_trans hstartMiddle hmiddleFinish),
        hcanonical⟩
  · have hmiddleTrace :
        traceAt (modCoefficients a p)
            middle.direction.fixed middle.point.1 =
          quadraticNormOneTrace p w := by
      simpa [t] using htraceW.symm
    have hlargeW :
        (p : ℝ) ^
            ((1 : ℝ) / 2 + startupRegularExponent) ≤
          orderOf (w ^ 2) := by
      calc
        (p : ℝ) ^
              ((1 : ℝ) / 2 + startupRegularExponent) ≤
            alternatingActualOrder middle :=
          by
            convert hmiddleOrder using 1 ;
              norm_num [startupRegularExponent]
        _ = orderOf (w ^ 2) :=
          by
            exact_mod_cast
              alternatingActualOrder_eq_orderOf_sq_of_quadraticNormOneTrace
                p (modCoefficients a p) middle w hmiddleTrace hw
    obtain ⟨finish, hmiddleFinish, hcanonical⟩ :=
      hnonsplit p hpBounds.2.2.2.1
        (modCoefficients a p) hA1 hA2 middle w
          hmiddleTrace hlargeW
    exact
      ⟨finish,
        sameRotationComponent_trans hxStart
          (sameRotationComponent_trans hstartMiddle hmiddleFinish),
        hcanonical⟩

/-- Explicit startup--middle--endgame route.  The universal analytic cutoff
is independent of the coefficient triple; the second cutoff is exactly the
finite bad-reduction height of the fixed triple. -/
theorem
    IntegrallyNondegenerate.every_puncturedRotationComponent_reaches_canonicalFirstAxisPrimitiveSplit_of_explicitCutoffs
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (p : ℕ) (hp : p.Prime)
    (hpAnalytic : GenMarkoff.General.Explicit.analyticCutoff ≤ p)
    (hpGeneric : genericAdmissibilityCutoff a ≤ p)
    (x : PuncturedSolutionSurface (modCoefficients a p)) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ finish : SolutionSurface (modCoefficients a p),
      SameRotationComponent x.1 finish ∧
        IsCanonicalFirstAxisPrimitiveSplit
          p (modCoefficients a p) finish := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpTwo : p ≠ 2 := by
    have hpFive :=
      GenMarkoff.General.Explicit.five_le_analyticCutoff.trans hpAnalytic
    omega
  have hgeneric : GenericAdmissibleAt a p :=
    ha.genericAdmissibleAt_of_cutoff_le hpGeneric
  have hA1 : (modCoefficients a p).a1 ^ 2 ≠ 4 :=
    hgeneric.2.1
  have hA2 : (modCoefficients a p).a2 ^ 2 ≠ 4 :=
    hgeneric.2.2.1
  have hSplit34 :
      WeightedShiftedTraceWeilBoundAssumption 34 :=
    weightedShiftedTraceWeilBoundAssumption_mono
      (show 33 ≤ 34 by norm_num)
        GenMarkoff.weightedShiftedTraceWeilBoundAssumption_thirtyThree
  have hNonsplit34 :
      ShiftedSeededNonsplitTraceWeilBoundAssumption 34 :=
    GenMarkoff.Symmetric.Endgame.Nonsplit.shiftedSeededNonsplitTraceWeilBoundAssumption_thirtyFour
  obtain ⟨start, hxStart, hstartOrder⟩ :=
    IntegrallyNondegenerate.every_rotationOrbit_has_powerLowerBound_alternatingRegularState_of_explicitCutoffs
      ha p hp hpAnalytic hpGeneric x
  obtain ⟨middle, hstartMiddle, hmiddleOrder⟩ :=
    alternatingRegularMiddleGame_reaches_endgame_of_analyticCutoff
      hpAnalytic (modCoefficients a p) hA1 hA2 start
        (by simpa [startupRegularExponent] using hstartOrder)
  let t :=
    traceAt (modCoefficients a p)
      middle.direction.fixed middle.point.1
  have hD : discriminant t ≠ 0 := by
    cases hdirection : middle.direction with
    | firstSecond =>
        have hregular :
            OrderedTraceCandidateRegular
              (modCoefficients a p).a1
              (modCoefficients a p).a2
              (modCoefficients a p).a3
              (traceAt (modCoefficients a p) .first middle.point.1) := by
          simpa [alternatingTraceRegular, hdirection] using
            middle.regular
        simpa [t, hdirection, AlternatingDirectedAxis.fixed,
          discriminant] using hregular.1
    | secondFirst =>
        have hregular :
            OrderedTraceCandidateRegular
              (modCoefficients a p).a2
              (modCoefficients a p).a1
              (modCoefficients a p).a3
              (traceAt (modCoefficients a p) .second middle.point.1) := by
          simpa [alternatingTraceRegular, hdirection] using
            middle.regular
        simpa [t, hdirection, AlternatingDirectedAxis.fixed,
          discriminant] using hregular.1
  have ht : t ^ 2 ≠ 4 :=
    sub_ne_zero.mp (by simpa [discriminant] using hD)
  rcases exists_split_or_quadraticNormOneTrace p hpTwo t ht with
      ⟨q, htraceQ, hq⟩ | ⟨w, htraceW, hw⟩
  · have hmiddleTrace :
        traceAt (modCoefficients a p)
            middle.direction.fixed middle.point.1 =
          splitTorusTrace q := by
      simpa [t] using htraceQ.symm
    have hlargeQ :
        (p : ℝ) ^
            ((1 : ℝ) / 2 + startupRegularExponent) ≤
          orderOf (q ^ 2) := by
      calc
        (p : ℝ) ^
              ((1 : ℝ) / 2 + startupRegularExponent) ≤
            alternatingActualOrder middle := by
          convert hmiddleOrder using 1 ;
            norm_num [startupRegularExponent]
        _ = orderOf (q ^ 2) := by
          exact_mod_cast
            alternatingActualOrder_eq_orderOf_sq_of_splitTrace
              p (modCoefficients a p) middle q hmiddleTrace hq
    obtain ⟨finish, hmiddleFinish, hcanonical⟩ :=
      alternatingRegularState_reaches_canonicalFirstAxisPrimitiveSplit_of_analyticCutoff
        34 hSplit34 (delta := startupRegularExponent)
          (by norm_num [startupRegularExponent]) (by norm_num)
          p hpAnalytic (modCoefficients a p) hA1 hA2 middle q
          hmiddleTrace hlargeQ
    exact
      ⟨finish,
        sameRotationComponent_trans hxStart
          (sameRotationComponent_trans hstartMiddle hmiddleFinish),
        hcanonical⟩
  · have hmiddleTrace :
        traceAt (modCoefficients a p)
            middle.direction.fixed middle.point.1 =
          quadraticNormOneTrace p w := by
      simpa [t] using htraceW.symm
    have hlargeW :
        (p : ℝ) ^
            ((1 : ℝ) / 2 + startupRegularExponent) ≤
          orderOf (w ^ 2) := by
      calc
        (p : ℝ) ^
              ((1 : ℝ) / 2 + startupRegularExponent) ≤
            alternatingActualOrder middle := by
          convert hmiddleOrder using 1 ;
            norm_num [startupRegularExponent]
        _ = orderOf (w ^ 2) := by
          exact_mod_cast
            alternatingActualOrder_eq_orderOf_sq_of_quadraticNormOneTrace
              p (modCoefficients a p) middle w hmiddleTrace hw
    obtain ⟨finish, hmiddleFinish, hcanonical⟩ :=
      alternatingRegularNonsplitState_reaches_canonicalFirstAxisPrimitiveSplit_of_analyticCutoff
        34 hNonsplit34 hSplit34 (delta := startupRegularExponent)
          (by norm_num [startupRegularExponent]) (by norm_num)
          p hpAnalytic (modCoefficients a p) hA1 hA2 middle w
          hmiddleTrace hlargeW
    exact
      ⟨finish,
        sameRotationComponent_trans hxStart
          (sameRotationComponent_trans hstartMiddle hmiddleFinish),
        hcanonical⟩

/-- Unconditional componentwise startup--middle--endgame route.  The two
uniform Weil constants are supplied by the in-repository general affine
Hasse--Weil theorem.  The conclusion remains deliberately componentwise:
the parity-aware cage needed to identify distinct rotation components is a
separate theorem. -/
theorem
    IntegrallyNondegenerate.exists_threshold_every_puncturedRotationComponent_reaches_canonicalFirstAxisPrimitiveSplit_of_generalHasseWeil
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a) :
    ∃ threshold : ℕ,
      ∀ (p : ℕ) (hp : p.Prime), threshold ≤ p →
        letI : Fact p.Prime := ⟨hp⟩
        ∀ x : PuncturedSolutionSurface (modCoefficients a p),
          ∃ finish : SolutionSurface (modCoefficients a p),
            SameRotationComponent x.1 finish ∧
              IsCanonicalFirstAxisPrimitiveSplit
                p (modCoefficients a p) finish := by
  obtain ⟨splitCoefficient, hSplit⟩ :=
    GenMarkoff.exists_weightedShiftedTraceWeilBoundAssumption
  obtain ⟨nonsplitCoefficient, hNonsplit⟩ :=
    GenMarkoff.Symmetric.Endgame.Nonsplit.exists_shiftedSeededNonsplitTraceWeilBoundAssumption
  exact
    GenMarkoff.General.Assembly.IntegrallyNondegenerate.exists_threshold_every_puncturedRotationComponent_reaches_canonicalFirstAxisPrimitiveSplit
      ha
      splitCoefficient hSplit nonsplitCoefficient hNonsplit

end

end GenMarkoff.General.Assembly
