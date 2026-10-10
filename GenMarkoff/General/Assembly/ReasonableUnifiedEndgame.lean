import GenMarkoff.General.Assembly.CoarseRegularMiddle
import GenMarkoff.General.Assembly.UnifiedRegularEndgame

/-!
# Every rotation component reaches a canonical split point

For an integrally nondegenerate coefficient triple `a` and a prime `p` beyond
`reasonableAnalyticCutoff` and `genericAdmissibilityCutoff a`, every punctured
rotation component modulo `p` contains a canonical first-axis primitive split
point (`IsCanonicalFirstAxisPrimitiveSplit`).  Writing
`T = #divisors (p - 1) + #divisors (p + 1)`, the route is:

1. generic Martin divisibility makes every punctured rotation orbit
   `p`-divisible, so the coarse startup
   (`exists_sameRotationComponent_coarseRegularState_of_dvd`) gives an
   alternating candidate-regular state of actual order above `(192 T)^3`;
2. the regular middle game raises the actual order to at least `p ^ (3/4)`;
3. the trace of the resulting state is split or comes from the quadratic
   norm-one torus, and the split or nonsplit endgame finishes, using the
   Hasse–Weil point-count estimates with coefficient `34`.
-/

namespace GenMarkoff.General.Assembly

open BGS.Markoff
open GenMarkoff.General.Endgame
open GenMarkoff.ShiftedTrace.Endgame.Nonsplit

noncomputable section

/-- The split Hasse–Weil assumption is monotone in its coefficient. -/
private theorem weightedShiftedTraceWeilBoundAssumption_mono_reasonable
    {coefficient largerCoefficient : ℕ}
    (hle : coefficient ≤ largerCoefficient)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient) :
    WeightedShiftedTraceWeilBoundAssumption largerCoefficient := by
  refine ⟨hWeil.1.trans_le hle, ?_⟩
  intro K _ _ _ alpha beta gamma d e halpha hbeta hd he hirreducible
  exact
    (hWeil.2 K alpha beta gamma d e halpha hbeta hd he
      hirreducible).trans (by gcongr)

/-- Beyond `reasonableAnalyticCutoff` and `genericAdmissibilityCutoff a`,
every punctured rotation component for an integrally nondegenerate
coefficient triple contains a canonical first-axis primitive split point. -/
theorem
    _root_.GenMarkoff.IntegrallyNondegenerate.every_puncturedRotationComponent_reaches_canonicalFirstAxisPrimitiveSplit_of_reasonableCutoff
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (p : ℕ) (hp : p.Prime)
    (hpReasonable :
      GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    (hpGeneric : genericAdmissibilityCutoff a ≤ p)
    (x : PuncturedSolutionSurface (modCoefficients a p)) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ finish : SolutionSurface (modCoefficients a p),
      SameRotationComponent x.1 finish ∧
        IsCanonicalFirstAxisPrimitiveSplit
          p (modCoefficients a p) finish := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (quadraticFiniteField p) := Fintype.ofFinite _
  have hpFive : 5 ≤ p :=
    GenMarkoff.General.Explicit.five_le_reasonableAnalyticCutoff.trans
      hpReasonable
  have hpTwo : p ≠ 2 := by omega
  have hgeneric : GenericAdmissibleAt a p :=
    ha.genericAdmissibleAt_of_cutoff_le hpGeneric
  have hA1 : (modCoefficients a p).a1 ^ 2 ≠ 4 :=
    hgeneric.2.1
  have hA2 : (modCoefficients a p).a2 ^ 2 ≠ 4 :=
    hgeneric.2.2.1
  have hSplit34 :
      WeightedShiftedTraceWeilBoundAssumption 34 :=
    weightedShiftedTraceWeilBoundAssumption_mono_reasonable
      (show 33 ≤ 34 by norm_num)
        GenMarkoff.weightedShiftedTraceWeilBoundAssumption_thirtyThree
  have hNonsplit34 :
      ShiftedSeededNonsplitTraceWeilBoundAssumption 34 :=
    GenMarkoff.ShiftedTrace.Endgame.Nonsplit.shiftedSeededNonsplitTraceWeilBoundAssumption_thirtyFour
  -- Startup: `p`-divisibility of the rotation orbit gives a coarse regular
  -- state; the middle game then reaches actual order `p ^ (3/4)`.
  have hVieta : VietaOrbitDivisibilityAt a p hp := by
    apply generalizedMartinGenericDivisibility
    · exact hpFive
    · exact hgeneric
  have hRotation : RotationOrbitDivisibilityAt a p hp :=
    rotationOrbitDivisibility_of_vietaOrbitDivisibility
      p hp hpFive (modCoefficients a p) hVieta
  obtain ⟨start, hxStart, hstartOrder⟩ :=
    exists_sameRotationComponent_coarseRegularState_of_dvd
      p hpTwo hpReasonable (modCoefficients a p) hgeneric.1
        hA1 hA2 x (hRotation x)
  obtain ⟨middle, hstartMiddle, hmiddleOrder⟩ :=
    alternatingRegularMiddleGame_reaches_threeQuarter_of_reasonableCutoff
      hpReasonable (modCoefficients a p) hA1 hA2 start hstartOrder
  -- Endgame: the fixed trace is nonparabolic, hence split or nonsplit.
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
          simpa [alternatingTraceRegular, hdirection] using middle.regular
        simpa [t, hdirection, AlternatingDirectedAxis.fixed,
          discriminant] using hregular.1
    | secondFirst =>
        have hregular :
            OrderedTraceCandidateRegular
              (modCoefficients a p).a2
              (modCoefficients a p).a1
              (modCoefficients a p).a3
              (traceAt (modCoefficients a p) .second middle.point.1) := by
          simpa [alternatingTraceRegular, hdirection] using middle.regular
        simpa [t, hdirection, AlternatingDirectedAxis.fixed,
          discriminant] using hregular.1
  have ht : t ^ 2 ≠ 4 :=
    sub_ne_zero.mp (by simpa [discriminant] using hD)
  rcases exists_split_or_quadraticNormOneTrace p hpTwo t ht with
      ⟨q, htraceQ, hq⟩ | ⟨w, htraceW, hw⟩
  -- Split trace `q + q⁻¹`.
  · have hmiddleTrace :
        traceAt (modCoefficients a p)
            middle.direction.fixed middle.point.1 =
          splitTorusTrace q := by
      simpa [t] using htraceQ.symm
    have hlargeQ :
        (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
          orderOf (q ^ 2) := by
      calc
        (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
            alternatingActualOrder middle := by
          convert hmiddleOrder using 1 ; norm_num
        _ = orderOf (q ^ 2) := by
          exact_mod_cast
            alternatingActualOrder_eq_orderOf_sq_of_splitTrace
              p (modCoefficients a p) middle q hmiddleTrace hq
    obtain ⟨finish, hmiddleFinish, hcanonical⟩ :=
      alternatingRegularState_reaches_canonicalFirstAxisPrimitiveSplit_of_reasonableCutoff
        34 hSplit34 (delta := (1 : ℝ) / 4) (by norm_num)
          (by norm_num) p hpReasonable (modCoefficients a p)
          hA1 hA2 middle q hmiddleTrace hlargeQ
    exact
      ⟨finish,
        sameRotationComponent_trans hxStart
          (sameRotationComponent_trans hstartMiddle hmiddleFinish),
        hcanonical⟩
  -- Nonsplit trace from the quadratic norm-one torus.
  · have hmiddleTrace :
        traceAt (modCoefficients a p)
            middle.direction.fixed middle.point.1 =
          quadraticNormOneTrace p w := by
      simpa [t] using htraceW.symm
    have hlargeW :
        (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
          orderOf (w ^ 2) := by
      calc
        (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
            alternatingActualOrder middle := by
          convert hmiddleOrder using 1 ; norm_num
        _ = orderOf (w ^ 2) := by
          exact_mod_cast
            alternatingActualOrder_eq_orderOf_sq_of_quadraticNormOneTrace
              p (modCoefficients a p) middle w hmiddleTrace hw
    obtain ⟨finish, hmiddleFinish, hcanonical⟩ :=
      alternatingRegularNonsplitState_reaches_canonicalFirstAxisPrimitiveSplit_of_reasonableCutoff
        34 hNonsplit34 hSplit34 (delta := (1 : ℝ) / 4)
          (by norm_num) (by norm_num) p hpReasonable
          (modCoefficients a p) hA1 hA2 middle w hmiddleTrace hlargeW
    exact
      ⟨finish,
        sameRotationComponent_trans hxStart
          (sameRotationComponent_trans hstartMiddle hmiddleFinish),
        hcanonical⟩

end

end GenMarkoff.General.Assembly
