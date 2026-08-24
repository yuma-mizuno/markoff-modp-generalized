import GenMarkoff.Symmetric.Cage.AxisBridge
import GenMarkoff.Symmetric.Cage.IncidenceGeometry
import BGS.NumberTheory.OneSidedPrimitiveWitness

/-!
# Hasse--Weil-ready common-neighbor endpoint

The geometric object counted here is the explicit pair of discriminant
square roots from `IncidenceGeometry`.  Candidate-irregular middle traces
are removed in the witness type, so the resulting primitive middle unit is
immediately a regular split-maximal fiber and can be used with the actual
one-step transitivity theorem.

The sole remaining geometric hypothesis is
`RegularIncidenceWitnessPointEstimate`.  Its domain explicitly separates the
diagonal case from the off-diagonal resultant condition; no global cage
connectivity is hidden in that assumption.
-/

namespace GenMarkoff.Symmetric.Cage

open Filter
open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

/-- Incidence witnesses whose common middle trace remains candidate regular. -/
def RegularIncidenceEquationWitness
    (p : ℕ) [Fact p.Prime] (c xi eta : ZMod p) :=
  {w : IncidenceEquationWitness c xi eta //
    OrderedTraceCandidateRegular c c c w.middle}

/-- The common trace carried by a regular incidence witness. -/
def regularIncidenceWitnessTrace
    {p : ℕ} [Fact p.Prime] {c xi eta : ZMod p}
    (w : RegularIncidenceEquationWitness p c xi eta) : ZMod p :=
  w.1.middle

/-- Witness-bearing solutions with the middle unit restricted to a power-map
range. -/
abbrev regularIncidenceWitnessPowerRangeSolutions
    (p : ℕ) [Fact p.Prime] (c xi eta : ZMod p) (d : ℕ) :=
  BGS.rightPowerTraceRangeSolutions
    (regularIncidenceWitnessTrace
      (p := p) (c := c) (xi := xi) (eta := eta))
    (BGS.Markoff.splitTorusTrace : (ZMod p)ˣ → ZMod p) d

/-- The diagonal is handled separately; off the diagonal the explicit
resultant obstruction must be nonzero. -/
def IsAdmissibleIncidencePair
    {K : Type*} [Field K] (c xi eta : K) : Prop :=
  xi = eta ∨ IsHasseWeilReadyIncidencePair c xi eta

/-- Exact point-count interface still required from the generalized cage
geometry.  The multiplicity is exposed because the diagonal main term need
not be one. -/
def RegularIncidenceWitnessPointEstimate (coefficient : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
    ∀ (c xi eta : ZMod p),
      c ^ 2 ≠ 4 →
      IsRegularSplitMaximalTrace p c xi →
      IsRegularSplitMaximalTrace p c eta →
      IsAdmissibleIncidencePair c xi eta →
      ∃ multiplicity : ℕ, 0 < multiplicity ∧
        ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
          |(Nat.card (regularIncidenceWitnessPowerRangeSolutions
              p c xi eta d) : ℝ) -
                (multiplicity : ℝ) * (p : ℝ) / d| ≤
            (coefficient : ℝ) * Real.sqrt (p : ℝ)

/-- A regular incidence witness pulls back to a pair of actual symmetric
surface points sharing its middle affine trace. -/
structure ActualIncidenceBridge
    (p : ℕ) [Fact p.Prime] (c xi eta middle : ZMod p) where
  firstPoint : SolutionSurface (coefficients c)
  secondPoint : SolutionSurface (coefficients c)
  firstOuterTrace : trace c firstPoint.1.x1 = xi
  secondOuterTrace : trace c secondPoint.1.x1 = eta
  firstMiddleTrace : trace c firstPoint.1.x2 = middle
  secondMiddleTrace : trace c secondPoint.1.x2 = middle

/-- The inverse trace map turns the two square-root equations into an actual
common-neighbor bridge. -/
def actualIncidenceBridgeOfWitness
    (p : ℕ) [Fact p.Prime] (c xi eta : ZMod p)
    (hmultiplier : multiplier c ≠ 0) (h2 : (2 : ZMod p) ≠ 0)
    (w : IncidenceEquationWitness c xi eta) :
    ActualIncidenceBridge p c xi eta w.middle := by
  let firstTrace := w.firstTracePoint
  let secondTrace := w.secondTracePoint
  let firstPoint := inverseTracePoint c firstTrace
  let secondPoint := inverseTracePoint c secondTrace
  have hfirstTrace : tracePolynomial c firstTrace = 0 :=
    w.firstTracePoint_mem h2
  have hsecondTrace : tracePolynomial c secondTrace = 0 :=
    w.secondTracePoint_mem h2
  have hfirstSolution : IsSolution (coefficients c) firstPoint :=
    isSolution_inverseTracePoint c firstTrace hmultiplier hfirstTrace
  have hsecondSolution : IsSolution (coefficients c) secondPoint :=
    isSolution_inverseTracePoint c secondTrace hmultiplier hsecondTrace
  refine
    { firstPoint := ⟨firstPoint, hfirstSolution⟩
      secondPoint := ⟨secondPoint, hsecondSolution⟩
      firstOuterTrace := ?_
      secondOuterTrace := ?_
      firstMiddleTrace := ?_
      secondMiddleTrace := ?_ }
  · have hmap := congrArg Point.x1
      (tracePoint_inverseTracePoint c firstTrace hmultiplier)
    simpa [firstPoint, firstTrace] using hmap
  · have hmap := congrArg Point.x1
      (tracePoint_inverseTracePoint c secondTrace hmultiplier)
    simpa [secondPoint, secondTrace] using hmap
  · have hmap := congrArg Point.x2
      (tracePoint_inverseTracePoint c firstTrace hmultiplier)
    simpa [firstPoint, firstTrace] using hmap
  · have hmap := congrArg Point.x2
      (tracePoint_inverseTracePoint c secondTrace hmultiplier)
    simpa [secondPoint, secondTrace] using hmap

/-- Recover a coordinate from its affine trace. -/
theorem eq_inverseTraceCoordinate_of_trace_eq
    {K : Type*} [Field K] (c x t : K)
    (hmultiplier : multiplier c ≠ 0) (htrace : trace c x = t) :
    x = inverseTraceCoordinate c t := by
  rw [inverseTraceCoordinate]
  apply (eq_div_iff hmultiplier).2
  rw [trace] at htrace
  linear_combination htrace

/-- The Hasse--Weil range estimates and the explicit Möbius inequality
produce a full-order middle unit together with an actual regular incidence
witness. -/
theorem exists_primitive_regularIncidenceWitness_of_explicitInequality
    (coefficient : ℕ)
    (hEstimate : RegularIncidenceWitnessPointEstimate coefficient)
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (c xi eta : ZMod p) (hc : c ^ 2 ≠ 4)
    (hxi : IsRegularSplitMaximalTrace p c xi)
    (heta : IsRegularSplitMaximalTrace p c eta)
    (hpair : IsAdmissibleIncidencePair c xi eta)
    (hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p) :
    ∃ (u : (ZMod p)ˣ)
      (w : RegularIncidenceEquationWitness p c xi eta),
      w.1.middle = BGS.Markoff.splitTorusTrace u ∧
        orderOf u = Nat.card (ZMod p)ˣ := by
  let leftTrace :
      RegularIncidenceEquationWitness p c xi eta → ZMod p :=
    regularIncidenceWitnessTrace
  let rightTrace : (ZMod p)ˣ → ZMod p :=
    BGS.Markoff.splitTorusTrace
  obtain ⟨multiplicity, hmultiplicity, hRangeEstimate⟩ :=
    hEstimate p hpFive c xi eta hc hxi heta hpair
  have hRange :
      ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
        |(Nat.card (BGS.rightPowerTraceRangeSolutions
            leftTrace rightTrace d) : ℝ) -
              (multiplicity : ℝ) * (p : ℝ) / d| ≤
          (coefficient : ℝ) * Real.sqrt (p : ℝ) := by
    intro d hdvd hd
    simpa [leftTrace, rightTrace,
      regularIncidenceWitnessPowerRangeSolutions] using
      hRangeEstimate d hdvd hd
  have hpositive :=
    BGS.Markoff.divisorsError_lt_primitiveTraceMoebiusMainTerm_of_explicitInequality
      (Nat.card (ZMod p)ˣ) p 1 coefficient Nat.card_pos (by norm_num)
      (by simpa using hexplicit)
  letI : Finite (IncidenceEquationWitness c xi eta) :=
    Finite.of_injective
      (fun w : IncidenceEquationWitness c xi eta =>
        (w.middle, w.firstRoot, w.secondRoot))
      (by
        intro a b hab
        cases a
        cases b
        simp_all)
  letI : Finite (RegularIncidenceEquationWitness p c xi eta) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  obtain ⟨z, hz⟩ :=
    BGS.rightTraceExactOrderSolutions_nonempty_of_divisorsError_lt_moebiusMain
      leftTrace rightTrace
      (fun d => (multiplicity : ℝ) * (p : ℝ) / d)
      ((coefficient : ℝ) * Real.sqrt (p : ℝ)) hRange (by
        have hmainPositive :
            0 < BGS.Markoff.primitiveTraceMoebiusMainTerm
              (Nat.card (ZMod p)ˣ) p 1 :=
          lt_of_le_of_lt (by positivity) hpositive
        have hmultiplicityReal : (1 : ℝ) ≤ multiplicity := by
          exact_mod_cast hmultiplicity
        have hscale :
            BGS.Markoff.primitiveTraceMoebiusMainTerm
                (Nat.card (ZMod p)ˣ) p 1 ≤
              (multiplicity : ℝ) *
                BGS.Markoff.primitiveTraceMoebiusMainTerm
                  (Nat.card (ZMod p)ˣ) p 1 := by
          nlinarith
        calc
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
                ((coefficient : ℝ) * Real.sqrt (p : ℝ)) <
              BGS.Markoff.primitiveTraceMoebiusMainTerm
                (Nat.card (ZMod p)ˣ) p 1 := hpositive
          _ ≤ (multiplicity : ℝ) *
                BGS.Markoff.primitiveTraceMoebiusMainTerm
                  (Nat.card (ZMod p)ˣ) p 1 := hscale
          _ = ∑ x ∈ (Nat.card (ZMod p)ˣ).divisorsAntidiagonal,
                (μ x.fst : ℝ) *
                  ((multiplicity : ℝ) * (p : ℝ) / x.fst) := by
            simp only [BGS.Markoff.primitiveTraceMoebiusMainTerm]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring)
  rcases z with ⟨w, u⟩
  have hz' :=
    (BGS.mem_rightTraceExactOrderSolutions_iff
      leftTrace rightTrace (Nat.card (ZMod p)ˣ) (w, u)).mp hz
  exact ⟨u, w, hz'.1, hz'.2⟩

/-- A primitive regular incidence witness supplies a regular split-maximal
middle trace and two actual bridge points. -/
theorem exists_actual_regularSplitMaximal_bridge_of_explicitInequality
    (coefficient : ℕ)
    (hEstimate : RegularIncidenceWitnessPointEstimate coefficient)
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (c xi eta : ZMod p) (hc : c ^ 2 ≠ 4)
    (hmultiplier : multiplier c ≠ 0)
    (hxi : IsRegularSplitMaximalTrace p c xi)
    (heta : IsRegularSplitMaximalTrace p c eta)
    (hpair : IsAdmissibleIncidencePair c xi eta)
    (hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p) :
    ∃ middle : ZMod p,
      IsRegularSplitMaximalTrace p c middle ∧
        Nonempty (ActualIncidenceBridge p c xi eta middle) := by
  have hpTwo : p ≠ 2 := by omega
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  obtain ⟨u, w, htrace, horder⟩ :=
    exists_primitive_regularIncidenceWitness_of_explicitInequality
      coefficient hEstimate p hpFive c xi eta hc hxi heta hpair hexplicit
  let middle := w.1.middle
  have hmiddle :
      IsRegularSplitMaximalTrace p c middle := by
    refine ⟨w.2, u, htrace, horder⟩
  refine ⟨middle, hmiddle, ?_⟩
  exact ⟨actualIncidenceBridgeOfWitness
    p c xi eta hmultiplier htwo w.1⟩

/-- Canonical first-axis cage connectivity, conditional only on the explicit
range estimate and the displayed nonexceptional pair condition. -/
theorem sameOneStepComponent_of_firstCagePair_of_explicitInequality
    (coefficient : ℕ)
    (hEstimate : RegularIncidenceWitnessPointEstimate coefficient)
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (c xi eta : ZMod p) (hc : c ^ 2 ≠ 4)
    (hmultiplier : multiplier c ≠ 0)
    (hxi : IsRegularSplitMaximalTrace p c xi)
    (heta : IsRegularSplitMaximalTrace p c eta)
    (hpair : IsAdmissibleIncidencePair c xi eta)
    (hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p)
    (x y : SolutionSurface (coefficients c))
    (hx : trace c x.1.x1 = xi) (hy : trace c y.1.x1 = eta) :
    SameOneStepComponent c x y := by
  by_cases hsame : xi = eta
  · have hyXi : trace c y.1.x1 = xi := hy.trans hsame.symm
    let u := inverseTraceCoordinate c xi
    have htraceU : xi = trace c u :=
      (trace_inverseTraceCoordinate c xi hmultiplier).symm
    apply sameOneStepComponent_of_same_regularSplitMaximalFiber
      p c u xi htraceU hxi .first x y
    · exact eq_inverseTraceCoordinate_of_trace_eq
        c x.1.x1 xi hmultiplier hx
    · exact eq_inverseTraceCoordinate_of_trace_eq
        c y.1.x1 xi hmultiplier hyXi
  · obtain ⟨middle, hmiddle, ⟨bridge⟩⟩ :=
      exists_actual_regularSplitMaximal_bridge_of_explicitInequality
        coefficient hEstimate p hpFive c xi eta hc hmultiplier
          hxi heta hpair hexplicit
    let uxi := inverseTraceCoordinate c xi
    let ueta := inverseTraceCoordinate c eta
    let umiddle := inverseTraceCoordinate c middle
    have htraceXi : xi = trace c uxi :=
      (trace_inverseTraceCoordinate c xi hmultiplier).symm
    have htraceEta : eta = trace c ueta :=
      (trace_inverseTraceCoordinate c eta hmultiplier).symm
    have htraceMiddle : middle = trace c umiddle :=
      (trace_inverseTraceCoordinate c middle hmultiplier).symm
    have hxFirst : coordinateAt Axis.first x.1 = uxi :=
      eq_inverseTraceCoordinate_of_trace_eq
        c x.1.x1 xi hmultiplier hx
    have hbridgeFirst :
        coordinateAt Axis.first bridge.firstPoint.1 = uxi :=
      eq_inverseTraceCoordinate_of_trace_eq
        c bridge.firstPoint.1.x1 xi hmultiplier bridge.firstOuterTrace
    have hbridgeMiddleFirst :
        coordinateAt Axis.second bridge.firstPoint.1 = umiddle :=
      eq_inverseTraceCoordinate_of_trace_eq
        c bridge.firstPoint.1.x2 middle hmultiplier bridge.firstMiddleTrace
    have hbridgeMiddleSecond :
        coordinateAt Axis.second bridge.secondPoint.1 = umiddle :=
      eq_inverseTraceCoordinate_of_trace_eq
        c bridge.secondPoint.1.x2 middle hmultiplier bridge.secondMiddleTrace
    have hbridgeSecond :
        coordinateAt Axis.first bridge.secondPoint.1 = ueta :=
      eq_inverseTraceCoordinate_of_trace_eq
        c bridge.secondPoint.1.x1 eta hmultiplier bridge.secondOuterTrace
    have hyFirst : coordinateAt Axis.first y.1 = ueta :=
      eq_inverseTraceCoordinate_of_trace_eq
        c y.1.x1 eta hmultiplier hy
    have hxBridge :
        SameOneStepComponent c x bridge.firstPoint :=
      sameOneStepComponent_of_same_regularSplitMaximalFiber
        p c uxi xi htraceXi hxi .first x bridge.firstPoint
          hxFirst hbridgeFirst
    have hmiddleBridge :
        SameOneStepComponent c bridge.firstPoint bridge.secondPoint :=
      sameOneStepComponent_of_same_regularSplitMaximalFiber
        p c umiddle middle htraceMiddle hmiddle .second
          bridge.firstPoint bridge.secondPoint
          hbridgeMiddleFirst hbridgeMiddleSecond
    have hbridgeY :
        SameOneStepComponent c bridge.secondPoint y :=
      sameOneStepComponent_of_same_regularSplitMaximalFiber
        p c ueta eta htraceEta heta .first bridge.secondPoint y
          hbridgeSecond hyFirst
    exact sameOneStepComponent_trans hxBridge
      (sameOneStepComponent_trans hmiddleBridge hbridgeY)

/-- Cage connectivity for arbitrary outer axes.  The same canonical
incidence curve is used for every axis pair; equal-coefficient coordinate
relabeling merely places its two trace coordinates on the requested axes. -/
theorem sameOneStepComponent_of_cagePair_of_explicitInequality
    (coefficient : ℕ)
    (hEstimate : RegularIncidenceWitnessPointEstimate coefficient)
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (c xi eta : ZMod p) (hc : c ^ 2 ≠ 4)
    (hmultiplier : multiplier c ≠ 0)
    (hxi : IsRegularSplitMaximalTrace p c xi)
    (heta : IsRegularSplitMaximalTrace p c eta)
    (hpair : IsAdmissibleIncidencePair c xi eta)
    (hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p)
    (axis other : Axis)
    (x y : SolutionSurface (coefficients c))
    (hx : traceAt c axis x.1 = xi)
    (hy : traceAt c other y.1 = eta) :
    SameOneStepComponent c x y := by
  obtain ⟨middle, hmiddle, ⟨bridge⟩⟩ :=
    exists_actual_regularSplitMaximal_bridge_of_explicitInequality
      coefficient hEstimate p hpFive c xi eta hc hmultiplier
        hxi heta hpair hexplicit
  let middleAxis := bridgeAxis axis other
  have haxisMiddle : axis ≠ middleAxis :=
    (bridgeAxis_ne_left axis other).symm
  have hotherMiddle : other ≠ middleAxis :=
    (bridgeAxis_ne_right axis other).symm
  let firstPlaced :=
    placeFirstSecondSurface c axis middleAxis haxisMiddle
      bridge.firstPoint
  let secondPlaced :=
    placeFirstSecondSurface c other middleAxis hotherMiddle
      bridge.secondPoint
  let uxi := inverseTraceCoordinate c xi
  let ueta := inverseTraceCoordinate c eta
  let umiddle := inverseTraceCoordinate c middle
  have htraceXi : xi = trace c uxi :=
    (trace_inverseTraceCoordinate c xi hmultiplier).symm
  have htraceEta : eta = trace c ueta :=
    (trace_inverseTraceCoordinate c eta hmultiplier).symm
  have htraceMiddle : middle = trace c umiddle :=
    (trace_inverseTraceCoordinate c middle hmultiplier).symm
  have hxOuter : coordinateAt axis x.1 = uxi :=
    eq_inverseTraceCoordinate_of_trace_eq
      c (coordinateAt axis x.1) xi hmultiplier hx
  have hfirstOuterTrace :
      trace c (coordinateAt axis firstPlaced.1) = xi := by
    simpa [firstPlaced] using bridge.firstOuterTrace
  have hfirstOuter : coordinateAt axis firstPlaced.1 = uxi :=
    eq_inverseTraceCoordinate_of_trace_eq
      c (coordinateAt axis firstPlaced.1) xi hmultiplier
        hfirstOuterTrace
  have hfirstMiddleTrace :
      trace c (coordinateAt middleAxis firstPlaced.1) = middle := by
    simpa [firstPlaced] using bridge.firstMiddleTrace
  have hfirstMiddle :
      coordinateAt middleAxis firstPlaced.1 = umiddle :=
    eq_inverseTraceCoordinate_of_trace_eq
      c (coordinateAt middleAxis firstPlaced.1) middle hmultiplier
        hfirstMiddleTrace
  have hsecondMiddleTrace :
      trace c (coordinateAt middleAxis secondPlaced.1) = middle := by
    simpa [secondPlaced] using bridge.secondMiddleTrace
  have hsecondMiddle :
      coordinateAt middleAxis secondPlaced.1 = umiddle :=
    eq_inverseTraceCoordinate_of_trace_eq
      c (coordinateAt middleAxis secondPlaced.1) middle hmultiplier
        hsecondMiddleTrace
  have hsecondOuterTrace :
      trace c (coordinateAt other secondPlaced.1) = eta := by
    simpa [secondPlaced] using bridge.secondOuterTrace
  have hsecondOuter : coordinateAt other secondPlaced.1 = ueta :=
    eq_inverseTraceCoordinate_of_trace_eq
      c (coordinateAt other secondPlaced.1) eta hmultiplier
        hsecondOuterTrace
  have hyOuter : coordinateAt other y.1 = ueta :=
    eq_inverseTraceCoordinate_of_trace_eq
      c (coordinateAt other y.1) eta hmultiplier hy
  have hxBridge : SameOneStepComponent c x firstPlaced :=
    sameOneStepComponent_of_same_regularSplitMaximalFiber
      p c uxi xi htraceXi hxi axis x firstPlaced hxOuter hfirstOuter
  have hmiddleBridge :
      SameOneStepComponent c firstPlaced secondPlaced :=
    sameOneStepComponent_of_same_regularSplitMaximalFiber
      p c umiddle middle htraceMiddle hmiddle middleAxis
        firstPlaced secondPlaced hfirstMiddle hsecondMiddle
  have hbridgeY : SameOneStepComponent c secondPlaced y :=
    sameOneStepComponent_of_same_regularSplitMaximalFiber
      p c ueta eta htraceEta heta other secondPlaced y
        hsecondOuter hyOuter
  exact sameOneStepComponent_trans hxBridge
    (sameOneStepComponent_trans hmiddleBridge hbridgeY)

/-- Uniform large-prime connectivity of every admissible pair of canonical
first-axis cage fibers, relative only to
`RegularIncidenceWitnessPointEstimate`. -/
theorem exists_threshold_firstCagePair_connected
    (coefficient : ℕ)
    (hEstimate : RegularIncidenceWitnessPointEstimate coefficient) :
    ∃ threshold : ℕ,
      ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
        ∀ (c xi eta : ZMod p),
          c ^ 2 ≠ 4 →
          multiplier c ≠ 0 →
          IsRegularSplitMaximalTrace p c xi →
          IsRegularSplitMaximalTrace p c eta →
          IsAdmissibleIncidencePair c xi eta →
          ∀ (x y : SolutionSurface (coefficients c)),
            trace c x.1.x1 = xi →
            trace c y.1.x1 = eta →
            SameOneStepComponent c x y := by
  obtain ⟨threshold, hthreshold⟩ :=
    BGS.Markoff.exists_threshold_endgamePrimitiveTrace_explicitInequality
      coefficient (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨max threshold 5, ?_⟩
  intro p hp _ c xi eta hc hmultiplier hxi heta hpair x y hx hy
  have hpThreshold : threshold ≤ p :=
    (le_max_left threshold 5).trans hp
  have hpOne : 1 ≤ p := by omega
  have hpOneReal : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hpOne
  have honeLe :
      ((1 : ℕ) : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2 - 1 / 4) := by
    simpa using
      (Real.one_le_rpow hpOneReal
        (show (0 : ℝ) ≤ 1 / 2 - 1 / 4 by norm_num))
  have hexplicit := hthreshold p hpThreshold 1 honeLe
  apply sameOneStepComponent_of_firstCagePair_of_explicitInequality
    coefficient hEstimate p (by omega) c xi eta hc hmultiplier
      hxi heta hpair _ x y hx hy
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  rw [hcard]
  simpa only [Nat.cast_one, one_mul] using hexplicit

/-- Uniform large-prime form of the arbitrary-axis bridge. -/
theorem exists_threshold_cagePair_connected
    (coefficient : ℕ)
    (hEstimate : RegularIncidenceWitnessPointEstimate coefficient) :
    ∃ threshold : ℕ,
      ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
        ∀ (c xi eta : ZMod p),
          c ^ 2 ≠ 4 →
          multiplier c ≠ 0 →
          IsRegularSplitMaximalTrace p c xi →
          IsRegularSplitMaximalTrace p c eta →
          IsAdmissibleIncidencePair c xi eta →
          ∀ (axis other : Axis)
            (x y : SolutionSurface (coefficients c)),
            traceAt c axis x.1 = xi →
            traceAt c other y.1 = eta →
            SameOneStepComponent c x y := by
  obtain ⟨threshold, hthreshold⟩ :=
    BGS.Markoff.exists_threshold_endgamePrimitiveTrace_explicitInequality
      coefficient (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨max threshold 5, ?_⟩
  intro p hp _ c xi eta hc hmultiplier hxi heta hpair
    axis other x y hx hy
  have hpThreshold : threshold ≤ p :=
    (le_max_left threshold 5).trans hp
  have hpOne : 1 ≤ p := by omega
  have hpOneReal : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hpOne
  have honeLe :
      ((1 : ℕ) : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2 - 1 / 4) := by
    simpa using
      (Real.one_le_rpow hpOneReal
        (show (0 : ℝ) ≤ 1 / 2 - 1 / 4 by norm_num))
  have hexplicit := hthreshold p hpThreshold 1 honeLe
  apply sameOneStepComponent_of_cagePair_of_explicitInequality
    coefficient hEstimate p (by omega) c xi eta hc hmultiplier
      hxi heta hpair _ axis other x y hx hy
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  rw [hcard]
  simpa only [Nat.cast_one, one_mul] using hexplicit

/-- The exact residual algebraic condition for the whole regular split cage:
every pair of its trace labels is diagonal or avoids the explicit pair
obstruction. -/
def AllRegularSplitMaximalPairsAdmissible
    (p : ℕ) [Fact p.Prime] (c : ZMod p) : Prop :=
  ∀ xi eta : ZMod p,
    IsRegularSplitMaximalTrace p c xi →
    IsRegularSplitMaximalTrace p c eta →
    IsAdmissibleIncidencePair c xi eta

/-- Conditional connectivity of the entire maximal regular split cage.  The
two remaining inputs are now exact and separate:

* the Hasse--Weil range estimate on the explicit incidence witness type;
* avoidance of the displayed pair obstruction by split-maximal regular
  labels.
-/
theorem exists_threshold_regularSplitCage_connected
    (coefficient : ℕ)
    (hEstimate : RegularIncidenceWitnessPointEstimate coefficient) :
    ∃ threshold : ℕ,
      ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
        ∀ (c : ZMod p),
          c ^ 2 ≠ 4 →
          multiplier c ≠ 0 →
          AllRegularSplitMaximalPairsAdmissible p c →
          ∀ x y : SolutionSurface (coefficients c),
            IsInRegularSplitCage p c x →
            IsInRegularSplitCage p c y →
            SameOneStepComponent c x y := by
  obtain ⟨threshold, hconnect⟩ :=
    exists_threshold_cagePair_connected coefficient hEstimate
  refine ⟨threshold, ?_⟩
  intro p hp _ c hc hmultiplier hall x y hxCage hyCage
  obtain ⟨axis, hxi⟩ := hxCage
  obtain ⟨other, heta⟩ := hyCage
  let xi := traceAt c axis x.1
  let eta := traceAt c other y.1
  exact hconnect p hp c xi eta hc hmultiplier hxi heta
    (hall xi eta hxi heta) axis other x y rfl rfl

end

end GenMarkoff.Symmetric.Cage
