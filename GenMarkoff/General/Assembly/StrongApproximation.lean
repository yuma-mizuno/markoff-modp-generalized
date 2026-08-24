import GenMarkoff.General.Assembly.CageReadyCanonicalEndgame
import GenMarkoff.General.Assembly.ClassicalZeroBridge
import GenMarkoff.General.Assembly.ConnectingCageBoundary
import GenMarkoff.General.Assembly.CyclicStrongApproximation
import GenMarkoff.General.Assembly.ParityCageBoundary
import GenMarkoff.General.Cage.CanonicalOrbitConnecting
import GenMarkoff.General.Cage.CanonicalTwoRootConnecting
import GenMarkoff.General.Cage.ConnectingAxisTwoAssembly

/-!
# Unconditional fixed-coefficient strong approximation

This file closes the final connecting-cage boundary for the full Vieta
group.  Endpoint normalization is carried out in the second-axis frame and
the directed three-root relay joins the resulting primitive connecting
fibers.  Cyclic transport is always simultaneous on coefficients and
coordinates; it is used only to put a nonzero integral coefficient in the
first position.
-/

namespace GenMarkoff.General.Assembly

open GenMarkoff.General.Cage

noncomputable section

/-- Abstract pointwise assembly of two normalized second-axis endpoints.

The first endpoint supplies the branch-separation obstruction.  The second
is chosen relative to its trace, so the two traces form a connecting
incidence pair.  This lemma isolates the direction reversal in that pair
from the later square/nonsquare case split. -/
theorem sameVietaComponent_of_secondAxis_endpoint_normalizations
    {p : ℕ} [Fact p.Prime]
    {a : Coefficients (ZMod p)}
    {x y : SolutionSurface a}
    (hx :
      ∃ x' : SolutionSurface a,
        SameVietaComponent x x' ∧
          IsObstructionReadyPrimitiveRegularConnectingAxisTwo
            p a x')
    (hy :
      ∀ eta : ZMod p,
        OrderedTraceCandidateRegular a.a2 a.a3 a.a1 eta →
        incidenceCenteredNormObstruction
            (directedCycleLeftCoefficients a) eta ≠ 0 →
        ∃ y' : SolutionSurface a,
          SameVietaComponent y y' ∧
            IsConnectingPairPrimitiveRegularConnectingAxisTwo
              p a eta y')
    (hrelay :
      ∀ x' y' : SolutionSurface a,
        IsPrimitiveRegularConnectingAxisTwo p a x' →
        IsPrimitiveRegularConnectingAxisTwo p a y' →
        IsConnectingIncidencePair
          (directedCycleLeftCoefficients a)
          (traceAt a .second x'.1)
          (traceAt a .second y'.1) →
        SameVietaComponent x' y') :
    SameVietaComponent x y := by
  obtain ⟨x', hxx', hxPrimitive, hxObstruction⟩ := hx
  obtain ⟨qx, hxTrace, hxOrder, hxRegular, hxConnecting⟩ :=
    hxPrimitive
  obtain ⟨y', hyy', hyPrimitive, hyPair⟩ :=
    hy (traceAt a .second x'.1) hxRegular hxObstruction
  have hnormalized : SameVietaComponent x' y' :=
    hrelay x' y'
      ⟨qx, hxTrace, hxOrder, hxRegular, hxConnecting⟩
      hyPrimitive hyPair.symm
  exact
    sameVietaComponent_trans hxx'
      (sameVietaComponent_trans hnormalized
        (sameVietaComponent_symm hyy'))

/-- Pointwise form of the final cage assembly.

It separates the older canonical-to-cage-ready rotation step from the new
endpoint normalization and directed connecting relay. -/
theorem canonicalFirstAxisPrimitiveSplitVietaCage_of_endpoint_normalizations
    {p : ℕ} [Fact p.Prime]
    {a : Coefficients (ZMod p)}
    (hready :
      ∀ x : SolutionSurface a,
        IsCanonicalFirstAxisPrimitiveSplit p a x →
        ∃ x' : SolutionSurface a,
          SameVietaComponent x x' ∧
            IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x')
    (hobstruction :
      ∀ x : SolutionSurface a,
        IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x →
        ∃ x' : SolutionSurface a,
          SameVietaComponent x x' ∧
            IsObstructionReadyPrimitiveRegularConnectingAxisTwo
              p a x')
    (hpair :
      ∀ eta : ZMod p,
        OrderedTraceCandidateRegular a.a2 a.a3 a.a1 eta →
        incidenceCenteredNormObstruction
            (directedCycleLeftCoefficients a) eta ≠ 0 →
        ∀ x : SolutionSurface a,
          IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x →
          ∃ x' : SolutionSurface a,
            SameVietaComponent x x' ∧
              IsConnectingPairPrimitiveRegularConnectingAxisTwo
                p a eta x')
    (hrelay :
      ∀ x' y' : SolutionSurface a,
        IsPrimitiveRegularConnectingAxisTwo p a x' →
        IsPrimitiveRegularConnectingAxisTwo p a y' →
        IsConnectingIncidencePair
          (directedCycleLeftCoefficients a)
          (traceAt a .second x'.1)
          (traceAt a .second y'.1) →
        SameVietaComponent x' y') :
    CanonicalFirstAxisPrimitiveSplitVietaCage p a := by
  intro x y hx hy
  obtain ⟨xReady, hxReadyComponent, hxReady⟩ := hready x hx
  obtain ⟨yReady, hyReadyComponent, hyReady⟩ := hready y hy
  have hreadyNormalized : SameVietaComponent xReady yReady :=
    sameVietaComponent_of_secondAxis_endpoint_normalizations
      (hobstruction xReady hxReady)
      (fun eta hetaRegular hetaObstruction =>
        hpair eta hetaRegular hetaObstruction yReady hyReady)
      hrelay
  exact
    sameVietaComponent_trans hxReadyComponent
      (sameVietaComponent_trans hreadyNormalized
        (sameVietaComponent_symm hyReadyComponent))

/-- Unconditional large-prime form of the old-canonical to cage-ready
conversion, with its rotation word viewed inside the full Vieta group. -/
theorem
    exists_threshold_canonicalFirstAxisPrimitiveSplit_reaches_cageReadyVieta :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      [Fact p.Prime] →
      ∀ (a : Coefficients (ZMod p)),
        a.a1 ^ 2 ≠ 4 →
        a.a2 ^ 2 ≠ 4 →
        a.a3 ^ 2 ≠ 4 →
        ∀ x : SolutionSurface a,
          IsCanonicalFirstAxisPrimitiveSplit p a x →
          ∃ finish : SolutionSurface a,
            SameVietaComponent x finish ∧
              IsCageReadyCanonicalFirstAxisPrimitiveSplit
                p a finish := by
  obtain ⟨coefficient, hWeil⟩ :=
    GenMarkoff.exists_weightedShiftedTraceWeilBoundAssumption
  obtain ⟨threshold, hthreshold⟩ :=
    exists_threshold_canonicalFirstAxisPrimitiveSplit_reaches_cageReady
      coefficient hWeil
  refine ⟨threshold, ?_⟩
  intro p hp _ a hA1 hA2 hA3 x hx
  obtain ⟨finish, hcomponent, hready⟩ :=
    hthreshold p hp a hA1 hA2 hA3 x hx
  exact
    ⟨finish,
      sameVietaComponent_of_sameRotationComponent hcomponent,
      hready⟩

/-- The square branch of canonical endpoint normalization, packaged in the
predicate used by the final assembly. -/
theorem
    exists_threshold_cageReadyCanonicalFirstAxis_square_reaches_obstructionReadyAxisTwo :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      [Fact p.Prime] →
      ∀ (a : Coefficients (ZMod p)),
        a.a1 ^ 2 ≠ 4 →
        a.a2 ^ 2 ≠ 4 →
        a.a3 ^ 2 ≠ 4 →
        (a.a3, a.a1) ≠ (0, 0) →
        ∀ x : SolutionSurface a,
          IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x →
          IsSquare
            (centeredNorm a.a2 a.a3
              (traceAt a .first x.1)) →
          ∃ y : SolutionSurface a,
            SameVietaComponent x y ∧
              IsObstructionReadyPrimitiveRegularConnectingAxisTwo
                p a y := by
  obtain ⟨threshold, hthreshold⟩ :=
    exists_threshold_cageReadyCanonicalFirstAxis_square_reaches_obstructionReadyPrimitiveConnectingAxisTwo
  refine ⟨threshold, ?_⟩
  intro p hp _ a hA1 hA2 hA3 hmoving x hx hsquare
  obtain
      ⟨y, hxy, v, htrace, horder, hregular,
        hobstruction, hconnecting⟩ :=
    hthreshold p hp a hA1 hA2 hA3 hmoving x hx hsquare
  exact
    ⟨y, hxy,
      ⟨⟨v, htrace, horder, hregular, hconnecting⟩,
        hobstruction⟩⟩

/-- The square branch relative to an already obstruction-ready trace,
packaged in the predicate used by the final assembly. -/
theorem
    exists_threshold_cageReadyCanonicalFirstAxis_square_reaches_connectingPairAxisTwo :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      [Fact p.Prime] →
      ∀ (a : Coefficients (ZMod p)),
        a.a1 ^ 2 ≠ 4 →
        a.a2 ^ 2 ≠ 4 →
        a.a3 ^ 2 ≠ 4 →
        (a.a3, a.a1) ≠ (0, 0) →
        ∀ eta : ZMod p,
          OrderedTraceCandidateRegular a.a2 a.a3 a.a1 eta →
          incidenceCenteredNormObstruction
              (directedCycleLeftCoefficients a) eta ≠ 0 →
          ∀ x : SolutionSurface a,
            IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x →
            IsSquare
              (centeredNorm a.a2 a.a3
                (traceAt a .first x.1)) →
            ∃ y : SolutionSurface a,
              SameVietaComponent x y ∧
                IsConnectingPairPrimitiveRegularConnectingAxisTwo
                  p a eta y := by
  obtain ⟨threshold, hthreshold⟩ :=
    exists_threshold_cageReadyCanonicalFirstAxis_square_reaches_primitiveConnectingPairAxisTwo
  refine ⟨threshold, ?_⟩
  intro p hp _ a hA1 hA2 hA3 hmoving
    eta hetaRegular hetaObstruction x hx hsquare
  obtain
      ⟨y, hxy, v, htrace, horder, hregular,
        hpair, hconnecting⟩ :=
    hthreshold p hp a hA1 hA2 hA3 hmoving
      eta hetaRegular hetaObstruction x hx hsquare
  exact
    ⟨y, hxy,
      ⟨⟨v, htrace, horder, hregular, hconnecting⟩,
        hpair⟩⟩

/-- The nonsquare branch of canonical endpoint normalization, packaged in
the obstruction-ready predicate used by the final assembly. -/
theorem
    exists_threshold_cageReadyCanonicalFirstAxis_nonsquare_reaches_obstructionReadyAxisTwo :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      [Fact p.Prime] →
      ∀ (a : Coefficients (ZMod p)),
        a.a1 ^ 2 ≠ 4 →
        a.a2 ^ 2 ≠ 4 →
        a.a3 ^ 2 ≠ 4 →
        (a.a3, a.a1) ≠ (0, 0) →
        ∀ x : SolutionSurface a,
          IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x →
          ¬ IsSquare
            (centeredNorm a.a2 a.a3
              (traceAt a .first x.1)) →
          ∃ y : SolutionSurface a,
            SameVietaComponent x y ∧
              IsObstructionReadyPrimitiveRegularConnectingAxisTwo
                p a y := by
  obtain ⟨threshold, hthreshold⟩ :=
    exists_threshold_cageReadyCanonicalFirstAxis_nonsquare_reaches_obstructionReadyPrimitiveConnectingAxisTwo
  refine ⟨threshold, ?_⟩
  intro p hp _ a hA1 hA2 hA3 hmoving x hx hnonsquare
  obtain
      ⟨y, hxy, q, htrace, horder, hregular,
        hobstruction, hconnecting⟩ :=
    hthreshold p hp a hA1 hA2 hA3 hmoving x hx hnonsquare
  exact
    ⟨y, hxy,
      ⟨⟨q, htrace, horder, hregular, hconnecting⟩,
        hobstruction⟩⟩

/-- The nonsquare branch relative to an already obstruction-ready trace,
packaged in the connecting-pair predicate used by the final assembly. -/
theorem
    exists_threshold_cageReadyCanonicalFirstAxis_nonsquare_reaches_connectingPairAxisTwo :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      [Fact p.Prime] →
      ∀ (a : Coefficients (ZMod p)),
        a.a1 ^ 2 ≠ 4 →
        a.a2 ^ 2 ≠ 4 →
        a.a3 ^ 2 ≠ 4 →
        (a.a3, a.a1) ≠ (0, 0) →
        ∀ eta : ZMod p,
          OrderedTraceCandidateRegular a.a2 a.a3 a.a1 eta →
          incidenceCenteredNormObstruction
              (directedCycleLeftCoefficients a) eta ≠ 0 →
          ∀ x : SolutionSurface a,
            IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x →
            ¬ IsSquare
              (centeredNorm a.a2 a.a3
                (traceAt a .first x.1)) →
            ∃ y : SolutionSurface a,
              SameVietaComponent x y ∧
                IsConnectingPairPrimitiveRegularConnectingAxisTwo
                  p a eta y := by
  obtain ⟨threshold, hthreshold⟩ :=
    exists_threshold_cageReadyCanonicalFirstAxis_nonsquare_reaches_primitiveConnectingPairAxisTwo
  refine ⟨threshold, ?_⟩
  intro p hp _ a hA1 hA2 hA3 hmoving
    eta hetaRegular hetaObstruction x hx hnonsquare
  obtain
      ⟨y, hxy, q, htrace, horder, hregular,
        hpair, hconnecting⟩ :=
    hthreshold p hp a hA1 hA2 hA3 hmoving
      eta hetaRegular hetaObstruction x hx hnonsquare
  exact
    ⟨y, hxy,
      ⟨⟨q, htrace, horder, hregular, hconnecting⟩,
        hpair⟩⟩

/-- The complete finite-field Vieta cage at the closed universal analytic
cutoff. -/
theorem canonicalFirstAxisPrimitiveSplitVietaCage_of_analyticCutoff
    (p : ℕ) (hp : GenMarkoff.General.Explicit.analyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hnormalizationMoving : (a.a3, a.a1) ≠ (0, 0))
    (hrelayMoving : (a.a1, a.a2) ≠ (0, 0)) :
    CanonicalFirstAxisPrimitiveSplitVietaCage p a := by
  apply
    canonicalFirstAxisPrimitiveSplitVietaCage_of_endpoint_normalizations
  · intro x hx
    obtain ⟨finish, hcomponent, hready⟩ :=
      canonicalFirstAxisPrimitiveSplit_reaches_cageReady_of_analyticCutoff
        33 GenMarkoff.weightedShiftedTraceWeilBoundAssumption_thirtyThree
        (by norm_num) p hp a hA1 hA2 hA3 x hx
    exact
      ⟨finish,
        sameVietaComponent_of_sameRotationComponent hcomponent,
        hready⟩
  · intro x hx
    by_cases hsquare :
        IsSquare
          (centeredNorm a.a2 a.a3
            (traceAt a .first x.1))
    · obtain
          ⟨y, hxy, v, htrace, horder, hregular,
            hobstruction, hconnecting⟩ :=
        cageReadyCanonicalFirstAxis_square_reaches_obstructionReadyPrimitiveConnectingAxisTwo_of_analyticCutoff
          p hp a hA1 hA2 hA3 hnormalizationMoving x hx hsquare
      exact
        ⟨y, hxy,
          ⟨⟨v, htrace, horder, hregular, hconnecting⟩,
            hobstruction⟩⟩
    · obtain
          ⟨y, hxy, q, htrace, horder, hregular,
            hobstruction, hconnecting⟩ :=
        cageReadyCanonicalFirstAxis_nonsquare_reaches_obstructionReadyPrimitiveConnectingAxisTwo_of_analyticCutoff
          p hp a hA1 hA2 hA3 hnormalizationMoving x hx hsquare
      exact
        ⟨y, hxy,
          ⟨⟨q, htrace, horder, hregular, hconnecting⟩,
            hobstruction⟩⟩
  · intro eta hetaRegular hetaObstruction x hx
    by_cases hsquare :
        IsSquare
          (centeredNorm a.a2 a.a3
            (traceAt a .first x.1))
    · obtain
          ⟨y, hxy, v, htrace, horder, hregular,
            hpair, hconnecting⟩ :=
        cageReadyCanonicalFirstAxis_square_reaches_primitiveConnectingPairAxisTwo_of_analyticCutoff
          p hp a hA1 hA2 hA3 hnormalizationMoving
          eta hetaRegular hetaObstruction x hx hsquare
      exact
        ⟨y, hxy,
          ⟨⟨v, htrace, horder, hregular, hconnecting⟩,
            hpair⟩⟩
    · obtain
          ⟨y, hxy, q, htrace, horder, hregular,
            hpair, hconnecting⟩ :=
        cageReadyCanonicalFirstAxis_nonsquare_reaches_primitiveConnectingPairAxisTwo_of_analyticCutoff
          p hp a hA1 hA2 hA3 hnormalizationMoving
          eta hetaRegular hetaObstruction x hx hsquare
      exact
        ⟨y, hxy,
          ⟨⟨q, htrace, horder, hregular, hconnecting⟩,
            hpair⟩⟩
  · exact
      sameVietaComponent_of_primitiveRegularConnectingAxisTwo_of_analyticCutoff
        p hp a hmultiplier hA1 hA2 hA3 hrelayMoving

/-- The complete finite-field Vieta cage at the reasonable universal
analytic cutoff. -/
theorem canonicalFirstAxisPrimitiveSplitVietaCage_of_reasonableCutoff
    (p : ℕ)
    (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hnormalizationMoving : (a.a3, a.a1) ≠ (0, 0))
    (hrelayMoving : (a.a1, a.a2) ≠ (0, 0)) :
    CanonicalFirstAxisPrimitiveSplitVietaCage p a := by
  apply
    canonicalFirstAxisPrimitiveSplitVietaCage_of_endpoint_normalizations
  · intro x hx
    obtain ⟨finish, hcomponent, hready⟩ :=
      canonicalFirstAxisPrimitiveSplit_reaches_cageReady_of_reasonableCutoff
        33 GenMarkoff.weightedShiftedTraceWeilBoundAssumption_thirtyThree
        (by norm_num) p hp a hA1 hA2 hA3 x hx
    exact
      ⟨finish,
        sameVietaComponent_of_sameRotationComponent hcomponent,
        hready⟩
  · intro x hx
    by_cases hsquare :
        IsSquare
          (centeredNorm a.a2 a.a3
            (traceAt a .first x.1))
    · obtain
          ⟨y, hxy, v, htrace, horder, hregular,
            hobstruction, hconnecting⟩ :=
        cageReadyCanonicalFirstAxis_square_reaches_obstructionReadyPrimitiveConnectingAxisTwo_of_reasonableCutoff
          p hp a hA1 hA2 hA3 hnormalizationMoving x hx hsquare
      exact
        ⟨y, hxy,
          ⟨⟨v, htrace, horder, hregular, hconnecting⟩,
            hobstruction⟩⟩
    · obtain
          ⟨y, hxy, q, htrace, horder, hregular,
            hobstruction, hconnecting⟩ :=
        cageReadyCanonicalFirstAxis_nonsquare_reaches_obstructionReadyPrimitiveConnectingAxisTwo_of_reasonableCutoff
          p hp a hA1 hA2 hA3 hnormalizationMoving x hx hsquare
      exact
        ⟨y, hxy,
          ⟨⟨q, htrace, horder, hregular, hconnecting⟩,
            hobstruction⟩⟩
  · intro eta hetaRegular hetaObstruction x hx
    by_cases hsquare :
        IsSquare
          (centeredNorm a.a2 a.a3
            (traceAt a .first x.1))
    · obtain
          ⟨y, hxy, v, htrace, horder, hregular,
            hpair, hconnecting⟩ :=
        cageReadyCanonicalFirstAxis_square_reaches_primitiveConnectingPairAxisTwo_of_reasonableCutoff
          p hp a hA1 hA2 hA3 hnormalizationMoving
          eta hetaRegular hetaObstruction x hx hsquare
      exact
        ⟨y, hxy,
          ⟨⟨v, htrace, horder, hregular, hconnecting⟩,
            hpair⟩⟩
    · obtain
          ⟨y, hxy, q, htrace, horder, hregular,
            hpair, hconnecting⟩ :=
        cageReadyCanonicalFirstAxis_nonsquare_reaches_primitiveConnectingPairAxisTwo_of_reasonableCutoff
          p hp a hA1 hA2 hA3 hnormalizationMoving
          eta hetaRegular hetaObstruction x hx hsquare
      exact
        ⟨y, hxy,
          ⟨⟨q, htrace, horder, hregular, hconnecting⟩,
            hpair⟩⟩
  · exact
      sameVietaComponent_of_primitiveRegularConnectingAxisTwo_of_reasonableCutoff
        p hp a hmultiplier hA1 hA2 hA3 hrelayMoving

/-- The final finite-field cage, reduced to the two nonsquare endpoint
normalization estimates.

All other ingredients in this statement are unconditional compiled
theorems: canonical-to-cage-ready conversion, both square normalizations,
and the directed three-root relay. -/
theorem
    exists_threshold_canonicalFirstAxisPrimitiveSplitVietaCage_of_nonsquare_normalizations
    (hobstructionNonsquare :
      ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
        [Fact p.Prime] →
        ∀ (a : Coefficients (ZMod p)),
          a.a1 ^ 2 ≠ 4 →
          a.a2 ^ 2 ≠ 4 →
          a.a3 ^ 2 ≠ 4 →
          (a.a3, a.a1) ≠ (0, 0) →
          ∀ x : SolutionSurface a,
            IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x →
            ¬ IsSquare
              (centeredNorm a.a2 a.a3
                (traceAt a .first x.1)) →
            ∃ y : SolutionSurface a,
              SameVietaComponent x y ∧
                IsObstructionReadyPrimitiveRegularConnectingAxisTwo
                  p a y)
    (hpairNonsquare :
      ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
        [Fact p.Prime] →
        ∀ (a : Coefficients (ZMod p)),
          a.a1 ^ 2 ≠ 4 →
          a.a2 ^ 2 ≠ 4 →
          a.a3 ^ 2 ≠ 4 →
          (a.a3, a.a1) ≠ (0, 0) →
          ∀ eta : ZMod p,
            OrderedTraceCandidateRegular a.a2 a.a3 a.a1 eta →
            incidenceCenteredNormObstruction
                (directedCycleLeftCoefficients a) eta ≠ 0 →
            ∀ x : SolutionSurface a,
              IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x →
              ¬ IsSquare
                (centeredNorm a.a2 a.a3
                  (traceAt a .first x.1)) →
              ∃ y : SolutionSurface a,
                SameVietaComponent x y ∧
                  IsConnectingPairPrimitiveRegularConnectingAxisTwo
                    p a eta y) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      [Fact p.Prime] →
      ∀ (a : Coefficients (ZMod p)),
        a.multiplier ≠ 0 →
        a.a1 ^ 2 ≠ 4 →
        a.a2 ^ 2 ≠ 4 →
        a.a3 ^ 2 ≠ 4 →
        (a.a3, a.a1) ≠ (0, 0) →
        (a.a1, a.a2) ≠ (0, 0) →
        CanonicalFirstAxisPrimitiveSplitVietaCage p a := by
  obtain ⟨readyThreshold, hready⟩ :=
    exists_threshold_canonicalFirstAxisPrimitiveSplit_reaches_cageReadyVieta
  obtain ⟨squareObstructionThreshold, hsquareObstruction⟩ :=
    exists_threshold_cageReadyCanonicalFirstAxis_square_reaches_obstructionReadyAxisTwo
  obtain ⟨nonsquareObstructionThreshold, hnonsquareObstruction⟩ :=
    hobstructionNonsquare
  obtain ⟨squarePairThreshold, hsquarePair⟩ :=
    exists_threshold_cageReadyCanonicalFirstAxis_square_reaches_connectingPairAxisTwo
  obtain ⟨nonsquarePairThreshold, hnonsquarePair⟩ :=
    hpairNonsquare
  obtain ⟨relayThreshold, hrelay⟩ :=
    exists_threshold_sameVietaComponent_of_primitiveRegularConnectingAxisTwo
  refine
    ⟨max readyThreshold
        (max squareObstructionThreshold
          (max nonsquareObstructionThreshold
            (max squarePairThreshold
              (max nonsquarePairThreshold relayThreshold)))),
      ?_⟩
  intro p hp _ a hmultiplier hA1 hA2 hA3
    hnormalizationMoving hrelayMoving
  simp only [max_le_iff] at hp
  obtain
      ⟨hpReady, hpSquareObstruction, hpNonsquareObstruction,
        hpSquarePair, hpNonsquarePair, hpRelay⟩ := hp
  apply
    canonicalFirstAxisPrimitiveSplitVietaCage_of_endpoint_normalizations
  · exact hready p hpReady a hA1 hA2 hA3
  · intro x hx
    by_cases hsquare :
        IsSquare
          (centeredNorm a.a2 a.a3
            (traceAt a .first x.1))
    · exact
        hsquareObstruction p hpSquareObstruction
          a hA1 hA2 hA3 hnormalizationMoving x hx hsquare
    · exact
        hnonsquareObstruction p hpNonsquareObstruction
          a hA1 hA2 hA3 hnormalizationMoving x hx hsquare
  · intro eta hetaRegular hetaObstruction x hx
    by_cases hsquare :
        IsSquare
          (centeredNorm a.a2 a.a3
            (traceAt a .first x.1))
    · exact
        hsquarePair p hpSquarePair
          a hA1 hA2 hA3 hnormalizationMoving
          eta hetaRegular hetaObstruction x hx hsquare
    · exact
        hnonsquarePair p hpNonsquarePair
          a hA1 hA2 hA3 hnormalizationMoving
          eta hetaRegular hetaObstruction x hx hsquare
  · exact
      hrelay p hpRelay a hmultiplier hA1 hA2 hA3 hrelayMoving

/-- An integral coefficient triple with nonzero first coefficient inherits an
eventual canonical cage from a uniform generic finite-field cage theorem.

The first coefficient survives reduction above an explicit cutoff and
simultaneously makes both directed moving pairs nonzero. -/
theorem
    IntegrallyNondegenerate.eventuallyCanonicalFirstAxisPrimitiveSplitVietaCage_of_a1_ne_zero_of_uniform_cage
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (ha1 : a.a1 ≠ 0)
    (hcage :
      ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
        [Fact p.Prime] →
        ∀ (b : Coefficients (ZMod p)),
          b.multiplier ≠ 0 →
          b.a1 ^ 2 ≠ 4 →
          b.a2 ^ 2 ≠ 4 →
          b.a3 ^ 2 ≠ 4 →
          (b.a3, b.a1) ≠ (0, 0) →
          (b.a1, b.a2) ≠ (0, 0) →
          CanonicalFirstAxisPrimitiveSplitVietaCage p b) :
    EventuallyCanonicalFirstAxisPrimitiveSplitVietaCage a := by
  obtain ⟨cageThreshold, hcage⟩ := hcage
  refine
    ⟨max cageThreshold
        (max (genericAdmissibilityCutoff a)
          (firstCoefficientNonzeroCutoff a)),
      ?_⟩
  intro p hpPrime hpLarge
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hpCage : cageThreshold ≤ p :=
    (Nat.le_max_left cageThreshold
      (max (genericAdmissibilityCutoff a)
        (firstCoefficientNonzeroCutoff a))).trans hpLarge
  have hpGeneric : genericAdmissibilityCutoff a ≤ p :=
    (Nat.le_max_left
      (genericAdmissibilityCutoff a)
      (firstCoefficientNonzeroCutoff a)).trans
        ((Nat.le_max_right cageThreshold
          (max (genericAdmissibilityCutoff a)
            (firstCoefficientNonzeroCutoff a))).trans hpLarge)
  have hpFirst : firstCoefficientNonzeroCutoff a ≤ p :=
    (Nat.le_max_right
      (genericAdmissibilityCutoff a)
      (firstCoefficientNonzeroCutoff a)).trans
        ((Nat.le_max_right cageThreshold
          (max (genericAdmissibilityCutoff a)
            (firstCoefficientNonzeroCutoff a))).trans hpLarge)
  have hadmissible :
      GenericAdmissible (modCoefficients a p) :=
    ha.genericAdmissibleAt_of_cutoff_le hpGeneric
  obtain ⟨hmultiplier, hA1, hA2, hA3⟩ := hadmissible
  have ha1mod : (modCoefficients a p).a1 ≠ 0 :=
    modCoefficients_a1_ne_zero_of_firstCoefficientNonzeroCutoff_le
      ha1 hpFirst
  have hnormalizationMoving :
      ((modCoefficients a p).a3, (modCoefficients a p).a1) ≠
        (0, 0) := by
    intro hzero
    apply ha1mod
    exact congrArg Prod.snd hzero
  have hrelayMoving :
      ((modCoefficients a p).a1, (modCoefficients a p).a2) ≠
        (0, 0) := by
    intro hzero
    apply ha1mod
    exact congrArg Prod.fst hzero
  exact
    hcage p hpCage (modCoefficients a p)
      hmultiplier hA1 hA2 hA3
      hnormalizationMoving hrelayMoving

/-- The uniform finite-field cage implies eventual Vieta strong
approximation for an integrally nondegenerate integral triple whose first
coefficient is nonzero. -/
theorem
    IntegrallyNondegenerate.eventuallyVietaStrongApproximation_of_a1_ne_zero_of_uniform_cage
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (ha1 : a.a1 ≠ 0)
    (hcage :
      ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
        [Fact p.Prime] →
        ∀ (b : Coefficients (ZMod p)),
          b.multiplier ≠ 0 →
          b.a1 ^ 2 ≠ 4 →
          b.a2 ^ 2 ≠ 4 →
          b.a3 ^ 2 ≠ 4 →
          (b.a3, b.a1) ≠ (0, 0) →
          (b.a1, b.a2) ≠ (0, 0) →
          CanonicalFirstAxisPrimitiveSplitVietaCage p b) :
    EventuallyVietaStrongApproximation a :=
  IntegrallyNondegenerate.eventuallyVietaStrongApproximation_of_canonicalFirstAxisPrimitiveSplitVietaCage
    ha
    (IntegrallyNondegenerate.eventuallyCanonicalFirstAxisPrimitiveSplitVietaCage_of_a1_ne_zero_of_uniform_cage
      ha ha1 hcage)

/-- A coefficient-independent uniform cage closes the global eventual
full-Vieta statement.  A simultaneous cyclic transport first places a
nonzero coefficient in the first position; the all-zero triple is handled
by the pinned classical BGS bridge. -/
theorem eventualVietaStrongApproximationStatement_of_uniform_cage
    (hcage :
      ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
        [Fact p.Prime] →
        ∀ (b : Coefficients (ZMod p)),
          b.multiplier ≠ 0 →
          b.a1 ^ 2 ≠ 4 →
          b.a2 ^ 2 ≠ 4 →
          b.a3 ^ 2 ≠ 4 →
          (b.a3, b.a1) ≠ (0, 0) →
          (b.a1, b.a2) ≠ (0, 0) →
          CanonicalFirstAxisPrimitiveSplitVietaCage p b) :
    EventualVietaStrongApproximationStatement := by
  intro a ha
  by_cases ha1 : a.a1 ≠ 0
  · exact
      IntegrallyNondegenerate.eventuallyVietaStrongApproximation_of_a1_ne_zero_of_uniform_cage
        ha ha1 hcage
  by_cases ha2 : a.a2 ≠ 0
  · have hcycled :
        IntegrallyNondegenerate
          (directedCycleLeftCoefficients a) :=
      (integrallyNondegenerate_directedCycleLeft_iff a).2 ha
    have hcycledA1 :
        (directedCycleLeftCoefficients a).a1 ≠ 0 := by
      simpa [directedCycleLeftCoefficients] using ha2
    exact
      eventuallyVietaStrongApproximation_of_directedCycleLeft a
        (IntegrallyNondegenerate.eventuallyVietaStrongApproximation_of_a1_ne_zero_of_uniform_cage
          hcycled hcycledA1 hcage)
  by_cases ha3 : a.a3 ≠ 0
  · have hcycled :
        IntegrallyNondegenerate
          (directedCycleRightCoefficients a) :=
      (integrallyNondegenerate_directedCycleRight_iff a).2 ha
    have hcycledA1 :
        (directedCycleRightCoefficients a).a1 ≠ 0 := by
      simpa [directedCycleRightCoefficients] using ha3
    exact
      eventuallyVietaStrongApproximation_of_directedCycleRight a
        (IntegrallyNondegenerate.eventuallyVietaStrongApproximation_of_a1_ne_zero_of_uniform_cage
          hcycled hcycledA1 hcage)
  · have ha1Zero : a.a1 = 0 := not_ne_iff.mp ha1
    have ha2Zero : a.a2 = 0 := not_ne_iff.mp ha2
    have ha3Zero : a.a3 = 0 := not_ne_iff.mp ha3
    have hzero : a = classicalZeroCoefficients ℤ := by
      ext <;>
        simp [classicalZeroCoefficients, ha1Zero, ha2Zero, ha3Zero]
    rw [hzero]
    exact classicalZero_eventuallyVietaStrongApproximation

/-- Uniform finite-field connecting cage for every generic coefficient frame
whose directed normalization and relay pairs are nonzero. -/
theorem exists_threshold_canonicalFirstAxisPrimitiveSplitVietaCage :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      [Fact p.Prime] →
      ∀ (a : Coefficients (ZMod p)),
        a.multiplier ≠ 0 →
        a.a1 ^ 2 ≠ 4 →
        a.a2 ^ 2 ≠ 4 →
        a.a3 ^ 2 ≠ 4 →
        (a.a3, a.a1) ≠ (0, 0) →
        (a.a1, a.a2) ≠ (0, 0) →
        CanonicalFirstAxisPrimitiveSplitVietaCage p a :=
  exists_threshold_canonicalFirstAxisPrimitiveSplitVietaCage_of_nonsquare_normalizations
    exists_threshold_cageReadyCanonicalFirstAxis_nonsquare_reaches_obstructionReadyAxisTwo
    exists_threshold_cageReadyCanonicalFirstAxis_nonsquare_reaches_connectingPairAxisTwo

/-- Eventual canonical full-Vieta cage when the first integral coefficient is
nonzero. -/
theorem
    IntegrallyNondegenerate.eventuallyCanonicalFirstAxisPrimitiveSplitVietaCage_of_a1_ne_zero
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (ha1 : a.a1 ≠ 0) :
    EventuallyCanonicalFirstAxisPrimitiveSplitVietaCage a :=
  IntegrallyNondegenerate.eventuallyCanonicalFirstAxisPrimitiveSplitVietaCage_of_a1_ne_zero_of_uniform_cage
    ha ha1 exists_threshold_canonicalFirstAxisPrimitiveSplitVietaCage

/-- Eventual full-Vieta strong approximation when the first integral
coefficient is nonzero.  The global theorem below removes this orientation
assumption by simultaneous cyclic transport. -/
theorem
    IntegrallyNondegenerate.eventuallyVietaStrongApproximation_of_a1_ne_zero
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (ha1 : a.a1 ≠ 0) :
    EventuallyVietaStrongApproximation a :=
  IntegrallyNondegenerate.eventuallyVietaStrongApproximation_of_a1_ne_zero_of_uniform_cage
    ha ha1 exists_threshold_canonicalFirstAxisPrimitiveSplitVietaCage

/-- The main full-Vieta theorem: every fixed integrally nondegenerate
integral coefficient triple has a connected punctured solution surface
modulo every sufficiently large prime. -/
theorem eventualVietaStrongApproximationStatement :
    EventualVietaStrongApproximationStatement :=
  eventualVietaStrongApproximationStatement_of_uniform_cage
    exists_threshold_canonicalFirstAxisPrimitiveSplitVietaCage

/-- Per-coefficient form of the main full-Vieta theorem. -/
theorem IntegrallyNondegenerate.eventuallyVietaStrongApproximation
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a) :
    EventuallyVietaStrongApproximation a :=
  eventualVietaStrongApproximationStatement a ha

/-- The project's main target: eventual transitivity of the rotation group
on the punctured fixed-coefficient surface. -/
theorem eventualStrongApproximationStatement :
    EventualStrongApproximationStatement :=
  eventualStrongApproximationStatement_iff_eventualVietaStrongApproximationStatement.mpr
    eventualVietaStrongApproximationStatement

/-- Per-coefficient form of eventual rotation strong approximation. -/
theorem IntegrallyNondegenerate.eventuallyRotationStrongApproximation
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a) :
    EventuallyRotationStrongApproximation a :=
  eventualStrongApproximationStatement a ha

/-- A canonical primitive split endpoint is punctured, because candidate
regularity excludes `trace + a₁ = 0`, while that expression vanishes at the
origin. -/
private theorem canonicalFirstAxisPrimitiveSplit_ne_surfaceOrigin
    {p : ℕ} [Fact p.Prime] {a : Coefficients (ZMod p)}
    {x : SolutionSurface a}
    (hx : IsCanonicalFirstAxisPrimitiveSplit p a x) :
    x ≠ surfaceOrigin a := by
  intro hxOrigin
  obtain ⟨_, _, _, hregular⟩ := hx
  apply hregular.2.1
  subst x
  simp [surfaceOrigin, origin]

/-- The parity-cage predicate itself is a downstream consequence of the
completed rotation-transitivity theorem.  What remains optional is a direct
parity-incidence construction usable upstream of transitivity. -/
theorem IntegrallyNondegenerate.eventuallyCanonicalFirstAxisPrimitiveSplitCage
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a) :
    EventuallyCanonicalFirstAxisPrimitiveSplitCage a := by
  obtain ⟨p0, hstrong⟩ :=
    IntegrallyNondegenerate.eventuallyRotationStrongApproximation ha
  refine ⟨p0, ?_⟩
  intro p hp hp0
  letI : Fact p.Prime := ⟨hp⟩
  intro x y hx hy
  let xPunctured : PuncturedSolutionSurface (modCoefficients a p) :=
    ⟨x, canonicalFirstAxisPrimitiveSplit_ne_surfaceOrigin hx⟩
  let yPunctured : PuncturedSolutionSurface (modCoefficients a p) :=
    ⟨y, canonicalFirstAxisPrimitiveSplit_ne_surfaceOrigin hy⟩
  obtain ⟨g, hg⟩ := hstrong p hp hp0 xPunctured yPunctured
  refine ⟨g, ?_⟩
  exact congrArg Subtype.val hg

/-- The completed rotation-transitivity theorem also implies the formal
giant-orbit statement: the orbit of `(1,1,1)` is the whole punctured surface,
so its complement has cardinality zero.  This is a consequence of strong
approximation, not the older direct giant-orbit route used as an input to a
finite-orbit argument. -/
theorem generalizedGiantOrbitStatement :
    GeneralizedGiantOrbitStatement := by
  intro a ha epsilon _hepsilon
  obtain ⟨p0, hstrong⟩ :=
    IntegrallyNondegenerate.eventuallyRotationStrongApproximation ha
  refine ⟨p0, ?_⟩
  intro p hp hp0
  letI : Fact p.Prime := ⟨hp⟩
  let x : PuncturedSolutionSurface (modCoefficients a p) :=
    ⟨surfaceUnit (modCoefficients a p),
      surfaceUnit_ne_surfaceOrigin (modCoefficients a p)⟩
  refine ⟨x, ?_⟩
  have horbit : puncturedRotationOrbit x = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    apply MulAction.mem_orbit_iff.mpr
    exact hstrong p hp hp0 x y
  simpa [rotationOrbitComplementCard, horbit] using
    (Real.rpow_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p) epsilon)

/-- Every solution modulo every sufficiently large prime lifts to an
integral point on the fixed generalized surface. -/
theorem IntegrallyNondegenerate.eventuallyReductionSurjective
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a) :
    ∃ p0 : ℕ, ∀ (p : ℕ) (_hp : p.Prime), p0 ≤ p →
      Function.Surjective
        ((fixedIntegralCoefficientSurfaceFunctor a).map
          (CommRingCat.ofHom (Int.castRingHom (ZMod p)))) :=
  eventually_reduction_surjective_of_eventuallyVietaStrongApproximation
    a
      (IntegrallyNondegenerate.eventuallyVietaStrongApproximation ha)

end

end GenMarkoff.General.Assembly
