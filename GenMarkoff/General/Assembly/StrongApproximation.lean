import GenMarkoff.General.Assembly.CageReadyCanonicalEndgame
import GenMarkoff.General.Assembly.ClassicalZeroBridge
import GenMarkoff.General.Assembly.ConnectingCageBoundary
import GenMarkoff.General.Assembly.CyclicStrongApproximation
import GenMarkoff.General.Assembly.UnifiedRegularEndgame
import GenMarkoff.General.Cage.CanonicalOrbitConnecting
import GenMarkoff.General.Cage.CanonicalTwoRootConnecting
import GenMarkoff.General.Cage.Connecting.AxisTwoAssembly

/-!
# The full-Vieta connecting cage beyond the reasonable cutoff

This file proves `canonicalFirstAxisPrimitiveSplitVietaCage_of_reasonableCutoff`:
beyond `reasonableAnalyticCutoff`, for coefficients over `ZMod p` with nonzero
multiplier, `aᵢ ^ 2 ≠ 4`, `(a₃, a₁) ≠ (0, 0)` and `(a₁, a₂) ≠ (0, 0)`, all
canonical first-axis primitive split points lie in one component of the full
Vieta group (`CanonicalFirstAxisPrimitiveSplitVietaCage`).

Each canonical point is first moved by rotations to a cage-ready one.  Two
cage-ready points are then normalized, inside their Vieta components, to
primitive regular connecting points on the second axis whose traces form a
connecting incidence pair, and the directed three-root relay
(`sameVietaComponent_of_primitiveRegularConnectingAxisTwo_of_reasonableCutoff`)
joins these normalized points.
-/

namespace GenMarkoff.General.Assembly

open GenMarkoff.General.Cage

noncomputable section

/-- Two points are Vieta-connected if the first can be normalized to an
obstruction-ready primitive regular connecting point on the second axis, the
second can be normalized relative to any such reference trace so that the two
traces form a connecting incidence pair, and the relay `hrelay` joins
normalized points whose traces form such a pair.  The incidence pair is
used in the order `(x', y')`, opposite to the order produced by `hy`. -/
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

/-- The connecting cage from its three ingredients: canonical points reach
cage-ready points (`hready`), cage-ready points admit the two second-axis
normalizations (`hobstruction`, `hpair`), and normalized points with a
connecting incidence pair of traces are Vieta-connected (`hrelay`). -/
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

/-- Beyond `reasonableAnalyticCutoff`, for coefficients with nonzero
multiplier, `aᵢ ^ 2 ≠ 4`, `(a₃, a₁) ≠ (0, 0)` and `(a₁, a₂) ≠ (0, 0)`, all
canonical first-axis primitive split points are Vieta-connected. -/
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
  -- Canonical points reach cage-ready points by rotations.
  · intro x hx
    obtain ⟨finish, hcomponent, hready⟩ :=
      canonicalFirstAxisPrimitiveSplit_reaches_cageReady_of_reasonableCutoff
        33 GenMarkoff.weightedShiftedTraceWeilBoundAssumption_thirtyThree
        (by norm_num) p hp a hA1 hA2 hA3 x hx
    exact
      ⟨finish,
        sameVietaComponent_of_sameRotationComponent hcomponent,
        hready⟩
  -- Obstruction-ready normalization, split by whether the first-axis
  -- centered norm is a square.
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
  -- Normalization relative to a reference trace `eta`, with the same case
  -- split.
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
  -- The directed three-root relay.
  · exact
      sameVietaComponent_of_primitiveRegularConnectingAxisTwo_of_reasonableCutoff
        p hp a hmultiplier hA1 hA2 hA3 hrelayMoving

end

end GenMarkoff.General.Assembly
