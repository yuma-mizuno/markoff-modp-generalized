module

public import GenMarkoff.General.Assembly.CageReadyCanonicalEndgame
public import GenMarkoff.General.Cage.Connecting.TwoRoot.Endpoint
public import GenMarkoff.General.Cage.Connecting.TwoRoot.PrimitiveWitness
public import BGS.NumberTheory.ExplicitDivisorBound
public import BGS.Markoff.Endgame.PrimitiveInclusionExclusion
public import GenMarkoff.General.Arithmetic.ReasonableCutoff

@[expose] public section

/-!
# Canonical nonsquare two-root connecting step

When the centered norm of a cage-ready canonical first-axis endpoint is
nonsquare, a point of a two-root cover (`ConnectingGoodTwoRootWitness`)
produces a point of the fixed generalized Markoff surface:

* the incidence root reconstructs a point with the prescribed middle trace;
* primitive connecting transitivity on the original first-axis fiber joins
  that point to the canonical endpoint; and
* the second root makes the centered norm of the new second-axis trace
  nonsquare.

The finite primitive sieves additionally make the new trace have nonzero
incidence obstruction, or make it a connecting incidence pair with a
prescribed reference trace.  Each version is stated under an explicit divisor
inequality and above `reasonableAnalyticCutoff`.  No coordinate permutation
is used.  Below, "Vieta-connected" means `SameVietaComponent`: the two points
lie in one Vieta-group orbit.
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff
open GenMarkoff.General.Assembly
open GenMarkoff.General.Endgame

noncomputable section

/-- Common step for the nonsquare case.  Given a selector that produces a
primitive, candidate-regular two-root witness whose middle trace satisfies
`P`, a cage-ready canonical first-axis endpoint with nonsquare centered norm
is Vieta-connected to a point whose second-axis trace is primitive split,
candidate-regular, satisfies `P`, and has nonsquare centered norm. -/
private theorem exists_axisTwo_of_connectingTwoRootWitnessSelector
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (a : Coefficients (ZMod p))
    (_hA1 : a.a1 ^ 2 ≠ 4)
    (_hA2 : a.a2 ^ 2 ≠ 4)
    (_hA3 : a.a3 ^ 2 ≠ 4)
    (_hmoving : (a.a3, a.a1) ≠ (0, 0))
    (x : SolutionSurface a)
    (hx : IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x)
    (hnonsquare :
      ¬ IsSquare
        (centeredNorm a.a2 a.a3 (traceAt a .first x.1)))
    (P : ZMod p → Prop)
    (hselect :
      ∀ (xi omegaInv : ZMod p),
        OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi →
        incidenceCenteredNormObstruction a xi ≠ 0 →
        ¬ IsSquare omegaInv →
        ∃q : (ZMod p)ˣ,
          ∃w : ConnectingGoodTwoRootWitness a xi omegaInv,
            w.1.middle = splitTorusTrace q ∧
              orderOf q = p - 1 ∧
                OrderedTraceCandidateRegular
                  a.a2 a.a3 a.a1 w.1.middle ∧
                  P w.1.middle) :
    ∃y : SolutionSurface a,
      SameVietaComponent x y ∧
        ∃q : (ZMod p)ˣ,
          traceAt a .second y.1 = splitTorusTrace q ∧
            orderOf q = Nat.card (ZMod p)ˣ ∧
              OrderedTraceCandidateRegular
                a.a2 a.a3 a.a1 (traceAt a .second y.1) ∧
                P (traceAt a .second y.1) ∧
                  ¬ IsSquare
                    (centeredNorm a.a3 a.a1
                      (traceAt a .second y.1)) := by
  obtain ⟨qx, heigenX, hqxOrder, hready⟩ := hx
  let u : ZMod p := x.1.x1
  let xi : ZMod p := traceAt a .first x.1
  have htraceX : traceAt a .first x.1 = xi := rfl
  have heigenXi : xi = splitTorusTrace qx := by
    simpa [xi] using heigenX
  have hregularXi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi := by
    simpa [xi] using hready.1
  have hobstructionXi :
      incidenceCenteredNormObstruction a xi ≠ 0 := by
    simpa [xi] using hready.2.2.1
  have hcoordinate :
      xi = orderedTrace a.multiplier a.a1 u := by
    rfl
  have hmultiplier : a.multiplier ≠ 0 := by
    intro hzero
    apply hregularXi.sigma_ne_zero
    rw [← actualSigma_eq_orderedTraceSigma
      a.multiplier a.a1 a.a2 a.a3 u xi hcoordinate]
    simp [actualSigma, actualAlpha, actualBeta, hzero]
  have hpTwo : p ≠ 2 := by omega
  have hchar : ringChar (ZMod p) ≠ 2 := by
    exact (ZMod.ringChar_zmod_n p).substr hpTwo
  obtain ⟨omegaInv, homegaInv⟩ :=
    FiniteField.exists_nonsquare hchar
  obtain ⟨qm, w, hwTrace, hqmOrder, hwRegular, hwP⟩ :=
    hselect xi omegaInv hregularXi hobstructionXi homegaInv
  have hcardUnits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  have hqmOrderCard :
      orderOf qm = Nat.card (ZMod p)ˣ :=
    hqmOrder.trans hcardUnits.symm
  obtain
      ⟨y, hxy, hyTrace, hyOrder, hyRegular, hyConnecting, hyP⟩ :=
    exists_sameVietaComponent_secondAxisPoint_of_connectingTwoRootData
      p hpTwo a hmultiplier x xi omegaInv w.1.middle
        w.1.firstRoot w.1.secondRoot htraceX qx qm
        heigenXi hqxOrder hregularXi
        (by simpa [xi] using hnonsquare)
        homegaInv w.1.firstEquation w.1.secondEquation w.2
        hwTrace hqmOrderCard hwRegular P hwP
  exact
    ⟨y, hxy, qm, hyTrace, hyOrder, hyRegular, hyP, hyConnecting⟩

/-- Under the explicit divisor inequality with coefficient `364`, a cage-ready
canonical first-axis endpoint with nonsquare centered norm is Vieta-connected
to a point whose second-axis trace is primitive split, candidate-regular in
the frame `(a₂, a₃, a₁)`, has nonzero `incidenceCenteredNormObstruction` for
`directedCycleLeftCoefficients a`, and has nonsquare centered norm
`centeredNorm a₃ a₁`. -/
theorem
    exists_sameVietaComponent_obstructionReadyPrimitiveConnectingAxisTwo_of_nonsquare_of_explicitInequality
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (x : SolutionSurface a)
    (hx : IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x)
    (hnonsquare :
      ¬ IsSquare
        (centeredNorm a.a2 a.a3 (traceAt a .first x.1)))
    (hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          (364 * Real.sqrt (p : ℝ)) < p) :
    ∃y : SolutionSurface a,
      SameVietaComponent x y ∧
        ∃q : (ZMod p)ˣ,
          traceAt a .second y.1 = splitTorusTrace q ∧
            orderOf q = Nat.card (ZMod p)ˣ ∧
              OrderedTraceCandidateRegular
                a.a2 a.a3 a.a1 (traceAt a .second y.1) ∧
                incidenceCenteredNormObstruction
                  (directedCycleLeftCoefficients a)
                    (traceAt a .second y.1) ≠ 0 ∧
                  ¬ IsSquare
                    (centeredNorm a.a3 a.a1
                      (traceAt a .second y.1)) := by
  exact
    exists_axisTwo_of_connectingTwoRootWitnessSelector
      p hpFive a hA1 hA2 hA3 hmoving x hx hnonsquare
        (fun t =>
          incidenceCenteredNormObstruction
            (directedCycleLeftCoefficients a) t ≠ 0)
        (by
          intro xi omegaInv hregular hobstruction homegaInv
          obtain ⟨q, w, hwTrace, hqOrder, hwRegular, hwObstruction⟩ :=
            exists_primitive_obstructionReady_connectingGoodTwoRootWitness_of_explicitInequality
              p hpFive a (directedCycleLeftCoefficients a)
                xi omegaInv hA1 hA2 hA3 hmoving
                hregular hobstruction
                (by
                  simpa [directedCycleLeftCoefficients] using hA2)
                (by
                  simpa [directedCycleLeftCoefficients] using hA3)
                homegaInv hexplicit
          exact
            ⟨q, w, hwTrace, hqOrder,
              by
                simpa [directedCycleLeftCoefficients] using hwRegular,
              hwObstruction⟩)

/-- Under the explicit divisor inequality with coefficient `388`, a cage-ready
canonical first-axis endpoint with nonsquare centered norm is Vieta-connected
to a point whose second-axis trace is primitive split, candidate-regular in
the frame `(a₂, a₃, a₁)`, forms a connecting incidence pair with the
prescribed trace `eta` for `directedCycleLeftCoefficients a`, and has
nonsquare centered norm `centeredNorm a₃ a₁`. -/
theorem
    exists_sameVietaComponent_primitiveConnectingPairAxisTwo_of_nonsquare_of_explicitInequality
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (eta : ZMod p)
    (hetaRegular :
      OrderedTraceCandidateRegular a.a2 a.a3 a.a1 eta)
    (hetaObstruction :
      incidenceCenteredNormObstruction
        (directedCycleLeftCoefficients a) eta ≠ 0)
    (x : SolutionSurface a)
    (hx : IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x)
    (hnonsquare :
      ¬ IsSquare
        (centeredNorm a.a2 a.a3 (traceAt a .first x.1)))
    (hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          (388 * Real.sqrt (p : ℝ)) < p) :
    ∃y : SolutionSurface a,
      SameVietaComponent x y ∧
        ∃q : (ZMod p)ˣ,
          traceAt a .second y.1 = splitTorusTrace q ∧
            orderOf q = Nat.card (ZMod p)ˣ ∧
              OrderedTraceCandidateRegular
                a.a2 a.a3 a.a1 (traceAt a .second y.1) ∧
                IsConnectingIncidencePair
                  (directedCycleLeftCoefficients a)
                    (traceAt a .second y.1) eta ∧
                  ¬ IsSquare
                    (centeredNorm a.a3 a.a1
                      (traceAt a .second y.1)) := by
  exact
    exists_axisTwo_of_connectingTwoRootWitnessSelector
      p hpFive a hA1 hA2 hA3 hmoving x hx hnonsquare
        (fun t =>
          IsConnectingIncidencePair
            (directedCycleLeftCoefficients a) t eta)
        (by
          intro xi omegaInv hregular hobstruction homegaInv
          obtain ⟨q, w, hwTrace, hqOrder, hwRegular, hwPair⟩ :=
            exists_primitive_connectingPair_connectingGoodTwoRootWitness_of_explicitInequality
              p hpFive a (directedCycleLeftCoefficients a)
                xi omegaInv eta hA1 hA2 hA3 hmoving
                hregular hobstruction
                (by
                  simpa [directedCycleLeftCoefficients] using hA2)
                (by
                  simpa [directedCycleLeftCoefficients] using hA3)
                (by
                  simpa [directedCycleLeftCoefficients] using
                    hetaRegular)
                hetaObstruction homegaInv hexplicit
          exact
            ⟨q, w, hwTrace, hqOrder,
              by
                simpa [directedCycleLeftCoefficients] using hwRegular,
              hwPair⟩)

/-- The conclusion of
`exists_sameVietaComponent_obstructionReadyPrimitiveConnectingAxisTwo_of_nonsquare_of_explicitInequality`
holds for every prime `p ≥ reasonableAnalyticCutoff`, where the divisor
inequality is automatic. -/
theorem cageReadyCanonicalFirstAxis_nonsquare_reaches_obstructionReadyPrimitiveConnectingAxisTwo_of_reasonableCutoff
    (p : ℕ)
    (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4) (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (x : SolutionSurface a)
    (hx : IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x)
    (hnonsquare :
      ¬ IsSquare (centeredNorm a.a2 a.a3 (traceAt a .first x.1))) :
    ∃ y : SolutionSurface a,
      SameVietaComponent x y ∧
        ∃ q : (ZMod p)ˣ,
          traceAt a .second y.1 = splitTorusTrace q ∧
            orderOf q = Nat.card (ZMod p)ˣ ∧
              OrderedTraceCandidateRegular a.a2 a.a3 a.a1
                  (traceAt a .second y.1) ∧
                incidenceCenteredNormObstruction
                    (directedCycleLeftCoefficients a)
                    (traceAt a .second y.1) ≠ 0 ∧
                  ¬ IsSquare
                    (centeredNorm a.a3 a.a1
                      (traceAt a .second y.1)) := by
  have hpFive : 5 ≤ p :=
    GenMarkoff.General.Explicit.five_le_reasonableAnalyticCutoff.trans hp
  have hexplicit :=
    GenMarkoff.General.Explicit.reasonable_primitiveTrace_explicitInequality_one
      hp (coefficient := 364) (by norm_num)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  apply
    exists_sameVietaComponent_obstructionReadyPrimitiveConnectingAxisTwo_of_nonsquare_of_explicitInequality
      p hpFive a hA1 hA2 hA3 hmoving x hx hnonsquare
  rw [hcard]
  simpa using hexplicit

/-- The conclusion of
`exists_sameVietaComponent_primitiveConnectingPairAxisTwo_of_nonsquare_of_explicitInequality`
holds for every prime `p ≥ reasonableAnalyticCutoff`, where the divisor
inequality is automatic. -/
theorem cageReadyCanonicalFirstAxis_nonsquare_reaches_primitiveConnectingPairAxisTwo_of_reasonableCutoff
    (p : ℕ)
    (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4) (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (eta : ZMod p)
    (hetaRegular : OrderedTraceCandidateRegular a.a2 a.a3 a.a1 eta)
    (hetaObstruction :
      incidenceCenteredNormObstruction
        (directedCycleLeftCoefficients a) eta ≠ 0)
    (x : SolutionSurface a)
    (hx : IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x)
    (hnonsquare :
      ¬ IsSquare (centeredNorm a.a2 a.a3 (traceAt a .first x.1))) :
    ∃ y : SolutionSurface a,
      SameVietaComponent x y ∧
        ∃ q : (ZMod p)ˣ,
          traceAt a .second y.1 = splitTorusTrace q ∧
            orderOf q = Nat.card (ZMod p)ˣ ∧
              OrderedTraceCandidateRegular a.a2 a.a3 a.a1
                  (traceAt a .second y.1) ∧
                IsConnectingIncidencePair
                    (directedCycleLeftCoefficients a)
                    (traceAt a .second y.1) eta ∧
                  ¬ IsSquare
                    (centeredNorm a.a3 a.a1
                      (traceAt a .second y.1)) := by
  have hpFive : 5 ≤ p :=
    GenMarkoff.General.Explicit.five_le_reasonableAnalyticCutoff.trans hp
  have hexplicit :=
    GenMarkoff.General.Explicit.reasonable_primitiveTrace_explicitInequality_one
      hp (coefficient := 388) (by norm_num)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  apply
    exists_sameVietaComponent_primitiveConnectingPairAxisTwo_of_nonsquare_of_explicitInequality
      p hpFive a hA1 hA2 hA3 hmoving
        eta hetaRegular hetaObstruction x hx hnonsquare
  rw [hcard]
  simpa using hexplicit

end

end GenMarkoff.General.Cage
