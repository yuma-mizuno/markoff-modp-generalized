module

public import GenMarkoff.General.Assembly.CageReadyCanonicalEndgame
public import GenMarkoff.General.Cage.Connecting.DirectedRelay
public import GenMarkoff.General.Cage.OrbitConnecting.PairPrimitiveWitness
public import GenMarkoff.General.Cage.OrbitConnecting.Reconstruction
public import GenMarkoff.General.Cage.OrbitConnecting.SquareClasses
public import BGS.NumberTheory.ExplicitDivisorBound
public import BGS.Markoff.Endgame.PrimitiveInclusionExclusion
public import GenMarkoff.General.Arithmetic.ReasonableCutoff

@[expose] public section

/-!
# Connecting a canonical primitive endpoint through its rotation coset

Let `x` satisfy `IsCageReadyCanonicalFirstAxisPrimitiveSplit` and suppose that
its centered norm `centeredNorm a₂ a₃ (traceAt a .first x)` is a square.  Then
the orbit-weight product `orderedTraceSigma` is a square `k ^ 2`, and the
three-root cover of `GenMarkoff.General.Cage.OrbitConnecting.ThreeRootEstimate`
(the two orbit-component radicands together with a nonsquare multiple of the
next centered norm) has a primitive point.

The reconstructed torus parameter is a square multiple `r * s ^ 2` of the
parameter `r` of `x`.  Since `rotation1` multiplies the parameter by `q ^ 2`
with `q` primitive, and `zpowers (q ^ 2)` is the full square subgroup, the
new point lies in the `rotation1` orbit of `x`.  Its second-axis trace is
primitive split and candidate-regular, and its centered norm
`centeredNorm a₃ a₁` is nonsquare.

The two main theorems hold above `reasonableAnalyticCutoff`; they add either a
nonzero incidence obstruction or a connecting incidence pair with a prescribed
trace `eta`, both for `directedCycleLeftCoefficients a`.  No coordinate
permutation of the fixed surface is used.  Below, "Vieta-connected" means
`SameVietaComponent`: the two points lie in one Vieta-group orbit.
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff
open GenMarkoff.General.Assembly
open GenMarkoff.General.Endgame
open GenMarkoff.General.MiddleGame

noncomputable section

/-- If `xi ^ 2 ≠ 4` and the centered norm `centeredNorm B C xi` is a square,
then the normalized orbit-weight product `orderedTraceSigma A B C xi` is a
square. -/
theorem orderedTraceSigma_isSquare_of_centeredNorm
    {K : Type*} [Field K] (A B C xi : K)
    (hD : xi ^ 2 - 4 ≠ 0)
    (hnorm : IsSquare (centeredNorm B C xi)) :
    IsSquare (orderedTraceSigma A B C xi) := by
  obtain ⟨r, hr⟩ := hnorm
  refine ⟨(xi + A) * r / (xi ^ 2 - 4), ?_⟩
  simp only [orderedTraceSigma, centeredNorm, discriminant] at hr ⊢
  rw [hr]
  field_simp [hD]

/-- Common step for the square-norm case.  Given a selector that produces a
primitive, candidate-regular good orbit-connecting witness whose middle trace
satisfies `P`, a cage-ready canonical first-axis endpoint with square centered
norm is Vieta-connected to a point whose second-axis trace is primitive split,
candidate-regular, satisfies `P`, and has nonsquare centered norm. -/
private theorem exists_axisTwo_of_orbitConnectingWitnessSelector
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (x : SolutionSurface a)
    (hx : IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x)
    (hsquare :
      IsSquare
        (centeredNorm a.a2 a.a3 (traceAt a .first x.1)))
    (P : ZMod p → Prop)
    (hselect :
      ∀ (alpha beta gamma k omegaInv : ZMod p),
        alpha ≠ 0 →
        alpha * beta =
          orderedTraceSigma a.a1 a.a2 a.a3
            (traceAt a .first x.1) →
        gamma =
          orderedTraceGamma a.a1 a.a2 a.a3
            (traceAt a .first x.1) →
        alpha * beta = k ^ 2 →
        omegaInv ≠ 0 →
        (∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
          SevenHyperellipticPlanesAbsolutelyIrreducible
            (orbitComponentPlusCosetPulledRadicand
              alpha gamma k d)
            (orbitComponentMinusCosetPulledRadicand
              alpha gamma k d)
            (Polynomial.C omegaInv *
              centeredNormPulledRadicand a.a3 a.a1 d)) →
        ∃ v : (ZMod p)ˣ,
          ∃ w :
              OrbitConnectingGoodThreeRootWitness
                alpha gamma k omegaInv a.a3 a.a1,
            w.1.middle = splitTorusTrace v ∧
              orderOf v = p - 1 ∧
                OrderedTraceCandidateRegular
                  a.a2 a.a3 a.a1 w.1.middle ∧
                  P w.1.middle) :
    ∃ y : SolutionSurface a,
      SameVietaComponent x y ∧
        ∃ v : (ZMod p)ˣ,
          traceAt a .second y.1 = splitTorusTrace v ∧
            orderOf v = Nat.card (ZMod p)ˣ ∧
              OrderedTraceCandidateRegular
                a.a2 a.a3 a.a1 (traceAt a .second y.1) ∧
                P (traceAt a .second y.1) ∧
                  ¬ IsSquare
                    (centeredNorm a.a3 a.a1
                      (traceAt a .second y.1)) := by
  -- Step 1: write `x` as `fiberPoint1 a u xi q r` on its first-coordinate
  -- fiber.
  obtain ⟨q, heigen, hqOrder, hready⟩ := hx
  let u : ZMod p := x.1.x1
  let xi : ZMod p := traceAt a .first x.1
  have heigenXi : xi = splitTorusTrace q := heigen
  have hcoordinate :
      xi = orderedTrace a.multiplier a.a1 u := by
    rfl
  have hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi := by
    simpa [xi] using hready.1
  have hobstruction :
      incidenceCenteredNormObstruction a xi ≠ 0 := by
    simpa [xi] using hready.2.2.1
  have hD : discriminant xi ≠ 0 := by
    simpa [discriminant] using hregular.1
  have hconic :
      fiberConic a.a2 a.a3 u xi x.1.x2 x.1.x3 = 0 := by
    have hsurface := x.property
    rw [IsSolution, polynomial_fixed_first] at hsurface
    simpa [u, xi, traceAt, orderedTrace] using hsurface
  obtain ⟨r, hrPair⟩ :=
    exists_unit_fiberPair_eq_of_candidateRegular
      a.multiplier a.a1 a.a2 a.a3 u xi q
        (x.1.x2, x.1.x3) hconic hcoordinate
        (by simpa [xi] using heigen) hregular
  have hrPoint :
      fiberPoint1 a u xi (q : ZMod p) (r : ZMod p) = x.1 := by
    apply Point.ext
    · rfl
    · exact congrArg Prod.fst hrPair
    · exact congrArg Prod.snd hrPair
  -- Step 2: the orbit weights `alpha`, `beta` and shift `gamma` of the
  -- second coordinate; the weight product is the square `k ^ 2`.
  let alpha : ZMod p :=
    actualAlpha a.multiplier * (r : ZMod p)
  let beta : ZMod p :=
    actualBeta a.multiplier a.a2 a.a3 u xi / (r : ZMod p)
  let gamma : ZMod p :=
    actualGammaFirst a.multiplier a.a2 a.a3 u xi
  have hproduct :
      alpha * beta =
        orderedTraceSigma a.a1 a.a2 a.a3 xi := by
    calc
      alpha * beta =
          actualSigma a.multiplier a.a2 a.a3 u xi := by
        simpa [alpha, beta] using
          actual_firstDirected_coset_weights_mul
            a.multiplier a.a2 a.a3 u xi r
      _ = orderedTraceSigma a.a1 a.a2 a.a3 xi :=
        actualSigma_eq_orderedTraceSigma
          a.multiplier a.a1 a.a2 a.a3 u xi hcoordinate
  have hgamma :
      gamma = orderedTraceGamma a.a1 a.a2 a.a3 xi := by
    exact actualGammaFirst_eq_orderedTraceGamma
      a.multiplier a.a1 a.a2 a.a3 u xi hD hcoordinate
  have hsigmaSquare :
      IsSquare (orderedTraceSigma a.a1 a.a2 a.a3 xi) :=
    orderedTraceSigma_isSquare_of_centeredNorm
      a.a1 a.a2 a.a3 xi
        (by
          simpa only [eval_orderedTraceDiscriminantPolynomial] using
            hregular.1)
        (by simpa [xi] using hsquare)
  obtain ⟨k, hk⟩ := hsigmaSquare
  have hsquareProduct : alpha * beta = k ^ 2 := by
    calc
      alpha * beta =
          orderedTraceSigma a.a1 a.a2 a.a3 xi := hproduct
      _ = k ^ 2 := by simpa [pow_two] using hk
  have hmultiplier : a.multiplier ≠ 0 := by
    intro hzero
    apply hregular.sigma_ne_zero
    rw [← actualSigma_eq_orderedTraceSigma
      a.multiplier a.a1 a.a2 a.a3 u xi hcoordinate]
    simp [actualSigma, actualAlpha, actualBeta, hzero]
  have halpha : alpha ≠ 0 := by
    exact mul_ne_zero
      (actualAlpha_ne_zero a.multiplier hmultiplier)
      (Units.ne_zero r)
  have hbeta : beta ≠ 0 := by
    exact div_ne_zero
      (actualBeta_ne_zero_of_candidateRegular
        a.multiplier a.a1 a.a2 a.a3 u xi
          hcoordinate hregular)
      (Units.ne_zero r)
  -- Step 3: fix a nonsquare `omegaInv`, verify absolute irreducibility of
  -- the seven hyperelliptic planes, and apply the selector.
  have hpTwo : p ≠ 2 := by omega
  have htwo : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have hchar : ringChar (ZMod p) ≠ 2 := by
    exact (ZMod.ringChar_zmod_n p).substr hpTwo
  obtain ⟨omegaInv, homegaInv⟩ :=
    FiniteField.exists_nonsquare hchar
  have homegaInvZero : omegaInv ≠ 0 := by
    intro hzero
    apply homegaInv
    rw [hzero]
    exact IsSquare.zero
  have habsolute :
      ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
        SevenHyperellipticPlanesAbsolutelyIrreducible
          (orbitComponentPlusCosetPulledRadicand
            alpha gamma k d)
          (orbitComponentMinusCosetPulledRadicand
            alpha gamma k d)
          (Polynomial.C omegaInv *
            centeredNormPulledRadicand a.a3 a.a1 d) := by
    intro d hdvd hd
    exact
      orbitConnectingSevenScaledHyperellipticPlanes_absolutelyIrreducible
        htwo hA1 hA2 hA3 hmoving hregular hobstruction
          halpha hproduct hgamma hsquareProduct hd
          (natCast_ne_zero_zmod_of_dvd_card_units p d hd hdvd)
          homegaInvZero
  obtain ⟨v, w, hwTrace, hvOrder, hwRegular, hwP⟩ :=
    hselect alpha beta gamma k omegaInv halpha
      (by simpa [xi] using hproduct)
      (by simpa [xi] using hgamma)
      hsquareProduct homegaInvZero habsolute
  -- Step 4: reconstruct `s`; the parameter `r * s ^ 2` lies in the
  -- `rotation1` orbit of `r`, which defines the target point `y`.
  obtain ⟨s, hsTrace⟩ :=
    exists_squareCosetParameter_of_orbitConnectingThreeRootWitness
      htwo halpha hbeta hsquareProduct w.1
  have hqTop : Subgroup.zpowers q = ⊤ :=
    zpowers_eq_top_of_orderOf_eq_natCard q hqOrder
  have hsqSubgroup :
      Subgroup.zpowers (q ^ 2) = Subgroup.square (ZMod p)ˣ :=
    zpowers_sq_eq_square_of_zpowers_eq_top q hqTop
  have hsMem : s ^ 2 ∈ Subgroup.zpowers (q ^ 2) := by
    rw [hsqSubgroup, Subgroup.mem_square]
    exact ⟨s, by simp [pow_two]⟩
  let h : Subgroup.zpowers (q ^ 2) := ⟨s ^ 2, hsMem⟩
  obtain ⟨n, hn⟩ :=
    exists_iterate_fiberPoint1_eq_mul_zpowers_sq
      a u xi q r hD
        heigenXi hcoordinate h
  have hySolution :
      IsSolution a
        (fiberPoint1 a u xi (q : ZMod p)
          ((r * s ^ 2 : (ZMod p)ˣ) : ZMod p)) :=
    fiberPoint1_isSolution
      a u xi (q : ZMod p)
        ((r * s ^ 2 : (ZMod p)ˣ) : ZMod p)
      hD (Units.ne_zero q) (Units.ne_zero (r * s ^ 2))
      (by
        simpa only [splitTorusTrace, Units.val_inv_eq_inv_val] using
          heigenXi)
      hcoordinate
  let y : SolutionSurface a :=
    ⟨fiberPoint1 a u xi (q : ZMod p)
      ((r * s ^ 2 : (ZMod p)ˣ) : ZMod p), hySolution⟩
  have hxy : SameVietaComponent x y := by
    apply sameVietaComponent_of_iterate_rotation1 a x y n
    rw [← hrPoint]
    simpa [y, h] using hn
  -- Step 5: the second-axis trace of `y` is the witness middle trace, so the
  -- witness properties transfer to `y`.
  have hyTraceMiddle :
      traceAt a .second y.1 = w.1.middle := by
    -- `traceAt a .second` unfolds to `orderedTrace a.multiplier a.a2 _.x2`
    -- and `y.1` is the `fiberPoint1` point by definition; restate so the
    -- calc below can rewrite its `x2` coordinate.
    change
      orderedTrace a.multiplier a.a2
          (fiberPoint1 a u xi (q : ZMod p)
            ((r * s ^ 2 : (ZMod p)ˣ) : ZMod p)).x2 =
        w.1.middle
    -- The coercion of a unit product is the product of coercions by `rfl`
    -- (`Units.val_mul`); split it so the parameter has the form `r * s ^ 2`.
    rw [show
      ((r * s ^ 2 : (ZMod p)ˣ) : ZMod p) =
        (r : ZMod p) * ((s ^ 2 : (ZMod p)ˣ) : ZMod p) by
          rfl]
    calc
      orderedTrace a.multiplier a.a2
          (fiberPoint1 a u xi (q : ZMod p)
            ((r : ZMod p) * ((s ^ 2 : (ZMod p)ˣ) : ZMod p))).x2 =
          weightedSplitTorusTrace alpha beta (s ^ 2) + gamma := by
        simpa only [alpha, beta, gamma, Units.val_mul] using
          orderedTrace_fiberPoint1_mul_eq_weightedSplitTorusTrace
            a u xi q r (s ^ 2)
      _ = w.1.middle := hsTrace
  have hyTrace :
      traceAt a .second y.1 = splitTorusTrace v :=
    hyTraceMiddle.trans hwTrace
  have hyRegular :
      OrderedTraceCandidateRegular
        a.a2 a.a3 a.a1 (traceAt a .second y.1) := by
    rw [hyTraceMiddle]
    exact hwRegular
  have hyConnecting :
      ¬ IsSquare
        (centeredNorm a.a3 a.a1
          (traceAt a .second y.1)) := by
    rw [hyTraceMiddle]
    exact
      centeredNorm_not_isSquare_of_orbitConnectingGoodThreeRootWitness
        homegaInv w
  have hyP : P (traceAt a .second y.1) := by
    rw [hyTraceMiddle]
    exact hwP
  have hcardUnits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  have hvOrderCard : orderOf v = Nat.card (ZMod p)ˣ :=
    hvOrder.trans hcardUnits.symm
  exact
    ⟨y, hxy, v, hyTrace, hvOrderCard, hyRegular, hyP, hyConnecting⟩

/-- For primes `p ≥ reasonableAnalyticCutoff`, a cage-ready canonical
first-axis endpoint with square centered norm is Vieta-connected to a point
whose second-axis trace is primitive split, candidate-regular in the frame
`(a₂, a₃, a₁)`, has nonzero `incidenceCenteredNormObstruction` for
`directedCycleLeftCoefficients a`, and has nonsquare centered norm
`centeredNorm a₃ a₁`. -/
theorem cageReadyCanonicalFirstAxis_square_reaches_obstructionReadyPrimitiveConnectingAxisTwo_of_reasonableCutoff
    (p : ℕ)
    (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4) (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (x : SolutionSurface a)
    (hx : IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x)
    (hsquare :
      IsSquare (centeredNorm a.a2 a.a3 (traceAt a .first x.1))) :
    ∃ y : SolutionSurface a,
      SameVietaComponent x y ∧
        ∃ v : (ZMod p)ˣ,
          traceAt a .second y.1 = splitTorusTrace v ∧
            orderOf v = Nat.card (ZMod p)ˣ ∧
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
      hp (coefficient := 984) (by norm_num)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  exact
    exists_axisTwo_of_orbitConnectingWitnessSelector
      p hpFive a hA1 hA2 hA3 hmoving x hx hsquare
        (fun t =>
          incidenceCenteredNormObstruction
            (directedCycleLeftCoefficients a) t ≠ 0)
        (by
          intro alpha beta gamma k omegaInv _ _ _ _
            homegaInvZero habsolute
          obtain
              ⟨v, w, hwTrace, hvOrder, hwRegular, hwObstruction⟩ :=
            exists_primitive_obstructionReady_orbitConnectingGoodThreeRootWitness_of_explicitInequality
              p hpFive (directedCycleLeftCoefficients a)
              alpha gamma k omegaInv a.a3 a.a1
              (by simpa [directedCycleLeftCoefficients] using hA2)
              (by simpa [directedCycleLeftCoefficients] using hA3)
              homegaInvZero habsolute
              (by rw [hcard]; simpa using hexplicit)
          exact
            ⟨v, w, hwTrace, hvOrder,
              by
                simpa [directedCycleLeftCoefficients] using hwRegular,
              hwObstruction⟩)

/-- For primes `p ≥ reasonableAnalyticCutoff`, a cage-ready canonical
first-axis endpoint with square centered norm is Vieta-connected to a point
whose second-axis trace is primitive split, candidate-regular in the frame
`(a₂, a₃, a₁)`, forms a connecting incidence pair with the prescribed trace
`eta` for `directedCycleLeftCoefficients a`, and has nonsquare centered norm
`centeredNorm a₃ a₁`. -/
theorem cageReadyCanonicalFirstAxis_square_reaches_primitiveConnectingPairAxisTwo_of_reasonableCutoff
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
    (hsquare :
      IsSquare (centeredNorm a.a2 a.a3 (traceAt a .first x.1))) :
    ∃ y : SolutionSurface a,
      SameVietaComponent x y ∧
        ∃ v : (ZMod p)ˣ,
          traceAt a .second y.1 = splitTorusTrace v ∧
            orderOf v = Nat.card (ZMod p)ˣ ∧
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
      hp (coefficient := 1032) (by norm_num)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  exact
    exists_axisTwo_of_orbitConnectingWitnessSelector
      p hpFive a hA1 hA2 hA3 hmoving x hx hsquare
        (fun t =>
          IsConnectingIncidencePair
            (directedCycleLeftCoefficients a) t eta)
        (by
          intro alpha beta gamma k omegaInv _ _ _ _
            homegaInvZero habsolute
          obtain ⟨v, w, hwTrace, hvOrder, hwRegular, hwPair⟩ :=
            exists_primitive_connectingPair_orbitConnectingGoodThreeRootWitness_of_explicitInequality
              p hpFive (directedCycleLeftCoefficients a) eta
              alpha gamma k omegaInv a.a3 a.a1
              (by simpa [directedCycleLeftCoefficients] using hA2)
              (by simpa [directedCycleLeftCoefficients] using hA3)
              (by
                simpa [directedCycleLeftCoefficients] using
                  hetaRegular)
              hetaObstruction homegaInvZero habsolute
              (by rw [hcard]; simpa using hexplicit)
          exact
            ⟨v, w, hwTrace, hvOrder,
              by
                simpa [directedCycleLeftCoefficients] using hwRegular,
              hwPair⟩)

end

end GenMarkoff.General.Cage
