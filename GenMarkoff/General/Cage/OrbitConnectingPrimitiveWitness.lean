import GenMarkoff.General.Cage.ConnectingPrimitiveWitness
import GenMarkoff.General.Cage.OrbitConnectingThreeRootEstimate

/-!
# Candidate-regular primitive orbit-connecting witnesses

The conditional orbit-connecting three-root estimate gives exact-order
witness pairs after one-sided Möbius inversion.  The middle connecting
fiber also needs candidate regularity in a supplied ordered coefficient
frame `(A, B, C)`.

For each fixed middle trace there are at most eight three-root witnesses
and at most two split-torus parameters.  Since the ordered safe polynomial
has at most ten roots, at most `8 * 2 * 10 = 160` exact-order pairs are
candidate-irregular.  Increasing the square-root error coefficient from
`792` to `952 = 792 + 160` absorbs this finite exceptional set.

Geometric irreducibility of all seven pulled hyperelliptic planes remains
an explicit hypothesis.
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff Polynomial
open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

/-- Exact-order orbit-connecting witness pairs after Möbius inversion. -/
noncomputable abbrev orbitConnectingGoodThreeRootExactOrderSolutions
    (p : ℕ) [Fact p.Prime]
    (alpha gamma k omegaInv centerB centerC : ZMod p) :=
  BGS.rightTraceExactOrderSolutions
    (fun w :
      OrbitConnectingGoodThreeRootWitness
        alpha gamma k omegaInv centerB centerC => w.1.middle)
    (splitTorusTrace : (ZMod p)ˣ → ZMod p)
    (Nat.card (ZMod p)ˣ)

/-- For one fixed middle trace, the three square-root choices give at most
eight good orbit-connecting witnesses. -/
theorem natCard_orbitConnectingGoodThreeRootWitness_fixed_middle_le_eight
    (p : ℕ) [Fact p.Prime]
    (alpha gamma k omegaInv centerB centerC t : ZMod p) :
    Nat.card
        {w :
            OrbitConnectingGoodThreeRootWitness
              alpha gamma k omegaInv centerB centerC //
          w.1.middle = t} ≤ 8 := by
  let f : (ZMod p)[X] :=
    C (orbitComponentRadicand alpha k (t - gamma))
  let g : (ZMod p)[X] :=
    C (orbitOppositeComponentRadicand alpha k (t - gamma))
  let h : (ZMod p)[X] :=
    C (omegaInv * centeredNorm centerB centerC t)
  let target := ThreeSquareRootFiber f g h 0
  let embedding :
      {w :
          OrbitConnectingGoodThreeRootWitness
            alpha gamma k omegaInv centerB centerC //
        w.1.middle = t} ↪ target :=
    { toFun := fun w =>
        { firstRoot := w.1.1.plusRoot
          secondRoot := w.1.1.minusRoot
          thirdRoot := w.1.1.thirdRoot
          firstEquation := by
            simpa [f] using
              w.1.1.plusEquation.trans
                (congrArg
                  (fun s =>
                    orbitComponentRadicand alpha k (s - gamma))
                  w.2)
          secondEquation := by
            simpa [g] using
              w.1.1.minusEquation.trans
                (congrArg
                  (fun s =>
                    orbitOppositeComponentRadicand alpha k (s - gamma))
                  w.2)
          thirdEquation := by
            simpa [h] using
              w.1.1.thirdEquation.trans
                (congrArg
                  (fun s =>
                    omegaInv * centeredNorm centerB centerC s)
                  w.2) }
      inj' := by
        intro w z hwz
        apply Subtype.ext
        apply Subtype.ext
        exact OrbitConnectingThreeRootWitness.ext
          (w.2.trans z.2.symm)
          (congrArg (fun q : target => q.firstRoot) hwz)
          (congrArg (fun q : target => q.secondRoot) hwz)
          (congrArg (fun q : target => q.thirdRoot) hwz) }
  exact
    (Nat.card_le_card_of_injective
      embedding.toFun embedding.injective).trans
      (natCard_threeSquareRootFiber_le_eight f g h 0)

/-- A fixed middle trace supports at most sixteen exact-order
orbit-connecting pairs. -/
theorem
    orbitConnectingGoodThreeRootExactOrderSolutions_fixed_middle_card_le_sixteen
    (p : ℕ) [Fact p.Prime]
    (alpha gamma k omegaInv centerB centerC t : ZMod p) :
    ((orbitConnectingGoodThreeRootExactOrderSolutions
        p alpha gamma k omegaInv centerB centerC).filter fun z =>
          z.1.1.middle = t).card ≤ 16 := by
  classical
  let primitive :=
    orbitConnectingGoodThreeRootExactOrderSolutions
      p alpha gamma k omegaInv centerB centerC
  let source := ↥(primitive.filter fun z => z.1.1.middle = t)
  let target :=
    {w :
        OrbitConnectingGoodThreeRootWitness
          alpha gamma k omegaInv centerB centerC //
      w.1.middle = t} ×
    {q : (ZMod p)ˣ // splitTorusTrace q = t}
  let embedding : source ↪ target :=
    { toFun := fun z =>
        (⟨z.1.1, (Finset.mem_filter.mp z.2).2⟩,
          ⟨z.1.2, by
            have hz :=
              (BGS.mem_rightTraceExactOrderSolutions_iff
                (fun w :
                  OrbitConnectingGoodThreeRootWitness
                    alpha gamma k omegaInv centerB centerC =>
                      w.1.middle)
                (splitTorusTrace : (ZMod p)ˣ → ZMod p)
                (Nat.card (ZMod p)ˣ) z.1).mp
                (Finset.mem_filter.mp z.2).1
            exact hz.1.symm.trans (Finset.mem_filter.mp z.2).2⟩)
      inj' := by
        intro z w hzw
        apply Subtype.ext
        exact Prod.ext
          (congrArg (fun q : target =>
            (q.1.1 :
              OrbitConnectingGoodThreeRootWitness
                alpha gamma k omegaInv centerB centerC)) hzw)
          (congrArg (fun q : target => (q.2.1 : (ZMod p)ˣ)) hzw) }
  have hcard :=
    Nat.card_le_card_of_injective embedding.toFun embedding.injective
  change Nat.card source ≤ Nat.card target at hcard
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_prod] at hcard
  have hwitness :=
    natCard_orbitConnectingGoodThreeRootWitness_fixed_middle_le_eight
      p alpha gamma k omegaInv centerB centerC t
  have hunit := natCard_splitTorusTrace_fiber_le_two p t
  exact hcard.trans <|
    (Nat.mul_le_mul hwitness hunit).trans (by norm_num)

/-- Candidate-irregular exact-order orbit-connecting pairs for a supplied
ordered coefficient frame. -/
noncomputable def
    irregularOrbitConnectingGoodThreeRootExactOrderSolutions
    (p : ℕ) [Fact p.Prime]
    (frameA frameB frameC : ZMod p)
    (alpha gamma k omegaInv centerB centerC : ZMod p) :
    Finset
      (OrbitConnectingGoodThreeRootWitness
          alpha gamma k omegaInv centerB centerC ×
        (ZMod p)ˣ) := by
  classical
  exact
    (orbitConnectingGoodThreeRootExactOrderSolutions
      p alpha gamma k omegaInv centerB centerC).filter fun z =>
        ¬ OrderedTraceCandidateRegular
          frameA frameB frameC z.1.1.middle

/-- At most `16 * 10 = 160` exact-order orbit-connecting pairs are
candidate-irregular in the supplied ordered frame. -/
theorem
    irregularOrbitConnectingGoodThreeRootExactOrderSolutions_card_le_oneHundredSixty
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (frameA frameB frameC : ZMod p)
    (alpha gamma k omegaInv centerB centerC : ZMod p)
    (hFrameA : frameA ^ 2 ≠ 4)
    (hFrameB : frameB ^ 2 ≠ 4) :
    (irregularOrbitConnectingGoodThreeRootExactOrderSolutions
      p frameA frameB frameC
        alpha gamma k omegaInv centerB centerC).card ≤ 160 := by
  classical
  let primitive :=
    orbitConnectingGoodThreeRootExactOrderSolutions
      p alpha gamma k omegaInv centerB centerC
  let bad :=
    irregularOrbitConnectingGoodThreeRootExactOrderSolutions
      p frameA frameB frameC
        alpha gamma k omegaInv centerB centerC
  let traceValue :
      OrbitConnectingGoodThreeRootWitness
          alpha gamma k omegaInv centerB centerC ×
        (ZMod p)ˣ → ZMod p :=
    fun z => z.1.1.middle
  have hfiber :
      ∀ t ∈ bad.image traceValue,
        (bad.filter fun z => traceValue z = t).card ≤ 16 := by
    intro t _
    calc
      (bad.filter fun z => traceValue z = t).card ≤
          (primitive.filter fun z => z.1.1.middle = t).card := by
        apply Finset.card_le_card
        intro z hz
        have hzBad := (Finset.mem_filter.mp hz).1
        have hzTrace := (Finset.mem_filter.mp hz).2
        change z ∈
          irregularOrbitConnectingGoodThreeRootExactOrderSolutions
            p frameA frameB frameC
              alpha gamma k omegaInv centerB centerC at hzBad
        rw [irregularOrbitConnectingGoodThreeRootExactOrderSolutions]
          at hzBad
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hzBad).1, hzTrace⟩
      _ ≤ 16 :=
        orbitConnectingGoodThreeRootExactOrderSolutions_fixed_middle_card_le_sixteen
          p alpha gamma k omegaInv centerB centerC t
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hsafe :
      orderedTraceSafePolynomial frameA frameB frameC ≠ 0 :=
    orderedTraceSafePolynomial_ne_zero
      frameA frameB frameC htwo hFrameA hFrameB
  have himage :
      bad.image traceValue ⊆
        (orderedTraceSafePolynomial
          frameA frameB frameC).roots.toFinset := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨z, hz, rfl⟩
    have hirregular :
        ¬ OrderedTraceCandidateRegular
          frameA frameB frameC z.1.1.middle :=
      (Finset.mem_filter.mp hz).2
    have hzero :
        eval z.1.1.middle
          (orderedTraceSafePolynomial frameA frameB frameC) = 0 := by
      by_contra hne
      exact hirregular
        ((orderedTraceSafePolynomial_eval_ne_zero_iff
          frameA frameB frameC z.1.1.middle).mp hne)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hsafe]
    exact hzero
  have himageCard :
      (bad.image traceValue).card ≤
        (orderedTraceSafePolynomial
          frameA frameB frameC).roots.toFinset.card :=
    Finset.card_le_card himage
  have hroots :
      (orderedTraceSafePolynomial
        frameA frameB frameC).roots.toFinset.card ≤ 10 :=
    orderedTraceSafePolynomial_roots_card_le
      frameA frameB frameC
  change bad.card ≤ 160
  calc
    bad.card ≤ 16 * (bad.image traceValue).card :=
      Finset.card_le_mul_card_image bad 16
        (fun t ht => hfiber t ht)
    _ ≤ 16 *
        (orderedTraceSafePolynomial
          frameA frameB frameC).roots.toFinset.card :=
      Nat.mul_le_mul_left 16 himageCard
    _ ≤ 16 * 10 := Nat.mul_le_mul_left 16 hroots
    _ = 160 := by norm_num

/-- A Möbius margin of `160` beyond the divisor error produces a primitive
orbit-connecting witness whose middle is candidate-regular in the supplied
frame. -/
theorem
    exists_primitive_candidateRegular_orbitConnectingGoodThreeRootWitness_of_margin
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (frameA frameB frameC : ZMod p)
    (alpha gamma k omegaInv centerB centerC : ZMod p)
    (hFrameA : frameA ^ 2 ≠ 4)
    (hFrameB : frameB ^ 2 ≠ 4)
    (homegaInv : omegaInv ≠ 0)
    (habsolute :
      ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
        SevenHyperellipticPlanesAbsolutelyIrreducible
          (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
          (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
          (C omegaInv *
            centeredNormPulledRadicand centerB centerC d))
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            (792 * Real.sqrt (p : ℝ)) +
          160 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p 1) :
    ∃ q : (ZMod p)ˣ,
      ∃ w :
          OrbitConnectingGoodThreeRootWitness
            alpha gamma k omegaInv centerB centerC,
        w.1.middle = splitTorusTrace q ∧
          orderOf q = p - 1 ∧
            OrderedTraceCandidateRegular
              frameA frameB frameC w.1.middle := by
  classical
  let leftTrace :
      OrbitConnectingGoodThreeRootWitness
          alpha gamma k omegaInv centerB centerC →
        ZMod p :=
    fun w => w.1.middle
  let rightTrace : (ZMod p)ˣ → ZMod p :=
    splitTorusTrace
  let primitive :=
    BGS.rightTraceExactOrderSolutions
      leftTrace rightTrace (Nat.card (ZMod p)ˣ)
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hRange :
      ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
        |(Nat.card
            (BGS.rightPowerTraceRangeSolutions
              leftTrace rightTrace d) : ℝ) -
            (p : ℝ) / d| ≤
          792 * Real.sqrt (p : ℝ) := by
    intro d hdvd hd
    simpa [leftTrace, rightTrace,
      orbitConnectingGoodThreeRootPowerRangeSolutions] using
      (orbitConnectingGoodThreeRootPowerRangeSolutions_card_error_le
        p hchar d hdvd hd homegaInv
          (habsolute d hdvd hd))
  have henvelope :
      |(primitive.card : ℝ) -
          primitiveTraceMoebiusMainTerm
            (Nat.card (ZMod p)ˣ) p 1| ≤
        ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
          (792 * Real.sqrt (p : ℝ)) := by
    simpa [primitive, leftTrace, rightTrace,
      primitiveTraceMoebiusMainTerm] using
      (BGS.rightTraceExactOrderSolutions_card_error_le_moebiusMain
        leftTrace rightTrace (fun d => (p : ℝ) / d)
        (792 * Real.sqrt (p : ℝ)) hRange)
  have hlower :
      primitiveTraceMoebiusMainTerm
            (Nat.card (ZMod p)ˣ) p 1 -
          (primitive.card : ℝ) ≤
        |(primitive.card : ℝ) -
          primitiveTraceMoebiusMainTerm
            (Nat.card (ZMod p)ˣ) p 1| := by
    simpa only [neg_sub] using
      neg_le_abs
        ((primitive.card : ℝ) -
          primitiveTraceMoebiusMainTerm
            (Nat.card (ZMod p)ˣ) p 1)
  have hcardReal : (160 : ℝ) < primitive.card := by
    linarith
  have hcard : 160 < primitive.card := by
    exact_mod_cast hcardReal
  have hexists :
      ∃ z ∈ primitive,
        OrderedTraceCandidateRegular
          frameA frameB frameC z.1.1.middle := by
    by_contra hnone
    push Not at hnone
    have hsubset :
        primitive ⊆
          irregularOrbitConnectingGoodThreeRootExactOrderSolutions
            p frameA frameB frameC
              alpha gamma k omegaInv centerB centerC := by
      intro z hz
      rw [irregularOrbitConnectingGoodThreeRootExactOrderSolutions,
        Finset.mem_filter]
      exact ⟨hz, hnone z hz⟩
    have hle := Finset.card_le_card hsubset
    have hbad :=
      irregularOrbitConnectingGoodThreeRootExactOrderSolutions_card_le_oneHundredSixty
        p hpFive frameA frameB frameC
          alpha gamma k omegaInv centerB centerC
          hFrameA hFrameB
    exact (Nat.not_le_of_lt hcard) (hle.trans hbad)
  obtain ⟨z, hz, hregular⟩ := hexists
  have hz' :=
    (BGS.mem_rightTraceExactOrderSolutions_iff
      leftTrace rightTrace (Nat.card (ZMod p)ˣ) z).mp hz
  rcases z with ⟨w, q⟩
  refine ⟨q, w, ?_, ?_, ?_⟩
  · simpa [leftTrace, rightTrace] using hz'.1
  · rw [Nat.card_units, Nat.card_zmod] at hz'
    exact hz'.2
  · exact hregular

/-- The explicit inequality with coefficient `952` absorbs the full
candidate-irregular exceptional set. -/
theorem
    exists_primitive_candidateRegular_orbitConnectingGoodThreeRootWitness_of_explicitInequality
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (frameA frameB frameC : ZMod p)
    (alpha gamma k omegaInv centerB centerC : ZMod p)
    (hFrameA : frameA ^ 2 ≠ 4)
    (hFrameB : frameB ^ 2 ≠ 4)
    (homegaInv : omegaInv ≠ 0)
    (habsolute :
      ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
        SevenHyperellipticPlanesAbsolutelyIrreducible
          (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
          (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
          (C omegaInv *
            centeredNormPulledRadicand centerB centerC d))
    (hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          (952 * Real.sqrt (p : ℝ)) < p) :
    ∃ q : (ZMod p)ˣ,
      ∃ w :
          OrbitConnectingGoodThreeRootWitness
            alpha gamma k omegaInv centerB centerC,
        w.1.middle = splitTorusTrace q ∧
          orderOf q = p - 1 ∧
            OrderedTraceCandidateRegular
              frameA frameB frameC w.1.middle := by
  have hpositive :=
    divisorsError_lt_primitiveTraceMoebiusMainTerm_of_explicitInequality
      (Nat.card (ZMod p)ˣ) p 1 952
      Nat.card_pos (by norm_num) (by
        simpa using hexplicit)
  have hdivisorsPositive :
      0 < (Nat.card (ZMod p)ˣ).divisors.card :=
    (Nat.nonempty_divisors.mpr Nat.card_pos.ne').card_pos
  have hdivisorsOne :
      (1 : ℝ) ≤
        ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) := by
    exact_mod_cast hdivisorsPositive
  have hpOne : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hpOneReal : (1 : ℝ) ≤ p := by
    exact_mod_cast hpOne
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hpOneReal
  have hproductOne :
      (1 : ℝ) ≤
        ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
          Real.sqrt (p : ℝ) := by
    nlinarith [mul_le_mul hdivisorsOne hsqrtOne
      (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity :
        (0 : ℝ) ≤ ((Nat.card (ZMod p)ˣ).divisors.card : ℝ))]
  have hlarge :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            (792 * Real.sqrt (p : ℝ)) +
          160 ≤
        ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
          (952 * Real.sqrt (p : ℝ)) := by
    have h160 :
        (160 : ℝ) ≤
          160 *
            (((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
              Real.sqrt (p : ℝ)) := by
      calc
        (160 : ℝ) = 160 * 1 := by ring
        _ ≤
            160 *
              (((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
                Real.sqrt (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hproductOne (by norm_num)
    calc
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
              (792 * Real.sqrt (p : ℝ)) +
            160 ≤
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
              (792 * Real.sqrt (p : ℝ)) +
            160 *
              (((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
                Real.sqrt (p : ℝ)) := by
        simpa [add_comm] using
          (add_le_add_left h160
            (((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
              (792 * Real.sqrt (p : ℝ))))
      _ =
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            (952 * Real.sqrt (p : ℝ)) := by ring
  apply
    exists_primitive_candidateRegular_orbitConnectingGoodThreeRootWitness_of_margin
      p hpFive frameA frameB frameC
        alpha gamma k omegaInv centerB centerC
        hFrameA hFrameB homegaInv habsolute
  exact hlarge.trans_lt hpositive

/-- Uniformly for sufficiently large primes, the conditional geometric
orbit-connecting input yields a good primitive witness whose middle is
candidate-regular in any supplied nonparabolic ordered frame. -/
theorem
    exists_threshold_primitive_candidateRegular_orbitConnectingGoodThreeRootWitness :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
      ∀ (frameA frameB frameC : ZMod p)
        (alpha gamma k omegaInv centerB centerC : ZMod p),
        frameA ^ 2 ≠ 4 →
        frameB ^ 2 ≠ 4 →
        omegaInv ≠ 0 →
        (∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
          SevenHyperellipticPlanesAbsolutelyIrreducible
            (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
            (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
            (C omegaInv *
              centeredNormPulledRadicand centerB centerC d)) →
          ∃ q : (ZMod p)ˣ,
            ∃ w :
                OrbitConnectingGoodThreeRootWitness
                  alpha gamma k omegaInv centerB centerC,
              w.1.middle = splitTorusTrace q ∧
                orderOf q = p - 1 ∧
                  OrderedTraceCandidateRegular
                    frameA frameB frameC w.1.middle := by
  obtain ⟨inequalityThreshold, hInequality⟩ :=
    exists_threshold_endgamePrimitiveTrace_explicitInequality
      952 (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨max inequalityThreshold 5, ?_⟩
  intro p hp _ frameA frameB frameC
    alpha gamma k omegaInv centerB centerC
    hFrameA hFrameB homegaInv habsolute
  have hpInequality : inequalityThreshold ≤ p :=
    (le_max_left inequalityThreshold 5).trans hp
  have hpFive : 5 ≤ p :=
    (le_max_right inequalityThreshold 5).trans hp
  have hpOne : 1 ≤ p := by omega
  have hpOneReal : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hpOne
  have honeLe :
      ((1 : ℕ) : ℝ) ≤
        (p : ℝ) ^ ((1 : ℝ) / 2 - 1 / 4) := by
    simpa using
      (Real.one_le_rpow hpOneReal
        (show (0 : ℝ) ≤ 1 / 2 - 1 / 4 by norm_num))
  have hexplicit :=
    hInequality p hpInequality 1 honeLe
  apply
    exists_primitive_candidateRegular_orbitConnectingGoodThreeRootWitness_of_explicitInequality
      p hpFive frameA frameB frameC
        alpha gamma k omegaInv centerB centerC
        hFrameA hFrameB homegaInv habsolute
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  rw [hcard]
  simpa using hexplicit

end

end GenMarkoff.General.Cage
