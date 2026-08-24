import GenMarkoff.General.Cage.ConnectingGoodPowerCover
import GenMarkoff.General.Cage.ConnectingThreeRootEstimate

/-!
# Primitive connecting witnesses

The good connecting power cover has exact power-map multiplicity.  Dividing
its affine Hasse estimate by that multiplicity gives a uniform estimate on
every divisor power range.  Möbius inversion then produces, for all
sufficiently large primes, a good connecting witness whose middle parameter
comes from a primitive split-torus unit.
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff
open Polynomial
open scoped ArithmeticFunction.Moebius BigOperators

universe u

noncomputable section

/-- A positive divisor of the split-torus order is nonzero in the prime
field. -/
private lemma natCast_ne_zero_zmod_of_dvd_card_units
    (p d : ℕ) [Fact p.Prime]
    (hd : 0 < d) (hdvd : d ∣ Nat.card (ZMod p)ˣ) :
    (d : ZMod p) ≠ 0 := by
  apply natCast_ne_zero_zmod_of_pos_of_lt hd
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  rw [hcard] at hdvd
  have hpTwo : 2 ≤ p := (Fact.out : p.Prime).two_le
  exact lt_of_le_of_lt
    (Nat.le_of_dvd (by omega) hdvd) (by omega)

/-- After exact division by the `d`-fold power-map fibers, the good
connecting range has a uniform square-root error. -/
theorem connectingGoodThreeRootPowerRangeSolutions_card_error_le
    (p : ℕ) [Fact p.Prime]
    (hchar : ringChar (ZMod p) ≠ 2)
    {a : Coefficients (ZMod p)} {xi eta omegaInv : ZMod p}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hpair : IsConnectingIncidencePair a xi eta)
    (d : ℕ) (hdvd : d ∣ Nat.card (ZMod p)ˣ) (hd : 0 < d)
    (homegaInv : omegaInv ≠ 0) :
    |(Nat.card
        (connectingGoodThreeRootPowerRangeSolutions
          a xi eta omegaInv d) : ℝ) - (p : ℝ) / d| ≤
      792 * Real.sqrt (p : ℝ) := by
  let goodCover :=
    GoodUnitThreeRootPowerCover
      (incidencePulledRadicand a xi d)
      (incidencePulledRadicand a eta d)
      (Polynomial.C omegaInv *
        centeredNormPulledRadicand a.a3 a.a1 d)
  let goodRange :=
    connectingGoodThreeRootPowerRangeSolutions
      a xi eta omegaInv d
  have hdegree : (d : ZMod p) ≠ 0 :=
    natCast_ne_zero_zmod_of_dvd_card_units p d hd hdvd
  have hcover :
      |(Nat.card goodCover : ℝ) - (p : ℝ)| ≤
        768 * d * Real.sqrt (p : ℝ) + 8 + 16 * d := by
    simpa [goodCover, ZMod.card] using
      (connectingScaledGoodUnitThreeRootPowerCover_card_error_le
        hchar hA1 hA2 hA3 hmoving hxi heta hpair
        hd hdegree homegaInv)
  have hmulNat :
      Nat.card goodCover = d * Nat.card goodRange := by
    simpa [goodCover, goodRange] using
      (natCard_connectingGoodUnitThreeRootPowerCover_eq_mul_powerRange
        a xi eta omegaInv d hdvd)
  have hmulReal :
      (Nat.card goodCover : ℝ) =
        (d : ℝ) * (Nat.card goodRange : ℝ) := by
    exact_mod_cast hmulNat
  rw [hmulReal] at hcover
  have hdReal : (0 : ℝ) < d := by
    exact_mod_cast hd
  have hrewrite :
      (d : ℝ) * (Nat.card goodRange : ℝ) - (p : ℝ) =
        (d : ℝ) *
          ((Nat.card goodRange : ℝ) - (p : ℝ) / d) := by
    field_simp
  rw [hrewrite, abs_mul, abs_of_pos hdReal] at hcover
  have hdOne : (1 : ℝ) ≤ d := by
    exact_mod_cast hd
  have hpOne : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hpOneReal : (1 : ℝ) ≤ p := by
    exact_mod_cast hpOne
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hpOneReal
  nlinarith

/-- The exact-order witness pairs used after Möbius inversion. -/
noncomputable abbrev connectingGoodThreeRootExactOrderSolutions
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (xi eta omegaInv : ZMod p) :=
  BGS.rightTraceExactOrderSolutions
    (fun w : ConnectingGoodThreeRootWitness a xi eta omegaInv =>
      w.1.middle)
    (BGS.Markoff.splitTorusTrace : (ZMod p)ˣ → ZMod p)
    (Nat.card (ZMod p)ˣ)

/-- A scalar in the prime field has at most two square roots. -/
private theorem natCard_connectingSquareRootFiber_le_two
    (p : ℕ) [Fact p.Prime] (b : ZMod p) :
    Nat.card {x : ZMod p // x ^ 2 = b} ≤ 2 := by
  let f : (ZMod p)[X] := X ^ 2 - Polynomial.C b
  have hf : f ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun q : (ZMod p)[X] => q.coeff 2) hzero
    simp [f] at hcoeff
  let rootEmbedding : {x : ZMod p // x ^ 2 = b} ↪ f.roots.toFinset :=
    { toFun := fun x => ⟨x, by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
        simpa [f, sub_eq_zero] using x.2⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg
          (fun z : f.roots.toFinset => (z : ZMod p)) h }
  calc
    Nat.card {x : ZMod p // x ^ 2 = b} ≤
        Nat.card ↥f.roots.toFinset := by
      exact Nat.card_le_card_of_injective
        rootEmbedding.toFun rootEmbedding.injective
    _ = f.roots.toFinset.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ f.roots.card := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f
    _ = 2 := by simp [f]

/-- For one fixed middle trace, the three square-root choices give at most
eight good connecting witnesses. -/
theorem natCard_connectingGoodThreeRootWitness_fixed_middle_le_eight
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (xi eta omegaInv t : ZMod p) :
    Nat.card
        {w : ConnectingGoodThreeRootWitness a xi eta omegaInv //
          w.1.middle = t} ≤ 8 := by
  let target :=
    ({r : ZMod p // r ^ 2 = incidenceDiscriminant a xi t} ×
      {r : ZMod p // r ^ 2 = incidenceDiscriminant a eta t}) ×
      {r : ZMod p //
        r ^ 2 = omegaInv * centeredNorm a.a3 a.a1 t}
  let embedding :
      {w : ConnectingGoodThreeRootWitness a xi eta omegaInv //
        w.1.middle = t} ↪ target :=
    { toFun := fun w =>
        ((⟨w.1.1.firstRoot,
            w.1.1.firstEquation.trans
              (congrArg (incidenceDiscriminant a xi) w.2)⟩,
          ⟨w.1.1.secondRoot,
            w.1.1.secondEquation.trans
              (congrArg (incidenceDiscriminant a eta) w.2)⟩),
          ⟨w.1.1.thirdRoot,
            w.1.1.thirdEquation.trans
              (congrArg
                (fun s => omegaInv * centeredNorm a.a3 a.a1 s)
                w.2)⟩)
      inj' := by
        intro w z hwz
        apply Subtype.ext
        apply Subtype.ext
        exact ConnectingThreeRootWitness.ext
          (w.2.trans z.2.symm)
          (congrArg (fun q : target => (q.1.1 : ZMod p)) hwz)
          (congrArg (fun q : target => (q.1.2 : ZMod p)) hwz)
          (congrArg (fun q : target => (q.2 : ZMod p)) hwz) }
  have hcard :=
    Nat.card_le_card_of_injective embedding.toFun embedding.injective
  change Nat.card _ ≤ Nat.card target at hcard
  rw [Nat.card_prod, Nat.card_prod] at hcard
  have hfirst :
      Nat.card {r : ZMod p //
        r ^ 2 = incidenceDiscriminant a xi t} ≤ 2 :=
    natCard_connectingSquareRootFiber_le_two p _
  have hsecond :
      Nat.card {r : ZMod p //
        r ^ 2 = incidenceDiscriminant a eta t} ≤ 2 :=
    natCard_connectingSquareRootFiber_le_two p _
  have hthird :
      Nat.card {r : ZMod p //
        r ^ 2 = omegaInv * centeredNorm a.a3 a.a1 t} ≤ 2 :=
    natCard_connectingSquareRootFiber_le_two p _
  exact hcard.trans <|
    (Nat.mul_le_mul (Nat.mul_le_mul hfirst hsecond) hthird).trans
      (by norm_num)

/-- The split-torus trace map has fibers of cardinality at most two. -/
theorem natCard_splitTorusTrace_fiber_le_two
    (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    Nat.card {q : (ZMod p)ˣ // splitTorusTrace q = t} ≤ 2 := by
  let f : (ZMod p)[X] :=
    twistedTracePolynomial 1 t
  have hf : f ≠ 0 :=
    (twistedTracePolynomial_monic (1 : ZMod p) t).ne_zero
  let rootEmbedding :
      {q : (ZMod p)ˣ // splitTorusTrace q = t} ↪ f.roots.toFinset :=
    { toFun := fun q => ⟨(q.1 : ZMod p), by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
        apply
          (eval_twistedTracePolynomial_eq_zero_iff
            (1 : ZMod p) t q.1).2
        rw [twistedUnitTrace, one_mul]
        change splitTorusTrace q.1 = t
        exact q.2⟩
      inj' := by
        intro q r h
        apply Subtype.ext
        apply Units.ext
        exact congrArg
          (fun z : f.roots.toFinset => (z : ZMod p)) h }
  calc
    Nat.card {q : (ZMod p)ˣ // splitTorusTrace q = t} ≤
        Nat.card ↥f.roots.toFinset := by
      exact Nat.card_le_card_of_injective
        rootEmbedding.toFun rootEmbedding.injective
    _ = f.roots.toFinset.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ f.roots.card := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f
    _ = 2 := twistedTracePolynomial_natDegree 1 t

/-- A fixed middle trace supports at most sixteen exact-order pairs: eight
three-root witnesses and at most two split-torus units. -/
theorem
    connectingGoodThreeRootExactOrderSolutions_fixed_middle_card_le_sixteen
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (xi eta omegaInv t : ZMod p) :
    ((connectingGoodThreeRootExactOrderSolutions
        p a xi eta omegaInv).filter fun z => z.1.1.middle = t).card ≤ 16 := by
  classical
  let primitive :=
    connectingGoodThreeRootExactOrderSolutions p a xi eta omegaInv
  let source := ↥(primitive.filter fun z => z.1.1.middle = t)
  let target :=
    {w : ConnectingGoodThreeRootWitness a xi eta omegaInv //
      w.1.middle = t} ×
    {q : (ZMod p)ˣ // splitTorusTrace q = t}
  let embedding : source ↪ target :=
    { toFun := fun z =>
        (⟨z.1.1, (Finset.mem_filter.mp z.2).2⟩,
          ⟨z.1.2, by
            have hz :=
              (BGS.mem_rightTraceExactOrderSolutions_iff
                (fun w : ConnectingGoodThreeRootWitness
                    a xi eta omegaInv => w.1.middle)
                (splitTorusTrace : (ZMod p)ˣ → ZMod p)
                (Nat.card (ZMod p)ˣ) z.1).mp
                (Finset.mem_filter.mp z.2).1
            exact hz.1.symm.trans (Finset.mem_filter.mp z.2).2⟩)
      inj' := by
        intro z w hzw
        apply Subtype.ext
        exact Prod.ext
          (congrArg (fun q : target =>
            (q.1.1 : ConnectingGoodThreeRootWitness
              a xi eta omegaInv)) hzw)
          (congrArg (fun q : target => (q.2.1 : (ZMod p)ˣ)) hzw) }
  have hcard :=
    Nat.card_le_card_of_injective embedding.toFun embedding.injective
  change Nat.card source ≤ Nat.card target at hcard
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_prod] at hcard
  have hwitness :=
    natCard_connectingGoodThreeRootWitness_fixed_middle_le_eight
      p a xi eta omegaInv t
  have hunit := natCard_splitTorusTrace_fiber_le_two p t
  exact hcard.trans <|
    (Nat.mul_le_mul hwitness hunit).trans (by norm_num)

/-- Exact-order witness pairs whose middle trace is outside the ordered
candidate-regular regime needed by the middle connecting fiber. -/
noncomputable def
    irregularConnectingGoodThreeRootExactOrderSolutions
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (xi eta omegaInv : ZMod p) :
    Finset
      (ConnectingGoodThreeRootWitness a xi eta omegaInv × (ZMod p)ˣ) := by
  classical
  exact
    (connectingGoodThreeRootExactOrderSolutions
      p a xi eta omegaInv).filter fun z =>
        ¬ OrderedTraceCandidateRegular
          a.a2 a.a3 a.a1 z.1.1.middle

/-- At most `16 * 10 = 160` exact-order witness pairs have a middle trace
outside the ordered candidate-regular regime needed by the middle
connecting fiber. -/
theorem
    irregularConnectingGoodThreeRootExactOrderSolutions_card_le_oneHundredSixty
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (a : Coefficients (ZMod p)) (xi eta omegaInv : ZMod p)
    (hA2 : a.a2 ^ 2 ≠ 4) (hA3 : a.a3 ^ 2 ≠ 4) :
    (irregularConnectingGoodThreeRootExactOrderSolutions
      p a xi eta omegaInv).card ≤ 160 := by
  classical
  let primitive :=
    connectingGoodThreeRootExactOrderSolutions p a xi eta omegaInv
  let bad :=
    irregularConnectingGoodThreeRootExactOrderSolutions
      p a xi eta omegaInv
  let traceValue :
      ConnectingGoodThreeRootWitness a xi eta omegaInv × (ZMod p)ˣ →
        ZMod p :=
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
          irregularConnectingGoodThreeRootExactOrderSolutions
            p a xi eta omegaInv at hzBad
        rw [irregularConnectingGoodThreeRootExactOrderSolutions] at hzBad
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hzBad).1, hzTrace⟩
      _ ≤ 16 :=
        connectingGoodThreeRootExactOrderSolutions_fixed_middle_card_le_sixteen
          p a xi eta omegaInv t
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hsafe :
      orderedTraceSafePolynomial a.a2 a.a3 a.a1 ≠ 0 :=
    orderedTraceSafePolynomial_ne_zero
      a.a2 a.a3 a.a1 htwo hA2 hA3
  have himage :
      bad.image traceValue ⊆
        (orderedTraceSafePolynomial a.a2 a.a3 a.a1).roots.toFinset := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨z, hz, rfl⟩
    have hirregular :
        ¬ OrderedTraceCandidateRegular
          a.a2 a.a3 a.a1 z.1.1.middle :=
      (Finset.mem_filter.mp hz).2
    have hzero :
        Polynomial.eval z.1.1.middle
          (orderedTraceSafePolynomial a.a2 a.a3 a.a1) = 0 := by
      by_contra hne
      exact hirregular
        ((orderedTraceSafePolynomial_eval_ne_zero_iff
          a.a2 a.a3 a.a1 z.1.1.middle).mp hne)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hsafe]
    exact hzero
  have himageCard :
      (bad.image traceValue).card ≤
        (orderedTraceSafePolynomial a.a2 a.a3 a.a1).roots.toFinset.card :=
    Finset.card_le_card himage
  have hroots :
      (orderedTraceSafePolynomial a.a2 a.a3 a.a1).roots.toFinset.card ≤
        10 :=
    orderedTraceSafePolynomial_roots_card_le a.a2 a.a3 a.a1
  change bad.card ≤ 160
  calc
    bad.card ≤ 16 * (bad.image traceValue).card :=
      Finset.card_le_mul_card_image bad 16
        (fun t ht => hfiber t ht)
    _ ≤ 16 *
        (orderedTraceSafePolynomial a.a2 a.a3 a.a1).roots.toFinset.card :=
      Nat.mul_le_mul_left 16 himageCard
    _ ≤ 16 * 10 := Nat.mul_le_mul_left 16 hroots
    _ = 160 := by norm_num

/-- If the Möbius main term dominates both the divisor error and the
`160` candidate-irregular exact-order pairs, a primitive good witness with
candidate-regular middle trace exists. -/
theorem
    exists_primitive_candidateRegular_connectingGoodThreeRootWitness_of_margin
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (a : Coefficients (ZMod p)) (xi eta omegaInv : ZMod p)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hpair : IsConnectingIncidencePair a xi eta)
    (homegaInvNonsquare : ¬ IsSquare omegaInv)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            (792 * Real.sqrt (p : ℝ)) +
          160 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p 1) :
    ∃ q : (ZMod p)ˣ,
      ∃ w : ConnectingGoodThreeRootWitness a xi eta omegaInv,
        w.1.middle = BGS.Markoff.splitTorusTrace q ∧
          orderOf q = p - 1 ∧
            OrderedTraceCandidateRegular
              a.a2 a.a3 a.a1 w.1.middle := by
  classical
  let leftTrace :
      ConnectingGoodThreeRootWitness a xi eta omegaInv → ZMod p :=
    fun w => w.1.middle
  let rightTrace : (ZMod p)ˣ → ZMod p :=
    BGS.Markoff.splitTorusTrace
  let primitive :=
    BGS.rightTraceExactOrderSolutions
      leftTrace rightTrace (Nat.card (ZMod p)ˣ)
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have homegaInv : omegaInv ≠ 0 := by
    intro hzero
    apply homegaInvNonsquare
    rw [hzero]
    exact IsSquare.zero
  have hRange :
      ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
        |(Nat.card
            (BGS.rightPowerTraceRangeSolutions
              leftTrace rightTrace d) : ℝ) -
            (p : ℝ) / d| ≤
          792 * Real.sqrt (p : ℝ) := by
    intro d hdvd hd
    simpa [leftTrace, rightTrace,
      connectingGoodThreeRootPowerRangeSolutions] using
      (connectingGoodThreeRootPowerRangeSolutions_card_error_le
        p hchar hA1 hA2 hA3 hmoving hxi heta hpair
        d hdvd hd homegaInv)
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
          a.a2 a.a3 a.a1 z.1.1.middle := by
    by_contra hnone
    push Not at hnone
    have hsubset :
        primitive ⊆
          irregularConnectingGoodThreeRootExactOrderSolutions
            p a xi eta omegaInv := by
      intro z hz
      rw [irregularConnectingGoodThreeRootExactOrderSolutions,
        Finset.mem_filter]
      exact ⟨hz, hnone z hz⟩
    have hle := Finset.card_le_card hsubset
    have hbad :=
      irregularConnectingGoodThreeRootExactOrderSolutions_card_le_oneHundredSixty
        p hpFive a xi eta omegaInv hA2 hA3
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

/-- The explicit inequality with coefficient `952 = 792 + 160` absorbs all
candidate-irregular exact-order pairs and produces a primitive regular
middle witness. -/
theorem
    exists_primitive_candidateRegular_connectingGoodThreeRootWitness_of_explicitInequality
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (a : Coefficients (ZMod p)) (xi eta omegaInv : ZMod p)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hpair : IsConnectingIncidencePair a xi eta)
    (homegaInvNonsquare : ¬ IsSquare omegaInv)
    (hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          (952 * Real.sqrt (p : ℝ)) < p) :
    ∃ q : (ZMod p)ˣ,
      ∃ w : ConnectingGoodThreeRootWitness a xi eta omegaInv,
        w.1.middle = BGS.Markoff.splitTorusTrace q ∧
          orderOf q = p - 1 ∧
            OrderedTraceCandidateRegular
              a.a2 a.a3 a.a1 w.1.middle := by
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
    exists_primitive_candidateRegular_connectingGoodThreeRootWitness_of_margin
      p hpFive a xi eta omegaInv
      hA1 hA2 hA3 hmoving hxi heta hpair homegaInvNonsquare
  exact hlarge.trans_lt hpositive

/-- The explicit divisor-error inequality produces a primitive split-torus
parameter together with a good connecting witness. -/
theorem
    exists_primitive_connectingGoodThreeRootWitness_of_explicitInequality
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (a : Coefficients (ZMod p)) (xi eta omegaInv : ZMod p)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hpair : IsConnectingIncidencePair a xi eta)
    (homegaInvNonsquare : ¬ IsSquare omegaInv)
    (hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          (792 * Real.sqrt (p : ℝ)) < p) :
    ∃ q : (ZMod p)ˣ,
      ∃ w : ConnectingGoodThreeRootWitness a xi eta omegaInv,
        w.1.middle = BGS.Markoff.splitTorusTrace q ∧
          orderOf q = p - 1 := by
  let leftTrace :
      ConnectingGoodThreeRootWitness a xi eta omegaInv → ZMod p :=
    fun w => w.1.middle
  let rightTrace : (ZMod p)ˣ → ZMod p :=
    BGS.Markoff.splitTorusTrace
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have homegaInv : omegaInv ≠ 0 := by
    intro hzero
    apply homegaInvNonsquare
    rw [hzero]
    exact IsSquare.zero
  have hRange :
      ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
        |(Nat.card
            (BGS.rightPowerTraceRangeSolutions
              leftTrace rightTrace d) : ℝ) -
            (p : ℝ) / d| ≤
          792 * Real.sqrt (p : ℝ) := by
    intro d hdvd hd
    simpa [leftTrace, rightTrace,
      connectingGoodThreeRootPowerRangeSolutions] using
      (connectingGoodThreeRootPowerRangeSolutions_card_error_le
        p hchar hA1 hA2 hA3 hmoving hxi heta hpair
        d hdvd hd homegaInv)
  have hpositive :=
    divisorsError_lt_primitiveTraceMoebiusMainTerm_of_explicitInequality
      (Nat.card (ZMod p)ˣ) p 1 792
      Nat.card_pos (by norm_num) (by
        simpa using hexplicit)
  obtain ⟨z, hz⟩ :=
    BGS.rightTraceExactOrderSolutions_nonempty_of_divisorsError_lt_moebiusMain
      leftTrace rightTrace (fun d => (p : ℝ) / d)
      (792 * Real.sqrt (p : ℝ)) hRange (by
        simpa [primitiveTraceMoebiusMainTerm] using hpositive)
  rcases z with ⟨w, q⟩
  have hz' :=
    (BGS.mem_rightTraceExactOrderSolutions_iff
      leftTrace rightTrace (Nat.card (ZMod p)ˣ) (w, q)).mp hz
  refine ⟨q, w, ?_, ?_⟩
  · simpa [leftTrace, rightTrace] using hz'.1
  · rw [Nat.card_units, Nat.card_zmod] at hz'
    exact hz'.2

/-- Uniformly for all sufficiently large primes, the unequal connecting
geometry admits a good witness over the trace of a primitive split-torus
unit. -/
theorem exists_threshold_primitive_connectingGoodThreeRootWitness :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
      ∀ (a : Coefficients (ZMod p)) (xi eta omegaInv : ZMod p),
        a.a1 ^ 2 ≠ 4 →
        a.a2 ^ 2 ≠ 4 →
        a.a3 ^ 2 ≠ 4 →
        (a.a3, a.a1) ≠ (0, 0) →
        OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi →
        OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta →
        IsConnectingIncidencePair a xi eta →
        (¬ IsSquare omegaInv) →
          ∃ q : (ZMod p)ˣ,
            ∃ w : ConnectingGoodThreeRootWitness
                a xi eta omegaInv,
              w.1.middle = BGS.Markoff.splitTorusTrace q ∧
                orderOf q = p - 1 := by
  obtain ⟨inequalityThreshold, hInequality⟩ :=
    exists_threshold_endgamePrimitiveTrace_explicitInequality
      792 (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨max inequalityThreshold 5, ?_⟩
  intro p hp _ a xi eta omegaInv
    hA1 hA2 hA3 hmoving hxi heta hpair homegaInvNonsquare
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
    exists_primitive_connectingGoodThreeRootWitness_of_explicitInequality
      p hpFive a xi eta omegaInv
      hA1 hA2 hA3 hmoving hxi heta hpair homegaInvNonsquare
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  rw [hcard]
  simpa using hexplicit

/-- Uniformly for all sufficiently large primes, the unequal connecting
geometry admits a good witness over a primitive split-torus trace whose
middle trace is candidate-regular in the directed middle-axis frame. -/
theorem
    exists_threshold_primitive_candidateRegular_connectingGoodThreeRootWitness :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
      ∀ (a : Coefficients (ZMod p)) (xi eta omegaInv : ZMod p),
        a.a1 ^ 2 ≠ 4 →
        a.a2 ^ 2 ≠ 4 →
        a.a3 ^ 2 ≠ 4 →
        (a.a3, a.a1) ≠ (0, 0) →
        OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi →
        OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta →
        IsConnectingIncidencePair a xi eta →
        (¬ IsSquare omegaInv) →
          ∃ q : (ZMod p)ˣ,
            ∃ w : ConnectingGoodThreeRootWitness
                a xi eta omegaInv,
              w.1.middle = BGS.Markoff.splitTorusTrace q ∧
                orderOf q = p - 1 ∧
                  OrderedTraceCandidateRegular
                    a.a2 a.a3 a.a1 w.1.middle := by
  obtain ⟨inequalityThreshold, hInequality⟩ :=
    exists_threshold_endgamePrimitiveTrace_explicitInequality
      952 (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨max inequalityThreshold 5, ?_⟩
  intro p hp _ a xi eta omegaInv
    hA1 hA2 hA3 hmoving hxi heta hpair homegaInvNonsquare
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
    exists_primitive_candidateRegular_connectingGoodThreeRootWitness_of_explicitInequality
      p hpFive a xi eta omegaInv
      hA1 hA2 hA3 hmoving hxi heta hpair homegaInvNonsquare
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  rw [hcard]
  simpa using hexplicit

end

end GenMarkoff.General.Cage
