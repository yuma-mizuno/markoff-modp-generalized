import GenMarkoff.General.Cage.ConnectingTwoRootEstimate
import GenMarkoff.General.Cage.ConnectingDirectedRelay
import GenMarkoff.General.Cage.ConnectingPrimitiveWitness

/-!
# Primitive connecting two-root witnesses

For a fixed connecting first-axis trace `xi`, the two-root cover records

* an incidence square root, which reconstructs a point sharing that first
  trace; and
* a nonzero square root of a nonsquare multiple of the centered norm of the
  prospective second-axis trace.

The good cover has exact power-map multiplicity.  Its divisor-range error is
`268 sqrt(p)`.  A fixed middle trace supports at most four root pairs and at
most two split-torus parameters, hence at most eight exact-order pairs.

The target-frame sieves remove:

* ten candidate-irregular labels and two centered-obstruction labels, costing
  `8 * 12 = 96` pairs and giving explicit coefficient `268 + 96 = 364`;
* additionally two pair-obstruction labels and the diagonal label, costing
  `8 * 15 = 120` pairs in total and giving coefficient `268 + 120 = 388`.
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff Polynomial
open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

universe u

section WitnessPowerCover

variable {K : Type u} [Field K]

/-- Two simultaneous square-root equations over a prospective middle trace. -/
structure ConnectingTwoRootWitness
    (a : Coefficients K) (xi omegaInv : K) where
  middle : K
  firstRoot : K
  secondRoot : K
  firstEquation :
    firstRoot ^ 2 = incidenceDiscriminant a xi middle
  secondEquation :
    secondRoot ^ 2 =
      omegaInv * centeredNorm a.a3 a.a1 middle

@[ext]
theorem ConnectingTwoRootWitness.ext
    {a : Coefficients K} {xi omegaInv : K}
    {x y : ConnectingTwoRootWitness a xi omegaInv}
    (hmiddle : x.middle = y.middle)
    (hfirst : x.firstRoot = y.firstRoot)
    (hsecond : x.secondRoot = y.secondRoot) :
    x = y := by
  cases x
  cases y
  simp_all

instance connectingTwoRootWitnessFinite
    [Finite K] (a : Coefficients K) (xi omegaInv : K) :
    Finite (ConnectingTwoRootWitness a xi omegaInv) :=
  Finite.of_injective
    (fun z => (z.middle, z.firstRoot, z.secondRoot))
    (by
      intro x y h
      exact ConnectingTwoRootWitness.ext
        (congrArg (fun z => z.1) h)
        (congrArg (fun z => z.2.1) h)
        (congrArg (fun z => z.2.2) h))

/-- The witness subtype in which the centered-norm root is nonzero. -/
def ConnectingGoodTwoRootWitness
    (a : Coefficients K) (xi omegaInv : K) :=
  {w : ConnectingTwoRootWitness a xi omegaInv //
    w.secondRoot ≠ 0}

instance connectingGoodTwoRootWitnessFinite
    [Finite K] (a : Coefficients K) (xi omegaInv : K) :
    Finite (ConnectingGoodTwoRootWitness a xi omegaInv) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- The pulled unit two-root cover attached to the incidence and centered
radicands. -/
abbrev ConnectingUnitTwoRootPowerCover
    (a : Coefficients K) (xi omegaInv : K) (d : ℕ) :=
  UnitTwoRootPowerCover
    (incidencePulledRadicand a xi d)
    (C omegaInv *
      centeredNormPulledRadicand a.a3 a.a1 d)

/-- The unrestricted witness-bearing one-sided power cover. -/
abbrev connectingTwoRootPowerCoverSolutions
    (a : Coefficients K) (xi omegaInv : K) (d : ℕ) :=
  BGS.rightPowerTraceCoverSolutions
    (fun w : ConnectingTwoRootWitness a xi omegaInv => w.middle)
    (splitTorusTrace : Kˣ → K) d

/-- The unrestricted power-range quotient. -/
abbrev connectingTwoRootPowerRangeSolutions
    (a : Coefficients K) (xi omegaInv : K) (d : ℕ) :=
  BGS.rightPowerTraceRangeSolutions
    (fun w : ConnectingTwoRootWitness a xi omegaInv => w.middle)
    (splitTorusTrace : Kˣ → K) d

/-- Scale both witness roots by the reciprocal-trace denominator. -/
def connectingTwoRootPowerCoverToPulled
    (a : Coefficients K) (xi omegaInv : K) (d : ℕ) :
    connectingTwoRootPowerCoverSolutions a xi omegaInv d →
      ConnectingUnitTwoRootPowerCover a xi omegaInv d := fun z => by
  let witness := z.1.1
  let parameter := z.1.2
  have hmiddle :
      witness.middle = splitTorusTrace (parameter ^ d) := z.2
  refine
    { parameter := parameter
      firstRoot := (parameter : K) ^ d * witness.firstRoot
      secondRoot := (parameter : K) ^ d * witness.secondRoot
      firstEquation := ?_
      secondEquation := ?_ }
  · apply
      (scaled_incidenceDiscriminant_iff_pulledRadicand
        a xi (parameter : K) witness.firstRoot
          parameter.ne_zero d).mp
    have htrace :
        (parameter : K) ^ d + ((parameter : K) ^ d)⁻¹ =
          splitTorusTrace (parameter ^ d) := by
      simp [splitTorusTrace]
    rw [htrace, ← hmiddle]
    exact witness.firstEquation
  · apply
      (scaled_centeredNorm_iff_pulledRadicand
        a.a3 a.a1 omegaInv (parameter : K) witness.secondRoot
          parameter.ne_zero d).mp
    have htrace :
        (parameter : K) ^ d + ((parameter : K) ^ d)⁻¹ =
          splitTorusTrace (parameter ^ d) := by
      simp [splitTorusTrace]
    rw [htrace, ← hmiddle]
    exact witness.secondEquation

/-- Divide both pulled roots by the common nonzero denominator. -/
def connectingPulledToTwoRootPowerCover
    (a : Coefficients K) (xi omegaInv : K) (d : ℕ) :
    ConnectingUnitTwoRootPowerCover a xi omegaInv d →
      connectingTwoRootPowerCoverSolutions a xi omegaInv d := fun z => by
  let q : K := (z.parameter : K) ^ d
  have hq : q ≠ 0 := pow_ne_zero d z.parameter.ne_zero
  let witness : ConnectingTwoRootWitness a xi omegaInv :=
    { middle := splitTorusTrace (z.parameter ^ d)
      firstRoot := q⁻¹ * z.firstRoot
      secondRoot := q⁻¹ * z.secondRoot
      firstEquation := by
        have h :=
          (scaled_incidenceDiscriminant_iff_pulledRadicand
            a xi (z.parameter : K) (q⁻¹ * z.firstRoot)
              z.parameter.ne_zero d).mpr (by
            simpa [q, hq] using z.firstEquation)
        simpa [q, splitTorusTrace] using h
      secondEquation := by
        have h :=
          (scaled_centeredNorm_iff_pulledRadicand
            a.a3 a.a1 omegaInv (z.parameter : K)
              (q⁻¹ * z.secondRoot) z.parameter.ne_zero d).mpr (by
            simpa [q, hq] using z.secondEquation)
        simpa [q, splitTorusTrace] using h }
  exact ⟨(witness, z.parameter), rfl⟩

/-- The witness-bearing cover is exactly the pulled unit two-root cover. -/
def connectingTwoRootPowerCoverEquivPulled
    (a : Coefficients K) (xi omegaInv : K) (d : ℕ) :
    connectingTwoRootPowerCoverSolutions a xi omegaInv d ≃
      ConnectingUnitTwoRootPowerCover a xi omegaInv d where
  toFun := connectingTwoRootPowerCoverToPulled a xi omegaInv d
  invFun := connectingPulledToTwoRootPowerCover a xi omegaInv d
  left_inv := by
    intro z
    apply Subtype.ext
    apply Prod.ext
    · apply ConnectingTwoRootWitness.ext
      · simpa [connectingTwoRootPowerCoverToPulled,
          connectingPulledToTwoRootPowerCover] using z.2.symm
      · simp [connectingTwoRootPowerCoverToPulled,
          connectingPulledToTwoRootPowerCover]
      · simp [connectingTwoRootPowerCoverToPulled,
          connectingPulledToTwoRootPowerCover]
    · rfl
  right_inv := by
    intro z
    apply UnitTwoRootPowerCover.ext
    · rfl
    · simp [connectingTwoRootPowerCoverToPulled,
        connectingPulledToTwoRootPowerCover]
    · simp [connectingTwoRootPowerCoverToPulled,
        connectingPulledToTwoRootPowerCover]

/-- The one-sided power cover formed from good two-root witnesses. -/
abbrev connectingGoodTwoRootPowerCoverSolutions
    (a : Coefficients K) (xi omegaInv : K) (d : ℕ) :=
  BGS.rightPowerTraceCoverSolutions
    (fun w : ConnectingGoodTwoRootWitness a xi omegaInv =>
      w.1.middle)
    (splitTorusTrace : Kˣ → K) d

/-- The power-range quotient formed from good two-root witnesses. -/
abbrev connectingGoodTwoRootPowerRangeSolutions
    (a : Coefficients K) (xi omegaInv : K) (d : ℕ) :=
  BGS.rightPowerTraceRangeSolutions
    (fun w : ConnectingGoodTwoRootWitness a xi omegaInv =>
      w.1.middle)
    (splitTorusTrace : Kˣ → K) d

private def connectingGoodTwoRootPowerCoverEquivRestrictedCover
    (a : Coefficients K) (xi omegaInv : K) (d : ℕ) :
    connectingGoodTwoRootPowerCoverSolutions a xi omegaInv d ≃
      {z : connectingTwoRootPowerCoverSolutions
          a xi omegaInv d //
        z.1.1.secondRoot ≠ 0} where
  toFun z :=
    ⟨⟨(z.1.1.1, z.1.2), z.2⟩, z.1.1.2⟩
  invFun z :=
    ⟨(⟨z.1.1.1, z.2⟩, z.1.1.2), z.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def connectingRestrictedTwoRootPowerCoverEquivGoodPulled
    (a : Coefficients K) (xi omegaInv : K) (d : ℕ) :
    {z : connectingTwoRootPowerCoverSolutions
        a xi omegaInv d //
      z.1.1.secondRoot ≠ 0} ≃
      GoodUnitTwoRootPowerCover
        (incidencePulledRadicand a xi d)
        (C omegaInv *
          centeredNormPulledRadicand a.a3 a.a1 d) :=
  Equiv.subtypeEquiv
    (p := fun z => z.1.1.secondRoot ≠ 0)
    (q := fun z => z.secondRoot ≠ 0)
    (connectingTwoRootPowerCoverEquivPulled
      a xi omegaInv d) fun z => by
    change z.1.1.secondRoot ≠ 0 ↔
      (z.1.2 : K) ^ d * z.1.1.secondRoot ≠ 0
    constructor
    · exact fun hsecond =>
        mul_ne_zero (pow_ne_zero d z.1.2.ne_zero) hsecond
    · intro hscaled hzero
      apply hscaled
      simp [hzero]

/-- Good witness-bearing power-cover points are exactly good points of the
pulled two-root cover. -/
def connectingGoodTwoRootPowerCoverEquivPulled
    (a : Coefficients K) (xi omegaInv : K) (d : ℕ) :
    connectingGoodTwoRootPowerCoverSolutions a xi omegaInv d ≃
      GoodUnitTwoRootPowerCover
        (incidencePulledRadicand a xi d)
        (C omegaInv *
          centeredNormPulledRadicand a.a3 a.a1 d) :=
  (connectingGoodTwoRootPowerCoverEquivRestrictedCover
      a xi omegaInv d).trans
    (connectingRestrictedTwoRootPowerCoverEquivGoodPulled
      a xi omegaInv d)

/-- Exact `d`-fold multiplicity of the good pulled cover over its witness
power-map range. -/
theorem natCard_connectingGoodUnitTwoRootPowerCover_eq_mul_powerRange
    [Finite K] [IsCyclic Kˣ]
    (a : Coefficients K) (xi omegaInv : K) (d : ℕ)
    (hd : d ∣ Nat.card Kˣ) :
    Nat.card
        (GoodUnitTwoRootPowerCover
          (incidencePulledRadicand a xi d)
          (C omegaInv *
            centeredNormPulledRadicand a.a3 a.a1 d)) =
      d * Nat.card
        (connectingGoodTwoRootPowerRangeSolutions
          a xi omegaInv d) := by
  calc
    Nat.card
        (GoodUnitTwoRootPowerCover
          (incidencePulledRadicand a xi d)
          (C omegaInv *
            centeredNormPulledRadicand a.a3 a.a1 d)) =
        Nat.card
          (connectingGoodTwoRootPowerCoverSolutions
            a xi omegaInv d) :=
      Nat.card_congr
        (connectingGoodTwoRootPowerCoverEquivPulled
          a xi omegaInv d).symm
    _ = d * Nat.card
        (connectingGoodTwoRootPowerRangeSolutions
          a xi omegaInv d) := by
      simpa [connectingGoodTwoRootPowerCoverSolutions,
        connectingGoodTwoRootPowerRangeSolutions] using
          (BGS.natCard_rightPowerTraceCoverSolutions_of_dvd
            (fun w : ConnectingGoodTwoRootWitness a xi omegaInv =>
              w.1.middle)
            (splitTorusTrace : Kˣ → K) d hd)

end WitnessPowerCover

private lemma natCast_ne_zero_zmod_of_dvd_twoRoot_card_units
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

/-- Dividing the good two-root cover estimate by its exact `d`-fold
multiplicity gives the uniform divisor-range error `268 sqrt(p)`. -/
theorem connectingGoodTwoRootPowerRangeSolutions_card_error_le
    (p : ℕ) [Fact p.Prime]
    (hchar : ringChar (ZMod p) ≠ 2)
    {a : Coefficients (ZMod p)} {xi omegaInv : ZMod p}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hobstruction :
      incidenceCenteredNormObstruction a xi ≠ 0)
    (d : ℕ) (hdvd : d ∣ Nat.card (ZMod p)ˣ) (hd : 0 < d)
    (homegaInv : omegaInv ≠ 0) :
    |(Nat.card
        (connectingGoodTwoRootPowerRangeSolutions
          a xi omegaInv d) : ℝ) - (p : ℝ) / d| ≤
      268 * Real.sqrt (p : ℝ) := by
  let goodCover :=
    GoodUnitTwoRootPowerCover
      (incidencePulledRadicand a xi d)
      (C omegaInv *
        centeredNormPulledRadicand a.a3 a.a1 d)
  let goodRange :=
    connectingGoodTwoRootPowerRangeSolutions a xi omegaInv d
  have hdegree : (d : ZMod p) ≠ 0 :=
    natCast_ne_zero_zmod_of_dvd_twoRoot_card_units p d hd hdvd
  have hcover :
      |(Nat.card goodCover : ℝ) - (p : ℝ)| ≤
        256 * d * Real.sqrt (p : ℝ) + 4 + 8 * d := by
    simpa [goodCover, ZMod.card] using
      (connectingScaledGoodUnitTwoRootPowerCover_card_error_le
        hchar hA1 hA2 hA3 hmoving hxi hobstruction
          hd hdegree homegaInv)
  have hmulNat :
      Nat.card goodCover = d * Nat.card goodRange := by
    simpa [goodCover, goodRange] using
      (natCard_connectingGoodUnitTwoRootPowerCover_eq_mul_powerRange
        a xi omegaInv d hdvd)
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

/-- Exact-order good two-root witness pairs after Möbius inversion. -/
noncomputable abbrev connectingGoodTwoRootExactOrderSolutions
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (xi omegaInv : ZMod p) :=
  BGS.rightTraceExactOrderSolutions
    (fun w : ConnectingGoodTwoRootWitness a xi omegaInv =>
      w.1.middle)
    (splitTorusTrace : (ZMod p)ˣ → ZMod p)
    (Nat.card (ZMod p)ˣ)

/-- A fixed middle trace supports at most four good two-root witnesses. -/
theorem natCard_connectingGoodTwoRootWitness_fixed_middle_le_four
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (xi omegaInv t : ZMod p) :
    Nat.card
        {w : ConnectingGoodTwoRootWitness a xi omegaInv //
          w.1.middle = t} ≤ 4 := by
  let f : (ZMod p)[X] :=
    C (incidenceDiscriminant a xi t)
  let g : (ZMod p)[X] :=
    C (omegaInv * centeredNorm a.a3 a.a1 t)
  let target := TwoSquareRootFiber f g 0
  let embedding :
      {w : ConnectingGoodTwoRootWitness a xi omegaInv //
        w.1.middle = t} ↪ target :=
    { toFun := fun w =>
        { firstRoot := w.1.1.firstRoot
          secondRoot := w.1.1.secondRoot
          firstEquation := by
            simpa [f] using
              w.1.1.firstEquation.trans
                (congrArg
                  (fun s => incidenceDiscriminant a xi s) w.2)
          secondEquation := by
            simpa [g] using
              w.1.1.secondEquation.trans
                (congrArg
                  (fun s =>
                    omegaInv * centeredNorm a.a3 a.a1 s) w.2) }
      inj' := by
        intro w z hwz
        apply Subtype.ext
        apply Subtype.ext
        exact ConnectingTwoRootWitness.ext
          (w.2.trans z.2.symm)
          (congrArg (fun q : target => q.firstRoot) hwz)
          (congrArg (fun q : target => q.secondRoot) hwz) }
  exact
    (Nat.card_le_card_of_injective
      embedding.toFun embedding.injective).trans
      (natCard_twoSquareRootFiber_le_four f g 0)

/-- A fixed middle trace supports at most eight exact-order good two-root
pairs: four root pairs times two split-torus parameters. -/
theorem
    connectingGoodTwoRootExactOrderSolutions_fixed_middle_card_le_eight
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (xi omegaInv t : ZMod p) :
    ((connectingGoodTwoRootExactOrderSolutions
        p a xi omegaInv).filter fun z =>
          z.1.1.middle = t).card ≤ 8 := by
  classical
  let primitive :=
    connectingGoodTwoRootExactOrderSolutions p a xi omegaInv
  let source := ↥(primitive.filter fun z => z.1.1.middle = t)
  let target :=
    {w : ConnectingGoodTwoRootWitness a xi omegaInv //
      w.1.middle = t} ×
    {q : (ZMod p)ˣ // splitTorusTrace q = t}
  let embedding : source ↪ target :=
    { toFun := fun z =>
        (⟨z.1.1, (Finset.mem_filter.mp z.2).2⟩,
          ⟨z.1.2, by
            have hz :=
              (BGS.mem_rightTraceExactOrderSolutions_iff
                (fun w : ConnectingGoodTwoRootWitness a xi omegaInv =>
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
            (q.1.1 : ConnectingGoodTwoRootWitness a xi omegaInv)) hzw)
          (congrArg (fun q : target => (q.2.1 : (ZMod p)ˣ)) hzw) }
  have hcard :=
    Nat.card_le_card_of_injective embedding.toFun embedding.injective
  change Nat.card source ≤ Nat.card target at hcard
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_prod] at hcard
  have hwitness :=
    natCard_connectingGoodTwoRootWitness_fixed_middle_le_four
      p a xi omegaInv t
  have hunit := natCard_splitTorusTrace_fiber_le_two p t
  exact hcard.trans <|
    (Nat.mul_le_mul hwitness hunit).trans (by norm_num)

/-- Exact-order pairs whose middle belongs to a prescribed finite set. -/
noncomputable def
    connectingGoodTwoRootExactOrderSolutionsWithMiddleIn
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (xi omegaInv : ZMod p)
    (traces : Finset (ZMod p)) :
    Finset
      (ConnectingGoodTwoRootWitness a xi omegaInv ×
        (ZMod p)ˣ) :=
  (connectingGoodTwoRootExactOrderSolutions p a xi omegaInv).filter fun z =>
    z.1.1.middle ∈ traces

/-- A forbidden set of `m` middle labels removes at most `8m` exact-order
pairs. -/
theorem
    connectingGoodTwoRootExactOrderSolutionsWithMiddleIn_card_le
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (xi omegaInv : ZMod p)
    (traces : Finset (ZMod p)) :
    (connectingGoodTwoRootExactOrderSolutionsWithMiddleIn
      p a xi omegaInv traces).card ≤ 8 * traces.card := by
  classical
  let primitive :=
    connectingGoodTwoRootExactOrderSolutions p a xi omegaInv
  let bad :=
    connectingGoodTwoRootExactOrderSolutionsWithMiddleIn
      p a xi omegaInv traces
  let traceValue :
      ConnectingGoodTwoRootWitness a xi omegaInv ×
          (ZMod p)ˣ → ZMod p :=
    fun z => z.1.1.middle
  have hfiber :
      ∀ t ∈ bad.image traceValue,
        (bad.filter fun z => traceValue z = t).card ≤ 8 := by
    intro t _
    calc
      (bad.filter fun z => traceValue z = t).card ≤
          (primitive.filter fun z => z.1.1.middle = t).card := by
        apply Finset.card_le_card
        intro z hz
        have hzBad := (Finset.mem_filter.mp hz).1
        have hzTrace := (Finset.mem_filter.mp hz).2
        change z ∈
          connectingGoodTwoRootExactOrderSolutionsWithMiddleIn
            p a xi omegaInv traces at hzBad
        rw [connectingGoodTwoRootExactOrderSolutionsWithMiddleIn] at hzBad
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hzBad).1, hzTrace⟩
      _ ≤ 8 :=
        connectingGoodTwoRootExactOrderSolutions_fixed_middle_card_le_eight
          p a xi omegaInv t
  have himage : bad.image traceValue ⊆ traces := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨z, hz, rfl⟩
    change z ∈
      connectingGoodTwoRootExactOrderSolutionsWithMiddleIn
        p a xi omegaInv traces at hz
    rw [connectingGoodTwoRootExactOrderSolutionsWithMiddleIn] at hz
    exact (Finset.mem_filter.mp hz).2
  change bad.card ≤ 8 * traces.card
  calc
    bad.card ≤ 8 * (bad.image traceValue).card :=
      Finset.card_le_mul_card_image bad 8
        (fun t ht => hfiber t ht)
    _ ≤ 8 * traces.card :=
      Nat.mul_le_mul_left 8 (Finset.card_le_card himage)

/-- General finite-sieve form.  It selects a primitive middle that is
candidate regular in `frame` and avoids a supplied finite forbidden set. -/
theorem
    exists_primitive_candidateRegular_connectingGoodTwoRootWitness_outside_of_margin
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (a frame : Coefficients (ZMod p))
    (xi omegaInv : ZMod p)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hxiObstruction :
      incidenceCenteredNormObstruction a xi ≠ 0)
    (hFrameA : frame.a1 ^ 2 ≠ 4)
    (hFrameB : frame.a2 ^ 2 ≠ 4)
    (homegaInvNonsquare : ¬ IsSquare omegaInv)
    (forbidden : Finset (ZMod p))
    (badTraceBudget : ℕ)
    (hforbidden : forbidden.card ≤ badTraceBudget)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            (268 * Real.sqrt (p : ℝ)) +
          (8 * (10 + badTraceBudget) : ℕ) <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p 1) :
    ∃ q : (ZMod p)ˣ,
      ∃ w : ConnectingGoodTwoRootWitness a xi omegaInv,
        w.1.middle = splitTorusTrace q ∧
          orderOf q = p - 1 ∧
            OrderedTraceCandidateRegular
              frame.a1 frame.a2 frame.a3 w.1.middle ∧
              w.1.middle ∉ forbidden := by
  classical
  let leftTrace :
      ConnectingGoodTwoRootWitness a xi omegaInv → ZMod p :=
    fun w => w.1.middle
  let rightTrace : (ZMod p)ˣ → ZMod p :=
    splitTorusTrace
  let primitive :=
    BGS.rightTraceExactOrderSolutions
      leftTrace rightTrace (Nat.card (ZMod p)ˣ)
  let safeRoots : Finset (ZMod p) :=
    (orderedTraceSafePolynomial
      frame.a1 frame.a2 frame.a3).roots.toFinset
  let badTraces := safeRoots ∪ forbidden
  let bad :=
    connectingGoodTwoRootExactOrderSolutionsWithMiddleIn
      p a xi omegaInv badTraces
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
          268 * Real.sqrt (p : ℝ) := by
    intro d hdvd hd
    simpa [leftTrace, rightTrace,
      connectingGoodTwoRootPowerRangeSolutions] using
      (connectingGoodTwoRootPowerRangeSolutions_card_error_le
        p hchar hA1 hA2 hA3 hmoving hxi hxiObstruction
          d hdvd hd homegaInv)
  have henvelope :
      |(primitive.card : ℝ) -
          primitiveTraceMoebiusMainTerm
            (Nat.card (ZMod p)ˣ) p 1| ≤
        ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
          (268 * Real.sqrt (p : ℝ)) := by
    simpa [primitive, leftTrace, rightTrace,
      primitiveTraceMoebiusMainTerm] using
      (BGS.rightTraceExactOrderSolutions_card_error_le_moebiusMain
        leftTrace rightTrace (fun d => (p : ℝ) / d)
        (268 * Real.sqrt (p : ℝ)) hRange)
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
  have hcardReal :
      ((8 * (10 + badTraceBudget) : ℕ) : ℝ) <
        primitive.card := by
    linarith
  have hcard :
      8 * (10 + badTraceBudget) < primitive.card := by
    exact_mod_cast hcardReal
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hsafePolynomial :
      orderedTraceSafePolynomial
          frame.a1 frame.a2 frame.a3 ≠ 0 :=
    orderedTraceSafePolynomial_ne_zero
      frame.a1 frame.a2 frame.a3 htwo hFrameA hFrameB
  have hsafeRoots : safeRoots.card ≤ 10 := by
    simpa [safeRoots] using
      orderedTraceSafePolynomial_roots_card_le
        frame.a1 frame.a2 frame.a3
  have hbadTraces : badTraces.card ≤ 10 + badTraceBudget := by
    calc
      badTraces.card ≤ safeRoots.card + forbidden.card := by
        simpa [badTraces] using
          Finset.card_union_le safeRoots forbidden
      _ ≤ 10 + badTraceBudget :=
        Nat.add_le_add hsafeRoots hforbidden
  have hbad :
      bad.card ≤ 8 * (10 + badTraceBudget) := by
    calc
      bad.card ≤ 8 * badTraces.card := by
        simpa [bad] using
          connectingGoodTwoRootExactOrderSolutionsWithMiddleIn_card_le
            p a xi omegaInv badTraces
      _ ≤ 8 * (10 + badTraceBudget) :=
        Nat.mul_le_mul_left 8 hbadTraces
  have hexists : ∃ z ∈ primitive, z ∉ bad := by
    by_contra hnone
    push Not at hnone
    have hsubset : primitive ⊆ bad := by
      intro z hz
      exact hnone z hz
    have hle := Finset.card_le_card hsubset
    exact (Nat.not_le_of_lt hcard) (hle.trans hbad)
  obtain ⟨z, hz, hzNotBad⟩ := hexists
  have hz' :=
    (BGS.mem_rightTraceExactOrderSolutions_iff
      leftTrace rightTrace (Nat.card (ZMod p)ˣ) z).mp hz
  have hmiddleNotBadTraces : z.1.1.middle ∉ badTraces := by
    intro hmiddle
    apply hzNotBad
    change z ∈
      connectingGoodTwoRootExactOrderSolutionsWithMiddleIn
        p a xi omegaInv badTraces
    rw [connectingGoodTwoRootExactOrderSolutionsWithMiddleIn]
    exact Finset.mem_filter.mpr
      ⟨by simpa [primitive, leftTrace, rightTrace] using hz, hmiddle⟩
  have hregular :
      OrderedTraceCandidateRegular
        frame.a1 frame.a2 frame.a3 z.1.1.middle := by
    by_contra hirregular
    apply hmiddleNotBadTraces
    apply Finset.mem_union_left
    change z.1.1.middle ∈
      (orderedTraceSafePolynomial
        frame.a1 frame.a2 frame.a3).roots.toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hsafePolynomial]
    by_contra hne
    exact hirregular
      ((orderedTraceSafePolynomial_eval_ne_zero_iff
        frame.a1 frame.a2 frame.a3 z.1.1.middle).mp hne)
  have houtside : z.1.1.middle ∉ forbidden := by
    intro hmiddle
    apply hmiddleNotBadTraces
    change z.1.1.middle ∈ safeRoots ∪ forbidden
    exact Finset.mem_union_right safeRoots hmiddle
  rcases z with ⟨w, q⟩
  refine ⟨q, w, ?_, ?_, hregular, houtside⟩
  · simpa [leftTrace, rightTrace] using hz'.1
  · rw [Nat.card_units, Nat.card_zmod] at hz'
    exact hz'.2

private theorem connectingTwoRoot_margin_of_explicitInequality
    (p budget coefficient : ℕ) [Fact p.Prime]
    (hcoefficient : coefficient = 268 + budget)
    (hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          (coefficient * Real.sqrt (p : ℝ)) < p) :
    ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            (268 * Real.sqrt (p : ℝ)) +
          budget <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p 1 := by
  have hpositive :=
    divisorsError_lt_primitiveTraceMoebiusMainTerm_of_explicitInequality
      (Nat.card (ZMod p)ˣ) p 1 coefficient
      Nat.card_pos (by norm_num) (by simpa using hexplicit)
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
  have hbudget :
      (budget : ℝ) ≤
        budget *
          (((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            Real.sqrt (p : ℝ)) := by
    calc
      (budget : ℝ) = budget * 1 := by ring
      _ ≤ budget *
          (((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            Real.sqrt (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hproductOne (by positivity)
  have hlarge :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
              (268 * Real.sqrt (p : ℝ)) +
            budget ≤
        ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
          (coefficient * Real.sqrt (p : ℝ)) := by
    calc
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
              (268 * Real.sqrt (p : ℝ)) +
            budget ≤
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
                (268 * Real.sqrt (p : ℝ)) +
              budget *
                (((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
                  Real.sqrt (p : ℝ)) := by
        linarith
      _ =
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            (((268 + budget : ℕ) : ℝ) *
              Real.sqrt (p : ℝ)) := by
        push_cast
        ring
      _ =
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            (coefficient * Real.sqrt (p : ℝ)) := by
        rw [hcoefficient]
  exact hlarge.trans_lt hpositive

/-- The coefficient-`364` primitive sieve selects a candidate-regular,
centered-obstruction-ready target trace. -/
theorem
    exists_primitive_obstructionReady_connectingGoodTwoRootWitness_of_explicitInequality
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (a frame : Coefficients (ZMod p))
    (xi omegaInv : ZMod p)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hxiObstruction :
      incidenceCenteredNormObstruction a xi ≠ 0)
    (hFrameA : frame.a1 ^ 2 ≠ 4)
    (hFrameB : frame.a2 ^ 2 ≠ 4)
    (homegaInvNonsquare : ¬ IsSquare omegaInv)
    (hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          (364 * Real.sqrt (p : ℝ)) < p) :
    ∃ q : (ZMod p)ˣ,
      ∃ w : ConnectingGoodTwoRootWitness a xi omegaInv,
        w.1.middle = splitTorusTrace q ∧
          orderOf q = p - 1 ∧
            OrderedTraceCandidateRegular
              frame.a1 frame.a2 frame.a3 w.1.middle ∧
              incidenceCenteredNormObstruction
                frame w.1.middle ≠ 0 := by
  let forbidden := incidenceCenteredNormObstructionBadTraces frame
  have hforbidden : forbidden.card ≤ 2 := by
    simpa [forbidden] using
      incidenceCenteredNormObstructionBadTraces_card_le_two frame
  obtain ⟨q, w, htrace, horder, hregular, houtside⟩ :=
    exists_primitive_candidateRegular_connectingGoodTwoRootWitness_outside_of_margin
      p hpFive a frame xi omegaInv hA1 hA2 hA3 hmoving
        hxi hxiObstruction hFrameA hFrameB homegaInvNonsquare
        forbidden 2 hforbidden (by
          have hmargin :=
            connectingTwoRoot_margin_of_explicitInequality
              p 96 364 (by norm_num) hexplicit
          simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] using
            hmargin)
  refine ⟨q, w, htrace, horder, hregular, ?_⟩
  intro hzero
  exact houtside
    ((mem_incidenceCenteredNormObstructionBadTraces_iff
      frame w.1.middle hFrameA hFrameB).2 hzero)

/-- The coefficient-`388` primitive sieve selects a target trace that forms
a full connecting incidence pair with the prescribed trace `eta`. -/
theorem
    exists_primitive_connectingPair_connectingGoodTwoRootWitness_of_explicitInequality
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (a frame : Coefficients (ZMod p))
    (xi omegaInv eta : ZMod p)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hxiObstruction :
      incidenceCenteredNormObstruction a xi ≠ 0)
    (hFrameA : frame.a1 ^ 2 ≠ 4)
    (hFrameB : frame.a2 ^ 2 ≠ 4)
    (hetaRegular :
      OrderedTraceCandidateRegular
        frame.a1 frame.a2 frame.a3 eta)
    (hetaObstruction :
      incidenceCenteredNormObstruction frame eta ≠ 0)
    (homegaInvNonsquare : ¬ IsSquare omegaInv)
    (hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          (388 * Real.sqrt (p : ℝ)) < p) :
    ∃ q : (ZMod p)ˣ,
      ∃ w : ConnectingGoodTwoRootWitness a xi omegaInv,
        w.1.middle = splitTorusTrace q ∧
          orderOf q = p - 1 ∧
            OrderedTraceCandidateRegular
              frame.a1 frame.a2 frame.a3 w.1.middle ∧
              IsConnectingIncidencePair frame w.1.middle eta := by
  classical
  let centeredBad :=
    incidenceCenteredNormObstructionBadTraces frame
  let pairBad :=
    incidencePairObstructionBadTraces frame eta
  let forbidden : Finset (ZMod p) :=
    (centeredBad ∪ pairBad) ∪ {eta}
  have hcenteredBad : centeredBad.card ≤ 2 := by
    simpa [centeredBad] using
      incidenceCenteredNormObstructionBadTraces_card_le_two frame
  have hpairBad : pairBad.card ≤ 2 := by
    simpa [pairBad] using
      incidencePairObstructionBadTraces_card_le_two frame eta
  have hunion : (centeredBad ∪ pairBad).card ≤ 4 := by
    calc
      (centeredBad ∪ pairBad).card ≤
          centeredBad.card + pairBad.card :=
        Finset.card_union_le _ _
      _ ≤ 2 + 2 := Nat.add_le_add hcenteredBad hpairBad
      _ = 4 := by norm_num
  have hforbidden : forbidden.card ≤ 5 := by
    calc
      forbidden.card ≤
          (centeredBad ∪ pairBad).card +
            ({eta} : Finset (ZMod p)).card := by
        simpa [forbidden] using
          Finset.card_union_le
            (centeredBad ∪ pairBad) ({eta} : Finset (ZMod p))
      _ ≤ 4 + 1 := by simpa using Nat.add_le_add_right hunion 1
      _ = 5 := by norm_num
  obtain ⟨q, w, htrace, horder, hregular, houtside⟩ :=
    exists_primitive_candidateRegular_connectingGoodTwoRootWitness_outside_of_margin
      p hpFive a frame xi omegaInv hA1 hA2 hA3 hmoving
        hxi hxiObstruction hFrameA hFrameB homegaInvNonsquare
        forbidden 5 hforbidden (by
          have hmargin :=
            connectingTwoRoot_margin_of_explicitInequality
              p 120 388 (by norm_num) hexplicit
          simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] using
            hmargin)
  have hmiddleCentered :
      incidenceCenteredNormObstruction frame w.1.middle ≠ 0 := by
    intro hzero
    apply houtside
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact
      (mem_incidenceCenteredNormObstructionBadTraces_iff
        frame w.1.middle hFrameA hFrameB).2 hzero
  have hetaMiddleObstruction :
      incidencePairObstruction frame eta w.1.middle ≠ 0 := by
    intro hzero
    apply houtside
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact
      (mem_incidencePairObstructionBadTraces_iff
        frame eta w.1.middle hetaRegular).2 hzero
  have hmiddleEtaObstruction :
      incidencePairObstruction frame w.1.middle eta ≠ 0 := by
    rw [incidencePairObstruction_comm]
    exact hetaMiddleObstruction
  have hmiddleNeEta : w.1.middle ≠ eta := by
    intro heq
    apply houtside
    apply Finset.mem_union_right
    simp [heq]
  exact
    ⟨q, w, htrace, horder, hregular,
      ⟨⟨hmiddleNeEta, hmiddleEtaObstruction⟩,
        hmiddleCentered, hetaObstruction⟩⟩

end

end GenMarkoff.General.Cage
