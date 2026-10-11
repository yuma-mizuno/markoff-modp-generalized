module

public import GenMarkoff.General.Cage.OrbitConnecting.PrimitiveWitness

@[expose] public section

/-!
# Primitive orbit-connecting witnesses avoiding finitely many middle traces

Each middle trace carries at most sixteen exact-order orbit-connecting
witness pairs, so removing a set of `m` middle traces removes at most `16 * m`
pairs.  Combined with the Möbius lower bound for the number of exact-order
pairs, this produces a primitive witness whose middle trace is
candidate-regular in a supplied frame (avoiding the at most ten roots of
`orderedTraceSafePolynomial`) and avoids a prescribed finite set
(`exists_primitive_candidateRegular_orbitConnectingGoodThreeRootWitness_outside_of_margin`).

Two instances are recorded.

* Avoiding `incidenceCenteredNormObstructionBadTraces` (at most two traces)
  gives a nonzero incidence obstruction, with budget `16 * (10 + 2) = 192`
  and divisor-inequality coefficient `792 + 192 = 984`.
* For a prescribed candidate-regular trace `eta` with nonzero obstruction,
  also avoiding `incidencePairObstructionBadTraces frame eta` (at most two)
  and `eta` itself gives a connecting incidence pair with `eta`, with budget
  `16 * (10 + 2 + 2 + 1) = 240` and coefficient `792 + 240 = 1032`.

The seven-plane absolute irreducibility hypothesis is explicit; it is
discharged by
`orbitConnectingSevenScaledHyperellipticPlanes_absolutelyIrreducible`.
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff Polynomial
open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

/-- Exact-order orbit-connecting witness pairs whose middle belongs to a
prescribed finite set. -/
noncomputable def
    orbitConnectingGoodThreeRootExactOrderSolutionsWithMiddleIn
    (p : ℕ) [Fact p.Prime]
    (alpha gamma k omegaInv centerB centerC : ZMod p)
    (traces : Finset (ZMod p)) :
    Finset
      (OrbitConnectingGoodThreeRootWitness
          alpha gamma k omegaInv centerB centerC ×
        (ZMod p)ˣ) :=
  (orbitConnectingGoodThreeRootExactOrderSolutions
    p alpha gamma k omegaInv centerB centerC).filter fun z =>
      z.1.1.middle ∈ traces

/-- At most `16 * traces.card` exact-order pairs have middle trace in
`traces`. -/
theorem
    orbitConnectingGoodThreeRootExactOrderSolutionsWithMiddleIn_card_le
    (p : ℕ) [Fact p.Prime]
    (alpha gamma k omegaInv centerB centerC : ZMod p)
    (traces : Finset (ZMod p)) :
    (orbitConnectingGoodThreeRootExactOrderSolutionsWithMiddleIn
      p alpha gamma k omegaInv centerB centerC traces).card ≤
        16 * traces.card := by
  classical
  let primitive :=
    orbitConnectingGoodThreeRootExactOrderSolutions
      p alpha gamma k omegaInv centerB centerC
  let bad :=
    orbitConnectingGoodThreeRootExactOrderSolutionsWithMiddleIn
      p alpha gamma k omegaInv centerB centerC traces
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
        -- `bad` is the local name for the `WithMiddleIn` set; restate
        -- `hzBad` with that definition so the `rw` below unfolds it to a
        -- `Finset.filter`.
        change z ∈
          orbitConnectingGoodThreeRootExactOrderSolutionsWithMiddleIn
            p alpha gamma k omegaInv centerB centerC traces at hzBad
        rw [orbitConnectingGoodThreeRootExactOrderSolutionsWithMiddleIn]
          at hzBad
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hzBad).1, hzTrace⟩
      _ ≤ 16 :=
        orbitConnectingGoodThreeRootExactOrderSolutions_fixed_middle_card_le_sixteen
          p alpha gamma k omegaInv centerB centerC t
  have himage : bad.image traceValue ⊆ traces := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨z, hz, rfl⟩
    -- As above, unfold the local name `bad` in `hz` so that the `rw` below
    -- can unfold the definition to a `Finset.filter`.
    change z ∈
      orbitConnectingGoodThreeRootExactOrderSolutionsWithMiddleIn
        p alpha gamma k omegaInv centerB centerC traces at hz
    rw [orbitConnectingGoodThreeRootExactOrderSolutionsWithMiddleIn] at hz
    exact (Finset.mem_filter.mp hz).2
  -- Restate the goal with the local name `bad` for the `WithMiddleIn` set,
  -- so that it matches the first term of the calc below.
  change bad.card ≤ 16 * traces.card
  calc
    bad.card ≤ 16 * (bad.image traceValue).card :=
      Finset.card_le_mul_card_image bad 16
        (fun t ht => hfiber t ht)
    _ ≤ 16 * traces.card :=
      Nat.mul_le_mul_left 16 (Finset.card_le_card himage)

/-- Finite sieve for primitive orbit-connecting witnesses.  If the Möbius
main term exceeds the divisor-weighted square-root error by
`16 * (10 + badTraceBudget)`, then some good witness with primitive
split-torus middle trace is candidate-regular in `frame` and has middle trace
outside a given set `forbidden` of at most `badTraceBudget` traces. -/
theorem
    exists_primitive_candidateRegular_orbitConnectingGoodThreeRootWitness_outside_of_margin
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (frame : Coefficients (ZMod p))
    (alpha gamma k omegaInv centerB centerC : ZMod p)
    (hFrameA : frame.a1 ^ 2 ≠ 4)
    (hFrameB : frame.a2 ^ 2 ≠ 4)
    (homegaInv : omegaInv ≠ 0)
    (habsolute :
      ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
        SevenHyperellipticPlanesAbsolutelyIrreducible
          (orbitComponentPlusCosetPulledRadicand alpha gamma k d)
          (orbitComponentMinusCosetPulledRadicand alpha gamma k d)
          (C omegaInv *
            centeredNormPulledRadicand centerB centerC d))
    (forbidden : Finset (ZMod p))
    (badTraceBudget : ℕ)
    (hforbidden : forbidden.card ≤ badTraceBudget)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            (792 * Real.sqrt (p : ℝ)) +
          (16 * (10 + badTraceBudget) : ℕ) <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p 1) :
    ∃ q : (ZMod p)ˣ,
      ∃ w :
          OrbitConnectingGoodThreeRootWitness
            alpha gamma k omegaInv centerB centerC,
        w.1.middle = splitTorusTrace q ∧
          orderOf q = p - 1 ∧
            OrderedTraceCandidateRegular
              frame.a1 frame.a2 frame.a3 w.1.middle ∧
              w.1.middle ∉ forbidden := by
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
  let safeRoots : Finset (ZMod p) :=
    (orderedTraceSafePolynomial
      frame.a1 frame.a2 frame.a3).roots.toFinset
  let badTraces : Finset (ZMod p) :=
    safeRoots ∪ forbidden
  let bad :=
    orbitConnectingGoodThreeRootExactOrderSolutionsWithMiddleIn
      p alpha gamma k omegaInv centerB centerC badTraces
  -- Step 1: the Möbius envelope and the margin give more than
  -- `16 * (10 + badTraceBudget)` exact-order pairs.
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
  have hcardReal :
      ((16 * (10 + badTraceBudget) : ℕ) : ℝ) <
        primitive.card := by
    linarith
  have hcard :
      16 * (10 + badTraceBudget) < primitive.card := by
    exact_mod_cast hcardReal
  -- Step 2: the pairs whose middle is a root of `orderedTraceSafePolynomial`
  -- or lies in `forbidden` number at most `16 * (10 + badTraceBudget)`.
  have htwo : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
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
      bad.card ≤ 16 * (10 + badTraceBudget) := by
    calc
      bad.card ≤ 16 * badTraces.card := by
        simpa [bad] using
          orbitConnectingGoodThreeRootExactOrderSolutionsWithMiddleIn_card_le
            p alpha gamma k omegaInv centerB centerC badTraces
      _ ≤ 16 * (10 + badTraceBudget) :=
        Nat.mul_le_mul_left 16 hbadTraces
  -- Step 3: some exact-order pair avoids the excluded middles; its middle is
  -- candidate-regular and outside `forbidden`.
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
    -- Unfold the local name `bad` so the `rw` below can unfold the
    -- `WithMiddleIn` definition to a `Finset.filter`.
    change z ∈
      orbitConnectingGoodThreeRootExactOrderSolutionsWithMiddleIn
        p alpha gamma k omegaInv centerB centerC badTraces
    rw [orbitConnectingGoodThreeRootExactOrderSolutionsWithMiddleIn]
    exact Finset.mem_filter.mpr ⟨by simpa [primitive, leftTrace, rightTrace] using hz,
      hmiddle⟩
  have hregular :
      OrderedTraceCandidateRegular
        frame.a1 frame.a2 frame.a3 z.1.1.middle := by
    by_contra hirregular
    apply hmiddleNotBadTraces
    apply Finset.mem_union_left
    -- Unfold the local name `safeRoots` to the root finset of
    -- `orderedTraceSafePolynomial`, so that `Multiset.mem_toFinset` and
    -- `Polynomial.mem_roots` rewrite the goal.
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
    -- Unfold the local name `badTraces := safeRoots ∪ forbidden` so that
    -- `Finset.mem_union_right` applies.
    change z.1.1.middle ∈ safeRoots ∪ forbidden
    exact Finset.mem_union_right safeRoots hmiddle
  rcases z with ⟨w, q⟩
  refine ⟨q, w, ?_, ?_, hregular, houtside⟩
  · simpa [leftTrace, rightTrace] using hz'.1
  · rw [Nat.card_units, Nat.card_zmod] at hz'
    exact hz'.2

/-- The explicit divisor inequality with coefficient `coefficient` absorbs a
fixed finite exceptional budget when `coefficient = 792 + budget`. -/
private theorem orbitConnecting_margin_of_explicitInequality
    (p budget coefficient : ℕ) [Fact p.Prime]
    (hcoefficient : coefficient = 792 + budget)
    (hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          (coefficient * Real.sqrt (p : ℝ)) < p) :
    ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            (792 * Real.sqrt (p : ℝ)) +
          budget <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p 1 := by
  have hpositive :=
    divisorsError_lt_primitiveTraceMoebiusMainTerm_of_explicitInequality
      (Nat.card (ZMod p)ˣ) p 1 coefficient
      Nat.card_pos (by norm_num) (by
        simpa using hexplicit)
  -- The product of the divisor count and `sqrt p` is at least one, so the
  -- additive `budget` is absorbed into `budget` extra units of the
  -- square-root error.
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
              (792 * Real.sqrt (p : ℝ)) +
            budget ≤
        ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
          (coefficient * Real.sqrt (p : ℝ)) := by
    calc
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
              (792 * Real.sqrt (p : ℝ)) +
            budget ≤
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
                (792 * Real.sqrt (p : ℝ)) +
              budget *
                (((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
                  Real.sqrt (p : ℝ)) :=
        by linarith
      _ =
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            (((792 + budget : ℕ) : ℝ) *
              Real.sqrt (p : ℝ)) := by
        push_cast
        ring
      _ =
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            (coefficient * Real.sqrt (p : ℝ)) := by
        rw [hcoefficient]
  exact hlarge.trans_lt hpositive

/-- A margin of `192 = 16 * (10 + 2)` produces a primitive,
candidate-regular witness whose middle trace also has nonzero
`incidenceCenteredNormObstruction frame`. -/
theorem
    exists_primitive_obstructionReady_orbitConnectingGoodThreeRootWitness_of_margin
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (frame : Coefficients (ZMod p))
    (alpha gamma k omegaInv centerB centerC : ZMod p)
    (hFrameA : frame.a1 ^ 2 ≠ 4)
    (hFrameB : frame.a2 ^ 2 ≠ 4)
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
          192 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p 1) :
    ∃ q : (ZMod p)ˣ,
      ∃ w :
          OrbitConnectingGoodThreeRootWitness
            alpha gamma k omegaInv centerB centerC,
        w.1.middle = splitTorusTrace q ∧
          orderOf q = p - 1 ∧
            OrderedTraceCandidateRegular
              frame.a1 frame.a2 frame.a3 w.1.middle ∧
              incidenceCenteredNormObstruction frame w.1.middle ≠ 0 := by
  let forbidden := incidenceCenteredNormObstructionBadTraces frame
  have hforbidden : forbidden.card ≤ 2 := by
    simpa [forbidden] using
      incidenceCenteredNormObstructionBadTraces_card_le_two frame
  obtain ⟨q, w, htrace, horder, hregular, houtside⟩ :=
    exists_primitive_candidateRegular_orbitConnectingGoodThreeRootWitness_outside_of_margin
      p hpFive frame alpha gamma k omegaInv centerB centerC
        hFrameA hFrameB homegaInv habsolute forbidden 2 hforbidden (by
          simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] using
            hmargin)
  refine ⟨q, w, htrace, horder, hregular, ?_⟩
  intro hzero
  exact houtside
    ((mem_incidenceCenteredNormObstructionBadTraces_iff
      frame w.1.middle hFrameA hFrameB).2 hzero)

/-- Under the explicit divisor inequality with coefficient
`984 = 792 + 192`, there is a primitive, candidate-regular witness whose
middle trace has nonzero `incidenceCenteredNormObstruction frame`. -/
theorem
    exists_primitive_obstructionReady_orbitConnectingGoodThreeRootWitness_of_explicitInequality
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (frame : Coefficients (ZMod p))
    (alpha gamma k omegaInv centerB centerC : ZMod p)
    (hFrameA : frame.a1 ^ 2 ≠ 4)
    (hFrameB : frame.a2 ^ 2 ≠ 4)
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
          (984 * Real.sqrt (p : ℝ)) < p) :
    ∃ q : (ZMod p)ˣ,
      ∃ w :
          OrbitConnectingGoodThreeRootWitness
            alpha gamma k omegaInv centerB centerC,
        w.1.middle = splitTorusTrace q ∧
          orderOf q = p - 1 ∧
            OrderedTraceCandidateRegular
              frame.a1 frame.a2 frame.a3 w.1.middle ∧
              incidenceCenteredNormObstruction frame w.1.middle ≠ 0 := by
  apply
    exists_primitive_obstructionReady_orbitConnectingGoodThreeRootWitness_of_margin
      p hpFive frame alpha gamma k omegaInv centerB centerC
        hFrameA hFrameB homegaInv habsolute
  exact
    orbitConnecting_margin_of_explicitInequality
      p 192 984 (by norm_num) hexplicit

/-- A margin of `240 = 16 * (10 + 2 + 2 + 1)` produces a primitive,
candidate-regular witness whose middle trace forms a connecting incidence
pair with the prescribed candidate-regular trace `eta`, provided `eta` has
nonzero `incidenceCenteredNormObstruction frame`. -/
theorem
    exists_primitive_connectingPair_orbitConnectingGoodThreeRootWitness_of_margin
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (frame : Coefficients (ZMod p))
    (eta : ZMod p)
    (alpha gamma k omegaInv centerB centerC : ZMod p)
    (hFrameA : frame.a1 ^ 2 ≠ 4)
    (hFrameB : frame.a2 ^ 2 ≠ 4)
    (hetaRegular :
      OrderedTraceCandidateRegular
        frame.a1 frame.a2 frame.a3 eta)
    (hetaObstruction :
      incidenceCenteredNormObstruction frame eta ≠ 0)
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
          240 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p 1) :
    ∃ q : (ZMod p)ˣ,
      ∃ w :
          OrbitConnectingGoodThreeRootWitness
            alpha gamma k omegaInv centerB centerC,
        w.1.middle = splitTorusTrace q ∧
          orderOf q = p - 1 ∧
            OrderedTraceCandidateRegular
              frame.a1 frame.a2 frame.a3 w.1.middle ∧
              IsConnectingIncidencePair frame w.1.middle eta := by
  classical
  -- Forbid the zeros of the centered-norm obstruction, the zeros of the
  -- pair obstruction with `eta`, and `eta` itself: at most five traces.
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
      _ ≤ 2 + 2 :=
        Nat.add_le_add hcenteredBad hpairBad
      _ = 4 := by norm_num
  have hsingleton : ({eta} : Finset (ZMod p)).card ≤ 1 := by
    simp
  have hforbidden : forbidden.card ≤ 5 := by
    calc
      forbidden.card ≤
          (centeredBad ∪ pairBad).card +
            ({eta} : Finset (ZMod p)).card := by
        simpa [forbidden] using
          Finset.card_union_le
            (centeredBad ∪ pairBad) ({eta} : Finset (ZMod p))
      _ ≤ 4 + 1 := Nat.add_le_add hunion hsingleton
      _ = 5 := by norm_num
  obtain ⟨q, w, htrace, horder, hregular, houtside⟩ :=
    exists_primitive_candidateRegular_orbitConnectingGoodThreeRootWitness_outside_of_margin
      p hpFive frame alpha gamma k omegaInv centerB centerC
        hFrameA hFrameB homegaInv habsolute forbidden 5 hforbidden (by
          simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] using
            hmargin)
  -- Avoiding each forbidden part gives one component of
  -- `IsConnectingIncidencePair`.
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

/-- Under the explicit divisor inequality with coefficient
`1032 = 792 + 240`, there is a primitive, candidate-regular witness whose
middle trace forms a connecting incidence pair with the prescribed trace
`eta`. -/
theorem
    exists_primitive_connectingPair_orbitConnectingGoodThreeRootWitness_of_explicitInequality
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (frame : Coefficients (ZMod p))
    (eta : ZMod p)
    (alpha gamma k omegaInv centerB centerC : ZMod p)
    (hFrameA : frame.a1 ^ 2 ≠ 4)
    (hFrameB : frame.a2 ^ 2 ≠ 4)
    (hetaRegular :
      OrderedTraceCandidateRegular
        frame.a1 frame.a2 frame.a3 eta)
    (hetaObstruction :
      incidenceCenteredNormObstruction frame eta ≠ 0)
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
          (1032 * Real.sqrt (p : ℝ)) < p) :
    ∃ q : (ZMod p)ˣ,
      ∃ w :
          OrbitConnectingGoodThreeRootWitness
            alpha gamma k omegaInv centerB centerC,
        w.1.middle = splitTorusTrace q ∧
          orderOf q = p - 1 ∧
            OrderedTraceCandidateRegular
              frame.a1 frame.a2 frame.a3 w.1.middle ∧
              IsConnectingIncidencePair frame w.1.middle eta := by
  apply
    exists_primitive_connectingPair_orbitConnectingGoodThreeRootWitness_of_margin
      p hpFive frame eta alpha gamma k omegaInv centerB centerC
        hFrameA hFrameB hetaRegular hetaObstruction homegaInv habsolute
  exact
    orbitConnecting_margin_of_explicitInequality
      p 240 1032 (by norm_num) hexplicit

end

end GenMarkoff.General.Cage
