import GenMarkoff.Symmetric.ExceptionalRouting
import GenMarkoff.Symmetric.MiddleGame.ShiftedTraceEquation
import GenMarkoff.TraceCurve.WeightedShiftedCoverCounting

/-!
# Candidate-regular primitive traces on weighted shifted covers

The weighted shifted primitive count produces pairs whose common trace is
primitive on the ordinary split torus, but it does not by itself ensure that
this trace is regular for the next symmetric fiber.  The reduced symmetric
safe polynomial has at most seven roots.  Above each fixed trace there are at
most two weighted left lifts and at most two ordinary-trace right lifts, so at
most twenty-eight primitive pairs are candidate-irregular.
-/

namespace GenMarkoff.Symmetric.Endgame

open BGS.Markoff Polynomial

noncomputable section

/-- A fixed common trace has at most four lifts among the weighted shifted
primitive pairs: at most two on each torus factor. -/
theorem weightedShiftedSplitPrimitiveTraceSolutions_traceFiber_card_le_four
    (p : ℕ) [Fact p.Prime]
    (alpha beta gamma : ZMod p) (orbitExponent : ℕ)
    (halpha : alpha ≠ 0) (target : ZMod p) :
    ((weightedShiftedSplitPrimitiveTraceSolutions
        p alpha beta gamma orbitExponent).filter fun z ↦
          splitTorusTrace z.2 = target).card ≤ 4 := by
  classical
  let S :=
    (weightedShiftedSplitPrimitiveTraceSolutions
      p alpha beta gamma orbitExponent).filter fun z ↦
        splitTorusTrace z.2 = target
  let leftPolynomial :=
    twistedTracePolynomial (beta / alpha) ((target - gamma) / alpha)
  let rightPolynomial := twistedTracePolynomial (1 : ZMod p) target
  have hleftPolynomial : leftPolynomial ≠ 0 :=
    (twistedTracePolynomial_monic (beta / alpha)
      ((target - gamma) / alpha)).ne_zero
  have hrightPolynomial : rightPolynomial ≠ 0 :=
    (twistedTracePolynomial_monic (1 : ZMod p) target).ne_zero
  let rootEmbedding :
      ↥S ↪
        ↥leftPolynomial.roots.toFinset ×
          ↥rightPolynomial.roots.toFinset :=
    { toFun := fun z ↦
        (⟨((z.1.1.1 : (ZMod p)ˣ) : ZMod p), by
            rw [Multiset.mem_toFinset,
              Polynomial.mem_roots hleftPolynomial]
            apply (eval_twistedTracePolynomial_eq_zero_iff
              (beta / alpha) ((target - gamma) / alpha)
              (z.1.1.1 : (ZMod p)ˣ)).2
            apply
              (MiddleGame.shiftedWeightedSplitTorusTrace_eq_iff_twistedUnitTrace_eq
                alpha beta gamma target
                (z.1.1.1 : (ZMod p)ˣ) halpha).mp
            have hzMem :
                z.1 ∈ weightedShiftedSplitPrimitiveTraceSolutions
                  p alpha beta gamma orbitExponent :=
              (Finset.mem_filter.mp z.2).1
            have hzTrace :=
              (mem_traceExactOrderSolutions_iff
                (weightedShiftedSplitTorusTrace
                  (ZMod p) alpha beta gamma)
                (splitTorusTrace : (ZMod p)ˣ → ZMod p)
                orbitExponent (Nat.card (ZMod p)ˣ) z.1).mp hzMem
            exact hzTrace.1.trans (Finset.mem_filter.mp z.2).2⟩,
          ⟨((z.1.2 : (ZMod p)ˣ) : ZMod p), by
            rw [Multiset.mem_toFinset,
              Polynomial.mem_roots hrightPolynomial]
            apply (eval_twistedTracePolynomial_eq_zero_iff
              (1 : ZMod p) target z.1.2).2
            have hzTarget : splitTorusTrace z.1.2 = target :=
              (Finset.mem_filter.mp z.2).2
            simpa only [twistedUnitTrace, splitTorusTrace, one_mul] using
              hzTarget⟩)
      inj' := by
        intro x y hxy
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          apply Units.ext
          exact congrArg (fun q ↦ (q.1 : ZMod p)) hxy
        · apply Units.ext
          exact congrArg (fun q ↦ (q.2 : ZMod p)) hxy }
  have hcard :
      S.card ≤
        leftPolynomial.roots.toFinset.card *
          rightPolynomial.roots.toFinset.card := by
    simpa only [Fintype.card_coe, Fintype.card_prod] using
      Fintype.card_le_of_injective rootEmbedding rootEmbedding.injective
  have hleftRoots : leftPolynomial.roots.toFinset.card ≤ 2 := by
    calc
      leftPolynomial.roots.toFinset.card ≤ leftPolynomial.roots.card :=
        Multiset.toFinset_card_le _
      _ ≤ leftPolynomial.natDegree := Polynomial.card_roots' _
      _ = 2 := twistedTracePolynomial_natDegree
        (beta / alpha) ((target - gamma) / alpha)
  have hrightRoots : rightPolynomial.roots.toFinset.card ≤ 2 := by
    calc
      rightPolynomial.roots.toFinset.card ≤ rightPolynomial.roots.card :=
        Multiset.toFinset_card_le _
      _ ≤ rightPolynomial.natDegree := Polynomial.card_roots' _
      _ = 2 := twistedTracePolynomial_natDegree (1 : ZMod p) target
  change S.card ≤ 4
  calc
    S.card ≤
        leftPolynomial.roots.toFinset.card *
          rightPolynomial.roots.toFinset.card := hcard
    _ ≤ 2 * 2 := Nat.mul_le_mul hleftRoots hrightRoots
    _ = 4 := by norm_num

/-- The primitive weighted shifted pairs whose common trace annihilates the
reduced symmetric safe polynomial. -/
noncomputable abbrev weightedShiftedSplitPrimitiveUnsafeTraceSolutions
    (p : ℕ) [Fact p.Prime]
    (c alpha beta gamma : ZMod p) (orbitExponent : ℕ) :=
  (weightedShiftedSplitPrimitiveTraceSolutions
    p alpha beta gamma orbitExponent).filter fun z ↦
      eval (splitTorusTrace z.2) (safePolynomial c) = 0

/-- At most twenty-eight weighted shifted primitive pairs have a
candidate-irregular common trace. -/
theorem weightedShiftedSplitPrimitiveUnsafeTraceSolutions_card_le_twentyEight
    (p : ℕ) [Fact p.Prime]
    (c alpha beta gamma : ZMod p) (orbitExponent : ℕ)
    (h2 : (2 : ZMod p) ≠ 0) (hc : c ^ 2 ≠ 4)
    (halpha : alpha ≠ 0) :
    (weightedShiftedSplitPrimitiveUnsafeTraceSolutions
      p c alpha beta gamma orbitExponent).card ≤ 28 := by
  classical
  let primitive :=
    weightedShiftedSplitPrimitiveTraceSolutions
      p alpha beta gamma orbitExponent
  let traceValue :
      (powMonoidHom orbitExponent :
        (ZMod p)ˣ →* (ZMod p)ˣ).range × (ZMod p)ˣ → ZMod p :=
    fun z ↦ splitTorusTrace z.2
  let bad := primitive.filter fun z ↦
    eval (traceValue z) (safePolynomial c) = 0
  have hbadFiber : ∀ t ∈ bad.image traceValue,
      (bad.filter fun z ↦ traceValue z = t).card ≤ 4 := by
    intro t _
    calc
      (bad.filter fun z ↦ traceValue z = t).card ≤
          (primitive.filter fun z ↦ traceValue z = t).card := by
        apply Finset.card_le_card
        intro z hz
        simp only [bad, Finset.mem_filter] at hz ⊢
        exact ⟨hz.1.1, hz.2⟩
      _ ≤ 4 := by
        simpa [primitive, traceValue] using
          weightedShiftedSplitPrimitiveTraceSolutions_traceFiber_card_le_four
            p alpha beta gamma orbitExponent halpha t
  have hp : safePolynomial c ≠ 0 := safePolynomial_ne_zero c h2 hc
  have himage :
      bad.image traceValue ⊆ (safePolynomial c).roots.toFinset := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨z, hz, rfl⟩
    have hzero :
        eval (traceValue z) (safePolynomial c) = 0 := by
      exact (Finset.mem_filter.mp hz).2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact hzero
  have himageCard :
      (bad.image traceValue).card ≤
        (safePolynomial c).roots.toFinset.card :=
    Finset.card_le_card himage
  have hrootCard : (safePolynomial c).roots.toFinset.card ≤ 7 :=
    safePolynomial_roots_card_le c
  change bad.card ≤ 28
  calc
    bad.card ≤ 4 * (bad.image traceValue).card :=
      Finset.card_le_mul_card_image bad 4 hbadFiber
    _ ≤ 4 * (safePolynomial c).roots.toFinset.card :=
      Nat.mul_le_mul_left 4 himageCard
    _ ≤ 4 * 7 := Nat.mul_le_mul_left 4 hrootCard
    _ = 28 := by norm_num

/-- More than twenty-eight weighted shifted primitive pairs force one whose
common trace is candidate-regular for the symmetric family. -/
theorem exists_weightedShiftedSplitPrimitiveTracePair_candidateRegular_of_twentyEight_lt_card
    (p : ℕ) [Fact p.Prime]
    (c alpha beta gamma : ZMod p) (orbitExponent : ℕ)
    (h2 : (2 : ZMod p) ≠ 0) (hc : c ^ 2 ≠ 4)
    (halpha : alpha ≠ 0)
    (hcard :
      28 <
        (weightedShiftedSplitPrimitiveTraceSolutions
          p alpha beta gamma orbitExponent).card) :
    ∃ z ∈ weightedShiftedSplitPrimitiveTraceSolutions
        p alpha beta gamma orbitExponent,
      OrderedTraceCandidateRegular c c c (splitTorusTrace z.2) := by
  classical
  let primitive :=
    weightedShiftedSplitPrimitiveTraceSolutions
      p alpha beta gamma orbitExponent
  by_contra hnone
  push Not at hnone
  have hsubset :
      primitive ⊆
        weightedShiftedSplitPrimitiveUnsafeTraceSolutions
          p c alpha beta gamma orbitExponent := by
    intro z hz
    rw [Finset.mem_filter]
    refine ⟨hz, ?_⟩
    by_contra hsafe
    exact hnone z hz
      (candidateRegular_of_eval_safePolynomial_ne_zero
        c (splitTorusTrace z.2) hc hsafe)
  have hle := Finset.card_le_card hsubset
  have hbad :=
    weightedShiftedSplitPrimitiveUnsafeTraceSolutions_card_le_twentyEight
      p c alpha beta gamma orbitExponent h2 hc halpha
  have : primitive.card ≤ 28 := hle.trans hbad
  exact (Nat.not_le_of_lt (by simpa [primitive] using hcard)) this

/-- The weighted shifted count estimate, strengthened by a twenty-eight-point
margin, produces a primitive ordinary trace that is also candidate-regular
for the symmetric family. -/
theorem exists_weightedShiftedSplitPrimitiveTracePair_candidateRegular_of_error_add_twentyEight_lt_main
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (c alpha beta gamma : ZMod p) (orbitExponent : ℕ)
    (h2 : (2 : ZMod p) ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hproductOne : alpha * beta ≠ 1)
    (hD2 : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0)
    (horbitPositive : 0 < orbitExponent)
    (horbitChar : (orbitExponent : ZMod p) ≠ 0)
    (horbitDvd : orbitExponent ∣ Nat.card (ZMod p)ˣ)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) +
          28 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p orbitExponent) :
    ∃ z : (powMonoidHom orbitExponent :
        (ZMod p)ˣ →* (ZMod p)ˣ).range × (ZMod p)ˣ,
      weightedShiftedSplitTorusTrace
          (ZMod p) alpha beta gamma z.1 =
          splitTorusTrace z.2 ∧
        orderOf z.2 = Nat.card (ZMod p)ˣ ∧
          OrderedTraceCandidateRegular c c c (splitTorusTrace z.2) := by
  let primitive :=
    weightedShiftedSplitPrimitiveTraceSolutions
      p alpha beta gamma orbitExponent
  let mainTerm :=
    primitiveTraceMoebiusMainTerm
      (Nat.card (ZMod p)ˣ) p orbitExponent
  let error :=
    ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
      ((coefficient : ℝ) * Real.sqrt (p : ℝ))
  have henvelope :
      |(primitive.card : ℝ) - mainTerm| ≤ error := by
    simpa [primitive, mainTerm, error] using
      weightedShiftedSplitPrimitiveTraceSolutions_card_error_le
        p coefficient hWeil alpha beta gamma orbitExponent h2
        halpha hbeta hproductOne hD2 horbitPositive horbitChar horbitDvd
  have hlower :
      mainTerm - (primitive.card : ℝ) ≤
        |(primitive.card : ℝ) - mainTerm| := by
    simpa only [neg_sub] using
      neg_le_abs ((primitive.card : ℝ) - mainTerm)
  have hcardReal : (28 : ℝ) < primitive.card := by
    have hmargin' : error + 28 < mainTerm := by
      simpa [error, mainTerm] using hmargin
    linarith
  have hcard : 28 < primitive.card := by
    exact_mod_cast hcardReal
  obtain ⟨z, hz, hregular⟩ :=
    exists_weightedShiftedSplitPrimitiveTracePair_candidateRegular_of_twentyEight_lt_card
      p c alpha beta gamma orbitExponent h2 hc halpha
      (by simpa [primitive] using hcard)
  have hz' :=
    (mem_traceExactOrderSolutions_iff
      (weightedShiftedSplitTorusTrace
        (ZMod p) alpha beta gamma)
      (splitTorusTrace : (ZMod p)ˣ → ZMod p)
      orbitExponent (Nat.card (ZMod p)ˣ) z).mp hz
  exact ⟨z, hz'.1, hz'.2, hregular⟩

end

end GenMarkoff.Symmetric.Endgame
