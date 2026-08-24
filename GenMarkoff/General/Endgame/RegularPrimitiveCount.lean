import GenMarkoff.Symmetric.Endgame.RegularPrimitiveCount
import GenMarkoff.TraceCurve.ExceptionalRouting

/-!
# Candidate-regular primitive traces for an ordered coefficient frame

The weighted shifted primitive count produces pairs whose common trace is
primitive on the ordinary split torus.  For an arbitrary ordered frame
`(A, B, C)`, candidate regularity is controlled by
`orderedTraceSafePolynomial A B C`.  Its ten-root bound, together with the
generic four-lift bound above each trace, leaves at most `4 * 10 = 40`
candidate-irregular primitive pairs.

## New consideration in the unequal-coefficient case

The symmetric degree-seven safe polynomial uses cancellations that depend on
coefficient equality.  They are unavailable for an ordered frame, so all six
ordered obstruction factors must be retained and the root budget rises from
seven to ten.  Moreover, nonvanishing of the ordered safe polynomial requires
`A ^ 2 ≠ 4` and `B ^ 2 ≠ 4` in these precise ordered roles; no coefficient
permutation is used, and no corresponding hypothesis on `C` is needed for
this polynomial-count step.

The four-lift trace-fiber theorem is coefficient-independent.  We reuse it at
its existing explicit theorem boundary rather than duplicating its
twisted-trace argument.
-/

namespace GenMarkoff.General.Endgame

open BGS.Markoff Polynomial

noncomputable section

/-- The primitive weighted shifted pairs whose common trace annihilates the
ordered safe polynomial for `(A, B, C)`. -/
noncomputable abbrev weightedShiftedSplitPrimitiveUnsafeTraceSolutions
    (p : ℕ) [Fact p.Prime]
    (A B C alpha beta gamma : ZMod p) (orbitExponent : ℕ) :=
  (weightedShiftedSplitPrimitiveTraceSolutions
    p alpha beta gamma orbitExponent).filter fun z ↦
      eval (splitTorusTrace z.2) (orderedTraceSafePolynomial A B C) = 0

/-- At most forty weighted shifted primitive pairs have a
candidate-irregular common trace for the ordered frame `(A, B, C)`. -/
theorem weightedShiftedSplitPrimitiveUnsafeTraceSolutions_card_le_forty
    (p : ℕ) [Fact p.Prime]
    (A B C alpha beta gamma : ZMod p) (orbitExponent : ℕ)
    (h2 : (2 : ZMod p) ≠ 0)
    (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4)
    (halpha : alpha ≠ 0) :
    (weightedShiftedSplitPrimitiveUnsafeTraceSolutions
      p A B C alpha beta gamma orbitExponent).card ≤ 40 := by
  classical
  let primitive :=
    weightedShiftedSplitPrimitiveTraceSolutions
      p alpha beta gamma orbitExponent
  let traceValue :
      (powMonoidHom orbitExponent :
        (ZMod p)ˣ →* (ZMod p)ˣ).range × (ZMod p)ˣ → ZMod p :=
    fun z ↦ splitTorusTrace z.2
  let bad := primitive.filter fun z ↦
    eval (traceValue z) (orderedTraceSafePolynomial A B C) = 0
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
          GenMarkoff.Symmetric.Endgame.weightedShiftedSplitPrimitiveTraceSolutions_traceFiber_card_le_four
            p alpha beta gamma orbitExponent halpha t
  have hp : orderedTraceSafePolynomial A B C ≠ 0 :=
    orderedTraceSafePolynomial_ne_zero A B C h2 hA hB
  have himage :
      bad.image traceValue ⊆
        (orderedTraceSafePolynomial A B C).roots.toFinset := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨z, hz, rfl⟩
    have hzero :
        eval (traceValue z) (orderedTraceSafePolynomial A B C) = 0 := by
      exact (Finset.mem_filter.mp hz).2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact hzero
  have himageCard :
      (bad.image traceValue).card ≤
        (orderedTraceSafePolynomial A B C).roots.toFinset.card :=
    Finset.card_le_card himage
  have hrootCard :
      (orderedTraceSafePolynomial A B C).roots.toFinset.card ≤ 10 :=
    orderedTraceSafePolynomial_roots_card_le A B C
  change bad.card ≤ 40
  calc
    bad.card ≤ 4 * (bad.image traceValue).card :=
      Finset.card_le_mul_card_image bad 4 hbadFiber
    _ ≤ 4 * (orderedTraceSafePolynomial A B C).roots.toFinset.card :=
      Nat.mul_le_mul_left 4 himageCard
    _ ≤ 4 * 10 := Nat.mul_le_mul_left 4 hrootCard
    _ = 40 := by norm_num

/-- More than forty weighted shifted primitive pairs force one whose common
trace is candidate-regular for the ordered frame `(A, B, C)`. -/
theorem exists_weightedShiftedSplitPrimitiveTracePair_candidateRegular_of_forty_lt_card
    (p : ℕ) [Fact p.Prime]
    (A B C alpha beta gamma : ZMod p) (orbitExponent : ℕ)
    (h2 : (2 : ZMod p) ≠ 0)
    (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4)
    (halpha : alpha ≠ 0)
    (hcard :
      40 <
        (weightedShiftedSplitPrimitiveTraceSolutions
          p alpha beta gamma orbitExponent).card) :
    ∃ z ∈ weightedShiftedSplitPrimitiveTraceSolutions
        p alpha beta gamma orbitExponent,
      OrderedTraceCandidateRegular A B C (splitTorusTrace z.2) := by
  classical
  let primitive :=
    weightedShiftedSplitPrimitiveTraceSolutions
      p alpha beta gamma orbitExponent
  by_contra hnone
  push Not at hnone
  have hsubset :
      primitive ⊆
        weightedShiftedSplitPrimitiveUnsafeTraceSolutions
          p A B C alpha beta gamma orbitExponent := by
    intro z hz
    rw [Finset.mem_filter]
    refine ⟨hz, ?_⟩
    by_contra hsafe
    exact hnone z hz
      ((orderedTraceSafePolynomial_eval_ne_zero_iff
        A B C (splitTorusTrace z.2)).mp hsafe)
  have hle := Finset.card_le_card hsubset
  have hbad :=
    weightedShiftedSplitPrimitiveUnsafeTraceSolutions_card_le_forty
      p A B C alpha beta gamma orbitExponent h2 hA hB halpha
  have : primitive.card ≤ 40 := hle.trans hbad
  exact (Nat.not_le_of_lt (by simpa [primitive] using hcard)) this

/-- The weighted shifted count estimate, strengthened by a forty-point margin,
produces a primitive ordinary trace that is candidate-regular for the ordered
frame `(A, B, C)`. -/
theorem exists_weightedShiftedSplitPrimitiveTracePair_candidateRegular_of_error_add_forty_lt_main
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (A B C alpha beta gamma : ZMod p) (orbitExponent : ℕ)
    (h2 : (2 : ZMod p) ≠ 0)
    (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hproductOne : alpha * beta ≠ 1)
    (hD2 : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0)
    (horbitPositive : 0 < orbitExponent)
    (horbitChar : (orbitExponent : ZMod p) ≠ 0)
    (horbitDvd : orbitExponent ∣ Nat.card (ZMod p)ˣ)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) +
          40 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p orbitExponent) :
    ∃ z : (powMonoidHom orbitExponent :
        (ZMod p)ˣ →* (ZMod p)ˣ).range × (ZMod p)ˣ,
      weightedShiftedSplitTorusTrace
          (ZMod p) alpha beta gamma z.1 =
          splitTorusTrace z.2 ∧
        orderOf z.2 = Nat.card (ZMod p)ˣ ∧
          OrderedTraceCandidateRegular A B C (splitTorusTrace z.2) := by
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
  have hcardReal : (40 : ℝ) < primitive.card := by
    have hmargin' : error + 40 < mainTerm := by
      simpa [error, mainTerm] using hmargin
    linarith
  have hcard : 40 < primitive.card := by
    exact_mod_cast hcardReal
  obtain ⟨z, hz, hregular⟩ :=
    exists_weightedShiftedSplitPrimitiveTracePair_candidateRegular_of_forty_lt_card
      p A B C alpha beta gamma orbitExponent h2 hA hB halpha
      (by simpa [primitive] using hcard)
  have hz' :=
    (mem_traceExactOrderSolutions_iff
      (weightedShiftedSplitTorusTrace
        (ZMod p) alpha beta gamma)
      (splitTorusTrace : (ZMod p)ˣ → ZMod p)
      orbitExponent (Nat.card (ZMod p)ˣ) z).mp hz
  exact ⟨z, hz'.1, hz'.2, hregular⟩

end

end GenMarkoff.General.Endgame
