import GenMarkoff.General.Endgame.RegularPrimitiveCount
import GenMarkoff.General.Cage.ConnectingIncidenceAlgebra

/-!
# Cage-ready primitive traces

The connecting postprocessing of a canonical first-axis endpoint may use
either moving coordinate.  The final primitive trace is therefore chosen
away from four finite exceptional loci:

* the ordered safe polynomial in the frame `(a₁, a₂, a₃)`;
* the ordered safe polynomial in the reverse frame `(a₁, a₃, a₂)`;
* the first-to-second incidence/centered-norm resultant obstruction; and
* the first-to-third obstruction, obtained by explicitly swapping the two
  moving coefficients in the coefficient triple.

The two safe polynomials have degree at most ten and the two resultant
obstructions have degree at most two.  Thus the combined polynomial has
degree at most twenty-four.  Since a fixed primitive trace has at most four
weighted-shifted lifts, at most ninety-six primitive pairs are discarded.

This is a genuinely new finite exclusion in the general cage.  It does not
permute the fixed surface: the swapped coefficient triple is used only to
write the algebraic obstruction for the other directed incidence problem.
-/

namespace GenMarkoff.General.Endgame

open BGS.Markoff Polynomial
open GenMarkoff.General.Cage

noncomputable section

/-- The coefficient ordering used only for the first-to-third incidence
calculation. -/
def reverseFirstAxisMovingCoefficients
    {R : Type*} (a : Coefficients R) : Coefficients R :=
  ⟨a.a1, a.a3, a.a2⟩

@[simp]
theorem reverseFirstAxisMovingCoefficients_a1
    {R : Type*} (a : Coefficients R) :
    (reverseFirstAxisMovingCoefficients a).a1 = a.a1 :=
  rfl

@[simp]
theorem reverseFirstAxisMovingCoefficients_a2
    {R : Type*} (a : Coefficients R) :
    (reverseFirstAxisMovingCoefficients a).a2 = a.a3 :=
  rfl

@[simp]
theorem reverseFirstAxisMovingCoefficients_a3
    {R : Type*} (a : Coefficients R) :
    (reverseFirstAxisMovingCoefficients a).a3 = a.a2 :=
  rfl

variable {K : Type*} [Field K]

/-- The four simultaneous nonvanishing conditions needed before the
endpoint-to-connecting count is dispatched in either moving direction. -/
def CageReadyFirstAxisTrace
    (a : Coefficients K) (t : K) : Prop :=
  OrderedTraceCandidateRegular a.a1 a.a2 a.a3 t ∧
    OrderedTraceCandidateRegular a.a1 a.a3 a.a2 t ∧
      incidenceCenteredNormObstruction a t ≠ 0 ∧
        incidenceCenteredNormObstruction
          (reverseFirstAxisMovingCoefficients a) t ≠ 0

/-- A single degree-at-most-twenty-four polynomial encoding the cage-ready
trace conditions. -/
def cageReadyFirstAxisTracePolynomial
    (a : Coefficients K) : K[X] :=
  orderedTraceSafePolynomial a.a1 a.a2 a.a3 *
    orderedTraceSafePolynomial a.a1 a.a3 a.a2 *
      incidenceCenteredNormObstructionPolynomial a *
        incidenceCenteredNormObstructionPolynomial
          (reverseFirstAxisMovingCoefficients a)

theorem cageReadyFirstAxisTracePolynomial_eval_ne_zero_iff
    (a : Coefficients K) (t : K) :
    eval t (cageReadyFirstAxisTracePolynomial a) ≠ 0 ↔
      CageReadyFirstAxisTrace a t := by
  simp only [cageReadyFirstAxisTracePolynomial, eval_mul,
    CageReadyFirstAxisTrace,
    orderedTraceSafePolynomial_eval_ne_zero_iff,
    eval_incidenceCenteredNormObstructionPolynomial,
    mul_ne_zero_iff]
  tauto

theorem cageReadyFirstAxisTracePolynomial_ne_zero
    (a : Coefficients K)
    (h2 : (2 : K) ≠ 0)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4) :
    cageReadyFirstAxisTracePolynomial a ≠ 0 := by
  unfold cageReadyFirstAxisTracePolynomial
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (orderedTraceSafePolynomial_ne_zero
          a.a1 a.a2 a.a3 h2 hA1 hA2)
        (orderedTraceSafePolynomial_ne_zero
          a.a1 a.a3 a.a2 h2 hA1 hA3))
      (incidenceCenteredNormObstructionPolynomial_ne_zero
        a hA1 hA2))
    (incidenceCenteredNormObstructionPolynomial_ne_zero
      (reverseFirstAxisMovingCoefficients a) hA1 hA3)

theorem cageReadyFirstAxisTracePolynomial_natDegree_le
    (a : Coefficients K) :
    (cageReadyFirstAxisTracePolynomial a).natDegree ≤ 24 := by
  unfold cageReadyFirstAxisTracePolynomial
  have hsafe :
      (orderedTraceSafePolynomial a.a1 a.a2 a.a3).natDegree ≤ 10 :=
    orderedTraceSafePolynomial_natDegree_le _ _ _
  have hreverse :
      (orderedTraceSafePolynomial a.a1 a.a3 a.a2).natDegree ≤ 10 :=
    orderedTraceSafePolynomial_natDegree_le _ _ _
  have hobs :
      (incidenceCenteredNormObstructionPolynomial a).natDegree ≤ 2 :=
    incidenceCenteredNormObstructionPolynomial_natDegree_le _
  have hobsReverse :
      (incidenceCenteredNormObstructionPolynomial
        (reverseFirstAxisMovingCoefficients a)).natDegree ≤ 2 :=
    incidenceCenteredNormObstructionPolynomial_natDegree_le _
  have hsafePair :
      (orderedTraceSafePolynomial a.a1 a.a2 a.a3 *
        orderedTraceSafePolynomial a.a1 a.a3 a.a2).natDegree ≤ 20 :=
    natDegree_mul_le.trans (by omega)
  have hthree :
      (orderedTraceSafePolynomial a.a1 a.a2 a.a3 *
          orderedTraceSafePolynomial a.a1 a.a3 a.a2 *
        incidenceCenteredNormObstructionPolynomial a).natDegree ≤ 22 :=
    natDegree_mul_le.trans (by omega)
  exact natDegree_mul_le.trans (by omega)

theorem cageReadyFirstAxisTracePolynomial_roots_card_le_twentyFour
    (a : Coefficients K) [DecidableEq K] :
    (cageReadyFirstAxisTracePolynomial a).roots.toFinset.card ≤ 24 := by
  calc
    (cageReadyFirstAxisTracePolynomial a).roots.toFinset.card ≤
        (cageReadyFirstAxisTracePolynomial a).roots.card :=
      Multiset.toFinset_card_le _
    _ ≤ (cageReadyFirstAxisTracePolynomial a).natDegree :=
      Polynomial.card_roots' _
    _ ≤ 24 := cageReadyFirstAxisTracePolynomial_natDegree_le a

section FiniteField

/-- Primitive shifted-trace pairs whose common trace is not cage-ready. -/
noncomputable abbrev weightedShiftedSplitPrimitiveCageUnsafeTraceSolutions
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (alpha beta gamma : ZMod p) (orbitExponent : ℕ) :=
  (weightedShiftedSplitPrimitiveTraceSolutions
    p alpha beta gamma orbitExponent).filter fun z ↦
      eval (splitTorusTrace z.2)
        (cageReadyFirstAxisTracePolynomial a) = 0

/-- At most ninety-six primitive shifted-trace pairs have a trace that is
unsafe for one of the two directed connecting postprocesses. -/
theorem
    weightedShiftedSplitPrimitiveCageUnsafeTraceSolutions_card_le_ninetySix
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (alpha beta gamma : ZMod p) (orbitExponent : ℕ)
    (h2 : (2 : ZMod p) ≠ 0)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (halpha : alpha ≠ 0) :
    (weightedShiftedSplitPrimitiveCageUnsafeTraceSolutions
      p a alpha beta gamma orbitExponent).card ≤ 96 := by
  classical
  let primitive :=
    weightedShiftedSplitPrimitiveTraceSolutions
      p alpha beta gamma orbitExponent
  let traceValue :
      (powMonoidHom orbitExponent :
        (ZMod p)ˣ →* (ZMod p)ˣ).range × (ZMod p)ˣ → ZMod p :=
    fun z ↦ splitTorusTrace z.2
  let bad := primitive.filter fun z ↦
    eval (traceValue z) (cageReadyFirstAxisTracePolynomial a) = 0
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
  have himage :
      bad.image traceValue ⊆
        (cageReadyFirstAxisTracePolynomial a).roots.toFinset := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨z, hz, rfl⟩
    have hzero :
        eval (traceValue z) (cageReadyFirstAxisTracePolynomial a) = 0 :=
      (Finset.mem_filter.mp hz).2
    have hpoly : cageReadyFirstAxisTracePolynomial a ≠ 0 :=
      cageReadyFirstAxisTracePolynomial_ne_zero
        a h2 hA1 hA2 hA3
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hpoly]
    exact hzero
  have himageCard :
      (bad.image traceValue).card ≤
        (cageReadyFirstAxisTracePolynomial a).roots.toFinset.card :=
    Finset.card_le_card himage
  have hrootCard :
      (cageReadyFirstAxisTracePolynomial a).roots.toFinset.card ≤ 24 :=
    cageReadyFirstAxisTracePolynomial_roots_card_le_twentyFour a
  change bad.card ≤ 96
  calc
    bad.card ≤ 4 * (bad.image traceValue).card :=
      Finset.card_le_mul_card_image bad 4 hbadFiber
    _ ≤ 4 * (cageReadyFirstAxisTracePolynomial a).roots.toFinset.card :=
      Nat.mul_le_mul_left 4 himageCard
    _ ≤ 4 * 24 := Nat.mul_le_mul_left 4 hrootCard
    _ = 96 := by norm_num

/-- More than ninety-six primitive shifted-trace pairs force a cage-ready
common trace. -/
theorem
    exists_weightedShiftedSplitPrimitiveTracePair_cageReady_of_ninetySix_lt_card
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (alpha beta gamma : ZMod p) (orbitExponent : ℕ)
    (h2 : (2 : ZMod p) ≠ 0)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (halpha : alpha ≠ 0)
    (hcard :
      96 <
        (weightedShiftedSplitPrimitiveTraceSolutions
          p alpha beta gamma orbitExponent).card) :
    ∃ z ∈ weightedShiftedSplitPrimitiveTraceSolutions
        p alpha beta gamma orbitExponent,
      CageReadyFirstAxisTrace a (splitTorusTrace z.2) := by
  classical
  let primitive :=
    weightedShiftedSplitPrimitiveTraceSolutions
      p alpha beta gamma orbitExponent
  by_contra hnone
  push Not at hnone
  have hsubset :
      primitive ⊆
        weightedShiftedSplitPrimitiveCageUnsafeTraceSolutions
          p a alpha beta gamma orbitExponent := by
    intro z hz
    rw [Finset.mem_filter]
    refine ⟨hz, ?_⟩
    by_contra hsafe
    exact hnone z hz
      ((cageReadyFirstAxisTracePolynomial_eval_ne_zero_iff
        a (splitTorusTrace z.2)).mp hsafe)
  have hle := Finset.card_le_card hsubset
  have hbad :=
    weightedShiftedSplitPrimitiveCageUnsafeTraceSolutions_card_le_ninetySix
      p a alpha beta gamma orbitExponent
        h2 hA1 hA2 hA3 halpha
  have : primitive.card ≤ 96 := hle.trans hbad
  exact (Nat.not_le_of_lt (by simpa [primitive] using hcard)) this

/-- A primitive shifted-trace estimate with a ninety-six-point margin
produces a cage-ready primitive trace. -/
theorem
    exists_weightedShiftedSplitPrimitiveTracePair_cageReady_of_error_add_ninetySix_lt_main
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (a : Coefficients (ZMod p))
    (alpha beta gamma : ZMod p) (orbitExponent : ℕ)
    (h2 : (2 : ZMod p) ≠ 0)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hproductOne : alpha * beta ≠ 1)
    (hD2 : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0)
    (horbitPositive : 0 < orbitExponent)
    (horbitChar : (orbitExponent : ZMod p) ≠ 0)
    (horbitDvd : orbitExponent ∣ Nat.card (ZMod p)ˣ)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) +
          96 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p orbitExponent) :
    ∃ z : (powMonoidHom orbitExponent :
        (ZMod p)ˣ →* (ZMod p)ˣ).range × (ZMod p)ˣ,
      weightedShiftedSplitTorusTrace
          (ZMod p) alpha beta gamma z.1 =
          splitTorusTrace z.2 ∧
        orderOf z.2 = Nat.card (ZMod p)ˣ ∧
          CageReadyFirstAxisTrace a (splitTorusTrace z.2) := by
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
  have hcardReal : (96 : ℝ) < primitive.card := by
    have hmargin' : error + 96 < mainTerm := by
      simpa [error, mainTerm] using hmargin
    linarith
  have hcard : 96 < primitive.card := by
    exact_mod_cast hcardReal
  obtain ⟨z, hz, hcageReady⟩ :=
    exists_weightedShiftedSplitPrimitiveTracePair_cageReady_of_ninetySix_lt_card
      p a alpha beta gamma orbitExponent
        h2 hA1 hA2 hA3 halpha
        (by simpa [primitive] using hcard)
  have hz' :=
    (mem_traceExactOrderSolutions_iff
      (weightedShiftedSplitTorusTrace
        (ZMod p) alpha beta gamma)
      (splitTorusTrace : (ZMod p)ˣ → ZMod p)
      orbitExponent (Nat.card (ZMod p)ˣ) z).mp hz
  exact ⟨z, hz'.1, hz'.2, hcageReady⟩

end FiniteField

end

end GenMarkoff.General.Endgame
