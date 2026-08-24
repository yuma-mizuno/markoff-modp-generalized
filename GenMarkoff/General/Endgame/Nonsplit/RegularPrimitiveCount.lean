import GenMarkoff.Symmetric.Endgame.Nonsplit.ShiftedPrimitiveCount
import GenMarkoff.TraceCurve.ExceptionalRouting

/-!
# Candidate-regular primitive traces on descended nonsplit covers

The descended nonsplit primitive count and its four-lift trace-fiber bound
do not use equality of the Markoff coefficients.  This file reuses those
two explicit counting boundaries and filters their common ordinary trace
with `orderedTraceSafePolynomial A B C`.

## New consideration in the unequal-coefficient case

The symmetric safe polynomial has degree seven, hence removes at most
`4 * 7 = 28` primitive pairs.  For a fixed ordered frame `(A, B, C)`, the
general safe polynomial retains all six ordered obstruction factors and has
degree at most ten.  The descended nonsplit filter therefore needs the
strictly larger correction `4 * 10 = 40`.

Nonvanishing of this ordered polynomial uses exactly `A ^ 2 ≠ 4` and
`B ^ 2 ≠ 4` in their displayed roles.  No hypothesis on `C` is introduced
by this counting step, and no coordinate permutation is used.  The endpoint
below produces a primitive candidate-regular trace only; it makes no claim
that an actual rotation reaches the corresponding pair.
-/

namespace GenMarkoff.General.Endgame.Nonsplit

open BGS.Markoff Polynomial
open GenMarkoff.Symmetric.Endgame.Nonsplit

noncomputable section

/-- Descended nonsplit primitive pairs whose common ordinary trace
annihilates the safe polynomial for the ordered frame `(A, B, C)`. -/
noncomputable abbrev shiftedSeededNonsplitPrimitiveUnsafeTraceSolutions
    (p : ℕ) [Fact p.Prime]
    (A B C : ZMod p) (k : (ZMod p)ˣ)
    (s : ↥(quadraticNormFiber p k)) (gamma : ZMod p)
    (orbitExponent : ℕ) :=
  (GenMarkoff.Symmetric.Endgame.Nonsplit.shiftedSeededNonsplitPrimitiveTraceSolutions
    p k s gamma orbitExponent).filter fun z ↦
      eval (splitTorusTrace z.2) (orderedTraceSafePolynomial A B C) = 0

/-- At most forty descended nonsplit primitive pairs have a
candidate-irregular common trace for the ordered frame `(A, B, C)`. -/
theorem shiftedSeededNonsplitPrimitiveUnsafeTraceSolutions_card_le_forty
    (p : ℕ) [Fact p.Prime]
    (A B C : ZMod p) (k : (ZMod p)ˣ)
    (s : ↥(quadraticNormFiber p k)) (gamma : ZMod p)
    (orbitExponent : ℕ)
    (h2 : (2 : ZMod p) ≠ 0)
    (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4) :
    (shiftedSeededNonsplitPrimitiveUnsafeTraceSolutions
      p A B C k s gamma orbitExponent).card ≤ 40 := by
  classical
  let primitive :=
    GenMarkoff.Symmetric.Endgame.Nonsplit.shiftedSeededNonsplitPrimitiveTraceSolutions
      p k s gamma orbitExponent
  let traceValue :
      (powMonoidHom orbitExponent :
        quadraticNormOneTorus p →* quadraticNormOneTorus p).range ×
          (ZMod p)ˣ → ZMod p :=
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
          GenMarkoff.Symmetric.Endgame.Nonsplit.shiftedSeededNonsplitPrimitiveTraceSolutions_traceFiber_card_le_four
            p k s gamma orbitExponent t
  have hp : orderedTraceSafePolynomial A B C ≠ 0 :=
    orderedTraceSafePolynomial_ne_zero A B C h2 hA hB
  have himage :
      bad.image traceValue ⊆
        (orderedTraceSafePolynomial A B C).roots.toFinset := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨z, hz, rfl⟩
    have hzero :
        eval (traceValue z) (orderedTraceSafePolynomial A B C) = 0 :=
      (Finset.mem_filter.mp hz).2
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

/-- A descended nonsplit primitive-count estimate with a forty-point margin
produces a primitive common trace that is candidate-regular for the ordered
frame `(A, B, C)`.

This is a counting endpoint: the norm-one parameter is constrained only by
membership in the specified power-map range. -/
theorem exists_shiftedSeededNonsplitPrimitiveTracePair_candidateRegular_of_error_add_forty_lt_main
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil :
      GenMarkoff.Symmetric.Endgame.Nonsplit.ShiftedSeededNonsplitTraceWeilBoundAssumption
        coefficient)
    (hpTwo : p ≠ 2)
    (A B C : ZMod p)
    (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4)
    (k : (ZMod p)ˣ) (hk : k ≠ 1)
    (s : ↥(quadraticNormFiber p k)) (gamma : ZMod p)
    (hD2 : shiftedTraceEvenObstruction (k : ZMod p) gamma ≠ 0)
    (orbitExponent : ℕ)
    (horbitPositive : 0 < orbitExponent)
    (horbitChar : (orbitExponent : quadraticFiniteField p) ≠ 0)
    (horbitDvd :
      orbitExponent ∣ Nat.card (quadraticNormOneTorus p))
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) + 40 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p orbitExponent) :
    ∃ z : (powMonoidHom orbitExponent :
        quadraticNormOneTorus p →* quadraticNormOneTorus p).range ×
          (ZMod p)ˣ,
      GenMarkoff.Symmetric.Endgame.Nonsplit.shiftedSeededNonsplitTorusTrace
          p k s gamma z.1 =
          splitTorusTrace z.2 ∧
        orderOf z.2 = Nat.card (ZMod p)ˣ ∧
          OrderedTraceCandidateRegular A B C
            (splitTorusTrace z.2) := by
  let primitive :=
    GenMarkoff.Symmetric.Endgame.Nonsplit.shiftedSeededNonsplitPrimitiveTraceSolutions
      p k s gamma orbitExponent
  let mainTerm :=
    primitiveTraceMoebiusMainTerm
      (Nat.card (ZMod p)ˣ) p orbitExponent
  let error :=
    ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
      ((coefficient : ℝ) * Real.sqrt (p : ℝ))
  have henvelope :
      |(primitive.card : ℝ) - mainTerm| ≤ error := by
    simpa [primitive, mainTerm, error] using
      GenMarkoff.Symmetric.Endgame.Nonsplit.shiftedSeededNonsplitPrimitiveTraceSolutions_card_error_le
        p coefficient hWeil hpTwo k hk s gamma hD2
        orbitExponent horbitPositive horbitChar horbitDvd
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
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
    exact hpTwo
      (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)
  have hbad :=
    shiftedSeededNonsplitPrimitiveUnsafeTraceSolutions_card_le_forty
      p A B C k s gamma orbitExponent h2 hA hB
  have hexists :
      ∃ z ∈ primitive,
        OrderedTraceCandidateRegular A B C
          (splitTorusTrace z.2) := by
    by_contra hnone
    push Not at hnone
    have hsubset :
        primitive ⊆
          shiftedSeededNonsplitPrimitiveUnsafeTraceSolutions
            p A B C k s gamma orbitExponent := by
      intro z hz
      rw [Finset.mem_filter]
      refine ⟨hz, ?_⟩
      by_contra hsafe
      exact hnone z hz
        ((orderedTraceSafePolynomial_eval_ne_zero_iff
          A B C (splitTorusTrace z.2)).mp hsafe)
    have hle := Finset.card_le_card hsubset
    have : primitive.card ≤ 40 := hle.trans hbad
    exact (Nat.not_le_of_lt hcard) this
  obtain ⟨z, hz, hregular⟩ := hexists
  have hz' :=
    (mem_traceExactOrderSolutions_iff
      (GenMarkoff.Symmetric.Endgame.Nonsplit.shiftedSeededNonsplitTorusTrace
        p k s gamma)
      (splitTorusTrace : (ZMod p)ˣ → ZMod p)
      orbitExponent (Nat.card (ZMod p)ˣ) z).mp hz
  exact ⟨z, hz'.1, hz'.2, hregular⟩

end

end GenMarkoff.General.Endgame.Nonsplit
