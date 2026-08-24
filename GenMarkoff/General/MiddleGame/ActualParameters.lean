import GenMarkoff.General.TraceParameters
import GenMarkoff.Symmetric.MiddleGame.ShiftedTraceEquation

/-!
# Regular actual parameters for a directed general fiber

For a directed ordered frame `(A,B,C)`, candidate regularity supplies the
nonvanishing hypotheses required by the already-proved shifted trace-curve
kernels.  This file treats the first moving coordinate, whose affine shift is
`orderedTraceGamma A B C t`.  Reversing `B` and `C` gives the other directed
choice.
-/

namespace GenMarkoff.General.MiddleGame

open BGS.Markoff

noncomputable section

variable {K : Type*} [Field K]

theorem actualAlpha_ne_zero
    (s : K) (hs : s ≠ 0) :
    actualAlpha s ≠ 0 := by
  simpa [actualAlpha] using hs

/-- Candidate regularity identifies the actual normalized weight product and
makes it nonzero. -/
theorem actualSigma_ne_zero_of_candidateRegular
    (s A B C u t : K)
    (htrace : t = orderedTrace s A u)
    (hregular : OrderedTraceCandidateRegular A B C t) :
    actualSigma s B C u t ≠ 0 := by
  rw [actualSigma_eq_orderedTraceSigma s A B C u t htrace]
  exact hregular.sigma_ne_zero

/-- Candidate regularity excludes equal normalized weights. -/
theorem actualSigma_ne_one_of_candidateRegular
    (s A B C u t : K)
    (htrace : t = orderedTrace s A u)
    (hregular : OrderedTraceCandidateRegular A B C t) :
    actualSigma s B C u t ≠ 1 := by
  rw [actualSigma_eq_orderedTraceSigma s A B C u t htrace]
  exact hregular.sigma_ne_one

/-- Candidate regularity makes the reciprocal actual weight nonzero. -/
theorem actualBeta_ne_zero_of_candidateRegular
    (s A B C u t : K)
    (htrace : t = orderedTrace s A u)
    (hregular : OrderedTraceCandidateRegular A B C t) :
    actualBeta s B C u t ≠ 0 := by
  intro hbeta
  apply actualSigma_ne_zero_of_candidateRegular
    s A B C u t htrace hregular
  simp [actualSigma, hbeta]

/-- The first-directed actual parameters satisfy the common-even Kummer
condition. -/
theorem actualEvenObstruction_ne_zero_of_candidateRegular
    (s A B C u t : K)
    (htrace : t = orderedTrace s A u) (hB : B ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular A B C t) :
    shiftedTraceEvenObstruction (actualSigma s B C u t)
        (actualGammaFirst s B C u t) ≠ 0 := by
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  rw [actualSigma_eq_orderedTraceSigma s A B C u t htrace,
    actualGammaFirst_eq_orderedTraceGamma
      s A B C u t hD htrace]
  exact hregular.evenObstruction_ne_zero hB

/-- Candidate regularity supplies all strong regular shifted-cover
hypotheses for the first directed trace. -/
theorem actual_shiftedCover_parameters_regular
    (s A B C u t : K)
    (htrace : t = orderedTrace s A u)
    (hs : s ≠ 0) (hB : B ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular A B C t) :
    actualAlpha s ≠ 0 ∧ actualBeta s B C u t ≠ 0 ∧
      actualSigma s B C u t ≠ 0 ∧
      actualSigma s B C u t ≠ 1 ∧
      shiftedTraceEvenObstruction (actualSigma s B C u t)
        (actualGammaFirst s B C u t) ≠ 0 := by
  exact ⟨actualAlpha_ne_zero s hs,
    actualBeta_ne_zero_of_candidateRegular
      s A B C u t htrace hregular,
    actualSigma_ne_zero_of_candidateRegular
      s A B C u t htrace hregular,
    actualSigma_ne_one_of_candidateRegular
      s A B C u t htrace hregular,
    actualEvenObstruction_ne_zero_of_candidateRegular
      s A B C u t htrace hB hregular⟩

/-- Exact normalization of the first directed trace formula. -/
theorem firstTrace_fiberPair_normalized
    (s B C u t q h : K) (hs : s ≠ 0) (hh : h ≠ 0) :
    s * (fiberPair B C u t q h).1 - B =
      actualAlpha s * h +
        actualSigma s B C u t / (actualAlpha s * h) +
          actualGammaFirst s B C u t := by
  rw [firstTrace_fiberPair s B C u t q h hh]
  simp only [actualSigma]
  field_simp [actualAlpha_ne_zero s hs, hh]

/-- Unit used to normalize the leading first-directed weight to one. -/
def actualAlphaUnit (s : K) (hs : s ≠ 0) : Kˣ :=
  Units.mk0 (actualAlpha s) (actualAlpha_ne_zero s hs)

@[simp]
theorem actualAlphaUnit_val (s : K) (hs : s ≠ 0) :
    (actualAlphaUnit s hs : K) = actualAlpha s :=
  rfl

/-- The normalized shifted weighted trace is the actual first adjacent
coordinate trace. -/
theorem shiftedWeightedTrace_normalizedParameter_eq_firstTrace_fiberPair
    (s B C u t q : K) (h : Kˣ) (hs : s ≠ 0) :
    weightedSplitTorusTrace 1 (actualSigma s B C u t)
          (actualAlphaUnit s hs * h) +
        actualGammaFirst s B C u t =
      s * (fiberPair B C u t q h).1 - B := by
  rw [firstTrace_fiberPair_normalized
    s B C u t q h hs (Units.ne_zero h)]
  simp only [weightedSplitTorusTrace, actualAlphaUnit_val,
    Units.val_mul, Units.val_inv_eq_inv_val, one_mul]
  field_simp [actualAlpha_ne_zero s hs, Units.ne_zero h]

end

end GenMarkoff.General.MiddleGame
