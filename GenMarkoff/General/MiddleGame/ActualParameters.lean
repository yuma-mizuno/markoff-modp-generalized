module

public import GenMarkoff.General.Trace.Parameters
public import GenMarkoff.ShiftedTrace.MiddleGame.ShiftedTraceEquation

@[expose] public section

/-!
# Regular actual parameters for a directed general fiber

Fix an ordered frame `(A,B,C)` and a fiber trace `t = orderedTrace s A u`.  On
the parametrized fiber, the trace of the first moving coordinate is a weighted
shifted torus trace with weights `actualAlpha s`, `actualBeta s B C u t`, weight
product `actualSigma s B C u t` and shift `actualGammaFirst s B C u t`; for
`t ^ 2 ≠ 4` these are the ordered candidates `orderedTraceSigma A B C t` and
`orderedTraceGamma A B C t`.  This file shows that
`OrderedTraceCandidateRegular A B C t` supplies the nonvanishing hypotheses of
the weighted shifted trace-curve count for these parameters: nonzero weights,
`actualSigma ≠ 1`, and a nonzero common-even obstruction.

The second moving coordinate (the frame `(A,C,B)`) is treated in
`GenMarkoff.General.MiddleGame.DirectedOrderGrowth`.
-/

namespace GenMarkoff.General.MiddleGame

open BGS.Markoff

noncomputable section

variable {K : Type*} [Field K]

/-- The first-directed leading weight `actualAlpha s` is nonzero when `s` is. -/
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

/-- Candidate regularity and `B ^ 2 ≠ 4` make the common-even obstruction
`shiftedTraceEvenObstruction` of the first-directed actual parameters
nonzero. -/
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

end

end GenMarkoff.General.MiddleGame
