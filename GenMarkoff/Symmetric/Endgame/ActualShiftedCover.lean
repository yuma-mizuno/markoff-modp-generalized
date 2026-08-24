import GenMarkoff.Symmetric.MiddleGame.ActualParameters
import GenMarkoff.TraceCurve.ShiftedCoverResidueBlocks
import GenMarkoff.TraceCurve.ShiftedCoverWeil

/-!
# The shifted cover attached to an actual symmetric fiber

This module specializes the degree-one shifted-cover geometry to the exact
parameters obtained from a candidate-regular one-step fiber.
-/

namespace GenMarkoff.Symmetric.Endgame

open GenMarkoff

noncomputable section

variable {K : Type*} [Field K]

/-- Candidate regularity makes the actual degree-one shifted cover absolutely
irreducible.  This is the base-curve input for both the shifted middle game and
the arbitrary-power end-game tower. -/
theorem actualDegreeOneShiftedCover_absolutelyIrreducible
    (c u t : K) (htrace : t = trace c u)
    (h2 : (2 : K) ≠ 0) (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (shiftedTraceCoverPolynomial 1 (actualSigma c u t)
          (actualGamma c u t) 1 1)) := by
  exact shiftedTraceDegreeOneCoverPolynomial_absolutelyIrreducible
    (actualSigma c u t) (actualGamma c u t) h2
    (MiddleGame.actualSigma_ne_zero_of_candidateRegular
      c u t htrace hregular)
    (MiddleGame.actualEvenObstruction_ne_zero_of_candidateRegular
      c u t htrace hc hregular)

/-- Candidate regularity makes every positive actual shifted power cover
absolutely irreducible.  No parity or coprimality assumption on the two
covering exponents is required. -/
theorem actualShiftedCover_absolutelyIrreducible_of_positiveExponents
    (c u t : K) (htrace : t = trace c u)
    (h2 : (2 : K) ≠ 0) (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e) (heChar : (e : K) ≠ 0) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (shiftedTraceCoverPolynomial 1 (actualSigma c u t)
          (actualGamma c u t) d e)) := by
  exact shiftedTraceCoverPolynomial_absolutelyIrreducible_of_positiveExponents
    (actualSigma c u t) (actualGamma c u t) h2
    (MiddleGame.actualSigma_ne_zero_of_candidateRegular
      c u t htrace hregular)
    (MiddleGame.actualSigma_ne_one_of_candidateRegular
      c u t htrace hregular)
    (MiddleGame.actualEvenObstruction_ne_zero_of_candidateRegular
      c u t htrace hc hregular)
    e d he heChar hd

/-- The uniform shifted Hasse--Weil estimate specialized to an actual
candidate-regular symmetric fiber. -/
theorem actualShiftedTraceCurveSolutions_count_error_le
    (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (coefficient : ℕ) (hWeil : ShiftedTraceWeilBoundAssumption coefficient)
    (c u t : F) (htrace : t = trace c u)
    (h2 : (2 : F) ≠ 0) (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e) (heChar : (e : F) ≠ 0) :
    |((shiftedTraceCurveSolutions F (actualSigma c u t)
          (actualGamma c u t) d e).card : ℝ) -
        (Fintype.card F : ℝ)| ≤
      (coefficient : ℝ) * Real.sqrt (Fintype.card F : ℝ) *
        (d : ℝ) * (e : ℝ) := by
  apply shiftedTraceCurveSolutions_count_error_le_of_weilBoundAssumption
    coefficient hWeil F (actualSigma c u t) (actualGamma c u t) d e
      (MiddleGame.actualSigma_ne_zero_of_candidateRegular
        c u t htrace hregular) hd he
  exact actualShiftedCover_absolutelyIrreducible_of_positiveExponents
    c u t htrace h2 hc hregular d e hd he heChar

end

end GenMarkoff.Symmetric.Endgame
