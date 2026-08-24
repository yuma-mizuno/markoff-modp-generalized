import GenMarkoff.Symmetric.MiddleGame.ActualParameters
import GenMarkoff.Symmetric.MiddleGame.ShiftedCorvajaZannier

/-!
# Corvaja--Zannier for an actual symmetric fiber

This is the public middle-game specialization: candidate regularity supplies
the exact `sigma` and `D₂` hypotheses of the shifted coefficient-`48`
torsion-intersection theorem.
-/

namespace GenMarkoff.Symmetric.MiddleGame

open BGS.Markoff

noncomputable section

/-- The shifted trace equation attached to an actual candidate-regular
symmetric fiber satisfies the BGS coefficient-`48` subgroup bound. -/
theorem actualShiftedWeightedTraceEquationSolutions_card_cast_le_corvajaZannier
    (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] [Fintype E] [DecidableEq E] [CharP E p]
    (c u t : E) (htrace : t = trace c u) (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (H₁ H₂ : Subgroup Eˣ) (hpTwo : p ≠ 2) :
    ((shiftedWeightedTraceEquationSolutions 1 (actualSigma c u t)
        (actualGamma c u t) H₁ H₂).card : ℝ) ≤
      corvajaZannierTraceUpperBound p (Nat.card H₁) (Nat.card H₂) := by
  exact shiftedWeightedTraceEquationSolutions_card_cast_le_corvajaZannier
    p E (actualSigma c u t) (actualGamma c u t) H₁ H₂ hpTwo
      (actualSigma_ne_zero_of_candidateRegular c u t htrace hregular)
      (actualEvenObstruction_ne_zero_of_candidateRegular
        c u t htrace hc hregular)

end

end GenMarkoff.Symmetric.MiddleGame
