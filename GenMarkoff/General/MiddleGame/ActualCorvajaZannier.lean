import GenMarkoff.General.MiddleGame.ActualParameters
import GenMarkoff.Symmetric.MiddleGame.ShiftedCorvajaZannier

/-!
# Corvaja--Zannier for a directed general fiber

This is the coefficient-sensitive specialization of the already-proved
shifted trace-curve estimate.  The ordered frame `(A,B,C)` records the fixed,
target, and remaining coefficients.  Reversing `B` and `C` supplies the other
directed adjacent trace; no coordinate permutation of the fixed surface is
used here.
-/

namespace GenMarkoff.General.MiddleGame

open BGS.Markoff
open GenMarkoff.Symmetric.MiddleGame

noncomputable section

/-- The shifted trace equation attached to a candidate-regular directed
general fiber satisfies the BGS coefficient-`48` subgroup bound. -/
theorem actualShiftedWeightedTraceEquationSolutions_card_cast_le_corvajaZannier
    (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] [Fintype E] [DecidableEq E] [CharP E p]
    (s A B C u t : E)
    (htrace : t = orderedTrace s A u)
    (hB : B ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular A B C t)
    (H₁ H₂ : Subgroup Eˣ) (hpTwo : p ≠ 2) :
    ((shiftedWeightedTraceEquationSolutions 1
        (actualSigma s B C u t) (actualGammaFirst s B C u t)
        H₁ H₂).card : ℝ) ≤
      corvajaZannierTraceUpperBound p (Nat.card H₁) (Nat.card H₂) := by
  exact
    shiftedWeightedTraceEquationSolutions_card_cast_le_corvajaZannier
      p E (actualSigma s B C u t) (actualGammaFirst s B C u t)
        H₁ H₂ hpTwo
        (actualSigma_ne_zero_of_candidateRegular
          s A B C u t htrace hregular)
        (actualEvenObstruction_ne_zero_of_candidateRegular
          s A B C u t htrace hB hregular)

end

end GenMarkoff.General.MiddleGame
