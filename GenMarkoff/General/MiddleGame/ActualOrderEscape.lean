import GenMarkoff.General.MiddleGame.ActualCorvajaZannier
import GenMarkoff.Symmetric.MiddleGame.ActualOrderEscape

/-!
# Shifted middle-game order escape for a directed general fiber

The finite-union argument is coefficient-independent once the ordered actual
parameters have been identified.  This file specializes that argument to the
first target coordinate of an ordered frame `(A,B,C)`.  Replacing the frame by
`(A,C,B)` gives the reverse target direction.
-/

namespace GenMarkoff.General.MiddleGame

open BGS.Markoff
open GenMarkoff.Symmetric.MiddleGame

noncomputable section

variable {E : Type} [Field E] [Fintype E]

/-- Candidate regularity discharges the shifted Corvaja--Zannier hypotheses
for a directed general fiber.  The remaining inputs are the exact candidate
right-subgroup orders and the two standard BGS size inequalities. -/
theorem exists_actualFiber_left_element_escaping_middleGameCandidateOrders
    (p : ℕ) [Fact p.Prime] [DecidableEq E] [CharP E p]
    (s A B C u t : E)
    (htrace : t = orderedTrace s A u)
    (hB : B ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular A B C t)
    (H1 : Subgroup Eˣ) (rightSubgroup : ℕ → Subgroup Eˣ)
    (hpTwo : p ≠ 2)
    (hrightOrder : ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      Nat.card (rightSubgroup d) = d)
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 <
        Nat.card H1)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) *
          Nat.card H1 < p) :
    ∃ h1 : H1, ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      ∀ h2 : rightSubgroup d,
        weightedSplitTorusTrace 1 (actualSigma s B C u t) h1 +
            actualGammaFirst s B C u t ≠ splitTorusTrace h2 := by
  have hCZ : ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      ((shiftedWeightedTraceEquationSolutions 1
        (actualSigma s B C u t) (actualGammaFirst s B C u t)
        H1 (rightSubgroup d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (Nat.card H1)
            (Nat.card (rightSubgroup d)) := by
    intro d _hd
    exact
      actualShiftedWeightedTraceEquationSolutions_card_cast_le_corvajaZannier
        p E s A B C u t htrace hB hregular
          H1 (rightSubgroup d) hpTwo
  exact
    exists_left_element_escaping_shiftedCandidateOrders_of_corvajaZannierSizeBounds
      (E := E) p 1 (actualSigma s B C u t)
        (actualGammaFirst s B C u t) H1 rightSubgroup
        hrightOrder hCZ Nat.card_pos hcube hlinear

/-- Canonical quadratic-extension form, with the BGS roots-of-unity subgroup
of each candidate order chosen internally. -/
theorem exists_actualFiber_left_element_escaping_canonicalRightSubgroups
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (s A B C u t : quadraticFiniteField p)
    (htrace : t = orderedTrace s A u)
    (hB : B ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular A B C t)
    (H1 : Subgroup (quadraticFiniteField p)ˣ)
    (hpTwo : p ≠ 2)
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 <
        Nat.card H1)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) *
          Nat.card H1 < p) :
    ∃ h1 : H1, ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      ∀ h2 : middleGameRightSubgroup p d,
        weightedSplitTorusTrace 1 (actualSigma s B C u t) h1 +
            actualGammaFirst s B C u t ≠ splitTorusTrace h2 := by
  letI : DecidableEq (quadraticFiniteField p) := Classical.decEq _
  let rightSubgroup : ℕ → Subgroup (quadraticFiniteField p)ˣ :=
    fun d => middleGameRightSubgroup p d
  have hrightOrder : ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      Nat.card (rightSubgroup d) = d := by
    intro d hd
    exact middleGameRightSubgroup_natCard p (Nat.card H1) d hd
  exact
    exists_actualFiber_left_element_escaping_middleGameCandidateOrders
      (E := quadraticFiniteField p) p s A B C u t
        htrace hB hregular H1 rightSubgroup hpTwo hrightOrder hcube hlinear

end

end GenMarkoff.General.MiddleGame
