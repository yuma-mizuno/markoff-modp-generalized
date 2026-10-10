import GenMarkoff.ShiftedTrace.MiddleGame.ShiftedTraceEquation
import GenMarkoff.Core.Statements
import GenMarkoff.TraceCurve.ExceptionalRouting
import GenMarkoff.ShiftedTrace.MiddleGame.ShiftedCorvajaZannier
import BGS.Markoff.MiddleGame.CorvajaZannierStep
import BGS.Markoff.MiddleGame.RightSubgroups

/-!
# Union bound for the shifted trace equation over several right orders

This file adapts the finite-union step of the BGS middle game
(`BGS.Markoff.badOrderTraceSupport_card_cast_le_sum`) to the shifted equation

`alpha * h + beta * h⁻¹ + gamma = k + k⁻¹`.

The left elements meeting some member of a finite family of right subgroups
are bounded by the sum of per-order bounds on the solution sets.  The general
middle game (`GenMarkoff.General.Assembly.RegularMiddleIteration`) combines
this with the Corvaja--Zannier bound
`weightedShiftedTraceEquationSolutions_card_cast_le_corvajaZannier`.
-/

namespace GenMarkoff.ShiftedTrace.MiddleGame

open BGS.Markoff

noncomputable section

variable {E : Type} [Field E] [Fintype E]

/-- If each shifted solution set for the right subgroup `rightSubgroup d`,
`d ∈ orders`, has at most `bound d` elements, then at most `∑ d ∈ orders, bound d`
left elements meet some right subgroup of the family. -/
theorem shiftedWeightedBadOrderTraceSupport_card_cast_le_sum
    (alpha beta gamma : E) (H1 : Subgroup Eˣ) (orders : Finset ℕ)
    (rightSubgroup : ℕ → Subgroup Eˣ) (bound : ℕ → ℝ)
    (hbound : ∀ d ∈ orders,
      ((shiftedWeightedTraceEquationSolutions alpha beta gamma H1
        (rightSubgroup d)).card : ℝ) ≤ bound d) :
    ((shiftedWeightedBadOrderTraceSupport alpha beta gamma H1 orders
      rightSubgroup).card : ℝ) ≤ ∑ d ∈ orders, bound d := by
  classical
  calc
    ((shiftedWeightedBadOrderTraceSupport alpha beta gamma H1 orders
        rightSubgroup).card : ℝ) ≤
        ∑ d ∈ orders,
          ((shiftedWeightedTraceEquationLeftSupport alpha beta gamma H1
            (rightSubgroup d)).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le :
        (shiftedWeightedBadOrderTraceSupport alpha beta gamma H1 orders
          rightSubgroup).card ≤
          ∑ d ∈ orders,
            (shiftedWeightedTraceEquationLeftSupport alpha beta gamma H1
              (rightSubgroup d)).card)
    _ ≤ ∑ d ∈ orders,
        ((shiftedWeightedTraceEquationSolutions alpha beta gamma H1
          (rightSubgroup d)).card : ℝ) := by
      exact Finset.sum_le_sum fun d _ ↦ by
        exact_mod_cast
          shiftedWeightedTraceEquationLeftSupport_card_le_solutions
            alpha beta gamma H1 (rightSubgroup d)
    _ ≤ ∑ d ∈ orders, bound d := Finset.sum_le_sum hbound

end

end GenMarkoff.ShiftedTrace.MiddleGame
