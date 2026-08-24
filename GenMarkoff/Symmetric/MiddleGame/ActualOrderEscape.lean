import GenMarkoff.Symmetric.MiddleGame.ActualCorvajaZannier
import BGS.Markoff.MiddleGame.CorvajaZannierStep
import BGS.Markoff.MiddleGame.RightSubgroups

/-!
# Shifted middle-game order escape for an actual symmetric fiber

This module adapts the finite-union part of the pinned BGS middle game to the
shifted equation

`h + sigma * h⁻¹ + gamma = k + k⁻¹`.

The coefficient-`48` estimate is supplied by
`actualShiftedWeightedTraceEquationSolutions_card_cast_le_corvajaZannier`;
it is not an additional theorem hypothesis in the final actual-fiber
statements.  The conclusion is deliberately kept at the subgroup/trace
level.  It does not yet assert that the escaping parameter occurs in the
one-step orbit of a chosen point, nor that a neighboring rotation order has
increased.
-/

namespace GenMarkoff.Symmetric.MiddleGame

open BGS.Markoff

noncomputable section

variable {E : Type} [Field E] [Fintype E]

/-- A real-valued bound for each shifted solution set sums over an arbitrary
finite family of candidate right orders. -/
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

/-- The shifted coefficient-`48` estimates, exact right-subgroup cardinalities,
and the common BGS envelope inequality give a parameter avoiding every
candidate right order. -/
theorem exists_left_element_escaping_shiftedCandidateOrders_of_corvajaZannierEstimate
    (p : ℕ) (alpha beta gamma : E) (H1 : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ)
    (hrightOrder : ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      Nat.card (rightSubgroup d) = d)
    (hCZ : ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      ((shiftedWeightedTraceEquationSolutions alpha beta gamma H1
        (rightSubgroup d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (Nat.card H1)
            (Nat.card (rightSubgroup d)))
    (hsmall :
      (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
          corvajaZannierCurrentOrderEnvelope p (Nat.card H1) <
        (Nat.card H1 : ℝ)) :
    ∃ h1 : H1, ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      ∀ h2 : rightSubgroup d,
        weightedSplitTorusTrace alpha beta h1 + gamma ≠
          splitTorusTrace h2 := by
  classical
  let orders := middleGameCandidateOrders p (Nat.card H1)
  let bad := shiftedWeightedBadOrderTraceSupport
    alpha beta gamma H1 orders rightSubgroup
  have hCZIndexed : ∀ d ∈ orders,
      ((shiftedWeightedTraceEquationSolutions alpha beta gamma H1
        (rightSubgroup d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (Nat.card H1) d := by
    intro d hd
    have hd' : d ∈ middleGameCandidateOrders p (Nat.card H1) := by
      simpa [orders] using hd
    have hEstimate := hCZ d hd'
    rw [hrightOrder d hd'] at hEstimate
    exact hEstimate
  have hbadReal : (bad.card : ℝ) < (Nat.card H1 : ℝ) := by
    calc
      (bad.card : ℝ) ≤
          ∑ d ∈ orders,
            corvajaZannierTraceUpperBound p (Nat.card H1) d := by
        exact shiftedWeightedBadOrderTraceSupport_card_cast_le_sum
          alpha beta gamma H1 orders rightSubgroup _ hCZIndexed
      _ ≤ (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
          corvajaZannierCurrentOrderEnvelope p (Nat.card H1) := by
        simpa [orders] using
          middleGameCorvajaZannierSum_le_divisorCount_mul_envelope
            p (Nat.card H1)
      _ < (Nat.card H1 : ℝ) := hsmall
  have hbad : bad.card < Nat.card H1 := by
    exact_mod_cast hbadReal
  have hexists : ∃ h1 : H1, h1 ∉ bad := by
    by_contra hall
    push Not at hall
    have hle : (Finset.univ : Finset H1).card ≤ bad.card :=
      Finset.card_le_card fun h1 _ ↦ hall h1
    rw [Finset.card_univ, Fintype.card_eq_nat_card] at hle
    exact (Nat.not_le_of_lt hbad) hle
  obtain ⟨h1, hh1⟩ := hexists
  refine ⟨h1, ?_⟩
  intro d hd h2 heq
  apply hh1
  exact mem_shiftedWeightedBadOrderTraceSupport_iff.mpr
    ⟨d, by simpa [orders] using hd, h2, heq⟩

/-- Natural-number cube and linear inequalities imply the strict shifted
bad-union inequality and hence the subgroup-level escape conclusion. -/
theorem exists_left_element_escaping_shiftedCandidateOrders_of_corvajaZannierSizeBounds
    (p : ℕ) (alpha beta gamma : E) (H1 : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ)
    (hrightOrder : ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      Nat.card (rightSubgroup d) = d)
    (hCZ : ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      ((shiftedWeightedTraceEquationSolutions alpha beta gamma H1
        (rightSubgroup d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (Nat.card H1)
            (Nat.card (rightSubgroup d)))
    (hcurrentOrder : 0 < Nat.card H1)
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 < Nat.card H1)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) * Nat.card H1 < p) :
    ∃ h1 : H1, ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      ∀ h2 : rightSubgroup d,
        weightedSplitTorusTrace alpha beta h1 + gamma ≠
          splitTorusTrace h2 := by
  exact
    exists_left_element_escaping_shiftedCandidateOrders_of_corvajaZannierEstimate
      p alpha beta gamma H1 rightSubgroup hrightOrder hCZ
        (divisorCount_mul_corvajaZannierEnvelope_lt_currentOrder
          p (Nat.card H1) hcurrentOrder hcube hlinear)

section ActualFiber

variable [DecidableEq E]

/-- Public actual-fiber subgroup escape theorem.  Candidate regularity proves
the shifted curve hypotheses, so the coefficient-`48` Corvaja--Zannier bound
is discharged internally.  The remaining assumptions are precisely the
right-subgroup cardinalities and the two finite BGS size inequalities. -/
theorem exists_actualFiber_left_element_escaping_middleGameCandidateOrders
    (p : ℕ) [Fact p.Prime] [CharP E p]
    (c u t : E) (htrace : t = trace c u) (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (H1 : Subgroup Eˣ) (rightSubgroup : ℕ → Subgroup Eˣ)
    (hpTwo : p ≠ 2)
    (hrightOrder : ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      Nat.card (rightSubgroup d) = d)
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 < Nat.card H1)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) * Nat.card H1 < p) :
    ∃ h1 : H1, ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      ∀ h2 : rightSubgroup d,
        weightedSplitTorusTrace 1 (actualSigma c u t) h1 +
            actualGamma c u t ≠ splitTorusTrace h2 := by
  have hCZ : ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      ((shiftedWeightedTraceEquationSolutions 1 (actualSigma c u t)
        (actualGamma c u t) H1 (rightSubgroup d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (Nat.card H1)
            (Nat.card (rightSubgroup d)) := by
    intro d _hd
    exact actualShiftedWeightedTraceEquationSolutions_card_cast_le_corvajaZannier
      p E c u t htrace hc hregular H1 (rightSubgroup d) hpTwo
  exact
    exists_left_element_escaping_shiftedCandidateOrders_of_corvajaZannierSizeBounds
      (E := E) p 1 (actualSigma c u t) (actualGamma c u t) H1
        rightSubgroup hrightOrder hCZ Nat.card_pos hcube hlinear

end ActualFiber

/-- Canonical quadratic-extension version of the actual-fiber escape theorem.
For every candidate order, the right subgroup is the BGS roots-of-unity
subgroup and its exact cardinality is proved internally. -/
theorem exists_actualFiber_left_element_escaping_canonicalRightSubgroups
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (c u t : quadraticFiniteField p) (htrace : t = trace c u)
    (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (H1 : Subgroup (quadraticFiniteField p)ˣ) (hpTwo : p ≠ 2)
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 < Nat.card H1)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) * Nat.card H1 < p) :
    ∃ h1 : H1, ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      ∀ h2 : middleGameRightSubgroup p d,
        weightedSplitTorusTrace 1 (actualSigma c u t) h1 +
            actualGamma c u t ≠ splitTorusTrace h2 := by
  letI : DecidableEq (quadraticFiniteField p) := Classical.decEq _
  let rightSubgroup : ℕ → Subgroup (quadraticFiniteField p)ˣ :=
    fun d ↦ middleGameRightSubgroup p d
  have hrightOrder : ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      Nat.card (rightSubgroup d) = d := by
    intro d hd
    exact middleGameRightSubgroup_natCard p (Nat.card H1) d hd
  exact
    exists_actualFiber_left_element_escaping_middleGameCandidateOrders
      (E := quadraticFiniteField p) p c u t htrace hc hregular H1
        rightSubgroup hpTwo hrightOrder hcube hlinear

end

end GenMarkoff.Symmetric.MiddleGame
