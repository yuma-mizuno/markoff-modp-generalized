import GenMarkoff.Symmetric.ExceptionalRouting
import GenMarkoff.Symmetric.MiddleGame.ActualOrderEscape

/-!
# Preserving candidate regularity in a middle-game escape

Strict order growth is not by itself iterable in the generalized symmetric
surface: the new fixed trace must again satisfy the candidate-regularity
hypotheses of the shifted curve.  There are at most seven bad trace values,
and every shifted weighted trace value has at most two lifts in the current
cyclic subgroup.  Thus fourteen extra exclusions suffice.
-/

namespace GenMarkoff.Symmetric.MiddleGame

open BGS.Markoff Polynomial

noncomputable section

variable {E : Type} [Field E] [Fintype E]

/-- Current subgroup parameters whose adjacent trace kills the reduced
symmetric safe polynomial. -/
def shiftedWeightedUnsafeTraceSupport
    (c alpha beta gamma : E) (H1 : Subgroup Eˣ) : Finset H1 := by
  classical
  exact Finset.univ.filter fun h ↦
    eval (weightedSplitTorusTrace alpha beta h + gamma)
      (safePolynomial c) = 0

@[simp]
theorem mem_shiftedWeightedUnsafeTraceSupport_iff
    {c alpha beta gamma : E} {H1 : Subgroup Eˣ} {h : H1} :
    h ∈ shiftedWeightedUnsafeTraceSupport c alpha beta gamma H1 ↔
      eval (weightedSplitTorusTrace alpha beta h + gamma)
        (safePolynomial c) = 0 := by
  classical
  simp [shiftedWeightedUnsafeTraceSupport]

/-- At most fourteen elements of a subgroup have a candidate-irregular
shifted weighted trace. -/
theorem shiftedWeightedUnsafeTraceSupport_card_le_fourteen
    (c alpha beta gamma : E) (H1 : Subgroup Eˣ)
    (h2 : (2 : E) ≠ 0) (hc : c ^ 2 ≠ 4) (halpha : alpha ≠ 0) :
    (shiftedWeightedUnsafeTraceSupport
      c alpha beta gamma H1).card ≤ 14 := by
  classical
  let traceValue : H1 → E :=
    fun h ↦ weightedSplitTorusTrace alpha beta h + gamma
  have hfiber :
      ∀ target,
        ((Finset.univ : Finset H1).filter
          fun h ↦ traceValue h = target).card ≤ 2 := by
    intro target
    simpa [traceValue, shiftedWeightedTraceValueFiber] using
      shiftedWeightedTraceValueFiber_card_le_two
        alpha beta gamma H1 target halpha
  simpa [shiftedWeightedUnsafeTraceSupport, traceValue] using
    card_safePolynomial_zero_le_fourteen
      c (Finset.univ : Finset H1) traceValue h2 hc hfiber

/-- Avoid both every designated low-order trace subgroup and the fourteen
candidate-irregular parameters. -/
theorem exists_left_element_escaping_shiftedCandidateOrders_and_regular
    (c alpha beta gamma : E) (H1 : Subgroup Eˣ)
    (orders : Finset ℕ) (rightSubgroup : ℕ → Subgroup Eˣ)
    (h2 : (2 : E) ≠ 0) (hc : c ^ 2 ≠ 4) (halpha : alpha ≠ 0)
    (hsmall :
      (shiftedWeightedBadOrderTraceSupport
          alpha beta gamma H1 orders rightSubgroup).card +
        14 < Nat.card H1) :
    ∃ h1 : H1,
      OrderedTraceCandidateRegular c c c
          (weightedSplitTorusTrace alpha beta h1 + gamma) ∧
        ∀ d ∈ orders, ∀ h2 : rightSubgroup d,
          weightedSplitTorusTrace alpha beta h1 + gamma ≠
            splitTorusTrace h2 := by
  classical
  let bad :=
    shiftedWeightedBadOrderTraceSupport
      alpha beta gamma H1 orders rightSubgroup
  let unsafeSet :=
    shiftedWeightedUnsafeTraceSupport c alpha beta gamma H1
  have hunsafe : unsafeSet.card ≤ 14 := by
    simpa [unsafeSet] using
      shiftedWeightedUnsafeTraceSupport_card_le_fourteen
        c alpha beta gamma H1 h2 hc halpha
  have hunion :
      (bad ∪ unsafeSet).card < Nat.card H1 := by
    calc
      (bad ∪ unsafeSet).card ≤ bad.card + unsafeSet.card :=
        Finset.card_union_le _ _
      _ ≤ bad.card + 14 := Nat.add_le_add_left hunsafe _
      _ < Nat.card H1 := by simpa [bad] using hsmall
  have hexists : ∃ h1 : H1, h1 ∉ bad ∪ unsafeSet := by
    by_contra hall
    push Not at hall
    have hle : (Finset.univ : Finset H1).card ≤ (bad ∪ unsafeSet).card :=
      Finset.card_le_card fun h _ ↦ hall h
    rw [Finset.card_univ, Fintype.card_eq_nat_card] at hle
    exact (Nat.not_le_of_lt hunion) hle
  obtain ⟨h1, hh1⟩ := hexists
  have hnotBad : h1 ∉ bad := fun hmem ↦ hh1 (Finset.mem_union_left _ hmem)
  have hnotUnsafe : h1 ∉ unsafeSet :=
    fun hmem ↦ hh1 (Finset.mem_union_right _ hmem)
  refine ⟨h1, ?_, ?_⟩
  · apply candidateRegular_of_eval_safePolynomial_ne_zero c _ hc
    simpa [unsafeSet] using hnotUnsafe
  · intro d hd hright heq
    apply hnotBad
    exact mem_shiftedWeightedBadOrderTraceSupport_iff.mpr
      ⟨d, hd, hright, heq⟩

/-- The coefficient-`48` estimates and a margin of fourteen beyond their
common divisor-count envelope produce an escaping parameter whose shifted
trace is still candidate regular.  The explicit margin is the exact extra
input needed to make the middle-game step iterable. -/
theorem
    exists_left_element_escaping_shiftedCandidateOrders_and_regular_of_estimate
    (p : ℕ) (c alpha beta gamma : E) (H1 : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ)
    (h2 : (2 : E) ≠ 0) (hc : c ^ 2 ≠ 4) (halpha : alpha ≠ 0)
    (hrightOrder : ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      Nat.card (rightSubgroup d) = d)
    (hCZ : ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      ((shiftedWeightedTraceEquationSolutions
        alpha beta gamma H1 (rightSubgroup d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (Nat.card H1)
            (Nat.card (rightSubgroup d)))
    (hmargin :
      (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
          corvajaZannierCurrentOrderEnvelope p (Nat.card H1) + 14 <
        (Nat.card H1 : ℝ)) :
    ∃ h1 : H1,
      OrderedTraceCandidateRegular c c c
          (weightedSplitTorusTrace alpha beta h1 + gamma) ∧
        ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
          ∀ h2 : rightSubgroup d,
            weightedSplitTorusTrace alpha beta h1 + gamma ≠
              splitTorusTrace h2 := by
  classical
  have hCZIndexed :
      ∀ d ∈ middleGameCandidateOrders p (Nat.card H1),
      ((shiftedWeightedTraceEquationSolutions
        alpha beta gamma H1 (rightSubgroup d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (Nat.card H1) d := by
    intro d hd
    have hEstimate := hCZ d hd
    rw [hrightOrder d hd] at hEstimate
    exact hEstimate
  have hbad :
      ((shiftedWeightedBadOrderTraceSupport
        alpha beta gamma H1
          (middleGameCandidateOrders p (Nat.card H1))
          rightSubgroup).card : ℝ) ≤
        (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
          corvajaZannierCurrentOrderEnvelope p (Nat.card H1) := by
    calc
      ((shiftedWeightedBadOrderTraceSupport
        alpha beta gamma H1
          (middleGameCandidateOrders p (Nat.card H1))
          rightSubgroup).card : ℝ) ≤
          ∑ d ∈ middleGameCandidateOrders p (Nat.card H1),
            corvajaZannierTraceUpperBound p (Nat.card H1) d := by
        exact
          shiftedWeightedBadOrderTraceSupport_card_cast_le_sum
            (E := E) (alpha := alpha) (beta := beta) (gamma := gamma)
            (H1 := H1)
            (orders := middleGameCandidateOrders p (Nat.card H1))
            (rightSubgroup := rightSubgroup)
            (bound :=
              fun d ↦ corvajaZannierTraceUpperBound p (Nat.card H1) d)
            hCZIndexed
      _ ≤
          (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p (Nat.card H1) := by
        exact middleGameCorvajaZannierSum_le_divisorCount_mul_envelope
          p (Nat.card H1)
  have hsmallReal :
      (((shiftedWeightedBadOrderTraceSupport
        alpha beta gamma H1
          (middleGameCandidateOrders p (Nat.card H1))
          rightSubgroup).card + 14 : ℕ) : ℝ) <
        (Nat.card H1 : ℝ) := by
    calc
      (((shiftedWeightedBadOrderTraceSupport
        alpha beta gamma H1
          (middleGameCandidateOrders p (Nat.card H1))
          rightSubgroup).card + 14 : ℕ) : ℝ) =
          ((shiftedWeightedBadOrderTraceSupport
            alpha beta gamma H1
              (middleGameCandidateOrders p (Nat.card H1))
              rightSubgroup).card : ℝ) + 14 := by norm_num
      _ ≤
          (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
              corvajaZannierCurrentOrderEnvelope p (Nat.card H1) +
            14 := by
        linarith
      _ < (Nat.card H1 : ℝ) := hmargin
  have hsmall :
      (shiftedWeightedBadOrderTraceSupport
        alpha beta gamma H1
          (middleGameCandidateOrders p (Nat.card H1))
          rightSubgroup).card + 14 <
        Nat.card H1 := by
    exact_mod_cast hsmallReal
  exact
    exists_left_element_escaping_shiftedCandidateOrders_and_regular
      c alpha beta gamma H1
        (middleGameCandidateOrders p (Nat.card H1))
        rightSubgroup h2 hc halpha hsmall

end

end GenMarkoff.Symmetric.MiddleGame
