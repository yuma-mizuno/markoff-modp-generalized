module

public import GenMarkoff.General.MiddleGame.ActualOrderGrowth
public import GenMarkoff.ShiftedTrace.MiddleGame.ShiftedTraceEquation
public import GenMarkoff.Core.Statements
public import GenMarkoff.TraceCurve.ExceptionalRouting
public import BGS.Markoff.Core.RotationTorus
public import Mathlib.Analysis.Complex.Norm
public import BGS.Markoff.Opening.UnitCircle
public import BGS.Markoff.Opening.CyclotomicBound
public import BGS.Markoff.Core.FiniteRotationEigenvalues
public import BGS.Markoff.Opening.PeriodicSemisimple
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import GenMarkoff.ShiftedTrace.MiddleGame.ActualOrderEscape
public import GenMarkoff.ShiftedTrace.MiddleGame.WeightedShiftedCorvajaZannier
public import BGS.Markoff.MiddleGame.OrderEscape
public import BGS.Dynamics.StrictMeasureEscape
public import BGS.Markoff.MiddleGame.DivisorRange

@[expose] public section

/-!
# Parity-closed candidate orders for the actual-order escape

The fixed-coefficient Vieta rotation acts on the torus parameter by `q ^ 2`,
while `rotationOrder t` is the order of the unsquared eigenvalue `q`.  Hence the
actual order attached to a trace `t` is

`rotationOrder t / gcd (rotationOrder t) 2`,

and the bad unsquared orders for a current actual order `L` are not only the
candidates `d ≤ L` of `BGS.Markoff.middleGameCandidateOrders`, but all divisor
orders of `p - 1` or `p + 1` with

`d / gcd d 2 ≤ L`.

This file defines that family, `parityClosedMiddleGameCandidateOrders`, and
proves the facts that the Corvaja--Zannier union bound needs for it:

* it has at most as many elements as the divisors of `p - 1` and `p + 1`;
* each member satisfies `d ≤ 2 * L`, so it is an ordinary candidate for the
  cutoff `2 * L`;
* the rotation order of a nonparabolic trace with actual order at most `L`
  lies in it;
* the Corvaja--Zannier bound for each member is at most twice
  `corvajaZannierCurrentOrderEnvelope p L`, so the bad-order sum is at most twice
  the divisor-count envelope.

The escape argument that uses these bounds is in
`GenMarkoff.General.Assembly.RegularMiddleIteration`.
-/

namespace GenMarkoff.General.MiddleGame

open BGS.Markoff
open GenMarkoff.ShiftedTrace.MiddleGame

noncomputable section

/-- Divisor orders whose associated squared-eigenvalue order is at most the
current actual order. -/
def parityClosedMiddleGameCandidateOrders
    (p currentOrder : ℕ) : Finset ℕ :=
  ((p - 1).divisors ∪ (p + 1).divisors).filter fun d ↦
    d / Nat.gcd d 2 ≤ currentOrder

/-- Membership in the parity-closed family: the parity bound together with
`d ∣ p - 1` (with `p - 1 ≠ 0`) or `d ∣ p + 1`. -/
theorem mem_parityClosedMiddleGameCandidateOrders_iff
    {p currentOrder d : ℕ} :
    d ∈ parityClosedMiddleGameCandidateOrders p currentOrder ↔
      d / Nat.gcd d 2 ≤ currentOrder ∧
        (d ∣ p - 1 ∧ p - 1 ≠ 0 ∨ d ∣ p + 1) := by
  simp only [parityClosedMiddleGameCandidateOrders, Finset.mem_filter,
    Finset.mem_union, Nat.mem_divisors]
  constructor
  · rintro ⟨hd, hle⟩
    refine ⟨hle, ?_⟩
    rcases hd with hd | hd
    · exact Or.inl hd
    · exact Or.inr hd.1
  · rintro ⟨hle, hd⟩
    refine ⟨?_, hle⟩
    rcases hd with hd | hd
    · exact Or.inl hd
    · exact Or.inr ⟨hd, by omega⟩

/-- The parity-closed family has at most as many elements as the divisors of
`p - 1` and `p + 1`. -/
theorem parityClosedMiddleGameCandidateOrders_card_le
    (p currentOrder : ℕ) :
    (parityClosedMiddleGameCandidateOrders p currentOrder).card ≤
      (p - 1).divisors.card + (p + 1).divisors.card := by
  calc
    (parityClosedMiddleGameCandidateOrders p currentOrder).card ≤
        ((p - 1).divisors ∪ (p + 1).divisors).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ (p - 1).divisors.card + (p + 1).divisors.card :=
      Finset.card_union_le _ _

/-- An unsquared order in the parity-closed family is at most twice the
current actual order. -/
theorem le_two_mul_of_mem_parityClosedMiddleGameCandidateOrders
    {p currentOrder d : ℕ}
    (hd : d ∈ parityClosedMiddleGameCandidateOrders p currentOrder) :
    d ≤ 2 * currentOrder := by
  let g := Nat.gcd d 2
  have hgPos : 0 < g :=
    Nat.gcd_pos_of_pos_right d (by norm_num)
  have hgLe : g ≤ 2 :=
    Nat.gcd_le_right d (by norm_num)
  have hgDvd : g ∣ d :=
    Nat.gcd_dvd_left d 2
  have hquotient : d / g ≤ currentOrder := by
    simpa [g] using
      (mem_parityClosedMiddleGameCandidateOrders_iff.mp hd).1
  calc
    d = d / g * g := (Nat.div_mul_cancel hgDvd).symm
    _ ≤ currentOrder * 2 := Nat.mul_le_mul hquotient hgLe
    _ = 2 * currentOrder := by omega

/-- Every parity-closed candidate is an ordinary BGS candidate after doubling
the current-order cutoff. -/
theorem mem_middleGameCandidateOrders_two_mul_of_mem_parityClosed
    {p currentOrder d : ℕ}
    (hd : d ∈ parityClosedMiddleGameCandidateOrders p currentOrder) :
    d ∈ middleGameCandidateOrders p (2 * currentOrder) := by
  apply mem_middleGameCandidateOrders_iff.mpr
  exact ⟨le_two_mul_of_mem_parityClosedMiddleGameCandidateOrders hd,
    (mem_parityClosedMiddleGameCandidateOrders_iff.mp hd).2⟩

/-- A nonparabolic trace whose actual squared order is at most `currentOrder`
has its BGS unsquared order in the parity-closed family. -/
theorem rotationOrder_mem_parityClosedCandidates_of_nonparabolic_actualOrder_le
    (p currentOrder : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (t : ZMod p) (hnonparabolic : t ^ 2 ≠ 4)
    (hsmall : rotationLinearOrder t ≤ currentOrder) :
    BGS.Markoff.rotationOrder t ∈
      parityClosedMiddleGameCandidateOrders p currentOrder := by
  let d := BGS.Markoff.rotationOrder t
  let g := Nat.gcd d 2
  have hgLe : g ≤ 2 :=
    Nat.gcd_le_right d (by norm_num)
  have hgDvd : g ∣ d :=
    Nat.gcd_dvd_left d 2
  have hquotient : d / g ≤ currentOrder := by
    simpa [d, g, Opening.rotationLinearOrder_eq_bgsRotationOrder_div_gcd]
      using hsmall
  have hdLe : d ≤ 2 * currentOrder := by
    calc
      d = d / g * g := (Nat.div_mul_cancel hgDvd).symm
      _ ≤ currentOrder * 2 := Nat.mul_le_mul hquotient hgLe
      _ = 2 * currentOrder := by omega
  have hdOrdinary :
      d ∈ middleGameCandidateOrders p (2 * currentOrder) :=
    rotationOrder_mem_middleGameCandidateOrders_of_nonparabolic
      p (2 * currentOrder) hpTwo t hnonparabolic hdLe
  apply mem_parityClosedMiddleGameCandidateOrders_iff.mpr
  exact ⟨hquotient,
    (mem_middleGameCandidateOrders_iff.mp hdOrdinary).2⟩

/-- For `d ≤ 2 * currentOrder`, the Corvaja--Zannier trace bound
`corvajaZannierTraceUpperBound p currentOrder d` is at most twice the common
envelope `corvajaZannierCurrentOrderEnvelope p currentOrder`. -/
theorem corvajaZannierTraceUpperBound_le_two_mul_currentOrderEnvelope
    (p currentOrder d : ℕ) (hd : d ≤ 2 * currentOrder) :
    corvajaZannierTraceUpperBound p currentOrder d ≤
      2 * corvajaZannierCurrentOrderEnvelope p currentOrder := by
  -- Bound `currentOrder * d` by twice `currentOrder ^ 2`, then the cube-root and linear terms.
  have hmulNat :
      currentOrder * d ≤ 2 * (currentOrder * currentOrder) := by
    calc
      currentOrder * d ≤ currentOrder * (2 * currentOrder) :=
        Nat.mul_le_mul_left currentOrder hd
      _ = 2 * (currentOrder * currentOrder) := by ring
  have hmul :
      (((currentOrder * d : ℕ) : ℝ)) ≤
        2 * (((currentOrder * currentOrder : ℕ) : ℝ)) := by
    exact_mod_cast hmulNat
  have hroot :
      (((currentOrder * d : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) ≤
        2 * (((currentOrder * currentOrder : ℕ) : ℝ) ^
          ((1 : ℝ) / 3)) := by
    calc
      (((currentOrder * d : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) ≤
          (((2 : ℝ) * (((currentOrder * currentOrder : ℕ) : ℝ))) ^
            ((1 : ℝ) / 3)) :=
        Real.rpow_le_rpow (by positivity) hmul (by norm_num)
      _ = (2 : ℝ) ^ ((1 : ℝ) / 3) *
          (((currentOrder * currentOrder : ℕ) : ℝ) ^
            ((1 : ℝ) / 3)) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
      _ ≤ 2 * (((currentOrder * currentOrder : ℕ) : ℝ) ^
          ((1 : ℝ) / 3)) := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num))
          (by positivity)
  have hquotient :
      (((currentOrder * d : ℕ) : ℝ) / (p : ℝ)) ≤
        2 * (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ)) := by
    calc
      (((currentOrder * d : ℕ) : ℝ) / (p : ℝ)) ≤
          (2 * (((currentOrder * currentOrder : ℕ) : ℝ))) / (p : ℝ) :=
        div_le_div_of_nonneg_right hmul (by positivity)
      _ = 2 * (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ)) := by
        ring
  -- Combine the two comparisons inside the `max`.
  unfold corvajaZannierTraceUpperBound
    corvajaZannierCurrentOrderEnvelope
  calc
    (corvajaZannierCorollaryTwoSafeCoefficient : ℝ) *
        max (((currentOrder * d : ℕ) : ℝ) ^ ((1 : ℝ) / 3))
          (((currentOrder * d : ℕ) : ℝ) / (p : ℝ)) ≤
      (corvajaZannierCorollaryTwoSafeCoefficient : ℝ) *
        (2 * max
          (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3))
          (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply max_le
        · exact hroot.trans
            (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
        · exact hquotient.trans
            (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))
    _ = 2 * ((corvajaZannierCorollaryTwoSafeCoefficient : ℝ) *
        max (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3))
          (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ))) := by
      ring

/-- The sum of Corvaja--Zannier bounds over the parity-closed candidate orders
is at most twice the divisor count of `p - 1` and `p + 1` times the common
envelope. -/
theorem
    parityClosedCorvajaZannierSum_le_two_mul_divisorCount_mul_envelope
    (p currentOrder : ℕ) :
    (∑ d ∈ parityClosedMiddleGameCandidateOrders p currentOrder,
        corvajaZannierTraceUpperBound p currentOrder d) ≤
      2 *
        (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
          corvajaZannierCurrentOrderEnvelope p currentOrder := by
  classical
  calc
    (∑ d ∈ parityClosedMiddleGameCandidateOrders p currentOrder,
        corvajaZannierTraceUpperBound p currentOrder d) ≤
        ∑ _d ∈ parityClosedMiddleGameCandidateOrders p currentOrder,
          2 * corvajaZannierCurrentOrderEnvelope p currentOrder := by
      exact Finset.sum_le_sum fun d hd ↦
        corvajaZannierTraceUpperBound_le_two_mul_currentOrderEnvelope
          p currentOrder d
            (le_two_mul_of_mem_parityClosedMiddleGameCandidateOrders hd)
    _ = ((parityClosedMiddleGameCandidateOrders p currentOrder).card : ℝ) *
        (2 * corvajaZannierCurrentOrderEnvelope p currentOrder) := by
      simp
    _ ≤
        (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
          (2 * corvajaZannierCurrentOrderEnvelope p currentOrder) := by
      apply mul_le_mul_of_nonneg_right _ (by
        unfold corvajaZannierCurrentOrderEnvelope
        positivity)
      exact_mod_cast
        parityClosedMiddleGameCandidateOrders_card_le p currentOrder
    _ = 2 *
        (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
          corvajaZannierCurrentOrderEnvelope p currentOrder := by
      ring

variable {E : Type} [Field E] [Fintype E]

end

end GenMarkoff.General.MiddleGame
