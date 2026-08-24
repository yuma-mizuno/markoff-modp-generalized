import GenMarkoff.General.MiddleGame.ActualOrderGrowth
import GenMarkoff.Symmetric.Assembly.RegularMiddleIteration

/-!
# Parity-closed actual-order escape

For an actual rotation, the order attached to a trace `t` is

`rotationOrder t / gcd (rotationOrder t) 2`.

Thus the bad unsquared orders for a current actual order `L` are not merely
the BGS orders `d ≤ L`, but all divisor orders satisfying

`d / gcd d 2 ≤ L`.

This file defines that parity-closed family and reruns the shifted
Corvaja--Zannier finite-union argument for it.

## New consideration in the general rotation proof

The fixed-coefficient Vieta rotation acts on the torus parameter by `q ^ 2`,
while the available trace classification is indexed by the unsquared
eigenvalue order `d = order(q)`.  Therefore:

* small actual rotation order means `d / gcd(d,2) ≤ L`, not `d ≤ L`;
* the candidate divisor count is unchanged, but such a `d` can be as large
  as `2 * L`;
* a factor two in the common Corvaja--Zannier envelope is sufficient, so the
  cube and linear size hypotheses below use twice the old coefficient.

This parity closure is the additional argument needed to turn the earlier
growth-or-factor-two dichotomy into strict growth for the actual rotation.
-/

namespace GenMarkoff.General.MiddleGame

open BGS.Markoff
open GenMarkoff.Symmetric.MiddleGame

noncomputable section

/-- Divisor orders whose associated squared-eigenvalue order is at most the
current actual order. -/
def parityClosedMiddleGameCandidateOrders
    (p currentOrder : ℕ) : Finset ℕ :=
  ((p - 1).divisors ∪ (p + 1).divisors).filter fun d ↦
    d / Nat.gcd d 2 ≤ currentOrder

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

/-- Parity closure changes only the filter, not the ambient divisor union. -/
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

/-- Allowing an unsquared order up to twice the actual order costs at most a
factor two in the common Corvaja--Zannier envelope.  This is the new
numerical input forced by passing from the old `d ≤ L` family to its
parity closure. -/
theorem corvajaZannierTraceUpperBound_le_two_mul_currentOrderEnvelope
    (p currentOrder d : ℕ) (hd : d ≤ 2 * currentOrder) :
    corvajaZannierTraceUpperBound p currentOrder d ≤
      2 * corvajaZannierCurrentOrderEnvelope p currentOrder := by
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

/-- The whole parity-closed bad-order sum is bounded by twice the ordinary
divisor-count envelope.  The number of candidate divisors does not increase;
only the individual envelope changes. -/
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

/-- Exact finite-union escape for the parity-closed order family.  The
numerical premise is the precise enlarged Corvaja--Zannier sum that must be
smaller than the actual left-subgroup order. -/
theorem
    exists_left_element_escaping_shiftedParityClosedOrders_of_corvajaZannierSum
    (p : ℕ) (alpha beta gamma : E) (H1 : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ)
    (hrightOrder :
      ∀ d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1),
        Nat.card (rightSubgroup d) = d)
    (hCZ :
      ∀ d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1),
        ((shiftedWeightedTraceEquationSolutions
          alpha beta gamma H1 (rightSubgroup d)).card : ℝ) ≤
            corvajaZannierTraceUpperBound p (Nat.card H1)
              (Nat.card (rightSubgroup d)))
    (hsmall :
      (∑ d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1),
          corvajaZannierTraceUpperBound p (Nat.card H1) d) <
        (Nat.card H1 : ℝ)) :
    ∃ h1 : H1,
      ∀ d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1),
        ∀ h2 : rightSubgroup d,
          weightedSplitTorusTrace alpha beta h1 + gamma ≠
            splitTorusTrace h2 := by
  classical
  let orders :=
    parityClosedMiddleGameCandidateOrders p (Nat.card H1)
  let bad := shiftedWeightedBadOrderTraceSupport
    alpha beta gamma H1 orders rightSubgroup
  have hCZIndexed :
      ∀ d ∈ orders,
        ((shiftedWeightedTraceEquationSolutions alpha beta gamma H1
          (rightSubgroup d)).card : ℝ) ≤
            corvajaZannierTraceUpperBound p (Nat.card H1) d := by
    intro d hd
    have hd' :
        d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1) := by
      simpa [orders] using hd
    have hEstimate := hCZ d hd'
    rw [hrightOrder d hd'] at hEstimate
    exact hEstimate
  have hbadReal : (bad.card : ℝ) < (Nat.card H1 : ℝ) := by
    calc
      (bad.card : ℝ) ≤
          ∑ d ∈ orders,
            corvajaZannierTraceUpperBound p (Nat.card H1) d := by
        exact
          shiftedWeightedBadOrderTraceSupport_card_cast_le_sum
            (E := E) (alpha := alpha) (beta := beta) (gamma := gamma)
            (H1 := H1) (orders := orders)
            (rightSubgroup := rightSubgroup)
            (bound :=
              fun d ↦ corvajaZannierTraceUpperBound p (Nat.card H1) d)
            hCZIndexed
      _ < (Nat.card H1 : ℝ) := by
        simpa [orders] using hsmall
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

/-- Doubling the coefficient in the two standard elementary size
inequalities absorbs the factor-two parity-closed envelope and yields a
genuine escape from every bad actual order. -/
theorem
    exists_left_element_escaping_shiftedParityClosedOrders_of_corvajaZannierSizeBounds
    (p : ℕ) (alpha beta gamma : E) (H1 : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ)
    (hrightOrder :
      ∀ d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1),
        Nat.card (rightSubgroup d) = d)
    (hCZ :
      ∀ d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1),
        ((shiftedWeightedTraceEquationSolutions
          alpha beta gamma H1 (rightSubgroup d)).card : ℝ) ≤
            corvajaZannierTraceUpperBound p (Nat.card H1)
              (Nat.card (rightSubgroup d)))
    (hcurrentOrder : 0 < Nat.card H1)
    (hcube :
      (2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card))) ^ 3 <
          Nat.card H1)
    (hlinear :
      2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) *
          Nat.card H1 < p) :
    ∃ h1 : H1,
      ∀ d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1),
        ∀ h2 : rightSubgroup d,
          weightedSplitTorusTrace alpha beta h1 + gamma ≠
            splitTorusTrace h2 := by
  apply
    exists_left_element_escaping_shiftedParityClosedOrders_of_corvajaZannierSum
      p alpha beta gamma H1 rightSubgroup hrightOrder hCZ
  exact
    (parityClosedCorvajaZannierSum_le_two_mul_divisorCount_mul_envelope
      p (Nat.card H1)).trans_lt
        (GenMarkoff.Symmetric.Assembly.two_mul_divisorCount_mul_corvajaZannierEnvelope_lt_currentOrder
            p (Nat.card H1) hcurrentOrder hcube hlinear)

/-- Axis-independent strict actual-order growth after parity closure.

Compared with the earlier square-coset theorem, the bad family is now
`d / gcd(d,2) ≤ L`; hence the factor-two residual branch is impossible.  The
price is exactly the doubled coefficient in the cube and linear size
hypotheses. -/
theorem exists_iterate_with_larger_actualOrder_of_squareCosetTrace
    {T : Type*}
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (t : ZMod p) (hD : discriminant t ≠ 0)
    (q : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (rotation : T → T) (x : T) (targetTrace : T → ZMod p)
    (alpha beta gamma : quadraticFiniteField p)
    (hsigma : alpha * beta ≠ 0)
    (hEven : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0)
    (hreachable :
      ∀ h : Subgroup.zpowers (q ^ 2),
        ∃ n : ℕ,
          weightedSplitTorusTrace alpha beta h + gamma =
            algebraMap (ZMod p) (quadraticFiniteField p)
              (targetTrace (((rotation)^[n]) x)))
    (hbelowEndgame :
      (rotationLinearOrder t : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      (2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card))) ^ 3 <
          rotationLinearOrder t)
    (hlinear :
      2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) *
          rotationLinearOrder t < p) :
    ∃ n : ℕ,
      let t' := targetTrace (((rotation)^[n]) x)
      rotationLinearOrder t < rotationLinearOrder t' := by
  let E := quadraticFiniteField p
  let H1 : Subgroup Eˣ := Subgroup.zpowers (q ^ 2)
  let rightSubgroup : ℕ → Subgroup Eˣ :=
    fun d ↦ middleGameRightSubgroup p d
  letI : DecidableEq E := Classical.decEq E
  have hleftCard :
      Nat.card H1 = rotationLinearOrder t := by
    simpa [H1, E] using
      card_zpowers_sq_eq_rotationLinearOrder_of_discriminant_ne_zero
        p t q hD heigen
  have hrightOrder :
      ∀ d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1),
        Nat.card (rightSubgroup d) = d := by
    intro d hd
    exact
      middleGameRightSubgroup_natCard p (2 * Nat.card H1) d
        (mem_middleGameCandidateOrders_two_mul_of_mem_parityClosed hd)
  have hCZ :
      ∀ d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1),
        ((shiftedWeightedTraceEquationSolutions
          alpha beta gamma H1 (rightSubgroup d)).card : ℝ) ≤
            corvajaZannierTraceUpperBound p (Nat.card H1)
              (Nat.card (rightSubgroup d)) := by
    intro d _hd
    exact
      weightedShiftedTraceEquationSolutions_card_cast_le_corvajaZannier
        p E alpha beta gamma H1 (rightSubgroup d)
          hpTwo hsigma hEven
  obtain ⟨h, hEscapes⟩ :=
    exists_left_element_escaping_shiftedParityClosedOrders_of_corvajaZannierSizeBounds
      p alpha beta gamma H1 rightSubgroup hrightOrder hCZ Nat.card_pos
        (by rw [hleftCard]; exact hcube)
        (by rw [hleftCard]; exact hlinear)
  obtain ⟨n, hyTrace⟩ := hreachable h
  let t' : ZMod p := targetTrace (((rotation)^[n]) x)
  refine ⟨n, ?_⟩
  change rotationLinearOrder t < rotationLinearOrder t'
  by_contra hgrowth
  have htargetLe :
      rotationLinearOrder t' ≤ rotationLinearOrder t :=
    Nat.le_of_not_gt hgrowth
  have hnonparabolic : t' ^ 2 ≠ 4 := by
    intro hparabolic
    have htarget :
        rotationLinearOrder t' = p :=
      rotationLinearOrder_eq_prime_of_parabolicTrace
        p hpTwo t' hparabolic
    have hthreshold :=
      endgamePowerThreshold_le_prime p delta hdelta
    have htargetLeReal :
        (p : ℝ) ≤ (rotationLinearOrder t : ℝ) := by
      calc
        (p : ℝ) = (rotationLinearOrder t' : ℝ) := by
          exact_mod_cast htarget.symm
        _ ≤ (rotationLinearOrder t : ℝ) := by
          exact_mod_cast htargetLe
    exact
      (not_le_of_gt hbelowEndgame)
        (hthreshold.trans htargetLeReal)
  have hd :
      BGS.Markoff.rotationOrder t' ∈
        parityClosedMiddleGameCandidateOrders p (Nat.card H1) := by
    simpa only [hleftCard] using
      rotationOrder_mem_parityClosedCandidates_of_nonparabolic_actualOrder_le
        p (rotationLinearOrder t) hpTwo t' hnonparabolic htargetLe
  obtain ⟨h2, htrace2⟩ :=
    exists_middleGameRightSubgroup_trace_of_nonparabolic_rotationOrder
      p (BGS.Markoff.rotationOrder t') hpTwo t' hnonparabolic rfl
  apply hEscapes (BGS.Markoff.rotationOrder t') hd h2
  exact hyTrace.trans htrace2

end

end GenMarkoff.General.MiddleGame
