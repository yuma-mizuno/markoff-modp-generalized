import GenMarkoff.General.Assembly.RegularMiddleIteration
import BGS.NumberTheory.ExplicitDivisorBound
import BGS.Markoff.Endgame.PrimitiveInclusionExclusion

/-!
# Scaled divisor-envelope estimate for the middle game

The regular middle game must absorb twenty exceptional square-coset
parameters from the ordered safe polynomial, and parity closure doubles the
Corvaja--Zannier divisor envelope.  This file proves
`scaled_divisorCount_mul_corvajaZannierEnvelope_lt_currentOrder`: for a scale
`s`, if `(s * C * T)^3 < n` and `s * C * T * n < p`, where
`C = corvajaZannierCorollaryTwoSafeCoefficient` (equal to `48`) and
`T = #divisors (p - 1) + #divisors (p + 1)`, then
`s * T * corvajaZannierCurrentOrderEnvelope p n < n`.  The middle game uses
it with `s = 4`, which leaves half of `n` for the additive margin.
-/

namespace GenMarkoff.General.Assembly

open Filter BGS.Markoff

noncomputable section

/-- If `(scale * C * T)^3 < currentOrder` and
`scale * C * T * currentOrder < p`, with
`C = corvajaZannierCorollaryTwoSafeCoefficient` and `T` the simultaneous
divisor count of `p - 1` and `p + 1`, then the scaled divisor-envelope term
`scale * T * corvajaZannierCurrentOrderEnvelope p currentOrder` is less than
`currentOrder`. -/
theorem scaled_divisorCount_mul_corvajaZannierEnvelope_lt_currentOrder
    (scale p currentOrder : ℕ) (hcurrentOrder : 0 < currentOrder)
    (hcube :
      (scale * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card))) ^ 3 <
          currentOrder)
    (hlinear :
      scale * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) *
          currentOrder < p) :
    (scale : ℝ) *
        (((p - 1).divisors.card +
          (p + 1).divisors.card : ℕ) : ℝ) *
        corvajaZannierCurrentOrderEnvelope p currentOrder <
      (currentOrder : ℝ) := by
  let divisorCount : ℕ :=
    (p - 1).divisors.card + (p + 1).divisors.card
  let coefficient : ℝ :=
    (scale *
      (corvajaZannierCorollaryTwoSafeCoefficient * divisorCount) : ℕ)
  have horderPos : (0 : ℝ) < currentOrder := by
    exact_mod_cast hcurrentOrder
  have horderNonneg : (0 : ℝ) ≤ currentOrder := horderPos.le
  have hcoefficientNonneg : 0 ≤ coefficient := by
    dsimp [coefficient]
    positivity
  -- First envelope term: `coefficient < n ^ (1/3)` gives
  -- `coefficient * (n * n) ^ (1/3) < n`.
  have hcubeReal :
      coefficient ^ (3 : ℕ) < (currentOrder : ℝ) := by
    dsimp [coefficient, divisorCount]
    exact_mod_cast hcube
  have hcoefficientRoot :
      coefficient < (currentOrder : ℝ) ^ ((1 : ℝ) / 3) := by
    have h := (Real.lt_rpow_inv_iff_of_pos
      hcoefficientNonneg horderNonneg
        (by norm_num : (0 : ℝ) < 3)).2
    have h' :
        coefficient < (currentOrder : ℝ) ^ (3 : ℝ)⁻¹ :=
      h (by simpa [Real.rpow_natCast] using hcubeReal)
    simpa only [one_div] using h'
  have hrootPositive :
      0 < (((currentOrder * currentOrder : ℕ) : ℝ) ^
        ((1 : ℝ) / 3)) := by
    positivity
  have hcubeRootIdentity :
      (currentOrder : ℝ) ^ ((1 : ℝ) / 3) *
          (((currentOrder * currentOrder : ℕ) : ℝ) ^
            ((1 : ℝ) / 3)) =
        (currentOrder : ℝ) := by
    rw [Nat.cast_mul]
    rw [← Real.mul_rpow horderNonneg
      (mul_nonneg horderNonneg horderNonneg)]
    convert Real.pow_rpow_inv_natCast horderNonneg
      (by norm_num : (3 : ℕ) ≠ 0) using 1
    all_goals ring_nf
  have hrootTerm :
      coefficient *
          (((currentOrder * currentOrder : ℕ) : ℝ) ^
            ((1 : ℝ) / 3)) <
        (currentOrder : ℝ) := by
    calc
      coefficient *
            (((currentOrder * currentOrder : ℕ) : ℝ) ^
              ((1 : ℝ) / 3)) <
          (currentOrder : ℝ) ^ ((1 : ℝ) / 3) *
            (((currentOrder * currentOrder : ℕ) : ℝ) ^
              ((1 : ℝ) / 3)) :=
        mul_lt_mul_of_pos_right hcoefficientRoot hrootPositive
      _ = (currentOrder : ℝ) := hcubeRootIdentity
  -- Second envelope term: `coefficient * n < p` gives
  -- `coefficient * (n * n) / p < n`.
  have hlinearReal :
      coefficient * (currentOrder : ℝ) < (p : ℝ) := by
    dsimp [coefficient, divisorCount]
    exact_mod_cast hlinear
  have hpPos : (0 : ℝ) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hquotientTerm :
      coefficient *
          (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ)) <
        (currentOrder : ℝ) := by
    have hratio :
        coefficient * (currentOrder : ℝ) / (p : ℝ) < 1 :=
      (div_lt_one hpPos).2 hlinearReal
    calc
      coefficient *
            (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ)) =
          (coefficient * (currentOrder : ℝ) / (p : ℝ)) *
            (currentOrder : ℝ) := by
        rw [Nat.cast_mul]
        ring
      _ < 1 * (currentOrder : ℝ) :=
        mul_lt_mul_of_pos_right hratio horderPos
      _ = (currentOrder : ℝ) := one_mul _
  -- The envelope is the maximum of the two terms.
  calc
    (scale : ℝ) *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
          corvajaZannierCurrentOrderEnvelope p currentOrder =
        coefficient * max
          (((currentOrder * currentOrder : ℕ) : ℝ) ^
            ((1 : ℝ) / 3))
          (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ)) := by
      simp only [corvajaZannierCurrentOrderEnvelope]
      dsimp [coefficient, divisorCount]
      push_cast
      ring
    _ = max
        (coefficient *
          (((currentOrder * currentOrder : ℕ) : ℝ) ^
            ((1 : ℝ) / 3)))
        (coefficient *
          (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ))) :=
      mul_max_of_nonneg _ _ hcoefficientNonneg
    _ < (currentOrder : ℝ) := max_lt hrootTerm hquotientTerm

end

end GenMarkoff.General.Assembly
