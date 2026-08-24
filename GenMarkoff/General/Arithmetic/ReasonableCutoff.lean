import BGS.Markoff.PreliminaryNumerics

/-!
# A first reasonable universal cutoff

The legacy analytic route forces the simultaneous divisor count

`T = τ(p - 1) + τ(p + 1)`

below an extremely small power of `p`.  The order-preserving coarse route
needs only the structural frontier `p ≤ C * T^8`.  The elementary BGS
tenth-moment estimate `T^10 ≤ 2^457 * p` then rules out that frontier above
the explicit cutoff in this file.

The coefficient `32 * 193^6` deliberately has slack.  It accommodates:

* the two-to-one trace fibers;
* the half-step-to-actual-order factor two;
* the additive exceptional-trace margin; and
* the coefficient-`192` Corvaja--Zannier cube.

No divisor table or maximal-divisor certificate is used.
-/

namespace GenMarkoff.General.Explicit

open BGS.Markoff

/-- Slack coefficient for the general order-preserving `T^8` frontier. -/
def reasonableFrontierCoefficient : ℕ :=
  32 * 193 ^ 6

theorem reasonableFrontierCoefficient_eq :
    reasonableFrontierCoefficient = 32 * 193 ^ 6 := rfl

theorem reasonableFrontierCoefficient_pos :
    0 < reasonableFrontierCoefficient := by
  norm_num [reasonableFrontierCoefficient]

/-- Open numerical boundary obtained by combining the general `T^8`
frontier with `T^10 ≤ 2^457 p`. -/
def reasonableAnalyticOpenCutoff : ℕ :=
  reasonableFrontierCoefficient ^ 5 * 2 ^ 1828

/-- Closed form of the first reasonable universal analytic cutoff. -/
opaque reasonableAnalyticCutoffData :
    {n : ℕ // n = reasonableAnalyticOpenCutoff + 1} :=
  ⟨reasonableAnalyticOpenCutoff + 1, rfl⟩

def reasonableAnalyticCutoff : ℕ :=
  reasonableAnalyticCutoffData.1

theorem reasonableAnalyticCutoff_eq :
    reasonableAnalyticCutoff = reasonableAnalyticOpenCutoff + 1 :=
  reasonableAnalyticCutoffData.2

theorem reasonableAnalyticCutoff_gt_one :
    1 < reasonableAnalyticCutoff := by
  rw [reasonableAnalyticCutoff_eq]
  have hpos : 0 < reasonableAnalyticOpenCutoff := by
    exact Nat.mul_pos
      (pow_pos reasonableFrontierCoefficient_pos 5)
      (pow_pos (by norm_num) 1828)
  omega

#guard_msgs (drop warning) in
theorem five_le_reasonableAnalyticCutoff :
    5 ≤ reasonableAnalyticCutoff := by
  rw [reasonableAnalyticCutoff_eq, reasonableAnalyticOpenCutoff]
  have hcoefficient : 1 ≤ reasonableFrontierCoefficient ^ 5 :=
    Nat.one_le_pow 5 reasonableFrontierCoefficient
      reasonableFrontierCoefficient_pos
  have htwo : 4 ≤ 2 ^ 1828 := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 1828 :=
        Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hproduct :
      4 ≤ reasonableFrontierCoefficient ^ 5 * 2 ^ 1828 := by
    calc
      4 = 1 * 4 := by norm_num
      _ ≤ reasonableFrontierCoefficient ^ 5 * 2 ^ 1828 :=
        Nat.mul_le_mul hcoefficient htwo
  omega

#guard_msgs (drop warning) in
theorem seven_le_reasonableAnalyticCutoff :
    7 ≤ reasonableAnalyticCutoff := by
  rw [reasonableAnalyticCutoff_eq, reasonableAnalyticOpenCutoff]
  have hcoefficient : 1 ≤ reasonableFrontierCoefficient ^ 5 :=
    Nat.one_le_pow 5 reasonableFrontierCoefficient
      reasonableFrontierCoefficient_pos
  have htwo : 8 ≤ 2 ^ 1828 := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ 1828 :=
        Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hproduct :
      8 ≤ reasonableFrontierCoefficient ^ 5 * 2 ^ 1828 := by
    calc
      8 = 1 * 8 := by norm_num
      _ ≤ reasonableFrontierCoefficient ^ 5 * 2 ^ 1828 :=
        Nat.mul_le_mul hcoefficient htwo
  omega

theorem reasonableAnalyticOpenCutoff_lt_of_cutoff_le
    {p : ℕ} (hp : reasonableAnalyticCutoff ≤ p) :
    reasonableAnalyticOpenCutoff < p := by
  rw [reasonableAnalyticCutoff_eq] at hp
  omega

set_option maxRecDepth 100000 in
#guard_msgs (drop warning) in
theorem preliminaryStrongApproximationCutoff_le_reasonableAnalyticCutoff :
    preliminaryStrongApproximationCutoff ≤ reasonableAnalyticCutoff := by
  have hbase :
      2 * (48 ^ 3 + 1) ^ 2 ≤ reasonableFrontierCoefficient := by
    norm_num [reasonableFrontierCoefficient]
  have hpow :
      (2 * (48 ^ 3 + 1) ^ 2) ^ 5 ≤
        reasonableFrontierCoefficient ^ 5 :=
    Nat.pow_le_pow_left hbase 5
  rw [preliminaryStrongApproximationCutoff_eq,
    reasonableAnalyticCutoff_eq]
  apply Nat.add_le_add_right
  calc
    2 ^ 1833 * (48 ^ 3 + 1) ^ 10 =
        (2 * (48 ^ 3 + 1) ^ 2) ^ 5 * 2 ^ 1828 := by
      rw [show (1833 : ℕ) = 5 + 1828 by norm_num, pow_add,
        show (10 : ℕ) = 2 * 5 by norm_num, pow_mul]
      ring
    _ ≤ reasonableFrontierCoefficient ^ 5 * 2 ^ 1828 := by
      gcongr
    _ = reasonableAnalyticOpenCutoff := rfl

theorem preliminaryStrongApproximationCutoff_le_of_reasonableCutoff_le
    {p : ℕ} (hp : reasonableAnalyticCutoff ≤ p) :
    preliminaryStrongApproximationCutoff ≤ p :=
  preliminaryStrongApproximationCutoff_le_reasonableAnalyticCutoff.trans hp

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
/-- The displayed cutoff has fewer than one thousand decimal digits. -/
theorem reasonableAnalyticCutoff_lt_ten_pow_oneThousand :
    reasonableAnalyticCutoff < 10 ^ 1000 := by
  rw [reasonableAnalyticCutoff_eq, reasonableAnalyticOpenCutoff,
    reasonableFrontierCoefficient]
  norm_num

set_option maxRecDepth 100000 in
#guard_msgs (drop warning) in
/-- Above the reasonable cutoff, the elementary tenth moment excludes the
general order-preserving `T^8` obstruction. -/
theorem reasonableFrontierCoefficient_mul_divisorSum_pow_eight_lt
    {p : ℕ} (hpTwo : 2 ≤ p)
    (hpCutoff : reasonableAnalyticCutoff ≤ p) :
    reasonableFrontierCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) ^ 8 < p := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  let C := reasonableFrontierCoefficient
  let Q := reasonableAnalyticOpenCutoff
  have hmoment : T ^ 10 ≤ 2 ^ 457 * p := by
    simpa [T, preliminaryDivisorMomentConstant] using
      preliminary_divisor_sum_pow_ten_le hpTwo
  have hQ : Q < p := by
    simpa [Q] using
      reasonableAnalyticOpenCutoff_lt_of_cutoff_le hpCutoff
  by_contra hfrontier
  have hpLe : p ≤ C * T ^ 8 := by
    simpa [C, T] using Nat.le_of_not_gt hfrontier
  have hpPowLe : p ^ 5 ≤ Q * p ^ 4 := by
    calc
      p ^ 5 ≤ (C * T ^ 8) ^ 5 :=
        Nat.pow_le_pow_left hpLe 5
      _ = C ^ 5 * (T ^ 10) ^ 4 := by ring
      _ ≤ C ^ 5 * (2 ^ 457 * p) ^ 4 := by gcongr
      _ = (C ^ 5 * 2 ^ 1828) * p ^ 4 := by ring
      _ = Q * p ^ 4 := by
        simp [Q, reasonableAnalyticOpenCutoff, C]
  have hstrict : Q * p ^ 4 < p ^ 5 := by
    calc
      Q * p ^ 4 < p * p ^ 4 :=
        Nat.mul_lt_mul_of_pos_right hQ (pow_pos (by omega) 4)
      _ = p ^ 5 := by ring
  exact (not_lt_of_ge hpPowLe) hstrict

set_option maxRecDepth 100000 in
#guard_msgs (drop warning) in
private theorem coefficient_192_pow_twenty_mul_moment_sq_le_openCutoff :
    192 ^ 20 * (2 ^ 457) ^ 2 ≤ reasonableAnalyticOpenCutoff := by
  have hbase : 192 ^ 4 ≤ reasonableFrontierCoefficient := by
    norm_num [reasonableFrontierCoefficient]
  have hcoefficient :
      192 ^ 20 ≤ reasonableFrontierCoefficient ^ 5 := by
    rw [show (20 : ℕ) = 4 * 5 by norm_num, pow_mul]
    exact Nat.pow_le_pow_left hbase 5
  calc
    192 ^ 20 * (2 ^ 457) ^ 2 ≤
        reasonableFrontierCoefficient ^ 5 * 2 ^ 914 := by
      rw [show (914 : ℕ) = 457 * 2 by norm_num, pow_mul]
      exact Nat.mul_le_mul hcoefficient (le_refl _)
    _ ≤ reasonableFrontierCoefficient ^ 5 * 2 ^ 1828 := by
      exact Nat.mul_le_mul_left (reasonableFrontierCoefficient ^ 5)
        (Nat.pow_le_pow_right
          (by norm_num : 0 < (2 : ℕ)) (by norm_num : 914 ≤ 1828))
    _ = reasonableAnalyticOpenCutoff := rfl

set_option maxRecDepth 100000 in
private theorem coefficient_2064_pow_twenty_mul_moment_four_le_openCutoff :
    2064 ^ 20 * (2 ^ 457) ^ 4 ≤ reasonableAnalyticOpenCutoff := by
  have hbase : 2064 ^ 4 ≤ reasonableFrontierCoefficient := by
    norm_num [reasonableFrontierCoefficient]
  have hcoefficient :
      2064 ^ 20 ≤ reasonableFrontierCoefficient ^ 5 := by
    rw [show (20 : ℕ) = 4 * 5 by norm_num, pow_mul]
    exact Nat.pow_le_pow_left hbase 5
  calc
    2064 ^ 20 * (2 ^ 457) ^ 4 ≤
        reasonableFrontierCoefficient ^ 5 * 2 ^ 1828 := by
      rw [show (1828 : ℕ) = 457 * 4 by norm_num, pow_mul]
      exact Nat.mul_le_mul hcoefficient (le_refl _)
    _ = reasonableAnalyticOpenCutoff := rfl

#guard_msgs (drop warning) in
/-- The coefficient used by the degree-one middle game, together with the
simultaneous divisor count, is smaller than the fourth root of the prime. -/
theorem reasonable_middleGame_divisor_term_lt_rpow_one_div_four
    {p : ℕ} (hp : reasonableAnalyticCutoff ≤ p) :
    ((192 * ((p - 1).divisors.card +
      (p + 1).divisors.card) : ℕ) : ℝ) <
        (p : ℝ) ^ (1 / 4 : ℝ) := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  have hpTwo : 2 ≤ p := by
    have := reasonableAnalyticCutoff_gt_one.trans_le hp
    omega
  have hmoment : T ^ 10 ≤ 2 ^ 457 * p := by
    simpa [T, preliminaryDivisorMomentConstant] using
      preliminary_divisor_sum_pow_ten_le hpTwo
  have hQ : reasonableAnalyticOpenCutoff < p :=
    reasonableAnalyticOpenCutoff_lt_of_cutoff_le hp
  have hpowNat : (192 * T) ^ 20 < p ^ 5 := by
    calc
      (192 * T) ^ 20 = 192 ^ 20 * (T ^ 10) ^ 2 := by ring
      _ ≤ 192 ^ 20 * (2 ^ 457 * p) ^ 2 := by gcongr
      _ = (192 ^ 20 * (2 ^ 457) ^ 2) * p ^ 2 := by ring
      _ ≤ reasonableAnalyticOpenCutoff * p ^ 2 := by
        exact Nat.mul_le_mul_right _
          coefficient_192_pow_twenty_mul_moment_sq_le_openCutoff
      _ < p * p ^ 2 := by
        exact Nat.mul_lt_mul_of_pos_right hQ (pow_pos (by omega) 2)
      _ = p ^ 3 := by ring
      _ ≤ p ^ 5 :=
        Nat.pow_le_pow_right (by omega) (by norm_num)
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hpowReal : ((192 * T : ℕ) : ℝ) ^ 20 < (p : ℝ) ^ 5 := by
    exact_mod_cast hpowNat
  have hrootPow :
      ((p : ℝ) ^ (1 / 4 : ℝ)) ^ 20 = (p : ℝ) ^ 5 := by
    calc
      ((p : ℝ) ^ (1 / 4 : ℝ)) ^ 20 =
          (p : ℝ) ^ ((1 / 4 : ℝ) * 20) :=
        (Real.rpow_mul_natCast hpNonnegative (1 / 4 : ℝ) 20).symm
      _ = (p : ℝ) ^ 5 := by norm_num
  change (192 * T : ℕ) < (p : ℝ) ^ (1 / 4 : ℝ)
  apply lt_of_pow_lt_pow_left₀ 20 (Real.rpow_nonneg hpNonnegative _)
  rw [hrootPow]
  exact hpowReal

#guard_msgs (drop warning) in
/-- The complete primitive-trace coefficient `2064 = 2 * 1032`, together
with two divisor factors, is smaller than the fourth root of the prime. -/
theorem reasonable_primitive_divisor_term_lt_rpow_one_div_four
    {p : ℕ} (hp : reasonableAnalyticCutoff ≤ p) :
    ((2064 * ((p - 1).divisors.card +
      (p + 1).divisors.card) ^ 2 : ℕ) : ℝ) <
        (p : ℝ) ^ (1 / 4 : ℝ) := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  have hpTwo : 2 ≤ p := by
    have := reasonableAnalyticCutoff_gt_one.trans_le hp
    omega
  have hmoment : T ^ 10 ≤ 2 ^ 457 * p := by
    simpa [T, preliminaryDivisorMomentConstant] using
      preliminary_divisor_sum_pow_ten_le hpTwo
  have hQ : reasonableAnalyticOpenCutoff < p :=
    reasonableAnalyticOpenCutoff_lt_of_cutoff_le hp
  have hpowNat : (2064 * T ^ 2) ^ 20 < p ^ 5 := by
    calc
      (2064 * T ^ 2) ^ 20 =
          2064 ^ 20 * (T ^ 10) ^ 4 := by ring
      _ ≤ 2064 ^ 20 * (2 ^ 457 * p) ^ 4 := by gcongr
      _ = (2064 ^ 20 * (2 ^ 457) ^ 4) * p ^ 4 := by ring
      _ ≤ reasonableAnalyticOpenCutoff * p ^ 4 := by
        exact Nat.mul_le_mul_right _
          coefficient_2064_pow_twenty_mul_moment_four_le_openCutoff
      _ < p * p ^ 4 := by
        exact Nat.mul_lt_mul_of_pos_right hQ (pow_pos (by omega) 4)
      _ = p ^ 5 := by ring
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hpowReal : ((2064 * T ^ 2 : ℕ) : ℝ) ^ 20 < (p : ℝ) ^ 5 := by
    exact_mod_cast hpowNat
  have hrootPow :
      ((p : ℝ) ^ (1 / 4 : ℝ)) ^ 20 = (p : ℝ) ^ 5 := by
    calc
      ((p : ℝ) ^ (1 / 4 : ℝ)) ^ 20 =
          (p : ℝ) ^ ((1 / 4 : ℝ) * 20) :=
        (Real.rpow_mul_natCast hpNonnegative (1 / 4 : ℝ) 20).symm
      _ = (p : ℝ) ^ 5 := by norm_num
  change (2064 * T ^ 2 : ℕ) < (p : ℝ) ^ (1 / 4 : ℝ)
  apply lt_of_pow_lt_pow_left₀ 20 (Real.rpow_nonneg hpNonnegative _)
  rw [hrootPow]
  exact hpowReal

/-- Assembly-facing primitive-trace certificate at the three-quarter
endgame scale. -/
theorem reasonable_primitiveTrace_explicitInequality
    {p orbitExponent coefficient : ℕ}
    (hp : reasonableAnalyticCutoff ≤ p)
    (horbit :
      (orbitExponent : ℝ) ≤ 2 * (p : ℝ) ^ (1 / 4 : ℝ))
    (hcoefficient : coefficient ≤ 1032) :
    (orbitExponent : ℝ) *
        ((p - 1).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  have hpRealOne : (1 : ℝ) < p := by
    exact_mod_cast reasonableAnalyticCutoff_gt_one.trans_le hp
  have hpRealPos : (0 : ℝ) < p := zero_lt_one.trans hpRealOne
  have hdivisor :
      ((p - 1).divisors.card : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast (show (p - 1).divisors.card ≤ T by
      dsimp [T]
      omega)
  have hweighted :
      (2064 : ℝ) * (T : ℝ) ^ 2 <
        (p : ℝ) ^ (1 / 4 : ℝ) := by
    simpa [T] using
      reasonable_primitive_divisor_term_lt_rpow_one_div_four hp
  calc
    (orbitExponent : ℝ) *
          ((p - 1).divisors.card : ℝ) ^ 2 *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) ≤
        (2 * (p : ℝ) ^ (1 / 4 : ℝ)) *
          (T : ℝ) ^ 2 * (1032 * Real.sqrt (p : ℝ)) := by
      gcongr
      exact_mod_cast hcoefficient
    _ = (2064 * (T : ℝ) ^ 2) *
        ((p : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (p : ℝ)) := by ring
    _ < (p : ℝ) ^ (1 / 4 : ℝ) *
        ((p : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (p : ℝ)) := by
      exact mul_lt_mul_of_pos_right hweighted <|
        mul_pos (Real.rpow_pos_of_pos hpRealPos _) (Real.sqrt_pos.2 hpRealPos)
    _ = p := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpRealPos,
        ← Real.rpow_add hpRealPos]
      norm_num

/-- Split-torus form of the reasonable primitive-trace certificate. -/
theorem reasonable_primitiveTrace_explicitInequality_of_card_sub_one
    {p orbitExponent orbitOrder coefficient : ℕ}
    {delta : ℝ}
    (hp : reasonableAnalyticCutoff ≤ p)
    (hmul : orbitExponent * orbitOrder = p - 1)
    (horder :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orbitOrder)
    (hdelta : (1 : ℝ) / 4 ≤ delta)
    (hcoefficient : coefficient ≤ 1032) :
    (orbitExponent : ℝ) *
        ((p - 1).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  apply reasonable_primitiveTrace_explicitInequality hp ?_ hcoefficient
  have hpNat : 0 < p :=
    Nat.zero_lt_one.trans (reasonableAnalyticCutoff_gt_one.trans_le hp)
  have horbit :=
    BGS.Markoff.orbitExponent_le_rpow_of_mul_order_eq_card_sub_one
      p orbitExponent orbitOrder hpNat hmul horder
  have hpRealOne : (1 : ℝ) ≤ p := by exact_mod_cast hpNat
  calc
    (orbitExponent : ℝ) ≤
        (p : ℝ) ^ ((1 : ℝ) / 2 - delta) := horbit
    _ ≤ (p : ℝ) ^ (1 / 4 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hpRealOne
      linarith
    _ ≤ 2 * (p : ℝ) ^ (1 / 4 : ℝ) := by
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg p) (1 / 4 : ℝ)]

/-- Nonsplit-torus form of the reasonable primitive-trace certificate. -/
theorem reasonable_primitiveTrace_explicitInequality_of_card_add_one
    {p orbitExponent orbitOrder coefficient : ℕ}
    {delta : ℝ}
    (hp : reasonableAnalyticCutoff ≤ p)
    (hmul : orbitExponent * orbitOrder = p + 1)
    (horder :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orbitOrder)
    (hdelta : (1 : ℝ) / 4 ≤ delta)
    (hcoefficient : coefficient ≤ 1032) :
    (orbitExponent : ℝ) *
        ((p - 1).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  apply reasonable_primitiveTrace_explicitInequality hp ?_ hcoefficient
  have hpNat : 0 < p :=
    Nat.zero_lt_one.trans (reasonableAnalyticCutoff_gt_one.trans_le hp)
  have horbit :=
    BGS.Markoff.orbitExponent_le_two_mul_rpow_of_mul_order_eq_card_add_one
      p orbitExponent orbitOrder hpNat hmul horder
  have hpRealOne : (1 : ℝ) ≤ p := by exact_mod_cast hpNat
  calc
    (orbitExponent : ℝ) ≤
        2 * (p : ℝ) ^ ((1 : ℝ) / 2 - delta) := horbit
    _ ≤ 2 * (p : ℝ) ^ (1 / 4 : ℝ) := by
      gcongr
      linarith

/-- Fixed-exponent form used by the connecting cage. -/
theorem reasonable_primitiveTrace_explicitInequality_one
    {p coefficient : ℕ}
    (hp : reasonableAnalyticCutoff ≤ p)
    (hcoefficient : coefficient ≤ 1032) :
    (1 : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  have hpRealOne : (1 : ℝ) ≤ p := by
    have hpNat : 1 ≤ p :=
      (reasonableAnalyticCutoff_gt_one.trans_le hp).le
    exact_mod_cast hpNat
  have hpowOne :
      (1 : ℝ) ≤ (p : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow hpRealOne (by norm_num)
  have horbit :
      ((1 : ℕ) : ℝ) ≤ 2 * (p : ℝ) ^ (1 / 4 : ℝ) := by
    nlinarith
  simpa only [Nat.cast_one] using
    (reasonable_primitiveTrace_explicitInequality
      (p := p) (orbitExponent := 1) (coefficient := coefficient)
      hp horbit hcoefficient)

/-- The BGS preliminary fixed-coefficient estimate is available at the
reasonable cutoff. -/
theorem reasonable_small_fixed_lt_rpow_one_div_eight
    {p fixed : ℕ} (hp : reasonableAnalyticCutoff ≤ p)
    (hfixed : fixed ≤ 100522) :
    (fixed : ℝ) < (p : ℝ) ^ (1 / 8 : ℝ) :=
  preliminary_small_fixed_lt_rpow_one_div_eight
    (preliminaryStrongApproximationCutoff_le_of_reasonableCutoff_le hp)
    hfixed

/-- The exact first/second trace-pair count for the source-order-preserving
coarse startup is absorbed by the displayed `T^8` frontier coefficient. -/
theorem reasonable_coarseRegularTracePairCount_lt
    {p : ℕ} (hp : reasonableAnalyticCutoff ≤ p) :
    let T := (p - 1).divisors.card + (p + 1).divisors.card
    let bound := (192 * T) ^ 3 + 1
    2 * (22 + (2 * bound - 1) * T) ^ 2 < p := by
  dsimp only
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  have hpTwo : 2 ≤ p := by
    have := reasonableAnalyticCutoff_gt_one.trans_le hp
    omega
  have hTOne : 1 ≤ T := by
    have hpPlus : p + 1 ≠ 0 := by omega
    have hone : 1 ∈ (p + 1).divisors :=
      Nat.one_mem_divisors.mpr hpPlus
    have hcard : 1 ≤ (p + 1).divisors.card :=
      Finset.one_le_card.mpr ⟨1, hone⟩
    dsimp [T]
    omega
  have hTLeFourth : T ≤ T ^ 4 := by
    calc
      T = T * 1 := by omega
      _ ≤ T * T ^ 3 := by
        gcongr
        exact Nat.one_le_pow 3 T hTOne
      _ = T ^ 4 := by ring
  have hFourthOne : 1 ≤ T ^ 4 := Nat.one_le_pow 4 T hTOne
  have hadditive : 22 + T ≤ 23 * T ^ 4 := by
    nlinarith
  have hcoefficient :
      2 * 192 ^ 3 + 23 ≤ 4 * 193 ^ 3 := by norm_num
  have hinner :
      22 + (2 * ((192 * T) ^ 3 + 1) - 1) * T ≤
        4 * 193 ^ 3 * T ^ 4 := by
    calc
      22 + (2 * ((192 * T) ^ 3 + 1) - 1) * T =
          22 + (2 * (192 * T) ^ 3 + 1) * T := by
        rw [show 2 * ((192 * T) ^ 3 + 1) - 1 =
          2 * (192 * T) ^ 3 + 1 by omega]
      _ = 2 * 192 ^ 3 * T ^ 4 + (22 + T) := by ring
      _ ≤ 2 * 192 ^ 3 * T ^ 4 + 23 * T ^ 4 := by
        omega
      _ = (2 * 192 ^ 3 + 23) * T ^ 4 := by ring
      _ ≤ (4 * 193 ^ 3) * T ^ 4 := by gcongr
      _ = 4 * 193 ^ 3 * T ^ 4 := by ring
  calc
    2 * (22 + (2 * ((192 * T) ^ 3 + 1) - 1) * T) ^ 2 ≤
        2 * (4 * 193 ^ 3 * T ^ 4) ^ 2 := by gcongr
    _ = reasonableFrontierCoefficient * T ^ 8 := by
      rw [reasonableFrontierCoefficient]
      ring
    _ < p := reasonableFrontierCoefficient_mul_divisorSum_pow_eight_lt
      hpTwo hp

end GenMarkoff.General.Explicit
