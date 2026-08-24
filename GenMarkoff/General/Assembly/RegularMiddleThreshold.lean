import GenMarkoff.General.Assembly.RegularMiddleIteration
import GenMarkoff.General.Arithmetic.ExplicitCutoff

/-!
# Uniform threshold for the general alternating regular middle game

The general ordered safe polynomial contributes twenty exceptional
square-coset parameters, while parity closure doubles the usual
Corvaja--Zannier divisor envelope.  To retain enough slack for the additive
twenty-point margin, the elementary cube and linear estimates below are
applied with scale four.  This is a new numerical bookkeeping step relative
to the symmetric proof.

The final theorem starts from an `AlternatingRegularState` whose actual
order is above `p^δ` and reaches actual order at least
`p^(1/2+δ)` inside the rotation component of the same fixed coefficient
triple.  No coordinate or coefficient permutation is used.
-/

namespace GenMarkoff.General.Assembly

open Filter BGS.Markoff
open GenMarkoff.General.Explicit

noncomputable section

/-- A scaled version of the elementary divisor-envelope estimate.  Scale
four will leave half of the current order available for the twenty-point
ordered exceptional support. -/
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

/-- Uniform middle-range discharge of the doubled parity-closed envelope
and the twenty ordered exceptional parameters. -/
theorem eventually_alternatingRegularMiddleGame_sizeBound
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ p : ℕ in atTop, ∀ currentOrder : ℕ,
      (p : ℝ) ^ delta < currentOrder →
      (currentOrder : ℝ) < (p : ℝ) ^ (1 - delta) →
      2 *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p currentOrder +
          20 <
        (currentOrder : ℝ) := by
  let epsilon : ℝ := delta / 6
  let C : ℝ :=
    (2 * corvajaZannierCorollaryTwoSafeCoefficient : ℕ) *
      (2 : ℝ) ^ epsilon
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hThreeEpsilon : 3 * epsilon < delta := by
    dsimp [epsilon]
    linarith
  have hLinearExponent : 1 - delta + epsilon < 1 := by
    dsimp [epsilon]
    linarith
  have hDivisor :=
    eventually_corvajaZannierDivisorCount_le_rpow hepsilon
  have hCubeDominance :
      ∀ᶠ p : ℕ in atTop,
        (4 * C) ^ 3 * (p : ℝ) ^ (3 * epsilon) <
          (p : ℝ) ^ delta :=
    eventually_const_mul_rpow_lt_rpow hThreeEpsilon
  have hLinearDominance :
      ∀ᶠ p : ℕ in atTop,
        (4 * C) * (p : ℝ) ^ (1 - delta + epsilon) <
          (p : ℝ) ^ (1 : ℝ) :=
    eventually_const_mul_rpow_lt_rpow hLinearExponent
  have hForty :
      ∀ᶠ p : ℕ in atTop, (40 : ℝ) < (p : ℝ) ^ delta := by
    simpa using
      (eventually_const_mul_rpow_lt_rpow
        (C := (40 : ℝ)) (a := (0 : ℝ)) (b := delta) hdelta)
  filter_upwards [hDivisor, hCubeDominance, hLinearDominance,
    hForty, eventually_ge_atTop 1] with
      p hDivisor hCubeDominance hLinearDominance hForty hpOne
  intro currentOrder hLower hUpper
  have hpRealPos : (0 : ℝ) < p := by
    exact_mod_cast (show 0 < p by omega)
  have hpRealNonneg : (0 : ℝ) ≤ p := hpRealPos.le
  have hCPos : 0 < C := by
    dsimp [C]
    simp only [corvajaZannierCorollaryTwoSafeCoefficient]
    positivity
  have hCurrentPos : 0 < currentOrder := by
    have : (0 : ℝ) < currentOrder :=
      (Real.rpow_pos_of_pos hpRealPos _).trans hLower
    exact_mod_cast this
  have hCurrentNonneg : (0 : ℝ) ≤ currentOrder := by
    positivity
  have hQuadrupleCubeIdentity :
      (4 * (C * (p : ℝ) ^ epsilon)) ^ 3 =
        (4 * C) ^ 3 * (p : ℝ) ^ (3 * epsilon) := by
    rw [mul_pow, mul_pow]
    rw [← Real.rpow_mul_natCast hpRealNonneg epsilon 3]
    ring_nf
  have hQuadrupleCubeReal :
      ((4 * (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card +
            (p + 1).divisors.card)) : ℕ) : ℝ) ^ 3 <
        (currentOrder : ℝ) := by
    calc
      ((4 * (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card +
            (p + 1).divisors.card)) : ℕ) : ℝ) ^ 3 =
          (4 * (corvajaZannierCorollaryTwoSafeCoefficient *
            ((p - 1).divisors.card +
              (p + 1).divisors.card) : ℝ)) ^ 3 := by
        norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      _ ≤ (4 * (C * (p : ℝ) ^ epsilon)) ^ 3 := by
        apply pow_le_pow_left₀
        · positivity
        · exact mul_le_mul_of_nonneg_left hDivisor (by norm_num)
      _ = (4 * C) ^ 3 * (p : ℝ) ^ (3 * epsilon) :=
        hQuadrupleCubeIdentity
      _ < (p : ℝ) ^ delta := hCubeDominance
      _ < (currentOrder : ℝ) := hLower
  have hQuadrupleLinearIdentity :
      4 * (C * (p : ℝ) ^ epsilon) *
          (p : ℝ) ^ (1 - delta) =
        (4 * C) * (p : ℝ) ^ (1 - delta + epsilon) := by
    calc
      4 * (C * (p : ℝ) ^ epsilon) *
            (p : ℝ) ^ (1 - delta) =
          (4 * C) *
            ((p : ℝ) ^ epsilon *
              (p : ℝ) ^ (1 - delta)) := by ring
      _ = (4 * C) *
          (p : ℝ) ^ (epsilon + (1 - delta)) := by
        rw [← Real.rpow_add hpRealPos]
      _ = (4 * C) *
          (p : ℝ) ^ (1 - delta + epsilon) := by
        congr 2
        ring
  have hQuadrupleLinearReal :
      ((4 * (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card +
            (p + 1).divisors.card)) *
          currentOrder : ℕ) : ℝ) < (p : ℝ) := by
    calc
      ((4 * (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card +
            (p + 1).divisors.card)) *
          currentOrder : ℕ) : ℝ) =
          4 * (corvajaZannierCorollaryTwoSafeCoefficient *
            ((p - 1).divisors.card +
              (p + 1).divisors.card) : ℝ) *
              (currentOrder : ℝ) := by
        norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      _ ≤ 4 * (C * (p : ℝ) ^ epsilon) *
          (currentOrder : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hDivisor (by norm_num))
          hCurrentNonneg
      _ < 4 * (C * (p : ℝ) ^ epsilon) *
          (p : ℝ) ^ (1 - delta) := by
        exact mul_lt_mul_of_pos_left hUpper
          (mul_pos (by norm_num) (mul_pos hCPos
            (Real.rpow_pos_of_pos hpRealPos _)))
      _ = (4 * C) *
          (p : ℝ) ^ (1 - delta + epsilon) :=
        hQuadrupleLinearIdentity
      _ < (p : ℝ) ^ (1 : ℝ) := hLinearDominance
      _ = (p : ℝ) := by simp
  have hQuadrupleEnvelope :=
    scaled_divisorCount_mul_corvajaZannierEnvelope_lt_currentOrder
      4 p currentOrder hCurrentPos
        (by exact_mod_cast hQuadrupleCubeReal)
        (by exact_mod_cast hQuadrupleLinearReal)
  have horderForty : (40 : ℝ) < currentOrder :=
    hForty.trans hLower
  calc
    2 *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p currentOrder +
          20 =
        (4 *
              (((p - 1).divisors.card +
                (p + 1).divisors.card : ℕ) : ℝ) *
                corvajaZannierCurrentOrderEnvelope p currentOrder +
            40) / 2 := by
      ring
    _ <
        ((currentOrder : ℝ) + (currentOrder : ℝ)) / 2 := by
      exact div_lt_div_of_pos_right
        (add_lt_add hQuadrupleEnvelope horderForty) (by norm_num)
    _ = (currentOrder : ℝ) := by ring

/-- Closed-cutoff middle-range discharge at the exponent `1/32` used by the
general startup route. -/
theorem alternatingRegularMiddleGame_sizeBound_of_analyticCutoff
    {p currentOrder : ℕ} (hp : analyticCutoff ≤ p)
    (hLower : (p : ℝ) ^ (1 / 32 : ℝ) < currentOrder)
    (hUpper : (currentOrder : ℝ) < (p : ℝ) ^ (31 / 32 : ℝ)) :
    2 *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p currentOrder +
          20 <
        (currentOrder : ℝ) := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  have hpRealStrict : (1 : ℝ) < p := by
    exact_mod_cast analyticCutoff_gt_one.trans_le hp
  have hpRealPos : (0 : ℝ) < p := zero_lt_one.trans hpRealStrict
  have hdivisor :
      (T : ℝ) < (p : ℝ) ^ (1 / 256 : ℝ) :=
    divisor_sum_lt_rpow_one_div_twoHundredFiftySix hp
  have hfixedCube :
      (192 : ℝ) ^ 3 <
        (p : ℝ) ^ (1 / 256 : ℝ) := by
    have h :=
      small_fixed_lt_rpow_one_div_twoHundredFiftySix
        (p := p) (fixed := 192 ^ 3) hp (by norm_num)
    convert h using 1 ; norm_num
  have hcubeReal :
      ((4 * (corvajaZannierCorollaryTwoSafeCoefficient * T) : ℕ) : ℝ) ^ 3 <
        (currentOrder : ℝ) := by
    calc
      ((4 * (corvajaZannierCorollaryTwoSafeCoefficient * T) : ℕ) : ℝ) ^ 3 =
          (192 * (T : ℝ)) ^ 3 := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        norm_num [corvajaZannierCorollaryTwoSafeCoefficient]
        ring
      _ < (192 * (p : ℝ) ^ (1 / 256 : ℝ)) ^ 3 := by
        gcongr
      _ = (192 ^ 3 : ℝ) *
          (p : ℝ) ^ (3 / 256 : ℝ) := by
        rw [mul_pow,
          ← Real.rpow_mul_natCast
            (Nat.cast_nonneg p) (1 / 256 : ℝ) 3]
        norm_num
      _ < (p : ℝ) ^ (1 / 256 : ℝ) *
          (p : ℝ) ^ (3 / 256 : ℝ) :=
        mul_lt_mul_of_pos_right hfixedCube
          (Real.rpow_pos_of_pos hpRealPos _)
      _ = (p : ℝ) ^ (1 / 64 : ℝ) := by
        rw [← Real.rpow_add hpRealPos]
        congr 1
        norm_num
      _ < (p : ℝ) ^ (1 / 32 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt hpRealStrict
          (by norm_num)
      _ < (currentOrder : ℝ) := hLower
  have hfixedLinear :
      (192 : ℝ) < (p : ℝ) ^ (1 / 256 : ℝ) :=
    small_fixed_lt_rpow_one_div_twoHundredFiftySix hp
      (by norm_num)
  have hcurrentRealPositive : (0 : ℝ) < currentOrder :=
    (Real.rpow_pos_of_pos hpRealPos _).trans hLower
  have hlinearReal :
      ((4 * (corvajaZannierCorollaryTwoSafeCoefficient * T) *
        currentOrder : ℕ) : ℝ) < p := by
    have hnumeric :
        4 * (corvajaZannierCorollaryTwoSafeCoefficient * T) *
            currentOrder =
          192 * T * currentOrder := by
      norm_num only [corvajaZannierCorollaryTwoSafeCoefficient]
      ring
    calc
      ((4 * (corvajaZannierCorollaryTwoSafeCoefficient * T) *
          currentOrder : ℕ) : ℝ) =
          192 * (T : ℝ) * currentOrder := by
        exact_mod_cast hnumeric
      _ < 192 * (p : ℝ) ^ (1 / 256 : ℝ) *
          currentOrder := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left hdivisor (by norm_num))
          hcurrentRealPositive
      _ < 192 * (p : ℝ) ^ (1 / 256 : ℝ) *
          (p : ℝ) ^ (31 / 32 : ℝ) := by
        exact mul_lt_mul_of_pos_left hUpper
          (mul_pos (by norm_num)
            (Real.rpow_pos_of_pos hpRealPos _))
      _ < (p : ℝ) ^ (1 / 256 : ℝ) *
          (p : ℝ) ^ (1 / 256 : ℝ) *
            (p : ℝ) ^ (31 / 32 : ℝ) := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hfixedLinear
            (Real.rpow_pos_of_pos hpRealPos _))
          (Real.rpow_pos_of_pos hpRealPos _)
      _ = (p : ℝ) ^ (125 / 128 : ℝ) := by
        rw [← Real.rpow_add hpRealPos,
          ← Real.rpow_add hpRealPos]
        congr 1
        norm_num
      _ < (p : ℝ) := by
        have hexponent : (125 / 128 : ℝ) < 1 := by norm_num
        simpa only [Real.rpow_one] using
          Real.rpow_lt_rpow_of_exponent_lt hpRealStrict
            hexponent
  have hcurrentPositive : 0 < currentOrder := by
    exact_mod_cast hcurrentRealPositive
  have henvelope :=
    scaled_divisorCount_mul_corvajaZannierEnvelope_lt_currentOrder
      4 p currentOrder hcurrentPositive
        (by exact_mod_cast hcubeReal)
        (by exact_mod_cast hlinearReal)
  have henvelope' :
      4 * ((T : ℝ) *
          corvajaZannierCurrentOrderEnvelope p currentOrder) <
        (currentOrder : ℝ) := by
    simpa [T, mul_assoc] using henvelope
  have hforty :
      (40 : ℝ) < currentOrder := by
    calc
      (40 : ℝ) < (p : ℝ) ^ (1 / 256 : ℝ) :=
        small_fixed_lt_rpow_one_div_twoHundredFiftySix hp
          (by norm_num)
      _ < (p : ℝ) ^ (1 / 32 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt hpRealStrict
          (by norm_num)
      _ < currentOrder := hLower
  calc
    2 * (T : ℝ) *
          corvajaZannierCurrentOrderEnvelope p currentOrder + 20 =
        (4 * ((T : ℝ) *
          corvajaZannierCurrentOrderEnvelope p currentOrder) + 40) /
            2 := by
      ring
    _ < ((currentOrder : ℝ) + (currentOrder : ℝ)) / 2 := by
      exact div_lt_div_of_pos_right
        (add_lt_add henvelope' hforty) (by norm_num)
    _ = (currentOrder : ℝ) := by ring

/-- Pointwise closed-cutoff startup-to-endgame middle route. -/
theorem alternatingRegularMiddleGame_reaches_endgame_of_analyticCutoff
    {p : ℕ} (hp : analyticCutoff ≤ p) [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (start : AlternatingRegularState a)
    (hstartLower :
      (p : ℝ) ^ (1 / 32 : ℝ) <
        alternatingActualOrder start) :
    ∃ finish : AlternatingRegularState a,
      SameRotationComponent start.point finish.point ∧
        (p : ℝ) ^ (17 / 32 : ℝ) ≤
          alternatingActualOrder finish := by
  letI : Fintype (quadraticFiniteField p) := Fintype.ofFinite _
  have hpFive : 5 ≤ p := five_le_analyticCutoff.trans hp
  have hpTwo : p ≠ 2 := by omega
  have hpOne : (1 : ℝ) ≤ p := by
    exact_mod_cast (Fact.out : p.Prime).one_le
  have htargetUpper :
      (p : ℝ) ^ (17 / 32 : ℝ) ≤
        (p : ℝ) ^ (31 / 32 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hpOne
    norm_num
  let endgameReal : ℝ := (p : ℝ) ^ (17 / 32 : ℝ)
  let target : ℕ := Nat.ceil endgameReal
  obtain ⟨finish, hcomponent, htarget⟩ :=
    exists_sameRotationComponent_alternatingRegularState_reaches_threshold
      p hpTwo (1 / 32 : ℝ) (by norm_num) a hA1 hA2 start target
        (by
          intro current _ hcurrentTarget
          have hcurrentEndgame :
              (current : ℝ) < endgameReal := by
            exact Nat.lt_ceil.mp (by
              simpa [target] using hcurrentTarget)
          convert hcurrentEndgame using 1 ;
            norm_num [endgameReal])
        (by
          intro current hstartCurrent hcurrentTarget
          have hcurrentEndgame :
              (current : ℝ) < endgameReal := by
            exact Nat.lt_ceil.mp (by
              simpa [target] using hcurrentTarget)
          have hcurrentUpper :
              (current : ℝ) < (p : ℝ) ^ (31 / 32 : ℝ) :=
            hcurrentEndgame.trans_le
              (by simpa [endgameReal] using htargetUpper)
          have hstartCurrentReal :
              (alternatingActualOrder start : ℝ) ≤ current := by
            exact_mod_cast hstartCurrent
          have hcurrentLower :
              (p : ℝ) ^ (1 / 32 : ℝ) < current :=
            hstartLower.trans_le hstartCurrentReal
          exact
            alternatingRegularMiddleGame_sizeBound_of_analyticCutoff
              hp hcurrentLower hcurrentUpper)
  have hendgame :
      endgameReal ≤ (alternatingActualOrder finish : ℝ) := by
    exact Nat.ceil_le.mp (by simpa [target] using htarget)
  exact ⟨finish, hcomponent, by
    simpa [endgameReal] using hendgame⟩

/-- For every sufficiently large prime, the alternating regular middle game
reaches the endgame scale inside the rotation component of the same fixed
coefficient triple.

Unlike the symmetric iterator, the lower middle-range bound is not a
property of an unstructured point: it is carried by the initial
`AlternatingRegularState` and propagated from the monotonicity of its actual
order.  This is the second new bookkeeping point in the unequal-coefficient
threshold argument. -/
theorem exists_threshold_alternatingRegularMiddleGame_reaches_endgame
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaQuarter : delta ≤ (1 : ℝ) / 4) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
      ∀ (a : Coefficients (ZMod p)),
        a.a1 ^ 2 ≠ 4 →
        a.a2 ^ 2 ≠ 4 →
        ∀ start : AlternatingRegularState a,
          (p : ℝ) ^ delta < alternatingActualOrder start →
          ∃ finish : AlternatingRegularState a,
            SameRotationComponent start.point finish.point ∧
              (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
                alternatingActualOrder finish := by
  obtain ⟨sizeThreshold, hsizeThreshold⟩ :=
    eventually_atTop.mp
      (eventually_alternatingRegularMiddleGame_sizeBound hdelta)
  refine ⟨max sizeThreshold 3, ?_⟩
  intro p hp _ a hA1 hA2 start hstartLower
  letI : Fintype (quadraticFiniteField p) := Fintype.ofFinite _
  have hpSize : sizeThreshold ≤ p := (le_max_left _ _).trans hp
  have hpThree : 3 ≤ p := (le_max_right _ _).trans hp
  have hpTwo : p ≠ 2 := by omega
  have hsize := hsizeThreshold p hpSize
  have hpOne : (1 : ℝ) ≤ p := by
    exact_mod_cast (show 1 ≤ p by
      exact (Fact.out : p.Prime).one_le)
  have htargetUpper :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
        (p : ℝ) ^ (1 - delta) := by
    apply Real.rpow_le_rpow_of_exponent_le hpOne
    linarith
  let endgameReal : ℝ :=
    (p : ℝ) ^ ((1 : ℝ) / 2 + delta)
  let target : ℕ := Nat.ceil endgameReal
  obtain ⟨finish, hcomponent, htarget⟩ :=
    exists_sameRotationComponent_alternatingRegularState_reaches_threshold
      p hpTwo delta (by linarith) a hA1 hA2 start target
        (by
          intro current _ hcurrentTarget
          have hcurrentEndgame :
              (current : ℝ) < endgameReal := by
            exact Nat.lt_ceil.mp (by
              simpa [target] using hcurrentTarget)
          simpa [endgameReal] using hcurrentEndgame)
        (by
          intro current hstartCurrent hcurrentTarget
          have hcurrentEndgame :
              (current : ℝ) < endgameReal := by
            exact Nat.lt_ceil.mp (by
              simpa [target] using hcurrentTarget)
          have hcurrentUpper :
              (current : ℝ) < (p : ℝ) ^ (1 - delta) := by
            exact hcurrentEndgame.trans_le (by
              simpa [endgameReal] using htargetUpper)
          have hstartCurrentReal :
              (alternatingActualOrder start : ℝ) ≤ current := by
            exact_mod_cast hstartCurrent
          have hcurrentLower :
              (p : ℝ) ^ delta < current :=
            hstartLower.trans_le hstartCurrentReal
          exact hsize current hcurrentLower hcurrentUpper)
  have hendgame :
      endgameReal ≤ (alternatingActualOrder finish : ℝ) := by
    exact Nat.ceil_le.mp (by simpa [target] using htarget)
  exact ⟨finish, hcomponent, by
    simpa [endgameReal] using hendgame⟩

end

end GenMarkoff.General.Assembly
