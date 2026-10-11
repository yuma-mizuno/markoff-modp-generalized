module

public import GenMarkoff.General.Assembly.CoarseRegularStartup
public import GenMarkoff.General.Assembly.RegularMiddleThreshold

@[expose] public section

/-!
# Middle game from the coarse threshold to `p ^ (3/4)`

Write `T = #divisors (p - 1) + #divisors (p + 1)`.  The coarse startup
produces an alternating regular state of actual order above `(192 T)^3`
(`coarseRegularBound`), and beyond `reasonableAnalyticCutoff` one has
`192 T < p ^ (1/4)`.  This module checks the regular-escape margin of the
middle game on the whole range from `(192 T)^3` to `p ^ (3/4)` and concludes
that the strict regular iteration reaches actual order at least `p ^ (3/4)`,
the scale used by the split and nonsplit endgames.
-/

namespace GenMarkoff.General.Assembly

open BGS.Markoff
open GenMarkoff.General.Explicit

noncomputable section

/-- Beyond `reasonableAnalyticCutoff`, every actual order between
`coarseRegularBound p` and `p ^ (3/4)` satisfies the regular-escape margin
`2 T E + 20 < currentOrder` of the middle game, where `E` is
`corvajaZannierCurrentOrderEnvelope p currentOrder`. -/
theorem alternatingRegularMiddleGame_sizeBound_of_reasonableCutoff
    {p currentOrder : ℕ} (hp : reasonableAnalyticCutoff ≤ p)
    (hLower : coarseRegularBound p ≤ currentOrder)
    (hUpper : (currentOrder : ℝ) < (p : ℝ) ^ (3 / 4 : ℝ)) :
    2 *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p currentOrder +
          20 <
        (currentOrder : ℝ) := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  have hpOne : (1 : ℝ) < p := by
    exact_mod_cast reasonableAnalyticCutoff_gt_one.trans_le hp
  have hpPos : (0 : ℝ) < p := zero_lt_one.trans hpOne
  -- Cube estimate `(192 T)^3 < currentOrder` from the lower bound.
  have hcube :
      (4 * (corvajaZannierCorollaryTwoSafeCoefficient * T)) ^ 3 <
        currentOrder := by
    have hbase :
        (4 * (corvajaZannierCorollaryTwoSafeCoefficient * T)) ^ 3 =
          (192 * T) ^ 3 := by
      norm_num [corvajaZannierCorollaryTwoSafeCoefficient]
      ring
    rw [hbase]
    exact (corvajaZannierCube_lt_coarseRegularBound p).trans_le hLower
  -- Linear estimate `192 T * currentOrder < p`, from `192 T < p ^ (1/4)`
  -- and `currentOrder < p ^ (3/4)`.
  have hcoefficient :
      ((192 * T : ℕ) : ℝ) < (p : ℝ) ^ (1 / 4 : ℝ) := by
    simpa [T] using
      reasonable_middleGame_divisor_term_lt_rpow_one_div_four hp
  have hcurrentPositive : (0 : ℝ) < currentOrder := by
    have hcubeNonnegative :
        0 ≤ (4 * (corvajaZannierCorollaryTwoSafeCoefficient * T)) ^ 3 :=
      Nat.zero_le _
    exact_mod_cast hcubeNonnegative.trans_lt hcube
  have hlinearReal :
      ((4 * (corvajaZannierCorollaryTwoSafeCoefficient * T) *
        currentOrder : ℕ) : ℝ) < p := by
    calc
      ((4 * (corvajaZannierCorollaryTwoSafeCoefficient * T) *
          currentOrder : ℕ) : ℝ) =
          (192 * T : ℕ) * currentOrder := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        rw [show corvajaZannierCorollaryTwoSafeCoefficient = 48 by
          norm_num [corvajaZannierCorollaryTwoSafeCoefficient]]
        ring
      _ < (p : ℝ) ^ (1 / 4 : ℝ) * currentOrder :=
        mul_lt_mul_of_pos_right hcoefficient hcurrentPositive
      _ < (p : ℝ) ^ (1 / 4 : ℝ) *
          (p : ℝ) ^ (3 / 4 : ℝ) :=
        mul_lt_mul_of_pos_left hUpper
          (Real.rpow_pos_of_pos hpPos _)
      _ = p := by
        rw [← Real.rpow_add hpPos]
        norm_num
  have hcurrentPositiveNat : 0 < currentOrder := by
    exact_mod_cast hcurrentPositive
  -- The scale-four envelope bound `4 T E < currentOrder`, together with
  -- `40 < currentOrder`, gives the margin `2 T E + 20 < currentOrder`.
  have henvelope :=
    scaled_divisorCount_mul_corvajaZannierEnvelope_lt_currentOrder
      4 p currentOrder hcurrentPositiveNat hcube
        (by exact_mod_cast hlinearReal)
  have henvelope' :
      4 * ((T : ℝ) *
          corvajaZannierCurrentOrderEnvelope p currentOrder) <
        (currentOrder : ℝ) := by
    simpa [T, mul_assoc] using henvelope
  have hTOne : 1 ≤ T := by
    have hpPlus : p + 1 ≠ 0 := by omega
    have hone : 1 ∈ (p + 1).divisors :=
      Nat.one_mem_divisors.mpr hpPlus
    have hcard : 1 ≤ (p + 1).divisors.card :=
      Finset.one_le_card.mpr ⟨1, hone⟩
    dsimp [T]
    omega
  have hforty : (40 : ℝ) < currentOrder := by
    have hnumeric : 40 < (192 * T) ^ 3 + 1 := by
      calc
        40 < 192 ^ 3 := by norm_num
        _ ≤ (192 * T) ^ 3 := by
          gcongr
          nlinarith
        _ < (192 * T) ^ 3 + 1 := by omega
    exact_mod_cast hnumeric.trans_le hLower
  calc
    2 * (T : ℝ) *
          corvajaZannierCurrentOrderEnvelope p currentOrder + 20 =
        (4 * ((T : ℝ) *
          corvajaZannierCurrentOrderEnvelope p currentOrder) + 40) /
            2 := by ring
    _ < ((currentOrder : ℝ) + currentOrder) / 2 := by
      exact div_lt_div_of_pos_right
        (add_lt_add henvelope' hforty) (by norm_num)
    _ = currentOrder := by ring

/-- Beyond `reasonableAnalyticCutoff`, an alternating regular state of
actual order at least `coarseRegularBound p` reaches, in its rotation
component, an alternating regular state of actual order at least
`p ^ (3/4)`. -/
theorem alternatingRegularMiddleGame_reaches_threeQuarter_of_reasonableCutoff
    {p : ℕ} (hp : reasonableAnalyticCutoff ≤ p) [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (start : AlternatingRegularState a)
    (hstartLower : coarseRegularBound p ≤ alternatingActualOrder start) :
    ∃ finish : AlternatingRegularState a,
      SameRotationComponent start.point finish.point ∧
        (p : ℝ) ^ (3 / 4 : ℝ) ≤
          alternatingActualOrder finish := by
  letI : Fintype (quadraticFiniteField p) := Fintype.ofFinite _
  have hpTwo : p ≠ 2 := by
    have := five_le_reasonableAnalyticCutoff.trans hp
    omega
  let endgameReal : ℝ := (p : ℝ) ^ (3 / 4 : ℝ)
  let target : ℕ := Nat.ceil endgameReal
  obtain ⟨finish, hcomponent, htarget⟩ :=
    exists_sameRotationComponent_alternatingRegularState_reaches_threshold
      p hpTwo (1 / 4 : ℝ) (by norm_num) a hA1 hA2 start target
        (by
          intro current _ hcurrentTarget
          have hcurrentEndgame :
              (current : ℝ) < endgameReal := by
            exact Nat.lt_ceil.mp (by
              simpa [target] using hcurrentTarget)
          convert hcurrentEndgame using 1 ; norm_num [endgameReal])
        (by
          intro current hstartCurrent hcurrentTarget
          have hcurrentEndgame :
              (current : ℝ) < endgameReal := by
            exact Nat.lt_ceil.mp (by
              simpa [target] using hcurrentTarget)
          apply alternatingRegularMiddleGame_sizeBound_of_reasonableCutoff hp
          · exact hstartLower.trans hstartCurrent
          · simpa [endgameReal] using hcurrentEndgame)
  have hendgame :
      endgameReal ≤ (alternatingActualOrder finish : ℝ) := by
    exact Nat.ceil_le.mp (by simpa [target] using htarget)
  exact ⟨finish, hcomponent, by
    simpa [endgameReal] using hendgame⟩

end

end GenMarkoff.General.Assembly
