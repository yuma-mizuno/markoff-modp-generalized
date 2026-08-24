import GenMarkoff.General.Assembly.SmallOrderCount
import GenMarkoff.Assembly.EventualStrongApproximation
import BGS.Markoff.Assembly.GiantOrbit

/-!
# Uniform startup from rotation-orbit divisibility

For the fixed exponent `1 / 8`, the set on which both of the first two
actual rotation linear orders are below

`Nat.ceil ((p : ℝ) ^ (1 / 8 : ℝ))`

has cardinality `O(p^(1 / 2 + o(1)))`, hence eventually has fewer than `p`
points.  Eventual divisibility makes every nonempty punctured rotation orbit
have at least `p` points, so every such orbit escapes this small-order set.

The new general-coefficient consideration is that the small-order count from
`SmallOrderCount` uses the doubled half-step cutoff.  Its resulting quartic
bound is still harmless precisely because `4 * (1 / 8) < 1`.
-/

namespace GenMarkoff.General.Assembly

open BGS.Markoff Filter

noncomputable section

/-- The fixed power exponent used by the general startup argument. -/
def startupExponent : ℝ := 1 / 8

theorem startupExponent_pos : 0 < startupExponent := by
  norm_num [startupExponent]

theorem startupExponent_lt_one_fourth :
    startupExponent < (1 : ℝ) / 4 := by
  norm_num [startupExponent]

/-- The quartic numerical bound supplied by the general small-order count
is eventually strictly smaller than `p` at exponent `1 / 8`. -/
theorem eventually_startupSmallOrderCountBound_lt_prime :
    ∀ᶠ p : ℕ in atTop,
      2 *
          (2 + 2 *
            (2 * Nat.ceil ((p : ℝ) ^ startupExponent)) ^ 2) ^ 2 <
        p := by
  let θ : ℝ := 3 / 16
  have hExponentLt : startupExponent < θ := by
    norm_num [startupExponent, θ]
  have hThetaPos : 0 < θ := startupExponent_pos.trans hExponentLt
  have hThreeFourthsLtOne : (3 : ℝ) / 4 < 1 := by
    norm_num
  have hceilBuffered :
      ∀ᶠ p : ℕ in atTop,
        (((Nat.ceil ((p : ℝ) ^ startupExponent) + 1 : ℕ) : ℝ) ≤
          (p : ℝ) ^ θ) :=
    eventually_natCeil_rpow_add_one_le_rpow
      startupExponent_pos hExponentLt
  have hdominance :
      ∀ᶠ p : ℕ in atTop,
        (200 : ℝ) * (p : ℝ) ^ ((3 : ℝ) / 4) <
          (p : ℝ) ^ (1 : ℝ) :=
    eventually_const_mul_rpow_lt_rpow
      (C := (200 : ℝ)) (a := (3 : ℝ) / 4) (b := 1)
        hThreeFourthsLtOne
  filter_upwards [hceilBuffered, hdominance, eventually_ge_atTop 1] with
      p hceilBuffer hdominanceP hpOne
  let B : ℕ := Nat.ceil ((p : ℝ) ^ startupExponent)
  have hpRealOne : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hpOne
  have hpowOne : (1 : ℝ) ≤ (p : ℝ) ^ θ :=
    Real.one_le_rpow hpRealOne hThetaPos.le
  have hB :
      (B : ℝ) ≤ (p : ℝ) ^ θ := by
    calc
      (B : ℝ) ≤ ((B + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.le_add_right B 1)
      _ ≤ (p : ℝ) ^ θ := by
        simpa [B] using hceilBuffer
  have hBSq :
      (B : ℝ) ^ 2 ≤ ((p : ℝ) ^ θ) ^ 2 := by
    gcongr
  have hpowSqOne :
      (1 : ℝ) ≤ ((p : ℝ) ^ θ) ^ 2 := by
    nlinarith [sq_nonneg ((p : ℝ) ^ θ - 1)]
  have hinner :
      (2 : ℝ) + 2 * (2 * (B : ℝ)) ^ 2 ≤
        10 * ((p : ℝ) ^ θ) ^ 2 := by
    calc
      (2 : ℝ) + 2 * (2 * (B : ℝ)) ^ 2 =
          2 + 8 * (B : ℝ) ^ 2 := by ring
      _ ≤ 2 + 8 * ((p : ℝ) ^ θ) ^ 2 := by
        gcongr
      _ ≤ 2 * ((p : ℝ) ^ θ) ^ 2 +
          8 * ((p : ℝ) ^ θ) ^ 2 := by
        nlinarith
      _ = 10 * ((p : ℝ) ^ θ) ^ 2 := by ring
  have hcountReal :
      ((2 *
          (2 + 2 * (2 * B) ^ 2) ^ 2 : ℕ) : ℝ) ≤
        200 * (p : ℝ) ^ ((3 : ℝ) / 4) := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow]
    calc
      (2 : ℝ) *
          ((2 : ℝ) + 2 * (2 * (B : ℝ)) ^ 2) ^ 2 ≤
          2 * (10 * ((p : ℝ) ^ θ) ^ 2) ^ 2 := by
        gcongr
      _ = 200 * (((p : ℝ) ^ θ) ^ 4) := by ring
      _ = 200 * (p : ℝ) ^ (θ * (4 : ℕ)) := by
        rw [Real.rpow_mul_natCast (Nat.cast_nonneg p) θ 4]
      _ = 200 * (p : ℝ) ^ ((3 : ℝ) / 4) := by
        norm_num [θ]
  have hcountRealLt :
      ((2 *
          (2 + 2 * (2 * B) ^ 2) ^ 2 : ℕ) : ℝ) < (p : ℝ) := by
    exact hcountReal.trans_lt <| by
      simpa only [Real.rpow_one] using hdominanceP
  change 2 * (2 + 2 * (2 * B) ^ 2) ^ 2 < p
  exact_mod_cast hcountRealLt

/-- Threshold form of the explicit quartic startup estimate. -/
theorem exists_threshold_startupSmallOrderCountBound_lt_prime :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      2 *
          (2 + 2 *
            (2 * Nat.ceil ((p : ℝ) ^ startupExponent)) ^ 2) ^ 2 <
        p :=
  eventually_atTop.mp eventually_startupSmallOrderCountBound_lt_prime

/-- For a fixed integrally nondegenerate integral coefficient triple, every
punctured rotation orbit modulo every sufficiently large prime contains a
point at which the first or second actual rotation linear order is at least
`ceil(p^(1/8))`. -/
theorem IntegrallyNondegenerate.exists_threshold_every_rotationOrbit_has_large_order
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a) :
    ∃ threshold : ℕ,
      ∀ (p : ℕ) (_hp : p.Prime), threshold ≤ p →
        ∀ x : PuncturedSolutionSurface (modCoefficients a p),
          ∃ y : PuncturedSolutionSurface (modCoefficients a p),
            y ∈ puncturedRotationOrbit x ∧
              (Nat.ceil ((p : ℝ) ^ startupExponent) ≤
                  rotationLinearOrder
                    (orderedTrace (modCoefficients a p).multiplier
                      (modCoefficients a p).a1 y.1.1.x1) ∨
                Nat.ceil ((p : ℝ) ^ startupExponent) ≤
                  rotationLinearOrder
                    (orderedTrace (modCoefficients a p).multiplier
                      (modCoefficients a p).a2 y.1.1.x2)) := by
  obtain ⟨divisibilityThreshold, hdivisibility⟩ :=
    ha.eventually_rotationOrbitDivisibility
  obtain ⟨countThreshold, hcount⟩ :=
    exists_threshold_startupSmallOrderCountBound_lt_prime
  refine
    ⟨max (max divisibilityThreshold (genericAdmissibilityCutoff a))
        (max countThreshold 5), ?_⟩
  intro p hp hpLarge x
  letI : Fact p.Prime := ⟨hp⟩
  have hpDivisibility : divisibilityThreshold ≤ p :=
    (Nat.le_max_left divisibilityThreshold
      (genericAdmissibilityCutoff a)).trans <|
        (Nat.le_max_left
          (max divisibilityThreshold (genericAdmissibilityCutoff a))
          (max countThreshold 5)).trans hpLarge
  have hpGeneric : genericAdmissibilityCutoff a ≤ p :=
    (Nat.le_max_right divisibilityThreshold
      (genericAdmissibilityCutoff a)).trans <|
        (Nat.le_max_left
          (max divisibilityThreshold (genericAdmissibilityCutoff a))
          (max countThreshold 5)).trans hpLarge
  have hpCount : countThreshold ≤ p :=
    (Nat.le_max_left countThreshold 5).trans <|
      (Nat.le_max_right
        (max divisibilityThreshold (genericAdmissibilityCutoff a))
        (max countThreshold 5)).trans hpLarge
  have hpFive : 5 ≤ p :=
    (Nat.le_max_right countThreshold 5).trans <|
      (Nat.le_max_right
        (max divisibilityThreshold (genericAdmissibilityCutoff a))
        (max countThreshold 5)).trans hpLarge
  have hpTwo : p ≠ 2 := by omega
  have hgeneric :
      GenericAdmissible (modCoefficients a p) :=
    ha.genericAdmissibleAt_of_cutoff_le hpGeneric
  let bound : ℕ := Nat.ceil ((p : ℝ) ^ startupExponent)
  have hsmallCard :
      (pointsWithSmallFirstTwoRotationLinearOrders
          p (modCoefficients a p) bound).card < p := by
    refine
      (pointsWithSmallFirstTwoRotationLinearOrders_card_le
        p hpTwo (modCoefficients a p) hgeneric.1 bound).trans_lt ?_
    simpa [bound] using hcount p hpCount
  have hdiv :
      p ∣ (puncturedRotationOrbit x).ncard := by
    exact hdivisibility p hp hpDivisibility x
  simpa [bound, coordinateTrace1, coordinateTrace2, orderedTrace] using
    (exists_mem_rotationOrbit_with_large_first_or_second_rotationLinearOrder_of_dvd
      p (modCoefficients a p) bound x hdiv hsmallCard)

end

end GenMarkoff.General.Assembly
