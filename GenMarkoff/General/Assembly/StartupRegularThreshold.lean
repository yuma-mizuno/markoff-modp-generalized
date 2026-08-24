import GenMarkoff.General.Assembly.StartupRegularRouting

/-!
# Uniform power threshold for general startup routing

The quantitative startup route discards

`20 + 2 * (2 + 2 * (2 * bound) ^ 2)`

points from a first- or second-axis point cycle.  This module chooses the
strict buffered target

`bound = Nat.ceil (p ^ (1 / 32)) + 1`

and proves that its discard cost is eventually smaller than both the incoming
startup scale `Nat.ceil (p ^ (1 / 8))` and the signed parabolic period `p`.

## New consideration in the unequal-coefficient case

The ordered safe-polynomial support contributes twenty points, and passage
from actual rotation order to the common BGS half-step doubles the trace
cutoff.  Consequently the real cost is bounded by
`24 + 16 * bound ^ 2`, rather than the symmetric cost.  The exponent
condition is still quadratic: `2 * (1 / 32) < 1 / 8`.

The extra `+ 1` in the target is retained through the proof so the final
state satisfies the strict real lower bound
`p ^ (1 / 32) < alternatingActualOrder`.
-/

namespace GenMarkoff.General.Assembly

open Filter BGS.Markoff
open GenMarkoff.General.Explicit

noncomputable section

/-- Fixed outgoing exponent for the startup-to-middle-game interface. -/
def startupRegularExponent : ℝ := 1 / 32

theorem startupRegularExponent_pos :
    0 < startupRegularExponent := by
  norm_num [startupRegularExponent]

theorem two_mul_startupRegularExponent_lt_startupExponent :
    2 * startupRegularExponent < startupExponent := by
  norm_num [startupRegularExponent, startupExponent]

/-- The strict integral target used for the initial regular state. -/
def startupRegularBound (p : ℕ) : ℕ :=
  Nat.ceil ((p : ℝ) ^ startupRegularExponent) + 1

/-- The ordered-unsafe plus low-actual-order discard cost. -/
def startupRegularRoutingCost (bound : ℕ) : ℕ :=
  20 + 2 * (2 + 2 * (2 * bound) ^ 2)

theorem rpow_startupRegularExponent_lt_startupRegularBound
    (p : ℕ) :
    (p : ℝ) ^ startupRegularExponent <
      (startupRegularBound p : ℝ) := by
  rw [startupRegularBound]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hceil :
      (p : ℝ) ^ startupRegularExponent ≤
        (Nat.ceil ((p : ℝ) ^ startupRegularExponent) : ℝ) :=
    Nat.le_ceil ((p : ℝ) ^ startupRegularExponent)
  linarith

/-- A buffered outgoing cutoff is eventually bounded by every strictly
larger real power. -/
theorem eventually_startupRegularBound_cast_le_rpow
    {delta theta : ℝ} (hdelta : 0 < delta)
    (hdeltaTheta : delta < theta) :
    ∀ᶠ p : ℕ in atTop,
      ((Nat.ceil ((p : ℝ) ^ delta) + 1 : ℕ) : ℝ) ≤
        (p : ℝ) ^ theta :=
  eventually_natCeil_rpow_add_one_le_rpow hdelta hdeltaTheta

/-- If `2 * delta < eta < 1`, the general ordered startup discard cost for
the buffered `delta` target is eventually smaller than both the incoming
`eta` cutoff and the signed parabolic period `p`. -/
theorem eventually_startupRegularRoutingCost_lt_powerBounds
    {delta eta : ℝ} (hdelta : 0 < delta)
    (htwoDelta : 2 * delta < eta) (heta : eta < 1) :
    ∀ᶠ p : ℕ in atTop,
      startupRegularRoutingCost
          (Nat.ceil ((p : ℝ) ^ delta) + 1) <
            Nat.ceil ((p : ℝ) ^ eta) ∧
        startupRegularRoutingCost
          (Nat.ceil ((p : ℝ) ^ delta) + 1) < p := by
  let theta : ℝ := (delta + eta / 2) / 2
  have hdeltaTheta : delta < theta := by
    dsimp [theta]
    linarith
  have htwoThetaEta : 2 * theta < eta := by
    dsimp [theta]
    linarith
  have htwoThetaOne : 2 * theta < 1 :=
    htwoThetaEta.trans heta
  have hthetaPos : 0 < theta := hdelta.trans hdeltaTheta
  have hboundEventually :
      ∀ᶠ p : ℕ in atTop,
        ((Nat.ceil ((p : ℝ) ^ delta) + 1 : ℕ) : ℝ) ≤
          (p : ℝ) ^ theta :=
    eventually_startupRegularBound_cast_le_rpow
      hdelta hdeltaTheta
  have hcostEta :
      ∀ᶠ p : ℕ in atTop,
        (40 : ℝ) * (p : ℝ) ^ (2 * theta) <
          (p : ℝ) ^ eta :=
    eventually_const_mul_rpow_lt_rpow
      (C := (40 : ℝ)) (a := 2 * theta) (b := eta)
        htwoThetaEta
  have hcostOne :
      ∀ᶠ p : ℕ in atTop,
        (40 : ℝ) * (p : ℝ) ^ (2 * theta) <
          (p : ℝ) ^ (1 : ℝ) :=
    eventually_const_mul_rpow_lt_rpow
      (C := (40 : ℝ)) (a := 2 * theta) (b := 1)
        htwoThetaOne
  filter_upwards [hboundEventually, hcostEta, hcostOne,
    eventually_ge_atTop 1] with p hbound hEta hOne hpOne
  let B : ℕ := Nat.ceil ((p : ℝ) ^ delta) + 1
  have hpRealOne : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hpOne
  have hpPowOne : (1 : ℝ) ≤ (p : ℝ) ^ (2 * theta) :=
    Real.one_le_rpow hpRealOne (by linarith)
  have hBSq :
      (((B ^ 2 : ℕ) : ℝ) : ℝ) ≤
        (p : ℝ) ^ (2 * theta) := by
    norm_num only [Nat.cast_pow]
    calc
      (B : ℝ) ^ 2 ≤ ((p : ℝ) ^ theta) ^ 2 := by
        gcongr
      _ = (p : ℝ) ^ (theta * (2 : ℕ)) :=
        (Real.rpow_mul_natCast (Nat.cast_nonneg p) theta 2).symm
      _ = (p : ℝ) ^ (2 * theta) := by ring_nf
  have hcost :
      ((startupRegularRoutingCost B : ℕ) : ℝ) ≤
        40 * (p : ℝ) ^ (2 * theta) := by
    rw [startupRegularRoutingCost]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    calc
      (20 : ℝ) + 2 * (2 + 2 * (2 * (B : ℝ)) ^ 2) =
          24 + 16 * (B : ℝ) ^ 2 := by ring
      _ ≤ 24 + 16 * (p : ℝ) ^ (2 * theta) := by
        gcongr
        simpa using hBSq
      _ ≤ 24 * (p : ℝ) ^ (2 * theta) +
          16 * (p : ℝ) ^ (2 * theta) := by
        nlinarith
      _ = 40 * (p : ℝ) ^ (2 * theta) := by ring
  have hpowEtaLeCeil :
      (p : ℝ) ^ eta ≤
        (Nat.ceil ((p : ℝ) ^ eta) : ℝ) :=
    Nat.le_ceil ((p : ℝ) ^ eta)
  constructor
  · exact_mod_cast hcost.trans_lt (hEta.trans_le hpowEtaLeCeil)
  · have hOne' :
        40 * (p : ℝ) ^ (2 * theta) < (p : ℝ) := by
      simpa only [Real.rpow_one] using hOne
    exact_mod_cast hcost.trans_lt hOne'

theorem eventually_startupRegularRoutingCost_lt_startupBounds :
    ∀ᶠ p : ℕ in atTop,
      startupRegularRoutingCost (startupRegularBound p) <
          Nat.ceil ((p : ℝ) ^ startupExponent) ∧
        startupRegularRoutingCost (startupRegularBound p) < p := by
  simpa [startupRegularBound] using
    (eventually_startupRegularRoutingCost_lt_powerBounds
      startupRegularExponent_pos
      two_mul_startupRegularExponent_lt_startupExponent
      (by norm_num [startupExponent]))

/-- Closed-cutoff form of the buffered startup routing inequalities. -/
theorem startupRegularRoutingCost_lt_startupBounds_of_analyticCutoff
    {p : ℕ} (hp : analyticCutoff ≤ p) :
    startupRegularRoutingCost (startupRegularBound p) <
          Nat.ceil ((p : ℝ) ^ startupExponent) ∧
        startupRegularRoutingCost (startupRegularBound p) < p := by
  let X : ℝ := (p : ℝ) ^ startupRegularExponent
  let B := startupRegularBound p
  have hpOne : 1 ≤ p :=
    (analyticCutoff_gt_one.trans_le hp).le
  have hpRealOne : (1 : ℝ) ≤ p := by exact_mod_cast hpOne
  have hpRealStrict : (1 : ℝ) < p := by
    exact_mod_cast analyticCutoff_gt_one.trans_le hp
  have hpRealPos : (0 : ℝ) < p := zero_lt_one.trans hpRealStrict
  have hXOne : (1 : ℝ) ≤ X := by
    exact Real.one_le_rpow hpRealOne
      (by
        norm_num [startupRegularExponent] :
          (0 : ℝ) ≤ startupRegularExponent)
  have hceil :
      (Nat.ceil ((p : ℝ) ^ startupRegularExponent) : ℝ) ≤
        2 * X := by
    simpa [X] using
      natCeil_rpow_le_two_mul hpOne
        (by norm_num [startupRegularExponent])
  have hB : (B : ℝ) ≤ 3 * X := by
    dsimp [B, startupRegularBound]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hXsqOne : (1 : ℝ) ≤ X ^ 2 := by
    nlinarith [sq_nonneg (X - 1)]
  have hcost :
      (startupRegularRoutingCost B : ℝ) ≤
        168 * (p : ℝ) ^ (1 / 16 : ℝ) := by
    rw [startupRegularRoutingCost]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_pow]
    calc
      (20 : ℝ) + 2 * (2 + 2 * (2 * (B : ℝ)) ^ 2) =
          24 + 16 * (B : ℝ) ^ 2 := by ring
      _ ≤ 24 * X ^ 2 + 16 * (3 * X) ^ 2 := by
        apply add_le_add
        · simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hXsqOne
              (by norm_num : (0 : ℝ) ≤ 24)
        · gcongr
      _ = 168 * X ^ 2 := by ring
      _ = 168 * (p : ℝ) ^ (1 / 16 : ℝ) := by
        dsimp [X]
        rw [← Real.rpow_mul_natCast
          (Nat.cast_nonneg p) startupRegularExponent 2]
        norm_num [startupRegularExponent]
  have hfixed :
      (168 : ℝ) < (p : ℝ) ^ (1 / 256 : ℝ) :=
    small_fixed_lt_rpow_one_div_twoHundredFiftySix
      hp (by norm_num)
  have hcostPower :
      (startupRegularRoutingCost B : ℝ) <
        (p : ℝ) ^ (17 / 256 : ℝ) := by
    calc
      (startupRegularRoutingCost B : ℝ) ≤
          168 * (p : ℝ) ^ (1 / 16 : ℝ) := hcost
      _ < (p : ℝ) ^ (1 / 256 : ℝ) *
          (p : ℝ) ^ (1 / 16 : ℝ) :=
        mul_lt_mul_of_pos_right hfixed
          (Real.rpow_pos_of_pos hpRealPos _)
      _ = (p : ℝ) ^ (17 / 256 : ℝ) := by
        rw [← Real.rpow_add hpRealPos]
        congr 1
        norm_num
  have hcostStartup :
      (startupRegularRoutingCost B : ℝ) <
        (p : ℝ) ^ startupExponent :=
    hcostPower.trans
      (Real.rpow_lt_rpow_of_exponent_lt hpRealStrict
        (by norm_num [startupExponent]))
  have hcostPrime :
      (startupRegularRoutingCost B : ℝ) < p :=
    hcostPower.trans
      (by
        have hexponent : (17 / 256 : ℝ) < 1 := by norm_num
        simpa only [Real.rpow_one] using
          Real.rpow_lt_rpow_of_exponent_lt hpRealStrict
            hexponent)
  constructor
  · exact_mod_cast hcostStartup.trans_le
      (Nat.le_ceil ((p : ℝ) ^ startupExponent))
  · exact_mod_cast hcostPrime

theorem exists_threshold_startupRegularRoutingCost_lt_startupBounds :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      startupRegularRoutingCost (startupRegularBound p) <
          Nat.ceil ((p : ℝ) ^ startupExponent) ∧
        startupRegularRoutingCost (startupRegularBound p) < p :=
  ⟨analyticCutoff,
    fun _p hp =>
      startupRegularRoutingCost_lt_startupBounds_of_analyticCutoff hp⟩

theorem
    IntegrallyNondegenerate.exists_threshold_every_rotationOrbit_has_powerLowerBound_alternatingRegularState
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a) :
    ∃ threshold : ℕ,
      ∀ (p : ℕ) (hp : p.Prime), threshold ≤ p →
        letI : Fact p.Prime := ⟨hp⟩
        ∀ x : PuncturedSolutionSurface (modCoefficients a p),
          ∃ state : AlternatingRegularState (modCoefficients a p),
            SameRotationComponent x.1 state.point ∧
              (p : ℝ) ^ startupRegularExponent <
                (alternatingActualOrder state : ℝ) := by
  obtain ⟨startupThreshold, hstartup⟩ :=
    IntegrallyNondegenerate.exists_threshold_every_rotationOrbit_has_alternatingRegularState
      ha
  obtain ⟨costThreshold, hcost⟩ :=
    exists_threshold_startupRegularRoutingCost_lt_startupBounds
  refine ⟨max startupThreshold costThreshold, ?_⟩
  intro p hp hpLarge x
  letI : Fact p.Prime := ⟨hp⟩
  have hpStartup : startupThreshold ≤ p :=
    (Nat.le_max_left _ _).trans hpLarge
  have hpCost : costThreshold ≤ p :=
    (Nat.le_max_right _ _).trans hpLarge
  have hcostP := hcost p hpCost
  obtain ⟨state, hcomponent, horder⟩ :=
    hstartup p hp hpStartup x (startupRegularBound p)
      (by
        simpa [startupRegularRoutingCost] using hcostP.1)
      (by
        simpa [startupRegularRoutingCost] using hcostP.2)
  refine ⟨state, hcomponent, ?_⟩
  have hboundReal :
      (startupRegularBound p : ℝ) ≤
        (alternatingActualOrder state : ℝ) := by
    exact_mod_cast horder
  exact
    (rpow_startupRegularExponent_lt_startupRegularBound p).trans_le
      hboundReal

/-- Pointwise power-lower-bound startup with the universal analytic and
coefficient-height cutoffs separated. -/
theorem
    IntegrallyNondegenerate.every_rotationOrbit_has_powerLowerBound_alternatingRegularState_of_explicitCutoffs
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (p : ℕ) (hp : p.Prime)
    (hpAnalytic : analyticCutoff ≤ p)
    (hpGeneric : genericAdmissibilityCutoff a ≤ p)
    (x : PuncturedSolutionSurface (modCoefficients a p)) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ state : AlternatingRegularState (modCoefficients a p),
      SameRotationComponent x.1 state.point ∧
        (p : ℝ) ^ startupRegularExponent <
          (alternatingActualOrder state : ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hcost :=
    startupRegularRoutingCost_lt_startupBounds_of_analyticCutoff hpAnalytic
  obtain ⟨state, hcomponent, horder⟩ :=
    IntegrallyNondegenerate.every_rotationOrbit_has_alternatingRegularState_of_explicitCutoffs
      ha p hp hpAnalytic hpGeneric x (startupRegularBound p)
      (by simpa [startupRegularRoutingCost] using hcost.1)
      (by simpa [startupRegularRoutingCost] using hcost.2)
  refine ⟨state, hcomponent, ?_⟩
  have hboundReal :
      (startupRegularBound p : ℝ) ≤
        (alternatingActualOrder state : ℝ) := by
    exact_mod_cast horder
  exact
    (rpow_startupRegularExponent_lt_startupRegularBound p).trans_le
      hboundReal

end

end GenMarkoff.General.Assembly
