module

public import GenMarkoff.ShiftedTrace.MiddleGame.ShiftedTraceEquation
public import GenMarkoff.TraceCurve.ShiftedCover.AbsoluteIrreducibility
public import BGS.Markoff.MiddleGame.CorvajaZannierFromGeneral

@[expose] public section

/-!
# The shifted trace curve is not a subtorus translate

For `sigma ≠ 0`, the normalized shifted trace curve

`h + sigma * h⁻¹ + gamma = k + k⁻¹`

over the algebraic closure is not contained in any translate `k ^ a * h ^ b = c`
of a proper subtorus (`shiftedWeightedTraceCurve_notSubtorusTranslate`).  This
is the non-specialness hypothesis of the general Corvaja--Zannier plane-curve
theorem; `ShiftedTrace.MiddleGame.WeightedShiftedCorvajaZannier` transports it
to arbitrary weights and checks the remaining hypotheses.

The argument follows `BGS.Markoff.weightedTraceCurve_notSubtorusTranslate_of_weights_ne_zero`
for the unshifted curve: the involutions `k ↦ k⁻¹` and `h ↦ sigma * h⁻¹`
preserve the curve, and they still do after adding the constant `gamma`.
-/

namespace GenMarkoff.ShiftedTrace.MiddleGame

open BGS.Markoff Polynomial

noncomputable section

section CharacterPowers

variable {F : Type*} [Field F] [Infinite F]

/-- No fixed nonzero integer power is identically one on the units of an
infinite field. -/
private theorem exists_unit_zpow_ne_one_shifted (n : ℤ) (hn : n ≠ 0) :
    ∃ u : Fˣ, u ^ n ≠ 1 := by
  by_contra h
  push Not at h
  let m := n.natAbs
  let q : Polynomial F := Polynomial.X ^ m - 1
  have hm : m ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have hqDegree : q.natDegree = m := by
    simpa [q] using
      (Polynomial.natDegree_X_pow_sub_C (R := F) (n := m) (r := 1))
  have hq : q ≠ 0 := by
    intro hzero
    have : q.natDegree = 0 := by simp [hzero]
    omega
  have hXq : Polynomial.X * q ≠ 0 :=
    mul_ne_zero Polynomial.X_ne_zero hq
  apply hXq
  apply Polynomial.zero_of_eval_zero
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · let u : Fˣ := Units.mk0 x hx
    have hu : u ^ m = 1 := pow_natAbs_eq_one.mpr (h u)
    have hxpow : x ^ m = 1 := by
      have hval := congrArg (fun v : Fˣ ↦ (v : F)) hu
      simpa [u] using hval
    simp [q, hxpow]

end CharacterPowers

section CurveProjections

variable {F : Type*} [Field F] [IsAlgClosed F]

/-- Every right torus coordinate occurs on a shifted trace curve when
`sigma` is nonzero. -/
private theorem exists_shiftedWeightedTraceCurve_point_over_right
    (sigma gamma : F) (hsigma : sigma ≠ 0) (k : Fˣ) :
    ∃ h : Fˣ,
      weightedSplitTorusTrace 1 sigma h + gamma = splitTorusTrace k := by
  let trace := splitTorusTrace k - gamma
  let q : Polynomial F :=
    Polynomial.X ^ 2 - Polynomial.C trace * Polynomial.X +
      Polynomial.C sigma
  have hqDegree : q.natDegree = 2 := by
    -- `show` rewrites `q` into the `C a * X ^ 2 + C b * X + C c` form of `natDegree_quadratic`.
    rw [show q = Polynomial.C (1 : F) * Polynomial.X ^ 2 +
        Polynomial.C (-trace) * Polynomial.X + Polynomial.C sigma by
      simp only [q, Polynomial.C_neg, Polynomial.C_1, one_mul]
      ring]
    exact Polynomial.natDegree_quadratic one_ne_zero
  have hq : q ≠ 0 := by
    intro hzero
    have : q.natDegree = 0 := by simp [hzero]
    omega
  have hqDegreeBot : q.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hq, hqDegree]
    norm_num
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q hqDegreeBot
  have hxzero : x ≠ 0 := by
    intro hzero
    subst x
    simp [Polynomial.IsRoot.def, q, hsigma] at hx
  refine ⟨Units.mk0 x hxzero, ?_⟩
  simp only [weightedSplitTorusTrace, Units.val_mk0,
    Units.val_inv_eq_inv_val, one_mul]
  -- Unfolded `weightedSplitTorusTrace 1 sigma`: restate as `x + sigma * x⁻¹` for `field_simp`.
  change x + sigma * x⁻¹ + gamma = splitTorusTrace k
  have hxeq : x ^ 2 - trace * x + sigma = 0 := by
    simpa [Polynomial.IsRoot.def, q] using hx
  field_simp [hxzero]
  dsimp [trace] at hxeq
  linear_combination hxeq

/-- Every left torus coordinate occurs on the shifted trace curve. -/
private theorem exists_shiftedWeightedTraceCurve_point_over_left
    (sigma gamma : F) (h : Fˣ) :
    ∃ k : Fˣ,
      weightedSplitTorusTrace 1 sigma h + gamma = splitTorusTrace k := by
  let trace := weightedSplitTorusTrace 1 sigma h + gamma
  let q : Polynomial F :=
    Polynomial.X ^ 2 - Polynomial.C trace * Polynomial.X + 1
  have hqDegree : q.natDegree = 2 := by
    -- `show` rewrites `q` into the `C a * X ^ 2 + C b * X + C c` form of `natDegree_quadratic`.
    rw [show q = Polynomial.C (1 : F) * Polynomial.X ^ 2 +
        Polynomial.C (-trace) * Polynomial.X + Polynomial.C 1 by
      simp only [q, Polynomial.C_neg, Polynomial.C_1, one_mul]
      ring]
    exact Polynomial.natDegree_quadratic one_ne_zero
  have hq : q ≠ 0 := by
    intro hzero
    have : q.natDegree = 0 := by simp [hzero]
    omega
  have hqDegreeBot : q.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hq, hqDegree]
    norm_num
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q hqDegreeBot
  have hxzero : x ≠ 0 := by
    intro hzero
    subst x
    simp [Polynomial.IsRoot.def, q] at hx
  refine ⟨Units.mk0 x hxzero, ?_⟩
  -- Fold the left side into `trace`; `splitTorusTrace (Units.mk0 x _)` is `x + x⁻¹`.
  change trace = x + x⁻¹
  have hxeq : x ^ 2 - trace * x + 1 = 0 := by
    simpa [Polynomial.IsRoot.def, q] using hx
  field_simp [hxzero]
  linear_combination -hxeq

end CurveProjections

section DeckInvolutions

variable {F : Type*} [Field F]

private theorem splitTorusTrace_inv_shifted (k : Fˣ) :
    splitTorusTrace k⁻¹ = splitTorusTrace k := by
  simp only [splitTorusTrace, Units.val_inv_eq_inv_val, inv_inv]
  exact add_comm _ _

/-- The deck involution `h ↦ sigma * h⁻¹` preserves the shifted weighted
trace `h + sigma * h⁻¹ + gamma`. -/
private theorem shiftedWeightedSplitTorusTrace_deck_involution
    (sigma gamma : F) (hsigma : sigma ≠ 0) (h : Fˣ) :
    let q : Fˣ := Units.mk0 sigma hsigma
    weightedSplitTorusTrace 1 sigma (q * h⁻¹) + gamma =
      weightedSplitTorusTrace 1 sigma h + gamma := by
  dsimp
  simp only [weightedSplitTorusTrace, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_mk0, one_mul]
  field_simp [hsigma, Units.ne_zero h]
  ring

end DeckInvolutions

section NonSubtorus

variable {K : Type*} [Field K]

/-- For `sigma ≠ 0`, no character `(k, h) ↦ k ^ a * h ^ b` with
`(a, b) ≠ (0, 0)` is constant on the points of the shifted trace curve
`h + sigma * h⁻¹ + gamma = k + k⁻¹` over the algebraic closure. -/
theorem shiftedWeightedTraceCurve_notSubtorusTranslate
    (sigma gamma : K) (hsigma : sigma ≠ 0) :
    ∀ (a b : ℤ), (a ≠ 0 ∨ b ≠ 0) →
      ∀ c : (AlgebraicClosure K)ˣ,
        ∃ k h : (AlgebraicClosure K)ˣ,
          weightedSplitTorusTrace 1
              (algebraMap K (AlgebraicClosure K) sigma) h +
              algebraMap K (AlgebraicClosure K) gamma = splitTorusTrace k ∧
          k ^ a * h ^ b ≠ c := by
  let sigmaL : AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K) sigma
  let gammaL : AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K) gamma
  have hsigmaL : sigmaL ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective).mpr hsigma
  intro a b hab c
  by_contra hvaries
  push Not at hvaries
  -- Step 1: the curve is stable under `k ↦ k⁻¹` and every `k` occurs on it,
  -- so `k ^ (2 * a) = 1` for every unit `k`; hence `a = 0`.
  have haUniversal : ∀ k : (AlgebraicClosure K)ˣ, k ^ (2 * a) = 1 := by
    intro k
    obtain ⟨h, hcurve⟩ :=
      exists_shiftedWeightedTraceCurve_point_over_right
        sigmaL gammaL hsigmaL k
    have hcurveInv :
        weightedSplitTorusTrace 1 sigmaL h + gammaL =
          splitTorusTrace k⁻¹ := by
      rw [splitTorusTrace_inv_shifted]
      exact hcurve
    have hvalue := hvaries k h hcurve
    have hvalueInv := hvaries k⁻¹ h hcurveInv
    have hpower : k ^ a = (k⁻¹) ^ a := by
      exact mul_right_cancel (hvalue.trans hvalueInv.symm)
    have hpowerInv : k ^ a = (k ^ a)⁻¹ := by
      simpa only [inv_zpow] using hpower
    have hsquare : k ^ a * k ^ a = 1 :=
      eq_inv_iff_mul_eq_one.mp hpowerInv
    calc
      k ^ (2 * a) = k ^ (a + a) := by
        congr 1
        ring
      _ = k ^ a * k ^ a := zpow_add k a a
      _ = 1 := hsquare
  have ha : a = 0 := by
    by_contra ha
    have htwoa : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha
    obtain ⟨k, hk⟩ := exists_unit_zpow_ne_one_shifted
      (F := AlgebraicClosure K) (2 * a) htwoa
    exact hk (haUniversal k)
  -- Step 2: the curve is stable under `h ↦ sigma * h⁻¹` and every `h` occurs on
  -- it, so `h ^ (2 * b)` is constant, equal to its value `1` at `h = 1`; hence `b = 0`.
  have hbUniversal : ∀ h : (AlgebraicClosure K)ˣ, h ^ (2 * b) = 1 := by
    let q : (AlgebraicClosure K)ˣ := Units.mk0 sigmaL hsigmaL
    have hconstant :
        ∀ h : (AlgebraicClosure K)ˣ, h ^ (2 * b) = q ^ b := by
      intro h
      obtain ⟨k, hcurve⟩ :=
        exists_shiftedWeightedTraceCurve_point_over_left sigmaL gammaL h
      have hcurveDeck :
          weightedSplitTorusTrace 1 sigmaL (q * h⁻¹) + gammaL =
            splitTorusTrace k := by
        rw [shiftedWeightedSplitTorusTrace_deck_involution
          sigmaL gammaL hsigmaL]
        exact hcurve
      have hvalue := hvaries k h hcurve
      have hvalueDeck := hvaries k (q * h⁻¹) hcurveDeck
      have hpower : h ^ b = (q * h⁻¹) ^ b := by
        exact mul_left_cancel (hvalue.trans hvalueDeck.symm)
      have hpowerExpanded : h ^ b = q ^ b * (h ^ b)⁻¹ := by
        simpa only [mul_zpow, inv_zpow] using hpower
      have hsquare : h ^ b * h ^ b = q ^ b := by
        calc
          h ^ b * h ^ b = (q ^ b * (h ^ b)⁻¹) * h ^ b := by
            exact congrArg (fun z ↦ z * h ^ b) hpowerExpanded
          _ = q ^ b := by simp
      calc
        h ^ (2 * b) = h ^ (b + b) := by
          congr 1
          ring
        _ = h ^ b * h ^ b := zpow_add h b b
        _ = q ^ b := hsquare
    have hq : q ^ b = 1 := by
      have hone := hconstant (1 : (AlgebraicClosure K)ˣ)
      simpa using hone.symm
    intro h
    exact (hconstant h).trans hq
  have hb : b = 0 := by
    by_contra hb
    have htwob : 2 * b ≠ 0 := mul_ne_zero (by norm_num) hb
    obtain ⟨h, hh⟩ := exists_unit_zpow_ne_one_shifted
      (F := AlgebraicClosure K) (2 * b) htwob
    exact hh (hbUniversal h)
  exact hab.elim (fun hne ↦ hne ha) (fun hne ↦ hne hb)

end NonSubtorus

end

end GenMarkoff.ShiftedTrace.MiddleGame
