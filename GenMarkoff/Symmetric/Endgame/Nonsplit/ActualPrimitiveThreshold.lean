import GenMarkoff.Symmetric.Endgame.Nonsplit.ActualPrimitiveOrbit

/-!
# Uniform large-order nonsplit primitive endgame

The candidate-regular primitive count loses at most twenty-eight pairs.  For
large primes this fixed loss is absorbed by running the standard BGS
large-nonsplit-order inequality with coefficient `coefficient + 28`.
-/

namespace GenMarkoff.Symmetric.Endgame.Nonsplit

open BGS.Markoff

noncomputable section

/-- Uniform large-order nonsplit endgame for an arbitrary point on an actual
candidate-regular symmetric fiber.  The produced adjacent trace is primitive
in the split torus and remains candidate-regular, so it can be fed back into
the next middle-game/end-game step. -/
theorem exists_threshold_actualNonsplitPoint_with_primitiveCandidateRegularAdjacentTrace
    (coefficient : ℕ)
    (hWeil : ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
      ∀ (c u t : ZMod p) (x : Point (ZMod p))
        (w : quadraticNormOneTorus p),
        IsSolution (coefficients c) x →
        x.x1 = u →
        t = trace c u →
        c ^ 2 ≠ 4 →
        OrderedTraceCandidateRegular c c c t →
        quadraticNormOneTrace p w = t →
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf w →
        ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
          trace c (((oneStep1 c)^[n]) x).x2 = splitTorusTrace v ∧
            orderOf v = Nat.card (ZMod p)ˣ ∧
              OrderedTraceCandidateRegular c c c (splitTorusTrace v) := by
  obtain ⟨inequalityThreshold, hInequality⟩ :=
    BGS.Markoff.exists_threshold_endgamePrimitiveTrace_explicitInequality_of_largeNonsplitOrder
      (coefficient + 28) hdelta
  refine ⟨max inequalityThreshold 3, ?_⟩
  intro p hp _ c u t x w hx hx1 htrace hc hregular htraceW hlarge
  have hpInequality : inequalityThreshold ≤ p :=
    (Nat.le_max_left inequalityThreshold 3).trans hp
  have hpThree : 3 ≤ p :=
    (Nat.le_max_right inequalityThreshold 3).trans hp
  have hpTwo : p ≠ 2 := by omega
  let orbitExponent :=
    Nat.card (quadraticNormOneTorus p) / orderOf w
  have hmul :
      orbitExponent * orderOf w = p + 1 := by
    dsimp [orbitExponent]
    rw [Nat.div_mul_cancel (orderOf_dvd_natCard w),
      quadraticNormOneTorus_natCard]
  have hexplicit :=
    hInequality p hpInequality orbitExponent (orderOf w) hmul hlarge
  have hcardUnits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  have hexplicit' :
      (orbitExponent : ℝ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
            (((coefficient + 28 : ℕ) : ℝ) *
              Real.sqrt (p : ℝ)) < p := by
    simpa only [hcardUnits] using hexplicit
  have hgroupPositive : 0 < Nat.card (ZMod p)ˣ := by
    rw [hcardUnits]
    omega
  have horbitPositive : 0 < orbitExponent := by
    exact BGS.Markoff.complementaryExponent_pos w
  have hdomination :=
    BGS.Markoff.divisorsError_lt_primitiveTraceMoebiusMainTerm_of_explicitInequality
      (Nat.card (ZMod p)ˣ) p orbitExponent (coefficient + 28)
      hgroupPositive horbitPositive hexplicit'
  have hdivisorsOne :
      (1 : ℝ) ≤ ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) := by
    exact_mod_cast
      (Nat.nonempty_divisors.mpr hgroupPositive.ne').card_pos
  have hpOneReal : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (show 1 ≤ p by omega)
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (p : ℝ) :=
    Real.one_le_sqrt.mpr hpOneReal
  have hproductOne :
      (1 : ℝ) ≤
        ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
          Real.sqrt (p : ℝ) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
          Real.sqrt (p : ℝ) := by gcongr
  have hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) + 28 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p orbitExponent := by
    calc
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
              ((coefficient : ℝ) * Real.sqrt (p : ℝ)) + 28 =
          (coefficient : ℝ) *
              (((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
                Real.sqrt (p : ℝ)) + 28 := by ring
      _ ≤ (coefficient : ℝ) *
              (((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
                Real.sqrt (p : ℝ)) +
            28 *
              (((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
                Real.sqrt (p : ℝ)) := by
          have htwentyEight :
              (28 : ℝ) ≤
                28 * (((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
                  Real.sqrt (p : ℝ)) := by
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hproductOne
                (show (0 : ℝ) ≤ 28 by norm_num))
          exact add_le_add
            (le_refl
              ((coefficient : ℝ) *
                (((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
                  Real.sqrt (p : ℝ))))
            htwentyEight
      _ = ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            (((coefficient + 28 : ℕ) : ℝ) *
              Real.sqrt (p : ℝ)) := by
          norm_num only [Nat.cast_add, Nat.cast_ofNat]
          ring
      _ < primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p orbitExponent := hdomination
  have hmargin' :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) + 28 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p
            (Nat.card (quadraticNormOneTorus p) / orderOf w) := by
    exact hmargin
  exact
    exists_iterate_actualNonsplitPoint_with_primitiveCandidateRegularAdjacentTrace
      p coefficient hWeil hpTwo c u t x hx hx1 htrace hc hregular
        w htraceW hmargin'

end

end GenMarkoff.Symmetric.Endgame.Nonsplit
