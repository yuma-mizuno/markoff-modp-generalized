import GenMarkoff.Symmetric.Endgame.ActualOrbitWiring
import GenMarkoff.Symmetric.Endgame.RegularPrimitiveCount

/-!
# Candidate-regular primitive traces on actual split orbits

This is the candidate-regular strengthening of the coset-correct split
endgame.  The twenty-eight potentially unsafe trace pairs are removed before
the counted parameter is transported back to an actual forward one-step
iterate.
-/

namespace GenMarkoff.Symmetric.Endgame

open BGS.Markoff

noncomputable section

private theorem error_add_twentyEight_lt_primitiveMain_of_augmented_explicitInequality
    (groupOrder fieldCard fixedExponent coefficient : ℕ)
    (hgroup : 0 < groupOrder) (hfield : 0 < fieldCard)
    (hfixed : 0 < fixedExponent)
    (hexplicit :
      (fixedExponent : ℝ) * (groupOrder.divisors.card : ℝ) ^ 2 *
          (((coefficient + 28 : ℕ) : ℝ) *
            Real.sqrt (fieldCard : ℝ)) < fieldCard) :
    (groupOrder.divisors.card : ℝ) *
          ((coefficient : ℝ) * Real.sqrt (fieldCard : ℝ)) + 28 <
      primitiveTraceMoebiusMainTerm
        groupOrder fieldCard fixedExponent := by
  have hdomination :=
    BGS.Markoff.divisorsError_lt_primitiveTraceMoebiusMainTerm_of_explicitInequality
      groupOrder fieldCard fixedExponent (coefficient + 28)
      hgroup hfixed hexplicit
  have hdivisorsOne :
      (1 : ℝ) ≤ (groupOrder.divisors.card : ℝ) := by
    exact_mod_cast
      (Nat.nonempty_divisors.mpr hgroup.ne').card_pos
  have hfieldOne : (1 : ℝ) ≤ (fieldCard : ℝ) := by
    exact_mod_cast hfield
  have hsqrtOne :
      (1 : ℝ) ≤ Real.sqrt (fieldCard : ℝ) :=
    Real.one_le_sqrt.mpr hfieldOne
  have hproductOne :
      (1 : ℝ) ≤
        (groupOrder.divisors.card : ℝ) *
          Real.sqrt (fieldCard : ℝ) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (groupOrder.divisors.card : ℝ) *
          Real.sqrt (fieldCard : ℝ) := by gcongr
  calc
    (groupOrder.divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (fieldCard : ℝ)) + 28 =
        (coefficient : ℝ) *
            ((groupOrder.divisors.card : ℝ) *
              Real.sqrt (fieldCard : ℝ)) + 28 := by ring
    _ ≤ (coefficient : ℝ) *
            ((groupOrder.divisors.card : ℝ) *
              Real.sqrt (fieldCard : ℝ)) +
          28 * ((groupOrder.divisors.card : ℝ) *
            Real.sqrt (fieldCard : ℝ)) := by
      have htwentyEight :
          (28 : ℝ) ≤
            28 * ((groupOrder.divisors.card : ℝ) *
              Real.sqrt (fieldCard : ℝ)) := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hproductOne
            (show (0 : ℝ) ≤ 28 by norm_num))
      exact add_le_add
        (le_refl
          ((coefficient : ℝ) *
            ((groupOrder.divisors.card : ℝ) *
              Real.sqrt (fieldCard : ℝ))))
        htwentyEight
    _ = (groupOrder.divisors.card : ℝ) *
          (((coefficient + 28 : ℕ) : ℝ) *
            Real.sqrt (fieldCard : ℝ)) := by
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      ring
    _ < primitiveTraceMoebiusMainTerm
        groupOrder fieldCard fixedExponent := hdomination

/-- Coset-correct split primitive count for an explicitly parametrized actual
fiber point, strengthened so the new trace is candidate-regular. -/
theorem exists_iterate_actualSplitFiberPoint_with_primitiveCandidateRegularAdjacentTrace
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (c u t : ZMod p) (q s : (ZMod p)ˣ)
    (htrace : t = trace c u)
    (heigen : t = splitTorusTrace q)
    (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) + 28 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p
            (Nat.card (ZMod p)ˣ / orderOf q)) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      trace c
          (((oneStep1 c)^[n])
            (fiberPoint c u t (q : ZMod p) (s : ZMod p))).x2 =
        splitTorusTrace v ∧
      orderOf v = Nat.card (ZMod p)ˣ ∧
        OrderedTraceCandidateRegular c c c (splitTorusTrace v) := by
  let orbitExponent := Nat.card (ZMod p)ˣ / orderOf q
  let alpha : ZMod p := actualAlpha c * (s : ZMod p)
  let beta : ZMod p := actualBeta c u t / (s : ZMod p)
  let gamma : ZMod p := actualGamma c u t
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
    exact hpTwo
      (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)
  have hmultiplier : multiplier c ≠ 0 :=
    multiplier_ne_zero_of_candidateRegular c u t htrace hregular
  have halpha : alpha ≠ 0 := by
    exact mul_ne_zero
      (MiddleGame.actualAlpha_ne_zero c hmultiplier) (Units.ne_zero s)
  have hbeta : beta ≠ 0 := by
    exact div_ne_zero
      (MiddleGame.actualBeta_ne_zero_of_candidateRegular
        c u t htrace hregular)
      (Units.ne_zero s)
  have hweights : alpha * beta = actualSigma c u t := by
    simpa [alpha, beta] using
      MiddleGame.actual_coset_weights_mul c u t s
  have hproductOne : alpha * beta ≠ 1 := by
    rw [hweights]
    exact MiddleGame.actualSigma_ne_one_of_candidateRegular
      c u t htrace hregular
  have hD2 :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact MiddleGame.actualEvenObstruction_ne_zero_of_candidateRegular
      c u t htrace hc hregular
  obtain ⟨z, hzTrace, hzOrder, hzRegular⟩ :=
    exists_weightedShiftedSplitPrimitiveTracePair_candidateRegular_of_error_add_twentyEight_lt_main
      p coefficient hWeil c alpha beta gamma orbitExponent
        htwo hc halpha hbeta hproductOne hD2
        (BGS.Markoff.complementaryExponent_pos q)
        (BGS.Markoff.splitComplementaryExponent_cast_ne_zero p q)
        (BGS.Markoff.complementaryExponent_dvd_natCard q)
        (by simpa [orbitExponent] using hmargin)
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  obtain ⟨n, hn⟩ :=
    exists_iterate_fiberPoint_eq_of_mem_complementaryPowerRange
      p c u t q s heigen htrace
        (ne_two_of_discriminant_ne_zero hD) z.1
  refine ⟨n, z.2, ?_, hzOrder, hzRegular⟩
  rw [hn]
  calc
    trace c
        (fiberPoint c u t (q : ZMod p)
          ((s * z.1.1 : (ZMod p)ˣ) : ZMod p)).x2 =
        weightedSplitTorusTrace alpha beta z.1.1 + gamma := by
      simpa [alpha, beta, gamma] using
        trace_fiberPoint_complementaryPowerRange_eq_weightedShiftedTrace
          p c u t q s z.1
    _ = weightedShiftedSplitTorusTrace
          (ZMod p) alpha beta gamma z.1 := by
      rfl
    _ = splitTorusTrace z.2 := hzTrace

/-- Arbitrary-point form of the candidate-regular split primitive endgame. -/
theorem exists_iterate_actualSplitPoint_with_primitiveCandidateRegularAdjacentTrace
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (c u t : ZMod p) (q : (ZMod p)ˣ)
    (x : Point (ZMod p))
    (hx : IsSolution (coefficients c) x) (hx1 : x.x1 = u)
    (htrace : t = trace c u)
    (heigen : t = splitTorusTrace q)
    (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) + 28 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p
            (Nat.card (ZMod p)ˣ / orderOf q)) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      trace c (((oneStep1 c)^[n]) x).x2 = splitTorusTrace v ∧
        orderOf v = Nat.card (ZMod p)ˣ ∧
          OrderedTraceCandidateRegular c c c (splitTorusTrace v) := by
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have hproduct : centeredFiberProduct c u t ≠ 0 :=
    MiddleGame.centeredFiberProduct_ne_zero_of_candidateRegular
      c u t htrace hregular
  obtain ⟨s, hs⟩ :=
    MiddleGame.exists_unit_fiberPoint_eq
      c u t q x hx1 hx htrace heigen hD hproduct
  obtain ⟨n, v, hn, hvOrder, hvRegular⟩ :=
    exists_iterate_actualSplitFiberPoint_with_primitiveCandidateRegularAdjacentTrace
      p coefficient hWeil hpTwo c u t q s htrace heigen hc hregular
        hmargin
  refine ⟨n, v, ?_, hvOrder, hvRegular⟩
  simpa [hs] using hn

/-- Uniform large-order split endgame with primitive and candidate-regular
adjacent trace.  The fixed unsafe-pair loss is absorbed by applying the BGS
threshold to `coefficient + 28`. -/
theorem exists_threshold_actualSplitPoint_with_primitiveCandidateRegularAdjacentTrace
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
      ∀ (c u t : ZMod p) (q : (ZMod p)ˣ) (x : Point (ZMod p)),
        IsSolution (coefficients c) x →
        x.x1 = u →
        t = trace c u →
        t = splitTorusTrace q →
        c ^ 2 ≠ 4 →
        OrderedTraceCandidateRegular c c c t →
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf q →
        ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
          trace c (((oneStep1 c)^[n]) x).x2 = splitTorusTrace v ∧
            orderOf v = Nat.card (ZMod p)ˣ ∧
              OrderedTraceCandidateRegular c c c (splitTorusTrace v) := by
  obtain ⟨inequalityThreshold, hInequality⟩ :=
    BGS.Markoff.exists_threshold_endgamePrimitiveTrace_explicitInequality_of_largeOrder
      (coefficient + 28) hdelta
  refine ⟨max inequalityThreshold 3, ?_⟩
  intro p hp _ c u t q x hx hx1 htrace heigen hc hregular hlarge
  have hpInequality : inequalityThreshold ≤ p :=
    (Nat.le_max_left inequalityThreshold 3).trans hp
  have hpThree : 3 ≤ p :=
    (Nat.le_max_right inequalityThreshold 3).trans hp
  have hpTwo : p ≠ 2 := by omega
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  let orbitExponent := Nat.card (ZMod p)ˣ / orderOf q
  have hmul :
      orbitExponent * orderOf q = p - 1 := by
    dsimp [orbitExponent]
    rw [Nat.div_mul_cancel (orderOf_dvd_natCard q), hcard]
  have hexplicit :=
    hInequality p hpInequality orbitExponent (orderOf q) hmul hlarge
  have hexplicit' :
      (orbitExponent : ℝ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
            (((coefficient + 28 : ℕ) : ℝ) *
              Real.sqrt (p : ℝ)) < p := by
    simpa only [hcard] using hexplicit
  have hgroupPositive : 0 < Nat.card (ZMod p)ˣ := by
    rw [hcard]
    omega
  have hmargin :=
    error_add_twentyEight_lt_primitiveMain_of_augmented_explicitInequality
      (Nat.card (ZMod p)ˣ) p orbitExponent coefficient
        hgroupPositive (by omega)
        (BGS.Markoff.complementaryExponent_pos q) hexplicit'
  exact
    exists_iterate_actualSplitPoint_with_primitiveCandidateRegularAdjacentTrace
      p coefficient hWeil hpTwo c u t q x hx hx1 htrace heigen hc
        hregular (by simpa [orbitExponent] using hmargin)

end

end GenMarkoff.Symmetric.Endgame
