import GenMarkoff.Symmetric.MiddleGame.ActualDiagonalization
import GenMarkoff.Symmetric.MiddleGame.ActualMoveWiring
import GenMarkoff.Symmetric.Endgame.ActualPrimitiveCount
import GenMarkoff.TraceCurve.WeightedShiftedCoverCounting
import BGS.Markoff.Endgame.PrimitiveOrbitWiring

/-!
# Coset-correct split endgame wiring

The primitive endgame counts a point in the complementary power-map image of
the fixed-fiber eigenvalue.  An actual point starts at a generally nontrivial
torus parameter `s`, so the reached parameters are `s * h`, not merely `h`.
This module records the exact transport to forward `oneStep1` iterates.
-/

namespace GenMarkoff.Symmetric.Endgame

open BGS.Markoff

noncomputable section

/-- A parameter in the complementary power image of the eigenvalue is
reached by a forward one-step iterate of the actual translated fiber point. -/
theorem exists_iterate_fiberPoint_eq_of_mem_complementaryPowerRange
    (p : ℕ) [Fact p.Prime]
    (c u t : ZMod p) (q s : (ZMod p)ˣ)
    (htraceEigenvalue : t = splitTorusTrace q)
    (htraceCoordinate : t = trace c u) (ht : t ≠ 2)
    (h : (powMonoidHom
      (Nat.card (ZMod p)ˣ / orderOf q) :
        (ZMod p)ˣ →* (ZMod p)ˣ).range) :
    ∃ n : ℕ,
      ((oneStep1 c)^[n])
          (fiberPoint c u t (q : ZMod p) (s : ZMod p)) =
        fiberPoint c u t (q : ZMod p)
          ((s * h.1 : (ZMod p)ˣ) : ZMod p) := by
  obtain ⟨n, hn⟩ :=
    BGS.Markoff.exists_pow_eq_of_mem_complementaryPowerRange q h
  refine ⟨n, ?_⟩
  have htraceEigenvalue' :
      t = (q : ZMod p) + (q : ZMod p)⁻¹ := by
    simpa only [splitTorusTrace, Units.val_inv_eq_inv_val] using
      htraceEigenvalue
  rw [MiddleGame.iterate_oneStep1_fiberPoint_eq_pow_mul
    c u t (q : ZMod p) (s : ZMod p)
    (Units.ne_zero q) (Units.ne_zero s)
    htraceEigenvalue' htraceCoordinate ht n]
  congr 1
  have hnVal : ((q ^ n : (ZMod p)ˣ) : ZMod p) = (h.1 : ZMod p) :=
    congrArg (fun z : (ZMod p)ˣ => (z : ZMod p)) hn
  simpa only [Units.val_pow_eq_pow_val, Units.val_mul, mul_comm] using
    congrArg (fun z : ZMod p => (s : ZMod p) * z) hnVal

/-- The adjacent trace at a point reached through the complementary power
image has the two actual coset weights. -/
theorem trace_fiberPoint_complementaryPowerRange_eq_weightedShiftedTrace
    (p : ℕ) [Fact p.Prime]
    (c u t : ZMod p) (q s : (ZMod p)ˣ)
    (h : (powMonoidHom
      (Nat.card (ZMod p)ˣ / orderOf q) :
        (ZMod p)ˣ →* (ZMod p)ˣ).range) :
    trace c
        (fiberPoint c u t (q : ZMod p)
          ((s * h.1 : (ZMod p)ˣ) : ZMod p)).x2 =
      weightedSplitTorusTrace
          (actualAlpha c * (s : ZMod p))
          (actualBeta c u t / (s : ZMod p)) h.1 +
        actualGamma c u t := by
  exact MiddleGame.trace_fiberPoint_mul_eq_weightedSplitTorusTrace
    c u t q s h.1

/-- The coset-correct split primitive count is an actual forward one-step
iterate.  This closes the reachability gap left by the normalized geometric
witness theorem. -/
theorem exists_iterate_actualSplitFiberPoint_with_primitiveAdjacentTrace
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (c u t : ZMod p) (q s : (ZMod p)ˣ)
    (htrace : t = trace c u)
    (heigen : t = splitTorusTrace q)
    (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (hexplicit :
      (Nat.card (ZMod p)ˣ / orderOf q : ℕ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p) :
    ∃ n : ℕ, ∃ k : (ZMod p)ˣ,
      trace c
          (((oneStep1 c)^[n])
            (fiberPoint c u t (q : ZMod p) (s : ZMod p))).x2 =
        splitTorusTrace k ∧
      orderOf k = Nat.card (ZMod p)ˣ := by
  let orbitExponent := Nat.card (ZMod p)ˣ / orderOf q
  let alpha : ZMod p := actualAlpha c * (s : ZMod p)
  let beta : ZMod p := actualBeta c u t / (s : ZMod p)
  let gamma : ZMod p := actualGamma c u t
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
    exact hpTwo (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)
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
  obtain ⟨z, hzTrace, hzOrder⟩ :=
    exists_weightedShiftedSplitPrimitiveTracePair_of_explicitInequality
      p coefficient hWeil alpha beta gamma orbitExponent htwo
      halpha hbeta hproductOne hD2
      (BGS.Markoff.complementaryExponent_pos q)
      (BGS.Markoff.splitComplementaryExponent_cast_ne_zero p q)
      (BGS.Markoff.complementaryExponent_dvd_natCard q)
      (by simpa [orbitExponent] using hexplicit)
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  obtain ⟨n, hn⟩ :=
    exists_iterate_fiberPoint_eq_of_mem_complementaryPowerRange
      p c u t q s heigen htrace
      (ne_two_of_discriminant_ne_zero hD) z.1
  refine ⟨n, z.2, ?_, hzOrder⟩
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

/-- Arbitrary-point form of the coset-correct split endgame. -/
theorem exists_iterate_actualSplitPoint_with_primitiveAdjacentTrace
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
    (hexplicit :
      (Nat.card (ZMod p)ˣ / orderOf q : ℕ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p) :
    ∃ n : ℕ, ∃ k : (ZMod p)ˣ,
      trace c (((oneStep1 c)^[n]) x).x2 =
          splitTorusTrace k ∧
        orderOf k = Nat.card (ZMod p)ˣ := by
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have hproduct : centeredFiberProduct c u t ≠ 0 :=
    MiddleGame.centeredFiberProduct_ne_zero_of_candidateRegular
      c u t htrace hregular
  obtain ⟨s, hs⟩ :=
    MiddleGame.exists_unit_fiberPoint_eq
      c u t q x hx1 hx htrace heigen hD hproduct
  obtain ⟨n, k, hn, hk⟩ :=
    exists_iterate_actualSplitFiberPoint_with_primitiveAdjacentTrace
      p coefficient hWeil hpTwo c u t q s htrace heigen hc hregular
      hexplicit
  refine ⟨n, k, ?_, hk⟩
  simpa [hs] using hn

/-- Uniform large-order split endgame for an arbitrary point on an actual
candidate-regular symmetric fiber. -/
theorem exists_threshold_actualSplitPoint_with_primitiveAdjacentTrace
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
        ∃ n : ℕ, ∃ k : (ZMod p)ˣ,
          trace c (((oneStep1 c)^[n]) x).x2 =
              splitTorusTrace k ∧
            orderOf k = Nat.card (ZMod p)ˣ := by
  obtain ⟨inequalityThreshold, hInequality⟩ :=
    BGS.Markoff.exists_threshold_endgamePrimitiveTrace_explicitInequality_of_largeOrder
      coefficient hdelta
  refine ⟨max inequalityThreshold 3, ?_⟩
  intro p hp _ c u t q x hx hx1 htrace heigen hc hregular hlarge
  have hpInequality : inequalityThreshold ≤ p :=
    (Nat.le_max_left inequalityThreshold 3).trans hp
  have hpTwo : p ≠ 2 := by omega
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  have hmul :
      (Nat.card (ZMod p)ˣ / orderOf q) * orderOf q = p - 1 := by
    rw [Nat.div_mul_cancel (orderOf_dvd_natCard q), hcard]
  have hexplicit :=
    hInequality p hpInequality
      (Nat.card (ZMod p)ˣ / orderOf q) (orderOf q)
      hmul hlarge
  have hexplicit' :
      (Nat.card (ZMod p)ˣ / orderOf q : ℕ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
    simpa only [hcard] using hexplicit
  exact exists_iterate_actualSplitPoint_with_primitiveAdjacentTrace
    p coefficient hWeil hpTwo c u t q x hx hx1 htrace heigen hc hregular
      hexplicit'

end

end GenMarkoff.Symmetric.Endgame
