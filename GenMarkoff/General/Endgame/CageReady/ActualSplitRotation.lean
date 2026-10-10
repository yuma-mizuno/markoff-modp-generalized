import GenMarkoff.General.Endgame.ActualSplitRotation
import GenMarkoff.General.Endgame.CageReady.PrimitiveCount
import BGS.NumberTheory.ExplicitDivisorBound
import BGS.Markoff.Endgame.PrimitiveInclusionExclusion
import GenMarkoff.General.Arithmetic.ReasonableCutoff

/-!
# Cage-ready actual split endgame

A variant of the second-to-first split move of
`GenMarkoff.General.Endgame.ActualSplitRotation`: a forward `rotation2` iterate
on the fixed coefficient surface moves a split second-axis fiber point to a
point whose first-axis trace is primitive on the split torus and satisfies
`CageReadyFirstAxisTrace`.  That is, the trace avoids both directed
candidate-irregular loci and both directed incidence/centered-norm resultant
obstructions.  The reachable parameters are again the `q²`-power coset, and the
primitive trace comes from the ninety-six-pair count of
`GenMarkoff.General.Endgame.CageReady.PrimitiveCount`.
-/

namespace GenMarkoff.General.Endgame

open BGS.Markoff
open GenMarkoff.General.MiddleGame

noncomputable section

/-- Under the ninety-six-pair counting margin for the complementary exponent
of `q²`, some forward `rotation2` iterate of `fiberPoint2 a u t q s` has a
first-axis trace that is primitive on the split torus and satisfies
`CageReadyFirstAxisTrace`. -/
theorem
    exists_iterate_actualSplitFiberPoint_with_primitiveCageReadyAxisOneTrace
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q s : (ZMod p)ˣ)
    (htrace : t = orderedTrace a.multiplier a.a2 u)
    (heigen : t = splitTorusTrace q)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a1 a.a3 t)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) +
          96 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p
            (Nat.card (ZMod p)ˣ / orderOf (q ^ 2))) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      orderedTrace a.multiplier a.a1
          (((rotation2 a)^[n])
            (fiberPoint2 a u t (q : ZMod p) (s : ZMod p))).x1 =
        splitTorusTrace v ∧
      orderOf v = Nat.card (ZMod p)ˣ ∧
        CageReadyFirstAxisTrace a (splitTorusTrace v) := by
  -- Exponent, weights and shift of the first-axis trace on the translated coset.
  let orbitExponent :=
    Nat.card (ZMod p)ˣ / orderOf (q ^ 2)
  let alpha : ZMod p :=
    (a.multiplier * (q : ZMod p)) * (s : ZMod p)
  let beta : ZMod p :=
    (a.multiplier * centeredFiberProduct a.a3 a.a1 u t /
      (q : ZMod p)) / (s : ZMod p)
  let gamma : ZMod p :=
    actualGammaSecond a.multiplier a.a3 a.a1 u t
  -- Reverse candidate regularity gives the nondegeneracy hypotheses of the weighted count.
  have htwo : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have hweights :
      alpha * beta =
        actualSigma a.multiplier a.a3 a.a1 u t := by
    simpa [alpha, beta] using
      actual_secondDirected_coset_weights_mul
        a.multiplier a.a3 a.a1 u t q s
  have hproduct : alpha * beta ≠ 0 := by
    rw [hweights]
    exact actualSigma_ne_zero_of_reverseCandidateRegular
      a.multiplier a.a2 a.a3 a.a1 u t htrace hregular
  have halpha : alpha ≠ 0 :=
    (mul_ne_zero_iff.mp hproduct).1
  have hbeta : beta ≠ 0 :=
    (mul_ne_zero_iff.mp hproduct).2
  have hproductOne : alpha * beta ≠ 1 := by
    rw [hweights,
      actualSigma_eq_orderedTraceSigma
        a.multiplier a.a2 a.a3 a.a1 u t htrace,
      orderedTraceSigma_swap a.a2 a.a3 a.a1 t]
    exact hregular.sigma_ne_one
  have hD2 :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualSecondEvenObstruction_ne_zero_of_candidateRegular
      a.multiplier a.a2 a.a3 a.a1 u t
        htrace hA1 hregular
  -- A primitive pair whose trace is cage-ready.
  obtain ⟨z, hzTrace, hzOrder, hzCageReady⟩ :=
    exists_weightedShiftedSplitPrimitiveTracePair_cageReady_of_error_add_ninetySix_lt_main
      p coefficient hWeil a alpha beta gamma orbitExponent
        htwo hA1 hA2 hA3 halpha hbeta hproductOne hD2
        (BGS.Markoff.complementaryExponent_pos (q ^ 2))
        (BGS.Markoff.splitComplementaryExponent_cast_ne_zero p (q ^ 2))
        (BGS.Markoff.complementaryExponent_dvd_natCard (q ^ 2))
        (by simpa [orbitExponent] using hmargin)
  -- Reach its parameter by a `rotation2` iterate and identify the trace.
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  obtain ⟨n, hn⟩ :=
    exists_iterate_fiberPoint2_eq_of_mem_complementarySquarePowerRange
      p a u t q s hD heigen htrace z.1
  refine ⟨n, z.2, ?_, hzOrder, hzCageReady⟩
  rw [hn]
  calc
    orderedTrace a.multiplier a.a1
        (fiberPoint2 a u t (q : ZMod p)
          ((s * z.1.1 : (ZMod p)ˣ) : ZMod p)).x1 =
        weightedSplitTorusTrace alpha beta z.1.1 + gamma := by
      simpa [alpha, beta, gamma] using
        orderedTrace_fiberPoint2_complementarySquarePowerRange_eq_weightedShiftedTrace
          p a u t q s z.1
    _ = weightedShiftedSplitTorusTrace
          (ZMod p) alpha beta gamma z.1 := by
      rfl
    _ = splitTorusTrace z.2 := hzTrace

/-- Arbitrary-point form of the cage-ready second-to-first split move: the same
conclusion for every solution `x` with `x.x2 = u`. -/
theorem
    exists_iterate_actualSplitPoint_with_primitiveCageReadyAxisOneTrace
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q : (ZMod p)ˣ)
    (x : Point (ZMod p))
    (hx : IsSolution a x) (hx2 : x.x2 = u)
    (htrace : t = orderedTrace a.multiplier a.a2 u)
    (heigen : t = splitTorusTrace q)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a1 a.a3 t)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) +
          96 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p
            (Nat.card (ZMod p)ˣ / orderOf (q ^ 2))) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      orderedTrace a.multiplier a.a1
          (((rotation2 a)^[n]) x).x1 =
        splitTorusTrace v ∧
      orderOf v = Nat.card (ZMod p)ˣ ∧
        CageReadyFirstAxisTrace a (splitTorusTrace v) := by
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have hconic :
      fiberConic a.a3 a.a1 u t x.x3 x.x1 = 0 := by
    have hsurface := hx
    rw [IsSolution, polynomial_fixed_second, hx2, ← htrace] at hsurface
    exact hsurface
  have hproduct :
      centeredFiberProduct a.a3 a.a1 u t ≠ 0 :=
    centeredFiberProduct_ne_zero_of_reverseCandidateRegular
      a.multiplier a.a2 a.a3 a.a1 u t htrace hregular
  obtain ⟨s, hsPair⟩ :=
    exists_unit_fiberPair_eq
      a.a3 a.a1 u t q (x.x3, x.x1)
        hconic heigen hD hproduct
  have hsPoint :
      fiberPoint2 a u t (q : ZMod p) (s : ZMod p) = x := by
    apply Point.ext
    · simpa [fiberPoint2] using congrArg Prod.snd hsPair
    · simpa using hx2.symm
    · simpa [fiberPoint2] using congrArg Prod.fst hsPair
  obtain ⟨n, v, hn, hvOrder, hvCageReady⟩ :=
    exists_iterate_actualSplitFiberPoint_with_primitiveCageReadyAxisOneTrace
      p coefficient hWeil hpTwo a u t q s htrace heigen
        hA1 hA2 hA3 hregular hmargin
  refine ⟨n, v, ?_, hvOrder, hvCageReady⟩
  simpa [hsPoint] using hn

/-- The explicit inequality for the coefficient `coefficient + 96` gives the
ninety-six-pair margin: the divisor-count error term plus `96` is below
`primitiveTraceMoebiusMainTerm`. -/
private theorem
    error_add_ninetySix_lt_primitiveMain_of_augmented_explicitInequality
    (groupOrder fieldCard fixedExponent coefficient : ℕ)
    (hgroup : 0 < groupOrder) (hfield : 0 < fieldCard)
    (hfixed : 0 < fixedExponent)
    (hexplicit :
      (fixedExponent : ℝ) * (groupOrder.divisors.card : ℝ) ^ 2 *
          (((coefficient + 96 : ℕ) : ℝ) *
            Real.sqrt (fieldCard : ℝ)) < fieldCard) :
    (groupOrder.divisors.card : ℝ) *
          ((coefficient : ℝ) * Real.sqrt (fieldCard : ℝ)) + 96 <
      primitiveTraceMoebiusMainTerm
        groupOrder fieldCard fixedExponent := by
  have hdomination :=
    BGS.Markoff.divisorsError_lt_primitiveTraceMoebiusMainTerm_of_explicitInequality
      groupOrder fieldCard fixedExponent (coefficient + 96)
      hgroup hfixed hexplicit
  -- Since `1 ≤ #divisors * √fieldCard`, the additive `96` is absorbed into the coefficient.
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
            ((coefficient : ℝ) * Real.sqrt (fieldCard : ℝ)) + 96 =
        (coefficient : ℝ) *
            ((groupOrder.divisors.card : ℝ) *
              Real.sqrt (fieldCard : ℝ)) + 96 := by ring
    _ ≤ (coefficient : ℝ) *
            ((groupOrder.divisors.card : ℝ) *
              Real.sqrt (fieldCard : ℝ)) +
          96 * ((groupOrder.divisors.card : ℝ) *
            Real.sqrt (fieldCard : ℝ)) := by
      have hninetysix :
          (96 : ℝ) ≤
            96 * ((groupOrder.divisors.card : ℝ) *
              Real.sqrt (fieldCard : ℝ)) := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hproductOne
            -- `show` only fixes the side goal `0 ≤ 96` in `ℝ`; nothing is unfolded.
            (show (0 : ℝ) ≤ 96 by norm_num))
      exact add_le_add
        (le_refl
          ((coefficient : ℝ) *
            ((groupOrder.divisors.card : ℝ) *
              Real.sqrt (fieldCard : ℝ))))
        hninetysix
    _ = (groupOrder.divisors.card : ℝ) *
          (((coefficient + 96 : ℕ) : ℝ) *
            Real.sqrt (fieldCard : ℝ)) := by
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      ring
    _ < primitiveTraceMoebiusMainTerm
        groupOrder fieldCard fixedExponent := hdomination

/-- Reasonable-cutoff version of the cage-ready split move: for
`p ≥ reasonableAnalyticCutoff`, `coefficient + 96 ≤ 1032` and
`p ^ (1/2 + delta) ≤ orderOf (q ^ 2)` with `delta ≥ 1/4`, the ninety-six-pair
margin holds and the arbitrary-point form applies. -/
theorem actualSplitPoint_with_primitiveCageReadyAxisOneTrace_of_reasonableCutoff
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : (1 : ℝ) / 4 ≤ delta)
    (hcoefficient : coefficient + 96 ≤ 1032)
    (p : ℕ)
    (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q : (ZMod p)ˣ) (x : Point (ZMod p))
    (hx : IsSolution a x) (hx2 : x.x2 = u)
    (htrace : t = orderedTrace a.multiplier a.a2 u)
    (heigen : t = splitTorusTrace q)
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a1 a.a3 t)
    (hlarge :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (q ^ 2)) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      orderedTrace a.multiplier a.a1 (((rotation2 a)^[n]) x).x1 =
          splitTorusTrace v ∧
        orderOf v = Nat.card (ZMod p)ˣ ∧
          CageReadyFirstAxisTrace a (splitTorusTrace v) := by
  have hpThree : 3 ≤ p := by
    have hpFive :=
      GenMarkoff.General.Explicit.five_le_reasonableAnalyticCutoff.trans hp
    omega
  have hpTwo : p ≠ 2 := by omega
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  let orbitExponent :=
    Nat.card (ZMod p)ˣ / orderOf (q ^ 2)
  have hmul :
      orbitExponent * orderOf (q ^ 2) = p - 1 := by
    dsimp [orbitExponent]
    rw [Nat.div_mul_cancel (orderOf_dvd_natCard (q ^ 2)), hcard]
  have hexplicit :=
    GenMarkoff.General.Explicit.reasonable_primitiveTrace_explicitInequality_of_card_sub_one
      hp hmul hlarge hdelta hcoefficient
  have hexplicit' :
      (orbitExponent : ℝ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
            (((coefficient + 96 : ℕ) : ℝ) *
              Real.sqrt (p : ℝ)) < p := by
    simpa only [hcard] using hexplicit
  have hgroupPositive : 0 < Nat.card (ZMod p)ˣ := by
    rw [hcard]
    omega
  have hmargin :=
    error_add_ninetySix_lt_primitiveMain_of_augmented_explicitInequality
      (Nat.card (ZMod p)ˣ) p orbitExponent coefficient
        hgroupPositive (by omega)
        (BGS.Markoff.complementaryExponent_pos (q ^ 2)) hexplicit'
  exact
    exists_iterate_actualSplitPoint_with_primitiveCageReadyAxisOneTrace
      p coefficient hWeil hpTwo a u t q x hx hx2 htrace heigen
        hA1 hA2 hA3 hregular
        (by simpa [orbitExponent] using hmargin)

end

end GenMarkoff.General.Endgame
