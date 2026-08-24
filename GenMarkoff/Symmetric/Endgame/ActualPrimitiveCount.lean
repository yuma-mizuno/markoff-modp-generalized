import GenMarkoff.Symmetric.Endgame.ActualShiftedCover
import GenMarkoff.TraceCurve.ShiftedCoverCounting

/-!
# Primitive split traces on an actual symmetric fiber

This module specializes the shifted split power-cover count to the parameters
of a candidate-regular symmetric fiber.  The resulting witness is an actual
point of that fiber with a primitive adjacent split trace.  It is not a cage
or global-orbit reachability theorem.

The nonsplit branch is deliberately absent: it requires a norm-one torus
model over the quadratic extension and a proof that its shifted power-cover
solutions descend to the ground field.  Counting all quadratic-field zeros
of the split polynomial would not prove that statement.
-/

namespace GenMarkoff.Symmetric.Endgame

open GenMarkoff BGS.Markoff

noncomputable section

private theorem two_ne_zero_zmod_of_prime_ne_two
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
  have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
  exact hpTwo (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)

/-- Candidate regularity forces the symmetric surface multiplier to be
nonzero, since it is a factor of the nonzero normalized weight product. -/
theorem multiplier_ne_zero_of_candidateRegular
    {K : Type*} [Field K] (c u t : K) (htrace : t = trace c u)
    (hregular : OrderedTraceCandidateRegular c c c t) :
    multiplier c ≠ 0 := by
  intro hzero
  apply MiddleGame.actualSigma_ne_zero_of_candidateRegular
    c u t htrace hregular
  change multiplier c * (multiplier c * centeredFiberProduct c u t) = 0
  rw [hzero]
  simp

/-- Primitive split trace coincidences for the normalized parameters of an
actual candidate-regular symmetric fiber. -/
noncomputable abbrev actualSplitPrimitiveTraceSolutions
    (p : ℕ) [Fact p.Prime]
    (c u t : ZMod p) (orbitExponent : ℕ) :=
  shiftedSplitPrimitiveTraceSolutions p
    (actualSigma c u t) (actualGamma c u t) orbitExponent

/-- The actual split primitive count has the expected Möbius main term and
the divisor-count accumulation of the uniform shifted Weil error. -/
theorem actualSplitPrimitiveTraceSolutions_card_error_le
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ) (hWeil : ShiftedTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (c u t : ZMod p) (htrace : t = trace c u) (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (orbitExponent : ℕ) (horbitPositive : 0 < orbitExponent)
    (horbitChar : (orbitExponent : ZMod p) ≠ 0)
    (horbitDvd : orbitExponent ∣ Nat.card (ZMod p)ˣ) :
    |((actualSplitPrimitiveTraceSolutions
        p c u t orbitExponent).card : ℝ) -
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p orbitExponent| ≤
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) := by
  exact shiftedSplitPrimitiveTraceSolutions_card_error_le
    p coefficient hWeil (actualSigma c u t) (actualGamma c u t)
      orbitExponent
      (two_ne_zero_zmod_of_prime_ne_two p hpTwo)
      (MiddleGame.actualSigma_ne_zero_of_candidateRegular
        c u t htrace hregular)
      (MiddleGame.actualSigma_ne_one_of_candidateRegular
        c u t htrace hregular)
      (MiddleGame.actualEvenObstruction_ne_zero_of_candidateRegular
        c u t htrace hc hregular)
      horbitPositive horbitChar horbitDvd

/-- Under the explicit BGS domination inequality, an actual normalized split
fiber has a trace coincidence with a primitive ground-field unit. -/
theorem exists_actualSplitPrimitiveTracePair_of_explicitInequality
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ) (hWeil : ShiftedTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (c u t : ZMod p) (htrace : t = trace c u) (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (orbitExponent : ℕ) (horbitPositive : 0 < orbitExponent)
    (horbitChar : (orbitExponent : ZMod p) ≠ 0)
    (horbitDvd : orbitExponent ∣ Nat.card (ZMod p)ˣ)
    (hexplicit :
      (orbitExponent : ℝ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p) :
    ∃ z : (powMonoidHom orbitExponent :
        (ZMod p)ˣ →* (ZMod p)ˣ).range × (ZMod p)ˣ,
      shiftedWeightedSplitTorusTrace (ZMod p)
          (actualSigma c u t) (actualGamma c u t) z.1 =
          splitTorusTrace z.2 ∧
        orderOf z.2 = Nat.card (ZMod p)ˣ := by
  exact exists_shiftedSplitPrimitiveTracePair_of_explicitInequality
    p coefficient hWeil (actualSigma c u t) (actualGamma c u t)
      orbitExponent
      (two_ne_zero_zmod_of_prime_ne_two p hpTwo)
      (MiddleGame.actualSigma_ne_zero_of_candidateRegular
        c u t htrace hregular)
      (MiddleGame.actualSigma_ne_one_of_candidateRegular
        c u t htrace hregular)
      (MiddleGame.actualEvenObstruction_ne_zero_of_candidateRegular
        c u t htrace hc hregular)
      horbitPositive horbitChar horbitDvd hexplicit

/-- Split-fiber geometric form of the primitive witness.  The produced point
lies on the symmetric surface and its normalized parameter is in the chosen
power image.  No assertion is made that an already chosen global orbit reaches
this point. -/
theorem exists_actualSplitFiberPoint_with_primitiveAdjacentTrace
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ) (hWeil : ShiftedTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (c u t : ZMod p) (q : (ZMod p)ˣ)
    (htrace : t = trace c u) (heigen : t = splitTorusTrace q)
    (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (orbitExponent : ℕ) (horbitPositive : 0 < orbitExponent)
    (horbitChar : (orbitExponent : ZMod p) ≠ 0)
    (horbitDvd : orbitExponent ∣ Nat.card (ZMod p)ˣ)
    (hexplicit :
      (orbitExponent : ℝ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p) :
    ∃ h k : (ZMod p)ˣ,
      MiddleGame.actualAlphaUnit c
          (multiplier_ne_zero_of_candidateRegular c u t htrace hregular) * h ∈
          (powMonoidHom orbitExponent :
            (ZMod p)ˣ →* (ZMod p)ˣ).range ∧
      IsSolution (coefficients c)
        (fiberPoint c u t (q : ZMod p) (h : ZMod p)) ∧
      trace c (fiberPoint c u t (q : ZMod p) (h : ZMod p)).x2 =
          splitTorusTrace k ∧
      orderOf k = Nat.card (ZMod p)ˣ := by
  have hmultiplier : multiplier c ≠ 0 :=
    multiplier_ne_zero_of_candidateRegular c u t htrace hregular
  obtain ⟨z, hztrace, hzorder⟩ :=
    exists_actualSplitPrimitiveTracePair_of_explicitInequality
      p coefficient hWeil hpTwo c u t htrace hc hregular orbitExponent
      horbitPositive horbitChar horbitDvd hexplicit
  let H : (ZMod p)ˣ := z.1
  let h : (ZMod p)ˣ :=
    (MiddleGame.actualAlphaUnit c hmultiplier)⁻¹ * H
  let k : (ZMod p)ˣ := z.2
  have hnormalize :
      MiddleGame.actualAlphaUnit c hmultiplier * h = H := by
    simp [h]
  have hrange :
      MiddleGame.actualAlphaUnit c hmultiplier * h ∈
        (powMonoidHom orbitExponent :
          (ZMod p)ˣ →* (ZMod p)ˣ).range := by
    rw [hnormalize]
    exact z.1.2
  have hdiscriminant : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have heigen' : t = (q : ZMod p) + (q : ZMod p)⁻¹ := by
    simpa only [splitTorusTrace, Units.val_inv_eq_inv_val] using heigen
  have hsolution :=
    fiberPoint_isSolution c u t (q : ZMod p) (h : ZMod p)
      (Units.ne_zero q) (Units.ne_zero h) heigen' htrace hdiscriminant
  have hactualTrace :
      shiftedWeightedSplitTorusTrace (ZMod p)
          (actualSigma c u t) (actualGamma c u t) H =
        trace c (fiberPoint c u t (q : ZMod p) (h : ZMod p)).x2 := by
    rw [← hnormalize]
    exact MiddleGame.shiftedWeightedTrace_normalizedParameter_eq_trace_fiberPoint_x2
      c u t (q : ZMod p) h hmultiplier
  refine ⟨h, k, ?_, hsolution, ?_, hzorder⟩
  · simpa only using hrange
  · exact hactualTrace.symm.trans hztrace

end

end GenMarkoff.Symmetric.Endgame
