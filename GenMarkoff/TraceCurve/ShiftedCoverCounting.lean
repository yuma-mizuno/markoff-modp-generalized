import GenMarkoff.TraceCurve.ShiftedCoverWeil
import BGS.Markoff.Endgame.PrimitiveInclusionExclusion

/-!
# Counting shifted trace power covers

This module connects the shifted trace-cover polynomial to the generic
power-map counting and Möbius-inversion machinery from BGS.  Everything here
is split: both torus parameters are units of the ground field.  No statement
about norm-one tori or descent from a quadratic extension is made.
-/

namespace GenMarkoff

open BGS.Markoff

noncomputable section

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

/-- The normalized weighted trace with the affine shift retained. -/
def shiftedWeightedSplitTorusTrace (sigma gamma : K) (w : Kˣ) : K :=
  weightedSplitTorusTrace 1 sigma w + gamma

/-- A torus zero of the shifted cover is exactly a coincidence between the
ordinary trace of the first powered coordinate and the shifted weighted trace
of the second powered coordinate. -/
theorem eval_shiftedTraceCoverPolynomial_eq_zero_iff_traceEquation
    (sigma gamma : K) (d e : ℕ) (x y : Kˣ) :
    MvPolynomial.eval ![(x : K), (y : K)]
        (shiftedTraceCoverPolynomial 1 sigma gamma d e) = 0 ↔
      shiftedWeightedSplitTorusTrace K sigma gamma (y ^ e) =
        splitTorusTrace (x ^ d) := by
  rw [eval_shiftedTraceCoverPolynomial]
  simp only [shiftedWeightedSplitTorusTrace, weightedSplitTorusTrace,
    splitTorusTrace, Units.val_pow_eq_pow_val, one_mul,
    Units.val_inv_eq_inv_val]
  have hx : (x : K) ^ d ≠ 0 := pow_ne_zero d x.ne_zero
  have hy : (y : K) ^ e ≠ 0 := pow_ne_zero e y.ne_zero
  have hxTwo : (x : K) ^ (2 * d) = ((x : K) ^ d) ^ 2 := by
    simpa [Nat.mul_comm] using (pow_mul (x : K) d 2)
  have hyTwo : (y : K) ^ (2 * e) = ((y : K) ^ e) ^ 2 := by
    simpa [Nat.mul_comm] using (pow_mul (y : K) e 2)
  rw [hxTwo, hyTwo]
  field_simp [hx, hy]
  constructor <;> intro h <;> linear_combination h

/-- The two power-map images occurring in the shifted split trace equation. -/
abbrev shiftedTracePowerRangeSolutions
    (sigma gamma : K) (d e : ℕ) :=
  powerTraceRangeSolutions
    (splitTorusTrace : Kˣ → K)
    (shiftedWeightedSplitTorusTrace K sigma gamma) d e

/-- The shifted polynomial solution finset is the generic two-power cover
solution type. -/
def shiftedTraceCurveSolutionsEquivPowerTraceCoverSolutions
    (sigma gamma : K) (d e : ℕ) :
    ↑(shiftedTraceCurveSolutions K sigma gamma d e) ≃
      powerTraceCoverSolutions
        (splitTorusTrace : Kˣ → K)
        (shiftedWeightedSplitTorusTrace K sigma gamma) d e where
  toFun z := ⟨z.1,
    (eval_shiftedTraceCoverPolynomial_eq_zero_iff_traceEquation
      K sigma gamma d e z.1.1 z.1.2).mp
      ((mem_shiftedTraceCurveSolutions_iff
        K sigma gamma d e z.1).mp z.2) |>.symm⟩
  invFun z := ⟨z.1,
    (mem_shiftedTraceCurveSolutions_iff K sigma gamma d e z.1).mpr
      ((eval_shiftedTraceCoverPolynomial_eq_zero_iff_traceEquation
        K sigma gamma d e z.1.1 z.1.2).mpr z.2.symm)⟩
  left_inv z := by rfl
  right_inv z := by rfl

/-- Exact power-cover multiplicity for the shifted split equation. -/
theorem shiftedTraceCurveSolutions_card_eq_mul_natCard_powerTraceRangeSolutions
    (sigma gamma : K) (d e : ℕ)
    (hdvd : d ∣ Nat.card Kˣ) (hedvd : e ∣ Nat.card Kˣ) :
    (shiftedTraceCurveSolutions K sigma gamma d e).card =
      d * e * Nat.card (shiftedTracePowerRangeSolutions K sigma gamma d e) := by
  calc
    (shiftedTraceCurveSolutions K sigma gamma d e).card =
        Nat.card ↑(shiftedTraceCurveSolutions K sigma gamma d e) := by
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_coe _).symm
    _ = Nat.card
        (powerTraceCoverSolutions
          (splitTorusTrace : Kˣ → K)
          (shiftedWeightedSplitTorusTrace K sigma gamma) d e) :=
      Nat.card_congr
        (shiftedTraceCurveSolutionsEquivPowerTraceCoverSolutions
          K sigma gamma d e)
    _ = d * e * Nat.card
        (shiftedTracePowerRangeSolutions K sigma gamma d e) :=
      natCard_powerTraceCoverSolutions_of_dvd
        (splitTorusTrace : Kˣ → K)
        (shiftedWeightedSplitTorusTrace K sigma gamma) d e hdvd hedvd

/-- Dividing the shifted Hasse--Weil estimate by the exact cover
multiplicity gives the uniform range-count error used by inclusion--exclusion. -/
theorem shiftedTracePowerRangeSolutions_count_error_le
    (coefficient : ℕ) (hWeil : ShiftedTraceWeilBoundAssumption coefficient)
    (sigma gamma : K) (d e : ℕ)
    (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) (hsigmaOne : sigma ≠ 1)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0)
    (hd : 0 < d) (he : 0 < e) (heChar : (e : K) ≠ 0)
    (hdvd : d ∣ Nat.card Kˣ) (hedvd : e ∣ Nat.card Kˣ) :
    |(Nat.card (shiftedTracePowerRangeSolutions K sigma gamma d e) : ℝ) -
        (Fintype.card K : ℝ) / ((d : ℝ) * (e : ℝ))| ≤
      (coefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ) := by
  apply rangeCount_error_le_of_coverCount_error_and_exactMultiplicity
    (shiftedTraceCurveSolutions K sigma gamma d e).card
    (Nat.card (shiftedTracePowerRangeSolutions K sigma gamma d e))
    (Fintype.card K) coefficient d e hd he
    (shiftedTraceCurveSolutions_card_eq_mul_natCard_powerTraceRangeSolutions
      K sigma gamma d e hdvd hedvd)
  exact shiftedTraceCurveSolutions_count_error_le_of_weilBoundAssumption_and_positiveExponents
    coefficient hWeil K sigma gamma d e h2 hsigma hsigmaOne hD2 hd he heChar

end

section PrimitiveSplit

/-- Split shifted-trace coincidences whose normalized fiber parameter lies in
one power image and whose ordinary trace parameter is primitive. -/
noncomputable abbrev shiftedSplitPrimitiveTraceSolutions
    (p : ℕ) [Fact p.Prime]
    (sigma gamma : ZMod p) (orbitExponent : ℕ) :=
  traceExactOrderSolutions
    (shiftedWeightedSplitTorusTrace (ZMod p) sigma gamma)
    (splitTorusTrace : (ZMod p)ˣ → ZMod p)
    orbitExponent (Nat.card (ZMod p)ˣ)

/-- Möbius inclusion--exclusion for a shifted split fiber.  The geometry is
used only through `ShiftedTraceWeilBoundAssumption`; the Möbius arithmetic is
the generic BGS theorem. -/
theorem shiftedSplitPrimitiveTraceSolutions_card_error_le
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ) (hWeil : ShiftedTraceWeilBoundAssumption coefficient)
    (sigma gamma : ZMod p) (orbitExponent : ℕ)
    (h2 : (2 : ZMod p) ≠ 0)
    (hsigma : sigma ≠ 0) (hsigmaOne : sigma ≠ 1)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0)
    (horbitPositive : 0 < orbitExponent)
    (horbitChar : (orbitExponent : ZMod p) ≠ 0)
    (horbitDvd : orbitExponent ∣ Nat.card (ZMod p)ˣ) :
    |((shiftedSplitPrimitiveTraceSolutions
        p sigma gamma orbitExponent).card : ℝ) -
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p orbitExponent| ≤
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) := by
  have hRange : ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
      |(Nat.card (powerTraceRangeSolutions
          (shiftedWeightedSplitTorusTrace (ZMod p) sigma gamma)
          (splitTorusTrace : (ZMod p)ˣ → ZMod p)
          orbitExponent d) : ℝ) -
        (p : ℝ) / ((d : ℝ) * (orbitExponent : ℝ))| ≤
          (coefficient : ℝ) * Real.sqrt (p : ℝ) := by
    intro d hdvd hd
    have hestimate :=
      shiftedTracePowerRangeSolutions_count_error_le
        (ZMod p) coefficient hWeil sigma gamma d orbitExponent
        h2 hsigma hsigmaOne hD2 hd horbitPositive horbitChar hdvd horbitDvd
    rw [natCard_powerTraceRangeSolutions_swap
      (shiftedWeightedSplitTorusTrace (ZMod p) sigma gamma)
      (splitTorusTrace : (ZMod p)ˣ → ZMod p) orbitExponent d]
    simpa [ZMod.card] using hestimate
  simpa [shiftedSplitPrimitiveTraceSolutions, primitiveTraceMoebiusMainTerm] using
    traceExactOrderSolutions_card_error_le_moebiusMain
      (shiftedWeightedSplitTorusTrace (ZMod p) sigma gamma)
      (splitTorusTrace : (ZMod p)ˣ → ZMod p)
      orbitExponent
      (fun d => (p : ℝ) / ((d : ℝ) * (orbitExponent : ℝ)))
      ((coefficient : ℝ) * Real.sqrt (p : ℝ)) hRange

/-- The explicit BGS main-term domination inequality produces a primitive
ordinary-trace parameter on the shifted split fiber. -/
theorem exists_shiftedSplitPrimitiveTracePair_of_explicitInequality
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ) (hWeil : ShiftedTraceWeilBoundAssumption coefficient)
    (sigma gamma : ZMod p) (orbitExponent : ℕ)
    (h2 : (2 : ZMod p) ≠ 0)
    (hsigma : sigma ≠ 0) (hsigmaOne : sigma ≠ 1)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0)
    (horbitPositive : 0 < orbitExponent)
    (horbitChar : (orbitExponent : ZMod p) ≠ 0)
    (horbitDvd : orbitExponent ∣ Nat.card (ZMod p)ˣ)
    (hexplicit :
      (orbitExponent : ℝ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p) :
    ∃ z : (powMonoidHom orbitExponent :
        (ZMod p)ˣ →* (ZMod p)ˣ).range × (ZMod p)ˣ,
      shiftedWeightedSplitTorusTrace (ZMod p) sigma gamma z.1 =
          splitTorusTrace z.2 ∧
        orderOf z.2 = Nat.card (ZMod p)ˣ := by
  have hmain :=
    divisorsError_lt_primitiveTraceMoebiusMainTerm_of_explicitInequality
      (Nat.card (ZMod p)ˣ) p orbitExponent coefficient
      Nat.card_pos horbitPositive hexplicit
  have hnonempty :
      (shiftedSplitPrimitiveTraceSolutions
        p sigma gamma orbitExponent).Nonempty := by
    apply finset_nonempty_of_card_error_le_and_error_lt_main
      (shiftedSplitPrimitiveTraceSolutions p sigma gamma orbitExponent)
      (primitiveTraceMoebiusMainTerm
        (Nat.card (ZMod p)ˣ) p orbitExponent)
      (((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)))
    · exact shiftedSplitPrimitiveTraceSolutions_card_error_le
        p coefficient hWeil sigma gamma orbitExponent h2 hsigma hsigmaOne hD2
        horbitPositive horbitChar horbitDvd
    · exact hmain
  obtain ⟨z, hz⟩ := hnonempty
  exact ⟨z, (mem_traceExactOrderSolutions_iff
    (shiftedWeightedSplitTorusTrace (ZMod p) sigma gamma)
    (splitTorusTrace : (ZMod p)ˣ → ZMod p)
    orbitExponent (Nat.card (ZMod p)ˣ) z).mp hz⟩

end PrimitiveSplit

end GenMarkoff
