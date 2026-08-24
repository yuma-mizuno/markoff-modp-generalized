import GenMarkoff.TraceCurve.WeightedShiftedCover
import GenMarkoff.TraceCurve.ShiftedCoverWeil
import BGS.Markoff.Endgame.PrimitiveInclusionExclusion

/-!
# Counting arbitrary-weight shifted trace power covers

The normalized shifted cover has weights `(1, sigma)`.  Actual symmetric
one-step fibers instead produce a translated torus coset with two independent
nonzero weights `(alpha, beta)`.  This module keeps those weights explicit
through the affine Hasse--Weil estimate, exact power-map multiplicity, and
Möbius primitive-trace count.

The algebraic-closure scaling used to prove absolute irreducibility does not
give a finite-field point-count equivalence: its scaling root need not belong
to the ground field.  Consequently the Hasse--Weil adapter below is proved
directly for the arbitrary-weight polynomial.
-/

namespace GenMarkoff

open BGS.Markoff

noncomputable section

section FiniteSolutions

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

/-- Torus-valued zeros of the arbitrary-weight shifted power cover. -/
noncomputable def weightedShiftedTraceCurveSolutions
    (alpha beta gamma : K) (d e : ℕ) : Finset (Kˣ × Kˣ) := by
  classical
  exact Finset.univ.filter fun z =>
    MvPolynomial.eval ![(z.1 : K), (z.2 : K)]
      (shiftedTraceCoverPolynomial alpha beta gamma d e) = 0

@[simp]
theorem mem_weightedShiftedTraceCurveSolutions_iff
    (alpha beta gamma : K) (d e : ℕ) (z : Kˣ × Kˣ) :
    z ∈ weightedShiftedTraceCurveSolutions K alpha beta gamma d e ↔
      MvPolynomial.eval ![(z.1 : K), (z.2 : K)]
        (shiftedTraceCoverPolynomial alpha beta gamma d e) = 0 := by
  classical
  simp [weightedShiftedTraceCurveSolutions]

/-- The affine arbitrary-weight shifted cover consists of its torus solutions
and the single boundary point `(0,0)`. -/
theorem affineWeightedShiftedTraceCoverZeros_card_eq_solutions_card_add_one
    (alpha beta gamma : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hbeta : beta ≠ 0) :
    (BGS.External.affinePlaneCurveZeros K
      (shiftedTraceCoverPolynomial alpha beta gamma d e)).card =
      (weightedShiftedTraceCurveSolutions K alpha beta gamma d e).card + 1 := by
  classical
  let A := BGS.External.affinePlaneCurveZeros K
    (shiftedTraceCoverPolynomial alpha beta gamma d e)
  have horigin : ((0, 0) : K × K) ∈ A := by
    rw [BGS.External.mem_affinePlaneCurveZeros_iff]
    exact weightedShiftedTraceCoverPolynomial_origin_zero
      alpha beta gamma d e hd he
  have herase : A.erase ((0, 0) : K × K) =
      (weightedShiftedTraceCurveSolutions K alpha beta gamma d e).image
        (fun z => ((z.1 : K), (z.2 : K))) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro ⟨hzne, hz⟩
      have hz' : MvPolynomial.eval ![z.1, z.2]
          (shiftedTraceCoverPolynomial alpha beta gamma d e) = 0 := by
        simpa [A] using hz
      have hcoords : z.1 ≠ 0 ∧ z.2 ≠ 0 := by
        constructor
        · intro hx
          apply hzne
          apply Prod.ext hx
          exact
            (weightedShiftedTraceCoverPolynomial_axis_zero_eq_origin
              alpha beta gamma d e hd he hbeta z.1 z.2 hz'
                (Or.inl hx)).2
        · intro hy
          apply hzne
          apply Prod.ext
          · exact
              (weightedShiftedTraceCoverPolynomial_axis_zero_eq_origin
                alpha beta gamma d e hd he hbeta z.1 z.2 hz'
                  (Or.inr hy)).1
          · exact hy
      let ux : Kˣ := Units.mk0 z.1 hcoords.1
      let uy : Kˣ := Units.mk0 z.2 hcoords.2
      refine ⟨(ux, uy), ?_, ?_⟩
      · rw [mem_weightedShiftedTraceCurveSolutions_iff]
        simpa [ux, uy] using hz'
      · simp [ux, uy]
    · rintro ⟨u, hu, rfl⟩
      rw [mem_weightedShiftedTraceCurveSolutions_iff] at hu
      refine ⟨?_, ?_⟩
      · intro hzero
        exact u.1.ne_zero (congrArg Prod.fst hzero)
      · simpa [A] using hu
  have himageCard :
      ((weightedShiftedTraceCurveSolutions K alpha beta gamma d e).image
        (fun z => ((z.1 : K), (z.2 : K)))).card =
        (weightedShiftedTraceCurveSolutions K alpha beta gamma d e).card := by
    rw [Finset.card_image_iff.mpr]
    intro x _ y _ hxy
    apply Prod.ext
    · apply Units.ext
      exact congrArg Prod.fst hxy
    · apply Units.ext
      exact congrArg Prod.snd hxy
  calc
    A.card = (A.erase ((0, 0) : K × K)).card + 1 :=
      (Finset.card_erase_add_one horigin).symm
    _ = (weightedShiftedTraceCurveSolutions
          K alpha beta gamma d e).card + 1 := by
      rw [herase, himageCard]

end FiniteSolutions

section HasseWeil

/-- Uniform affine point-count interface for arbitrary-weight shifted covers.
The coefficient is independent of the field, all three affine parameters,
and the covering exponents. -/
def WeightedShiftedTraceWeilBoundAssumption (coefficient : ℕ) : Prop :=
  0 < coefficient ∧
    ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K]
      (alpha beta gamma : K) (d e : ℕ),
      alpha ≠ 0 →
      beta ≠ 0 →
      0 < d →
      0 < e →
      Irreducible
        (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
          (shiftedTraceCoverPolynomial alpha beta gamma d e)) →
      |((weightedShiftedTraceCurveSolutions
          K alpha beta gamma d e).card : ℝ) -
          (Fintype.card K : ℝ)| ≤
        (coefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ) *
          (d : ℝ) * (e : ℝ)

/-- Apply the uniform arbitrary-weight estimate after supplying absolute
irreducibility of the concrete cover. -/
theorem weightedShiftedTraceCurveSolutions_count_error_le_of_weilBoundAssumption
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (K : Type) [Field K] [Fintype K] [DecidableEq K]
    (alpha beta gamma : K) (d e : ℕ)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hd : 0 < d) (he : 0 < e)
    (hirreducible :
      Irreducible
        (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
          (shiftedTraceCoverPolynomial alpha beta gamma d e))) :
    |((weightedShiftedTraceCurveSolutions
        K alpha beta gamma d e).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      (coefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ) *
        (d : ℝ) * (e : ℝ) :=
  hWeil.2 K alpha beta gamma d e halpha hbeta hd he hirreducible

/-- Endgame-ready arbitrary-weight estimate.  The weighted shifted Kummer
theorem discharges absolute irreducibility from the invariant product and
even-cover obstruction. -/
theorem weightedShiftedTraceCurveSolutions_count_error_le_of_weilBoundAssumption_and_positiveExponents
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (K : Type) [Field K] [Fintype K] [DecidableEq K]
    (alpha beta gamma : K) (d e : ℕ)
    (h2 : (2 : K) ≠ 0)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hproductOne : alpha * beta ≠ 1)
    (hD2 : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0)
    (hd : 0 < d) (he : 0 < e) (heChar : (e : K) ≠ 0) :
    |((weightedShiftedTraceCurveSolutions
        K alpha beta gamma d e).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      (coefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ) *
        (d : ℝ) * (e : ℝ) := by
  apply
    weightedShiftedTraceCurveSolutions_count_error_le_of_weilBoundAssumption
      coefficient hWeil K alpha beta gamma d e halpha hbeta hd he
  exact
    weightedShiftedTraceCoverPolynomial_absolutelyIrreducible_of_positiveExponents
      alpha beta gamma h2 halpha hbeta hproductOne hD2 e d he heChar hd

/-- A fixed affine Hasse--Weil coefficient gives the corresponding fixed
weighted shifted-cover coefficient. -/
theorem weightedShiftedTraceWeilBoundAssumption_of_bivariateAffineHasseWeilBound
    (generalCoefficient : ℕ) (hgeneralPositive : 0 < generalCoefficient)
    (hgeneral :
      BGS.External.BivariateAffineHasseWeilBound generalCoefficient) :
    WeightedShiftedTraceWeilBoundAssumption
      (4 * generalCoefficient + 1) := by
  refine ⟨?_, ?_⟩
  · omega
  · intro K _ _ _ alpha beta gamma d e _halpha hbeta hd he hirreducible
    have hAffine := hgeneral K
      (shiftedTraceCoverPolynomial alpha beta gamma d e)
      (2 * d) (2 * e) (by omega) (by omega)
      (weightedShiftedTraceCoverPolynomial_hasBidegreeAtMost
        alpha beta gamma d e)
      hirreducible
    have hcardNat :=
      affineWeightedShiftedTraceCoverZeros_card_eq_solutions_card_add_one
        K alpha beta gamma d e hd he hbeta
    have hcardReal :
        ((BGS.External.affinePlaneCurveZeros K
          (shiftedTraceCoverPolynomial alpha beta gamma d e)).card : ℝ) =
          (weightedShiftedTraceCurveSolutions
            K alpha beta gamma d e).card + 1 := by
      exact_mod_cast hcardNat
    let x : ℝ :=
      Real.sqrt (Fintype.card K : ℝ) * (d : ℝ) * (e : ℝ)
    have hcardOne : (1 : ℝ) ≤ (Fintype.card K : ℝ) := by
      have hcardPositive : 0 < Fintype.card K :=
        Fintype.card_pos_iff.mpr ⟨(0 : K)⟩
      exact_mod_cast hcardPositive
    have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (Fintype.card K : ℝ) :=
      Real.one_le_sqrt.mpr hcardOne
    have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have heOne : (1 : ℝ) ≤ e := by exact_mod_cast he
    have hxOne : (1 : ℝ) ≤ x := by
      dsimp [x]
      calc
        (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ Real.sqrt (Fintype.card K : ℝ) * d * e := by gcongr
    have hAffine' :
        |((BGS.External.affinePlaneCurveZeros K
            (shiftedTraceCoverPolynomial alpha beta gamma d e)).card : ℝ) -
            (Fintype.card K : ℝ)| ≤
          4 * (generalCoefficient : ℝ) * x := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hAffine
      convert hAffine using 1
      all_goals
        dsimp [x]
        ring
    have herrorIdentity :
        ((weightedShiftedTraceCurveSolutions
          K alpha beta gamma d e).card : ℝ) -
            (Fintype.card K : ℝ) =
          (((BGS.External.affinePlaneCurveZeros K
            (shiftedTraceCoverPolynomial
              alpha beta gamma d e)).card : ℝ) -
              (Fintype.card K : ℝ)) - 1 := by
      rw [hcardReal]
      ring
    rw [herrorIdentity]
    calc
      |(((BGS.External.affinePlaneCurveZeros K
          (shiftedTraceCoverPolynomial alpha beta gamma d e)).card : ℝ) -
            (Fintype.card K : ℝ)) - 1| ≤
          |((BGS.External.affinePlaneCurveZeros K
            (shiftedTraceCoverPolynomial
              alpha beta gamma d e)).card : ℝ) -
              (Fintype.card K : ℝ)| + 1 := by
        simpa using abs_sub
          (((BGS.External.affinePlaneCurveZeros K
            (shiftedTraceCoverPolynomial
              alpha beta gamma d e)).card : ℝ) -
              (Fintype.card K : ℝ)) (1 : ℝ)
      _ ≤ 4 * (generalCoefficient : ℝ) * x + 1 := by gcongr
      _ ≤ ((4 * generalCoefficient + 1 : ℕ) : ℝ) * x := by
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
        nlinarith
      _ = ((4 * generalCoefficient + 1 : ℕ) : ℝ) *
          Real.sqrt (Fintype.card K : ℝ) * (d : ℝ) * (e : ℝ) := by
        dsimp [x]
        ring

/-- The general affine Hasse--Weil theorem gives a uniform estimate for the
arbitrary-weight shifted family; the unique affine boundary point is absorbed
into the coefficient. -/
theorem exists_weightedShiftedTraceWeilBoundAssumption_of_generalHasseWeil
    (hHasse : BGS.External.GeneralBivariateAffineHasseWeilTheorem) :
    ∃ coefficient : ℕ,
      WeightedShiftedTraceWeilBoundAssumption coefficient := by
  obtain ⟨generalCoefficient, hgeneralPositive, hgeneral⟩ := hHasse
  exact
    ⟨4 * generalCoefficient + 1,
      weightedShiftedTraceWeilBoundAssumption_of_bivariateAffineHasseWeilBound
        generalCoefficient hgeneralPositive hgeneral⟩

/-- Fixed coefficient `33 = 4 * 8 + 1` supplied by the in-repository affine
Hasse--Weil theorem. -/
theorem weightedShiftedTraceWeilBoundAssumption_thirtyThree :
    WeightedShiftedTraceWeilBoundAssumption 33 := by
  simpa using
    weightedShiftedTraceWeilBoundAssumption_of_bivariateAffineHasseWeilBound
      8 (by norm_num)
        BGS.HasseWeil.bivariateAffineHasseWeilBound_eight

/-- Unconditional uniform arbitrary-weight shifted-cover estimate, obtained
from the in-repository general affine plane-curve theorem. -/
theorem exists_weightedShiftedTraceWeilBoundAssumption :
    ∃ coefficient : ℕ,
      WeightedShiftedTraceWeilBoundAssumption coefficient :=
  exists_weightedShiftedTraceWeilBoundAssumption_of_generalHasseWeil
    BGS.HasseWeil.generalBivariateAffineHasseWeilTheorem

end HasseWeil

section PowerCoverCounting

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

/-- The arbitrary weighted trace with its affine shift retained. -/
def weightedShiftedSplitTorusTrace
    (alpha beta gamma : K) (w : Kˣ) : K :=
  weightedSplitTorusTrace alpha beta w + gamma

omit [Fintype K] [DecidableEq K] in
/-- A torus zero of the arbitrary-weight shifted cover is exactly the
corresponding shifted weighted-trace coincidence. -/
theorem eval_weightedShiftedTraceCoverPolynomial_eq_zero_iff_traceEquation
    (alpha beta gamma : K) (d e : ℕ) (x y : Kˣ) :
    MvPolynomial.eval ![(x : K), (y : K)]
        (shiftedTraceCoverPolynomial alpha beta gamma d e) = 0 ↔
      weightedShiftedSplitTorusTrace K alpha beta gamma (y ^ e) =
        splitTorusTrace (x ^ d) := by
  rw [eval_shiftedTraceCoverPolynomial]
  simp only [weightedShiftedSplitTorusTrace, weightedSplitTorusTrace,
    splitTorusTrace, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  have hx : (x : K) ^ d ≠ 0 := pow_ne_zero d x.ne_zero
  have hy : (y : K) ^ e ≠ 0 := pow_ne_zero e y.ne_zero
  have hxTwo : (x : K) ^ (2 * d) = ((x : K) ^ d) ^ 2 := by
    simpa [Nat.mul_comm] using (pow_mul (x : K) d 2)
  have hyTwo : (y : K) ^ (2 * e) = ((y : K) ^ e) ^ 2 := by
    simpa [Nat.mul_comm] using (pow_mul (y : K) e 2)
  rw [hxTwo, hyTwo]
  field_simp [hx, hy]
  constructor <;> intro h <;> linear_combination h

/-- The two power-map images in the arbitrary-weight shifted equation. -/
abbrev weightedShiftedTracePowerRangeSolutions
    (alpha beta gamma : K) (d e : ℕ) :=
  powerTraceRangeSolutions
    (splitTorusTrace : Kˣ → K)
    (weightedShiftedSplitTorusTrace K alpha beta gamma) d e

/-- The arbitrary-weight polynomial solution finset is the generic two-power
cover solution type. -/
def weightedShiftedTraceCurveSolutionsEquivPowerTraceCoverSolutions
    (alpha beta gamma : K) (d e : ℕ) :
    ↑(weightedShiftedTraceCurveSolutions K alpha beta gamma d e) ≃
      powerTraceCoverSolutions
        (splitTorusTrace : Kˣ → K)
        (weightedShiftedSplitTorusTrace K alpha beta gamma) d e where
  toFun z := ⟨z.1,
    (eval_weightedShiftedTraceCoverPolynomial_eq_zero_iff_traceEquation
      K alpha beta gamma d e z.1.1 z.1.2).mp
      ((mem_weightedShiftedTraceCurveSolutions_iff
        K alpha beta gamma d e z.1).mp z.2) |>.symm⟩
  invFun z := ⟨z.1,
    (mem_weightedShiftedTraceCurveSolutions_iff
      K alpha beta gamma d e z.1).mpr
      ((eval_weightedShiftedTraceCoverPolynomial_eq_zero_iff_traceEquation
        K alpha beta gamma d e z.1.1 z.1.2).mpr z.2.symm)⟩
  left_inv z := by rfl
  right_inv z := by rfl

/-- Exact power-cover multiplicity for the arbitrary-weight shifted equation. -/
theorem weightedShiftedTraceCurveSolutions_card_eq_mul_natCard_powerTraceRangeSolutions
    (alpha beta gamma : K) (d e : ℕ)
    (hdvd : d ∣ Nat.card Kˣ) (hedvd : e ∣ Nat.card Kˣ) :
    (weightedShiftedTraceCurveSolutions
      K alpha beta gamma d e).card =
      d * e * Nat.card
        (weightedShiftedTracePowerRangeSolutions
          K alpha beta gamma d e) := by
  calc
    (weightedShiftedTraceCurveSolutions K alpha beta gamma d e).card =
        Nat.card ↑(weightedShiftedTraceCurveSolutions
          K alpha beta gamma d e) := by
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_coe _).symm
    _ = Nat.card
        (powerTraceCoverSolutions
          (splitTorusTrace : Kˣ → K)
          (weightedShiftedSplitTorusTrace K alpha beta gamma) d e) :=
      Nat.card_congr
        (weightedShiftedTraceCurveSolutionsEquivPowerTraceCoverSolutions
          K alpha beta gamma d e)
    _ = d * e * Nat.card
        (weightedShiftedTracePowerRangeSolutions
          K alpha beta gamma d e) :=
      natCard_powerTraceCoverSolutions_of_dvd
        (splitTorusTrace : Kˣ → K)
        (weightedShiftedSplitTorusTrace K alpha beta gamma)
        d e hdvd hedvd

/-- Dividing the arbitrary-weight Hasse--Weil estimate by the exact cover
multiplicity gives the uniform range-count error. -/
theorem weightedShiftedTracePowerRangeSolutions_count_error_le
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (alpha beta gamma : K) (d e : ℕ)
    (h2 : (2 : K) ≠ 0)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hproductOne : alpha * beta ≠ 1)
    (hD2 : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0)
    (hd : 0 < d) (he : 0 < e) (heChar : (e : K) ≠ 0)
    (hdvd : d ∣ Nat.card Kˣ) (hedvd : e ∣ Nat.card Kˣ) :
    |(Nat.card
        (weightedShiftedTracePowerRangeSolutions
          K alpha beta gamma d e) : ℝ) -
        (Fintype.card K : ℝ) / ((d : ℝ) * (e : ℝ))| ≤
      (coefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ) := by
  apply rangeCount_error_le_of_coverCount_error_and_exactMultiplicity
    (weightedShiftedTraceCurveSolutions K alpha beta gamma d e).card
    (Nat.card
      (weightedShiftedTracePowerRangeSolutions K alpha beta gamma d e))
    (Fintype.card K) coefficient d e hd he
    (weightedShiftedTraceCurveSolutions_card_eq_mul_natCard_powerTraceRangeSolutions
      K alpha beta gamma d e hdvd hedvd)
  exact
    weightedShiftedTraceCurveSolutions_count_error_le_of_weilBoundAssumption_and_positiveExponents
      coefficient hWeil K alpha beta gamma d e h2 halpha hbeta
      hproductOne hD2 hd he heChar

end PowerCoverCounting

section PrimitiveSplit

/-- Arbitrary-weight shifted trace coincidences whose weighted coordinate is
in one power image and whose ordinary trace coordinate is primitive. -/
noncomputable abbrev weightedShiftedSplitPrimitiveTraceSolutions
    (p : ℕ) [Fact p.Prime]
    (alpha beta gamma : ZMod p) (orbitExponent : ℕ) :=
  traceExactOrderSolutions
    (weightedShiftedSplitTorusTrace
      (ZMod p) alpha beta gamma)
    (splitTorusTrace : (ZMod p)ˣ → ZMod p)
    orbitExponent (Nat.card (ZMod p)ˣ)

/-- Möbius inclusion--exclusion for an arbitrary-weight shifted split fiber. -/
theorem weightedShiftedSplitPrimitiveTraceSolutions_card_error_le
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (alpha beta gamma : ZMod p) (orbitExponent : ℕ)
    (h2 : (2 : ZMod p) ≠ 0)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hproductOne : alpha * beta ≠ 1)
    (hD2 : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0)
    (horbitPositive : 0 < orbitExponent)
    (horbitChar : (orbitExponent : ZMod p) ≠ 0)
    (horbitDvd : orbitExponent ∣ Nat.card (ZMod p)ˣ) :
    |((weightedShiftedSplitPrimitiveTraceSolutions
        p alpha beta gamma orbitExponent).card : ℝ) -
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p orbitExponent| ≤
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) := by
  have hRange : ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
      |(Nat.card (powerTraceRangeSolutions
          (weightedShiftedSplitTorusTrace
            (ZMod p) alpha beta gamma)
          (splitTorusTrace : (ZMod p)ˣ → ZMod p)
          orbitExponent d) : ℝ) -
        (p : ℝ) / ((d : ℝ) * (orbitExponent : ℝ))| ≤
          (coefficient : ℝ) * Real.sqrt (p : ℝ) := by
    intro d hdvd hd
    have hestimate :=
      weightedShiftedTracePowerRangeSolutions_count_error_le
        (ZMod p) coefficient hWeil alpha beta gamma d orbitExponent
        h2 halpha hbeta hproductOne hD2 hd horbitPositive horbitChar
        hdvd horbitDvd
    rw [natCard_powerTraceRangeSolutions_swap
      (weightedShiftedSplitTorusTrace
        (ZMod p) alpha beta gamma)
      (splitTorusTrace : (ZMod p)ˣ → ZMod p) orbitExponent d]
    simpa [ZMod.card] using hestimate
  simpa [weightedShiftedSplitPrimitiveTraceSolutions,
    primitiveTraceMoebiusMainTerm] using
    traceExactOrderSolutions_card_error_le_moebiusMain
      (weightedShiftedSplitTorusTrace
        (ZMod p) alpha beta gamma)
      (splitTorusTrace : (ZMod p)ˣ → ZMod p)
      orbitExponent
      (fun d => (p : ℝ) / ((d : ℝ) * (orbitExponent : ℝ)))
      ((coefficient : ℝ) * Real.sqrt (p : ℝ)) hRange

/-- The explicit BGS main-term domination inequality produces a primitive
ordinary-trace parameter on the arbitrary-weight shifted split fiber. -/
theorem exists_weightedShiftedSplitPrimitiveTracePair_of_explicitInequality
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (alpha beta gamma : ZMod p) (orbitExponent : ℕ)
    (h2 : (2 : ZMod p) ≠ 0)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hproductOne : alpha * beta ≠ 1)
    (hD2 : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0)
    (horbitPositive : 0 < orbitExponent)
    (horbitChar : (orbitExponent : ZMod p) ≠ 0)
    (horbitDvd : orbitExponent ∣ Nat.card (ZMod p)ˣ)
    (hexplicit :
      (orbitExponent : ℝ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p) :
    ∃ z : (powMonoidHom orbitExponent :
        (ZMod p)ˣ →* (ZMod p)ˣ).range × (ZMod p)ˣ,
      weightedShiftedSplitTorusTrace
          (ZMod p) alpha beta gamma z.1 =
          splitTorusTrace z.2 ∧
        orderOf z.2 = Nat.card (ZMod p)ˣ := by
  have hmain :=
    divisorsError_lt_primitiveTraceMoebiusMainTerm_of_explicitInequality
      (Nat.card (ZMod p)ˣ) p orbitExponent coefficient
      Nat.card_pos horbitPositive hexplicit
  have hnonempty :
      (weightedShiftedSplitPrimitiveTraceSolutions
        p alpha beta gamma orbitExponent).Nonempty := by
    apply finset_nonempty_of_card_error_le_and_error_lt_main
      (weightedShiftedSplitPrimitiveTraceSolutions
        p alpha beta gamma orbitExponent)
      (primitiveTraceMoebiusMainTerm
        (Nat.card (ZMod p)ˣ) p orbitExponent)
      (((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)))
    · exact weightedShiftedSplitPrimitiveTraceSolutions_card_error_le
        p coefficient hWeil alpha beta gamma orbitExponent h2 halpha hbeta
        hproductOne hD2 horbitPositive horbitChar horbitDvd
    · exact hmain
  obtain ⟨z, hz⟩ := hnonempty
  exact ⟨z, (mem_traceExactOrderSolutions_iff
    (weightedShiftedSplitTorusTrace
      (ZMod p) alpha beta gamma)
    (splitTorusTrace : (ZMod p)ˣ → ZMod p)
    orbitExponent (Nat.card (ZMod p)ˣ) z).mp hz⟩

end PrimitiveSplit

end

end GenMarkoff
