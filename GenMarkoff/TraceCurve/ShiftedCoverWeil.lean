import GenMarkoff.TraceCurve.ShiftedCoverResidueBlocks
import BGS.HasseWeil.GeneralBivariateAffineHasseWeil
import BGS.Markoff.Endgame.WeilFromGeneralHasse

/-!
# Affine Hasse--Weil adapter for shifted trace covers

The shifted cover has the same rectangular bidegree and the same single
affine boundary point as the unshifted BGS cover.  This module proves those
two facts directly and applies the generic affine Hasse--Weil theorem.  The
absolute-irreducibility hypothesis remains visible; a later theorem can
discharge it using the shifted Kummer tower.
-/

namespace GenMarkoff

open Polynomial

noncomputable section

section Degrees

variable {K : Type*} [Field K]

private theorem shiftedCover_degreeOf_first_monomial_le
    (a b : ℕ) (r : K) :
    MvPolynomial.degreeOf (0 : Fin 2)
        (MvPolynomial.C r * MvPolynomial.X 0 ^ a *
          MvPolynomial.X 1 ^ b) ≤ a := by
  calc
    _ ≤ MvPolynomial.degreeOf (0 : Fin 2)
          (MvPolynomial.C r * MvPolynomial.X 0 ^ a) +
        MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 1 ^ b) :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ (MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.C r) +
          MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 0 ^ a)) +
        MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 1 ^ b) := by
      gcongr
      exact MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ a := by
      have ha : MvPolynomial.degreeOf (0 : Fin 2)
          (MvPolynomial.X 0 ^ a : MvPolynomial (Fin 2) K) ≤ a := by
        calc
          _ ≤ a * MvPolynomial.degreeOf (0 : Fin 2)
              (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) :=
            MvPolynomial.degreeOf_pow_le _ _ _
          _ = a := by rw [MvPolynomial.degreeOf_X]; norm_num
      have hb : MvPolynomial.degreeOf (0 : Fin 2)
          (MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) K) ≤ 0 := by
        calc
          _ ≤ b * MvPolynomial.degreeOf (0 : Fin 2)
              (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) :=
            MvPolynomial.degreeOf_pow_le _ _ _
          _ = 0 := by rw [MvPolynomial.degreeOf_X]; norm_num
      rw [MvPolynomial.degreeOf_C]
      omega

private theorem shiftedCover_degreeOf_second_monomial_le
    (a b : ℕ) (r : K) :
    MvPolynomial.degreeOf (1 : Fin 2)
        (MvPolynomial.C r * MvPolynomial.X 0 ^ a *
          MvPolynomial.X 1 ^ b) ≤ b := by
  calc
    _ ≤ MvPolynomial.degreeOf (1 : Fin 2)
          (MvPolynomial.C r * MvPolynomial.X 0 ^ a) +
        MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 1 ^ b) :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ (MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.C r) +
          MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 0 ^ a)) +
        MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 1 ^ b) := by
      gcongr
      exact MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ b := by
      have ha : MvPolynomial.degreeOf (1 : Fin 2)
          (MvPolynomial.X 0 ^ a : MvPolynomial (Fin 2) K) ≤ 0 := by
        calc
          _ ≤ a * MvPolynomial.degreeOf (1 : Fin 2)
              (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) :=
            MvPolynomial.degreeOf_pow_le _ _ _
          _ = 0 := by rw [MvPolynomial.degreeOf_X]; norm_num
      have hb : MvPolynomial.degreeOf (1 : Fin 2)
          (MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) K) ≤ b := by
        calc
          _ ≤ b * MvPolynomial.degreeOf (1 : Fin 2)
              (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) :=
            MvPolynomial.degreeOf_pow_le _ _ _
          _ = b := by rw [MvPolynomial.degreeOf_X]; norm_num
      rw [MvPolynomial.degreeOf_C]
      omega

theorem weightedShiftedTraceCoverPolynomial_degreeOf_first_le
    (alpha beta gamma : K) (d e : ℕ) :
    MvPolynomial.degreeOf (0 : Fin 2)
      (shiftedTraceCoverPolynomial alpha beta gamma d e) ≤ 2 * d := by
  unfold shiftedTraceCoverPolynomial
  refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
        · simpa using
            (shiftedCover_degreeOf_first_monomial_le d (2 * e) alpha).trans
              (show d ≤ 2 * d by omega)
        · simpa using
            (shiftedCover_degreeOf_first_monomial_le d 0 beta).trans
              (show d ≤ 2 * d by omega)
      · simpa using
          (shiftedCover_degreeOf_first_monomial_le d e gamma).trans
            (show d ≤ 2 * d by omega)
    · simpa using
        (shiftedCover_degreeOf_first_monomial_le (2 * d) e (1 : K))
  · simpa using
      (shiftedCover_degreeOf_first_monomial_le 0 e (1 : K)).trans
        (show 0 ≤ 2 * d by omega)

theorem shiftedTraceCoverPolynomial_degreeOf_first_le
    (sigma gamma : K) (d e : ℕ) :
    MvPolynomial.degreeOf (0 : Fin 2)
      (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e) ≤ 2 * d :=
  weightedShiftedTraceCoverPolynomial_degreeOf_first_le
    (1 : K) sigma gamma d e

theorem weightedShiftedTraceCoverPolynomial_degreeOf_second_le
    (alpha beta gamma : K) (d e : ℕ) :
    MvPolynomial.degreeOf (1 : Fin 2)
      (shiftedTraceCoverPolynomial alpha beta gamma d e) ≤ 2 * e := by
  unfold shiftedTraceCoverPolynomial
  refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
        · simpa using
            shiftedCover_degreeOf_second_monomial_le d (2 * e) alpha
        · simpa using
            (shiftedCover_degreeOf_second_monomial_le d 0 beta).trans
              (show 0 ≤ 2 * e by omega)
      · simpa using
          (shiftedCover_degreeOf_second_monomial_le d e gamma).trans
            (show e ≤ 2 * e by omega)
    · simpa using
        (shiftedCover_degreeOf_second_monomial_le (2 * d) e (1 : K)).trans
          (show e ≤ 2 * e by omega)
  · simpa using
      (shiftedCover_degreeOf_second_monomial_le 0 e (1 : K)).trans
        (show e ≤ 2 * e by omega)

theorem shiftedTraceCoverPolynomial_degreeOf_second_le
    (sigma gamma : K) (d e : ℕ) :
    MvPolynomial.degreeOf (1 : Fin 2)
      (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e) ≤ 2 * e :=
  weightedShiftedTraceCoverPolynomial_degreeOf_second_le
    (1 : K) sigma gamma d e

theorem weightedShiftedTraceCoverPolynomial_hasBidegreeAtMost
    (alpha beta gamma : K) (d e : ℕ) :
    BGS.External.HasBidegreeAtMost
      (shiftedTraceCoverPolynomial alpha beta gamma d e)
      (2 * d) (2 * e) := by
  intro monomial hmonomial
  exact ⟨
    (MvPolynomial.degreeOf_le_iff.mp
      (weightedShiftedTraceCoverPolynomial_degreeOf_first_le
        alpha beta gamma d e))
        monomial hmonomial,
    (MvPolynomial.degreeOf_le_iff.mp
      (weightedShiftedTraceCoverPolynomial_degreeOf_second_le
        alpha beta gamma d e))
        monomial hmonomial⟩

theorem shiftedTraceCoverPolynomial_hasBidegreeAtMost
    (sigma gamma : K) (d e : ℕ) :
    BGS.External.HasBidegreeAtMost
      (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e)
      (2 * d) (2 * e) :=
  weightedShiftedTraceCoverPolynomial_hasBidegreeAtMost
    (1 : K) sigma gamma d e

end Degrees

section Boundary

variable {K : Type*} [Field K]

theorem weightedShiftedTraceCoverPolynomial_axis_zero_eq_origin
    (alpha beta gamma : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hbeta : beta ≠ 0) (x y : K)
    (hzero : MvPolynomial.eval ![x, y]
      (shiftedTraceCoverPolynomial alpha beta gamma d e) = 0)
    (haxis : x = 0 ∨ y = 0) :
    x = 0 ∧ y = 0 := by
  rw [eval_shiftedTraceCoverPolynomial] at hzero
  have htwoD : 2 * d ≠ 0 := by omega
  have htwoE : 2 * e ≠ 0 := by omega
  rcases haxis with rfl | rfl
  · constructor
    · rfl
    · have hyPow : y ^ e = 0 := by
        have hneg : -(y ^ e) = 0 := by
          simpa only [zero_pow hd.ne', zero_pow htwoD, zero_mul, mul_zero,
            add_zero, sub_zero, zero_sub] using hzero
        exact neg_eq_zero.mp hneg
      exact (pow_eq_zero_iff he.ne').mp hyPow
  · constructor
    · have hxPow : x ^ d = 0 := by
        have hbetaPow : beta * x ^ d = 0 := by
          simpa only [zero_pow he.ne', zero_pow htwoE, mul_zero,
            add_zero, sub_zero, zero_add] using hzero
        exact (mul_eq_zero.mp hbetaPow).resolve_left hbeta
      exact (pow_eq_zero_iff hd.ne').mp hxPow
    · rfl

theorem shiftedTraceCoverPolynomial_axis_zero_eq_origin
    (sigma gamma : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hsigma : sigma ≠ 0) (x y : K)
    (hzero : MvPolynomial.eval ![x, y]
      (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e) = 0)
    (haxis : x = 0 ∨ y = 0) :
    x = 0 ∧ y = 0 :=
  weightedShiftedTraceCoverPolynomial_axis_zero_eq_origin
    (1 : K) sigma gamma d e hd he hsigma x y hzero haxis

theorem weightedShiftedTraceCoverPolynomial_origin_zero
    (alpha beta gamma : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    MvPolynomial.eval ![(0 : K), (0 : K)]
      (shiftedTraceCoverPolynomial alpha beta gamma d e) = 0 := by
  rw [eval_shiftedTraceCoverPolynomial]
  have htwoD : 2 * d ≠ 0 := by omega
  have htwoE : 2 * e ≠ 0 := by omega
  simp only [zero_pow hd.ne', zero_pow he.ne', zero_pow htwoD,
    zero_pow htwoE, mul_zero, add_zero, sub_zero]

theorem shiftedTraceCoverPolynomial_origin_zero
    (sigma gamma : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    MvPolynomial.eval ![(0 : K), (0 : K)]
      (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e) = 0 :=
  weightedShiftedTraceCoverPolynomial_origin_zero
    (1 : K) sigma gamma d e hd he

end Boundary

section FiniteCount

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

/-- Torus-valued zeros of the shifted power cover. -/
noncomputable def shiftedTraceCurveSolutions
    (sigma gamma : K) (d e : ℕ) : Finset (Kˣ × Kˣ) := by
  classical
  exact Finset.univ.filter fun z =>
    MvPolynomial.eval ![(z.1 : K), (z.2 : K)]
      (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e) = 0

@[simp]
theorem mem_shiftedTraceCurveSolutions_iff
    (sigma gamma : K) (d e : ℕ) (z : Kˣ × Kˣ) :
    z ∈ shiftedTraceCurveSolutions K sigma gamma d e ↔
      MvPolynomial.eval ![(z.1 : K), (z.2 : K)]
        (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e) = 0 := by
  classical
  simp [shiftedTraceCurveSolutions]

/-- The affine shifted cover consists of its torus solutions and the single
boundary point `(0,0)`. -/
theorem affineShiftedTraceCoverZeros_card_eq_solutions_card_add_one
    (sigma gamma : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hsigma : sigma ≠ 0) :
    (BGS.External.affinePlaneCurveZeros K
      (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e)).card =
      (shiftedTraceCurveSolutions K sigma gamma d e).card + 1 := by
  classical
  let A := BGS.External.affinePlaneCurveZeros K
    (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e)
  have horigin : ((0, 0) : K × K) ∈ A := by
    rw [BGS.External.mem_affinePlaneCurveZeros_iff]
    exact shiftedTraceCoverPolynomial_origin_zero sigma gamma d e hd he
  have herase : A.erase ((0, 0) : K × K) =
      (shiftedTraceCurveSolutions K sigma gamma d e).image
        (fun z => ((z.1 : K), (z.2 : K))) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro ⟨hzne, hz⟩
      have hz' : MvPolynomial.eval ![z.1, z.2]
          (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e) = 0 := by
        simpa [A] using hz
      have hcoords : z.1 ≠ 0 ∧ z.2 ≠ 0 := by
        constructor
        · intro hx
          apply hzne
          apply Prod.ext hx
          exact (shiftedTraceCoverPolynomial_axis_zero_eq_origin
            sigma gamma d e hd he hsigma z.1 z.2 hz' (Or.inl hx)).2
        · intro hy
          apply hzne
          apply Prod.ext
          · exact (shiftedTraceCoverPolynomial_axis_zero_eq_origin
              sigma gamma d e hd he hsigma z.1 z.2 hz' (Or.inr hy)).1
          · exact hy
      let ux : Kˣ := Units.mk0 z.1 hcoords.1
      let uy : Kˣ := Units.mk0 z.2 hcoords.2
      refine ⟨(ux, uy), ?_, ?_⟩
      · rw [mem_shiftedTraceCurveSolutions_iff]
        simpa [ux, uy] using hz'
      · simp [ux, uy]
    · rintro ⟨u, hu, rfl⟩
      rw [mem_shiftedTraceCurveSolutions_iff] at hu
      refine ⟨?_, ?_⟩
      · intro hzero
        exact u.1.ne_zero (congrArg Prod.fst hzero)
      · simpa [A] using hu
  have himageCard :
      ((shiftedTraceCurveSolutions K sigma gamma d e).image
        (fun z => ((z.1 : K), (z.2 : K)))).card =
        (shiftedTraceCurveSolutions K sigma gamma d e).card := by
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
    _ = (shiftedTraceCurveSolutions K sigma gamma d e).card + 1 := by
      rw [herase, himageCard]

end FiniteCount

section HasseWeil

/-- Uniform affine point-count interface for every shifted power cover. -/
def ShiftedTraceWeilBoundAssumption (coefficient : ℕ) : Prop :=
  0 < coefficient ∧
    ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K]
      (sigma gamma : K) (d e : ℕ),
      sigma ≠ 0 →
      0 < d →
      0 < e →
      Irreducible
        (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
          (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e)) →
      |((shiftedTraceCurveSolutions K sigma gamma d e).card : ℝ) -
          (Fintype.card K : ℝ)| ≤
        (coefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ) *
          (d : ℝ) * (e : ℝ)

/-- Apply the uniform shifted-cover estimate after supplying the concrete
absolute-irreducibility theorem. -/
theorem shiftedTraceCurveSolutions_count_error_le_of_weilBoundAssumption
    (coefficient : ℕ) (hWeil : ShiftedTraceWeilBoundAssumption coefficient)
    (K : Type) [Field K] [Fintype K] [DecidableEq K]
    (sigma gamma : K) (d e : ℕ) (hsigma : sigma ≠ 0)
    (hd : 0 < d) (he : 0 < e)
    (hirreducible :
      Irreducible
        (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
          (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e))) :
    |((shiftedTraceCurveSolutions K sigma gamma d e).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      (coefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ) *
        (d : ℝ) * (e : ℝ) :=
  hWeil.2 K sigma gamma d e hsigma hd he hirreducible

/-- Endgame-ready shifted-cover estimate.  The arbitrary-exponent Kummer
theorem discharges absolute irreducibility from the actual shifted
nondegeneracy and prime-to-characteristic hypotheses. -/
theorem shiftedTraceCurveSolutions_count_error_le_of_weilBoundAssumption_and_positiveExponents
    (coefficient : ℕ) (hWeil : ShiftedTraceWeilBoundAssumption coefficient)
    (K : Type) [Field K] [Fintype K] [DecidableEq K]
    (sigma gamma : K) (d e : ℕ)
    (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0) (hsigmaOne : sigma ≠ 1)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0)
    (hd : 0 < d) (he : 0 < e) (heChar : (e : K) ≠ 0) :
    |((shiftedTraceCurveSolutions K sigma gamma d e).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      (coefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ) *
        (d : ℝ) * (e : ℝ) := by
  apply shiftedTraceCurveSolutions_count_error_le_of_weilBoundAssumption
    coefficient hWeil K sigma gamma d e hsigma hd he
  exact shiftedTraceCoverPolynomial_absolutelyIrreducible_of_positiveExponents
    sigma gamma h2 hsigma hsigmaOne hD2 e d he heChar hd

/-- The generic affine Hasse--Weil theorem gives a uniform shifted-cover
estimate; the unique affine boundary point is absorbed into the coefficient. -/
theorem exists_shiftedTraceWeilBoundAssumption_of_generalHasseWeil
    (hHasse : BGS.External.GeneralBivariateAffineHasseWeilTheorem) :
    ∃ coefficient : ℕ, ShiftedTraceWeilBoundAssumption coefficient := by
  obtain ⟨generalCoefficient, hgeneralPositive, hgeneral⟩ := hHasse
  refine ⟨4 * generalCoefficient + 1, ?_, ?_⟩
  · omega
  · intro K _ _ _ sigma gamma d e hsigma hd he hirreducible
    have hAffine := hgeneral K
      (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e)
      (2 * d) (2 * e) (by omega) (by omega)
      (shiftedTraceCoverPolynomial_hasBidegreeAtMost sigma gamma d e)
      hirreducible
    have hcardNat := affineShiftedTraceCoverZeros_card_eq_solutions_card_add_one
      K sigma gamma d e hd he hsigma
    have hcardReal :
        ((BGS.External.affinePlaneCurveZeros K
          (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e)).card : ℝ) =
          (shiftedTraceCurveSolutions K sigma gamma d e).card + 1 := by
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
            (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e)).card : ℝ) -
            (Fintype.card K : ℝ)| ≤
          4 * (generalCoefficient : ℝ) * x := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hAffine
      convert hAffine using 1
      all_goals
        dsimp [x]
        ring
    have herrorIdentity :
        ((shiftedTraceCurveSolutions K sigma gamma d e).card : ℝ) -
            (Fintype.card K : ℝ) =
          (((BGS.External.affinePlaneCurveZeros K
            (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e)).card : ℝ) -
              (Fintype.card K : ℝ)) - 1 := by
      rw [hcardReal]
      ring
    rw [herrorIdentity]
    calc
      |(((BGS.External.affinePlaneCurveZeros K
          (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e)).card : ℝ) -
            (Fintype.card K : ℝ)) - 1| ≤
          |((BGS.External.affinePlaneCurveZeros K
            (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e)).card : ℝ) -
              (Fintype.card K : ℝ)| + 1 := by
        simpa using abs_sub
          (((BGS.External.affinePlaneCurveZeros K
            (shiftedTraceCoverPolynomial (1 : K) sigma gamma d e)).card : ℝ) -
              (Fintype.card K : ℝ)) (1 : ℝ)
      _ ≤ 4 * (generalCoefficient : ℝ) * x + 1 := by gcongr
      _ ≤ ((4 * generalCoefficient + 1 : ℕ) : ℝ) * x := by
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
        nlinarith
      _ = ((4 * generalCoefficient + 1 : ℕ) : ℝ) *
          Real.sqrt (Fintype.card K : ℝ) * (d : ℝ) * (e : ℝ) := by
        dsimp [x]
        ring

/-- Unconditional uniform shifted-cover Hasse--Weil estimate, obtained from
the in-repository general affine plane-curve theorem in pinned BGS. -/
theorem exists_shiftedTraceWeilBoundAssumption :
    ∃ coefficient : ℕ, ShiftedTraceWeilBoundAssumption coefficient :=
  exists_shiftedTraceWeilBoundAssumption_of_generalHasseWeil
    BGS.HasseWeil.generalBivariateAffineHasseWeilTheorem

end HasseWeil

end

end GenMarkoff
