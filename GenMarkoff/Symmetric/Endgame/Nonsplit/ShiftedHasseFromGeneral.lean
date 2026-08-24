import GenMarkoff.Symmetric.Endgame.Nonsplit.ShiftedDescendedCounting

/-!
# The shifted nonsplit estimate from general affine Hasse--Weil

The descended curve has bidegree `(2d,2e)`.  The Cayley chart omits at most
`2e` points, so a general affine Hasse--Weil coefficient `C` gives the
uniform shifted seeded nonsplit coefficient `4C + 2`.
-/

namespace GenMarkoff.Symmetric.Endgame.Nonsplit

open BGS.Markoff

noncomputable section

/-- Uniform Hasse--Weil estimate for shifted seeded nonsplit covers.  The
irreducibility premise is the scalar-extended arbitrary-weight shifted cover
proved earlier. -/
def ShiftedSeededNonsplitTraceWeilBoundAssumption
    (coefficient : ℕ) : Prop :=
  0 < coefficient ∧
    ∀ (p : ℕ) [Fact p.Prime],
      p ≠ 2 →
      ∀ (k : (ZMod p)ˣ), k ≠ 1 →
      ∀ (s : ↥(quadraticNormFiber p k)) (gamma : ZMod p)
        (d e : ℕ),
        0 < d →
        0 < e →
        Irreducible
          (MvPolynomial.map
            (algebraMap (quadraticFiniteField p)
              (AlgebraicClosure (quadraticFiniteField p)))
            (shiftedTraceCoverPolynomial
              (s.1 : quadraticFiniteField p)
              ((s.1 : quadraticFiniteField p) ^ p)
              (algebraMap (ZMod p) (quadraticFiniteField p) gamma)
              e d)) →
        |((shiftedSeededNonsplitTraceCurveSolutions
            p k s gamma d e).card : ℝ) - (p : ℝ)| ≤
          (coefficient : ℝ) * Real.sqrt (p : ℝ) *
            (d : ℝ) * (e : ℝ)

theorem shiftedSeededNonsplitTraceCurveSolutions_count_error_le_of_weilBoundAssumption
    (coefficient : ℕ)
    (hWeil : ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient)
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (k : (ZMod p)ˣ) (hk : k ≠ 1)
    (s : ↥(quadraticNormFiber p k)) (gamma : ZMod p)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hirreducible :
      Irreducible
        (MvPolynomial.map
          (algebraMap (quadraticFiniteField p)
            (AlgebraicClosure (quadraticFiniteField p)))
          (shiftedTraceCoverPolynomial
            (s.1 : quadraticFiniteField p)
            ((s.1 : quadraticFiniteField p) ^ p)
            (algebraMap (ZMod p) (quadraticFiniteField p) gamma)
            e d))) :
    |((shiftedSeededNonsplitTraceCurveSolutions
        p k s gamma d e).card : ℝ) - (p : ℝ)| ≤
      (coefficient : ℝ) * Real.sqrt (p : ℝ) *
        (d : ℝ) * (e : ℝ) :=
  hWeil.2 p hpTwo k hk s gamma d e hd he hirreducible

/-- The endgame-ready estimate, with split-cover irreducibility discharged
from the nontrivial seed norm and the shifted even obstruction. -/
theorem shiftedSeededNonsplitTraceCurveSolutions_count_error_le_of_weilBoundAssumption_and_positiveExponents
    (coefficient : ℕ)
    (hWeil : ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient)
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (k : (ZMod p)ˣ) (hk : k ≠ 1)
    (s : ↥(quadraticNormFiber p k)) (gamma : ZMod p)
    (hD2 : shiftedTraceEvenObstruction (k : ZMod p) gamma ≠ 0)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hdChar : (d : quadraticFiniteField p) ≠ 0) :
    |((shiftedSeededNonsplitTraceCurveSolutions
        p k s gamma d e).card : ℝ) - (p : ℝ)| ≤
      (coefficient : ℝ) * Real.sqrt (p : ℝ) *
        (d : ℝ) * (e : ℝ) := by
  apply
    shiftedSeededNonsplitTraceCurveSolutions_count_error_le_of_weilBoundAssumption
      coefficient hWeil p hpTwo k hk s gamma d e hd he
  exact
    shiftedSeededNonsplit_weightedCover_absolutelyIrreducible
      p hpTwo k hk s gamma hD2 d e hd he hdChar

/-- A fixed affine Hasse--Weil coefficient gives a fixed shifted seeded
nonsplit coefficient. -/
theorem shiftedSeededNonsplitTraceWeilBoundAssumption_of_bivariateAffineHasseWeilBound
    (generalCoefficient : ℕ)
    (hgeneralCoefficient : 0 < generalCoefficient)
    (hgeneral :
      BGS.External.BivariateAffineHasseWeilBound generalCoefficient) :
    ShiftedSeededNonsplitTraceWeilBoundAssumption
      (4 * generalCoefficient + 2) := by
  let coefficient := 4 * generalCoefficient + 2
  refine ⟨by omega, ?_⟩
  intro p _ hpTwo k hk s gamma d e hd he hirreducible
  have hDescendedIrreducible :=
    shiftedSeededNonsplitDescendedPolynomial_absolutelyIrreducible_of_cover
      p s.1 gamma d e hd he hirreducible
  have hAffine := hgeneral (ZMod p)
    (shiftedSeededNonsplitDescendedPolynomial p s.1 gamma d e)
    (2 * d) (2 * e) (by omega) (by omega)
    (shiftedSeededNonsplitDescendedPolynomial_hasBidegreeAtMost
      p s.1 gamma d e)
    hDescendedIrreducible
  have hCardNat :=
    shiftedSeededNonsplitTraceCurveSolutions_card_eq_affine_add_boundary
      p k s gamma d e hd he
  have hBoundaryNat :=
    shiftedSeededNonsplitIdentityBoundarySolutions_card_le
      p k s gamma d e he
  let affineCard :=
    (BGS.External.affinePlaneCurveZeros (ZMod p)
      (shiftedSeededNonsplitDescendedPolynomial
        p s.1 gamma d e)).card
  let boundaryCard :=
    (shiftedSeededNonsplitIdentityBoundarySolutions
      p k s gamma d e).card
  let x : ℝ := Real.sqrt (p : ℝ) * (d : ℝ) * (e : ℝ)
  have hCardReal :
      ((shiftedSeededNonsplitTraceCurveSolutions
          p k s gamma d e).card : ℝ) =
        affineCard + boundaryCard := by
    dsimp only [affineCard, boundaryCard]
    exact_mod_cast hCardNat
  have hBoundaryReal : (boundaryCard : ℝ) ≤ 2 * (e : ℝ) := by
    exact_mod_cast hBoundaryNat
  have hpOneNat : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    exact Real.one_le_sqrt.mpr (by exact_mod_cast hpOneNat)
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have heNonnegative : (0 : ℝ) ≤ e := by positivity
  have hBoundaryAbsorb : (boundaryCard : ℝ) ≤ 2 * x := by
    have hscaleOne : (1 : ℝ) ≤ Real.sqrt (p : ℝ) * (d : ℝ) := by
      nlinarith
    have heScale :
        (e : ℝ) ≤ Real.sqrt (p : ℝ) * (d : ℝ) * (e : ℝ) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hscaleOne heNonnegative
    calc
      (boundaryCard : ℝ) ≤ 2 * (e : ℝ) := hBoundaryReal
      _ ≤ 2 * (Real.sqrt (p : ℝ) * (d : ℝ) * (e : ℝ)) := by
        gcongr
      _ = 2 * x := by rfl
  have hAffine' :
      |(affineCard : ℝ) - (p : ℝ)| ≤
        4 * (generalCoefficient : ℝ) * x := by
    dsimp only [affineCard]
    rw [ZMod.card] at hAffine
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hAffine
    convert hAffine using 1 <;> dsimp [x] <;> ring
  rw [hCardReal]
  calc
    |((affineCard : ℝ) + boundaryCard) - (p : ℝ)| =
        |((affineCard : ℝ) - (p : ℝ)) + boundaryCard| := by ring_nf
    _ ≤ |(affineCard : ℝ) - (p : ℝ)| +
        |(boundaryCard : ℝ)| := abs_add_le _ _
    _ = |(affineCard : ℝ) - (p : ℝ)| + boundaryCard := by
      have hbabs : |(boundaryCard : ℝ)| = boundaryCard :=
        abs_of_nonneg (Nat.cast_nonneg boundaryCard)
      rw [hbabs]
    _ ≤ 4 * (generalCoefficient : ℝ) * x + 2 * x := by
      gcongr
    _ = (coefficient : ℝ) * Real.sqrt (p : ℝ) *
        (d : ℝ) * (e : ℝ) := by
      dsimp [coefficient, x]
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring

/-- The general affine Hasse--Weil theorem supplies the shifted seeded
nonsplit estimate. -/
theorem exists_shiftedSeededNonsplitTraceWeilBoundAssumption_of_generalHasseWeil
    (hHasse : BGS.External.GeneralBivariateAffineHasseWeilTheorem) :
    ∃ coefficient : ℕ,
      ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient := by
  obtain ⟨generalCoefficient, hgeneralCoefficient, hgeneral⟩ := hHasse
  exact
    ⟨4 * generalCoefficient + 2,
      shiftedSeededNonsplitTraceWeilBoundAssumption_of_bivariateAffineHasseWeilBound
        generalCoefficient hgeneralCoefficient hgeneral⟩

/-- Fixed coefficient `34 = 4 * 8 + 2` supplied by the in-repository affine
Hasse--Weil theorem. -/
theorem shiftedSeededNonsplitTraceWeilBoundAssumption_thirtyFour :
    ShiftedSeededNonsplitTraceWeilBoundAssumption 34 := by
  simpa using
    shiftedSeededNonsplitTraceWeilBoundAssumption_of_bivariateAffineHasseWeilBound
      8 (by norm_num)
        BGS.HasseWeil.bivariateAffineHasseWeilBound_eight

/-- Unconditional existence, using the in-repository general affine
Hasse--Weil theorem. -/
theorem exists_shiftedSeededNonsplitTraceWeilBoundAssumption :
    ∃ coefficient : ℕ,
      ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient :=
  exists_shiftedSeededNonsplitTraceWeilBoundAssumption_of_generalHasseWeil
    BGS.HasseWeil.generalBivariateAffineHasseWeilTheorem

end

end GenMarkoff.Symmetric.Endgame.Nonsplit
