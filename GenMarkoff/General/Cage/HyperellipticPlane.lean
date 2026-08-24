import GenMarkoff.General.Cage.ThreeSquareRootCount
import BGS.HasseWeil.GeneralBivariateAffineHasseWeil
import BGS.Markoff.Cage.PlaneModels
import Mathlib.FieldTheory.Perfect

/-!
# Generic hyperelliptic plane models

For a univariate polynomial `P`, this file constructs the affine plane
equation

`root ^ 2 = P(parameter)`.

Squarefreeness and nonconstancy of `P` imply absolute irreducibility over a
perfect field.  The construction is independent of the generalized Markoff
coefficients, so the same model applies to each of the seven nonempty
products in the three-square-root identity.
-/

namespace GenMarkoff.General.Cage

open Polynomial BGS.Markoff

noncomputable section

variable {K : Type*} [Field K]

/-- Embed a univariate polynomial in the second affine coordinate. -/
def hyperellipticSecondCoordinateRingHom :
    K[X] →+* MvPolynomial (Fin 2) K :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 1)

/-- A univariate polynomial placed in the second affine coordinate. -/
def hyperellipticSecondCoordinate
    (P : K[X]) : MvPolynomial (Fin 2) K :=
  hyperellipticSecondCoordinateRingHom P

/-- The equation `root ^ 2 - P(parameter)`, viewed as a polynomial in the
root coordinate over the parameter polynomial ring. -/
def hyperellipticIteratedPolynomial (P : K[X]) : K[X][X] :=
  adjoinSquarePolynomial P

/-- The bivariate affine equation `root ^ 2 - P(parameter)`. -/
def hyperellipticPlanePolynomial
    (P : K[X]) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ 2 - hyperellipticSecondCoordinate P

@[simp]
theorem finTwoToIteratedPolynomial_hyperellipticSecondCoordinate
    (P : K[X]) :
    finTwoToIteratedPolynomial (hyperellipticSecondCoordinate P) =
      C P := by
  let lhs : K[X] →+* K[X][X] :=
    finTwoToIteratedPolynomial.toRingEquiv.toRingHom.comp
      hyperellipticSecondCoordinateRingHom
  let rhs : K[X] →+* K[X][X] := Polynomial.C
  have heq : lhs = rhs := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [lhs, rhs, hyperellipticSecondCoordinateRingHom]
    · simp [lhs, rhs, hyperellipticSecondCoordinateRingHom]
  exact DFunLike.congr_fun heq P

@[simp]
theorem finTwoToIteratedPolynomial_hyperellipticPlanePolynomial
    (P : K[X]) :
    finTwoToIteratedPolynomial (hyperellipticPlanePolynomial P) =
      hyperellipticIteratedPolynomial P := by
  simp [hyperellipticPlanePolynomial, hyperellipticIteratedPolynomial,
    adjoinSquarePolynomial]

/-- A radicand that is nonsquare in the rational function field gives an
irreducible quadratic over the parameter polynomial ring. -/
theorem hyperellipticIteratedPolynomial_irreducible_of_not_isSquare
    {P : K[X]}
    (hnonsquare :
      ¬ IsSquare (algebraMap K[X] (FractionRing K[X]) P)) :
    Irreducible (hyperellipticIteratedPolynomial P) := by
  have hfraction :
      Irreducible
        ((hyperellipticIteratedPolynomial P).map
          (algebraMap K[X] (FractionRing K[X]))) := by
    simpa [hyperellipticIteratedPolynomial, adjoinSquarePolynomial] using
      adjoinSquarePolynomial_irreducible_of_not_isSquare hnonsquare
  have hmonic : (hyperellipticIteratedPolynomial P).Monic :=
    adjoinSquarePolynomial_monic _
  exact
    hmonic.isPrimitive.irreducible_iff_irreducible_map_fraction_map.mpr
      hfraction

/-- A nonunit squarefree radicand gives an irreducible quadratic over the
parameter polynomial ring. -/
theorem hyperellipticIteratedPolynomial_irreducible
    {P : K[X]} (hsquarefree : Squarefree P)
    (hnonunit : ¬ IsUnit P) :
    Irreducible (hyperellipticIteratedPolynomial P) := by
  apply
    hyperellipticIteratedPolynomial_irreducible_of_not_isSquare
  exact
    not_isSquare_algebraMap_of_squarefree_not_isUnit
      hsquarefree hnonunit

/-- Ground-field irreducibility of the hyperelliptic plane equation. -/
theorem hyperellipticPlanePolynomial_irreducible
    {P : K[X]} (hsquarefree : Squarefree P)
    (hnonunit : ¬ IsUnit P) :
    Irreducible (hyperellipticPlanePolynomial P) := by
  have hiterated :=
    hyperellipticIteratedPolynomial_irreducible
      hsquarefree hnonunit
  have hback :=
    hiterated.map (finTwoToIteratedPolynomial (K := K)).symm
  have heq :
      (finTwoToIteratedPolynomial (K := K)).symm
          (hyperellipticIteratedPolynomial P) =
        hyperellipticPlanePolynomial P := by
    rw [←
      finTwoToIteratedPolynomial_hyperellipticPlanePolynomial]
    exact
      (finTwoToIteratedPolynomial (K := K)).symm_apply_apply _
  rw [heq] at hback
  exact hback

/-- Direct geometric irreducibility criterion.  This version only asks that
the scalar-extended radicand be nonsquare in the rational function field;
it therefore also applies when the original polynomial contains an explicit
square factor. -/
theorem
    hyperellipticPlanePolynomial_absolutelyIrreducible_of_not_isSquare_map
    {P : K[X]}
    (hnonsquare :
      ¬ IsSquare
        (algebraMap
          (Polynomial (AlgebraicClosure K))
          (FractionRing (Polynomial (AlgebraicClosure K)))
          (P.map (algebraMap K (AlgebraicClosure K))))) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (hyperellipticPlanePolynomial P)) := by
  let phi := algebraMap K (AlgebraicClosure K)
  have hiterated :
      Irreducible
        (hyperellipticIteratedPolynomial (P.map phi)) :=
    hyperellipticIteratedPolynomial_irreducible_of_not_isSquare
      hnonsquare
  have himage :
      finTwoToIteratedPolynomial (K := AlgebraicClosure K)
          (MvPolynomial.map phi (hyperellipticPlanePolynomial P)) =
        hyperellipticIteratedPolynomial (P.map phi) := by
    rw [finTwoToIteratedPolynomial_map]
    simp [hyperellipticIteratedPolynomial, adjoinSquarePolynomial]
  rw [← himage] at hiterated
  have hback :=
    hiterated.map
      (finTwoToIteratedPolynomial
        (K := AlgebraicClosure K)).symm
  simpa [phi] using hback

/-- Over a perfect ground field, a nonunit squarefree radicand gives an
absolutely irreducible hyperelliptic plane equation. -/
theorem hyperellipticPlanePolynomial_absolutelyIrreducible
    [PerfectField K] {P : K[X]}
    (hsquarefree : Squarefree P) (hnonunit : ¬ IsUnit P) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (hyperellipticPlanePolynomial P)) := by
  let phi := algebraMap K (AlgebraicClosure K)
  have hsquarefreeMap : Squarefree (P.map phi) :=
    (PerfectField.separable_iff_squarefree.mpr
      hsquarefree).map.squarefree
  have hnonunitMap : ¬ IsUnit (P.map phi) := by
    rwa [Polynomial.isUnit_map]
  have hiterated :=
    hyperellipticIteratedPolynomial_irreducible
      hsquarefreeMap hnonunitMap
  have himage :
      finTwoToIteratedPolynomial (K := AlgebraicClosure K)
          (MvPolynomial.map phi (hyperellipticPlanePolynomial P)) =
        hyperellipticIteratedPolynomial (P.map phi) := by
    rw [finTwoToIteratedPolynomial_map]
    simp [hyperellipticIteratedPolynomial, adjoinSquarePolynomial]
  rw [← himage] at hiterated
  have hback :=
    hiterated.map
      (finTwoToIteratedPolynomial
        (K := AlgebraicClosure K)).symm
  simpa [phi] using hback

/-- The embedded radicand is independent of the root coordinate. -/
theorem hyperellipticSecondCoordinate_degreeOf_first_le
    (P : K[X]) :
    MvPolynomial.degreeOf (0 : Fin 2)
      (hyperellipticSecondCoordinate P) ≤ 0 := by
  have heq :
      hyperellipticSecondCoordinate P =
        BGS.CorvajaZannier.polynomialInSecondCoordinateOnly P := by
    simp [hyperellipticSecondCoordinate,
      hyperellipticSecondCoordinateRingHom,
      Polynomial.eval₂_eq_sum,
      BGS.CorvajaZannier.polynomialInSecondCoordinateOnly]
  rw [heq]
  exact
    BGS.CorvajaZannier.polynomialInSecondCoordinateOnly_degreeOf_first_le P

/-- The second-coordinate degree of the embedded radicand is bounded by its
ordinary univariate degree. -/
theorem hyperellipticSecondCoordinate_degreeOf_second_le
    (P : K[X]) :
    MvPolynomial.degreeOf (1 : Fin 2)
      (hyperellipticSecondCoordinate P) ≤ P.natDegree := by
  rw [hyperellipticSecondCoordinate,
    hyperellipticSecondCoordinateRingHom,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum,
    Polynomial.sum_def]
  refine
    (MvPolynomial.degreeOf_sum_le (1 : Fin 2) P.support fun n =>
      MvPolynomial.C (P.coeff n) * MvPolynomial.X 1 ^ n).trans ?_
  apply Finset.sup_le
  intro n hn
  refine
    (MvPolynomial.degreeOf_mul_le (1 : Fin 2)
      (MvPolynomial.C (P.coeff n))
      (MvPolynomial.X 1 ^ n)).trans ?_
  rw [MvPolynomial.degreeOf_C,
    MvPolynomial.degreeOf_X_self_pow]
  simpa using Polynomial.le_natDegree_of_mem_supp n hn

/-- If `P` has degree at most `D`, its hyperelliptic model has bidegree at
most `(2,D)`. -/
theorem hyperellipticPlanePolynomial_hasBidegreeAtMost
    (P : K[X]) {D : ℕ} (hdegree : P.natDegree ≤ D) :
    BGS.External.HasBidegreeAtMost
      (hyperellipticPlanePolynomial P) 2 D := by
  have hfirst :
      MvPolynomial.degreeOf (0 : Fin 2)
        (hyperellipticPlanePolynomial P) ≤ 2 := by
    unfold hyperellipticPlanePolynomial
    refine
      (MvPolynomial.degreeOf_sub_le _ _ _).trans
        (max_le ?_ ?_)
    · simp
    · exact
        (hyperellipticSecondCoordinate_degreeOf_first_le P).trans
          (by omega)
  have hsecond :
      MvPolynomial.degreeOf (1 : Fin 2)
        (hyperellipticPlanePolynomial P) ≤ D := by
    unfold hyperellipticPlanePolynomial
    refine
      (MvPolynomial.degreeOf_sub_le _ _ _).trans
        (max_le ?_ ?_)
    · rw [MvPolynomial.degreeOf_X_pow_of_ne 2
        (by decide : (1 : Fin 2) ≠ 0)]
      omega
    · exact
        (hyperellipticSecondCoordinate_degreeOf_second_le P).trans
          hdegree
  intro monomial hmonomial
  exact
    ⟨(MvPolynomial.degreeOf_le_iff.mp hfirst)
        monomial hmonomial,
      (MvPolynomial.degreeOf_le_iff.mp hsecond)
        monomial hmonomial⟩

/-- Evaluation of the embedded radicand is ordinary univariate evaluation
in the parameter coordinate. -/
@[simp]
theorem eval_hyperellipticSecondCoordinate
    (P : K[X]) (root parameter : K) :
    MvPolynomial.eval ![root, parameter]
        (hyperellipticSecondCoordinate P) =
      P.eval parameter := by
  simp [hyperellipticSecondCoordinate,
    hyperellipticSecondCoordinateRingHom,
    Polynomial.eval₂_eq_sum, Polynomial.eval_eq_sum,
    Polynomial.sum_def]

/-- Zeros of the plane model are exactly square roots of the radicand
value. -/
theorem eval_hyperellipticPlanePolynomial_eq_zero_iff
    (P : K[X]) (root parameter : K) :
    MvPolynomial.eval ![root, parameter]
        (hyperellipticPlanePolynomial P) = 0 ↔
      root ^ 2 = P.eval parameter := by
  simp [hyperellipticPlanePolynomial, sub_eq_zero]

section FiniteFieldCount

variable [Fintype K] [DecidableEq K]

/-- The affine zero count of the hyperelliptic plane is the sum of the
numbers of square roots over all parameters. -/
theorem hyperellipticPlaneZeros_card_eq_sum_squareRoots
    (P : K[X]) :
    (BGS.External.affinePlaneCurveZeros K
        (hyperellipticPlanePolynomial P)).card =
      ∑ parameter : K,
        {root : K | root ^ 2 = P.eval parameter}.toFinset.card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (t := Finset.univ) (f := fun z : K × K => z.2)
    (by simp)]
  apply Finset.sum_congr rfl
  intro parameter _
  refine
    Finset.card_bij'
      (fun z _ => z.1)
      (fun root _ => (root, parameter))
      (fun z hz => ?_)
      (fun root hroot => ?_)
      ?_ ?_
  · rw [Set.mem_toFinset]
    have hz' := Finset.mem_filter.mp hz
    have hzero :=
      BGS.External.mem_affinePlaneCurveZeros_iff.mp hz'.1
    have heq :=
      (eval_hyperellipticPlanePolynomial_eq_zero_iff
        P z.1 z.2).mp hzero
    simpa [hz'.2] using heq
  · apply Finset.mem_filter.mpr
    refine
      ⟨BGS.External.mem_affinePlaneCurveZeros_iff.mpr ?_,
        rfl⟩
    apply
      (eval_hyperellipticPlanePolynomial_eq_zero_iff
        P root parameter).mpr
    rw [Set.mem_toFinset] at hroot
    exact hroot
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    cases z
    simp_all
  · intro root _
    rfl

/-- The affine zero count agrees exactly with the integer-valued cover
count used by the three-square-root identity. -/
theorem hyperellipticPlaneZeros_card_int_eq_squareRootCoverPointCount
    (P : K[X]) :
    ((BGS.External.affinePlaneCurveZeros K
        (hyperellipticPlanePolynomial P)).card : ℤ) =
      squareRootCoverPointCount (fun parameter : K =>
        P.eval parameter) := by
  rw [hyperellipticPlaneZeros_card_eq_sum_squareRoots]
  simp [squareRootCoverPointCount, squareRootCount]

/-- The in-repository coefficient-eight affine Hasse--Weil theorem yields
the simplified error `16 * sqrt(|K|) * D`. -/
theorem hyperellipticPlaneZeros_card_error_le
    [PerfectField K]
    {P : K[X]} (hsquarefree : Squarefree P)
    (hnonunit : ¬ IsUnit P)
    {D : ℕ} (hD : 0 < D) (hdegree : P.natDegree ≤ D) :
    |((BGS.External.affinePlaneCurveZeros K
          (hyperellipticPlanePolynomial P)).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      16 * Real.sqrt (Fintype.card K : ℝ) * D := by
  have hbound :=
    BGS.HasseWeil.abs_affinePlaneCurveZeros_card_sub_card_le_eight_mul_bidegree
      K (hyperellipticPlanePolynomial P) 2 D
      (by norm_num) hD
      (hyperellipticPlanePolynomial_hasBidegreeAtMost
        P hdegree)
      (hyperellipticPlanePolynomial_absolutelyIrreducible
        hsquarefree hnonunit)
  calc
    |((BGS.External.affinePlaneCurveZeros K
          (hyperellipticPlanePolynomial P)).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
        (8 : ℝ) * Real.sqrt (Fintype.card K : ℝ) *
          (((2 : ℕ) : ℝ)) * (D : ℝ) :=
      hbound
    _ = 16 * Real.sqrt (Fintype.card K : ℝ) * D := by
      ring

/-- The same coefficient-eight estimate, expressed in terms of the cover
count consumed by the seven-cover identity. -/
theorem squareRootCoverPointCount_error_le
    [PerfectField K]
    {P : K[X]} (hsquarefree : Squarefree P)
    (hnonunit : ¬ IsUnit P)
    {D : ℕ} (hD : 0 < D) (hdegree : P.natDegree ≤ D) :
    |((squareRootCoverPointCount
          (fun parameter : K => P.eval parameter) : ℤ) : ℝ) -
        (Fintype.card K : ℝ)| ≤
      16 * Real.sqrt (Fintype.card K : ℝ) * D := by
  have hcountReal :
      ((squareRootCoverPointCount
          (fun parameter : K => P.eval parameter) : ℤ) : ℝ) =
        ((BGS.External.affinePlaneCurveZeros K
          (hyperellipticPlanePolynomial P)).card : ℝ) := by
    have hcountInt :=
      (hyperellipticPlaneZeros_card_int_eq_squareRootCoverPointCount
        P).symm
    exact_mod_cast hcountInt
  rw [hcountReal]
  exact
    hyperellipticPlaneZeros_card_error_le
      hsquarefree hnonunit hD hdegree

end FiniteFieldCount

end

end GenMarkoff.General.Cage
