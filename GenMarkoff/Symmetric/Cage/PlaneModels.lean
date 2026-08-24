import GenMarkoff.Symmetric.Cage.PulledRadicand
import GenMarkoff.Symmetric.Opening.ReturnExponentBound
import BGS.Markoff.Cage.PlaneModels

/-!
# Direct affine-plane models for symmetric generalized incidence

The second coordinate is the split-torus power parameter.  The diagonal
model adjoins one square root of the pulled incidence radicand.  Off the
diagonal, the first coordinate is the primitive sum of two square roots.
-/

namespace GenMarkoff.Symmetric.Cage

open Polynomial BGS.Markoff

noncomputable section

variable {K : Type*} [Field K]

/-- The diagonal equation, viewed as a polynomial in the root coordinate
over the parameter polynomial ring. -/
def incidenceDiagonalIteratedPolynomial
    (c xi : K) (d : ℕ) : K[X][X] :=
  adjoinSquarePolynomial (incidencePulledRadicand c xi d)

/-- The primitive-element equation for two distinct incidence radicands. -/
def incidenceOffDiagonalIteratedPolynomial
    (c xi eta : K) (d : ℕ) : K[X][X] :=
  (X ^ 2 -
      C (incidencePulledRadicand c xi d +
        incidencePulledRadicand c eta d)) ^ 2 -
    C (4 *
      (incidencePulledRadicand c xi d *
        incidencePulledRadicand c eta d))

/-- Put the pulled radicand in the second bivariate coordinate. -/
def incidencePulledRadicandSecondCoordinate
    (c xi : K) (d : ℕ) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (incidenceLeadingCoefficient xi) *
      MvPolynomial.X 1 ^ (4 * d) +
    MvPolynomial.C (incidenceLinearCoefficient c xi) *
      MvPolynomial.X 1 ^ (3 * d) +
    MvPolynomial.C (incidencePulledMiddleCoefficient c xi) *
      MvPolynomial.X 1 ^ (2 * d) +
    MvPolynomial.C (incidenceLinearCoefficient c xi) *
      MvPolynomial.X 1 ^ d +
    MvPolynomial.C (incidenceLeadingCoefficient xi)

@[simp]
lemma finTwoToIteratedPolynomial_incidencePulledRadicandSecondCoordinate
    (c xi : K) (d : ℕ) :
    finTwoToIteratedPolynomial
        (incidencePulledRadicandSecondCoordinate c xi d) =
      C (incidencePulledRadicand c xi d) := by
  simp [incidencePulledRadicandSecondCoordinate,
    incidencePulledRadicand]

/-- The diagonal bivariate equation `L² = F_{c,xi,d}(t)`. -/
def incidenceDiagonalPlanePolynomial
    (c xi : K) (d : ℕ) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ 2 -
    incidencePulledRadicandSecondCoordinate c xi d

/-- The off-diagonal primitive quartic as a bivariate polynomial. -/
def incidenceOffDiagonalPlanePolynomial
    (c xi eta : K) (d : ℕ) : MvPolynomial (Fin 2) K :=
  (MvPolynomial.X 0 ^ 2 -
      (incidencePulledRadicandSecondCoordinate c xi d +
        incidencePulledRadicandSecondCoordinate c eta d)) ^ 2 -
    MvPolynomial.C 4 *
      incidencePulledRadicandSecondCoordinate c xi d *
      incidencePulledRadicandSecondCoordinate c eta d

@[simp]
lemma finTwoToIteratedPolynomial_incidenceDiagonalPlanePolynomial
    (c xi : K) (d : ℕ) :
    finTwoToIteratedPolynomial
        (incidenceDiagonalPlanePolynomial c xi d) =
      incidenceDiagonalIteratedPolynomial c xi d := by
  simp [incidenceDiagonalPlanePolynomial,
    incidenceDiagonalIteratedPolynomial, adjoinSquarePolynomial]

@[simp]
lemma finTwoToIteratedPolynomial_incidenceOffDiagonalPlanePolynomial
    (c xi eta : K) (d : ℕ) :
    finTwoToIteratedPolynomial
        (incidenceOffDiagonalPlanePolynomial c xi eta d) =
      incidenceOffDiagonalIteratedPolynomial c xi eta d := by
  simp only [incidenceOffDiagonalPlanePolynomial,
    incidenceOffDiagonalIteratedPolynomial, map_sub, map_pow, map_add,
    map_mul, finTwoToIteratedPolynomial_X_zero,
    finTwoToIteratedPolynomial_incidencePulledRadicandSecondCoordinate,
    finTwoToIteratedPolynomial_C]
  have hC4 : (C (4 : K) : K[X]) = 4 :=
    map_natCast (Polynomial.C : K →+* K[X]) 4
  rw [hC4]
  ring

/-- The diagonal iterated polynomial is irreducible. -/
lemma incidenceDiagonalIteratedPolynomial_irreducible
    (h2 : (2 : K) ≠ 0) {c xi : K} (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c xi)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    Irreducible (incidenceDiagonalIteratedPolynomial c xi d) := by
  have hsquarefree :=
    (incidencePulledRadicand_separable
      h2 hc hregular hd hdegree).squarefree
  have hnonsquare :
      ¬ IsSquare
        (algebraMap K[X] (FractionRing K[X])
          (incidencePulledRadicand c xi d)) :=
    BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
      hsquarefree
      (incidencePulledRadicand_not_isUnit hregular hd)
  have hfraction :
      Irreducible
        ((incidenceDiagonalIteratedPolynomial c xi d).map
          (algebraMap K[X] (FractionRing K[X]))) := by
    simpa [incidenceDiagonalIteratedPolynomial,
      adjoinSquarePolynomial] using
      adjoinSquarePolynomial_irreducible_of_not_isSquare hnonsquare
  have hmonic :
      (incidenceDiagonalIteratedPolynomial c xi d).Monic :=
    adjoinSquarePolynomial_monic _
  exact
    hmonic.isPrimitive.irreducible_iff_irreducible_map_fraction_map.mpr
      hfraction

/-- Ground-field irreducibility of the diagonal bivariate equation. -/
lemma incidenceDiagonalPlanePolynomial_irreducible
    (h2 : (2 : K) ≠ 0) {c xi : K} (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c xi)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    Irreducible (incidenceDiagonalPlanePolynomial c xi d) := by
  have hiterated :=
    incidenceDiagonalIteratedPolynomial_irreducible
      h2 hc hregular hd hdegree
  have hback :=
    hiterated.map (finTwoToIteratedPolynomial (K := K)).symm
  have heq :
      (finTwoToIteratedPolynomial (K := K)).symm
          (incidenceDiagonalIteratedPolynomial c xi d) =
        incidenceDiagonalPlanePolynomial c xi d := by
    rw [←
      finTwoToIteratedPolynomial_incidenceDiagonalPlanePolynomial]
    exact
      (finTwoToIteratedPolynomial (K := K)).symm_apply_apply _
  rw [heq] at hback
  exact hback

/-- The off-diagonal primitive quartic is irreducible over the parameter
polynomial ring. -/
lemma incidenceOffDiagonalIteratedPolynomial_irreducible
    (h2 : (2 : K) ≠ 0) {c xi eta : K} (hc : c ^ 2 ≠ 4)
    (hxi : OrderedTraceCandidateRegular c c c xi)
    (heta : OrderedTraceCandidateRegular c c c eta)
    (hpair : IsHasseWeilReadyIncidencePair c xi eta)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    Irreducible
      (incidenceOffDiagonalIteratedPolynomial c xi eta d) := by
  have hfractionGeneric :=
    incidenceBiquadraticPrimitiveQuartic_irreducible_ratFunc
      h2 hc hxi heta hpair hd hdegree
  have hfraction :
      Irreducible
        ((incidenceOffDiagonalIteratedPolynomial c xi eta d).map
          (algebraMap K[X] (RatFunc K))) := by
    have heq :
        (incidenceOffDiagonalIteratedPolynomial c xi eta d).map
            (algebraMap K[X] (RatFunc K)) =
          BGS.Markoff.biquadraticPrimitiveQuartic
            (algebraMap K[X] (RatFunc K)
              (incidencePulledRadicand c xi d))
            (algebraMap K[X] (RatFunc K)
              (incidencePulledRadicand c eta d)) := by
      simp only [incidenceOffDiagonalIteratedPolynomial,
        BGS.Markoff.biquadraticPrimitiveQuartic, Polynomial.map_sub,
        Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
        Polynomial.map_add, Polynomial.map_mul, map_add, map_mul]
      have hfour :
          algebraMap K[X] (RatFunc K) (4 : K[X]) =
            (4 : RatFunc K) :=
        map_natCast (algebraMap K[X] (RatFunc K)) 4
      rw [hfour]
      ring
    rw [heq]
    exact hfractionGeneric
  have hmonic :
      (incidenceOffDiagonalIteratedPolynomial c xi eta d).Monic := by
    have hquadratic :
        IsMonicOfDegree
          (X ^ 2 -
            C (incidencePulledRadicand c xi d +
              incidencePulledRadicand c eta d) : K[X][X]) 2 :=
      (isMonicOfDegree_X_pow K[X] 2).sub (by simp)
    exact
      ((hquadratic.pow 2).sub (by
        have hpos : 0 < 2 * 2 := by norm_num
        simpa only [← C_mul, natDegree_C] using hpos)).monic
  exact
    hmonic.isPrimitive.irreducible_iff_irreducible_map_fraction_map.mpr
      hfraction

/-- Ground-field irreducibility of the off-diagonal bivariate equation. -/
lemma incidenceOffDiagonalPlanePolynomial_irreducible
    (h2 : (2 : K) ≠ 0) {c xi eta : K} (hc : c ^ 2 ≠ 4)
    (hxi : OrderedTraceCandidateRegular c c c xi)
    (heta : OrderedTraceCandidateRegular c c c eta)
    (hpair : IsHasseWeilReadyIncidencePair c xi eta)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    Irreducible
      (incidenceOffDiagonalPlanePolynomial c xi eta d) := by
  have hiterated :=
    incidenceOffDiagonalIteratedPolynomial_irreducible
      h2 hc hxi heta hpair hd hdegree
  have hback :=
    hiterated.map (finTwoToIteratedPolynomial (K := K)).symm
  have heq :
      (finTwoToIteratedPolynomial (K := K)).symm
          (incidenceOffDiagonalIteratedPolynomial c xi eta d) =
        incidenceOffDiagonalPlanePolynomial c xi eta d := by
    rw [←
      finTwoToIteratedPolynomial_incidenceOffDiagonalPlanePolynomial]
    exact
      (finTwoToIteratedPolynomial (K := K)).symm_apply_apply _
  rw [heq] at hback
  exact hback

/-- Scalar extension commutes with the off-diagonal obstruction. -/
lemma map_incidencePairObstruction
    {L : Type*} [Field L] (phi : K →+* L)
    (c xi eta : K) :
    phi (incidencePairObstruction c xi eta) =
      incidencePairObstruction (phi c) (phi xi) (phi eta) := by
  simp only [incidencePairObstruction, map_add, map_mul, map_pow,
    map_neg, map_ofNat]

/-- Admissibility of an off-diagonal incidence pair is preserved by an
injective scalar extension. -/
lemma isHasseWeilReadyIncidencePair_map
    {L : Type*} [Field L] (phi : K →+* L)
    (hphi : Function.Injective phi) {c xi eta : K}
    (hpair : IsHasseWeilReadyIncidencePair c xi eta) :
    IsHasseWeilReadyIncidencePair (phi c) (phi xi) (phi eta) := by
  refine ⟨?_, ?_⟩
  · exact fun h => hpair.1 (hphi h)
  · have hmapped :=
      (map_ne_zero_iff phi hphi).mpr hpair.2
    simpa only [map_incidencePairObstruction] using hmapped

/-- The diagonal plane model remains irreducible after extension to an
algebraic closure. -/
lemma incidenceDiagonalPlanePolynomial_absolutelyIrreducible
    (h2 : (2 : K) ≠ 0) {c xi : K} (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c xi)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (incidenceDiagonalPlanePolynomial c xi d)) := by
  let phi : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  have h2' : (2 : AlgebraicClosure K) ≠ 0 := by
    have hmapped := (map_ne_zero_iff phi phi.injective).mpr h2
    simpa only [map_ofNat] using hmapped
  have hc' : (phi c) ^ 2 ≠ 4 := by
    apply sub_ne_zero.mp
    have hmapped :=
      (map_ne_zero_iff phi phi.injective).mpr
        (sub_ne_zero.mpr hc)
    simpa only [map_sub, map_pow, map_ofNat] using hmapped
  have hregular' :
      OrderedTraceCandidateRegular
        (phi c) (phi c) (phi c) (phi xi) :=
    Opening.orderedTraceCandidateRegular_map
      phi phi.injective hregular
  have hdegree' : (d : AlgebraicClosure K) ≠ 0 := by
    have hmapped := (map_ne_zero_iff phi phi.injective).mpr hdegree
    simpa only [map_natCast] using hmapped
  have hiterated :=
    incidenceDiagonalIteratedPolynomial_irreducible
      h2' hc' hregular' hd hdegree'
  have himage :
      finTwoToIteratedPolynomial (K := AlgebraicClosure K)
          (MvPolynomial.map phi
            (incidenceDiagonalPlanePolynomial c xi d)) =
        incidenceDiagonalIteratedPolynomial
          (phi c) (phi xi) d := by
    rw [BGS.Markoff.finTwoToIteratedPolynomial_map]
    simp [finTwoToIteratedPolynomial_incidenceDiagonalPlanePolynomial,
      incidenceDiagonalIteratedPolynomial, adjoinSquarePolynomial,
      map_incidencePulledRadicand]
  rw [← himage] at hiterated
  have hback :=
    hiterated.map
      (finTwoToIteratedPolynomial
        (K := AlgebraicClosure K)).symm
  simpa [phi] using hback

/-- The off-diagonal primitive quartic remains irreducible after extension
to an algebraic closure. -/
lemma incidenceOffDiagonalPlanePolynomial_absolutelyIrreducible
    (h2 : (2 : K) ≠ 0) {c xi eta : K} (hc : c ^ 2 ≠ 4)
    (hxi : OrderedTraceCandidateRegular c c c xi)
    (heta : OrderedTraceCandidateRegular c c c eta)
    (hpair : IsHasseWeilReadyIncidencePair c xi eta)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (incidenceOffDiagonalPlanePolynomial c xi eta d)) := by
  let phi : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  have h2' : (2 : AlgebraicClosure K) ≠ 0 := by
    have hmapped := (map_ne_zero_iff phi phi.injective).mpr h2
    simpa only [map_ofNat] using hmapped
  have hc' : (phi c) ^ 2 ≠ 4 := by
    apply sub_ne_zero.mp
    have hmapped :=
      (map_ne_zero_iff phi phi.injective).mpr
        (sub_ne_zero.mpr hc)
    simpa only [map_sub, map_pow, map_ofNat] using hmapped
  have hxi' :
      OrderedTraceCandidateRegular
        (phi c) (phi c) (phi c) (phi xi) :=
    Opening.orderedTraceCandidateRegular_map
      phi phi.injective hxi
  have heta' :
      OrderedTraceCandidateRegular
        (phi c) (phi c) (phi c) (phi eta) :=
    Opening.orderedTraceCandidateRegular_map
      phi phi.injective heta
  have hpair' :
      IsHasseWeilReadyIncidencePair
        (phi c) (phi xi) (phi eta) :=
    isHasseWeilReadyIncidencePair_map phi phi.injective hpair
  have hdegree' : (d : AlgebraicClosure K) ≠ 0 := by
    have hmapped := (map_ne_zero_iff phi phi.injective).mpr hdegree
    simpa only [map_natCast] using hmapped
  have hiterated :=
    incidenceOffDiagonalIteratedPolynomial_irreducible
      h2' hc' hxi' heta' hpair' hd hdegree'
  have himage :
      finTwoToIteratedPolynomial (K := AlgebraicClosure K)
          (MvPolynomial.map phi
            (incidenceOffDiagonalPlanePolynomial c xi eta d)) =
        incidenceOffDiagonalIteratedPolynomial
          (phi c) (phi xi) (phi eta) d := by
    rw [BGS.Markoff.finTwoToIteratedPolynomial_map]
    simp [finTwoToIteratedPolynomial_incidenceOffDiagonalPlanePolynomial,
      incidenceOffDiagonalIteratedPolynomial,
      map_incidencePulledRadicand]
  rw [← himage] at hiterated
  have hback :=
    hiterated.map
      (finTwoToIteratedPolynomial
        (K := AlgebraicClosure K)).symm
  simpa [phi] using hback

private lemma degreeOf_C_mul_X_one_pow_first_le
    (a : K) (n : ℕ) :
    MvPolynomial.degreeOf (0 : Fin 2)
      (MvPolynomial.C a * MvPolynomial.X 1 ^ n) ≤ 0 := by
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  rw [MvPolynomial.degreeOf_C,
    MvPolynomial.degreeOf_X_pow_of_ne n
      (by decide : (0 : Fin 2) ≠ 1)]

private lemma degreeOf_C_mul_X_one_pow_second_le
    (a : K) (n : ℕ) :
    MvPolynomial.degreeOf (1 : Fin 2)
      (MvPolynomial.C a * MvPolynomial.X 1 ^ n) ≤ n := by
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  rw [MvPolynomial.degreeOf_C,
    MvPolynomial.degreeOf_X_self_pow]
  omega

/-- The embedded pulled radicand is independent of the root coordinate. -/
lemma incidencePulledRadicandSecondCoordinate_degreeOf_first_le
    (c xi : K) (d : ℕ) :
    MvPolynomial.degreeOf (0 : Fin 2)
      (incidencePulledRadicandSecondCoordinate c xi d) ≤ 0 := by
  unfold incidencePulledRadicandSecondCoordinate
  refine (MvPolynomial.degreeOf_add_le _ _ _).trans
    (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_add_le _ _ _).trans
      (max_le ?_ ?_)
    · refine (MvPolynomial.degreeOf_add_le _ _ _).trans
        (max_le ?_ ?_)
      · refine (MvPolynomial.degreeOf_add_le _ _ _).trans
          (max_le ?_ ?_)
        · exact degreeOf_C_mul_X_one_pow_first_le _ _
        · exact degreeOf_C_mul_X_one_pow_first_le _ _
      · exact degreeOf_C_mul_X_one_pow_first_le _ _
    · exact degreeOf_C_mul_X_one_pow_first_le _ _
  · rw [MvPolynomial.degreeOf_C]

/-- The embedded pulled radicand has parameter degree at most `4d`. -/
lemma incidencePulledRadicandSecondCoordinate_degreeOf_second_le
    (c xi : K) (d : ℕ) :
    MvPolynomial.degreeOf (1 : Fin 2)
      (incidencePulledRadicandSecondCoordinate c xi d) ≤ 4 * d := by
  unfold incidencePulledRadicandSecondCoordinate
  refine (MvPolynomial.degreeOf_add_le _ _ _).trans
    (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_add_le _ _ _).trans
      (max_le ?_ ?_)
    · refine (MvPolynomial.degreeOf_add_le _ _ _).trans
        (max_le ?_ ?_)
      · refine (MvPolynomial.degreeOf_add_le _ _ _).trans
          (max_le ?_ ?_)
        · exact degreeOf_C_mul_X_one_pow_second_le _ _
        · exact
            (degreeOf_C_mul_X_one_pow_second_le _ _).trans
              (by omega)
      · exact
          (degreeOf_C_mul_X_one_pow_second_le _ _).trans
            (by omega)
    · exact
        (degreeOf_C_mul_X_one_pow_second_le _ _).trans
          (by omega)
  · rw [MvPolynomial.degreeOf_C]
    omega

/-- The diagonal model has bidegree at most `(2,4d)`. -/
lemma incidenceDiagonalPlanePolynomial_hasBidegreeAtMost
    (c xi : K) (d : ℕ) :
    BGS.External.HasBidegreeAtMost
      (incidenceDiagonalPlanePolynomial c xi d) 2 (4 * d) := by
  have hfirst :
      MvPolynomial.degreeOf (0 : Fin 2)
        (incidenceDiagonalPlanePolynomial c xi d) ≤ 2 := by
    unfold incidenceDiagonalPlanePolynomial
    refine (MvPolynomial.degreeOf_sub_le _ _ _).trans
      (max_le ?_ ?_)
    · simp
    · exact
        (incidencePulledRadicandSecondCoordinate_degreeOf_first_le
          c xi d).trans (by omega)
  have hsecond :
      MvPolynomial.degreeOf (1 : Fin 2)
        (incidenceDiagonalPlanePolynomial c xi d) ≤ 4 * d := by
    unfold incidenceDiagonalPlanePolynomial
    refine (MvPolynomial.degreeOf_sub_le _ _ _).trans
      (max_le ?_ ?_)
    · rw [MvPolynomial.degreeOf_X_pow_of_ne 2
        (by decide : (1 : Fin 2) ≠ 0)]
      omega
    · exact
        incidencePulledRadicandSecondCoordinate_degreeOf_second_le
          c xi d
  intro monomial hmonomial
  exact
    ⟨(MvPolynomial.degreeOf_le_iff.mp hfirst) monomial hmonomial,
      (MvPolynomial.degreeOf_le_iff.mp hsecond) monomial hmonomial⟩

/-- The primitive off-diagonal model has bidegree at most `(4,8d)`. -/
lemma incidenceOffDiagonalPlanePolynomial_hasBidegreeAtMost
    (c xi eta : K) (d : ℕ) :
    BGS.External.HasBidegreeAtMost
      (incidenceOffDiagonalPlanePolynomial c xi eta d) 4 (8 * d) := by
  have hfirst :
      MvPolynomial.degreeOf (0 : Fin 2)
        (incidenceOffDiagonalPlanePolynomial c xi eta d) ≤ 4 := by
    unfold incidenceOffDiagonalPlanePolynomial
    have hsum :
        MvPolynomial.degreeOf (0 : Fin 2)
          (incidencePulledRadicandSecondCoordinate c xi d +
            incidencePulledRadicandSecondCoordinate c eta d) ≤ 0 :=
      (MvPolynomial.degreeOf_add_le _ _ _).trans
        (max_le
          (incidencePulledRadicandSecondCoordinate_degreeOf_first_le
            c xi d)
          (incidencePulledRadicandSecondCoordinate_degreeOf_first_le
            c eta d))
    have hinside :
        MvPolynomial.degreeOf (0 : Fin 2)
          (MvPolynomial.X 0 ^ 2 -
            (incidencePulledRadicandSecondCoordinate c xi d +
              incidencePulledRadicandSecondCoordinate c eta d)) ≤ 2 :=
      (MvPolynomial.degreeOf_sub_le _ _ _).trans
        (max_le (by simp) (hsum.trans (by omega)))
    have hsquare :=
      MvPolynomial.degreeOf_pow_le (0 : Fin 2)
        (MvPolynomial.X 0 ^ 2 -
          (incidencePulledRadicandSecondCoordinate c xi d +
            incidencePulledRadicandSecondCoordinate c eta d)) 2
    have hproduct :
        MvPolynomial.degreeOf (0 : Fin 2)
          (MvPolynomial.C 4 *
            incidencePulledRadicandSecondCoordinate c xi d *
            incidencePulledRadicandSecondCoordinate c eta d) ≤ 0 := by
      have hleft :
          MvPolynomial.degreeOf (0 : Fin 2)
            (MvPolynomial.C 4 *
              incidencePulledRadicandSecondCoordinate c xi d) ≤ 0 := by
        refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
        rw [MvPolynomial.degreeOf_C]
        simpa using
          incidencePulledRadicandSecondCoordinate_degreeOf_first_le
            c xi d
      refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
      exact
        (add_le_add hleft
          (incidencePulledRadicandSecondCoordinate_degreeOf_first_le
            c eta d)).trans (by omega)
    refine (MvPolynomial.degreeOf_sub_le _ _ _).trans
      (max_le ?_ ?_)
    · exact hsquare.trans (by omega)
    · exact hproduct.trans (by omega)
  have hsecond :
      MvPolynomial.degreeOf (1 : Fin 2)
        (incidenceOffDiagonalPlanePolynomial c xi eta d) ≤
          8 * d := by
    unfold incidenceOffDiagonalPlanePolynomial
    have hsum :
        MvPolynomial.degreeOf (1 : Fin 2)
          (incidencePulledRadicandSecondCoordinate c xi d +
            incidencePulledRadicandSecondCoordinate c eta d) ≤
            4 * d :=
      (MvPolynomial.degreeOf_add_le _ _ _).trans
        (max_le
          (incidencePulledRadicandSecondCoordinate_degreeOf_second_le
            c xi d)
          (incidencePulledRadicandSecondCoordinate_degreeOf_second_le
            c eta d))
    have hinside :
        MvPolynomial.degreeOf (1 : Fin 2)
          (MvPolynomial.X 0 ^ 2 -
            (incidencePulledRadicandSecondCoordinate c xi d +
              incidencePulledRadicandSecondCoordinate c eta d)) ≤
              4 * d := by
      refine (MvPolynomial.degreeOf_sub_le _ _ _).trans
        (max_le ?_ hsum)
      rw [MvPolynomial.degreeOf_X_pow_of_ne 2
        (by decide : (1 : Fin 2) ≠ 0)]
      omega
    refine (MvPolynomial.degreeOf_sub_le _ _ _).trans
      (max_le ?_ ?_)
    · exact
        (MvPolynomial.degreeOf_pow_le _ _ _).trans
          ((Nat.mul_le_mul_left 2 hinside).trans (by omega))
    · have hleft :
          MvPolynomial.degreeOf (1 : Fin 2)
            (MvPolynomial.C 4 *
              incidencePulledRadicandSecondCoordinate c xi d) ≤
              4 * d := by
        refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
        rw [MvPolynomial.degreeOf_C]
        simpa using
          incidencePulledRadicandSecondCoordinate_degreeOf_second_le
            c xi d
      refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
      exact
        (add_le_add hleft
          (incidencePulledRadicandSecondCoordinate_degreeOf_second_le
            c eta d)).trans (by omega)
  intro monomial hmonomial
  exact
    ⟨(MvPolynomial.degreeOf_le_iff.mp hfirst) monomial hmonomial,
      (MvPolynomial.degreeOf_le_iff.mp hsecond) monomial hmonomial⟩

/-- Evaluation of the embedded radicand is ordinary univariate evaluation
in the second coordinate. -/
lemma eval_incidencePulledRadicandSecondCoordinate
    (c xi : K) (d : ℕ) (root parameter : K) :
    MvPolynomial.eval ![root, parameter]
        (incidencePulledRadicandSecondCoordinate c xi d) =
      (incidencePulledRadicand c xi d).eval parameter := by
  simp [incidencePulledRadicandSecondCoordinate,
    incidencePulledRadicand]

/-- Zeros of the diagonal model are exactly square roots of the pulled
incidence radicand. -/
lemma eval_incidenceDiagonalPlanePolynomial_eq_zero_iff
    (c xi : K) (d : ℕ) (root parameter : K) :
    MvPolynomial.eval ![root, parameter]
        (incidenceDiagonalPlanePolynomial c xi d) = 0 ↔
      root ^ 2 =
        (incidencePulledRadicand c xi d).eval parameter := by
  simp [incidenceDiagonalPlanePolynomial,
    eval_incidencePulledRadicandSecondCoordinate, sub_eq_zero]

/-- Evaluation of the off-diagonal plane model is the primitive quartic
in the two scalar radicand values. -/
lemma eval_incidenceOffDiagonalPlanePolynomial
    (c xi eta : K) (d : ℕ) (sumRoot parameter : K) :
    MvPolynomial.eval ![sumRoot, parameter]
        (incidenceOffDiagonalPlanePolynomial c xi eta d) =
      (sumRoot ^ 2 -
          ((incidencePulledRadicand c xi d).eval parameter +
            (incidencePulledRadicand c eta d).eval parameter)) ^ 2 -
        4 * (incidencePulledRadicand c xi d).eval parameter *
          (incidencePulledRadicand c eta d).eval parameter := by
  simp [incidenceOffDiagonalPlanePolynomial,
    eval_incidencePulledRadicandSecondCoordinate]

/-- Away from the primitive-coordinate boundary, a zero of the
off-diagonal model is equivalent to a pair of square roots. -/
lemma eval_incidenceOffDiagonalPlanePolynomial_eq_zero_iff_exists_rootPair
    (h2 : (2 : K) ≠ 0) (c xi eta : K) (d : ℕ)
    {sumRoot parameter : K} (hsum : sumRoot ≠ 0) :
    MvPolynomial.eval ![sumRoot, parameter]
        (incidenceOffDiagonalPlanePolynomial c xi eta d) = 0 ↔
      ∃ firstRoot secondRoot : K,
        firstRoot ^ 2 =
            (incidencePulledRadicand c xi d).eval parameter ∧
        secondRoot ^ 2 =
            (incidencePulledRadicand c eta d).eval parameter ∧
        firstRoot + secondRoot = sumRoot := by
  rw [eval_incidenceOffDiagonalPlanePolynomial]
  exact
    BGS.Markoff.primitiveQuarticEquation_iff_exists_rootPair
      h2 hsum

end

end GenMarkoff.Symmetric.Cage
