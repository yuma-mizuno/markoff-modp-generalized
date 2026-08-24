import GenMarkoff.General.Cage.ThreeRadicandSquareClasses
import GenMarkoff.General.MiddleGame.ActualOrderGrowth

/-!
# Geometric square classes for the unequal connecting cage

Absolute irreducibility of the seven hyperelliptic planes requires the
three-radicand square-class calculation after extension to an algebraic
closure.  This file transports the unequal incidence hypotheses through
that extension and then restores the forced polynomial square removed from
the centered-norm radicand.

The final statement is deliberately phrased using `Polynomial.map` on the
three original polynomials.  This is the form consumed by geometric
irreducibility arguments.
-/

namespace GenMarkoff.General.Cage

open Polynomial

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- Scalar extension commutes with the incidence/centered-norm obstruction. -/
theorem map_incidenceCenteredNormObstruction
    {L : Type*} [Field L] (phi : K →+* L)
    (a : Coefficients K) (xi : K) :
    phi (incidenceCenteredNormObstruction a xi) =
      incidenceCenteredNormObstruction
        (MiddleGame.mapCoefficients phi a) (phi xi) := by
  simp only [incidenceCenteredNormObstruction,
    MiddleGame.mapCoefficients_a1, MiddleGame.mapCoefficients_a2,
    MiddleGame.mapCoefficients_a3, map_add, map_mul, map_sub, map_pow,
    map_ofNat]

/-- Scalar extension commutes with the formal pair resultant. -/
theorem map_incidencePairResultant
    {L : Type*} [Field L] (phi : K →+* L)
    (a : Coefficients K) (xi eta : K) :
    phi (incidencePairResultant a xi eta) =
      incidencePairResultant
        (MiddleGame.mapCoefficients phi a) (phi xi) (phi eta) := by
  rw [incidencePairResultant, incidencePairResultant,
    ← Polynomial.resultant_map_map,
    map_incidenceDiscriminantPolynomial phi a xi,
    map_incidenceDiscriminantPolynomial phi a eta]

/-- The three branch-separation conditions are preserved by an injective
field homomorphism. -/
theorem isConnectingIncidencePair_map
    {L : Type*} [Field L] (phi : K →+* L)
    (hphi : Function.Injective phi)
    {a : Coefficients K} {xi eta : K}
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hpair : IsConnectingIncidencePair a xi eta) :
    IsConnectingIncidencePair
      (MiddleGame.mapCoefficients phi a) (phi xi) (phi eta) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro heq
    exact hpair.1.1 (hphi heq)
  · have hresultant :
        incidencePairResultant a xi eta ≠ 0 :=
      hpair.incidenceResultant_ne_zero hA2
    have hresultantMap :
        incidencePairResultant
            (MiddleGame.mapCoefficients phi a) (phi xi) (phi eta) ≠ 0 := by
      rw [← map_incidencePairResultant phi a xi eta]
      exact (map_ne_zero_iff phi hphi).2 hresultant
    intro hobstruction
    apply hresultantMap
    rw [incidencePairResultant_factor, hobstruction, mul_zero]
  · rw [← map_incidenceCenteredNormObstruction phi a xi]
    exact (map_ne_zero_iff phi hphi).2 hpair.2.1
  · rw [← map_incidenceCenteredNormObstruction phi a eta]
    exact (map_ne_zero_iff phi hphi).2 hpair.2.2

/-- A nonzero ordered moving coefficient pair remains nonzero after
injective scalar extension. -/
theorem movingCoefficientPair_ne_zero_map
    {L : Type*} [Field L] (phi : K →+* L)
    (hphi : Function.Injective phi)
    {B C : K} (hpair : (B, C) ≠ (0, 0)) :
    (phi B, phi C) ≠ (0, 0) := by
  intro hzero
  apply hpair
  have hB : phi B = 0 := congrArg Prod.fst hzero
  have hC : phi C = 0 := congrArg Prod.snd hzero
  exact Prod.ext
    (hphi (hB.trans (map_zero phi).symm))
    (hphi (hC.trans (map_zero phi).symm))

/-- Multiplication by a nonzero polynomial square does not alter any of the
four square classes in which the third radicand occurs. -/
theorem seven_not_isSquare_replace_third_by_square_mul
    {f g q h : K[X]}
    (hq : q ≠ 0)
    (hs :
      (¬ IsSquare (algebraMap K[X] (RatFunc K) f)) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) g)) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) h)) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g))) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * h))) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) (g * h))) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g * h)))) :
    (¬ IsSquare (algebraMap K[X] (RatFunc K) f)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) g)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (q ^ 2 * h))) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g))) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K) (f * (q ^ 2 * h)))) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K) (g * (q ^ 2 * h)))) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K) (f * g * (q ^ 2 * h)))) := by
  let i : K[X] →+* RatFunc K := algebraMap K[X] (RatFunc K)
  have hiq : i q ≠ 0 :=
    (map_ne_zero_iff i (RatFunc.algebraMap_injective K)).2 hq
  refine ⟨hs.1, hs.2.1, ?_, hs.2.2.2.1, ?_, ?_, ?_⟩
  · rw [map_mul, map_pow]
    exact fun hsquare =>
      hs.2.2.1 ((isSquare_sq_mul_iff (i q) (i h) hiq).1 hsquare)
  · rw [show f * (q ^ 2 * h) = q ^ 2 * (f * h) by ring,
      map_mul, map_pow]
    exact fun hsquare =>
      hs.2.2.2.2.1
        ((isSquare_sq_mul_iff (i q) (i (f * h)) hiq).1 hsquare)
  · rw [show g * (q ^ 2 * h) = q ^ 2 * (g * h) by ring,
      map_mul, map_pow]
    exact fun hsquare =>
      hs.2.2.2.2.2.1
        ((isSquare_sq_mul_iff (i q) (i (g * h)) hiq).1 hsquare)
  · rw [show f * g * (q ^ 2 * h) = q ^ 2 * (f * g * h) by ring,
      map_mul, map_pow]
    exact fun hsquare =>
      hs.2.2.2.2.2.2
        ((isSquare_sq_mul_iff (i q) (i (f * g * h)) hiq).1 hsquare)

/-- Over an algebraically closed field, multiplication by a nonzero
constant does not change a polynomial's nonsquare class in the rational
function field. -/
theorem not_isSquare_C_mul_of_not_isSquare_of_isAlgClosed
    {L : Type*} [Field L] [IsAlgClosed L]
    {c : L} (hc : c ≠ 0) {f : L[X]}
    (hf : ¬ IsSquare (algebraMap L[X] (RatFunc L) f)) :
    ¬ IsSquare
      (algebraMap L[X] (RatFunc L) (C c * f)) := by
  let p : L[X] := X ^ 2 - C c
  have hp : p.degree ≠ 0 := by
    dsimp only [p]
    rw [degree_X_pow_sub_C (by omega)]
    norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root p hp
  have hy' : y ^ 2 = c := by
    rw [Polynomial.IsRoot.def] at hy
    dsimp only [p] at hy
    simpa only [eval_sub, eval_pow, eval_X, eval_C,
      sub_eq_zero] using hy
  have hy0 : y ≠ 0 := by
    intro hzero
    apply hc
    rw [← hy', hzero, zero_pow (by omega)]
  let i : L[X] →+* RatFunc L := algebraMap L[X] (RatFunc L)
  have hiCy : i (C y) ≠ 0 :=
    (map_ne_zero_iff i (RatFunc.algebraMap_injective L)).2
      (C_ne_zero.2 hy0)
  rw [← hy', map_pow, map_mul]
  intro hsquare
  apply hf
  apply (isSquare_sq_mul_iff (i (C y)) (i f) hiCy).1
  simpa only [map_pow] using hsquare

/-- All seven original unequal connecting-cage products remain nonsquares
over the algebraic closure of the coefficient field.

The polynomials are displayed as scalar extensions of the original
incidence and full centered-norm pullbacks, rather than being rebuilt from
mapped parameters. -/
theorem
    connectingSevenOriginalRadicandProducts_not_isSquare_algebraicClosure
    (h2 : (2 : K) ≠ 0)
    {a : Coefficients K} {xi eta : K}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hpair : IsConnectingIncidencePair a xi eta)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    let phi : K →+* AlgebraicClosure K :=
      algebraMap K (AlgebraicClosure K)
    let f :=
      (incidencePulledRadicand a xi d).map phi
    let g :=
      (incidencePulledRadicand a eta d).map phi
    let h :=
      (centeredNormPulledRadicand a.a3 a.a1 d).map phi
    (¬ IsSquare
      (algebraMap (AlgebraicClosure K)[X]
        (RatFunc (AlgebraicClosure K)) f)) ∧
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) g)) ∧
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) h)) ∧
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) (f * g))) ∧
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) (f * h))) ∧
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) (g * h))) ∧
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) (f * g * h))) := by
  dsimp only
  let phi : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  let aE : Coefficients (AlgebraicClosure K) :=
    MiddleGame.mapCoefficients phi a
  have hphi : Function.Injective phi := phi.injective
  have h2E : (2 : AlgebraicClosure K) ≠ 0 := by
    simpa only [← map_ofNat phi] using
      (map_ne_zero_iff phi hphi).2 h2
  have hA1E : aE.a1 ^ 2 ≠ 4 := by
    change (phi a.a1) ^ 2 ≠ 4
    intro heq
    apply hA1
    apply hphi
    simpa only [map_pow, map_ofNat] using heq
  have hA2E : aE.a2 ^ 2 ≠ 4 := by
    change (phi a.a2) ^ 2 ≠ 4
    intro heq
    apply hA2
    apply hphi
    simpa only [map_pow, map_ofNat] using heq
  have hA3E : aE.a3 ^ 2 ≠ 4 := by
    change (phi a.a3) ^ 2 ≠ 4
    intro heq
    apply hA3
    apply hphi
    simpa only [map_pow, map_ofNat] using heq
  have hmovingE : (aE.a3, aE.a1) ≠ (0, 0) := by
    simpa only [aE, MiddleGame.mapCoefficients_a1,
      MiddleGame.mapCoefficients_a3] using
      movingCoefficientPair_ne_zero_map phi hphi hmoving
  have hxiE :
      OrderedTraceCandidateRegular aE.a1 aE.a2 aE.a3 (phi xi) := by
    simpa only [aE, MiddleGame.mapCoefficients_a1,
      MiddleGame.mapCoefficients_a2, MiddleGame.mapCoefficients_a3] using
      MiddleGame.orderedTraceCandidateRegular_map phi hphi hxi
  have hetaE :
      OrderedTraceCandidateRegular aE.a1 aE.a2 aE.a3 (phi eta) := by
    simpa only [aE, MiddleGame.mapCoefficients_a1,
      MiddleGame.mapCoefficients_a2, MiddleGame.mapCoefficients_a3] using
      MiddleGame.orderedTraceCandidateRegular_map phi hphi heta
  have hpairE :
      IsConnectingIncidencePair aE (phi xi) (phi eta) := by
    simpa only [aE] using
      isConnectingIncidencePair_map phi hphi hA2 hpair
  have hdegreeE : (d : AlgebraicClosure K) ≠ 0 := by
    have hdegreeMap : phi (d : K) ≠ 0 :=
      (map_ne_zero_iff phi hphi).2 hdegree
    simpa only [map_natCast] using hdegreeMap
  let fE := incidencePulledRadicand aE (phi xi) d
  let gE := incidencePulledRadicand aE (phi eta) d
  let rE := centeredNormReducedPulledRadicand aE.a3 aE.a1 d
  let qE := centeredNormForcedFactor aE.a3 aE.a1 d
  have hsReduced :
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) fE)) ∧
        (¬ IsSquare
          (algebraMap (AlgebraicClosure K)[X]
            (RatFunc (AlgebraicClosure K)) gE)) ∧
        (¬ IsSquare
          (algebraMap (AlgebraicClosure K)[X]
            (RatFunc (AlgebraicClosure K)) rE)) ∧
        (¬ IsSquare
          (algebraMap (AlgebraicClosure K)[X]
            (RatFunc (AlgebraicClosure K)) (fE * gE))) ∧
        (¬ IsSquare
          (algebraMap (AlgebraicClosure K)[X]
            (RatFunc (AlgebraicClosure K)) (fE * rE))) ∧
        (¬ IsSquare
          (algebraMap (AlgebraicClosure K)[X]
            (RatFunc (AlgebraicClosure K)) (gE * rE))) ∧
        (¬ IsSquare
          (algebraMap (AlgebraicClosure K)[X]
            (RatFunc (AlgebraicClosure K)) (fE * gE * rE))) := by
    exact connectingSevenRadicandProducts_not_isSquare_ratFunc
      h2E hA1E hA2E hA3E hmovingE hxiE hetaE hpairE hd hdegreeE
  have hqE : qE ≠ 0 :=
    centeredNormForcedFactor_ne_zero aE.a3 aE.a1 hd
  have hsFull :
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) fE)) ∧
        (¬ IsSquare
          (algebraMap (AlgebraicClosure K)[X]
            (RatFunc (AlgebraicClosure K)) gE)) ∧
        (¬ IsSquare
          (algebraMap (AlgebraicClosure K)[X]
            (RatFunc (AlgebraicClosure K))
            (centeredNormPulledRadicand aE.a3 aE.a1 d))) ∧
        (¬ IsSquare
          (algebraMap (AlgebraicClosure K)[X]
            (RatFunc (AlgebraicClosure K)) (fE * gE))) ∧
        (¬ IsSquare
          (algebraMap (AlgebraicClosure K)[X]
            (RatFunc (AlgebraicClosure K))
            (fE * centeredNormPulledRadicand aE.a3 aE.a1 d))) ∧
        (¬ IsSquare
          (algebraMap (AlgebraicClosure K)[X]
            (RatFunc (AlgebraicClosure K))
            (gE * centeredNormPulledRadicand aE.a3 aE.a1 d))) ∧
        (¬ IsSquare
          (algebraMap (AlgebraicClosure K)[X]
            (RatFunc (AlgebraicClosure K))
            (fE * gE *
              centeredNormPulledRadicand aE.a3 aE.a1 d))) := by
    rw [centeredNormPulledRadicand_eq_forcedFactor_sq_mul_reduced]
    exact seven_not_isSquare_replace_third_by_square_mul hqE hsReduced
  simpa only [fE, gE, aE, phi, MiddleGame.mapCoefficients_a1,
    MiddleGame.mapCoefficients_a3, ← map_incidencePulledRadicand,
    ← map_centeredNormPulledRadicand] using hsFull

/-- Arbitrary nonzero constant multiples of all seven original products
remain nonsquares over the algebraic closure.  In particular this covers
the inverse-character scalar multiplying the centered-norm equation in the
three-cover model. -/
theorem
    connectingSevenOriginalRadicandProducts_scalarMultiples_not_isSquare_algebraicClosure
    (h2 : (2 : K) ≠ 0)
    {a : Coefficients K} {xi eta : K}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hpair : IsConnectingIncidencePair a xi eta)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0)
    {cf cg ch cfg cfh cgh cfgh : AlgebraicClosure K}
    (hcf : cf ≠ 0) (hcg : cg ≠ 0) (hch : ch ≠ 0)
    (hcfg : cfg ≠ 0) (hcfh : cfh ≠ 0) (hcgh : cgh ≠ 0)
    (hcfgh : cfgh ≠ 0) :
    let phi : K →+* AlgebraicClosure K :=
      algebraMap K (AlgebraicClosure K)
    let f :=
      (incidencePulledRadicand a xi d).map phi
    let g :=
      (incidencePulledRadicand a eta d).map phi
    let h :=
      (centeredNormPulledRadicand a.a3 a.a1 d).map phi
    (¬ IsSquare
      (algebraMap (AlgebraicClosure K)[X]
        (RatFunc (AlgebraicClosure K)) (C cf * f))) ∧
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) (C cg * g))) ∧
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) (C ch * h))) ∧
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) (C cfg * (f * g)))) ∧
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) (C cfh * (f * h)))) ∧
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K)) (C cgh * (g * h)))) ∧
      (¬ IsSquare
        (algebraMap (AlgebraicClosure K)[X]
          (RatFunc (AlgebraicClosure K))
          (C cfgh * (f * g * h)))) := by
  dsimp only
  obtain ⟨hf, hg, hh, hfg, hfh, hgh, hfgh⟩ :=
    connectingSevenOriginalRadicandProducts_not_isSquare_algebraicClosure
      h2 hA1 hA2 hA3 hmoving hxi heta hpair hd hdegree
  exact
    ⟨not_isSquare_C_mul_of_not_isSquare_of_isAlgClosed hcf hf,
      not_isSquare_C_mul_of_not_isSquare_of_isAlgClosed hcg hg,
      not_isSquare_C_mul_of_not_isSquare_of_isAlgClosed hch hh,
      not_isSquare_C_mul_of_not_isSquare_of_isAlgClosed hcfg hfg,
      not_isSquare_C_mul_of_not_isSquare_of_isAlgClosed hcfh hfh,
      not_isSquare_C_mul_of_not_isSquare_of_isAlgClosed hcgh hgh,
      not_isSquare_C_mul_of_not_isSquare_of_isAlgClosed hcfgh hfgh⟩

end

end GenMarkoff.General.Cage
