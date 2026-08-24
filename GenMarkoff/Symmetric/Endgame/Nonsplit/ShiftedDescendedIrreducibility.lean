import GenMarkoff.Symmetric.Endgame.Nonsplit.ShiftedDescendedTraceCurve
import BGS.Markoff.Endgame.Nonsplit.DescendedIrreducibility

/-!
# Absolute irreducibility of the shifted descended nonsplit curve

This file transports the arbitrary-weight shifted split cover through the
Cayley linear-fractional automorphism.  The shift contributes `gamma * Q^d`
to the middle coefficient; because this term is divisible by `Q`, it does
not change the coprimality needed for Gauss's lemma.
-/

namespace GenMarkoff.Symmetric.Endgame.Nonsplit

open Polynomial
open BGS.Markoff

noncomputable section

variable (p : ℕ) [Fact p.Prime]

private abbrev F := ZMod p
private abbrev E := quadraticFiniteField p

/-- The shifted split cover in the ordinary `(variable 0)`-outer iterated
polynomial coordinates. -/
theorem finTwoToIteratedPolynomial_shiftedTraceCoverPolynomial_general
    {K : Type*} [Field K]
    (alpha beta gamma : K) (e d : ℕ) :
    finTwoToIteratedPolynomial
        (shiftedTraceCoverPolynomial alpha beta gamma e d) =
      monomial (2 * e) (-(X ^ d)) +
        monomial e
          (C alpha * X ^ (2 * d) + C beta + C gamma * X ^ d) +
        C (-(X ^ d)) := by
  simp [shiftedTraceCoverPolynomial, ← C_mul_X_pow_eq_monomial]
  ring

theorem finTwoToIteratedPolynomial_shiftedTraceCoverPolynomial_general_natDegree
    {K : Type*} [Field K]
    (alpha beta gamma : K) (e d : ℕ) (he : 0 < e) :
    (finTwoToIteratedPolynomial
      (shiftedTraceCoverPolynomial alpha beta gamma e d)).natDegree =
        2 * e := by
  rw [finTwoToIteratedPolynomial_shiftedTraceCoverPolynomial_general]
  have htwoNe : 2 * e ≠ e := by omega
  have heTwoNe : e ≠ 2 * e := by omega
  have heNe : e ≠ 0 := by omega
  have htwoZero : 2 * e ≠ 0 := by omega
  have hcoeff :
      (monomial (2 * e) (-(X ^ d)) +
          monomial e
              (C alpha * X ^ (2 * d) + C beta + C gamma * X ^ d) +
          C (-(X ^ d))).coeff (2 * e) = -(X ^ d) := by
    rw [coeff_add, coeff_add, coeff_monomial, if_pos rfl,
      coeff_monomial, if_neg heTwoNe, coeff_C_ne_zero htwoZero]
    simp
  have hnonzero : -(X ^ d : Polynomial K) ≠ 0 :=
    neg_ne_zero.mpr (pow_ne_zero d X_ne_zero)
  apply le_antisymm
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact natDegree_monomial_le _
      · exact (natDegree_monomial_le _).trans (by omega)
    · simp
  · exact le_natDegree_of_ne_zero (by rwa [hcoeff])

/-- The shifted numerator after scalar extension to the quadratic splitting
field. -/
def extendedShiftedSeededCayleyNumerator
    (s : (E p)ˣ) (gamma : E p) (d : ℕ) : Polynomial (E p) :=
  extendedSeededCayleyNumerator p s d +
    C gamma * extendedCayleyNormFactor p ^ d

/-- Adding the shift term does not change coprimality with the Cayley norm
factor. -/
theorem extendedCayleyNormFactor_isCoprime_extendedShiftedSeededCayleyNumerator
    (s : (E p)ˣ) (gamma : E p) (d : ℕ) (hd : 0 < d) :
    IsCoprime (extendedCayleyNormFactor p)
      (extendedShiftedSeededCayleyNumerator p s gamma d) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  have hbase :=
    extendedCayleyNormFactor_isCoprime_extendedSeededCayleyNumerator
      p s (n + 1) (by omega)
  have hadd := hbase.add_mul_right_right
    (C gamma * extendedCayleyNormFactor p ^ n)
  have hshift :
      C gamma * extendedCayleyNormFactor p ^ (n + 1) =
        (C gamma * extendedCayleyNormFactor p ^ n) *
          extendedCayleyNormFactor p := by
    rw [pow_succ]
    ring
  rw [extendedShiftedSeededCayleyNumerator, hshift]
  exact hadd

theorem finTwoSecondToIteratedPolynomial_map_shiftedSeededNonsplitDescendedPolynomial
    (s : (E p)ˣ) (gamma : F p) (d e : ℕ) :
    finTwoSecondToIteratedPolynomial
        (MvPolynomial.map (algebraMap (F p) (E p))
          (shiftedSeededNonsplitDescendedPolynomial p s gamma d e)) =
      monomial (2 * e) (-(extendedCayleyNormFactor p ^ d)) +
        monomial e
          (extendedShiftedSeededCayleyNumerator p s
            (algebraMap (F p) (E p) gamma) d) +
        C (-(extendedCayleyNormFactor p ^ d)) := by
  rw [shiftedSeededNonsplitDescendedPolynomial]
  simp only [map_sub, map_mul, map_pow, map_add, map_one,
    finTwoSecondToIteratedPolynomial_map_univariateInFirstCoordinate,
    map_X, finTwoSecondToIteratedPolynomial_X_one]
  rw [shiftedSeededCayleyTraceNumeratorPolynomial_map,
    quadraticCayleyNormPolynomial_map]
  simp [← C_mul_X_pow_eq_monomial, extendedShiftedSeededCayleyNumerator,
    extendedSeededCayleyNumerator, extendedCayleyNormFactor,
    extendedCayleyNumeratorFactor, extendedCayleyDenominatorFactor,
    Nat.mul_comm]
  ring

/-- The shifted split cover transported through the Cayley automorphism.
The shift becomes `gamma * Q^d` in the middle coefficient. -/
theorem cayleyTransport_shiftedSplitIteratedPolynomial
    {K : Type*} [Field K]
    (alpha beta gamma r t : K) (e d : ℕ) (hrt : r ≠ t)
    (hdet : (1 : K) * (-t) - (-r) * 1 ≠ 0) :
    let phi := BGS.Algebra.ratFuncLinearFractionalEquiv
      (1 : K) (-r) 1 (-t) hdet
    let A : RatFunc K := RatFunc.X - RatFunc.C r
    let B : RatFunc K := RatFunc.X - RatFunc.C t
    let Q : Polynomial K := (X - C r) * (X - C t)
    let N : Polynomial K :=
      C alpha * (X - C r) ^ (2 * d) +
        C beta * (X - C t) ^ (2 * d) +
        C gamma * Q ^ d
    C (B ^ (2 * d)) *
        ((finTwoToIteratedPolynomial
          (shiftedTraceCoverPolynomial alpha beta gamma e d)).map
            (algebraMap K[X] (RatFunc K))).map phi.toRingHom =
      (monomial (2 * e) (-(Q ^ d)) +
        monomial e N + C (-(Q ^ d))).map
          (algebraMap K[X] (RatFunc K)) := by
  have hphi (f : K[X]) :
      (BGS.Algebra.ratFuncLinearFractionalEquiv
          (1 : K) (-r) 1 (-t) hdet).toRingEquiv.toRingHom
          (algebraMap K[X] (RatFunc K) f) =
        aeval (BGS.Algebra.ratFuncLinearFractionalValue
          (1 : K) (-r) 1 (-t)) f := by
    change BGS.Algebra.ratFuncLinearFractionalEquiv
        (1 : K) (-r) 1 (-t) hdet
          (algebraMap K[X] (RatFunc K) f) = _
    exact
      BGS.Algebra.ratFuncLinearFractionalEquiv_apply_algebraMap
        (1 : K) (-r) 1 (-t) hdet f
  have hconst (x : K) :
      BGS.Algebra.ratFuncLinearFractionalEquiv
          (1 : K) (-r) 1 (-t) hdet (RatFunc.C x) = RatFunc.C x := by
    change BGS.Algebra.ratFuncLinearFractionalEquiv
        (1 : K) (-r) 1 (-t) hdet
          (algebraMap K (RatFunc K) x) =
        algebraMap K (RatFunc K) x
    exact
      (BGS.Algebra.ratFuncLinearFractionalEquiv
        (1 : K) (-r) 1 (-t) hdet).commutes x
  dsimp only
  rw [finTwoToIteratedPolynomial_shiftedTraceCoverPolynomial_general]
  simp only [← C_mul_X_pow_eq_monomial, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X]
  rw [hphi]
  simp [BGS.Algebra.ratFuncLinearFractionalValue, aeval_def,
    eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
    ← C_mul_X_pow_eq_monomial]
  rw [hconst, hconst, hconst]
  let A : RatFunc K := RatFunc.X - RatFunc.C r
  let B : RatFunc K := RatFunc.X - RatFunc.C t
  let q : RatFunc K := A / B
  have hqExpanded :
      (RatFunc.X + -RatFunc.C r) / (RatFunc.X + -RatFunc.C t) = q := by
    simp [q, A, B, sub_eq_add_neg]
  have hB : RatFunc.X - RatFunc.C t ≠ (0 : RatFunc K) := by
    simpa only [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using
      RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero t)
  rw [hqExpanded]
  have hqD : B ^ (2 * d) * q ^ d = (A * B) ^ d := by
    have hB' : B ≠ 0 := by simpa [B] using hB
    dsimp only [q]
    rw [pow_mul, ← mul_pow]
    congr 1
    field_simp [hB']
  have hqTwoD : B ^ (2 * d) * q ^ (2 * d) = A ^ (2 * d) := by
    have hB' : B ≠ 0 := by simpa [B] using hB
    dsimp only [q]
    rw [← mul_pow]
    congr 1
    field_simp [hB']
  have hmiddle :
      B ^ (2 * d) *
          (RatFunc.C alpha * q ^ (2 * d) +
            RatFunc.C beta + RatFunc.C gamma * q ^ d) =
        RatFunc.C alpha * A ^ (2 * d) +
          RatFunc.C beta * B ^ (2 * d) +
          RatFunc.C gamma * (A * B) ^ d := by
    calc
      _ = RatFunc.C alpha * (B ^ (2 * d) * q ^ (2 * d)) +
          RatFunc.C beta * B ^ (2 * d) +
          RatFunc.C gamma * (B ^ (2 * d) * q ^ d) := by ring
      _ = _ := by rw [hqTwoD, hqD]
  have hnegative : B ^ (2 * d) * (-q ^ d) = -(A * B) ^ d := by
    rw [mul_neg, hqD]
  calc
    _ = C (B ^ (2 * d) * (-q ^ d)) * X ^ (2 * e) +
          C (B ^ (2 * d) *
            (RatFunc.C alpha * q ^ (2 * d) + RatFunc.C beta +
              RatFunc.C gamma * q ^ d)) * X ^ e +
          C (B ^ (2 * d) * (-q ^ d)) := by
      dsimp [B]
      simp only [map_add, map_sub, map_mul, map_pow, map_neg]
      ring
    _ = _ := by
      rw [hnegative, hmiddle]
      dsimp [A, B]
      simp only [map_add, map_mul, map_pow, map_sub, map_neg]
      ring

/-- Irreducibility descends through the Cayley model after any field
extension of the quadratic splitting field. -/
theorem map_shiftedSeededNonsplitDescendedPolynomial_irreducible_of_map_cover
    {L : Type*} [Field L] (φ : E p →+* L)
    (s : (E p)ˣ) (gamma : F p) (d e : ℕ)
    (hd : 0 < d) (he : 0 < e)
    (hcover : Irreducible
      (MvPolynomial.map φ
        (shiftedTraceCoverPolynomial
          (s : E p) ((s : E p) ^ p)
          (algebraMap (F p) (E p) gamma) e d))) :
    Irreducible
      (MvPolynomial.map (φ.comp (algebraMap (F p) (E p)))
        (shiftedSeededNonsplitDescendedPolynomial p s gamma d e)) := by
  let alpha : L := φ (s : E p)
  let beta : L := φ ((s : E p) ^ p)
  let shiftedGamma : L := φ (algebraMap (F p) (E p) gamma)
  let r : L := φ (quadraticNonbaseElement p ^ p)
  let t : L := φ (quadraticNonbaseElement p)
  have hsplit :
      MvPolynomial.map φ
          (shiftedTraceCoverPolynomial
            (s : E p) ((s : E p) ^ p)
            (algebraMap (F p) (E p) gamma) e d) =
        shiftedTraceCoverPolynomial alpha beta shiftedGamma e d := by
    rw [map_shiftedTraceCoverPolynomial]
  have hq : Irreducible
      (finTwoToIteratedPolynomial
        (shiftedTraceCoverPolynomial alpha beta shiftedGamma e d)) := by
    have h := hcover.map (finTwoToIteratedPolynomial (K := L))
    rwa [hsplit] at h
  have hqPrimitive :
      (finTwoToIteratedPolynomial
        (shiftedTraceCoverPolynomial alpha beta shiftedGamma e d)).IsPrimitive := by
    apply hq.isPrimitive
    rw [finTwoToIteratedPolynomial_shiftedTraceCoverPolynomial_general_natDegree
      alpha beta shiftedGamma e d he]
    omega
  have hqFraction : Irreducible
      ((finTwoToIteratedPolynomial
          (shiftedTraceCoverPolynomial alpha beta shiftedGamma e d)).map
        (algebraMap L[X] (RatFunc L))) :=
    hqPrimitive.irreducible_iff_irreducible_map_fraction_map.mp hq
  have hrt : r ≠ t :=
    φ.injective.ne (quadraticNonbaseElement_frobenius_ne_self p)
  have hdet : (1 : L) * (-t) - (-r) * 1 ≠ 0 := by
    rw [show (1 : L) * (-t) - (-r) * 1 = r - t by ring]
    exact sub_ne_zero.mpr hrt
  let cayleyEquiv := BGS.Algebra.ratFuncLinearFractionalEquiv
    (1 : L) (-r) 1 (-t) hdet
  have hqTransported : Irreducible
      (((finTwoToIteratedPolynomial
          (shiftedTraceCoverPolynomial alpha beta shiftedGamma e d)).map
        (algebraMap L[X] (RatFunc L))).map cayleyEquiv.toRingHom) :=
    hqFraction.map (Polynomial.mapAlgEquiv cayleyEquiv)
  let A : RatFunc L := RatFunc.X - RatFunc.C r
  let B : RatFunc L := RatFunc.X - RatFunc.C t
  let Q : Polynomial L := (X - C r) * (X - C t)
  let N : Polynomial L :=
    C alpha * (X - C r) ^ (2 * d) +
      C beta * (X - C t) ^ (2 * d) +
      C shiftedGamma * Q ^ d
  let R : Polynomial L[X] :=
    monomial (2 * e) (-(Q ^ d)) + monomial e N + C (-(Q ^ d))
  have hB : B ≠ 0 := by
    dsimp [B, t]
    simpa only [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using
      RatFunc.algebraMap_ne_zero
        (X_sub_C_ne_zero (φ (quadraticNonbaseElement p)))
  have hscale : IsUnit (C (B ^ (2 * d)) : Polynomial (RatFunc L)) := by
    rw [Polynomial.isUnit_C]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hB)
  have hRFraction : Irreducible
      (R.map (algebraMap L[X] (RatFunc L))) := by
    rw [← cayleyTransport_shiftedSplitIteratedPolynomial
      alpha beta shiftedGamma r t e d hrt hdet]
    exact (irreducible_isUnit_mul hscale).2 hqTransported
  have hcoprime : IsCoprime Q N := by
    have h :=
      (extendedCayleyNormFactor_isCoprime_extendedShiftedSeededCayleyNumerator
        p s (algebraMap (F p) (E p) gamma) d hd).map
          (Polynomial.mapRingHom φ)
    simpa [Q, N, alpha, beta, shiftedGamma, r, t,
      extendedShiftedSeededCayleyNumerator, extendedCayleyNormFactor,
      extendedSeededCayleyNumerator, extendedCayleyNumeratorFactor,
      extendedCayleyDenominatorFactor] using h
  have hRPrimitive : R.IsPrimitive := by
    have hcoprimePow : IsCoprime (Q ^ d) N := hcoprime.pow_left
    have hprimitive :=
      descendedIteratedPolynomial_isPrimitive_of_isCoprime
        (Q ^ d) N e he hcoprimePow
    simpa only [R] using hprimitive
  have hR : Irreducible R :=
    hRPrimitive.irreducible_iff_irreducible_map_fraction_map.mpr hRFraction
  have hdescendedIterated :
      finTwoSecondToIteratedPolynomial
          (MvPolynomial.map (φ.comp (algebraMap (F p) (E p)))
            (shiftedSeededNonsplitDescendedPolynomial p s gamma d e)) = R := by
    rw [← MvPolynomial.map_map]
    rw [finTwoSecondToIteratedPolynomial_map]
    rw [
      finTwoSecondToIteratedPolynomial_map_shiftedSeededNonsplitDescendedPolynomial]
    simp [R, Q, N, alpha, beta, shiftedGamma, r, t,
      extendedShiftedSeededCayleyNumerator, extendedCayleyNormFactor,
      extendedSeededCayleyNumerator, extendedCayleyNumeratorFactor,
      extendedCayleyDenominatorFactor]
  have hback := hR.map (finTwoSecondToIteratedPolynomial (K := L)).symm
  simpa [← hdescendedIterated] using hback

/-- Absolute irreducibility of the shifted descended curve follows from
absolute irreducibility of the shifted split cover. -/
theorem shiftedSeededNonsplitDescendedPolynomial_absolutelyIrreducible_of_cover
    (s : (E p)ˣ) (gamma : F p) (d e : ℕ)
    (hd : 0 < d) (he : 0 < e)
    (hcover : Irreducible
      (MvPolynomial.map
        (algebraMap (E p) (AlgebraicClosure (E p)))
        (shiftedTraceCoverPolynomial
          (s : E p) ((s : E p) ^ p)
          (algebraMap (F p) (E p) gamma) e d))) :
    Irreducible
      (MvPolynomial.map
        (algebraMap (F p) (AlgebraicClosure (F p)))
        (shiftedSeededNonsplitDescendedPolynomial p s gamma d e)) := by
  let K := AlgebraicClosure (E p)
  have hdescendedOverK : Irreducible
      (MvPolynomial.map
        ((algebraMap (E p) K).comp (algebraMap (F p) (E p)))
        (shiftedSeededNonsplitDescendedPolynomial p s gamma d e)) :=
    map_shiftedSeededNonsplitDescendedPolynomial_irreducible_of_map_cover
      p (algebraMap (E p) K) s gamma d e hd he hcover
  let closureEquiv : K ≃ₐ[F p] AlgebraicClosure (F p) :=
    IsAlgClosure.equivOfAlgebraic
      (F p) (E p) K (AlgebraicClosure (F p))
  have hmapped := hdescendedOverK.map
    (MvPolynomial.mapAlgEquiv (Fin 2) closureEquiv)
  have hcomp :
      (closureEquiv : K →+* AlgebraicClosure (F p)).comp
          ((algebraMap (E p) K).comp (algebraMap (F p) (E p))) =
        algebraMap (F p) (AlgebraicClosure (F p)) := by
    ext x
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact closureEquiv.commutes x
  have hmapped' : Irreducible
      (MvPolynomial.map
        ((closureEquiv : K →+* AlgebraicClosure (F p)).comp
          ((algebraMap (E p) K).comp (algebraMap (F p) (E p))))
        (shiftedSeededNonsplitDescendedPolynomial p s gamma d e)) := by
    simpa only [MvPolynomial.mapAlgEquiv_apply, MvPolynomial.map_map] using
      hmapped
  rw [hcomp] at hmapped'
  exact hmapped'

/-- The shifted descended curve attached to a nontrivial norm seed is
absolutely irreducible under the same explicit obstruction used for the
split cover. -/
theorem shiftedSeededNonsplitDescendedPolynomial_absolutelyIrreducible
    (hpTwo : p ≠ 2)
    (k : (F p)ˣ) (hk : k ≠ 1)
    (s : ↥(quadraticNormFiber p k)) (gamma : F p)
    (hD2 : shiftedTraceEvenObstruction (k : F p) gamma ≠ 0)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hdChar : (d : E p) ≠ 0) :
    Irreducible
      (MvPolynomial.map
        (algebraMap (F p) (AlgebraicClosure (F p)))
        (shiftedSeededNonsplitDescendedPolynomial p s.1 gamma d e)) := by
  apply shiftedSeededNonsplitDescendedPolynomial_absolutelyIrreducible_of_cover
    p s.1 gamma d e hd he
  exact shiftedSeededNonsplit_weightedCover_absolutelyIrreducible
    p hpTwo k hk s gamma hD2 d e hd he hdChar

end

end GenMarkoff.Symmetric.Endgame.Nonsplit
