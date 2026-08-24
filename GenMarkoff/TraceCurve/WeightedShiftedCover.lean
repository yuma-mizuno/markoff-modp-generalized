import GenMarkoff.TraceCurve.ShiftedCoverResidueBlocks
import BGS.Markoff.TraceCurve.WeightedOddCoprimeIrreducibility

/-!
# Arbitrary-weight shifted trace covers

The shifted-cover Kummer proof is normalized to the coefficient pair
`(1, sigma)`.  An actual one-step orbit, however, runs through a translated
torus coset and therefore has two separate nonzero weights `(alpha, beta)`.

Over the algebraic closure, choose an `e`-th root `c` of `alpha`.  Scaling the
second variable by `c` carries the normalized cover with
`sigma = alpha * beta` to the weighted cover, up to the nonzero scalar
`alpha`.  This is the shifted analogue of the scaling boundary in the pinned
BGS split endgame.
-/

namespace GenMarkoff

noncomputable section

variable {K : Type*} [Field K]

/-- Exact scaling identity from a normalized shifted cover to arbitrary
nonzero weights. -/
theorem finTwoSecondVariableScaleEquiv_normalizedShiftedCover
    (alpha beta gamma : K) (e d : ℕ) (c : Kˣ)
    (hc : (c : K) ^ e = alpha) :
    BGS.Markoff.finTwoSecondVariableScaleEquiv c
        (shiftedTraceCoverPolynomial (1 : K) (alpha * beta) gamma d e) =
      MvPolynomial.C alpha *
        shiftedTraceCoverPolynomial alpha beta gamma d e := by
  simp only [shiftedTraceCoverPolynomial, map_add, map_sub, map_mul, map_pow,
    BGS.Markoff.finTwoSecondVariableScaleEquiv_C,
    BGS.Markoff.finTwoSecondVariableScaleEquiv_X_zero,
    BGS.Markoff.finTwoSecondVariableScaleEquiv_X_one, map_one]
  simp only [mul_pow, ← map_pow]
  rw [Nat.mul_comm 2 e, pow_mul, hc]
  rw [map_pow]
  ring

/-- Absolute irreducibility of the shifted trace cover with arbitrary
nonzero weights.  The exceptional parameters depend only on the invariant
product `alpha * beta` and the affine shift `gamma`. -/
theorem weightedShiftedTraceCoverPolynomial_absolutelyIrreducible_of_positiveExponents
    (alpha beta gamma : K) (h2 : (2 : K) ≠ 0)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hproductOne : alpha * beta ≠ 1)
    (hD2 : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0)
    (e d : ℕ) (he : 0 < e) (heChar : (e : K) ≠ 0) (hd : 0 < d) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (shiftedTraceCoverPolynomial alpha beta gamma d e)) := by
  let phi : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  rw [map_shiftedTraceCoverPolynomial phi alpha beta gamma d e]
  have halphaL : phi alpha ≠ 0 :=
    (map_ne_zero_iff phi phi.injective).mpr halpha
  have hbetaL : phi beta ≠ 0 :=
    (map_ne_zero_iff phi phi.injective).mpr hbeta
  obtain ⟨c, hc⟩ :=
    IsAlgClosed.exists_pow_nat_eq (phi alpha) he
  have hcne : c ≠ 0 := by
    intro hc0
    apply halphaL
    rw [← hc]
    simp [hc0, Nat.ne_of_gt he]
  let cUnit : (AlgebraicClosure K)ˣ := Units.mk0 c hcne
  have hnormalized : Irreducible
      (shiftedTraceCoverPolynomial
        (1 : AlgebraicClosure K) (phi alpha * phi beta) (phi gamma) d e) := by
    have hnormalizedMap :=
      shiftedTraceCoverPolynomial_absolutelyIrreducible_of_positiveExponents
        (alpha * beta) gamma h2 (mul_ne_zero halpha hbeta)
        hproductOne hD2 e d he heChar hd
    rw [map_shiftedTraceCoverPolynomial
      phi (1 : K) (alpha * beta) gamma d e] at hnormalizedMap
    simpa only [map_one, map_mul] using hnormalizedMap
  have hscaled :=
    hnormalized.map
      (BGS.Markoff.finTwoSecondVariableScaleEquiv cUnit)
  have hscaleIdentity :
      BGS.Markoff.finTwoSecondVariableScaleEquiv cUnit
          (shiftedTraceCoverPolynomial
            (1 : AlgebraicClosure K) (phi alpha * phi beta) (phi gamma) d e) =
        MvPolynomial.C (phi alpha) *
          shiftedTraceCoverPolynomial
            (phi alpha) (phi beta) (phi gamma) d e := by
    apply finTwoSecondVariableScaleEquiv_normalizedShiftedCover
    simpa [cUnit] using hc
  rw [hscaleIdentity] at hscaled
  exact (irreducible_isUnit_mul
    (halphaL.isUnit.map
      (MvPolynomial.C : AlgebraicClosure K →+*
        MvPolynomial (Fin 2) (AlgebraicClosure K)))).mp hscaled

end

end GenMarkoff
