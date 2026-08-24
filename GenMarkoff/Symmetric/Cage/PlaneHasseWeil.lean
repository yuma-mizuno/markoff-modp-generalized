import GenMarkoff.Symmetric.Cage.PlaneModels

/-!
# Hasse--Weil estimates for the generalized incidence plane models

This module applies the single general affine Hasse--Weil input to the
diagonal and off-diagonal models.  The power exponent is proved prime to the
characteristic from its divisibility by the split-torus order.
-/

namespace GenMarkoff.Symmetric.Cage

open BGS.Markoff

noncomputable section

/-- A uniform point estimate for both generalized incidence plane models. -/
def IncidencePlanePointEstimate (coefficient : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
    ∀ (c xi eta : ZMod p),
      c ^ 2 ≠ 4 →
      OrderedTraceCandidateRegular c c c xi →
      OrderedTraceCandidateRegular c c c eta →
      ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
        |((BGS.External.affinePlaneCurveZeros (ZMod p)
              (incidenceDiagonalPlanePolynomial c xi d)).card : ℝ) -
            p| ≤
          (coefficient : ℝ) * Real.sqrt p * d ∧
        (IsHasseWeilReadyIncidencePair c xi eta →
          |((BGS.External.affinePlaneCurveZeros (ZMod p)
                (incidenceOffDiagonalPlanePolynomial c xi eta d)).card :
                  ℝ) -
              p| ≤
            (coefficient : ℝ) * Real.sqrt p * d)

/-- A positive divisor of the split-torus order is strictly smaller than
the prime characteristic. -/
lemma divisor_card_zmod_units_lt_prime
    {p d : ℕ} [Fact p.Prime] (hpTwo : 2 ≤ p)
    (hd : d ∣ Nat.card (ZMod p)ˣ) :
    d < p := by
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rw [hcard] at hd
  have hdLe : d ≤ p - 1 :=
    Nat.le_of_dvd (by omega) hd
  omega

/-- Every positive divisor exponent in the split-torus cover is nonzero in
`ZMod p`. -/
lemma divisor_card_zmod_units_ne_zero
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    {d : ℕ} (hd : d ∣ Nat.card (ZMod p)ˣ)
    (hdPositive : 0 < d) :
    (d : ZMod p) ≠ 0 :=
  natCast_ne_zero_zmod_of_pos_of_lt hdPositive
    (divisor_card_zmod_units_lt_prime (by omega) hd)

/-- The allowed general affine Hasse--Weil theorem gives uniform estimates
for both generalized incidence plane models. -/
theorem exists_incidencePlanePointEstimate_of_generalHasseWeil
    (hHasse :
      BGS.External.GeneralBivariateAffineHasseWeilTheorem) :
    ∃ coefficient : ℕ,
      0 < coefficient ∧
        IncidencePlanePointEstimate coefficient := by
  obtain ⟨generalCoefficient, hgeneralCoefficient, hgeneral⟩ :=
    hHasse
  let coefficient := 32 * generalCoefficient
  refine
    ⟨coefficient, by
      dsimp [coefficient]
      omega, ?_⟩
  intro p _ hpFive c xi eta hc hxi heta d hd hdPositive
  have h2 : (2 : ZMod p) ≠ 0 :=
    natCast_ne_zero_zmod_of_pos_of_lt
      (n := 2) (p := p) (by norm_num) (by omega)
  have hdegree : (d : ZMod p) ≠ 0 :=
    divisor_card_zmod_units_ne_zero
      p hpFive hd hdPositive
  have hDiagonal :=
    hgeneral (ZMod p)
      (incidenceDiagonalPlanePolynomial c xi d) 2 (4 * d)
      (by norm_num) (by omega)
      (incidenceDiagonalPlanePolynomial_hasBidegreeAtMost c xi d)
      (incidenceDiagonalPlanePolynomial_absolutelyIrreducible
        h2 hc hxi hdPositive hdegree)
  constructor
  · have hcard : Fintype.card (ZMod p) = p := ZMod.card p
    rw [hcard] at hDiagonal
    dsimp [coefficient]
    calc
      |((BGS.External.affinePlaneCurveZeros (ZMod p)
            (incidenceDiagonalPlanePolynomial c xi d)).card : ℝ) -
          p| ≤
          (generalCoefficient : ℝ) * Real.sqrt p *
            ((2 : ℕ) : ℝ) * ((4 * d : ℕ) : ℝ) :=
        hDiagonal
      _ = (8 * generalCoefficient : ℕ) *
          Real.sqrt p * d := by
        push_cast
        ring
      _ ≤ ((32 * generalCoefficient : ℕ) : ℝ) *
          Real.sqrt p * d := by
        push_cast
        have hnonnegative :
            0 ≤ (generalCoefficient : ℝ) *
              Real.sqrt p * (d : ℝ) := by
          positivity
        nlinarith
  · intro hpair
    have hOffDiagonal :=
      hgeneral (ZMod p)
        (incidenceOffDiagonalPlanePolynomial c xi eta d)
        4 (8 * d) (by norm_num) (by omega)
        (incidenceOffDiagonalPlanePolynomial_hasBidegreeAtMost
          c xi eta d)
        (incidenceOffDiagonalPlanePolynomial_absolutelyIrreducible
          h2 hc hxi heta hpair hdPositive hdegree)
    have hcard : Fintype.card (ZMod p) = p := ZMod.card p
    rw [hcard] at hOffDiagonal
    dsimp [coefficient]
    calc
      |((BGS.External.affinePlaneCurveZeros (ZMod p)
            (incidenceOffDiagonalPlanePolynomial c xi eta d)).card :
              ℝ) -
          p| ≤
          (generalCoefficient : ℝ) * Real.sqrt p *
            ((4 : ℕ) : ℝ) * ((8 * d : ℕ) : ℝ) :=
        hOffDiagonal
      _ = ((32 * generalCoefficient : ℕ) : ℝ) *
          Real.sqrt p * d := by
        push_cast
        ring

end

end GenMarkoff.Symmetric.Cage
