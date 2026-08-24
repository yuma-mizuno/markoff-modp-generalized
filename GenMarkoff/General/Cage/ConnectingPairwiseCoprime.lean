import GenMarkoff.General.Cage.CenteredReducedPulledRadicand

/-!
# Branch separation after the connecting-cage power pullback

The formal resultant in `ConnectingIncidenceAlgebra` separates an incidence
quadratic from the middle-axis centered-norm quadratic.  This file transports
that separation through the reciprocal trace substitution
`Y = u + u⁻¹` and the further power substitution `u = X^d`.

The centered pullback can have an even parabolic factor when its two
coefficients are equal or opposite.  Coprimality with the full centered
pullback is nevertheless the useful statement: it immediately descends to
any reduced representative obtained by removing that square factor.
-/

namespace GenMarkoff.General.Cage

open Polynomial

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- Scalar extension commutes with the centered-norm quadratic. -/
theorem map_orderedTraceCenteredNormPolynomial
    {L : Type*} [Field L] (phi : K →+* L) (B C : K) :
    (orderedTraceCenteredNormPolynomial B C).map phi =
      orderedTraceCenteredNormPolynomial (phi B) (phi C) := by
  simp [orderedTraceCenteredNormPolynomial, map_ofNat]

/-- A nonzero base resultant remains a branch-separation certificate after
both trace substitutions. -/
theorem
    incidencePulledRadicand_isCoprime_centeredNormPulledRadicand
    {a : Coefficients K} {xi : K}
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hobstruction : incidenceCenteredNormObstruction a xi ≠ 0)
    {d : ℕ} (hd : 0 < d) :
    IsCoprime (incidencePulledRadicand a xi d)
      (centeredNormPulledRadicand a.a3 a.a1 d) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (k := K) (AlgebraicClosure K)
      (incidencePulledRadicand a xi d)
      (centeredNormPulledRadicand a.a3 a.a1 d)).2
  intro t
  let phi : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  by_contra hcommon
  push Not at hcommon
  rcases hcommon with ⟨hincidenceRoot, hcenterRoot⟩
  have hincidenceRootMapped :
      eval t
          (incidencePulledRadicand
            (MiddleGame.mapCoefficients phi a) (phi xi) d) = 0 := by
    rw [← map_incidencePulledRadicand phi a xi d]
    simpa only [aeval_def, eval₂_eq_eval_map, phi] using hincidenceRoot
  have hcenterRootMapped :
      eval t
          (centeredNormPulledRadicand
            (phi a.a3) (phi a.a1) d) = 0 := by
    rw [← map_centeredNormPulledRadicand phi a.a3 a.a1 d]
    simpa only [aeval_def, eval₂_eq_eval_map, phi] using hcenterRoot
  have hLeadingK : incidenceLeadingCoefficient xi ≠ 0 := by
    simpa only [incidenceLeadingCoefficient,
      eval_orderedTraceDiscriminantPolynomial] using hxi.1
  have hLeading :
      incidenceLeadingCoefficient (phi xi) ≠ 0 := by
    have hmap :=
      (map_ne_zero_iff phi phi.injective).mpr hLeadingK
    simpa only [incidenceLeadingCoefficient, map_sub, map_pow,
      map_ofNat] using hmap
  have ht : t ≠ 0 := by
    intro ht
    subst t
    apply hLeading
    simpa only [eval_incidencePulledRadicand_zero
      (MiddleGame.mapCoefficients phi a) (phi xi) hd] using
      hincidenceRootMapped
  have hu : t ^ d ≠ 0 := pow_ne_zero d ht
  have hincidenceQuartic :
      incidenceReciprocalQuartic
        (MiddleGame.mapCoefficients phi a) (phi xi) (t ^ d) = 0 := by
    simpa only [eval_incidencePulledRadicand] using hincidenceRootMapped
  have hcenterQuartic :
      centeredNormReciprocalQuartic
        (phi a.a3) (phi a.a1) (t ^ d) = 0 := by
    simpa only [eval_centeredNormPulledRadicand] using hcenterRootMapped
  have hincidence :
      incidenceDiscriminant
        (MiddleGame.mapCoefficients phi a) (phi xi)
        (t ^ d + (t ^ d)⁻¹) = 0 := by
    have hidentity :=
      incidenceReciprocalQuartic_eq_mul_discriminant
        (MiddleGame.mapCoefficients phi a) (phi xi) (t ^ d) hu
    rw [hincidenceQuartic] at hidentity
    exact (mul_eq_zero.mp hidentity.symm).resolve_left
      (pow_ne_zero 2 hu)
  have hcenter :
      centeredNorm (phi a.a3) (phi a.a1)
        (t ^ d + (t ^ d)⁻¹) = 0 := by
    have hidentity :=
      centeredNormReciprocalQuartic_eq_mul_centeredNorm
        (phi a.a3) (phi a.a1) (t ^ d) hu
    rw [hcenterQuartic] at hidentity
    exact (mul_eq_zero.mp hidentity.symm).resolve_left
      (pow_ne_zero 2 hu)
  let middle : AlgebraicClosure K := t ^ d + (t ^ d)⁻¹
  have hincidencePolynomial :
      eval middle ((incidenceDiscriminantPolynomial a xi).map phi) = 0 := by
    rw [map_incidenceDiscriminantPolynomial,
      eval_incidenceDiscriminantPolynomial]
    exact hincidence
  have hcenterPolynomial :
      eval middle
          ((orderedTraceCenteredNormPolynomial a.a3 a.a1).map phi) = 0 := by
    rw [map_orderedTraceCenteredNormPolynomial,
      eval_orderedTraceCenteredNormPolynomial]
    simpa only [centeredNorm, discriminant] using hcenter
  have hincidenceDegree :
      ((incidenceDiscriminantPolynomial a xi).map phi).natDegree ≤ 2 := by
    calc
      ((incidenceDiscriminantPolynomial a xi).map phi).natDegree ≤
          (incidenceDiscriminantPolynomial a xi).natDegree :=
        Polynomial.natDegree_map_le
      _ = 2 := incidenceDiscriminantPolynomial_natDegree hxi
  have hcenterDegree :
      ((orderedTraceCenteredNormPolynomial a.a3 a.a1).map phi).natDegree ≤
        2 := by
    calc
      ((orderedTraceCenteredNormPolynomial a.a3 a.a1).map phi).natDegree ≤
          (orderedTraceCenteredNormPolynomial a.a3 a.a1).natDegree :=
        Polynomial.natDegree_map_le
      _ ≤ 2 := by
        simp only [orderedTraceCenteredNormPolynomial]
        compute_degree
  have hresultantMapped :
      Polynomial.resultant
          ((incidenceDiscriminantPolynomial a xi).map phi)
          ((orderedTraceCenteredNormPolynomial a.a3 a.a1).map phi)
          2 2 = 0 :=
    BGS.CorvajaZannier.resultant_eq_zero_of_common_root
      ((incidenceDiscriminantPolynomial a xi).map phi)
      ((orderedTraceCenteredNormPolynomial a.a3 a.a1).map phi)
      2 2 hincidenceDegree hcenterDegree (by left; norm_num)
      middle hincidencePolynomial hcenterPolynomial
  rw [Polynomial.resultant_map_map] at hresultantMapped
  have hresultant :
      Polynomial.resultant
          (incidenceDiscriminantPolynomial a xi)
          (orderedTraceCenteredNormPolynomial a.a3 a.a1) 2 2 ≠ 0 :=
    resultant_incidenceDiscriminant_centeredNorm_ne_zero
      a xi hobstruction
  exact
    (map_ne_zero_iff phi phi.injective).mpr hresultant
      hresultantMapped

/-- Both incidence pullbacks in a connecting pair are coprime to the full
middle centered-norm pullback. -/
theorem connectingIncidencePair_coprime_centeredNormPulledRadicand
    {a : Coefficients K} {xi eta : K}
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hpair : IsConnectingIncidencePair a xi eta)
    {d : ℕ} (hd : 0 < d) :
    IsCoprime (incidencePulledRadicand a xi d)
        (centeredNormPulledRadicand a.a3 a.a1 d) ∧
      IsCoprime (incidencePulledRadicand a eta d)
        (centeredNormPulledRadicand a.a3 a.a1 d) :=
  ⟨incidencePulledRadicand_isCoprime_centeredNormPulledRadicand
      hxi hpair.2.1 hd,
    incidencePulledRadicand_isCoprime_centeredNormPulledRadicand
      heta hpair.2.2 hd⟩

/-- The reduced centered pullback divides the full centered pullback. -/
theorem centeredNormReducedPulledRadicand_dvd
    (B C : K) (d : ℕ) :
    centeredNormReducedPulledRadicand B C d ∣
      centeredNormPulledRadicand B C d := by
  refine ⟨centeredNormForcedFactor B C d ^ 2, ?_⟩
  rw [centeredNormPulledRadicand_eq_forcedFactor_sq_mul_reduced]
  ac_rfl

/-- Both incidence pullbacks in a connecting pair are coprime to the
squarefree reduced representative of the centered-norm pullback. -/
theorem connectingIncidencePair_coprime_centeredNormReducedPulledRadicand
    {a : Coefficients K} {xi eta : K}
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hpair : IsConnectingIncidencePair a xi eta)
    {d : ℕ} (hd : 0 < d) :
    IsCoprime (incidencePulledRadicand a xi d)
        (centeredNormReducedPulledRadicand a.a3 a.a1 d) ∧
      IsCoprime (incidencePulledRadicand a eta d)
        (centeredNormReducedPulledRadicand a.a3 a.a1 d) := by
  obtain ⟨hxiFull, hetaFull⟩ :=
    connectingIncidencePair_coprime_centeredNormPulledRadicand
      hxi heta hpair hd
  exact
    ⟨IsCoprime.of_isCoprime_of_dvd_right hxiFull
        (centeredNormReducedPulledRadicand_dvd a.a3 a.a1 d),
      IsCoprime.of_isCoprime_of_dvd_right hetaFull
        (centeredNormReducedPulledRadicand_dvd a.a3 a.a1 d)⟩

end

end GenMarkoff.General.Cage
