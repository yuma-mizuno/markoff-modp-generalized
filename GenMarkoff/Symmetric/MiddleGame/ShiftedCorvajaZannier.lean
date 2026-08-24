import GenMarkoff.Symmetric.MiddleGame.ShiftedTraceEquation
import GenMarkoff.TraceCurve.ShiftedCoverAbsoluteIrreducibility
import BGS.Markoff.MiddleGame.CorvajaZannierFromGeneral

/-!
# Corvaja--Zannier for the shifted symmetric trace curve

The affine center in an equal-coefficient generalized Markoff fiber changes
the middle-game trace equation to

`h + sigma * h⁻¹ + gamma = k + k⁻¹`.

This module verifies the geometric hypotheses of the general
Corvaja--Zannier plane-curve theorem for its degree-one cleared equation and
applies the theorem to the finite subgroup solution set.  The additive shift
is fixed by both deck involutions, so the non-subtorus argument survives.
-/

namespace GenMarkoff.Symmetric.MiddleGame

open BGS.Markoff Polynomial

noncomputable section

section GeometricCurve

variable {K : Type*} [Field K]

/-- The normalized degree-one shifted trace curve in torus coordinate order
`(k,h)`. -/
def shiftedWeightedTraceTorusClosurePolynomial (sigma gamma : K) :
    MvPolynomial (Fin 2) K :=
  shiftedTraceCoverPolynomial 1 sigma gamma 1 1

/-- On nonzero coordinates, the cleared polynomial is exactly the shifted
weighted trace equation. -/
theorem eval_shiftedWeightedTraceTorusClosurePolynomial_eq_zero_iff
    (sigma gamma : K) (k h : Kˣ) :
    MvPolynomial.eval ![(k : K), (h : K)]
        (shiftedWeightedTraceTorusClosurePolynomial sigma gamma) = 0 ↔
      weightedSplitTorusTrace 1 sigma h + gamma = splitTorusTrace k := by
  rw [shiftedWeightedTraceTorusClosurePolynomial,
    eval_shiftedTraceCoverPolynomial]
  simp only [pow_one, one_mul, weightedSplitTorusTrace, splitTorusTrace,
    Units.val_inv_eq_inv_val]
  have hk : (k : K) ≠ 0 := Units.ne_zero k
  have hh : (h : K) ≠ 0 := Units.ne_zero h
  field_simp [hk, hh]
  constructor <;> intro heq <;> linear_combination heq

/-- The shifted degree-one closure is absolutely irreducible under the exact
branch-discriminant hypotheses. -/
theorem shiftedWeightedTraceTorusClosurePolynomial_absolutelyIrreducible
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (shiftedWeightedTraceTorusClosurePolynomial sigma gamma)) := by
  exact shiftedTraceDegreeOneCoverPolynomial_absolutelyIrreducible
    sigma gamma h2 hsigma hD2

end GeometricCurve

section CharacterPowers

variable {F : Type*} [Field F] [Infinite F]

/-- No fixed nonzero integer power is identically one on the units of an
infinite field. -/
private theorem exists_unit_zpow_ne_one_shifted (n : ℤ) (hn : n ≠ 0) :
    ∃ u : Fˣ, u ^ n ≠ 1 := by
  by_contra h
  push Not at h
  let m := n.natAbs
  let q : Polynomial F := Polynomial.X ^ m - 1
  have hm : m ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have hqDegree : q.natDegree = m := by
    simpa [q] using
      (Polynomial.natDegree_X_pow_sub_C (R := F) (n := m) (r := 1))
  have hq : q ≠ 0 := by
    intro hzero
    have : q.natDegree = 0 := by simp [hzero]
    omega
  have hXq : Polynomial.X * q ≠ 0 :=
    mul_ne_zero Polynomial.X_ne_zero hq
  apply hXq
  apply Polynomial.zero_of_eval_zero
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · let u : Fˣ := Units.mk0 x hx
    have hu : u ^ m = 1 := pow_natAbs_eq_one.mpr (h u)
    have hxpow : x ^ m = 1 := by
      have hval := congrArg (fun v : Fˣ ↦ (v : F)) hu
      simpa [u] using hval
    simp [q, hxpow]

end CharacterPowers

section CurveProjections

variable {F : Type*} [Field F] [IsAlgClosed F]

/-- Every right torus coordinate occurs on a shifted trace curve when
`sigma` is nonzero. -/
private theorem exists_shiftedWeightedTraceCurve_point_over_right
    (sigma gamma : F) (hsigma : sigma ≠ 0) (k : Fˣ) :
    ∃ h : Fˣ,
      weightedSplitTorusTrace 1 sigma h + gamma = splitTorusTrace k := by
  let trace := splitTorusTrace k - gamma
  let q : Polynomial F :=
    Polynomial.X ^ 2 - Polynomial.C trace * Polynomial.X +
      Polynomial.C sigma
  have hqDegree : q.natDegree = 2 := by
    rw [show q = Polynomial.C (1 : F) * Polynomial.X ^ 2 +
        Polynomial.C (-trace) * Polynomial.X + Polynomial.C sigma by
      simp only [q, Polynomial.C_neg, Polynomial.C_1, one_mul]
      ring]
    exact Polynomial.natDegree_quadratic one_ne_zero
  have hq : q ≠ 0 := by
    intro hzero
    have : q.natDegree = 0 := by simp [hzero]
    omega
  have hqDegreeBot : q.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hq, hqDegree]
    norm_num
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q hqDegreeBot
  have hxzero : x ≠ 0 := by
    intro hzero
    subst x
    simp [Polynomial.IsRoot.def, q, hsigma] at hx
  refine ⟨Units.mk0 x hxzero, ?_⟩
  simp only [weightedSplitTorusTrace, Units.val_mk0,
    Units.val_inv_eq_inv_val, one_mul]
  change x + sigma * x⁻¹ + gamma = splitTorusTrace k
  have hxeq : x ^ 2 - trace * x + sigma = 0 := by
    simpa [Polynomial.IsRoot.def, q] using hx
  field_simp [hxzero]
  dsimp [trace] at hxeq
  linear_combination hxeq

/-- Every left torus coordinate occurs on the shifted trace curve. -/
private theorem exists_shiftedWeightedTraceCurve_point_over_left
    (sigma gamma : F) (h : Fˣ) :
    ∃ k : Fˣ,
      weightedSplitTorusTrace 1 sigma h + gamma = splitTorusTrace k := by
  let trace := weightedSplitTorusTrace 1 sigma h + gamma
  let q : Polynomial F :=
    Polynomial.X ^ 2 - Polynomial.C trace * Polynomial.X + 1
  have hqDegree : q.natDegree = 2 := by
    rw [show q = Polynomial.C (1 : F) * Polynomial.X ^ 2 +
        Polynomial.C (-trace) * Polynomial.X + Polynomial.C 1 by
      simp only [q, Polynomial.C_neg, Polynomial.C_1, one_mul]
      ring]
    exact Polynomial.natDegree_quadratic one_ne_zero
  have hq : q ≠ 0 := by
    intro hzero
    have : q.natDegree = 0 := by simp [hzero]
    omega
  have hqDegreeBot : q.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hq, hqDegree]
    norm_num
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q hqDegreeBot
  have hxzero : x ≠ 0 := by
    intro hzero
    subst x
    simp [Polynomial.IsRoot.def, q] at hx
  refine ⟨Units.mk0 x hxzero, ?_⟩
  change trace = x + x⁻¹
  have hxeq : x ^ 2 - trace * x + 1 = 0 := by
    simpa [Polynomial.IsRoot.def, q] using hx
  field_simp [hxzero]
  linear_combination -hxeq

end CurveProjections

section DeckInvolutions

variable {F : Type*} [Field F]

private theorem splitTorusTrace_inv_shifted (k : Fˣ) :
    splitTorusTrace k⁻¹ = splitTorusTrace k := by
  simp only [splitTorusTrace, Units.val_inv_eq_inv_val, inv_inv]
  exact add_comm _ _

/-- The shifted term `gamma` is fixed by the weighted-coordinate deck
involution `h ↦ sigma * h⁻¹`. -/
private theorem shiftedWeightedSplitTorusTrace_deck_involution
    (sigma gamma : F) (hsigma : sigma ≠ 0) (h : Fˣ) :
    let q : Fˣ := Units.mk0 sigma hsigma
    weightedSplitTorusTrace 1 sigma (q * h⁻¹) + gamma =
      weightedSplitTorusTrace 1 sigma h + gamma := by
  dsimp
  simp only [weightedSplitTorusTrace, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_mk0, one_mul]
  field_simp [hsigma, Units.ne_zero h]
  ring

end DeckInvolutions

section NonSubtorus

variable {K : Type*} [Field K]

/-- Equation-level non-specialness of the complete shifted trace curve. -/
theorem shiftedWeightedTraceCurve_notSubtorusTranslate
    (sigma gamma : K) (hsigma : sigma ≠ 0) :
    ∀ (a b : ℤ), (a ≠ 0 ∨ b ≠ 0) →
      ∀ c : (AlgebraicClosure K)ˣ,
        ∃ k h : (AlgebraicClosure K)ˣ,
          weightedSplitTorusTrace 1
              (algebraMap K (AlgebraicClosure K) sigma) h +
              algebraMap K (AlgebraicClosure K) gamma = splitTorusTrace k ∧
          k ^ a * h ^ b ≠ c := by
  let sigmaL : AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K) sigma
  let gammaL : AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K) gamma
  have hsigmaL : sigmaL ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective).mpr hsigma
  intro a b hab c
  by_contra hvaries
  push Not at hvaries
  have haUniversal : ∀ k : (AlgebraicClosure K)ˣ, k ^ (2 * a) = 1 := by
    intro k
    obtain ⟨h, hcurve⟩ :=
      exists_shiftedWeightedTraceCurve_point_over_right
        sigmaL gammaL hsigmaL k
    have hcurveInv :
        weightedSplitTorusTrace 1 sigmaL h + gammaL =
          splitTorusTrace k⁻¹ := by
      rw [splitTorusTrace_inv_shifted]
      exact hcurve
    have hvalue := hvaries k h hcurve
    have hvalueInv := hvaries k⁻¹ h hcurveInv
    have hpower : k ^ a = (k⁻¹) ^ a := by
      exact mul_right_cancel (hvalue.trans hvalueInv.symm)
    have hpowerInv : k ^ a = (k ^ a)⁻¹ := by
      simpa only [inv_zpow] using hpower
    have hsquare : k ^ a * k ^ a = 1 :=
      eq_inv_iff_mul_eq_one.mp hpowerInv
    calc
      k ^ (2 * a) = k ^ (a + a) := by
        congr 1
        ring
      _ = k ^ a * k ^ a := zpow_add k a a
      _ = 1 := hsquare
  have ha : a = 0 := by
    by_contra ha
    have htwoa : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha
    obtain ⟨k, hk⟩ := exists_unit_zpow_ne_one_shifted
      (F := AlgebraicClosure K) (2 * a) htwoa
    exact hk (haUniversal k)
  have hbUniversal : ∀ h : (AlgebraicClosure K)ˣ, h ^ (2 * b) = 1 := by
    let q : (AlgebraicClosure K)ˣ := Units.mk0 sigmaL hsigmaL
    have hconstant :
        ∀ h : (AlgebraicClosure K)ˣ, h ^ (2 * b) = q ^ b := by
      intro h
      obtain ⟨k, hcurve⟩ :=
        exists_shiftedWeightedTraceCurve_point_over_left sigmaL gammaL h
      have hcurveDeck :
          weightedSplitTorusTrace 1 sigmaL (q * h⁻¹) + gammaL =
            splitTorusTrace k := by
        rw [shiftedWeightedSplitTorusTrace_deck_involution
          sigmaL gammaL hsigmaL]
        exact hcurve
      have hvalue := hvaries k h hcurve
      have hvalueDeck := hvaries k (q * h⁻¹) hcurveDeck
      have hpower : h ^ b = (q * h⁻¹) ^ b := by
        exact mul_left_cancel (hvalue.trans hvalueDeck.symm)
      have hpowerExpanded : h ^ b = q ^ b * (h ^ b)⁻¹ := by
        simpa only [mul_zpow, inv_zpow] using hpower
      have hsquare : h ^ b * h ^ b = q ^ b := by
        calc
          h ^ b * h ^ b = (q ^ b * (h ^ b)⁻¹) * h ^ b := by
            exact congrArg (fun z ↦ z * h ^ b) hpowerExpanded
          _ = q ^ b := by simp
      calc
        h ^ (2 * b) = h ^ (b + b) := by
          congr 1
          ring
        _ = h ^ b * h ^ b := zpow_add h b b
        _ = q ^ b := hsquare
    have hq : q ^ b = 1 := by
      have hone := hconstant (1 : (AlgebraicClosure K)ˣ)
      simpa using hone.symm
    intro h
    exact (hconstant h).trans hq
  have hb : b = 0 := by
    by_contra hb
    have htwob : 2 * b ≠ 0 := mul_ne_zero (by norm_num) hb
    obtain ⟨h, hh⟩ := exists_unit_zpow_ne_one_shifted
      (F := AlgebraicClosure K) (2 * b) htwob
    exact hh (hbUniversal h)
  exact hab.elim (fun hne ↦ hne ha) (fun hne ↦ hne hb)

/-- The equation-level deck-involution theorem gives the exact general
plane-curve non-subtorus condition. -/
theorem shiftedWeightedTraceTorusClosurePolynomial_notSubtorusTranslate
    (sigma gamma : K) (hsigma : sigma ≠ 0) :
    BGS.External.TorusCurveNotSubtorusTranslate
      (shiftedWeightedTraceTorusClosurePolynomial sigma gamma) := by
  intro a b hab c
  obtain ⟨k, h, hcurve, hcharacter⟩ :=
    shiftedWeightedTraceCurve_notSubtorusTranslate sigma gamma hsigma
      a b hab c
  refine ⟨k, h, ?_, hcharacter⟩
  rw [shiftedWeightedTraceTorusClosurePolynomial,
    map_shiftedTraceCoverPolynomial]
  simpa [shiftedWeightedTraceTorusClosurePolynomial] using
    (eval_shiftedWeightedTraceTorusClosurePolynomial_eq_zero_iff
      (algebraMap K (AlgebraicClosure K) sigma)
      (algebraMap K (AlgebraicClosure K) gamma) k h).2 hcurve

end NonSubtorus

section PlaneCurveHypotheses

variable {K : Type*} [Field K]

theorem shiftedWeightedTraceTorusClosurePolynomial_pderiv_first_ne_zero
    (sigma gamma : K) (hsigma : sigma ≠ 0) :
    MvPolynomial.pderiv 0
      (shiftedWeightedTraceTorusClosurePolynomial sigma gamma) ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval ![(0 : K), (0 : K)]) hzero
  simp [shiftedWeightedTraceTorusClosurePolynomial,
    shiftedTraceCoverPolynomial] at heval
  exact hsigma heval

theorem shiftedWeightedTraceTorusClosurePolynomial_pderiv_second_ne_zero
    (sigma gamma : K) :
    MvPolynomial.pderiv 1
      (shiftedWeightedTraceTorusClosurePolynomial sigma gamma) ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval ![(0 : K), (0 : K)]) hzero
  simp [shiftedWeightedTraceTorusClosurePolynomial,
    shiftedTraceCoverPolynomial] at heval

private theorem shiftedTraceShiftMonomial_degreeOf_first_le_two
    (gamma : K) :
    MvPolynomial.degreeOf (0 : Fin 2)
        (MvPolynomial.C gamma * MvPolynomial.X 0 * MvPolynomial.X 1) ≤ 2 := by
  calc
    _ ≤ MvPolynomial.degreeOf (0 : Fin 2)
          (MvPolynomial.C gamma * MvPolynomial.X 0) +
        MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 1) :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ (MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.C gamma) +
          MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 0)) +
        MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 1) := by
      gcongr
      exact MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ 2 := by
      rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X,
        MvPolynomial.degreeOf_X]
      norm_num

private theorem shiftedTraceShiftMonomial_degreeOf_second_le_two
    (gamma : K) :
    MvPolynomial.degreeOf (1 : Fin 2)
        (MvPolynomial.C gamma * MvPolynomial.X 0 * MvPolynomial.X 1) ≤ 2 := by
  calc
    _ ≤ MvPolynomial.degreeOf (1 : Fin 2)
          (MvPolynomial.C gamma * MvPolynomial.X 0) +
        MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 1) :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ (MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.C gamma) +
          MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 0)) +
        MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 1) := by
      gcongr
      exact MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ 2 := by
      rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X,
        MvPolynomial.degreeOf_X]
      norm_num

private theorem shiftedWeightedTraceTorusClosurePolynomial_eq_unshifted_add
    (sigma gamma : K) :
    shiftedWeightedTraceTorusClosurePolynomial sigma gamma =
      splitTraceCoverPolynomial 1 sigma 1 1 +
        MvPolynomial.C gamma * MvPolynomial.X 0 * MvPolynomial.X 1 := by
  simp [shiftedWeightedTraceTorusClosurePolynomial,
    shiftedTraceCoverPolynomial, splitTraceCoverPolynomial]
  ring

theorem shiftedWeightedTraceTorusClosurePolynomial_hasBidegreeAtMost
    (sigma gamma : K) :
    BGS.External.HasBidegreeAtMost
      (shiftedWeightedTraceTorusClosurePolynomial sigma gamma) 2 2 := by
  have hfirst : MvPolynomial.degreeOf (0 : Fin 2)
      (shiftedWeightedTraceTorusClosurePolynomial sigma gamma) ≤ 2 := by
    rw [shiftedWeightedTraceTorusClosurePolynomial_eq_unshifted_add]
    refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
    · simpa using
        (splitTraceCoverPolynomial_degreeOf_first_le
          (1 : K) sigma 1 1)
    · exact shiftedTraceShiftMonomial_degreeOf_first_le_two gamma
  have hsecond : MvPolynomial.degreeOf (1 : Fin 2)
      (shiftedWeightedTraceTorusClosurePolynomial sigma gamma) ≤ 2 := by
    rw [shiftedWeightedTraceTorusClosurePolynomial_eq_unshifted_add]
    refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
    · simpa using
        (splitTraceCoverPolynomial_degreeOf_second_le
          (1 : K) sigma 1 1)
    · exact shiftedTraceShiftMonomial_degreeOf_second_le_two gamma
  intro monomial hmonomial
  exact ⟨
    (MvPolynomial.degreeOf_le_iff.mp hfirst) monomial hmonomial,
    (MvPolynomial.degreeOf_le_iff.mp hsecond) monomial hmonomial⟩

/-- All geometric hypotheses of the general Corvaja--Zannier theorem for the
shifted degree-one trace curve. -/
theorem shiftedWeightedTraceCurve_isCorvajaZannierPlaneCurve
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0) :
    BGS.External.IsCorvajaZannierPlaneCurve
      (shiftedWeightedTraceTorusClosurePolynomial sigma gamma) := by
  exact ⟨
    shiftedWeightedTraceTorusClosurePolynomial_absolutelyIrreducible
      sigma gamma h2 hsigma hD2,
    shiftedWeightedTraceTorusClosurePolynomial_notSubtorusTranslate
      sigma gamma hsigma,
    shiftedWeightedTraceTorusClosurePolynomial_pderiv_first_ne_zero
      sigma gamma hsigma,
    shiftedWeightedTraceTorusClosurePolynomial_pderiv_second_ne_zero
      sigma gamma⟩

end PlaneCurveHypotheses

section FiniteSubgroupSolutions

variable {E : Type*} [Field E] [Fintype E] [DecidableEq E]

/-- A shifted subgroup solution, with coordinates swapped to the geometric
order `(k,h)`, lies in the corresponding general torsion intersection. -/
theorem shiftedWeightedTraceSubgroupSolutionToCurvePoint_mem_torsionIntersection
    (sigma gamma : E) (H₁ H₂ : Subgroup Eˣ) (z : H₁ × H₂)
    (hz : z ∈ shiftedWeightedTraceEquationSolutions 1 sigma gamma H₁ H₂) :
    weightedTraceSubgroupSolutionToCurvePoint H₁ H₂ z ∈
      BGS.External.torusCurveTorsionIntersection E
        (shiftedWeightedTraceTorusClosurePolynomial sigma gamma)
        (Nat.card H₂) (Nat.card H₁) := by
  letI := Fintype.ofFinite H₁
  letI := Fintype.ofFinite H₂
  rw [BGS.External.mem_torusCurveTorsionIntersection_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply (eval_shiftedWeightedTraceTorusClosurePolynomial_eq_zero_iff
      sigma gamma z.2 z.1).2
    exact mem_shiftedWeightedTraceEquationSolutions_iff.mp hz
  · have hpow : z.2 ^ Fintype.card H₂ = 1 := pow_card_eq_one
    have hval := congrArg (fun u : H₂ ↦ (u : Eˣ)) hpow
    change ((z.2 : Eˣ) ^ Fintype.card H₂) = 1 at hval
    simpa only [weightedTraceSubgroupSolutionToCurvePoint,
      Fintype.card_eq_nat_card] using hval
  · have hpow : z.1 ^ Fintype.card H₁ = 1 := pow_card_eq_one
    have hval := congrArg (fun u : H₁ ↦ (u : Eˣ)) hpow
    change ((z.1 : Eˣ) ^ Fintype.card H₁) = 1 at hval
    simpa only [weightedTraceSubgroupSolutionToCurvePoint,
      Fintype.card_eq_nat_card] using hval

/-- The finite shifted subgroup solution count injects into the exact general
torsion intersection. -/
theorem shiftedWeightedTraceEquationSolutions_card_le_torsionIntersection
    (sigma gamma : E) (H₁ H₂ : Subgroup Eˣ) :
    (shiftedWeightedTraceEquationSolutions 1 sigma gamma H₁ H₂).card ≤
      (BGS.External.torusCurveTorsionIntersection E
        (shiftedWeightedTraceTorusClosurePolynomial sigma gamma)
        (Nat.card H₂) (Nat.card H₁)).card := by
  classical
  exact Finset.card_le_card_of_injOn
    (weightedTraceSubgroupSolutionToCurvePoint H₁ H₂)
    (fun z hz ↦
      shiftedWeightedTraceSubgroupSolutionToCurvePoint_mem_torsionIntersection
        sigma gamma H₁ H₂ z hz)
    (weightedTraceSubgroupSolutionToCurvePoint_injective H₁ H₂).injOn

end FiniteSubgroupSolutions

section CorvajaZannierBound

/-- The general Corvaja--Zannier theorem gives the coefficient-`48` envelope
for the shifted degree-one torsion intersection.  The torsion orders are kept
explicit here, including their positivity and prime-to-characteristic
hypotheses. -/
theorem shiftedWeightedTraceTorsionIntersection_card_cast_le
    (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] [Fintype E] [DecidableEq E] [CharP E p]
    (sigma gamma : E) (firstOrder secondOrder : ℕ)
    (hpTwo : p ≠ 2) (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0)
    (hfirstPositive : 0 < firstOrder)
    (hsecondPositive : 0 < secondOrder)
    (hfirstPrime : ¬ p ∣ firstOrder)
    (hsecondPrime : ¬ p ∣ secondOrder) :
    ((BGS.External.torusCurveTorsionIntersection E
      (shiftedWeightedTraceTorusClosurePolynomial sigma gamma)
      firstOrder secondOrder).card : ℝ) ≤
        corvajaZannierTraceUpperBound p secondOrder firstOrder := by
  have hRingChar : ringChar E ≠ 2 := by
    rw [ringChar.eq E p]
    exact hpTwo
  have h2 : (2 : E) ≠ 0 := Ring.two_ne_zero hRingChar
  have hsource :=
    BGS.CorvajaZannier.generalCorvajaZannierPlaneCurveTheorem p E
      (shiftedWeightedTraceTorusClosurePolynomial sigma gamma)
      2 2 firstOrder secondOrder (by norm_num) (by norm_num)
      (shiftedWeightedTraceTorusClosurePolynomial_hasBidegreeAtMost
        sigma gamma)
      (shiftedWeightedTraceCurve_isCorvajaZannierPlaneCurve
        sigma gamma h2 hsigma hD2)
      hfirstPositive hsecondPositive hfirstPrime hsecondPrime
  rw [show BGS.External.planeTorusEulerCharacteristicBound 2 2 = 8 by
    norm_num [BGS.External.planeTorusEulerCharacteristicBound]] at hsource
  exact hsource.trans <| by
    simpa [corvajaZannierTraceUpperBound,
      mul_comm, mul_left_comm, mul_assoc] using
      (corvajaZannierCorollaryTwoNumericalBound_bidegree_two_euler_eight_le
        p firstOrder secondOrder)

/-- Final shifted middle-game bound for two multiplicative subgroups.  Their
orders are positive and prime to `p` automatically, so only the genuine
geometric conditions `p ≠ 2`, `sigma ≠ 0`, and `D₂ ≠ 0` remain as arguments. -/
theorem shiftedWeightedTraceEquationSolutions_card_cast_le_corvajaZannier
    (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] [Fintype E] [DecidableEq E] [CharP E p]
    (sigma gamma : E) (H₁ H₂ : Subgroup Eˣ)
    (hpTwo : p ≠ 2) (hsigma : sigma ≠ 0)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0) :
    ((shiftedWeightedTraceEquationSolutions
      1 sigma gamma H₁ H₂).card : ℝ) ≤
        corvajaZannierTraceUpperBound p (Nat.card H₁) (Nat.card H₂) := by
  have hfinite :
      ((shiftedWeightedTraceEquationSolutions
        1 sigma gamma H₁ H₂).card : ℝ) ≤
        ((BGS.External.torusCurveTorsionIntersection E
          (shiftedWeightedTraceTorusClosurePolynomial sigma gamma)
          (Nat.card H₂) (Nat.card H₁)).card : ℝ) := by
    exact_mod_cast
      shiftedWeightedTraceEquationSolutions_card_le_torsionIntersection
        sigma gamma H₁ H₂
  obtain ⟨hH₁Prime, hH₂Prime⟩ :=
    weightedTraceCurveTorsionIntersection_orders_primeToCharacteristic
      p H₁ H₂
  have htorus := shiftedWeightedTraceTorsionIntersection_card_cast_le
    p E sigma gamma (Nat.card H₂) (Nat.card H₁)
      hpTwo hsigma hD2 Nat.card_pos Nat.card_pos hH₂Prime hH₁Prime
  exact hfinite.trans htorus

end CorvajaZannierBound

end

end GenMarkoff.Symmetric.MiddleGame
