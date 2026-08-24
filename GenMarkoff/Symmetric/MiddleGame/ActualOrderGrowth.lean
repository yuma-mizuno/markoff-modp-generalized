import GenMarkoff.Symmetric.MiddleGame.ActualDiagonalization
import GenMarkoff.Symmetric.MiddleGame.ActualMoveWiring
import GenMarkoff.Symmetric.MiddleGame.RegularTraceEscape
import GenMarkoff.Symmetric.MiddleGame.WeightedShiftedCorvajaZannier
import GenMarkoff.Symmetric.Opening.ReturnExponentBound
import BGS.Markoff.MiddleGame.OrderEscape

/-!
# Actual one-step middle-game order growth

This module closes the orbit-theoretic bridge after the shifted
Corvaja--Zannier estimate.  The current fiber is diagonalized over the
canonical quadratic field, but its starting parameter is retained.  Thus the
left subgroup is `Subgroup.zpowers q` and the starting parameter contributes
to the two weights; it is not incorrectly replaced by the normalized
subgroup equation.
-/

namespace GenMarkoff.Symmetric.MiddleGame

open BGS.Markoff

noncomputable section

theorem mapPoint_oneStep1
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c : R) (x : Point R) :
    Opening.mapPoint f (oneStep1 c x) =
      oneStep1 (f c) (Opening.mapPoint f x) := by
  ext <;>
    simp [Opening.mapPoint, oneStep1, swap23, vieta2, coefficients,
      Coefficients.multiplier, map_ofNat]

theorem mapPoint_iterate_oneStep1
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c : R) (x : Point R) (n : ℕ) :
    Opening.mapPoint f (((oneStep1 c)^[n]) x) =
      ((oneStep1 (f c))^[n]) (Opening.mapPoint f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        mapPoint_oneStep1, ih]

/-- Candidate regularity reflected from a field extension. -/
theorem orderedTraceCandidateRegular_of_map
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) {A B C t : K}
    (h :
      OrderedTraceCandidateRegular (f A) (f B) (f C) (f t)) :
    OrderedTraceCandidateRegular A B C t := by
  rcases h with ⟨hD, htA, hcenter, hweight, hminus, hplus⟩
  simp only [eval_orderedTraceDiscriminantPolynomial] at hD ⊢
  simp only [eval_orderedTraceCenteredNormPolynomial] at hcenter ⊢
  simp only [eval_orderedTraceWeightDifferencePolynomial] at hweight ⊢
  simp only [eval_orderedTraceEvenMinusPolynomial] at hminus ⊢
  simp only [eval_orderedTraceEvenPlusPolynomial] at hplus ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    apply hD
    simpa [map_ofNat] using congrArg f hzero
  · intro hzero
    apply htA
    simpa using congrArg f hzero
  · intro hzero
    apply hcenter
    simpa [map_ofNat] using congrArg f hzero
  · intro hzero
    apply hweight
    simpa [map_ofNat] using congrArg f hzero
  · intro hzero
    apply hminus
    simpa [map_ofNat] using congrArg f hzero
  · intro hzero
    apply hplus
    simpa [map_ofNat] using congrArg f hzero

/-- A diagonalized candidate-regular symmetric point admits a reachable
first-axis one-step iterate whose adjacent half-step order is strictly
larger.  This is the coset-correct counterpart of the pinned BGS
`exists_iterate_with_larger_secondRotationOrder_of_diagonalizedFiber`. -/
theorem
    exists_oneStep1_iterate_with_larger_adjacent_halfStepOrder_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (c u t : ZMod p) (x : Point (ZMod p))
    (htrace : t = trace c u)
    (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (q s : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      Opening.mapPoint
          (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint
          (algebraMap (ZMod p) (quadraticFiniteField p) c)
          (algebraMap (ZMod p) (quadraticFiniteField p) u)
          (algebraMap (ZMod p) (quadraticFiniteField p) t)
          (q : quadraticFiniteField p) (s : quadraticFiniteField p))
    (hbelowEndgame :
      (halfStepOrder t : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 <
          halfStepOrder t)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) *
          halfStepOrder t < p) :
    ∃ n : ℕ,
      halfStepOrder t <
        halfStepOrder (trace c (((oneStep1 c)^[n]) x).x2) := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let cE : E := f c
  let uE : E := f u
  let tE : E := f t
  let alpha : E := actualAlpha cE * (s : E)
  let beta : E := actualBeta cE uE tE / (s : E)
  let gamma : E := actualGamma cE uE tE
  let H₁ : Subgroup Eˣ := Subgroup.zpowers q
  let rightSubgroup : ℕ → Subgroup Eˣ :=
    fun d ↦ middleGameRightSubgroup p d
  letI : DecidableEq E := Classical.decEq E
  have htraceE : tE = trace cE uE := by
    dsimp [tE, cE, uE, f]
    rw [htrace, Opening.map_trace]
  have hregularE :
      OrderedTraceCandidateRegular cE cE cE tE := by
    exact Opening.orderedTraceCandidateRegular_map f f.injective hregular
  have hcE : cE ^ 2 ≠ 4 := by
    intro hzero
    apply hc
    apply f.injective
    simpa [cE, f, map_ofNat] using hzero
  have hDE : discriminant tE ≠ 0 := by
    simpa [discriminant] using hregularE.1
  have htE : tE ≠ 2 := ne_two_of_discriminant_ne_zero hDE
  have heigen' :
      tE = (q : E) + ((q⁻¹ : Eˣ) : E) := by
    simpa [tE, E, f, splitTorusTrace] using heigen
  have hq : (q : E) ^ 2 ≠ 1 :=
    actualFiber_eigenvalue_sq_ne_one_of_discriminant_ne_zero
      tE q heigen hDE
  have horder :
      orderOf q = halfStepOrder t := by
    rw [Opening.halfStepOrder_eq_bgsRotationOrder]
    exact
      (rotationOrder_eq_orderOf_extensionEigenvalue t q hq heigen).symm
  have hleftCard : Nat.card H₁ = halfStepOrder t := by
    rw [Nat.card_zpowers, horder]
  have hweights :
      alpha * beta = actualSigma cE uE tE := by
    simpa [alpha, beta] using actual_coset_weights_mul cE uE tE s
  have hsigma : alpha * beta ≠ 0 := by
    rw [hweights]
    exact actualSigma_ne_zero_of_candidateRegular
      cE uE tE htraceE hregularE
  have hD2 :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualEvenObstruction_ne_zero_of_candidateRegular
      cE uE tE htraceE hcE hregularE
  have hrightOrder :
      ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
        Nat.card (rightSubgroup d) = d := by
    intro d hd
    exact middleGameRightSubgroup_natCard p (Nat.card H₁) d hd
  have hCZ :
      ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
        ((shiftedWeightedTraceEquationSolutions
          alpha beta gamma H₁ (rightSubgroup d)).card : ℝ) ≤
            corvajaZannierTraceUpperBound p (Nat.card H₁)
              (Nat.card (rightSubgroup d)) := by
    intro d _hd
    exact
      weightedShiftedTraceEquationSolutions_card_cast_le_corvajaZannier
        p E alpha beta gamma H₁ (rightSubgroup d) hpTwo hsigma hD2
  obtain ⟨h, hEscapes⟩ :=
    exists_left_element_escaping_shiftedCandidateOrders_of_corvajaZannierSizeBounds
      p alpha beta gamma H₁ rightSubgroup hrightOrder hCZ Nat.card_pos
        (by
          simpa only [Fintype.card_eq_nat_card, hleftCard] using hcube)
        (by
          simpa only [Fintype.card_eq_nat_card, hleftCard] using hlinear)
  obtain ⟨n, hn⟩ :=
    exists_iterate_fiberPoint_eq_mul_zpowers
      cE uE tE q s heigen' htraceE htE h
  refine ⟨n, ?_⟩
  let y : Point (ZMod p) := ((oneStep1 c)^[n]) x
  have hyPoint :
      Opening.mapPoint f y =
        fiberPoint cE uE tE (q : E) ((s * (h : Eˣ) : Eˣ) : E) := by
    calc
      Opening.mapPoint f y =
          ((oneStep1 cE)^[n]) (Opening.mapPoint f x) := by
        simpa [y, cE, f] using mapPoint_iterate_oneStep1 f c x n
      _ = ((oneStep1 cE)^[n])
          (fiberPoint cE uE tE (q : E) (s : E)) := by
        rw [hdiagonalized]
      _ = fiberPoint cE uE tE (q : E)
          ((s * (h : Eˣ) : Eˣ) : E) := hn
  apply lt_of_not_ge
  intro hsmall
  let t₂ : ZMod p := trace c y.x2
  have hsmallRotation :
      rotationOrder t₂ ≤ rotationOrder t := by
    simpa only [Opening.halfStepOrder_eq_bgsRotationOrder] using hsmall
  have hbelowRotation :
      (rotationOrder t : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta) := by
    simpa only [Opening.halfStepOrder_eq_bgsRotationOrder] using hbelowEndgame
  by_cases hparabolic : t₂ ^ 2 = 4
  · have hcases :=
      (normalizedTrace_sq_eq_four_iff_parabolic p t₂).mp hparabolic
    have hthreshold :=
      endgamePowerThreshold_le_rotationOrder_of_parabolicTrace
        p hpTwo delta hdelta t₂ hcases
    have hsmallReal :
        (rotationOrder t₂ : ℝ) ≤ (rotationOrder t : ℝ) := by
      exact_mod_cast hsmallRotation
    exact (not_le_of_gt hbelowRotation) (hthreshold.trans hsmallReal)
  · have hd :=
      rotationOrder_mem_middleGameCandidateOrders_of_nonparabolic
        p (rotationOrder t) hpTwo t₂ hparabolic hsmallRotation
    have hdH :
      rotationOrder t₂ ∈
          middleGameCandidateOrders p (Nat.card H₁) := by
      simpa only [Fintype.card_eq_nat_card, hleftCard,
        Opening.halfStepOrder_eq_bgsRotationOrder] using hd
    obtain ⟨h₂, htrace₂⟩ :=
      exists_middleGameRightSubgroup_trace_of_nonparabolic_rotationOrder
        p (rotationOrder t₂) hpTwo t₂ hparabolic rfl
    apply hEscapes (rotationOrder t₂) hdH h₂
    have hyTrace :
        weightedSplitTorusTrace alpha beta h + gamma = f t₂ := by
      calc
        weightedSplitTorusTrace alpha beta h + gamma =
            trace cE
              (fiberPoint cE uE tE (q : E)
                ((s * (h : Eˣ) : Eˣ) : E)).x2 := by
          simpa [alpha, beta, gamma] using
            (trace_fiberPoint_mul_eq_weightedSplitTorusTrace
              cE uE tE q s (h : Eˣ)).symm
        _ = trace cE (Opening.mapPoint f y).x2 := by rw [hyPoint]
        _ = f (trace c y.x2) := by
          simpa [cE, f, Opening.mapPoint] using
            (Opening.map_trace f c y.x2).symm
        _ = f t₂ := rfl
    exact hyTrace.trans htrace₂

/-- The iterable diagonalized middle-game step.  In addition to strict
adjacent order growth, the selected adjacent trace remains candidate regular.
The extra numerical premise is precisely the fourteen-point margin beyond
the common Corvaja--Zannier bad-support envelope. -/
theorem
    exists_oneStep1_iterate_with_larger_regular_adjacent_halfStepOrder_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (c u t : ZMod p) (x : Point (ZMod p))
    (htrace : t = trace c u)
    (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (q s : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      Opening.mapPoint
          (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint
          (algebraMap (ZMod p) (quadraticFiniteField p) c)
          (algebraMap (ZMod p) (quadraticFiniteField p) u)
          (algebraMap (ZMod p) (quadraticFiniteField p) t)
          (q : quadraticFiniteField p) (s : quadraticFiniteField p))
    (hbelowEndgame :
      (halfStepOrder t : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (_hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 <
          halfStepOrder t)
    (_hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) *
          halfStepOrder t < p)
    (hregularMargin :
      (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
          corvajaZannierCurrentOrderEnvelope p (halfStepOrder t) + 14 <
        (halfStepOrder t : ℝ)) :
    ∃ n : ℕ,
      OrderedTraceCandidateRegular c c c
          (trace c (((oneStep1 c)^[n]) x).x2) ∧
        halfStepOrder t <
          halfStepOrder (trace c (((oneStep1 c)^[n]) x).x2) := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let cE : E := f c
  let uE : E := f u
  let tE : E := f t
  let alpha : E := actualAlpha cE * (s : E)
  let beta : E := actualBeta cE uE tE / (s : E)
  let gamma : E := actualGamma cE uE tE
  let H₁ : Subgroup Eˣ := Subgroup.zpowers q
  let rightSubgroup : ℕ → Subgroup Eˣ :=
    fun d ↦ middleGameRightSubgroup p d
  letI : DecidableEq E := Classical.decEq E
  have htraceE : tE = trace cE uE := by
    dsimp [tE, cE, uE, f]
    rw [htrace, Opening.map_trace]
  have hregularE :
      OrderedTraceCandidateRegular cE cE cE tE := by
    exact Opening.orderedTraceCandidateRegular_map f f.injective hregular
  have hcE : cE ^ 2 ≠ 4 := by
    intro hzero
    apply hc
    apply f.injective
    simpa [cE, f, map_ofNat] using hzero
  have hDE : discriminant tE ≠ 0 := by
    simpa [discriminant] using hregularE.1
  have htE : tE ≠ 2 := ne_two_of_discriminant_ne_zero hDE
  have heigen' :
      tE = (q : E) + ((q⁻¹ : Eˣ) : E) := by
    simpa [tE, E, f, splitTorusTrace] using heigen
  have hq : (q : E) ^ 2 ≠ 1 :=
    actualFiber_eigenvalue_sq_ne_one_of_discriminant_ne_zero
      tE q heigen hDE
  have horder :
      orderOf q = halfStepOrder t := by
    rw [Opening.halfStepOrder_eq_bgsRotationOrder]
    exact
      (rotationOrder_eq_orderOf_extensionEigenvalue t q hq heigen).symm
  have hleftCard : Nat.card H₁ = halfStepOrder t := by
    rw [Nat.card_zpowers, horder]
  have hweights :
      alpha * beta = actualSigma cE uE tE := by
    simpa [alpha, beta] using actual_coset_weights_mul cE uE tE s
  have hsigma : alpha * beta ≠ 0 := by
    rw [hweights]
    exact actualSigma_ne_zero_of_candidateRegular
      cE uE tE htraceE hregularE
  have hD2 :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualEvenObstruction_ne_zero_of_candidateRegular
      cE uE tE htraceE hcE hregularE
  have hrightOrder :
      ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
        Nat.card (rightSubgroup d) = d := by
    intro d hd
    exact middleGameRightSubgroup_natCard p (Nat.card H₁) d hd
  have hCZ :
      ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
        ((shiftedWeightedTraceEquationSolutions
          alpha beta gamma H₁ (rightSubgroup d)).card : ℝ) ≤
            corvajaZannierTraceUpperBound p (Nat.card H₁)
              (Nat.card (rightSubgroup d)) := by
    intro d _hd
    exact
      weightedShiftedTraceEquationSolutions_card_cast_le_corvajaZannier
        p E alpha beta gamma H₁ (rightSubgroup d) hpTwo hsigma hD2
  have htwoBase : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    exact hpTwo (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)
  have htwoE : (2 : E) ≠ 0 := by
    exact (map_ne_zero f).2 htwoBase
  have hmultiplierE : multiplier cE ≠ 0 :=
    multiplier_ne_zero_of_candidateRegular
      cE uE tE htraceE hregularE
  have halpha : alpha ≠ 0 := by
    exact mul_ne_zero (actualAlpha_ne_zero cE hmultiplierE)
      (Units.ne_zero s)
  have hmarginH :
      (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
          corvajaZannierCurrentOrderEnvelope p (Nat.card H₁) + 14 <
        (Nat.card H₁ : ℝ) := by
    simpa only [hleftCard] using hregularMargin
  obtain ⟨h, hselectedRegular, hEscapes⟩ :=
    exists_left_element_escaping_shiftedCandidateOrders_and_regular_of_estimate
      p cE alpha beta gamma H₁ rightSubgroup htwoE hcE halpha
        hrightOrder hCZ hmarginH
  obtain ⟨n, hn⟩ :=
    exists_iterate_fiberPoint_eq_mul_zpowers
      cE uE tE q s heigen' htraceE htE h
  let y : Point (ZMod p) := ((oneStep1 c)^[n]) x
  have hyPoint :
      Opening.mapPoint f y =
        fiberPoint cE uE tE (q : E) ((s * (h : Eˣ) : Eˣ) : E) := by
    calc
      Opening.mapPoint f y =
          ((oneStep1 cE)^[n]) (Opening.mapPoint f x) := by
        simpa [y, cE, f] using mapPoint_iterate_oneStep1 f c x n
      _ = ((oneStep1 cE)^[n])
          (fiberPoint cE uE tE (q : E) (s : E)) := by
        rw [hdiagonalized]
      _ = fiberPoint cE uE tE (q : E)
          ((s * (h : Eˣ) : Eˣ) : E) := hn
  let t₂ : ZMod p := trace c y.x2
  have hyTrace :
      weightedSplitTorusTrace alpha beta h + gamma = f t₂ := by
    calc
      weightedSplitTorusTrace alpha beta h + gamma =
          trace cE
            (fiberPoint cE uE tE (q : E)
              ((s * (h : Eˣ) : Eˣ) : E)).x2 := by
        simpa [alpha, beta, gamma] using
          (trace_fiberPoint_mul_eq_weightedSplitTorusTrace
            cE uE tE q s (h : Eˣ)).symm
      _ = trace cE (Opening.mapPoint f y).x2 := by rw [hyPoint]
      _ = f (trace c y.x2) := by
        simpa [cE, f, Opening.mapPoint] using
          (Opening.map_trace f c y.x2).symm
      _ = f t₂ := rfl
  have hregular₂ :
      OrderedTraceCandidateRegular c c c t₂ := by
    apply orderedTraceCandidateRegular_of_map f
    change OrderedTraceCandidateRegular cE cE cE (f t₂)
    rw [← hyTrace]
    exact hselectedRegular
  refine ⟨n, ?_, ?_⟩
  · simpa [y, t₂] using hregular₂
  · apply lt_of_not_ge
    intro hsmall
    have hsmallRotation :
        rotationOrder t₂ ≤ rotationOrder t := by
      simpa only [Opening.halfStepOrder_eq_bgsRotationOrder] using hsmall
    have hbelowRotation :
        (rotationOrder t : ℝ) <
          (p : ℝ) ^ ((1 : ℝ) / 2 + delta) := by
      simpa only [Opening.halfStepOrder_eq_bgsRotationOrder] using
        hbelowEndgame
    by_cases hparabolic : t₂ ^ 2 = 4
    · have hcases :=
        (normalizedTrace_sq_eq_four_iff_parabolic p t₂).mp hparabolic
      have hthreshold :=
        endgamePowerThreshold_le_rotationOrder_of_parabolicTrace
          p hpTwo delta hdelta t₂ hcases
      have hsmallReal :
          (rotationOrder t₂ : ℝ) ≤ (rotationOrder t : ℝ) := by
        exact_mod_cast hsmallRotation
      exact (not_le_of_gt hbelowRotation) (hthreshold.trans hsmallReal)
    · have hd :=
        rotationOrder_mem_middleGameCandidateOrders_of_nonparabolic
          p (rotationOrder t) hpTwo t₂ hparabolic hsmallRotation
      have hdH :
          rotationOrder t₂ ∈
            middleGameCandidateOrders p (Nat.card H₁) := by
        simpa only [Fintype.card_eq_nat_card, hleftCard,
          Opening.halfStepOrder_eq_bgsRotationOrder] using hd
      obtain ⟨h₂, htrace₂⟩ :=
        exists_middleGameRightSubgroup_trace_of_nonparabolic_rotationOrder
          p (rotationOrder t₂) hpTwo t₂ hparabolic rfl
      apply hEscapes (rotationOrder t₂) hdH h₂
      exact hyTrace.trans htrace₂

/-- Every candidate-regular symmetric fiber point admits a diagonalized
presentation over the canonical quadratic field, with its actual initial
parameter retained as a unit. -/
theorem exists_actualFiber_diagonalization
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (c u t : ZMod p) (x : Point (ZMod p))
    (hx : IsSolution (coefficients c) x)
    (hx1 : x.x1 = u)
    (htrace : t = trace c u)
    (hregular : OrderedTraceCandidateRegular c c c t) :
    ∃ q s : (quadraticFiniteField p)ˣ,
      algebraMap (ZMod p) (quadraticFiniteField p) t =
          splitTorusTrace q ∧
        Opening.mapPoint
            (algebraMap (ZMod p) (quadraticFiniteField p)) x =
          fiberPoint
            (algebraMap (ZMod p) (quadraticFiniteField p) c)
            (algebraMap (ZMod p) (quadraticFiniteField p) u)
            (algebraMap (ZMod p) (quadraticFiniteField p) t)
            (q : quadraticFiniteField p) (s : quadraticFiniteField p) := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let cE : E := f c
  let uE : E := f u
  let tE : E := f t
  let xE : Point E := Opening.mapPoint f x
  have hDBase : t ^ 2 - 4 ≠ 0 := by
    simpa only [eval_orderedTraceDiscriminantPolynomial] using hregular.1
  have hnonparabolic : t ^ 2 ≠ 4 := sub_ne_zero.mp hDBase
  have hxE : IsSolution (coefficients cE) xE := by
    simpa [cE, xE] using Opening.isSolution_mapPoint_symmetric f c x hx
  have hx1E : xE.x1 = uE := by
    simpa [xE, uE, Opening.mapPoint] using congrArg f hx1
  have htraceE : tE = trace cE uE := by
    dsimp [tE, cE, uE, f]
    rw [htrace, Opening.map_trace]
  have hregularE : OrderedTraceCandidateRegular cE cE cE tE :=
    Opening.orderedTraceCandidateRegular_map f f.injective hregular
  have hDE : discriminant tE ≠ 0 := by
    simpa [discriminant] using hregularE.1
  have hproductE : centeredFiberProduct cE uE tE ≠ 0 :=
    centeredFiberProduct_ne_zero_of_candidateRegular
      cE uE tE htraceE hregularE
  rcases exists_split_or_quadraticNormOneTrace p hpTwo t hnonparabolic with
    ⟨w, htraceW, _hw⟩ | ⟨w, htraceW, _hw⟩
  · let embedding : (ZMod p)ˣ →* Eˣ := Units.map f.toMonoidHom
    let q : Eˣ := embedding w
    have heigen : tE = splitTorusTrace q := by
      dsimp [tE]
      rw [← htraceW]
      change f (splitTorusTrace w) = splitTorusTrace (embedding w)
      rw [splitTorusTrace, splitTorusTrace, map_add]
      rfl
    obtain ⟨s, hs⟩ :=
      exists_unit_fiberPoint_eq
        cE uE tE q xE hx1E hxE htraceE heigen hDE hproductE
    refine ⟨q, s, ?_, ?_⟩
    · exact heigen
    · simpa [E, f, cE, uE, tE, xE] using hs.symm
  · let q : Eˣ := (w : (quadraticFiniteField p)ˣ)
    have heigen : tE = splitTorusTrace q := by
      dsimp [tE, f]
      rw [← htraceW]
      exact algebraMap_quadraticNormOneTrace p w
    obtain ⟨s, hs⟩ :=
      exists_unit_fiberPoint_eq
        cE uE tE q xE hx1E hxE htraceE heigen hDE hproductE
    refine ⟨q, s, ?_, ?_⟩
    · exact heigen
    · simpa [E, f, cE, uE, tE, xE] using hs.symm

/-- Candidate regularity and the explicit middle-range inequalities suffice
for a reachable first-axis one-step iterate with strictly larger adjacent
half-step order.  No diagonalization data are required from the caller. -/
theorem exists_oneStep1_iterate_with_larger_adjacent_halfStepOrder
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (c u t : ZMod p) (x : Point (ZMod p))
    (hx : IsSolution (coefficients c) x)
    (hx1 : x.x1 = u)
    (htrace : t = trace c u)
    (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (hbelowEndgame :
      (halfStepOrder t : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 <
          halfStepOrder t)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) *
          halfStepOrder t < p) :
    ∃ n : ℕ,
      halfStepOrder t <
        halfStepOrder (trace c (((oneStep1 c)^[n]) x).x2) := by
  obtain ⟨q, s, heigen, hdiagonalized⟩ :=
    exists_actualFiber_diagonalization
      p hpTwo c u t x hx hx1 htrace hregular
  exact
    exists_oneStep1_iterate_with_larger_adjacent_halfStepOrder_of_diagonalizedFiber
      p hpTwo delta hdelta c u t x htrace hc hregular q s heigen
        hdiagonalized hbelowEndgame hcube hlinear

/-- Iterable arbitrary-point middle-game order growth.  The returned adjacent
trace is candidate regular, so it can serve as the fixed trace for the next
one-step growth application. -/
theorem exists_oneStep1_iterate_with_larger_regular_adjacent_halfStepOrder
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (c u t : ZMod p) (x : Point (ZMod p))
    (hx : IsSolution (coefficients c) x)
    (hx1 : x.x1 = u)
    (htrace : t = trace c u)
    (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (hbelowEndgame :
      (halfStepOrder t : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 <
          halfStepOrder t)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) *
          halfStepOrder t < p)
    (hregularMargin :
      (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
          corvajaZannierCurrentOrderEnvelope p (halfStepOrder t) + 14 <
        (halfStepOrder t : ℝ)) :
    ∃ n : ℕ,
      OrderedTraceCandidateRegular c c c
          (trace c (((oneStep1 c)^[n]) x).x2) ∧
        halfStepOrder t <
          halfStepOrder (trace c (((oneStep1 c)^[n]) x).x2) := by
  obtain ⟨q, s, heigen, hdiagonalized⟩ :=
    exists_actualFiber_diagonalization
      p hpTwo c u t x hx hx1 htrace hregular
  exact
    exists_oneStep1_iterate_with_larger_regular_adjacent_halfStepOrder_of_diagonalizedFiber
      p hpTwo delta hdelta c u t x htrace hc hregular q s heigen
        hdiagonalized hbelowEndgame hcube hlinear hregularMargin

end

end GenMarkoff.Symmetric.MiddleGame
