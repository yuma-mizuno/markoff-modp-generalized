import GenMarkoff.General.MiddleGame.ActualDiagonalization
import GenMarkoff.General.MiddleGame.ActualMoveWiring
import GenMarkoff.General.MiddleGame.ActualOrderEscape
import GenMarkoff.General.MiddleGame.RotationEigenvalueOrder
import GenMarkoff.Symmetric.MiddleGame.WeightedShiftedCorvajaZannier
import BGS.Markoff.MiddleGame.OrderEscape

/-!
# Actual first-axis middle-game order growth

This module wires the ordered general first-axis fiber to the existing
shifted Corvaja--Zannier escape theorem.  Reachability uses `rotation1`, so
the left parameter subgroup is `Subgroup.zpowers (q ^ 2)`.

The BGS candidate orders are orders of the unsquared trace eigenvalue.  The
actual source rotation has the squared eigenvalue.  Consequently the result
below records the exact parity boundary: the selected adjacent trace either
has larger actual rotation-linear order, or its BGS half-step order lies
outside the candidate orders bounded by the current actual order.
-/

namespace GenMarkoff.General.MiddleGame

open BGS.Markoff
open GenMarkoff.Symmetric.MiddleGame

noncomputable section

/-- Apply a ring homomorphism coordinatewise to a point. -/
def mapPoint
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (x : Point R) : Point S :=
  ⟨f x.x1, f x.x2, f x.x3⟩

/-- Apply a ring homomorphism coefficientwise. -/
def mapCoefficients
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (a : Coefficients R) : Coefficients S :=
  ⟨f a.a1, f a.a2, f a.a3⟩

@[simp]
theorem mapCoefficients_a1
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (a : Coefficients R) :
    (mapCoefficients f a).a1 = f a.a1 :=
  rfl

@[simp]
theorem mapCoefficients_a2
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (a : Coefficients R) :
    (mapCoefficients f a).a2 = f a.a2 :=
  rfl

@[simp]
theorem mapCoefficients_a3
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (a : Coefficients R) :
    (mapCoefficients f a).a3 = f a.a3 :=
  rfl

@[simp]
theorem mapCoefficients_multiplier
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (a : Coefficients R) :
    (mapCoefficients f a).multiplier = f a.multiplier := by
  simp [mapCoefficients, Coefficients.multiplier, map_ofNat]

/-- Scalar extension commutes with the first source rotation for an arbitrary
fixed coefficient triple. -/
theorem mapPoint_rotation1
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Coefficients R) (x : Point R) :
    mapPoint f (rotation1 a x) =
      rotation1 (mapCoefficients f a)
        (mapPoint f x) := by
  ext <;>
    simp [mapPoint, rotation1, vieta2, vieta3, mapCoefficients,
      Coefficients.multiplier, map_ofNat]

/-- Scalar extension commutes with every first-axis rotation iterate. -/
theorem mapPoint_iterate_rotation1
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Coefficients R) (x : Point R) (n : ℕ) :
    mapPoint f (((rotation1 a)^[n]) x) =
      ((rotation1 (mapCoefficients f a))^[n])
        (mapPoint f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        mapPoint_rotation1, ih]

/-- Candidate regularity preserved by an injective field homomorphism. -/
theorem orderedTraceCandidateRegular_map
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (hf : Function.Injective f)
    {A B C t : K} (h : OrderedTraceCandidateRegular A B C t) :
    OrderedTraceCandidateRegular (f A) (f B) (f C) (f t) := by
  rcases h with ⟨hD, htA, hcenter, hweight, hminus, hplus⟩
  simp only [eval_orderedTraceDiscriminantPolynomial] at hD ⊢
  simp only [eval_orderedTraceCenteredNormPolynomial] at hcenter ⊢
  simp only [eval_orderedTraceWeightDifferencePolynomial] at hweight ⊢
  simp only [eval_orderedTraceEvenMinusPolynomial] at hminus ⊢
  simp only [eval_orderedTraceEvenPlusPolynomial] at hplus ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [map_ofNat] using (map_ne_zero_iff f hf).mpr hD
  · simpa using (map_ne_zero_iff f hf).mpr htA
  · simpa [map_ofNat] using (map_ne_zero_iff f hf).mpr hcenter
  · simpa [map_ofNat] using (map_ne_zero_iff f hf).mpr hweight
  · simpa [map_ofNat] using (map_ne_zero_iff f hf).mpr hminus
  · simpa [map_ofNat] using (map_ne_zero_iff f hf).mpr hplus

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

/-- Both parabolic trace signs have actual squared-rotation order `p`.
The unsquared BGS orders are `p` and `2p`, but squaring removes the latter
sign's factor `2`. -/
theorem rotationLinearOrder_eq_prime_of_parabolicTrace
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (t : ZMod p) (hparabolic : t ^ 2 = 4) :
    rotationLinearOrder t = p := by
  rcases (normalizedTrace_sq_eq_four_iff_parabolic p t).mp hparabolic with
    ht | ht
  · rw [ht, Opening.rotationLinearOrder_eq_bgsRotationOrder_div_gcd,
      rotationOrder_two]
    have hcoprime : Nat.Coprime p 2 :=
      ((Fact.out : p.Prime).odd_of_ne_two hpTwo).coprime_two_right
    rw [hcoprime.gcd_eq_one]
    simp
  · rw [ht, Opening.rotationLinearOrder_eq_bgsRotationOrder_div_gcd,
      rotationOrder_neg_two p hpTwo]
    simp

/-- If the actual squared order does not grow but the unsquared BGS order
escapes the current candidate range, the only possible obstruction is the
factor-two parity class. -/
theorem halfStepOrder_parity_obstruction_of_actualOrder_le_of_not_mem_candidates
    (p currentOrder : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (t : ZMod p) (hnonparabolic : t ^ 2 ≠ 4)
    (hle : rotationLinearOrder t ≤ currentOrder)
    (hout :
      BGS.Markoff.rotationOrder t ∉
        middleGameCandidateOrders p currentOrder) :
    Nat.gcd (BGS.Markoff.rotationOrder t) 2 = 2 ∧
      currentOrder < BGS.Markoff.rotationOrder t ∧
      BGS.Markoff.rotationOrder t ≤ 2 * currentOrder := by
  let n := BGS.Markoff.rotationOrder t
  let g := Nat.gcd n 2
  have hgt : currentOrder < n := by
    apply lt_of_not_ge
    intro hn
    apply hout
    exact rotationOrder_mem_middleGameCandidateOrders_of_nonparabolic
      p currentOrder hpTwo t hnonparabolic hn
  have hgPos : 0 < g :=
    Nat.gcd_pos_of_pos_right n (by norm_num)
  have hgLe : g ≤ 2 :=
    Nat.gcd_le_right n (by norm_num)
  have hgDvd : g ∣ n :=
    Nat.gcd_dvd_left n 2
  have hquotient : n / g ≤ currentOrder := by
    simpa [n, g, Opening.rotationLinearOrder_eq_bgsRotationOrder_div_gcd]
      using hle
  have hgNeOne : g ≠ 1 := by
    intro hg
    have hnLe : n ≤ currentOrder := by
      simpa [hg] using hquotient
    exact (not_le_of_gt hgt) hnLe
  have hgTwo : g = 2 := by
    omega
  refine ⟨by simpa [g, n] using hgTwo, hgt, ?_⟩
  calc
    n = n / g * g := (Nat.div_mul_cancel hgDvd).symm
    _ ≤ currentOrder * 2 := Nat.mul_le_mul hquotient hgLe
    _ = 2 * currentOrder := by omega

/-- A diagonalized candidate-regular first-axis point admits a reachable
`rotation1` iterate whose adjacent trace either has strictly larger actual
rotation-linear order, or has BGS half-step order outside the candidate
orders bounded by the current actual order.

The second alternative is the precise residual parity branch: the escape
estimate controls unsquared eigenvalue orders, whereas reachability is through
the square-generated subgroup. -/
theorem
    exists_rotation1_iterate_with_larger_actualOrder_or_halfStepOrder_outside_candidates_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u)
    (hB : a.a2 ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      mapPoint (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint1
          (mapCoefficients
            (algebraMap (ZMod p) (quadraticFiniteField p)) a)
          (algebraMap (ZMod p) (quadraticFiniteField p) u)
          (algebraMap (ZMod p) (quadraticFiniteField p) t)
          (q : quadraticFiniteField p) (r : quadraticFiniteField p))
    (hbelowEndgame :
      (rotationLinearOrder t : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 <
          rotationLinearOrder t)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) *
          rotationLinearOrder t < p) :
    ∃ n : ℕ,
      let y := ((rotation1 a)^[n]) x
      let t₂ := orderedTrace a.multiplier a.a2 y.x2
      rotationLinearOrder t < rotationLinearOrder t₂ ∨
        (BGS.Markoff.rotationOrder t₂ ∉
            middleGameCandidateOrders p (rotationLinearOrder t) ∧
          Nat.gcd (BGS.Markoff.rotationOrder t₂) 2 = 2 ∧
          rotationLinearOrder t < BGS.Markoff.rotationOrder t₂ ∧
          BGS.Markoff.rotationOrder t₂ ≤
            2 * rotationLinearOrder t) := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := mapCoefficients f a
  let uE : E := f u
  let tE : E := f t
  let alpha : E := actualAlpha aE.multiplier * (r : E)
  let beta : E :=
    actualBeta aE.multiplier aE.a2 aE.a3 uE tE / (r : E)
  let gamma : E :=
    actualGammaFirst aE.multiplier aE.a2 aE.a3 uE tE
  let H₁ : Subgroup Eˣ := Subgroup.zpowers (q ^ 2)
  let rightSubgroup : ℕ → Subgroup Eˣ :=
    fun d ↦ middleGameRightSubgroup p d
  letI : DecidableEq E := Classical.decEq E
  have hDBase : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a1 uE := by
    have hmap := congrArg f hcoordinate
    simpa [tE, uE, aE, orderedTrace] using hmap
  have hregularE :
      OrderedTraceCandidateRegular aE.a1 aE.a2 aE.a3 tE := by
    simpa [aE, tE] using
      orderedTraceCandidateRegular_map f f.injective hregular
  have hBE : aE.a2 ^ 2 ≠ 4 := by
    intro hzero
    apply hB
    apply f.injective
    simpa [aE, map_ofNat] using hzero
  have hDE : discriminant tE ≠ 0 := by
    simpa [discriminant] using hregularE.1
  have heigen' :
      tE = (q : E) + ((q⁻¹ : Eˣ) : E) := by
    simpa [tE, E, f, splitTorusTrace] using heigen
  have hleftCard :
      Nat.card H₁ = rotationLinearOrder t := by
    simpa [H₁, E, f] using
      card_zpowers_sq_eq_rotationLinearOrder_of_discriminant_ne_zero
        p t q hDBase heigen
  have hweights :
      alpha * beta =
        actualSigma aE.multiplier aE.a2 aE.a3 uE tE := by
    simpa [alpha, beta] using
      actual_firstDirected_coset_weights_mul
        aE.multiplier aE.a2 aE.a3 uE tE r
  have hsigma : alpha * beta ≠ 0 := by
    rw [hweights]
    exact actualSigma_ne_zero_of_candidateRegular
      aE.multiplier aE.a1 aE.a2 aE.a3 uE tE htraceE hregularE
  have hEven :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualEvenObstruction_ne_zero_of_candidateRegular
      aE.multiplier aE.a1 aE.a2 aE.a3 uE tE htraceE hBE hregularE
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
        p E alpha beta gamma H₁ (rightSubgroup d)
          hpTwo hsigma hEven
  obtain ⟨h, hEscapes⟩ :=
    exists_left_element_escaping_shiftedCandidateOrders_of_corvajaZannierSizeBounds
      p alpha beta gamma H₁ rightSubgroup hrightOrder hCZ Nat.card_pos
        (by simpa only [hleftCard] using hcube)
        (by simpa only [hleftCard] using hlinear)
  obtain ⟨n, hn⟩ :=
    exists_iterate_fiberPoint1_eq_mul_zpowers_sq
      aE uE tE q r hDE heigen' htraceE h
  let y : Point (ZMod p) := ((rotation1 a)^[n]) x
  have hyPoint :
      mapPoint f y =
        fiberPoint1 aE uE tE (q : E)
          ((r * (h : Eˣ) : Eˣ) : E) := by
    calc
      mapPoint f y =
          ((rotation1 aE)^[n]) (mapPoint f x) := by
        simpa [y, aE] using mapPoint_iterate_rotation1 f a x n
      _ = ((rotation1 aE)^[n])
          (fiberPoint1 aE uE tE (q : E) (r : E)) := by
        simpa [E, f, aE, uE, tE] using congrArg
          (fun z : Point E ↦ ((rotation1 aE)^[n]) z) hdiagonalized
      _ = fiberPoint1 aE uE tE (q : E)
          ((r * (h : Eˣ) : Eˣ) : E) := hn
  let t₂ : ZMod p := orderedTrace a.multiplier a.a2 y.x2
  have hyTrace :
      weightedSplitTorusTrace alpha beta h + gamma = f t₂ := by
    calc
      weightedSplitTorusTrace alpha beta h + gamma =
          orderedTrace aE.multiplier aE.a2
            (fiberPoint1 aE uE tE (q : E)
              ((r * (h : Eˣ) : Eˣ) : E)).x2 := by
        simpa [alpha, beta, gamma] using
          (orderedTrace_fiberPoint1_mul_eq_weightedSplitTorusTrace
            aE uE tE q r (h : Eˣ)).symm
      _ = orderedTrace aE.multiplier aE.a2 (mapPoint f y).x2 := by
        rw [hyPoint]
      _ = f (orderedTrace a.multiplier a.a2 y.x2) := by
        simp [orderedTrace, aE, mapPoint]
      _ = f t₂ := rfl
  refine ⟨n, ?_⟩
  change
    rotationLinearOrder t < rotationLinearOrder t₂ ∨
      (BGS.Markoff.rotationOrder t₂ ∉
          middleGameCandidateOrders p (rotationLinearOrder t) ∧
        Nat.gcd (BGS.Markoff.rotationOrder t₂) 2 = 2 ∧
        rotationLinearOrder t < BGS.Markoff.rotationOrder t₂ ∧
        BGS.Markoff.rotationOrder t₂ ≤
          2 * rotationLinearOrder t)
  by_cases hgrowth :
      rotationLinearOrder t < rotationLinearOrder t₂
  · exact Or.inl hgrowth
  · have htargetLe :
      rotationLinearOrder t₂ ≤ rotationLinearOrder t :=
      Nat.le_of_not_gt hgrowth
    have hnonparabolic : t₂ ^ 2 ≠ 4 := by
      intro hparabolic
      have htarget :
          rotationLinearOrder t₂ = p :=
        rotationLinearOrder_eq_prime_of_parabolicTrace
          p hpTwo t₂ hparabolic
      have hthreshold :=
        endgamePowerThreshold_le_prime p delta hdelta
      have htargetLeReal :
          (p : ℝ) ≤ (rotationLinearOrder t : ℝ) := by
        calc
          (p : ℝ) = (rotationLinearOrder t₂ : ℝ) := by
            exact_mod_cast htarget.symm
          _ ≤ (rotationLinearOrder t : ℝ) := by
            exact_mod_cast htargetLe
      exact
        (not_le_of_gt hbelowEndgame)
          (hthreshold.trans htargetLeReal)
    have hout :
        BGS.Markoff.rotationOrder t₂ ∉
          middleGameCandidateOrders p (rotationLinearOrder t) := by
      intro hd
      obtain ⟨h₂, htrace₂⟩ :=
        exists_middleGameRightSubgroup_trace_of_nonparabolic_rotationOrder
          p (BGS.Markoff.rotationOrder t₂) hpTwo t₂ hnonparabolic rfl
      apply hEscapes (BGS.Markoff.rotationOrder t₂)
        (by simpa only [hleftCard] using hd) h₂
      exact hyTrace.trans htrace₂
    exact Or.inr ⟨hout,
      halfStepOrder_parity_obstruction_of_actualOrder_le_of_not_mem_candidates
        p (rotationLinearOrder t) hpTwo t₂ hnonparabolic htargetLe hout⟩

end

end GenMarkoff.General.MiddleGame
