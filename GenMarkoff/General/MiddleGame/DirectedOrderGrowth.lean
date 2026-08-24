import GenMarkoff.General.MiddleGame.ActualOrderGrowth

/-!
# Directed general middle-game order growth

The first-axis order-growth theorem is not transported by a coordinate
permutation: such a permutation is not a symmetry of a fixed unequal
coefficient triple.  This file isolates the coefficient-independent
square-coset escape argument and supplies the other directed surface
specializations by their own rotation, parametrization, and trace formulas.
-/

namespace GenMarkoff.General.MiddleGame

open BGS.Markoff
open GenMarkoff.Symmetric.MiddleGame

noncomputable section

section ScalarExtension

/-- Scalar extension commutes with the second source rotation for the same
fixed coefficient order. -/
theorem mapPoint_rotation2
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Coefficients R) (x : Point R) :
    mapPoint f (rotation2 a x) =
      rotation2 (mapCoefficients f a) (mapPoint f x) := by
  ext <;>
    simp [mapPoint, rotation2, vieta1, vieta3, mapCoefficients,
      Coefficients.multiplier, map_ofNat]

/-- Scalar extension commutes with the third source rotation for the same
fixed coefficient order. -/
theorem mapPoint_rotation3
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Coefficients R) (x : Point R) :
    mapPoint f (rotation3 a x) =
      rotation3 (mapCoefficients f a) (mapPoint f x) := by
  ext <;>
    simp [mapPoint, rotation3, vieta1, vieta2, mapCoefficients,
      Coefficients.multiplier, map_ofNat]

/-- Scalar extension commutes with every second-axis rotation iterate. -/
theorem mapPoint_iterate_rotation2
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Coefficients R) (x : Point R) (n : ℕ) :
    mapPoint f (((rotation2 a)^[n]) x) =
      ((rotation2 (mapCoefficients f a))^[n]) (mapPoint f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        mapPoint_rotation2, ih]

/-- Scalar extension commutes with every third-axis rotation iterate. -/
theorem mapPoint_iterate_rotation3
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Coefficients R) (x : Point R) (n : ℕ) :
    mapPoint f (((rotation3 a)^[n]) x) =
      ((rotation3 (mapCoefficients f a))^[n]) (mapPoint f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        mapPoint_rotation3, ih]

end ScalarExtension

section DirectedMoveWiring

variable {K : Type*} [Field K]

/-- Every second-axis rotation iterate multiplies the torus parameter by the
corresponding power of `q ^ 2`. -/
theorem iterate_rotation2_fiberPoint2_eq_pow_mul
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u) (n : ℕ) :
    ((rotation2 a)^[n]) (fiberPoint2 a u t q h) =
      fiberPoint2 a u t q ((q ^ 2) ^ n * h) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [rotation2_fiberPoint2
        a u t q ((q ^ 2) ^ n * h) hD hq
        (mul_ne_zero (pow_ne_zero n (pow_ne_zero 2 hq)) hh)
        heigen hcoordinate]
      congr 1
      rw [pow_succ]
      ring

/-- Every translated square-coset parameter on a second-coordinate fiber is
reached by a forward `rotation2` iterate. -/
theorem exists_iterate_fiberPoint2_eq_mul_zpowers_sq
    [Finite K] (a : Coefficients K) (u t : K) (q r : Kˣ)
    (hD : discriminant t ≠ 0)
    (heigen : t = (q : K) + ((q⁻¹ : Kˣ) : K))
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u)
    (h : Subgroup.zpowers (q ^ 2)) :
    ∃ n : ℕ,
      ((rotation2 a)^[n])
          (fiberPoint2 a u t (q : K) (r : K)) =
        fiberPoint2 a u t (q : K) ((r * (h : Kˣ) : Kˣ) : K) := by
  have hhPowers : (h : Kˣ) ∈ Submonoid.powers (q ^ 2) :=
    mem_powers_iff_mem_zpowers.mpr h.property
  obtain ⟨n, hn⟩ :=
    (Submonoid.mem_powers_iff (h : Kˣ) (q ^ 2)).mp hhPowers
  refine ⟨n, ?_⟩
  have heigen' : t = (q : K) + (q : K)⁻¹ := by
    simpa only [Units.val_inv_eq_inv_val] using heigen
  rw [iterate_rotation2_fiberPoint2_eq_pow_mul
    a u t (q : K) (r : K) hD (Units.ne_zero q) (Units.ne_zero r)
    heigen' hcoordinate n]
  congr 1
  have hnVal :
      ((h : Kˣ) : K) = (((q ^ 2) ^ n : Kˣ) : K) :=
    congrArg (fun z : Kˣ => (z : K)) hn.symm
  simp only [Units.val_pow_eq_pow_val] at hnVal
  simp only [Units.val_mul]
  rw [hnVal]
  ring

/-- Every third-axis rotation iterate multiplies the torus parameter by the
corresponding power of `q ^ 2`. -/
theorem iterate_rotation3_fiberPoint3_eq_pow_mul
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a3 u) (n : ℕ) :
    ((rotation3 a)^[n]) (fiberPoint3 a u t q h) =
      fiberPoint3 a u t q ((q ^ 2) ^ n * h) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [rotation3_fiberPoint3
        a u t q ((q ^ 2) ^ n * h) hD hq
        (mul_ne_zero (pow_ne_zero n (pow_ne_zero 2 hq)) hh)
        heigen hcoordinate]
      congr 1
      rw [pow_succ]
      ring

/-- Every translated square-coset parameter on a third-coordinate fiber is
reached by a forward `rotation3` iterate. -/
theorem exists_iterate_fiberPoint3_eq_mul_zpowers_sq
    [Finite K] (a : Coefficients K) (u t : K) (q r : Kˣ)
    (hD : discriminant t ≠ 0)
    (heigen : t = (q : K) + ((q⁻¹ : Kˣ) : K))
    (hcoordinate : t = orderedTrace a.multiplier a.a3 u)
    (h : Subgroup.zpowers (q ^ 2)) :
    ∃ n : ℕ,
      ((rotation3 a)^[n])
          (fiberPoint3 a u t (q : K) (r : K)) =
        fiberPoint3 a u t (q : K) ((r * (h : Kˣ) : Kˣ) : K) := by
  have hhPowers : (h : Kˣ) ∈ Submonoid.powers (q ^ 2) :=
    mem_powers_iff_mem_zpowers.mpr h.property
  obtain ⟨n, hn⟩ :=
    (Submonoid.mem_powers_iff (h : Kˣ) (q ^ 2)).mp hhPowers
  refine ⟨n, ?_⟩
  have heigen' : t = (q : K) + (q : K)⁻¹ := by
    simpa only [Units.val_inv_eq_inv_val] using heigen
  rw [iterate_rotation3_fiberPoint3_eq_pow_mul
    a u t (q : K) (r : K) hD (Units.ne_zero q) (Units.ne_zero r)
    heigen' hcoordinate n]
  congr 1
  have hnVal :
      ((h : Kˣ) : K) = (((q ^ 2) ^ n : Kˣ) : K) :=
    congrArg (fun z : Kˣ => (z : K)) hn.symm
  simp only [Units.val_pow_eq_pow_val] at hnVal
  simp only [Units.val_mul]
  rw [hnVal]
  ring

/-- First-moving-coordinate trace on a translated square-coset parameter. -/
theorem firstTrace_fiberPair_mul_eq_weightedSplitTorusTrace
    (s B C u t : K) (q r h : Kˣ) :
    s * (fiberPair B C u t (q : K) ((r * h : Kˣ) : K)).1 - B =
      weightedSplitTorusTrace
          (actualAlpha s * (r : K))
          (actualBeta s B C u t / (r : K)) h +
        actualGammaFirst s B C u t := by
  rw [firstTrace_fiberPair s B C u t
    (q : K) ((r * h : Kˣ) : K) (Units.ne_zero (r * h))]
  simp only [weightedSplitTorusTrace, Units.val_mul,
    Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero r, Units.ne_zero h]

/-- Second-moving-coordinate trace on a translated square-coset parameter. -/
theorem secondTrace_fiberPair_mul_eq_weightedSplitTorusTrace
    (s B C u t : K) (q r h : Kˣ) :
    s * (fiberPair B C u t (q : K) ((r * h : Kˣ) : K)).2 - C =
      weightedSplitTorusTrace
          ((s * (q : K)) * (r : K))
          ((s * centeredFiberProduct B C u t / (q : K)) / (r : K)) h +
        actualGammaSecond s B C u t := by
  rw [secondTrace_fiberPair s B C u t
    (q : K) ((r * h : Kˣ) : K)
    (Units.ne_zero q) (Units.ne_zero (r * h))]
  simp only [weightedSplitTorusTrace, Units.val_mul,
    Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero q, Units.ne_zero r, Units.ne_zero h]

/-- Translating the second-directed weights preserves the common invariant
product `actualSigma`. -/
theorem actual_secondDirected_coset_weights_mul
    (s B C u t : K) (q r : Kˣ) :
    ((s * (q : K)) * (r : K)) *
        ((s * centeredFiberProduct B C u t / (q : K)) / (r : K)) =
      actualSigma s B C u t := by
  calc
    ((s * (q : K)) * (r : K)) *
          ((s * centeredFiberProduct B C u t / (q : K)) / (r : K)) =
        (s * (q : K)) *
          (s * centeredFiberProduct B C u t / (q : K)) := by
            field_simp [Units.ne_zero r]
    _ = actualSigma s B C u t :=
      secondTrace_weight_product s B C u t (q : K) (Units.ne_zero q)

/-- The ordered weight product is symmetric in the two moving
coefficients. -/
theorem orderedTraceSigma_swap (A B C t : K) :
    orderedTraceSigma A B C t = orderedTraceSigma A C B t := by
  simp only [orderedTraceSigma]
  ring

/-- Candidate regularity for the reverse directed frame makes the common
actual weight product nonzero. -/
theorem actualSigma_ne_zero_of_reverseCandidateRegular
    (s A B C u t : K)
    (htrace : t = orderedTrace s A u)
    (hregular : OrderedTraceCandidateRegular A C B t) :
    actualSigma s B C u t ≠ 0 := by
  rw [actualSigma_eq_orderedTraceSigma s A B C u t htrace,
    orderedTraceSigma_swap A B C t]
  exact hregular.sigma_ne_zero

/-- Candidate regularity for the reverse directed frame supplies its actual
common-even nonvanishing condition. -/
theorem actualSecondEvenObstruction_ne_zero_of_candidateRegular
    (s A B C u t : K)
    (htrace : t = orderedTrace s A u) (hC : C ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular A C B t) :
    shiftedTraceEvenObstruction (actualSigma s B C u t)
        (actualGammaSecond s B C u t) ≠ 0 := by
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  rw [actualSigma_eq_orderedTraceSigma s A B C u t htrace,
    orderedTraceSigma_swap A B C t,
    actualGammaSecond_eq_orderedTraceGamma
      s A B C u t hD htrace]
  exact hregular.evenObstruction_ne_zero hC

end DirectedMoveWiring

section AbstractEscape

/-- Axis-independent square-coset order escape.  All surface-specific work is
encapsulated in `hreachable`, which identifies a weighted trace value with an
actual target trace on a forward iterate of the specified fixed-axis
rotation. -/
theorem
    exists_iterate_with_larger_actualOrder_or_halfStepOrder_outside_candidates_of_squareCosetTrace
    {T : Type*}
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (t : ZMod p) (hD : discriminant t ≠ 0)
    (q : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (rotation : T → T) (x : T) (targetTrace : T → ZMod p)
    (alpha beta gamma : quadraticFiniteField p)
    (hsigma : alpha * beta ≠ 0)
    (hEven : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0)
    (hreachable :
      ∀ h : Subgroup.zpowers (q ^ 2),
        ∃ n : ℕ,
          weightedSplitTorusTrace alpha beta h + gamma =
            algebraMap (ZMod p) (quadraticFiniteField p)
              (targetTrace (((rotation)^[n]) x)))
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
      let t' := targetTrace (((rotation)^[n]) x)
      rotationLinearOrder t < rotationLinearOrder t' ∨
        (BGS.Markoff.rotationOrder t' ∉
            middleGameCandidateOrders p (rotationLinearOrder t) ∧
          Nat.gcd (BGS.Markoff.rotationOrder t') 2 = 2 ∧
          rotationLinearOrder t < BGS.Markoff.rotationOrder t' ∧
          BGS.Markoff.rotationOrder t' ≤
            2 * rotationLinearOrder t) := by
  let E := quadraticFiniteField p
  let H₁ : Subgroup Eˣ := Subgroup.zpowers (q ^ 2)
  let rightSubgroup : ℕ → Subgroup Eˣ :=
    fun d ↦ middleGameRightSubgroup p d
  letI : DecidableEq E := Classical.decEq E
  have hleftCard :
      Nat.card H₁ = rotationLinearOrder t := by
    simpa [H₁, E] using
      card_zpowers_sq_eq_rotationLinearOrder_of_discriminant_ne_zero
        p t q hD heigen
  have hrightOrder :
      ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
        Nat.card (rightSubgroup d) = d := by
    intro d hd
    exact middleGameRightSubgroup_natCard p (Nat.card H₁) d hd
  have hCZ :
      ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
        ((shiftedWeightedTraceEquationSolutions
          alpha beta gamma H₁ (rightSubgroup d)).card : ℕ) ≤
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
        (by rw [hleftCard]; exact hcube)
        (by rw [hleftCard]; exact hlinear)
  obtain ⟨n, hyTrace⟩ := hreachable h
  let t' : ZMod p := targetTrace (((rotation)^[n]) x)
  refine ⟨n, ?_⟩
  change
    rotationLinearOrder t < rotationLinearOrder t' ∨
      (BGS.Markoff.rotationOrder t' ∉
          middleGameCandidateOrders p (rotationLinearOrder t) ∧
        Nat.gcd (BGS.Markoff.rotationOrder t') 2 = 2 ∧
        rotationLinearOrder t < BGS.Markoff.rotationOrder t' ∧
        BGS.Markoff.rotationOrder t' ≤
          2 * rotationLinearOrder t)
  by_cases hgrowth :
      rotationLinearOrder t < rotationLinearOrder t'
  · exact Or.inl hgrowth
  · have htargetLe :
      rotationLinearOrder t' ≤ rotationLinearOrder t :=
      Nat.le_of_not_gt hgrowth
    have hnonparabolic : t' ^ 2 ≠ 4 := by
      intro hparabolic
      have htarget :
          rotationLinearOrder t' = p :=
        rotationLinearOrder_eq_prime_of_parabolicTrace
          p hpTwo t' hparabolic
      have hthreshold :=
        endgamePowerThreshold_le_prime p delta hdelta
      have htargetLeReal :
          (p : ℝ) ≤ (rotationLinearOrder t : ℝ) := by
        calc
          (p : ℝ) = (rotationLinearOrder t' : ℝ) := by
            exact_mod_cast htarget.symm
          _ ≤ (rotationLinearOrder t : ℝ) := by
            exact_mod_cast htargetLe
      exact
        (not_le_of_gt hbelowEndgame)
          (hthreshold.trans htargetLeReal)
    have hout :
        BGS.Markoff.rotationOrder t' ∉
          middleGameCandidateOrders p (rotationLinearOrder t) := by
      intro hd
      obtain ⟨h₂, htrace₂⟩ :=
        exists_middleGameRightSubgroup_trace_of_nonparabolic_rotationOrder
          p (BGS.Markoff.rotationOrder t') hpTwo t' hnonparabolic rfl
      apply hEscapes (BGS.Markoff.rotationOrder t')
        (by rw [hleftCard]; exact hd) h₂
      exact hyTrace.trans htrace₂
    exact Or.inr ⟨hout,
      halfStepOrder_parity_obstruction_of_actualOrder_le_of_not_mem_candidates
        p (rotationLinearOrder t) hpTwo t'
          hnonparabolic htargetLe hout⟩

end AbstractEscape

section SurfaceSpecializations

/-- Reverse target from a first-coordinate fiber: an actual `rotation1`
iterate reaches a point whose third-coordinate trace satisfies the same
growth/parity dichotomy.  The ordered frame is `(a₁,a₃,a₂)`. -/
theorem
    exists_rotation1_iterate_axisThree_with_larger_actualOrder_or_halfStepOrder_outside_candidates_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u)
    (hC : a.a3 ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a1 a.a3 a.a2 t)
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
      let t' := orderedTrace a.multiplier a.a3 y.x3
      rotationLinearOrder t < rotationLinearOrder t' ∨
        (BGS.Markoff.rotationOrder t' ∉
            middleGameCandidateOrders p (rotationLinearOrder t) ∧
          Nat.gcd (BGS.Markoff.rotationOrder t') 2 = 2 ∧
          rotationLinearOrder t < BGS.Markoff.rotationOrder t' ∧
          BGS.Markoff.rotationOrder t' ≤
            2 * rotationLinearOrder t) := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := mapCoefficients f a
  let uE : E := f u
  let tE : E := f t
  let alpha : E :=
    (aE.multiplier * (q : E)) * (r : E)
  let beta : E :=
    (aE.multiplier * centeredFiberProduct aE.a2 aE.a3 uE tE /
      (q : E)) / (r : E)
  let gamma : E :=
    actualGammaSecond aE.multiplier aE.a2 aE.a3 uE tE
  have hDBase : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a1 uE := by
    have hmap := congrArg f hcoordinate
    simpa [tE, uE, aE, orderedTrace] using hmap
  have hregularE :
      OrderedTraceCandidateRegular aE.a1 aE.a3 aE.a2 tE := by
    simpa [aE, tE] using
      orderedTraceCandidateRegular_map f f.injective hregular
  have hCE : aE.a3 ^ 2 ≠ 4 := by
    intro hzero
    apply hC
    apply f.injective
    simpa [aE, map_ofNat] using hzero
  have hweights :
      alpha * beta =
        actualSigma aE.multiplier aE.a2 aE.a3 uE tE := by
    simpa [alpha, beta] using
      actual_secondDirected_coset_weights_mul
        aE.multiplier aE.a2 aE.a3 uE tE q r
  have hsigma : alpha * beta ≠ 0 := by
    rw [hweights]
    exact actualSigma_ne_zero_of_reverseCandidateRegular
      aE.multiplier aE.a1 aE.a2 aE.a3 uE tE htraceE hregularE
  have hEven :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualSecondEvenObstruction_ne_zero_of_candidateRegular
      aE.multiplier aE.a1 aE.a2 aE.a3 uE tE
        htraceE hCE hregularE
  have hreachable :
      ∀ h : Subgroup.zpowers (q ^ 2),
        ∃ n : ℕ,
          weightedSplitTorusTrace alpha beta h + gamma =
            f (orderedTrace a.multiplier a.a3
              (((rotation1 a)^[n]) x).x3) := by
    intro h
    have hDE : discriminant tE ≠ 0 := by
      simpa [discriminant] using hregularE.1
    have heigen' :
        tE = (q : E) + ((q⁻¹ : Eˣ) : E) := by
      simpa [tE, E, f, splitTorusTrace] using heigen
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
    refine ⟨n, ?_⟩
    calc
      weightedSplitTorusTrace alpha beta h + gamma =
          orderedTrace aE.multiplier aE.a3
            (fiberPoint1 aE uE tE (q : E)
              ((r * (h : Eˣ) : Eˣ) : E)).x3 := by
        change
          weightedSplitTorusTrace alpha beta h + gamma =
            aE.multiplier *
                (fiberPair aE.a2 aE.a3 uE tE (q : E)
                  ((r * (h : Eˣ) : Eˣ) : E)).2 -
              aE.a3
        simpa [alpha, beta, gamma] using
          (secondTrace_fiberPair_mul_eq_weightedSplitTorusTrace
            aE.multiplier aE.a2 aE.a3 uE tE q r (h : Eˣ)).symm
      _ = orderedTrace aE.multiplier aE.a3 (mapPoint f y).x3 := by
        rw [hyPoint]
      _ = f (orderedTrace a.multiplier a.a3 y.x3) := by
        simp [orderedTrace, aE, mapPoint]
      _ = f (orderedTrace a.multiplier a.a3
          (((rotation1 a)^[n]) x).x3) := rfl
  exact
    exists_iterate_with_larger_actualOrder_or_halfStepOrder_outside_candidates_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation1 a) x
        (fun y ↦ orderedTrace a.multiplier a.a3 y.x3)
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hcube hlinear

/-- Forward target from a second-coordinate fiber.  This is an independent
`rotation2` specialization with ordered frame `(a₂,a₃,a₁)`. -/
theorem
    exists_rotation2_iterate_axisThree_with_larger_actualOrder_or_halfStepOrder_outside_candidates_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u)
    (hB : a.a3 ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a3 a.a1 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      mapPoint (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint2
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
      let y := ((rotation2 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a3 y.x3
      rotationLinearOrder t < rotationLinearOrder t' ∨
        (BGS.Markoff.rotationOrder t' ∉
            middleGameCandidateOrders p (rotationLinearOrder t) ∧
          Nat.gcd (BGS.Markoff.rotationOrder t') 2 = 2 ∧
          rotationLinearOrder t < BGS.Markoff.rotationOrder t' ∧
          BGS.Markoff.rotationOrder t' ≤
            2 * rotationLinearOrder t) := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := mapCoefficients f a
  let uE : E := f u
  let tE : E := f t
  let alpha : E := actualAlpha aE.multiplier * (r : E)
  let beta : E :=
    actualBeta aE.multiplier aE.a3 aE.a1 uE tE / (r : E)
  let gamma : E :=
    actualGammaFirst aE.multiplier aE.a3 aE.a1 uE tE
  have hDBase : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a2 uE := by
    have hmap := congrArg f hcoordinate
    simpa [tE, uE, aE, orderedTrace] using hmap
  have hregularE :
      OrderedTraceCandidateRegular aE.a2 aE.a3 aE.a1 tE := by
    simpa [aE, tE] using
      orderedTraceCandidateRegular_map f f.injective hregular
  have hBE : aE.a3 ^ 2 ≠ 4 := by
    intro hzero
    apply hB
    apply f.injective
    simpa [aE, map_ofNat] using hzero
  have hweights :
      alpha * beta =
        actualSigma aE.multiplier aE.a3 aE.a1 uE tE := by
    simpa [alpha, beta] using
      actual_firstDirected_coset_weights_mul
        aE.multiplier aE.a3 aE.a1 uE tE r
  have hsigma : alpha * beta ≠ 0 := by
    rw [hweights]
    exact actualSigma_ne_zero_of_candidateRegular
      aE.multiplier aE.a2 aE.a3 aE.a1 uE tE htraceE hregularE
  have hEven :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualEvenObstruction_ne_zero_of_candidateRegular
      aE.multiplier aE.a2 aE.a3 aE.a1 uE tE
        htraceE hBE hregularE
  have hreachable :
      ∀ h : Subgroup.zpowers (q ^ 2),
        ∃ n : ℕ,
          weightedSplitTorusTrace alpha beta h + gamma =
            f (orderedTrace a.multiplier a.a3
              (((rotation2 a)^[n]) x).x3) := by
    intro h
    have hDE : discriminant tE ≠ 0 := by
      simpa [discriminant] using hregularE.1
    have heigen' :
        tE = (q : E) + ((q⁻¹ : Eˣ) : E) := by
      simpa [tE, E, f, splitTorusTrace] using heigen
    obtain ⟨n, hn⟩ :=
      exists_iterate_fiberPoint2_eq_mul_zpowers_sq
        aE uE tE q r hDE heigen' htraceE h
    let y : Point (ZMod p) := ((rotation2 a)^[n]) x
    have hyPoint :
        mapPoint f y =
          fiberPoint2 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := by
      calc
        mapPoint f y =
            ((rotation2 aE)^[n]) (mapPoint f x) := by
          simpa [y, aE] using mapPoint_iterate_rotation2 f a x n
        _ = ((rotation2 aE)^[n])
            (fiberPoint2 aE uE tE (q : E) (r : E)) := by
          simpa [E, f, aE, uE, tE] using congrArg
            (fun z : Point E ↦ ((rotation2 aE)^[n]) z) hdiagonalized
        _ = fiberPoint2 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := hn
    refine ⟨n, ?_⟩
    calc
      weightedSplitTorusTrace alpha beta h + gamma =
          orderedTrace aE.multiplier aE.a3
            (fiberPoint2 aE uE tE (q : E)
              ((r * (h : Eˣ) : Eˣ) : E)).x3 := by
        change
          weightedSplitTorusTrace alpha beta h + gamma =
            aE.multiplier *
                (fiberPair aE.a3 aE.a1 uE tE (q : E)
                  ((r * (h : Eˣ) : Eˣ) : E)).1 -
              aE.a3
        simpa [alpha, beta, gamma] using
          (firstTrace_fiberPair_mul_eq_weightedSplitTorusTrace
            aE.multiplier aE.a3 aE.a1 uE tE q r (h : Eˣ)).symm
      _ = orderedTrace aE.multiplier aE.a3 (mapPoint f y).x3 := by
        rw [hyPoint]
      _ = f (orderedTrace a.multiplier a.a3 y.x3) := by
        simp [orderedTrace, aE, mapPoint]
      _ = f (orderedTrace a.multiplier a.a3
          (((rotation2 a)^[n]) x).x3) := rfl
  exact
    exists_iterate_with_larger_actualOrder_or_halfStepOrder_outside_candidates_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation2 a) x
        (fun y ↦ orderedTrace a.multiplier a.a3 y.x3)
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hcube hlinear

/-- Reverse target from a second-coordinate fiber, with ordered frame
`(a₂,a₁,a₃)` and the original coefficient triple left fixed. -/
theorem
    exists_rotation2_iterate_axisOne_with_larger_actualOrder_or_halfStepOrder_outside_candidates_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a1 a.a3 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      mapPoint (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint2
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
      let y := ((rotation2 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a1 y.x1
      rotationLinearOrder t < rotationLinearOrder t' ∨
        (BGS.Markoff.rotationOrder t' ∉
            middleGameCandidateOrders p (rotationLinearOrder t) ∧
          Nat.gcd (BGS.Markoff.rotationOrder t') 2 = 2 ∧
          rotationLinearOrder t < BGS.Markoff.rotationOrder t' ∧
          BGS.Markoff.rotationOrder t' ≤
            2 * rotationLinearOrder t) := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := mapCoefficients f a
  let uE : E := f u
  let tE : E := f t
  let alpha : E :=
    (aE.multiplier * (q : E)) * (r : E)
  let beta : E :=
    (aE.multiplier * centeredFiberProduct aE.a3 aE.a1 uE tE /
      (q : E)) / (r : E)
  let gamma : E :=
    actualGammaSecond aE.multiplier aE.a3 aE.a1 uE tE
  have hDBase : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a2 uE := by
    have hmap := congrArg f hcoordinate
    simpa [tE, uE, aE, orderedTrace] using hmap
  have hregularE :
      OrderedTraceCandidateRegular aE.a2 aE.a1 aE.a3 tE := by
    simpa [aE, tE] using
      orderedTraceCandidateRegular_map f f.injective hregular
  have hA1E : aE.a1 ^ 2 ≠ 4 := by
    intro hzero
    apply hA1
    apply f.injective
    simpa [aE, map_ofNat] using hzero
  have hweights :
      alpha * beta =
        actualSigma aE.multiplier aE.a3 aE.a1 uE tE := by
    simpa [alpha, beta] using
      actual_secondDirected_coset_weights_mul
        aE.multiplier aE.a3 aE.a1 uE tE q r
  have hsigma : alpha * beta ≠ 0 := by
    rw [hweights]
    exact actualSigma_ne_zero_of_reverseCandidateRegular
      aE.multiplier aE.a2 aE.a3 aE.a1 uE tE htraceE hregularE
  have hEven :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualSecondEvenObstruction_ne_zero_of_candidateRegular
      aE.multiplier aE.a2 aE.a3 aE.a1 uE tE
        htraceE hA1E hregularE
  have hreachable :
      ∀ h : Subgroup.zpowers (q ^ 2),
        ∃ n : ℕ,
          weightedSplitTorusTrace alpha beta h + gamma =
            f (orderedTrace a.multiplier a.a1
              (((rotation2 a)^[n]) x).x1) := by
    intro h
    have hDE : discriminant tE ≠ 0 := by
      simpa [discriminant] using hregularE.1
    have heigen' :
        tE = (q : E) + ((q⁻¹ : Eˣ) : E) := by
      simpa [tE, E, f, splitTorusTrace] using heigen
    obtain ⟨n, hn⟩ :=
      exists_iterate_fiberPoint2_eq_mul_zpowers_sq
        aE uE tE q r hDE heigen' htraceE h
    let y : Point (ZMod p) := ((rotation2 a)^[n]) x
    have hyPoint :
        mapPoint f y =
          fiberPoint2 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := by
      calc
        mapPoint f y =
            ((rotation2 aE)^[n]) (mapPoint f x) := by
          simpa [y, aE] using mapPoint_iterate_rotation2 f a x n
        _ = ((rotation2 aE)^[n])
            (fiberPoint2 aE uE tE (q : E) (r : E)) := by
          simpa [E, f, aE, uE, tE] using congrArg
            (fun z : Point E ↦ ((rotation2 aE)^[n]) z) hdiagonalized
        _ = fiberPoint2 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := hn
    refine ⟨n, ?_⟩
    calc
      weightedSplitTorusTrace alpha beta h + gamma =
          orderedTrace aE.multiplier aE.a1
            (fiberPoint2 aE uE tE (q : E)
              ((r * (h : Eˣ) : Eˣ) : E)).x1 := by
        change
          weightedSplitTorusTrace alpha beta h + gamma =
            aE.multiplier *
                (fiberPair aE.a3 aE.a1 uE tE (q : E)
                  ((r * (h : Eˣ) : Eˣ) : E)).2 -
              aE.a1
        simpa [alpha, beta, gamma] using
          (secondTrace_fiberPair_mul_eq_weightedSplitTorusTrace
            aE.multiplier aE.a3 aE.a1 uE tE q r (h : Eˣ)).symm
      _ = orderedTrace aE.multiplier aE.a1 (mapPoint f y).x1 := by
        rw [hyPoint]
      _ = f (orderedTrace a.multiplier a.a1 y.x1) := by
        simp [orderedTrace, aE, mapPoint]
      _ = f (orderedTrace a.multiplier a.a1
          (((rotation2 a)^[n]) x).x1) := rfl
  exact
    exists_iterate_with_larger_actualOrder_or_halfStepOrder_outside_candidates_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation2 a) x
        (fun y ↦ orderedTrace a.multiplier a.a1 y.x1)
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hcube hlinear

/-- Forward target from a third-coordinate fiber.  This is an independent
`rotation3` specialization with ordered frame `(a₃, a₁, a₂)`. -/
theorem
    exists_rotation3_iterate_axisOne_with_larger_actualOrder_or_halfStepOrder_outside_candidates_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a3 u)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a3 a.a1 a.a2 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      mapPoint (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint3
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
      let y := ((rotation3 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a1 y.x1
      rotationLinearOrder t < rotationLinearOrder t' ∨
        (BGS.Markoff.rotationOrder t' ∉
            middleGameCandidateOrders p (rotationLinearOrder t) ∧
          Nat.gcd (BGS.Markoff.rotationOrder t') 2 = 2 ∧
          rotationLinearOrder t < BGS.Markoff.rotationOrder t' ∧
          BGS.Markoff.rotationOrder t' ≤
            2 * rotationLinearOrder t) := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := mapCoefficients f a
  let uE : E := f u
  let tE : E := f t
  let alpha : E := actualAlpha aE.multiplier * (r : E)
  let beta : E :=
    actualBeta aE.multiplier aE.a1 aE.a2 uE tE / (r : E)
  let gamma : E :=
    actualGammaFirst aE.multiplier aE.a1 aE.a2 uE tE
  have hDBase : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a3 uE := by
    have hmap := congrArg f hcoordinate
    simpa [tE, uE, aE, orderedTrace] using hmap
  have hregularE :
      OrderedTraceCandidateRegular aE.a3 aE.a1 aE.a2 tE := by
    simpa [aE, tE] using
      orderedTraceCandidateRegular_map f f.injective hregular
  have hA1E : aE.a1 ^ 2 ≠ 4 := by
    intro hzero
    apply hA1
    apply f.injective
    simpa [aE, map_ofNat] using hzero
  have hweights :
      alpha * beta =
        actualSigma aE.multiplier aE.a1 aE.a2 uE tE := by
    simpa [alpha, beta] using
      actual_firstDirected_coset_weights_mul
        aE.multiplier aE.a1 aE.a2 uE tE r
  have hsigma : alpha * beta ≠ 0 := by
    rw [hweights]
    exact actualSigma_ne_zero_of_candidateRegular
      aE.multiplier aE.a3 aE.a1 aE.a2 uE tE htraceE hregularE
  have hEven :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualEvenObstruction_ne_zero_of_candidateRegular
      aE.multiplier aE.a3 aE.a1 aE.a2 uE tE
        htraceE hA1E hregularE
  have hreachable :
      ∀ h : Subgroup.zpowers (q ^ 2),
        ∃ n : ℕ,
          weightedSplitTorusTrace alpha beta h + gamma =
            f (orderedTrace a.multiplier a.a1
              (((rotation3 a)^[n]) x).x1) := by
    intro h
    have hDE : discriminant tE ≠ 0 := by
      simpa [discriminant] using hregularE.1
    have heigen' :
        tE = (q : E) + ((q⁻¹ : Eˣ) : E) := by
      simpa [tE, E, f, splitTorusTrace] using heigen
    obtain ⟨n, hn⟩ :=
      exists_iterate_fiberPoint3_eq_mul_zpowers_sq
        aE uE tE q r hDE heigen' htraceE h
    let y : Point (ZMod p) := ((rotation3 a)^[n]) x
    have hyPoint :
        mapPoint f y =
          fiberPoint3 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := by
      calc
        mapPoint f y =
            ((rotation3 aE)^[n]) (mapPoint f x) := by
          simpa [y, aE] using mapPoint_iterate_rotation3 f a x n
        _ = ((rotation3 aE)^[n])
            (fiberPoint3 aE uE tE (q : E) (r : E)) := by
          simpa [E, f, aE, uE, tE] using congrArg
            (fun z : Point E ↦ ((rotation3 aE)^[n]) z) hdiagonalized
        _ = fiberPoint3 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := hn
    refine ⟨n, ?_⟩
    calc
      weightedSplitTorusTrace alpha beta h + gamma =
          orderedTrace aE.multiplier aE.a1
            (fiberPoint3 aE uE tE (q : E)
              ((r * (h : Eˣ) : Eˣ) : E)).x1 := by
        change
          weightedSplitTorusTrace alpha beta h + gamma =
            aE.multiplier *
                (fiberPair aE.a1 aE.a2 uE tE (q : E)
                  ((r * (h : Eˣ) : Eˣ) : E)).1 -
              aE.a1
        simpa [alpha, beta, gamma] using
          (firstTrace_fiberPair_mul_eq_weightedSplitTorusTrace
            aE.multiplier aE.a1 aE.a2 uE tE q r (h : Eˣ)).symm
      _ = orderedTrace aE.multiplier aE.a1 (mapPoint f y).x1 := by
        rw [hyPoint]
      _ = f (orderedTrace a.multiplier a.a1 y.x1) := by
        simp [orderedTrace, aE, mapPoint]
      _ = f (orderedTrace a.multiplier a.a1
          (((rotation3 a)^[n]) x).x1) := rfl
  exact
    exists_iterate_with_larger_actualOrder_or_halfStepOrder_outside_candidates_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation3 a) x
        (fun y ↦ orderedTrace a.multiplier a.a1 y.x1)
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hcube hlinear

/-- Reverse target from a third-coordinate fiber, with ordered frame
`(a₃, a₂, a₁)` and the original coefficient triple left fixed. -/
theorem
    exists_rotation3_iterate_axisTwo_with_larger_actualOrder_or_halfStepOrder_outside_candidates_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a3 u)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a3 a.a2 a.a1 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      mapPoint (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint3
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
      let y := ((rotation3 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a2 y.x2
      rotationLinearOrder t < rotationLinearOrder t' ∨
        (BGS.Markoff.rotationOrder t' ∉
            middleGameCandidateOrders p (rotationLinearOrder t) ∧
          Nat.gcd (BGS.Markoff.rotationOrder t') 2 = 2 ∧
          rotationLinearOrder t < BGS.Markoff.rotationOrder t' ∧
          BGS.Markoff.rotationOrder t' ≤
            2 * rotationLinearOrder t) := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := mapCoefficients f a
  let uE : E := f u
  let tE : E := f t
  let alpha : E :=
    (aE.multiplier * (q : E)) * (r : E)
  let beta : E :=
    (aE.multiplier * centeredFiberProduct aE.a1 aE.a2 uE tE /
      (q : E)) / (r : E)
  let gamma : E :=
    actualGammaSecond aE.multiplier aE.a1 aE.a2 uE tE
  have hDBase : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a3 uE := by
    have hmap := congrArg f hcoordinate
    simpa [tE, uE, aE, orderedTrace] using hmap
  have hregularE :
      OrderedTraceCandidateRegular aE.a3 aE.a2 aE.a1 tE := by
    simpa [aE, tE] using
      orderedTraceCandidateRegular_map f f.injective hregular
  have hA2E : aE.a2 ^ 2 ≠ 4 := by
    intro hzero
    apply hA2
    apply f.injective
    simpa [aE, map_ofNat] using hzero
  have hweights :
      alpha * beta =
        actualSigma aE.multiplier aE.a1 aE.a2 uE tE := by
    simpa [alpha, beta] using
      actual_secondDirected_coset_weights_mul
        aE.multiplier aE.a1 aE.a2 uE tE q r
  have hsigma : alpha * beta ≠ 0 := by
    rw [hweights]
    exact actualSigma_ne_zero_of_reverseCandidateRegular
      aE.multiplier aE.a3 aE.a1 aE.a2 uE tE htraceE hregularE
  have hEven :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualSecondEvenObstruction_ne_zero_of_candidateRegular
      aE.multiplier aE.a3 aE.a1 aE.a2 uE tE
        htraceE hA2E hregularE
  have hreachable :
      ∀ h : Subgroup.zpowers (q ^ 2),
        ∃ n : ℕ,
          weightedSplitTorusTrace alpha beta h + gamma =
            f (orderedTrace a.multiplier a.a2
              (((rotation3 a)^[n]) x).x2) := by
    intro h
    have hDE : discriminant tE ≠ 0 := by
      simpa [discriminant] using hregularE.1
    have heigen' :
        tE = (q : E) + ((q⁻¹ : Eˣ) : E) := by
      simpa [tE, E, f, splitTorusTrace] using heigen
    obtain ⟨n, hn⟩ :=
      exists_iterate_fiberPoint3_eq_mul_zpowers_sq
        aE uE tE q r hDE heigen' htraceE h
    let y : Point (ZMod p) := ((rotation3 a)^[n]) x
    have hyPoint :
        mapPoint f y =
          fiberPoint3 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := by
      calc
        mapPoint f y =
            ((rotation3 aE)^[n]) (mapPoint f x) := by
          simpa [y, aE] using mapPoint_iterate_rotation3 f a x n
        _ = ((rotation3 aE)^[n])
            (fiberPoint3 aE uE tE (q : E) (r : E)) := by
          simpa [E, f, aE, uE, tE] using congrArg
            (fun z : Point E ↦ ((rotation3 aE)^[n]) z) hdiagonalized
        _ = fiberPoint3 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := hn
    refine ⟨n, ?_⟩
    calc
      weightedSplitTorusTrace alpha beta h + gamma =
          orderedTrace aE.multiplier aE.a2
            (fiberPoint3 aE uE tE (q : E)
              ((r * (h : Eˣ) : Eˣ) : E)).x2 := by
        change
          weightedSplitTorusTrace alpha beta h + gamma =
            aE.multiplier *
                (fiberPair aE.a1 aE.a2 uE tE (q : E)
                  ((r * (h : Eˣ) : Eˣ) : E)).2 -
              aE.a2
        simpa [alpha, beta, gamma] using
          (secondTrace_fiberPair_mul_eq_weightedSplitTorusTrace
            aE.multiplier aE.a1 aE.a2 uE tE q r (h : Eˣ)).symm
      _ = orderedTrace aE.multiplier aE.a2 (mapPoint f y).x2 := by
        rw [hyPoint]
      _ = f (orderedTrace a.multiplier a.a2 y.x2) := by
        simp [orderedTrace, aE, mapPoint]
      _ = f (orderedTrace a.multiplier a.a2
          (((rotation3 a)^[n]) x).x2) := rfl
  exact
    exists_iterate_with_larger_actualOrder_or_halfStepOrder_outside_candidates_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation3 a) x
        (fun y ↦ orderedTrace a.multiplier a.a2 y.x2)
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hcube hlinear

end SurfaceSpecializations

end

end GenMarkoff.General.MiddleGame
