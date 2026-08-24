import GenMarkoff.General.Cage.OrbitConnectingThreeRootEstimate
import GenMarkoff.General.Cage.ConnectingGeometricSquareClasses

/-!
# Square classes for orbit-correct connecting radicands

The incidence radicand attached to one endpoint is the orbit-discriminant
radicand, up to its nonzero leading coefficient.  When the orbit weight
product is a square, that discriminant splits into the two component
radicands.

For the actual orbit-coset cover, both component equations carry an
additional factor `X ^ d`.  This file keeps those factors explicit and
proves the seven rational-function square classes needed by the
hyperelliptic-plane argument.
-/

namespace GenMarkoff.General.Cage

open Polynomial

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- Scalar extension commutes with the ordered orbit-weight product. -/
theorem map_orderedTraceSigma
    {L : Type*} [Field L] (phi : K →+* L)
    (A B C0 xi : K) :
    phi (orderedTraceSigma A B C0 xi) =
      orderedTraceSigma (phi A) (phi B) (phi C0) (phi xi) := by
  simp [orderedTraceSigma, map_ofNat]

/-- Scalar extension commutes with the ordered orbit shift. -/
theorem map_orderedTraceGamma
    {L : Type*} [Field L] (phi : K →+* L)
    (A B C0 xi : K) :
    phi (orderedTraceGamma A B C0 xi) =
      orderedTraceGamma (phi A) (phi B) (phi C0) (phi xi) := by
  simp [orderedTraceGamma, eval_orderedTraceShiftPolynomial, map_ofNat]

/-- Scalar extension commutes with the positive component pullback. -/
theorem map_orbitComponentPlusPulledRadicand
    {L : Type*} [Field L] (phi : K →+* L)
    (alpha gamma k : K) (d : ℕ) :
    (orbitComponentPlusPulledRadicand alpha gamma k d).map phi =
      orbitComponentPlusPulledRadicand
        (phi alpha) (phi gamma) (phi k) d := by
  simp [orbitComponentPlusPulledRadicand, map_ofNat]

/-- Scalar extension commutes with the negative component pullback. -/
theorem map_orbitComponentMinusPulledRadicand
    {L : Type*} [Field L] (phi : K →+* L)
    (alpha gamma k : K) (d : ℕ) :
    (orbitComponentMinusPulledRadicand alpha gamma k d).map phi =
      orbitComponentMinusPulledRadicand
        (phi alpha) (phi gamma) (phi k) d := by
  simp [orbitComponentMinusPulledRadicand, map_ofNat]

/-- Scalar extension commutes with the coset-correct positive component
pullback. -/
theorem map_orbitComponentPlusCosetPulledRadicand
    {L : Type*} [Field L] (phi : K →+* L)
    (alpha gamma k : K) (d : ℕ) :
    (orbitComponentPlusCosetPulledRadicand alpha gamma k d).map phi =
      orbitComponentPlusCosetPulledRadicand
        (phi alpha) (phi gamma) (phi k) d := by
  simp [orbitComponentPlusCosetPulledRadicand,
    map_orbitComponentPlusPulledRadicand]

/-- Scalar extension commutes with the coset-correct negative component
pullback. -/
theorem map_orbitComponentMinusCosetPulledRadicand
    {L : Type*} [Field L] (phi : K →+* L)
    (alpha gamma k : K) (d : ℕ) :
    (orbitComponentMinusCosetPulledRadicand alpha gamma k d).map phi =
      orbitComponentMinusCosetPulledRadicand
        (phi alpha) (phi gamma) (phi k) d := by
  simp [orbitComponentMinusCosetPulledRadicand,
    map_orbitComponentMinusPulledRadicand]

/-- The unequal incidence pullback is exactly the orbit-discriminant
pullback multiplied by its leading coefficient. -/
theorem incidencePulledRadicand_eq_C_mul_orbitDiscriminantPulledRadicand
    {a : Coefficients K} {xi alpha beta gamma : K} (d : ℕ)
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hproduct :
      alpha * beta = orderedTraceSigma a.a1 a.a2 a.a3 xi)
    (hgamma :
      gamma = orderedTraceGamma a.a1 a.a2 a.a3 xi) :
    incidencePulledRadicand a xi d =
      C (incidenceLeadingCoefficient xi) *
        orbitDiscriminantPulledRadicand alpha beta gamma d := by
  have hD : xi ^ 2 - 4 ≠ 0 := by
    simpa only [eval_orderedTraceDiscriminantPolynomial] using hregular.1
  have hlinear :
      incidenceLinearCoefficient a xi =
        incidenceLeadingCoefficient xi * (-2 * gamma) := by
    rw [hgamma]
    simp only [orderedTraceGamma, eval_orderedTraceShiftPolynomial,
      incidenceLeadingCoefficient, incidenceLinearCoefficient,
      traceLinearCoefficient2, traceLinearCoefficient3]
    field_simp [hD]
    ring
  have hmiddle :
      incidencePulledMiddleCoefficient a xi =
        incidenceLeadingCoefficient xi *
          (gamma ^ 2 + 2 - 4 * alpha * beta) := by
    have hproduct4 :
        4 * alpha * beta =
          4 * orderedTraceSigma a.a1 a.a2 a.a3 xi := by
      calc
        4 * alpha * beta = 4 * (alpha * beta) := by ring
        _ = 4 * orderedTraceSigma a.a1 a.a2 a.a3 xi := by
          rw [hproduct]
    rw [hgamma, hproduct4]
    simp only [orderedTraceGamma, orderedTraceSigma,
      eval_orderedTraceShiftPolynomial, incidencePulledMiddleCoefficient,
      incidenceLeadingCoefficient, incidenceConstantCoefficient,
      traceLinearCoefficient1, traceLinearCoefficient3, traceConstant]
    field_simp [hD]
    ring
  rw [incidencePulledRadicand, orbitDiscriminantPulledRadicand,
    hlinear, hmiddle]
  simp only [map_mul, map_neg, map_ofNat, map_add, map_sub, map_pow]
  ring

/-- The two unscaled component pullbacks have separable product. -/
theorem orbitComponentPulledRadicands_mul_separable
    (h2 : (2 : K) ≠ 0)
    {a : Coefficients K} {xi alpha beta gamma k : K}
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (halpha : alpha ≠ 0)
    (hproduct :
      alpha * beta = orderedTraceSigma a.a1 a.a2 a.a3 xi)
    (hgamma :
      gamma = orderedTraceGamma a.a1 a.a2 a.a3 xi)
    (hsquareProduct : alpha * beta = k ^ 2)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    (orbitComponentPlusPulledRadicand alpha gamma k d *
      orbitComponentMinusPulledRadicand alpha gamma k d).Separable := by
  have hD : incidenceLeadingCoefficient xi ≠ 0 := by
    simpa only [incidenceLeadingCoefficient,
      eval_orderedTraceDiscriminantPolynomial] using hregular.1
  have hincidence :
      (incidencePulledRadicand a xi d).Separable :=
    incidencePulledRadicand_separable
      h2 hA2 hregular hd hdegree
  have horbit :
      (orbitDiscriminantPulledRadicand alpha beta gamma d).Separable := by
    have hscaled :
        (C (incidenceLeadingCoefficient xi) *
          orbitDiscriminantPulledRadicand alpha beta gamma d).Separable := by
      rw [←
        incidencePulledRadicand_eq_C_mul_orbitDiscriminantPulledRadicand
          d hregular hproduct hgamma]
      exact hincidence
    exact hscaled.of_mul_right
  have halphaSq : alpha ^ 2 ≠ 0 := pow_ne_zero 2 halpha
  have hconstant : IsUnit (C (alpha ^ 2) : K[X]) := by
    rw [isUnit_C]
    exact halphaSq.isUnit
  have hscaled :
      (C (alpha ^ 2) *
        orbitDiscriminantPulledRadicand alpha beta gamma d).Separable :=
    horbit.unit_mul hconstant
  rw [← orbitComponentPulledRadicands_mul_eq_discriminant
    alpha beta gamma k d hsquareProduct] at hscaled
  exact hscaled

/-- Squarefreeness and mutual coprimality of the two unscaled orbit
component pullbacks. -/
theorem orbitComponentPulledRadicands_squarefree_and_isCoprime
    (h2 : (2 : K) ≠ 0)
    {a : Coefficients K} {xi alpha beta gamma k : K}
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (halpha : alpha ≠ 0)
    (hproduct :
      alpha * beta = orderedTraceSigma a.a1 a.a2 a.a3 xi)
    (hgamma :
      gamma = orderedTraceGamma a.a1 a.a2 a.a3 xi)
    (hsquareProduct : alpha * beta = k ^ 2)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    Squarefree (orbitComponentPlusPulledRadicand alpha gamma k d) ∧
      Squarefree (orbitComponentMinusPulledRadicand alpha gamma k d) ∧
      IsCoprime
        (orbitComponentPlusPulledRadicand alpha gamma k d)
        (orbitComponentMinusPulledRadicand alpha gamma k d) := by
  have hsep :=
    orbitComponentPulledRadicands_mul_separable h2 hA2 hregular
      halpha hproduct hgamma hsquareProduct hd hdegree
  exact ⟨hsep.of_mul_left.squarefree, hsep.of_mul_right.squarefree,
    hsep.isCoprime⟩

/-- A positive component pullback is not a polynomial unit. -/
theorem orbitComponentPlusPulledRadicand_not_isUnit
    {alpha : K} (halpha : alpha ≠ 0) (gamma k : K)
    {d : ℕ} (hd : 0 < d) :
    ¬ IsUnit (orbitComponentPlusPulledRadicand alpha gamma k d) := by
  apply not_isUnit_of_natDegree_pos
  rw [orbitComponentPlusPulledRadicand_natDegree_eq
    halpha gamma k hd]
  omega

/-- A negative component pullback is not a polynomial unit. -/
theorem orbitComponentMinusPulledRadicand_not_isUnit
    {alpha : K} (halpha : alpha ≠ 0) (gamma k : K)
    {d : ℕ} (hd : 0 < d) :
    ¬ IsUnit (orbitComponentMinusPulledRadicand alpha gamma k d) := by
  apply not_isUnit_of_natDegree_pos
  rw [orbitComponentMinusPulledRadicand_natDegree_eq
    halpha gamma k hd]
  omega

/-- Both orbit-component factors are coprime to the reduced centered-norm
factor.  This descends the already-proved incidence/centered resultant
through the exact orbit factorization. -/
theorem
    orbitComponentPulledRadicands_isCoprime_centeredNormReducedPulledRadicand
    {a : Coefficients K} {xi alpha beta gamma k : K}
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hobstruction : incidenceCenteredNormObstruction a xi ≠ 0)
    (halpha : alpha ≠ 0)
    (hproduct :
      alpha * beta = orderedTraceSigma a.a1 a.a2 a.a3 xi)
    (hgamma :
      gamma = orderedTraceGamma a.a1 a.a2 a.a3 xi)
    (hsquareProduct : alpha * beta = k ^ 2)
    {d : ℕ} (hd : 0 < d) :
    IsCoprime
        (orbitComponentPlusPulledRadicand alpha gamma k d)
        (centeredNormReducedPulledRadicand a.a3 a.a1 d) ∧
      IsCoprime
        (orbitComponentMinusPulledRadicand alpha gamma k d)
        (centeredNormReducedPulledRadicand a.a3 a.a1 d) := by
  let h :=
    centeredNormReducedPulledRadicand a.a3 a.a1 d
  have hD : incidenceLeadingCoefficient xi ≠ 0 := by
    simpa only [incidenceLeadingCoefficient,
      eval_orderedTraceDiscriminantPolynomial] using hregular.1
  have hincidenceFull :
      IsCoprime (incidencePulledRadicand a xi d)
        (centeredNormPulledRadicand a.a3 a.a1 d) :=
    incidencePulledRadicand_isCoprime_centeredNormPulledRadicand
      hregular hobstruction hd
  have hincidence :
      IsCoprime (incidencePulledRadicand a xi d) h :=
    IsCoprime.of_isCoprime_of_dvd_right hincidenceFull
      (centeredNormReducedPulledRadicand_dvd a.a3 a.a1 d)
  have hDUnit :
      IsUnit (C (incidenceLeadingCoefficient xi) : K[X]) := by
    rw [isUnit_C]
    exact hD.isUnit
  have horbit :
      IsCoprime
        (orbitDiscriminantPulledRadicand alpha beta gamma d) h := by
    rw [incidencePulledRadicand_eq_C_mul_orbitDiscriminantPulledRadicand
      d hregular hproduct hgamma] at hincidence
    exact
      (isCoprime_mul_unit_left_left hDUnit
        (orbitDiscriminantPulledRadicand alpha beta gamma d) h).mp
        hincidence
  have halphaSq : alpha ^ 2 ≠ 0 := pow_ne_zero 2 halpha
  have halphaUnit : IsUnit (C (alpha ^ 2) : K[X]) := by
    rw [isUnit_C]
    exact halphaSq.isUnit
  have hcomponents :
      IsCoprime
        (orbitComponentPlusPulledRadicand alpha gamma k d *
          orbitComponentMinusPulledRadicand alpha gamma k d) h := by
    rw [orbitComponentPulledRadicands_mul_eq_discriminant
      alpha beta gamma k d hsquareProduct]
    exact
      (isCoprime_mul_unit_left_left halphaUnit
        (orbitDiscriminantPulledRadicand alpha beta gamma d) h).mpr
        horbit
  exact ⟨hcomponents.of_mul_left_left,
    hcomponents.of_mul_left_right⟩

/-- The two unscaled orbit-component factors and the reduced centered-norm
factor have all seven nontrivial rational-function square classes. -/
theorem orbitComponentSevenRadicandProducts_not_isSquare_ratFunc
    (h2 : (2 : K) ≠ 0)
    {a : Coefficients K} {xi alpha beta gamma k : K}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hobstruction : incidenceCenteredNormObstruction a xi ≠ 0)
    (halpha : alpha ≠ 0)
    (hproduct :
      alpha * beta = orderedTraceSigma a.a1 a.a2 a.a3 xi)
    (hgamma :
      gamma = orderedTraceGamma a.a1 a.a2 a.a3 xi)
    (hsquareProduct : alpha * beta = k ^ 2)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    let f := orbitComponentPlusPulledRadicand alpha gamma k d
    let g := orbitComponentMinusPulledRadicand alpha gamma k d
    let h := centeredNormReducedPulledRadicand a.a3 a.a1 d
    (¬ IsSquare (algebraMap K[X] (RatFunc K) f)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) g)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) h)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g))) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * h))) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (g * h))) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g * h))) := by
  dsimp only
  obtain ⟨hf, hg, hfg⟩ :=
    orbitComponentPulledRadicands_squarefree_and_isCoprime
      h2 hA2 hregular halpha hproduct hgamma hsquareProduct hd hdegree
  have hh :
      Squarefree
        (centeredNormReducedPulledRadicand a.a3 a.a1 d) :=
    centeredNormReducedPulledRadicand_squarefree
      hA3 hA1 hmoving hd hdegree
  obtain ⟨hfh, hgh⟩ :=
    orbitComponentPulledRadicands_isCoprime_centeredNormReducedPulledRadicand
      hregular hobstruction halpha hproduct hgamma hsquareProduct hd
  exact
    sevenRadicandProducts_not_isSquare_ratFunc
      hf hg hh hfg hfh hgh
      (orbitComponentPlusPulledRadicand_not_isUnit
        halpha gamma k hd)
      (orbitComponentMinusPulledRadicand_not_isUnit
        halpha gamma k hd)
      (centeredNormReducedPulledRadicand_not_isUnit
        a.a3 a.a1 hd)

/-- A polynomial with nonzero constant coefficient is coprime to `X`. -/
theorem isCoprime_X_of_coeff_zero_ne_zero
    {f : K[X]} (hf : f.coeff 0 ≠ 0) :
    IsCoprime (X : K[X]) f := by
  let c := f.coeff 0
  have htail : f - X * divX f = C c := by
    apply sub_eq_iff_eq_add.mpr
    calc
      f = X * divX f + C (f.coeff 0) :=
        (X_mul_divX_add f).symm
      _ = C c + X * divX f := by
        dsimp only [c]
        ac_rfl
  refine
    ⟨-(C c⁻¹ * divX f), C c⁻¹, ?_⟩
  calc
    -(C c⁻¹ * divX f) * X + C c⁻¹ * f =
        C c⁻¹ * (f - X * divX f) := by ring
    _ = C c⁻¹ * C c :=
      congrArg (fun z : K[X] => C c⁻¹ * z) htail
    _ = 1 := by
      rw [← C_mul, inv_mul_cancel₀ hf, C_1]

@[simp]
theorem coeff_zero_orbitComponentPlusPulledRadicand
    (alpha gamma k : K) {d : ℕ} (hd : 0 < d) :
    (orbitComponentPlusPulledRadicand alpha gamma k d).coeff 0 =
      alpha := by
  have h0d : 0 ≠ d := ne_of_lt hd
  have h02d : 0 ≠ 2 * d := by omega
  simp [orbitComponentPlusPulledRadicand, h0d, h02d]

@[simp]
theorem coeff_zero_orbitComponentMinusPulledRadicand
    (alpha gamma k : K) {d : ℕ} (hd : 0 < d) :
    (orbitComponentMinusPulledRadicand alpha gamma k d).coeff 0 =
      alpha := by
  have h0d : 0 ≠ d := ne_of_lt hd
  have h02d : 0 ≠ 2 * d := by omega
  simp [orbitComponentMinusPulledRadicand, h0d, h02d]

@[simp]
theorem coeff_zero_centeredNormReducedPulledRadicand
    (B C0 : K) {d : ℕ} (hd : 0 < d) :
    (centeredNormReducedPulledRadicand B C0 d).coeff 0 = 1 := by
  classical
  have h0d : 0 ≠ d := ne_of_lt hd
  have h02d : 0 ≠ 2 * d := by omega
  have h03d : 0 ≠ 3 * d := by omega
  have h04d : 0 ≠ 4 * d := by omega
  have hmonic (A : K) :
      (monicQuadraticPowerPulledRadicand A d).coeff 0 = 1 := by
    simp [monicQuadraticPowerPulledRadicand, h0d, h02d]
  have hfull :
      (centeredNormPulledRadicand B C0 d).coeff 0 = 1 := by
    simp [centeredNormPulledRadicand, h0d, h02d, h03d, h04d]
  by_cases hEq : B = C0
  · rw [centeredNormReducedPulledRadicand, if_pos hEq]
    exact hmonic _
  · by_cases hNeg : B = -C0
    · rw [centeredNormReducedPulledRadicand, if_neg hEq, if_pos hNeg]
      exact hmonic _
    · rw [centeredNormReducedPulledRadicand, if_neg hEq, if_neg hNeg]
      exact hfull

/-- The coordinate prime is disjoint from both component pullbacks and
from the reduced centered-norm pullback. -/
theorem isCoprime_X_orbitComponents_and_centeredNormReduced
    {alpha gamma k : K} (halpha : alpha ≠ 0)
    (B C0 : K) {d : ℕ} (hd : 0 < d) :
    IsCoprime (X : K[X])
        (orbitComponentPlusPulledRadicand alpha gamma k d) ∧
      IsCoprime (X : K[X])
        (orbitComponentMinusPulledRadicand alpha gamma k d) ∧
      IsCoprime (X : K[X])
        (centeredNormReducedPulledRadicand B C0 d) := by
  exact
    ⟨isCoprime_X_of_coeff_zero_ne_zero (by
        rw [coeff_zero_orbitComponentPlusPulledRadicand
          alpha gamma k hd]
        exact halpha),
      isCoprime_X_of_coeff_zero_ne_zero (by
        rw [coeff_zero_orbitComponentMinusPulledRadicand
          alpha gamma k hd]
        exact halpha),
      isCoprime_X_of_coeff_zero_ne_zero (by
        rw [coeff_zero_centeredNormReducedPulledRadicand B C0 hd]
        exact one_ne_zero)⟩

/-- Multiplying the first two radicands by independent nonzero polynomial
squares leaves all seven rational-function square classes unchanged. -/
theorem seven_not_isSquare_replace_first_two_by_square_mul
    {f g h q r : K[X]}
    (hq : q ≠ 0) (hr : r ≠ 0)
    (hs :
      (¬ IsSquare (algebraMap K[X] (RatFunc K) f)) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) g)) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) h)) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g))) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * h))) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) (g * h))) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g * h)))) :
    (¬ IsSquare
      (algebraMap K[X] (RatFunc K) (q ^ 2 * f))) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K) (r ^ 2 * g))) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K) h)) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K)
          ((q ^ 2 * f) * (r ^ 2 * g)))) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K) ((q ^ 2 * f) * h))) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K) ((r ^ 2 * g) * h))) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K)
          ((q ^ 2 * f) * (r ^ 2 * g) * h))) := by
  let i : K[X] →+* RatFunc K := algebraMap K[X] (RatFunc K)
  have hiq : i q ≠ 0 :=
    (map_ne_zero_iff i (RatFunc.algebraMap_injective K)).2 hq
  have hir : i r ≠ 0 :=
    (map_ne_zero_iff i (RatFunc.algebraMap_injective K)).2 hr
  have hiqr : i (q * r) ≠ 0 :=
    (map_ne_zero_iff i (RatFunc.algebraMap_injective K)).2
      (mul_ne_zero hq hr)
  refine ⟨?_, ?_, hs.2.2.1, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_pow]
    exact fun hsquare =>
      hs.1 ((isSquare_sq_mul_iff (i q) (i f) hiq).1 hsquare)
  · rw [map_mul, map_pow]
    exact fun hsquare =>
      hs.2.1 ((isSquare_sq_mul_iff (i r) (i g) hir).1 hsquare)
  · rw [show (q ^ 2 * f) * (r ^ 2 * g) =
        (q * r) ^ 2 * (f * g) by ring, map_mul, map_pow]
    exact fun hsquare =>
      hs.2.2.2.1
        ((isSquare_sq_mul_iff (i (q * r)) (i (f * g)) hiqr).1
          hsquare)
  · rw [show (q ^ 2 * f) * h = q ^ 2 * (f * h) by ring,
      map_mul, map_pow]
    exact fun hsquare =>
      hs.2.2.2.2.1
        ((isSquare_sq_mul_iff (i q) (i (f * h)) hiq).1 hsquare)
  · rw [show (r ^ 2 * g) * h = r ^ 2 * (g * h) by ring,
      map_mul, map_pow]
    exact fun hsquare =>
      hs.2.2.2.2.2.1
        ((isSquare_sq_mul_iff (i r) (i (g * h)) hir).1 hsquare)
  · rw [show (q ^ 2 * f) * (r ^ 2 * g) * h =
        (q * r) ^ 2 * (f * g * h) by ring, map_mul, map_pow]
    exact fun hsquare =>
      hs.2.2.2.2.2.2
        ((isSquare_sq_mul_iff
          (i (q * r)) (i (f * g * h)) hiqr).1 hsquare)

/-- If `X` is coprime to each of three base radicands, inserting `X` in
both of the first two radicands preserves independence of the seven square
classes.  The common `X` cancels in the products containing both. -/
theorem seven_X_mul_first_two_not_isSquare_ratFunc
    {f g h : K[X]}
    (hf : Squarefree f) (hg : Squarefree g) (hh : Squarefree h)
    (hfg : IsCoprime f g) (hfh : IsCoprime f h)
    (hgh : IsCoprime g h)
    (hXf : IsCoprime (X : K[X]) f)
    (hXg : IsCoprime (X : K[X]) g)
    (hXh : IsCoprime (X : K[X]) h)
    (hfUnit : ¬ IsUnit f) (hgUnit : ¬ IsUnit g)
    (hhUnit : ¬ IsUnit h) :
    (¬ IsSquare
      (algebraMap K[X] (RatFunc K) (X * f))) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K) (X * g))) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K) h)) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K) ((X * f) * (X * g)))) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K) ((X * f) * h))) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K) ((X * g) * h))) ∧
      (¬ IsSquare
        (algebraMap K[X] (RatFunc K) ((X * f) * (X * g) * h))) := by
  have hs :=
    sevenRadicandProducts_not_isSquare_ratFunc
      hf hg hh hfg hfh hgh hfUnit hgUnit hhUnit
  have hXSquarefree : Squarefree (X : K[X]) :=
    Polynomial.separable_X.squarefree
  have hXfSquarefree : Squarefree (X * f) :=
    squarefree_mul_iff.mpr ⟨hXf.isRelPrime, hXSquarefree, hf⟩
  have hXgSquarefree : Squarefree (X * g) :=
    squarefree_mul_iff.mpr ⟨hXg.isRelPrime, hXSquarefree, hg⟩
  have hXf_h : IsCoprime (X * f) h := hXh.mul_left hfh
  have hXg_h : IsCoprime (X * g) h := hXh.mul_left hgh
  have hXf_hSquarefree : Squarefree ((X * f) * h) :=
    squarefree_mul_iff.mpr
      ⟨hXf_h.isRelPrime, hXfSquarefree, hh⟩
  have hXg_hSquarefree : Squarefree ((X * g) * h) :=
    squarefree_mul_iff.mpr
      ⟨hXg_h.isRelPrime, hXgSquarefree, hh⟩
  have hXfUnit : ¬ IsUnit (X * f) := by
    intro hunit
    exact Polynomial.not_isUnit_X (IsUnit.mul_iff.mp hunit).1
  have hXgUnit : ¬ IsUnit (X * g) := by
    intro hunit
    exact Polynomial.not_isUnit_X (IsUnit.mul_iff.mp hunit).1
  have hXf_hUnit : ¬ IsUnit ((X * f) * h) := by
    intro hunit
    exact hXfUnit (IsUnit.mul_iff.mp hunit).1
  have hXg_hUnit : ¬ IsUnit ((X * g) * h) := by
    intro hunit
    exact hXgUnit (IsUnit.mul_iff.mp hunit).1
  let i : K[X] →+* RatFunc K := algebraMap K[X] (RatFunc K)
  have hiX : i X ≠ 0 :=
    (map_ne_zero_iff i (RatFunc.algebraMap_injective K)).2 X_ne_zero
  refine
    ⟨BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        hXfSquarefree hXfUnit,
      BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        hXgSquarefree hXgUnit,
      hs.2.2.1, ?_,
      BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        hXf_hSquarefree hXf_hUnit,
      BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        hXg_hSquarefree hXg_hUnit,
      ?_⟩
  · rw [show (X * f) * (X * g) = X ^ 2 * (f * g) by ring,
      map_mul, map_pow]
    exact fun hsquare =>
      hs.2.2.2.1
        ((isSquare_sq_mul_iff (i X) (i (f * g)) hiX).1 hsquare)
  · rw [show (X * f) * (X * g) * h =
        X ^ 2 * (f * g * h) by ring, map_mul, map_pow]
    exact fun hsquare =>
      hs.2.2.2.2.2.2
        ((isSquare_sq_mul_iff (i X) (i (f * g * h)) hiX).1
          hsquare)

/-- The two coset-correct component pullbacks and the reduced centered-norm
pullback have all seven nontrivial rational-function square classes.

For even `d`, the added powers of `X` are squares.  For odd `d`, one
residual `X` remains in each component; the preceding lemma treats their
shared factor without incorrectly asserting pairwise coprimality. -/
theorem orbitCosetSevenRadicandProducts_not_isSquare_ratFunc
    (h2 : (2 : K) ≠ 0)
    {a : Coefficients K} {xi alpha beta gamma k : K}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hobstruction : incidenceCenteredNormObstruction a xi ≠ 0)
    (halpha : alpha ≠ 0)
    (hproduct :
      alpha * beta = orderedTraceSigma a.a1 a.a2 a.a3 xi)
    (hgamma :
      gamma = orderedTraceGamma a.a1 a.a2 a.a3 xi)
    (hsquareProduct : alpha * beta = k ^ 2)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    let f := orbitComponentPlusCosetPulledRadicand alpha gamma k d
    let g := orbitComponentMinusCosetPulledRadicand alpha gamma k d
    let h := centeredNormReducedPulledRadicand a.a3 a.a1 d
    (¬ IsSquare (algebraMap K[X] (RatFunc K) f)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) g)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) h)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g))) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * h))) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (g * h))) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g * h))) := by
  dsimp only
  let f := orbitComponentPlusPulledRadicand alpha gamma k d
  let g := orbitComponentMinusPulledRadicand alpha gamma k d
  let h := centeredNormReducedPulledRadicand a.a3 a.a1 d
  have hsBase :
      (¬ IsSquare (algebraMap K[X] (RatFunc K) f)) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) g)) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) h)) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g))) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * h))) ∧
        (¬ IsSquare (algebraMap K[X] (RatFunc K) (g * h))) ∧
        (¬ IsSquare
          (algebraMap K[X] (RatFunc K) (f * g * h))) := by
    exact
      orbitComponentSevenRadicandProducts_not_isSquare_ratFunc
        h2 hA1 hA2 hA3 hmoving hregular hobstruction halpha
          hproduct hgamma hsquareProduct hd hdegree
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' d
  · let q : K[X] := X ^ m
    have hq : q ≠ 0 := pow_ne_zero m X_ne_zero
    have hsEven :=
      seven_not_isSquare_replace_first_two_by_square_mul
        hq hq hsBase
    have hpower : (X : K[X]) ^ d = q ^ 2 := by
      rw [hm, show 2 * m = m * 2 by omega, pow_mul]
    simpa only [orbitComponentPlusCosetPulledRadicand,
      orbitComponentMinusCosetPulledRadicand, f, g, h, hpower] using
      hsEven
  · have hfgh :=
      orbitComponentPulledRadicands_squarefree_and_isCoprime
        h2 hA2 hregular halpha hproduct hgamma hsquareProduct hd hdegree
    have hh :
        Squarefree h :=
      centeredNormReducedPulledRadicand_squarefree
        hA3 hA1 hmoving hd hdegree
    have hfCenter :
        IsCoprime f h ∧ IsCoprime g h :=
      orbitComponentPulledRadicands_isCoprime_centeredNormReducedPulledRadicand
        hregular hobstruction halpha hproduct hgamma hsquareProduct hd
    have hX :
        IsCoprime (X : K[X]) f ∧
          IsCoprime (X : K[X]) g ∧
          IsCoprime (X : K[X]) h := by
      simpa only [f, g, h] using
        isCoprime_X_orbitComponents_and_centeredNormReduced
          halpha a.a3 a.a1 hd
    have hsOdd :=
      seven_X_mul_first_two_not_isSquare_ratFunc
        hfgh.1 hfgh.2.1 hh hfgh.2.2
        hfCenter.1 hfCenter.2 hX.1 hX.2.1 hX.2.2
        (orbitComponentPlusPulledRadicand_not_isUnit
          halpha gamma k hd)
        (orbitComponentMinusPulledRadicand_not_isUnit
          halpha gamma k hd)
        (centeredNormReducedPulledRadicand_not_isUnit
          a.a3 a.a1 hd)
    let q : K[X] := X ^ m
    have hq : q ≠ 0 := pow_ne_zero m X_ne_zero
    have hsOddScaled :=
      seven_not_isSquare_replace_first_two_by_square_mul
        hq hq hsOdd
    have hpower : (X : K[X]) ^ d = q ^ 2 * X := by
      rw [hm, pow_succ, show 2 * m = m * 2 by omega, pow_mul]
    simpa only [orbitComponentPlusCosetPulledRadicand,
      orbitComponentMinusCosetPulledRadicand, f, g, h, hpower,
      mul_assoc] using hsOddScaled

/-- All seven coset-correct orbit/connecting products remain nonsquares
after extension to the algebraic closure.  The centered-norm polynomial is
the original pullback, with its forced square factor restored. -/
theorem
    orbitCosetSevenOriginalRadicandProducts_not_isSquare_algebraicClosure
    (h2 : (2 : K) ≠ 0)
    {a : Coefficients K} {xi alpha beta gamma k : K}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hobstruction : incidenceCenteredNormObstruction a xi ≠ 0)
    (halpha : alpha ≠ 0)
    (hproduct :
      alpha * beta = orderedTraceSigma a.a1 a.a2 a.a3 xi)
    (hgamma :
      gamma = orderedTraceGamma a.a1 a.a2 a.a3 xi)
    (hsquareProduct : alpha * beta = k ^ 2)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    let phi : K →+* AlgebraicClosure K :=
      algebraMap K (AlgebraicClosure K)
    let f :=
      (orbitComponentPlusCosetPulledRadicand alpha gamma k d).map phi
    let g :=
      (orbitComponentMinusCosetPulledRadicand alpha gamma k d).map phi
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
  have hregularE :
      OrderedTraceCandidateRegular
        aE.a1 aE.a2 aE.a3 (phi xi) := by
    simpa only [aE, MiddleGame.mapCoefficients_a1,
      MiddleGame.mapCoefficients_a2,
      MiddleGame.mapCoefficients_a3] using
      MiddleGame.orderedTraceCandidateRegular_map phi hphi hregular
  have hobstructionE :
      incidenceCenteredNormObstruction aE (phi xi) ≠ 0 := by
    rw [← map_incidenceCenteredNormObstruction phi a xi]
    exact (map_ne_zero_iff phi hphi).2 hobstruction
  have halphaE : phi alpha ≠ 0 :=
    (map_ne_zero_iff phi hphi).2 halpha
  have hproductE :
      phi alpha * phi beta =
        orderedTraceSigma aE.a1 aE.a2 aE.a3 (phi xi) := by
    have hmap := congrArg phi hproduct
    simpa only [map_mul, aE, MiddleGame.mapCoefficients_a1,
      MiddleGame.mapCoefficients_a2, MiddleGame.mapCoefficients_a3,
      map_orderedTraceSigma] using hmap
  have hgammaE :
      phi gamma =
        orderedTraceGamma aE.a1 aE.a2 aE.a3 (phi xi) := by
    have hmap := congrArg phi hgamma
    simpa only [aE, MiddleGame.mapCoefficients_a1,
      MiddleGame.mapCoefficients_a2, MiddleGame.mapCoefficients_a3,
      map_orderedTraceGamma] using hmap
  have hsquareProductE :
      phi alpha * phi beta = (phi k) ^ 2 := by
    have hmap := congrArg phi hsquareProduct
    simpa only [map_mul, map_pow] using hmap
  have hdegreeE : (d : AlgebraicClosure K) ≠ 0 := by
    have hdegreeMap : phi (d : K) ≠ 0 :=
      (map_ne_zero_iff phi hphi).2 hdegree
    simpa only [map_natCast] using hdegreeMap
  let fE :=
    orbitComponentPlusCosetPulledRadicand
      (phi alpha) (phi gamma) (phi k) d
  let gE :=
    orbitComponentMinusCosetPulledRadicand
      (phi alpha) (phi gamma) (phi k) d
  let rE :=
    centeredNormReducedPulledRadicand aE.a3 aE.a1 d
  let qE :=
    centeredNormForcedFactor aE.a3 aE.a1 d
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
    exact
      orbitCosetSevenRadicandProducts_not_isSquare_ratFunc
        h2E hA1E hA2E hA3E hmovingE hregularE hobstructionE
          halphaE hproductE hgammaE hsquareProductE hd hdegreeE
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
  simpa only [fE, gE, aE, phi,
    MiddleGame.mapCoefficients_a1, MiddleGame.mapCoefficients_a3,
    ← map_orbitComponentPlusCosetPulledRadicand,
    ← map_orbitComponentMinusCosetPulledRadicand,
    ← map_centeredNormPulledRadicand] using hsFull

/-- The orbit-correct seven hyperelliptic planes, with an arbitrary nonzero
scalar on the centered-norm equation, are absolutely irreducible. -/
theorem
    orbitConnectingSevenScaledHyperellipticPlanes_absolutelyIrreducible
    (h2 : (2 : K) ≠ 0)
    {a : Coefficients K}
    {xi alpha beta gamma k omegaInv : K}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hobstruction : incidenceCenteredNormObstruction a xi ≠ 0)
    (halpha : alpha ≠ 0)
    (hproduct :
      alpha * beta = orderedTraceSigma a.a1 a.a2 a.a3 xi)
    (hgamma :
      gamma = orderedTraceGamma a.a1 a.a2 a.a3 xi)
    (hsquareProduct : alpha * beta = k ^ 2)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0)
    (homegaInv : omegaInv ≠ 0) :
    let f :=
      orbitComponentPlusCosetPulledRadicand alpha gamma k d
    let g :=
      orbitComponentMinusCosetPulledRadicand alpha gamma k d
    let h :=
      C omegaInv * centeredNormPulledRadicand a.a3 a.a1 d
    SevenHyperellipticPlanesAbsolutelyIrreducible f g h := by
  dsimp only
  let phi : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  have homegaInvMap : phi omegaInv ≠ 0 :=
    (map_ne_zero_iff phi phi.injective).2 homegaInv
  obtain ⟨hf, hg, hh, hfg, hfh, hgh, hfgh⟩ :=
    orbitCosetSevenOriginalRadicandProducts_not_isSquare_algebraicClosure
      h2 hA1 hA2 hA3 hmoving hregular hobstruction halpha
        hproduct hgamma hsquareProduct hd hdegree
  have hhScaled :=
    not_isSquare_C_mul_of_not_isSquare_of_isAlgClosed
      homegaInvMap hh
  have hfhScaled :=
    not_isSquare_C_mul_of_not_isSquare_of_isAlgClosed
      homegaInvMap hfh
  have hghScaled :=
    not_isSquare_C_mul_of_not_isSquare_of_isAlgClosed
      homegaInvMap hgh
  have hfghScaled :=
    not_isSquare_C_mul_of_not_isSquare_of_isAlgClosed
      homegaInvMap hfgh
  unfold SevenHyperellipticPlanesAbsolutelyIrreducible
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply
      hyperellipticPlanePolynomial_absolutelyIrreducible_of_not_isSquare_map
    apply not_isSquare_fractionRing_of_not_isSquare_ratFunc
    simpa [map_mul, map_C, mul_assoc, mul_left_comm, mul_comm] using hf
  · apply
      hyperellipticPlanePolynomial_absolutelyIrreducible_of_not_isSquare_map
    apply not_isSquare_fractionRing_of_not_isSquare_ratFunc
    simpa [map_mul, map_C, mul_assoc, mul_left_comm, mul_comm] using hg
  · apply
      hyperellipticPlanePolynomial_absolutelyIrreducible_of_not_isSquare_map
    apply not_isSquare_fractionRing_of_not_isSquare_ratFunc
    simpa [map_mul, map_C, mul_assoc, mul_left_comm, mul_comm] using
      hhScaled
  · apply
      hyperellipticPlanePolynomial_absolutelyIrreducible_of_not_isSquare_map
    apply not_isSquare_fractionRing_of_not_isSquare_ratFunc
    simpa [map_mul, map_C, mul_assoc, mul_left_comm, mul_comm] using hfg
  · apply
      hyperellipticPlanePolynomial_absolutelyIrreducible_of_not_isSquare_map
    apply not_isSquare_fractionRing_of_not_isSquare_ratFunc
    simpa [map_mul, map_C, mul_assoc, mul_left_comm, mul_comm] using
      hfhScaled
  · apply
      hyperellipticPlanePolynomial_absolutelyIrreducible_of_not_isSquare_map
    apply not_isSquare_fractionRing_of_not_isSquare_ratFunc
    simpa [map_mul, map_C, mul_assoc, mul_left_comm, mul_comm] using
      hghScaled
  · apply
      hyperellipticPlanePolynomial_absolutelyIrreducible_of_not_isSquare_map
    apply not_isSquare_fractionRing_of_not_isSquare_ratFunc
    simpa [map_mul, map_C, mul_assoc, mul_left_comm, mul_comm] using
      hfghScaled

end

end GenMarkoff.General.Cage
