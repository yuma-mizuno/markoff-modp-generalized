import GenMarkoff.Symmetric.Opening.RotationBridge
import GenMarkoff.Symmetric.ExceptionalRouting
import GenMarkoff.Symmetric.OneStepParabolic
import BGS.Markoff.Opening.PeriodicSemisimple

/-!
# Periodic semisimple affine half-steps

Centering conjugates a nonparabolic affine half-step to the pinned BGS
matrix `rho(t)`.  A periodic nonzero centered vector has a nonzero coordinate
in the two eigenlines, so the corresponding eigenvalue is torsion.  The
explicit non-centered hypothesis records the only point-level obstruction;
it is not hidden inside a matrix-order assertion.
-/

namespace GenMarkoff.Symmetric.Opening

universe u

variable {K : Type u} [Field K]

/-- First coordinate in the eigenbasis of `rho(w+w⁻¹)`. -/
def firstEigenCoordinate (w : Kˣ) (v : K × K) : K :=
  (v.2 - v.1 * ((w⁻¹ : Kˣ) : K)) /
    ((w : K) - ((w⁻¹ : Kˣ) : K))

/-- Second coordinate in the eigenbasis of `rho(w+w⁻¹)`. -/
def secondEigenCoordinate (w : Kˣ) (v : K × K) : K :=
  (v.1 * (w : K) - v.2) /
    ((w : K) - ((w⁻¹ : Kˣ) : K))

private theorem eigenvalue_sub_inv_ne_zero
    (w : Kˣ) (hw : (w : K) ^ 2 ≠ 1) :
    (w : K) - ((w⁻¹ : Kˣ) : K) ≠ 0 := by
  intro hzero
  have hinv : (w : K) = ((w⁻¹ : Kˣ) : K) := sub_eq_zero.mp hzero
  apply hw
  rw [pow_two]
  calc
    (w : K) * (w : K) = ((w⁻¹ : Kˣ) : K) * (w : K) :=
      congrArg (fun z : K ↦ z * (w : K)) hinv
    _ = 1 := by simp

theorem first_add_secondEigenCoordinate
    (w : Kˣ) (hw : (w : K) ^ 2 ≠ 1) (v : K × K) :
    firstEigenCoordinate w v + secondEigenCoordinate w v = v.1 := by
  simp only [firstEigenCoordinate, secondEigenCoordinate]
  rw [← add_div]
  rw [div_eq_iff (eigenvalue_sub_inv_ne_zero w hw)]
  ring

theorem first_mul_add_second_mul_invEigenCoordinate
    (w : Kˣ) (hw : (w : K) ^ 2 ≠ 1) (v : K × K) :
    firstEigenCoordinate w v * (w : K) +
        secondEigenCoordinate w v * ((w⁻¹ : Kˣ) : K) = v.2 := by
  simp only [firstEigenCoordinate, secondEigenCoordinate]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  rw [div_eq_iff (eigenvalue_sub_inv_ne_zero w hw)]
  ring

theorem firstEigenCoordinate_linearStep
    (w : Kˣ) (hw : (w : K) ^ 2 ≠ 1) (v : K × K) :
    firstEigenCoordinate w
        (linearStep (BGS.Markoff.splitTorusTrace w) v) =
      firstEigenCoordinate w v * (w : K) := by
  simp only [firstEigenCoordinate, linearStep, BGS.Markoff.splitTorusTrace]
  rw [div_mul_eq_mul_div]
  rw [div_left_inj' (eigenvalue_sub_inv_ne_zero w hw)]
  field_simp [Units.ne_zero w]
  ring_nf
  rw [show (w : K) * ((w⁻¹ : Kˣ) : K) = 1 by simp]
  ring

theorem secondEigenCoordinate_linearStep
    (w : Kˣ) (hw : (w : K) ^ 2 ≠ 1) (v : K × K) :
    secondEigenCoordinate w
        (linearStep (BGS.Markoff.splitTorusTrace w) v) =
      secondEigenCoordinate w v * ((w⁻¹ : Kˣ) : K) := by
  simp only [secondEigenCoordinate, linearStep, BGS.Markoff.splitTorusTrace]
  rw [div_mul_eq_mul_div]
  rw [div_left_inj' (eigenvalue_sub_inv_ne_zero w hw)]
  field_simp [Units.ne_zero w]
  ring_nf
  rw [show (w : K) * ((w⁻¹ : Kˣ) : K) = 1 by simp]
  ring

theorem firstEigenCoordinate_iterate_linearStep
    (w : Kˣ) (hw : (w : K) ^ 2 ≠ 1) (v : K × K) (n : ℕ) :
    firstEigenCoordinate w
        (((linearStep (BGS.Markoff.splitTorusTrace w))^[n]) v) =
      firstEigenCoordinate w v * (w : K) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', firstEigenCoordinate_linearStep w hw, ih,
        pow_succ]
      ring

theorem secondEigenCoordinate_iterate_linearStep
    (w : Kˣ) (hw : (w : K) ^ 2 ≠ 1) (v : K × K) (n : ℕ) :
    secondEigenCoordinate w
        (((linearStep (BGS.Markoff.splitTorusTrace w))^[n]) v) =
      secondEigenCoordinate w v * ((w⁻¹ : Kˣ) : K) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', secondEigenCoordinate_linearStep w hw, ih,
        pow_succ]
      ring

private theorem eigenCoordinate_ne_zero
    (w : Kˣ) (hw : (w : K) ^ 2 ≠ 1) {v : K × K}
    (hv : v ≠ (0, 0)) :
    firstEigenCoordinate w v ≠ 0 ∨ secondEigenCoordinate w v ≠ 0 := by
  by_contra h
  push Not at h
  rcases h with ⟨hfirst, hsecond⟩
  apply hv
  apply Prod.ext
  · have hsum := first_add_secondEigenCoordinate w hw v
    simpa [hfirst, hsecond] using hsum.symm
  · have hsum := first_mul_add_second_mul_invEigenCoordinate w hw v
    simpa [hfirst, hsecond] using hsum.symm

private theorem eigenvalue_nonparabolic
    (t : K) (w : Kˣ) (htrace : t = BGS.Markoff.splitTorusTrace w)
    (ht : t ^ 2 ≠ 4) :
    (w : K) ^ 2 ≠ 1 := by
  intro hw
  have hinv : ((w⁻¹ : Kˣ) : K) = (w : K) := by
    apply mul_right_cancel₀ (Units.ne_zero w)
    simpa [pow_two] using hw.symm
  apply ht
  rw [htrace, BGS.Markoff.splitTorusTrace, hinv]
  calc
    ((w : K) + (w : K)) ^ 2 = 4 * (w : K) ^ 2 := by ring
    _ = 4 := by rw [hw]; ring

/-- A positive return of a nonzero vector under a nonparabolic BGS rotation
forces a torsion eigenvalue representing the trace. -/
theorem periodic_linearStep_has_torsion_eigenvalue
    [IsAlgClosed K] (t : K) (v : K × K) (ht : t ^ 2 ≠ 4)
    (hv : v ≠ (0, 0)) (n : ℕ) (hn : 0 < n)
    (hperiodic : ((linearStep t)^[n]) v = v) :
    ∃ w : Kˣ, IsOfFinOrder w ∧ t = BGS.Markoff.splitTorusTrace w := by
  obtain ⟨w, htrace⟩ := BGS.Markoff.exists_splitTorusTrace_eq t
  have hw : (w : K) ^ 2 ≠ 1 := eigenvalue_nonparabolic t w htrace ht
  have hperiodic' :
      ((linearStep (BGS.Markoff.splitTorusTrace w))^[n]) v = v := by
    rwa [← htrace]
  rcases eigenCoordinate_ne_zero w hw hv with hfirst | hsecond
  · have heq := congrArg (firstEigenCoordinate w) hperiodic'
    rw [firstEigenCoordinate_iterate_linearStep w hw] at heq
    have hpow : (w : K) ^ n = 1 := by
      apply mul_left_cancel₀ hfirst
      simpa using heq
    refine ⟨w, ?_, htrace⟩
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨n, hn, ?_⟩
    apply Units.ext
    exact hpow
  · have heq := congrArg (secondEigenCoordinate w) hperiodic'
    rw [secondEigenCoordinate_iterate_linearStep w hw] at heq
    have hpowInv : ((w⁻¹ : Kˣ) : K) ^ n = 1 := by
      apply mul_left_cancel₀ hsecond
      simpa using heq
    have hpowInvUnits : (w⁻¹ : Kˣ) ^ n = 1 := by
      apply Units.ext
      exact hpowInv
    have hpowUnits : w ^ n = 1 := by
      have := congrArg Inv.inv hpowInvUnits
      simpa using this
    refine ⟨w, ?_, htrace⟩
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, hn, hpowUnits⟩

theorem centerCoordinates_iterate_affineStep
    (c u t : K) (v : K × K) (ht : t ≠ 2) (n : ℕ) :
    centerCoordinates (fiberCenter c u t) (((affineStep c u t)^[n]) v) =
      ((linearStep t)^[n]) (centerCoordinates (fiberCenter c u t) v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        centerCoordinates_affineStep c u t _ ht, ih]

/-- Candidate regularity removes the affine-center fixed-point obstruction on
the first-coordinate fiber. -/
theorem centeredMovingCoordinates1_ne_zero_of_candidateRegular
    (c : K) (x : Point K) (hx : IsSolution (coefficients c) x)
    (hregular : OrderedTraceCandidateRegular c c c (trace c x.x1)) :
    centerCoordinates (fiberCenter c x.x1 (trace c x.x1))
        (movingCoordinates1 x) ≠ (0, 0) := by
  let t := trace c x.x1
  have hD : t ^ 2 - 4 ≠ 0 := by
    simpa [t] using hregular.1
  have htTwo : t ≠ 2 := by
    intro ht
    apply hD
    rw [ht]
    norm_num
  have htC : t + c ≠ 0 := by
    simpa [t] using hregular.2.1
  have hcenterEval :
      Polynomial.eval t (orderedTraceCenteredNormPolynomial c c) ≠ 0 := by
    simpa [t] using hregular.2.2.1
  have hcenterFactor : (t + 2) * (t + c ^ 2 - 2) ≠ 0 := by
    rwa [eval_orderedTraceCenteredNormPolynomial_symmetric] at hcenterEval
  have hcenterTerm : t + c ^ 2 - 2 ≠ 0 := (mul_ne_zero_iff.mp hcenterFactor).2
  intro hzero
  have hx2 : x.x2 = fiberCenter c x.x1 t := by
    have hfirst := congrArg Prod.fst hzero
    simpa [centerCoordinates, movingCoordinates1, t] using sub_eq_zero.mp hfirst
  have hx3 : x.x3 = fiberCenter c x.x1 t := by
    have hsecond := congrArg Prod.snd hzero
    simpa [centerCoordinates, movingCoordinates1, t] using sub_eq_zero.mp hsecond
  have hcentered := polynomial_centered_fixed_first
    c x.x1 t 0 0 rfl htTwo
  have hpolyZero :
      polynomial (coefficients c)
        ⟨x.x1, 0 + fiberCenter c x.x1 t,
          0 + fiberCenter c x.x1 t⟩ = 0 := by
    simpa only [zero_add] using (show polynomial (coefficients c)
        ⟨x.x1, fiberCenter c x.x1 t, fiberCenter c x.x1 t⟩ = 0 by
      have hpoint :
          (⟨x.x1, fiberCenter c x.x1 t,
            fiberCenter c x.x1 t⟩ : Point K) = x := by
        apply Point.ext
        · rfl
        · exact hx2.symm
        · exact hx3.symm
      rw [hpoint]
      exact hx)
  have hconstant : x.x1 ^ 2 * (t + c ^ 2 - 2) / (t - 2) = 0 := by
    calc
      x.x1 ^ 2 * (t + c ^ 2 - 2) / (t - 2) =
          polynomial (coefficients c)
            ⟨x.x1, 0 + fiberCenter c x.x1 t,
              0 + fiberCenter c x.x1 t⟩ := by
            simpa using hcentered.symm
      _ = 0 := hpolyZero
  have hden : t - 2 ≠ 0 := sub_ne_zero.mpr htTwo
  have hnumerator : x.x1 ^ 2 * (t + c ^ 2 - 2) = 0 :=
    (div_eq_zero_iff).mp hconstant |>.resolve_right hden
  have hx1sq : x.x1 ^ 2 = 0 :=
    (mul_eq_zero.mp hnumerator).resolve_right hcenterTerm
  have hx1 : x.x1 = 0 := sq_eq_zero_iff.mp hx1sq
  apply htC
  simp [t, trace, hx1]

/-- Point-level semisimple opening kernel for the symmetric affine half-step.
The centered vector is stated explicitly because the affine center can be a
fixed point even when the ambient matrix has infinite order. -/
theorem periodic_affineStep_has_torsion_eigenvalue
    [IsAlgClosed K] (c u t : K) (v : K × K)
    (htTwo : t ≠ 2) (ht : t ^ 2 ≠ 4)
    (hv : centerCoordinates (fiberCenter c u t) v ≠ (0, 0))
    (n : ℕ) (hn : 0 < n)
    (hperiodic : ((affineStep c u t)^[n]) v = v) :
    ∃ w : Kˣ, IsOfFinOrder w ∧ t = BGS.Markoff.splitTorusTrace w := by
  apply periodic_linearStep_has_torsion_eigenvalue t
    (centerCoordinates (fiberCenter c u t) v) ht hv n hn
  have h := congrArg (centerCoordinates (fiberCenter c u t)) hperiodic
  rwa [centerCoordinates_iterate_affineStep c u t v htTwo] at h

/-- A positive return of the first one-step generator at a candidate-regular
surface point produces a torsion eigenvalue for its actual trace. -/
theorem periodic_oneStep1_candidateRegular_has_torsion_eigenvalue
    [IsAlgClosed K] (c : K) (x : Point K)
    (hx : IsSolution (coefficients c) x)
    (hregular : OrderedTraceCandidateRegular c c c (trace c x.x1))
    (n : ℕ) (hn : 0 < n)
    (hperiodic : ((oneStep1 c)^[n]) x = x) :
    ∃ w : Kˣ, IsOfFinOrder w ∧
      trace c x.x1 = BGS.Markoff.splitTorusTrace w := by
  let t := trace c x.x1
  have hD : t ^ 2 ≠ 4 := by
    apply sub_ne_zero.mp
    simpa [t] using hregular.1
  have htTwo : t ≠ 2 := by
    intro ht
    apply hD
    rw [ht]
    norm_num
  have hv : centerCoordinates (fiberCenter c x.x1 t)
      (movingCoordinates1 x) ≠ (0, 0) := by
    simpa [t] using
      centeredMovingCoordinates1_ne_zero_of_candidateRegular c x hx hregular
  have hpair :
      ((affineStep c x.x1 t)^[n]) (movingCoordinates1 x) =
        movingCoordinates1 x := by
    have h := congrArg movingCoordinates1 hperiodic
    rw [movingCoordinates1_iterate_oneStep1] at h
    simpa [fiberStep, t] using h
  exact periodic_affineStep_has_torsion_eigenvalue
    c x.x1 t (movingCoordinates1 x) htTwo hD hv n hn hpair

/-- Cyclic second-axis form of the candidate-regular periodicity theorem. -/
theorem periodic_oneStep2_candidateRegular_has_torsion_eigenvalue
    [IsAlgClosed K] (c : K) (x : Point K)
    (hx : IsSolution (coefficients c) x)
    (hregular : OrderedTraceCandidateRegular c c c (trace c x.x2))
    (n : ℕ) (hn : 0 < n)
    (hperiodic : ((oneStep2 c)^[n]) x = x) :
    ∃ w : Kˣ, IsOfFinOrder w ∧
      trace c x.x2 = BGS.Markoff.splitTorusTrace w := by
  have hsolution : IsSolution (coefficients c) (cycleLeftEquiv x) :=
    (isSolution_cycleLeftEquiv c x).2 hx
  have hregular' :
      OrderedTraceCandidateRegular c c c
        (trace c (cycleLeftEquiv x).x1) := by
    simpa [cycleLeftEquiv] using hregular
  have hperiodic' : ((oneStep1 c)^[n]) (cycleLeftEquiv x) =
      cycleLeftEquiv x := by
    rw [← cycleLeftEquiv_iterate_oneStep2 n c x, hperiodic]
  simpa [cycleLeftEquiv] using
    periodic_oneStep1_candidateRegular_has_torsion_eigenvalue
      c (cycleLeftEquiv x) hsolution hregular' n hn hperiodic'

/-- Cyclic third-axis form of the candidate-regular periodicity theorem. -/
theorem periodic_oneStep3_candidateRegular_has_torsion_eigenvalue
    [IsAlgClosed K] (c : K) (x : Point K)
    (hx : IsSolution (coefficients c) x)
    (hregular : OrderedTraceCandidateRegular c c c (trace c x.x3))
    (n : ℕ) (hn : 0 < n)
    (hperiodic : ((oneStep3 c)^[n]) x = x) :
    ∃ w : Kˣ, IsOfFinOrder w ∧
      trace c x.x3 = BGS.Markoff.splitTorusTrace w := by
  have hsolution : IsSolution (coefficients c) (cycleRightEquiv x) :=
    (isSolution_cycleRightEquiv c x).2 hx
  have hregular' :
      OrderedTraceCandidateRegular c c c
        (trace c (cycleRightEquiv x).x1) := by
    simpa [cycleRightEquiv, cycleLeftEquiv] using hregular
  have hperiodic' : ((oneStep1 c)^[n]) (cycleRightEquiv x) =
      cycleRightEquiv x := by
    rw [← cycleRightEquiv_iterate_oneStep3 n c x, hperiodic]
  simpa [cycleRightEquiv, cycleLeftEquiv] using
    periodic_oneStep1_candidateRegular_has_torsion_eigenvalue
      c (cycleRightEquiv x) hsolution hregular' n hn hperiodic'

end GenMarkoff.Symmetric.Opening
