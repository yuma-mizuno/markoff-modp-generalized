import GenMarkoff.Symmetric.MiddleGame.ActualParameters
import BGS.Markoff.Core.RotationTorus

/-!
# Diagonalizing an actual symmetric affine fiber

The forward parametrization `fiberPoint` is useful in the middle game only
after one proves that it contains the point from which the one-step orbit
starts.  This module gives the inverse parameter explicitly.  In particular,
the initial parameter is not silently replaced by `1`; it is the translate
which later produces the weighted coset equation.
-/

namespace GenMarkoff.Symmetric.MiddleGame

noncomputable section

universe u

variable {K : Type u} [Field K]

theorem centeredFiberProduct_ne_zero_of_candidateRegular
    (c u t : K) (htrace : t = trace c u)
    (hregular : OrderedTraceCandidateRegular c c c t) :
    centeredFiberProduct c u t ≠ 0 := by
  intro hzero
  apply actualSigma_ne_zero_of_candidateRegular c u t htrace hregular
  simp [actualSigma, actualBeta, hzero]

/-- The coefficient of the `q`-eigenline in centered moving coordinates. -/
def actualFiberParameter
    (c u t : K) (q : Kˣ) (x : Point K) : K :=
  let m := fiberCenter c u t
  ((x.x3 - m) - (x.x2 - m) * ((q⁻¹ : Kˣ) : K)) /
    ((q : K) - ((q⁻¹ : Kˣ) : K))

/-- The coefficient of the inverse-eigenvalue line. -/
def actualFiberReciprocalParameter
    (c u t : K) (q : Kˣ) (x : Point K) : K :=
  let m := fiberCenter c u t
  ((x.x2 - m) * (q : K) - (x.x3 - m)) /
    ((q : K) - ((q⁻¹ : Kˣ) : K))

theorem actualFiber_eigenvalue_sub_inv_ne_zero
    (q : Kˣ) (hq : (q : K) ^ 2 ≠ 1) :
    (q : K) - ((q⁻¹ : Kˣ) : K) ≠ 0 := by
  intro hzero
  have hinv : (q : K) = ((q⁻¹ : Kˣ) : K) := sub_eq_zero.mp hzero
  apply hq
  rw [pow_two]
  calc
    (q : K) * (q : K) = ((q⁻¹ : Kˣ) : K) * (q : K) :=
      congrArg (fun z : K ↦ z * (q : K)) hinv
    _ = 1 := by simp

theorem actualFiber_eigenvalue_sq_ne_one_of_discriminant_ne_zero
    (t : K) (q : Kˣ)
    (htrace : t = BGS.Markoff.splitTorusTrace q)
    (hD : discriminant t ≠ 0) :
    (q : K) ^ 2 ≠ 1 := by
  intro hq
  have hinv : ((q⁻¹ : Kˣ) : K) = (q : K) := by
    apply mul_right_cancel₀ (Units.ne_zero q)
    simpa [pow_two] using hq.symm
  apply hD
  rw [htrace, BGS.Markoff.splitTorusTrace, hinv, discriminant]
  calc
    ((q : K) + (q : K)) ^ 2 - 4 =
        4 * ((q : K) ^ 2 - 1) := by ring
    _ = 0 := by rw [hq]; ring

theorem actualFiberParameter_add_reciprocal
    (c u t : K) (q : Kˣ) (x : Point K)
    (hq : (q : K) ^ 2 ≠ 1) :
    actualFiberParameter c u t q x +
        actualFiberReciprocalParameter c u t q x =
      x.x2 - fiberCenter c u t := by
  simp only [actualFiberParameter, actualFiberReciprocalParameter]
  rw [← add_div]
  rw [div_eq_iff (actualFiber_eigenvalue_sub_inv_ne_zero q hq)]
  ring

theorem actualFiberParameter_mul_add_reciprocal_mul_inv
    (c u t : K) (q : Kˣ) (x : Point K)
    (hq : (q : K) ^ 2 ≠ 1) :
    actualFiberParameter c u t q x * (q : K) +
        actualFiberReciprocalParameter c u t q x *
          ((q⁻¹ : Kˣ) : K) =
      x.x3 - fiberCenter c u t := by
  simp only [actualFiberParameter, actualFiberReciprocalParameter]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  rw [div_eq_iff (actualFiber_eigenvalue_sub_inv_ne_zero q hq)]
  field_simp [Units.ne_zero q]
  ring

theorem actualFiberParameter_mul_reciprocal_eq_centeredFiberProduct
    (c u t : K) (q : Kˣ) (x : Point K)
    (hx1 : x.x1 = u) (hx : IsSolution (coefficients c) x)
    (htraceCoordinate : t = trace c u)
    (htraceEigenvalue : t = BGS.Markoff.splitTorusTrace q)
    (hD : discriminant t ≠ 0) :
    actualFiberParameter c u t q x *
        actualFiberReciprocalParameter c u t q x =
      centeredFiberProduct c u t := by
  have ht : t ≠ 2 := ne_two_of_discriminant_ne_zero hD
  let m := fiberCenter c u t
  let Y := x.x2 - m
  let Z := x.x3 - m
  have hxPoint : (⟨u, Y + m, Z + m⟩ : Point K) = x := by
    ext
    · exact hx1.symm
    · simp [Y, m]
    · simp [Z, m]
  have hconic :
      Y ^ 2 + Z ^ 2 - t * Y * Z +
          u ^ 2 * (t + c ^ 2 - 2) / (t - 2) = 0 := by
    have hcentered :=
      polynomial_centered_fixed_first c u t Y Z htraceCoordinate ht
    rw [hxPoint] at hcentered
    rw [IsSolution] at hx
    rw [hx] at hcentered
    exact hcentered.symm
  have hq : (q : K) ^ 2 ≠ 1 := by
    exact actualFiber_eigenvalue_sq_ne_one_of_discriminant_ne_zero
      t q htraceEigenvalue hD
  have hdenomSq :
      ((q : K) - ((q⁻¹ : Kˣ) : K)) ^ 2 = discriminant t := by
    have hunit :
        (q : K) * ((q⁻¹ : Kˣ) : K) = 1 := by simp
    have htq :
        t = (q : K) + ((q⁻¹ : Kˣ) : K) := by
      simpa only [BGS.Markoff.splitTorusTrace] using htraceEigenvalue
    calc
      ((q : K) - ((q⁻¹ : Kˣ) : K)) ^ 2 =
          ((q : K) + ((q⁻¹ : Kˣ) : K)) ^ 2 -
            4 * ((q : K) * ((q⁻¹ : Kˣ) : K)) := by ring
      _ = ((q : K) + ((q⁻¹ : Kˣ) : K)) ^ 2 - 4 := by
        rw [hunit]
        ring
      _ = t ^ 2 - 4 := by rw [htq]
      _ = discriminant t := rfl
  have hnumerator :
      (Z - Y * ((q⁻¹ : Kˣ) : K)) *
          (Y * (q : K) - Z) =
        u ^ 2 * (t + c ^ 2 - 2) / (t - 2) := by
    have htq :
        t = (q : K) + ((q⁻¹ : Kˣ) : K) := by
      simpa only [BGS.Markoff.splitTorusTrace] using htraceEigenvalue
    have hinvUnit :
        ((q⁻¹ : Kˣ) : K) * (q : K) = 1 := by simp
    have hnegativeConic :
        t * Y * Z - Y ^ 2 - Z ^ 2 =
          u ^ 2 * (t + c ^ 2 - 2) / (t - 2) := by
      linear_combination -hconic
    calc
      (Z - Y * ((q⁻¹ : Kˣ) : K)) * (Y * (q : K) - Z) =
          ((q : K) + ((q⁻¹ : Kˣ) : K)) * Y * Z -
            Y ^ 2 * (((q⁻¹ : Kˣ) : K) * (q : K)) - Z ^ 2 := by
              ring
      _ = ((q : K) + ((q⁻¹ : Kˣ) : K)) * Y * Z -
            Y ^ 2 - Z ^ 2 := by rw [hinvUnit]; ring
      _ = t * Y * Z - Y ^ 2 - Z ^ 2 := by rw [htq]
      _ = u ^ 2 * (t + c ^ 2 - 2) / (t - 2) := hnegativeConic
  simp only [actualFiberParameter, actualFiberReciprocalParameter]
  rw [div_mul_div_comm, hnumerator, ← pow_two, hdenomSq]
  simp only [centeredFiberProduct]
  field_simp [hD, sub_ne_zero.mpr ht]

theorem actualFiberParameter_ne_zero
    (c u t : K) (q : Kˣ) (x : Point K)
    (hx1 : x.x1 = u) (hx : IsSolution (coefficients c) x)
    (htraceCoordinate : t = trace c u)
    (htraceEigenvalue : t = BGS.Markoff.splitTorusTrace q)
    (hD : discriminant t ≠ 0)
    (hproduct : centeredFiberProduct c u t ≠ 0) :
    actualFiberParameter c u t q x ≠ 0 := by
  intro hzero
  apply hproduct
  rw [← actualFiberParameter_mul_reciprocal_eq_centeredFiberProduct
    c u t q x hx1 hx htraceCoordinate htraceEigenvalue hD, hzero, zero_mul]

/-- Every nondegenerate point on a nonparabolic symmetric fiber is the
explicit torus point with its actual initial (coset) parameter. -/
theorem fiberPoint_actualFiberParameter_eq
    (c u t : K) (q : Kˣ) (x : Point K)
    (hx1 : x.x1 = u) (hx : IsSolution (coefficients c) x)
    (htraceCoordinate : t = trace c u)
    (htraceEigenvalue : t = BGS.Markoff.splitTorusTrace q)
    (hD : discriminant t ≠ 0)
    (hproduct : centeredFiberProduct c u t ≠ 0) :
    fiberPoint c u t q (actualFiberParameter c u t q x) = x := by
  have hq : (q : K) ^ 2 ≠ 1 := by
    exact actualFiber_eigenvalue_sq_ne_one_of_discriminant_ne_zero
      t q htraceEigenvalue hD
  let h := actualFiberParameter c u t q x
  let r := actualFiberReciprocalParameter c u t q x
  have hhr : h * r = centeredFiberProduct c u t :=
    actualFiberParameter_mul_reciprocal_eq_centeredFiberProduct
      c u t q x hx1 hx htraceCoordinate htraceEigenvalue hD
  have hh : h ≠ 0 :=
    actualFiberParameter_ne_zero c u t q x hx1 hx htraceCoordinate
      htraceEigenvalue hD hproduct
  have hdiv : centeredFiberProduct c u t / h = r := by
    rw [← hhr]
    field_simp [hh]
  apply Point.ext
  · exact hx1.symm
  · change h + centeredFiberProduct c u t / h + fiberCenter c u t = x.x2
    rw [hdiv]
    have hsum := actualFiberParameter_add_reciprocal c u t q x hq
    change h + r = x.x2 - fiberCenter c u t at hsum
    linear_combination hsum
  · change (q : K) * h +
        centeredFiberProduct c u t / ((q : K) * h) +
          fiberCenter c u t = x.x3
    rw [← hhr]
    have hrewrite : h * r / ((q : K) * h) =
        r * ((q⁻¹ : Kˣ) : K) := by
      simp only [Units.val_inv_eq_inv_val]
      field_simp [Units.ne_zero q, hh]
    rw [hrewrite]
    have hsum :=
      actualFiberParameter_mul_add_reciprocal_mul_inv c u t q x hq
    change h * (q : K) + r * ((q⁻¹ : Kˣ) : K) =
      x.x3 - fiberCenter c u t at hsum
    linear_combination hsum

/-- Package the actual nonzero initial parameter as a unit.  This is the
precise translated-coset datum consumed by the one-step middle game. -/
theorem exists_unit_fiberPoint_eq
    (c u t : K) (q : Kˣ) (x : Point K)
    (hx1 : x.x1 = u) (hx : IsSolution (coefficients c) x)
    (htraceCoordinate : t = trace c u)
    (htraceEigenvalue : t = BGS.Markoff.splitTorusTrace q)
    (hD : discriminant t ≠ 0)
    (hproduct : centeredFiberProduct c u t ≠ 0) :
    ∃ s : Kˣ, fiberPoint c u t (q : K) (s : K) = x := by
  have hs0 :
      actualFiberParameter c u t q x ≠ 0 :=
    actualFiberParameter_ne_zero c u t q x hx1 hx htraceCoordinate
      htraceEigenvalue hD hproduct
  let s : Kˣ := Units.mk0 (actualFiberParameter c u t q x) hs0
  refine ⟨s, ?_⟩
  simpa [s] using
    fiberPoint_actualFiberParameter_eq c u t q x hx1 hx htraceCoordinate
      htraceEigenvalue hD hproduct

end

end GenMarkoff.Symmetric.MiddleGame
