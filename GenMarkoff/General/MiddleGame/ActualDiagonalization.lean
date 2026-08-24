import GenMarkoff.General.MiddleGame.ActualParameters
import BGS.Markoff.Core.RotationTorus

/-!
# Diagonalizing an ordered general affine fiber

The forward map `fiberPair B C u t q h` parametrizes the ordered moving
coordinates on a nonparabolic fiber.  This module constructs its inverse
parameter explicitly.  The two moving coordinates have different affine
centers when `B ≠ C`; retaining their order is therefore essential.
-/

namespace GenMarkoff.General.MiddleGame

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- Candidate regularity forces the centered conic product to be nonzero. -/
theorem centeredFiberProduct_ne_zero_of_candidateRegular
    (s A B C u t : K)
    (htrace : t = orderedTrace s A u)
    (hregular : OrderedTraceCandidateRegular A B C t) :
    centeredFiberProduct B C u t ≠ 0 := by
  intro hzero
  apply actualSigma_ne_zero_of_candidateRegular
    s A B C u t htrace hregular
  simp [actualSigma, actualBeta, hzero]

/-- The coefficient of the `q`-eigenline in ordered centered coordinates. -/
def actualFiberParameter
    (B C u t : K) (q : Kˣ) (v : K × K) : K :=
  let m := fiberCenter B C u t
  ((v.2 - m.2) - (v.1 - m.1) * ((q⁻¹ : Kˣ) : K)) /
    ((q : K) - ((q⁻¹ : Kˣ) : K))

/-- The coefficient of the inverse-eigenvalue line in ordered centered
coordinates. -/
def actualFiberReciprocalParameter
    (B C u t : K) (q : Kˣ) (v : K × K) : K :=
  let m := fiberCenter B C u t
  ((v.1 - m.1) * (q : K) - (v.2 - m.2)) /
    ((q : K) - ((q⁻¹ : Kˣ) : K))

theorem actualFiber_eigenvalue_sub_inv_ne_zero
    (q : Kˣ) (hq : (q : K) ^ 2 ≠ 1) :
    (q : K) - ((q⁻¹ : Kˣ) : K) ≠ 0 := by
  intro hzero
  have hinv : (q : K) = ((q⁻¹ : Kˣ) : K) :=
    sub_eq_zero.mp hzero
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
    (B C u t : K) (q : Kˣ) (v : K × K)
    (hq : (q : K) ^ 2 ≠ 1) :
    actualFiberParameter B C u t q v +
        actualFiberReciprocalParameter B C u t q v =
      v.1 - (fiberCenter B C u t).1 := by
  simp only [actualFiberParameter, actualFiberReciprocalParameter]
  rw [← add_div]
  rw [div_eq_iff (actualFiber_eigenvalue_sub_inv_ne_zero q hq)]
  ring

theorem actualFiberParameter_mul_add_reciprocal_mul_inv
    (B C u t : K) (q : Kˣ) (v : K × K)
    (hq : (q : K) ^ 2 ≠ 1) :
    actualFiberParameter B C u t q v * (q : K) +
        actualFiberReciprocalParameter B C u t q v *
          ((q⁻¹ : Kˣ) : K) =
      v.2 - (fiberCenter B C u t).2 := by
  simp only [actualFiberParameter, actualFiberReciprocalParameter]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  rw [div_eq_iff (actualFiber_eigenvalue_sub_inv_ne_zero q hq)]
  field_simp [Units.ne_zero q]
  ring

/-- On the ordered affine conic, the two eigenline coefficients multiply to
the centered product parameter. -/
theorem actualFiberParameter_mul_reciprocal_eq_centeredFiberProduct
    (B C u t : K) (q : Kˣ) (v : K × K)
    (hv : fiberConic B C u t v.1 v.2 = 0)
    (htrace : t = BGS.Markoff.splitTorusTrace q)
    (hD : discriminant t ≠ 0) :
    actualFiberParameter B C u t q v *
        actualFiberReciprocalParameter B C u t q v =
      centeredFiberProduct B C u t := by
  let m := fiberCenter B C u t
  let Y := v.1 - m.1
  let Z := v.2 - m.2
  have hconic :
      Y ^ 2 + Z ^ 2 - t * Y * Z +
          u ^ 2 * centeredNorm B C t / discriminant t = 0 := by
    have hcentered := fiberConic_centered B C u t Y Z hD
    have hY : Y + (fiberCenter B C u t).1 = v.1 := by
      simp [Y, m]
    have hZ : Z + (fiberCenter B C u t).2 = v.2 := by
      simp [Z, m]
    rw [hY, hZ, hv] at hcentered
    exact hcentered.symm
  have hq : (q : K) ^ 2 ≠ 1 :=
    actualFiber_eigenvalue_sq_ne_one_of_discriminant_ne_zero
      t q htrace hD
  have hdenomSq :
      ((q : K) - ((q⁻¹ : Kˣ) : K)) ^ 2 = discriminant t := by
    have hunit :
        (q : K) * ((q⁻¹ : Kˣ) : K) = 1 := by simp
    have htq :
        t = (q : K) + ((q⁻¹ : Kˣ) : K) := by
      simpa only [BGS.Markoff.splitTorusTrace] using htrace
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
        u ^ 2 * centeredNorm B C t / discriminant t := by
    have htq :
        t = (q : K) + ((q⁻¹ : Kˣ) : K) := by
      simpa only [BGS.Markoff.splitTorusTrace] using htrace
    have hinvUnit :
        ((q⁻¹ : Kˣ) : K) * (q : K) = 1 := by simp
    have hnegativeConic :
        t * Y * Z - Y ^ 2 - Z ^ 2 =
          u ^ 2 * centeredNorm B C t / discriminant t := by
      linear_combination -hconic
    calc
      (Z - Y * ((q⁻¹ : Kˣ) : K)) * (Y * (q : K) - Z) =
          ((q : K) + ((q⁻¹ : Kˣ) : K)) * Y * Z -
            Y ^ 2 * (((q⁻¹ : Kˣ) : K) * (q : K)) - Z ^ 2 := by
              ring
      _ = ((q : K) + ((q⁻¹ : Kˣ) : K)) * Y * Z -
            Y ^ 2 - Z ^ 2 := by rw [hinvUnit]; ring
      _ = t * Y * Z - Y ^ 2 - Z ^ 2 := by rw [htq]
      _ = u ^ 2 * centeredNorm B C t / discriminant t :=
        hnegativeConic
  simp only [actualFiberParameter, actualFiberReciprocalParameter]
  rw [div_mul_div_comm, hnumerator, ← pow_two, hdenomSq]
  simp only [centeredFiberProduct]
  field_simp [hD]

theorem actualFiberParameter_ne_zero
    (B C u t : K) (q : Kˣ) (v : K × K)
    (hv : fiberConic B C u t v.1 v.2 = 0)
    (htrace : t = BGS.Markoff.splitTorusTrace q)
    (hD : discriminant t ≠ 0)
    (hproduct : centeredFiberProduct B C u t ≠ 0) :
    actualFiberParameter B C u t q v ≠ 0 := by
  intro hzero
  apply hproduct
  rw [← actualFiberParameter_mul_reciprocal_eq_centeredFiberProduct
    B C u t q v hv htrace hD, hzero, zero_mul]

/-- Every regular point on a nonparabolic ordered affine conic is the
explicit torus pair with its actual initial parameter. -/
theorem fiberPair_actualFiberParameter_eq
    (B C u t : K) (q : Kˣ) (v : K × K)
    (hv : fiberConic B C u t v.1 v.2 = 0)
    (htrace : t = BGS.Markoff.splitTorusTrace q)
    (hD : discriminant t ≠ 0)
    (hproduct : centeredFiberProduct B C u t ≠ 0) :
    fiberPair B C u t (q : K)
        (actualFiberParameter B C u t q v) = v := by
  have hq : (q : K) ^ 2 ≠ 1 :=
    actualFiber_eigenvalue_sq_ne_one_of_discriminant_ne_zero
      t q htrace hD
  let h := actualFiberParameter B C u t q v
  let r := actualFiberReciprocalParameter B C u t q v
  have hhr : h * r = centeredFiberProduct B C u t :=
    actualFiberParameter_mul_reciprocal_eq_centeredFiberProduct
      B C u t q v hv htrace hD
  have hh : h ≠ 0 :=
    actualFiberParameter_ne_zero
      B C u t q v hv htrace hD hproduct
  have hdiv : centeredFiberProduct B C u t / h = r := by
    rw [← hhr]
    field_simp [hh]
  apply Prod.ext
  · change
      h + centeredFiberProduct B C u t / h +
          (fiberCenter B C u t).1 = v.1
    rw [hdiv]
    have hsum :=
      actualFiberParameter_add_reciprocal B C u t q v hq
    change h + r = v.1 - (fiberCenter B C u t).1 at hsum
    linear_combination hsum
  · change
      (q : K) * h +
          centeredFiberProduct B C u t / ((q : K) * h) +
          (fiberCenter B C u t).2 = v.2
    rw [← hhr]
    have hrewrite :
        h * r / ((q : K) * h) =
          r * ((q⁻¹ : Kˣ) : K) := by
      simp only [Units.val_inv_eq_inv_val]
      field_simp [Units.ne_zero q, hh]
    rw [hrewrite]
    have hsum :=
      actualFiberParameter_mul_add_reciprocal_mul_inv
        B C u t q v hq
    change
      h * (q : K) + r * ((q⁻¹ : Kˣ) : K) =
        v.2 - (fiberCenter B C u t).2 at hsum
    linear_combination hsum

/-- Package the explicit nonzero initial parameter as a unit. -/
theorem exists_unit_fiberPair_eq
    (B C u t : K) (q : Kˣ) (v : K × K)
    (hv : fiberConic B C u t v.1 v.2 = 0)
    (htrace : t = BGS.Markoff.splitTorusTrace q)
    (hD : discriminant t ≠ 0)
    (hproduct : centeredFiberProduct B C u t ≠ 0) :
    ∃ h : Kˣ, fiberPair B C u t (q : K) (h : K) = v := by
  have hh :
      actualFiberParameter B C u t q v ≠ 0 :=
    actualFiberParameter_ne_zero
      B C u t q v hv htrace hD hproduct
  let h : Kˣ := Units.mk0 (actualFiberParameter B C u t q v) hh
  refine ⟨h, ?_⟩
  simpa [h] using
    fiberPair_actualFiberParameter_eq
      B C u t q v hv htrace hD hproduct

/-- Candidate regularity supplies the nonzero product needed by the ordered
inverse parametrization. -/
theorem exists_unit_fiberPair_eq_of_candidateRegular
    (s A B C u t : K) (q : Kˣ) (v : K × K)
    (hv : fiberConic B C u t v.1 v.2 = 0)
    (hcoordinate : t = orderedTrace s A u)
    (htrace : t = BGS.Markoff.splitTorusTrace q)
    (hregular : OrderedTraceCandidateRegular A B C t) :
    ∃ h : Kˣ, fiberPair B C u t (q : K) (h : K) = v := by
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  exact exists_unit_fiberPair_eq
    B C u t q v hv htrace hD
      (centeredFiberProduct_ne_zero_of_candidateRegular
        s A B C u t hcoordinate hregular)

end

end GenMarkoff.General.MiddleGame
