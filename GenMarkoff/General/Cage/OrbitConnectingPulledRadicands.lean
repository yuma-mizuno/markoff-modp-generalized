import GenMarkoff.General.Cage.OrbitCosetBiquadratic
import GenMarkoff.General.Cage.ConnectingPulledRadicands

/-!
# Pulled radicands for an orbit connecting coset

For a split-torus power trace

`T = t^d + t⁻ᵈ`,

this file clears the reciprocal denominators in the orbit discriminant

`(T - gamma)^2 - 4 * alpha * beta`

and in the two component factors

`alpha * ((T - gamma) + 2 * k)`,
`alpha * ((T - gamma) - 2 * k)`.

The resulting reciprocal polynomials have degrees at most `4d`, `2d`, and
`2d`.  When `d > 0` these bounds are sharp (for the component factors one
also assumes `alpha ≠ 0`).
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff Polynomial

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- The component radicand with the sign opposite to
`orbitComponentRadicand`. -/
def orbitOppositeComponentRadicand
    (alpha k U : K) : K :=
  alpha * (U - 2 * k)

/-- Reciprocal quartic obtained by clearing the denominator in the orbit
discriminant at `T = u + u⁻¹`. -/
def orbitDiscriminantReciprocalQuartic
    (alpha beta gamma u : K) : K :=
  u ^ 4 +
    (-2 * gamma) * u ^ 3 +
    (gamma ^ 2 + 2 - 4 * alpha * beta) * u ^ 2 +
    (-2 * gamma) * u +
    1

/-- Reciprocal quadratic for
`alpha * ((T - gamma) + 2 * k)`. -/
def orbitComponentPlusReciprocalQuadratic
    (alpha gamma k u : K) : K :=
  alpha * u ^ 2 +
    (alpha * (2 * k - gamma)) * u +
    alpha

/-- Reciprocal quadratic for
`alpha * ((T - gamma) - 2 * k)`. -/
def orbitComponentMinusReciprocalQuadratic
    (alpha gamma k u : K) : K :=
  alpha * u ^ 2 +
    (alpha * (-2 * k - gamma)) * u +
    alpha

/-- Pullback of the orbit discriminant along `u = t^d`. -/
def orbitDiscriminantPulledRadicand
    (alpha beta gamma : K) (d : ℕ) : K[X] :=
  X ^ (4 * d) +
    C (-2 * gamma) * X ^ (3 * d) +
    C (gamma ^ 2 + 2 - 4 * alpha * beta) * X ^ (2 * d) +
    C (-2 * gamma) * X ^ d +
    1

/-- Pullback of the positive component factor along `u = t^d`. -/
def orbitComponentPlusPulledRadicand
    (alpha gamma k : K) (d : ℕ) : K[X] :=
  C alpha * X ^ (2 * d) +
    C (alpha * (2 * k - gamma)) * X ^ d +
    C alpha

/-- Pullback of the negative component factor along `u = t^d`. -/
def orbitComponentMinusPulledRadicand
    (alpha gamma k : K) (d : ℕ) : K[X] :=
  C alpha * X ^ (2 * d) +
    C (alpha * (-2 * k - gamma)) * X ^ d +
    C alpha

@[simp]
theorem eval_orbitDiscriminantPulledRadicand
    (alpha beta gamma t : K) (d : ℕ) :
    eval t (orbitDiscriminantPulledRadicand alpha beta gamma d) =
      orbitDiscriminantReciprocalQuartic
        alpha beta gamma (t ^ d) := by
  simp only [orbitDiscriminantPulledRadicand,
    orbitDiscriminantReciprocalQuartic, eval_add, eval_mul, eval_C,
    eval_pow, eval_X, eval_one]
  simp only [← pow_mul]
  ring

@[simp]
theorem eval_orbitComponentPlusPulledRadicand
    (alpha gamma k t : K) (d : ℕ) :
    eval t (orbitComponentPlusPulledRadicand alpha gamma k d) =
      orbitComponentPlusReciprocalQuadratic
        alpha gamma k (t ^ d) := by
  simp only [orbitComponentPlusPulledRadicand,
    orbitComponentPlusReciprocalQuadratic, eval_add, eval_mul, eval_C,
    eval_pow, eval_X]
  simp only [← pow_mul]
  ring

@[simp]
theorem eval_orbitComponentMinusPulledRadicand
    (alpha gamma k t : K) (d : ℕ) :
    eval t (orbitComponentMinusPulledRadicand alpha gamma k d) =
      orbitComponentMinusReciprocalQuadratic
        alpha gamma k (t ^ d) := by
  simp only [orbitComponentMinusPulledRadicand,
    orbitComponentMinusReciprocalQuadratic, eval_add, eval_mul, eval_C,
    eval_pow, eval_X]
  simp only [← pow_mul]
  ring

/-- The reciprocal quartic is the denominator-cleared orbit
discriminant. -/
theorem orbitDiscriminantReciprocalQuartic_eq_mul_discriminant
    (alpha beta gamma u : K) (hu : u ≠ 0) :
    orbitDiscriminantReciprocalQuartic alpha beta gamma u =
      u ^ 2 *
        weightedOrbitDiscriminant alpha beta (u + u⁻¹ - gamma) := by
  simp only [orbitDiscriminantReciprocalQuartic,
    weightedOrbitDiscriminant]
  field_simp [hu]
  ring

/-- The positive reciprocal quadratic is its denominator-cleared component
factor. -/
theorem orbitComponentPlusReciprocalQuadratic_eq_mul_component
    (alpha gamma k u : K) (hu : u ≠ 0) :
    orbitComponentPlusReciprocalQuadratic alpha gamma k u =
      u * orbitComponentRadicand alpha k (u + u⁻¹ - gamma) := by
  simp only [orbitComponentPlusReciprocalQuadratic,
    orbitComponentRadicand]
  field_simp [hu]
  ring

/-- The negative reciprocal quadratic is its denominator-cleared component
factor. -/
theorem orbitComponentMinusReciprocalQuadratic_eq_mul_component
    (alpha gamma k u : K) (hu : u ≠ 0) :
    orbitComponentMinusReciprocalQuadratic alpha gamma k u =
      u * orbitOppositeComponentRadicand
        alpha k (u + u⁻¹ - gamma) := by
  simp only [orbitComponentMinusReciprocalQuadratic,
    orbitOppositeComponentRadicand]
  field_simp [hu]
  ring

/-- Exact orbit-discriminant evaluation at a unit power parameter. -/
theorem eval_orbitDiscriminantPulledRadicand_unit
    (alpha beta gamma : K) (t : Kˣ) (d : ℕ) :
    eval (t : K)
        (orbitDiscriminantPulledRadicand alpha beta gamma d) =
      ((t : K) ^ d) ^ 2 *
        weightedOrbitDiscriminant alpha beta
          (splitTorusTrace (t ^ d) - gamma) := by
  rw [eval_orbitDiscriminantPulledRadicand,
    orbitDiscriminantReciprocalQuartic_eq_mul_discriminant
      alpha beta gamma ((t : K) ^ d)
        (pow_ne_zero d t.ne_zero)]
  congr 2
  simp [splitTorusTrace]

/-- Exact positive-component evaluation at a unit power parameter. -/
theorem eval_orbitComponentPlusPulledRadicand_unit
    (alpha gamma k : K) (t : Kˣ) (d : ℕ) :
    eval (t : K)
        (orbitComponentPlusPulledRadicand alpha gamma k d) =
      (t : K) ^ d *
        orbitComponentRadicand alpha k
          (splitTorusTrace (t ^ d) - gamma) := by
  rw [eval_orbitComponentPlusPulledRadicand,
    orbitComponentPlusReciprocalQuadratic_eq_mul_component
      alpha gamma k ((t : K) ^ d)
        (pow_ne_zero d t.ne_zero)]
  congr 2
  simp [splitTorusTrace]

/-- Exact negative-component evaluation at a unit power parameter. -/
theorem eval_orbitComponentMinusPulledRadicand_unit
    (alpha gamma k : K) (t : Kˣ) (d : ℕ) :
    eval (t : K)
        (orbitComponentMinusPulledRadicand alpha gamma k d) =
      (t : K) ^ d *
        orbitOppositeComponentRadicand alpha k
          (splitTorusTrace (t ^ d) - gamma) := by
  rw [eval_orbitComponentMinusPulledRadicand,
    orbitComponentMinusReciprocalQuadratic_eq_mul_component
      alpha gamma k ((t : K) ^ d)
        (pow_ne_zero d t.ne_zero)]
  congr 2
  simp [splitTorusTrace]

/-- When `alpha * beta = k²`, the two pulled component factors multiply to
`alpha²` times the pulled orbit discriminant. -/
theorem orbitComponentPulledRadicands_mul_eq_discriminant
    (alpha beta gamma k : K) (d : ℕ)
    (hproduct : alpha * beta = k ^ 2) :
    orbitComponentPlusPulledRadicand alpha gamma k d *
        orbitComponentMinusPulledRadicand alpha gamma k d =
      C (alpha ^ 2) *
        orbitDiscriminantPulledRadicand alpha beta gamma d := by
  simp only [orbitComponentPlusPulledRadicand,
    orbitComponentMinusPulledRadicand,
    orbitDiscriminantPulledRadicand]
  have hproduct4 :
      4 * alpha * beta = 4 * k ^ 2 := by
    calc
      4 * alpha * beta = 4 * (alpha * beta) := by ring
      _ = 4 * k ^ 2 := by rw [hproduct]
  rw [hproduct4]
  simp only [map_pow, map_add, map_sub, map_mul, map_neg, map_ofNat]
  ring

/-- The orbit-discriminant pullback has degree at most `4d`. -/
theorem orbitDiscriminantPulledRadicand_natDegree_le
    (alpha beta gamma : K) (d : ℕ) :
    (orbitDiscriminantPulledRadicand alpha beta gamma d).natDegree ≤
      4 * d := by
  unfold orbitDiscriminantPulledRadicand
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact natDegree_X_pow_le _
        · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
      · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · simp

/-- The positive component pullback has degree at most `2d`. -/
theorem orbitComponentPlusPulledRadicand_natDegree_le
    (alpha gamma k : K) (d : ℕ) :
    (orbitComponentPlusPulledRadicand alpha gamma k d).natDegree ≤
      2 * d := by
  unfold orbitComponentPlusPulledRadicand
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_C_mul_X_pow_le _ _
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · exact (natDegree_C _).le.trans (Nat.zero_le _)

/-- The negative component pullback has degree at most `2d`. -/
theorem orbitComponentMinusPulledRadicand_natDegree_le
    (alpha gamma k : K) (d : ℕ) :
    (orbitComponentMinusPulledRadicand alpha gamma k d).natDegree ≤
      2 * d := by
  unfold orbitComponentMinusPulledRadicand
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_C_mul_X_pow_le _ _
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · exact (natDegree_C _).le.trans (Nat.zero_le _)

/-- For positive `d`, the orbit-discriminant pullback has leading
coefficient one. -/
theorem coeff_orbitDiscriminantPulledRadicand_four_mul
    (alpha beta gamma : K) {d : ℕ} (hd : 0 < d) :
    (orbitDiscriminantPulledRadicand alpha beta gamma d).coeff (4 * d) =
      1 := by
  have hcoeff3 :
      (C (-2 * gamma) * X ^ (3 * d) : K[X]).coeff (4 * d) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact (natDegree_C_mul_X_pow_le _ _).trans_lt (by omega)
  have hcoeff2 :
      (C (gamma ^ 2 + 2 - 4 * alpha * beta) *
          X ^ (2 * d) : K[X]).coeff (4 * d) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact (natDegree_C_mul_X_pow_le _ _).trans_lt (by omega)
  have hcoeff1 :
      (C (-2 * gamma) * X ^ d : K[X]).coeff (4 * d) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact (natDegree_C_mul_X_pow_le _ _).trans_lt (by omega)
  have h40 : 4 * d ≠ 0 := by omega
  rw [orbitDiscriminantPulledRadicand]
  simp only [coeff_add, hcoeff3, hcoeff2, hcoeff1, add_zero]
  rw [coeff_one, if_neg h40]
  simp

/-- For positive `d`, a nonzero `alpha` is the leading coefficient of the
positive component pullback. -/
theorem coeff_orbitComponentPlusPulledRadicand_two_mul
    (alpha gamma k : K) {d : ℕ} (hd : 0 < d) :
    (orbitComponentPlusPulledRadicand alpha gamma k d).coeff (2 * d) =
      alpha := by
  have hcoeff1 :
      (C (alpha * (2 * k - gamma)) * X ^ d : K[X]).coeff
          (2 * d) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact (natDegree_C_mul_X_pow_le _ _).trans_lt (by omega)
  have hcoeff0 : (C alpha : K[X]).coeff (2 * d) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact (natDegree_C _).le.trans_lt (by omega)
  rw [orbitComponentPlusPulledRadicand]
  simp only [coeff_add, hcoeff1, hcoeff0, add_zero]
  simp

/-- For positive `d`, a nonzero `alpha` is also the leading coefficient of
the negative component pullback. -/
theorem coeff_orbitComponentMinusPulledRadicand_two_mul
    (alpha gamma k : K) {d : ℕ} (hd : 0 < d) :
    (orbitComponentMinusPulledRadicand alpha gamma k d).coeff (2 * d) =
      alpha := by
  have hcoeff1 :
      (C (alpha * (-2 * k - gamma)) * X ^ d : K[X]).coeff
          (2 * d) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact (natDegree_C_mul_X_pow_le _ _).trans_lt (by omega)
  have hcoeff0 : (C alpha : K[X]).coeff (2 * d) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact (natDegree_C _).le.trans_lt (by omega)
  rw [orbitComponentMinusPulledRadicand]
  simp only [coeff_add, hcoeff1, hcoeff0, add_zero]
  simp

/-- The `4d` degree bound is sharp for positive `d`. -/
theorem orbitDiscriminantPulledRadicand_natDegree_eq
    (alpha beta gamma : K) {d : ℕ} (hd : 0 < d) :
    (orbitDiscriminantPulledRadicand alpha beta gamma d).natDegree =
      4 * d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact orbitDiscriminantPulledRadicand_natDegree_le
      alpha beta gamma d
  · rw [coeff_orbitDiscriminantPulledRadicand_four_mul
      alpha beta gamma hd]
    exact one_ne_zero

/-- The `2d` positive-component degree bound is sharp when
`alpha ≠ 0`. -/
theorem orbitComponentPlusPulledRadicand_natDegree_eq
    {alpha : K} (halpha : alpha ≠ 0) (gamma k : K)
    {d : ℕ} (hd : 0 < d) :
    (orbitComponentPlusPulledRadicand alpha gamma k d).natDegree =
      2 * d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact orbitComponentPlusPulledRadicand_natDegree_le
      alpha gamma k d
  · simpa [coeff_orbitComponentPlusPulledRadicand_two_mul
      alpha gamma k hd] using halpha

/-- The `2d` negative-component degree bound is sharp when
`alpha ≠ 0`. -/
theorem orbitComponentMinusPulledRadicand_natDegree_eq
    {alpha : K} (halpha : alpha ≠ 0) (gamma k : K)
    {d : ℕ} (hd : 0 < d) :
    (orbitComponentMinusPulledRadicand alpha gamma k d).natDegree =
      2 * d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact orbitComponentMinusPulledRadicand_natDegree_le
      alpha gamma k d
  · simpa [coeff_orbitComponentMinusPulledRadicand_two_mul
      alpha gamma k hd] using halpha

/-- The monic orbit-discriminant pullback is nonzero for positive `d`. -/
theorem orbitDiscriminantPulledRadicand_ne_zero
    (alpha beta gamma : K) {d : ℕ} (hd : 0 < d) :
    orbitDiscriminantPulledRadicand alpha beta gamma d ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun f : K[X] => f.coeff (4 * d)) hzero
  rw [coeff_orbitDiscriminantPulledRadicand_four_mul
    alpha beta gamma hd] at hcoeff
  simp at hcoeff

/-- For positive `d`, the positive component pullback is nonzero exactly
when `alpha` is nonzero. -/
theorem orbitComponentPlusPulledRadicand_ne_zero_iff
    (alpha gamma k : K) {d : ℕ} (hd : 0 < d) :
    orbitComponentPlusPulledRadicand alpha gamma k d ≠ 0 ↔
      alpha ≠ 0 := by
  constructor
  · intro hpolynomial halpha
    apply hpolynomial
    simp [orbitComponentPlusPulledRadicand, halpha]
  · intro halpha hzero
    have hcoeff := congrArg (fun f : K[X] => f.coeff (2 * d)) hzero
    rw [coeff_orbitComponentPlusPulledRadicand_two_mul
      alpha gamma k hd] at hcoeff
    exact halpha (by simpa using hcoeff)

/-- For positive `d`, the negative component pullback is nonzero exactly
when `alpha` is nonzero. -/
theorem orbitComponentMinusPulledRadicand_ne_zero_iff
    (alpha gamma k : K) {d : ℕ} (hd : 0 < d) :
    orbitComponentMinusPulledRadicand alpha gamma k d ≠ 0 ↔
      alpha ≠ 0 := by
  constructor
  · intro hpolynomial halpha
    apply hpolynomial
    simp [orbitComponentMinusPulledRadicand, halpha]
  · intro halpha hzero
    have hcoeff := congrArg (fun f : K[X] => f.coeff (2 * d)) hzero
    rw [coeff_orbitComponentMinusPulledRadicand_two_mul
      alpha gamma k hd] at hcoeff
    exact halpha (by simpa using hcoeff)

end

end GenMarkoff.General.Cage
