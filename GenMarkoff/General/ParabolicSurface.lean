import GenMarkoff.General.Parabolic

/-!
# Parabolic cycles on the generalized surface

The affine calculation leaves a signed fixed locus at trace `2` or `-2`.
On a genuine surface fiber that locus is incompatible with the usual
coefficient nondegeneracy.  This file proves that exclusion without using
coordinate permutations and upgrades the affine period calculation to an
actual first-rotation period theorem.
-/

namespace GenMarkoff.General

universe u

section Field

variable {K : Type u} [Field K]

/-- A positive-parabolic fixed point on the ordered conic forces the moving
coefficient square to be `4`. -/
theorem affineRotation_two_ne_self_of_fiberConic_eq_zero
    (B C u y z : K) (hu : u ≠ 0) (hC : C ^ 2 ≠ 4)
    (hconic : fiberConic B C u 2 y z = 0) :
    affineRotation B C u 2 (y, z) ≠ (y, z) := by
  intro hfixed
  rcases (affineRotation_two_eq_self_iff B C u (y, z)).mp hfixed with
    ⟨hline, hsignedMul⟩
  have hsigned : B + C = 0 :=
    (mul_eq_zero.mp hsignedMul).resolve_right hu
  have hlineZero : 2 * (z - y) - C * u = 0 := by
    linear_combination hline
  have hfactor : (4 - C ^ 2) * u ^ 2 = 0 := by
    simp only [fiberConic] at hconic
    linear_combination
      4 * hconic - 4 * u * z * hsigned -
        (2 * (z - y) - C * u) * hlineZero
  have hcoefficient : 4 - C ^ 2 ≠ 0 :=
    sub_ne_zero.mpr hC.symm
  have huSq : u ^ 2 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hcoefficient
  exact hu (sq_eq_zero_iff.mp huSq)

/-- A negative-parabolic fixed point on the ordered conic has the analogous
consequence, now using the signed condition `B - C = 0`. -/
theorem affineRotation_neg_two_ne_self_of_fiberConic_eq_zero
    (B C u y z : K) (hu : u ≠ 0) (hC : C ^ 2 ≠ 4)
    (hconic : fiberConic B C u (-2) y z = 0) :
    affineRotation B C u (-2) (y, z) ≠ (y, z) := by
  intro hfixed
  rcases (affineRotation_neg_two_eq_self_iff B C u (y, z)).mp hfixed with
    ⟨hline, hsignedMul⟩
  have hsigned : B - C = 0 :=
    (mul_eq_zero.mp hsignedMul).resolve_right hu
  have hlineZero : 2 * (y + z) + C * u = 0 := by
    linear_combination hline
  have hfactor : (4 - C ^ 2) * u ^ 2 = 0 := by
    simp only [fiberConic] at hconic
    linear_combination
      4 * hconic - 4 * u * z * hsigned -
        (2 * (y + z) + C * u) * hlineZero
  have hcoefficient : 4 - C ^ 2 ≠ 0 :=
    sub_ne_zero.mpr hC.symm
  have huSq : u ^ 2 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hcoefficient
  exact hu (sq_eq_zero_iff.mp huSq)

theorem fixedCoordinate_ne_zero_of_orderedTrace_eq_two
    (s A u : K) (hA : A ^ 2 ≠ 4)
    (htrace : orderedTrace s A u = 2) :
    u ≠ 0 := by
  intro hu
  have hAeq : A = -2 := by
    rw [hu, orderedTrace] at htrace
    linear_combination -htrace
  apply hA
  rw [hAeq]
  norm_num

theorem fixedCoordinate_ne_zero_of_orderedTrace_eq_neg_two
    (s A u : K) (hA : A ^ 2 ≠ 4)
    (htrace : orderedTrace s A u = -2) :
    u ≠ 0 := by
  intro hu
  have hAeq : A = 2 := by
    rw [hu, orderedTrace] at htrace
    linear_combination -htrace
  apply hA
  rw [hAeq]
  norm_num

/-- The first rotation is nonfixed at a positive-parabolic surface point
under the two coefficient-square hypotheses belonging to the fixed and
second moving entries of its ordered frame. -/
theorem rotation1_ne_self_of_trace_eq_two
    (a : Coefficients K) (x : Point K)
    (hA : a.a1 ^ 2 ≠ 4) (hC : a.a3 ^ 2 ≠ 4)
    (htrace : orderedTrace a.multiplier a.a1 x.x1 = 2)
    (hx : IsSolution a x) :
    rotation1 a x ≠ x := by
  have hu : x.x1 ≠ 0 :=
    fixedCoordinate_ne_zero_of_orderedTrace_eq_two
      a.multiplier a.a1 x.x1 hA htrace
  have hconic : fiberConic a.a2 a.a3 x.x1 2 x.x2 x.x3 = 0 := by
    have hsurface := hx
    rw [IsSolution, polynomial_fixed_first, htrace] at hsurface
    exact hsurface
  have hpair :
      affineRotation a.a2 a.a3 x.x1 2 (movingCoordinates1 x) ≠
        movingCoordinates1 x := by
    simpa [movingCoordinates1] using
      affineRotation_two_ne_self_of_fiberConic_eq_zero
        a.a2 a.a3 x.x1 x.x2 x.x3 hu hC hconic
  intro hfixed
  apply hpair
  calc
    affineRotation a.a2 a.a3 x.x1 2 (movingCoordinates1 x) =
        movingCoordinates1 (rotation1 a x) := by
      symm
      simpa [htrace] using movingCoordinates1_rotation1 a x
    _ = movingCoordinates1 x := congrArg movingCoordinates1 hfixed

/-- Negative-parabolic analogue of
`rotation1_ne_self_of_trace_eq_two`. -/
theorem rotation1_ne_self_of_trace_eq_neg_two
    (a : Coefficients K) (x : Point K)
    (hA : a.a1 ^ 2 ≠ 4) (hC : a.a3 ^ 2 ≠ 4)
    (htrace : orderedTrace a.multiplier a.a1 x.x1 = -2)
    (hx : IsSolution a x) :
    rotation1 a x ≠ x := by
  have hu : x.x1 ≠ 0 :=
    fixedCoordinate_ne_zero_of_orderedTrace_eq_neg_two
      a.multiplier a.a1 x.x1 hA htrace
  have hconic :
      fiberConic a.a2 a.a3 x.x1 (-2) x.x2 x.x3 = 0 := by
    have hsurface := hx
    rw [IsSolution, polynomial_fixed_first, htrace] at hsurface
    exact hsurface
  have hpair :
      affineRotation a.a2 a.a3 x.x1 (-2) (movingCoordinates1 x) ≠
        movingCoordinates1 x := by
    simpa [movingCoordinates1] using
      affineRotation_neg_two_ne_self_of_fiberConic_eq_zero
        a.a2 a.a3 x.x1 x.x2 x.x3 hu hC hconic
  intro hfixed
  apply hpair
  calc
    affineRotation a.a2 a.a3 x.x1 (-2) (movingCoordinates1 x) =
        movingCoordinates1 (rotation1 a x) := by
      symm
      simpa [htrace] using movingCoordinates1_rotation1 a x
    _ = movingCoordinates1 x := congrArg movingCoordinates1 hfixed

/-- The second rotation has no fixed surface point on its positive-parabolic
fiber under the ordered coefficient-square hypotheses. -/
theorem rotation2_ne_self_of_trace_eq_two
    (a : Coefficients K) (x : Point K)
    (hA : a.a2 ^ 2 ≠ 4) (hC : a.a1 ^ 2 ≠ 4)
    (htrace : orderedTrace a.multiplier a.a2 x.x2 = 2)
    (hx : IsSolution a x) :
    rotation2 a x ≠ x := by
  have hu : x.x2 ≠ 0 :=
    fixedCoordinate_ne_zero_of_orderedTrace_eq_two
      a.multiplier a.a2 x.x2 hA htrace
  have hconic : fiberConic a.a3 a.a1 x.x2 2 x.x3 x.x1 = 0 := by
    have hsurface := hx
    rw [IsSolution, polynomial_fixed_second, htrace] at hsurface
    exact hsurface
  have hpair :
      affineRotation a.a3 a.a1 x.x2 2 (movingCoordinates2 x) ≠
        movingCoordinates2 x := by
    simpa [movingCoordinates2] using
      affineRotation_two_ne_self_of_fiberConic_eq_zero
        a.a3 a.a1 x.x2 x.x3 x.x1 hu hC hconic
  intro hfixed
  apply hpair
  calc
    affineRotation a.a3 a.a1 x.x2 2 (movingCoordinates2 x) =
        movingCoordinates2 (rotation2 a x) := by
      symm
      simpa [htrace] using movingCoordinates2_rotation2 a x
    _ = movingCoordinates2 x := congrArg movingCoordinates2 hfixed

/-- Negative-parabolic second-axis fixed-point exclusion. -/
theorem rotation2_ne_self_of_trace_eq_neg_two
    (a : Coefficients K) (x : Point K)
    (hA : a.a2 ^ 2 ≠ 4) (hC : a.a1 ^ 2 ≠ 4)
    (htrace : orderedTrace a.multiplier a.a2 x.x2 = -2)
    (hx : IsSolution a x) :
    rotation2 a x ≠ x := by
  have hu : x.x2 ≠ 0 :=
    fixedCoordinate_ne_zero_of_orderedTrace_eq_neg_two
      a.multiplier a.a2 x.x2 hA htrace
  have hconic :
      fiberConic a.a3 a.a1 x.x2 (-2) x.x3 x.x1 = 0 := by
    have hsurface := hx
    rw [IsSolution, polynomial_fixed_second, htrace] at hsurface
    exact hsurface
  have hpair :
      affineRotation a.a3 a.a1 x.x2 (-2) (movingCoordinates2 x) ≠
        movingCoordinates2 x := by
    simpa [movingCoordinates2] using
      affineRotation_neg_two_ne_self_of_fiberConic_eq_zero
        a.a3 a.a1 x.x2 x.x3 x.x1 hu hC hconic
  intro hfixed
  apply hpair
  calc
    affineRotation a.a3 a.a1 x.x2 (-2) (movingCoordinates2 x) =
        movingCoordinates2 (rotation2 a x) := by
      symm
      simpa [htrace] using movingCoordinates2_rotation2 a x
    _ = movingCoordinates2 x := congrArg movingCoordinates2 hfixed

/-- The third rotation has no fixed surface point on its
positive-parabolic fiber. -/
theorem rotation3_ne_self_of_trace_eq_two
    (a : Coefficients K) (x : Point K)
    (hA : a.a3 ^ 2 ≠ 4) (hC : a.a2 ^ 2 ≠ 4)
    (htrace : orderedTrace a.multiplier a.a3 x.x3 = 2)
    (hx : IsSolution a x) :
    rotation3 a x ≠ x := by
  have hu : x.x3 ≠ 0 :=
    fixedCoordinate_ne_zero_of_orderedTrace_eq_two
      a.multiplier a.a3 x.x3 hA htrace
  have hconic : fiberConic a.a1 a.a2 x.x3 2 x.x1 x.x2 = 0 := by
    have hsurface := hx
    rw [IsSolution, polynomial_fixed_third, htrace] at hsurface
    exact hsurface
  have hpair :
      affineRotation a.a1 a.a2 x.x3 2 (movingCoordinates3 x) ≠
        movingCoordinates3 x := by
    simpa [movingCoordinates3] using
      affineRotation_two_ne_self_of_fiberConic_eq_zero
        a.a1 a.a2 x.x3 x.x1 x.x2 hu hC hconic
  intro hfixed
  apply hpair
  calc
    affineRotation a.a1 a.a2 x.x3 2 (movingCoordinates3 x) =
        movingCoordinates3 (rotation3 a x) := by
      symm
      simpa [htrace] using movingCoordinates3_rotation3 a x
    _ = movingCoordinates3 x := congrArg movingCoordinates3 hfixed

/-- Negative-parabolic third-axis fixed-point exclusion. -/
theorem rotation3_ne_self_of_trace_eq_neg_two
    (a : Coefficients K) (x : Point K)
    (hA : a.a3 ^ 2 ≠ 4) (hC : a.a2 ^ 2 ≠ 4)
    (htrace : orderedTrace a.multiplier a.a3 x.x3 = -2)
    (hx : IsSolution a x) :
    rotation3 a x ≠ x := by
  have hu : x.x3 ≠ 0 :=
    fixedCoordinate_ne_zero_of_orderedTrace_eq_neg_two
      a.multiplier a.a3 x.x3 hA htrace
  have hconic :
      fiberConic a.a1 a.a2 x.x3 (-2) x.x1 x.x2 = 0 := by
    have hsurface := hx
    rw [IsSolution, polynomial_fixed_third, htrace] at hsurface
    exact hsurface
  have hpair :
      affineRotation a.a1 a.a2 x.x3 (-2) (movingCoordinates3 x) ≠
        movingCoordinates3 x := by
    simpa [movingCoordinates3] using
      affineRotation_neg_two_ne_self_of_fiberConic_eq_zero
        a.a1 a.a2 x.x3 x.x1 x.x2 hu hC hconic
  intro hfixed
  apply hpair
  calc
    affineRotation a.a1 a.a2 x.x3 (-2) (movingCoordinates3 x) =
        movingCoordinates3 (rotation3 a x) := by
      symm
      simpa [htrace] using movingCoordinates3_rotation3 a x
    _ = movingCoordinates3 x := congrArg movingCoordinates3 hfixed

end Field

section PrimeCharacteristic

variable {R : Type u} [Field R]

@[simp]
theorem rotation1_firstCoordinate
    (a : Coefficients R) (x : Point R) :
    (rotation1 a x).x1 = x.x1 := by
  rfl

@[simp]
theorem iterate_rotation1_firstCoordinate
    (a : Coefficients R) (x : Point R) (n : ℕ) :
    (((rotation1 a)^[n]) x).x1 = x.x1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', rotation1_firstCoordinate, ih]

/-- Iterating the first rotation on moving coordinates is exactly iteration
of its ordered affine rotation; the fixed trace is retained at every step. -/
theorem movingCoordinates1_iterate_rotation1
    (a : Coefficients R) (x : Point R) (n : ℕ) :
    movingCoordinates1 (((rotation1 a)^[n]) x) =
      ((affineRotation a.a2 a.a3 x.x1
        (orderedTrace a.multiplier a.a1 x.x1))^[n])
          (movingCoordinates1 x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        movingCoordinates1_rotation1, ih]
      rw [iterate_rotation1_firstCoordinate]

@[simp]
theorem rotation2_secondCoordinate
    (a : Coefficients R) (x : Point R) :
    (rotation2 a x).x2 = x.x2 := by
  rfl

@[simp]
theorem iterate_rotation2_secondCoordinate
    (a : Coefficients R) (x : Point R) (n : ℕ) :
    (((rotation2 a)^[n]) x).x2 = x.x2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', rotation2_secondCoordinate, ih]

theorem movingCoordinates2_iterate_rotation2
    (a : Coefficients R) (x : Point R) (n : ℕ) :
    movingCoordinates2 (((rotation2 a)^[n]) x) =
      ((affineRotation a.a3 a.a1 x.x2
        (orderedTrace a.multiplier a.a2 x.x2))^[n])
          (movingCoordinates2 x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        movingCoordinates2_rotation2, ih]
      rw [iterate_rotation2_secondCoordinate]

@[simp]
theorem rotation3_thirdCoordinate
    (a : Coefficients R) (x : Point R) :
    (rotation3 a x).x3 = x.x3 := by
  rfl

@[simp]
theorem iterate_rotation3_thirdCoordinate
    (a : Coefficients R) (x : Point R) (n : ℕ) :
    (((rotation3 a)^[n]) x).x3 = x.x3 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', rotation3_thirdCoordinate, ih]

theorem movingCoordinates3_iterate_rotation3
    (a : Coefficients R) (x : Point R) (n : ℕ) :
    movingCoordinates3 (((rotation3 a)^[n]) x) =
      ((affineRotation a.a1 a.a2 x.x3
        (orderedTrace a.multiplier a.a3 x.x3))^[n])
          (movingCoordinates3 x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        movingCoordinates3_rotation3, ih]
      rw [iterate_rotation3_thirdCoordinate]

/-- Every first-axis positive-parabolic surface point has actual rotation
period exactly `p` under the standard coefficient nondegeneracy. -/
theorem minimalPeriod_rotation1_eq_prime_of_trace_eq_two
    (p : ℕ) [Fact p.Prime] [CharP R p] (hpTwo : p ≠ 2)
    (a : Coefficients R) (x : Point R)
    (hA : a.a1 ^ 2 ≠ 4) (hC : a.a3 ^ 2 ≠ 4)
    (htrace : orderedTrace a.multiplier a.a1 x.x1 = 2)
    (hx : IsSolution a x) :
    Function.minimalPeriod (rotation1 a) x = p := by
  apply Function.minimalPeriod_eq_prime
  · apply Point.ext
    · exact iterate_rotation1_firstCoordinate a x p
    · have hpair := movingCoordinates1_iterate_rotation1 a x p
      rw [htrace, iterate_affineRotation_two_prime
        p Fact.out hpTwo a.a2 a.a3 x.x1 (movingCoordinates1 x)] at hpair
      exact congrArg Prod.fst hpair
    · have hpair := movingCoordinates1_iterate_rotation1 a x p
      rw [htrace, iterate_affineRotation_two_prime
        p Fact.out hpTwo a.a2 a.a3 x.x1 (movingCoordinates1 x)] at hpair
      exact congrArg Prod.snd hpair
  · exact rotation1_ne_self_of_trace_eq_two a x hA hC htrace hx

/-- Every first-axis negative-parabolic surface point likewise has actual
rotation period exactly `p`. -/
theorem minimalPeriod_rotation1_eq_prime_of_trace_eq_neg_two
    (p : ℕ) [Fact p.Prime] [CharP R p] (hpTwo : p ≠ 2)
    (a : Coefficients R) (x : Point R)
    (hA : a.a1 ^ 2 ≠ 4) (hC : a.a3 ^ 2 ≠ 4)
    (htrace : orderedTrace a.multiplier a.a1 x.x1 = -2)
    (hx : IsSolution a x) :
    Function.minimalPeriod (rotation1 a) x = p := by
  apply Function.minimalPeriod_eq_prime
  · apply Point.ext
    · exact iterate_rotation1_firstCoordinate a x p
    · have hpair := movingCoordinates1_iterate_rotation1 a x p
      rw [htrace, iterate_affineRotation_neg_two_prime
        p Fact.out hpTwo a.a2 a.a3 x.x1 (movingCoordinates1 x)] at hpair
      exact congrArg Prod.fst hpair
    · have hpair := movingCoordinates1_iterate_rotation1 a x p
      rw [htrace, iterate_affineRotation_neg_two_prime
        p Fact.out hpTwo a.a2 a.a3 x.x1 (movingCoordinates1 x)] at hpair
      exact congrArg Prod.snd hpair
  · exact rotation1_ne_self_of_trace_eq_neg_two a x hA hC htrace hx

/-- Positive-parabolic period classification for the second rotation. -/
theorem minimalPeriod_rotation2_eq_prime_of_trace_eq_two
    (p : ℕ) [Fact p.Prime] [CharP R p] (hpTwo : p ≠ 2)
    (a : Coefficients R) (x : Point R)
    (hA : a.a2 ^ 2 ≠ 4) (hC : a.a1 ^ 2 ≠ 4)
    (htrace : orderedTrace a.multiplier a.a2 x.x2 = 2)
    (hx : IsSolution a x) :
    Function.minimalPeriod (rotation2 a) x = p := by
  apply Function.minimalPeriod_eq_prime
  · apply Point.ext
    · have hpair := movingCoordinates2_iterate_rotation2 a x p
      rw [htrace, iterate_affineRotation_two_prime
        p Fact.out hpTwo a.a3 a.a1 x.x2 (movingCoordinates2 x)] at hpair
      exact congrArg Prod.snd hpair
    · exact iterate_rotation2_secondCoordinate a x p
    · have hpair := movingCoordinates2_iterate_rotation2 a x p
      rw [htrace, iterate_affineRotation_two_prime
        p Fact.out hpTwo a.a3 a.a1 x.x2 (movingCoordinates2 x)] at hpair
      exact congrArg Prod.fst hpair
  · exact rotation2_ne_self_of_trace_eq_two a x hA hC htrace hx

/-- Negative-parabolic period classification for the second rotation. -/
theorem minimalPeriod_rotation2_eq_prime_of_trace_eq_neg_two
    (p : ℕ) [Fact p.Prime] [CharP R p] (hpTwo : p ≠ 2)
    (a : Coefficients R) (x : Point R)
    (hA : a.a2 ^ 2 ≠ 4) (hC : a.a1 ^ 2 ≠ 4)
    (htrace : orderedTrace a.multiplier a.a2 x.x2 = -2)
    (hx : IsSolution a x) :
    Function.minimalPeriod (rotation2 a) x = p := by
  apply Function.minimalPeriod_eq_prime
  · apply Point.ext
    · have hpair := movingCoordinates2_iterate_rotation2 a x p
      rw [htrace, iterate_affineRotation_neg_two_prime
        p Fact.out hpTwo a.a3 a.a1 x.x2 (movingCoordinates2 x)] at hpair
      exact congrArg Prod.snd hpair
    · exact iterate_rotation2_secondCoordinate a x p
    · have hpair := movingCoordinates2_iterate_rotation2 a x p
      rw [htrace, iterate_affineRotation_neg_two_prime
        p Fact.out hpTwo a.a3 a.a1 x.x2 (movingCoordinates2 x)] at hpair
      exact congrArg Prod.fst hpair
  · exact rotation2_ne_self_of_trace_eq_neg_two a x hA hC htrace hx

/-- Positive-parabolic period classification for the third rotation. -/
theorem minimalPeriod_rotation3_eq_prime_of_trace_eq_two
    (p : ℕ) [Fact p.Prime] [CharP R p] (hpTwo : p ≠ 2)
    (a : Coefficients R) (x : Point R)
    (hA : a.a3 ^ 2 ≠ 4) (hC : a.a2 ^ 2 ≠ 4)
    (htrace : orderedTrace a.multiplier a.a3 x.x3 = 2)
    (hx : IsSolution a x) :
    Function.minimalPeriod (rotation3 a) x = p := by
  apply Function.minimalPeriod_eq_prime
  · apply Point.ext
    · have hpair := movingCoordinates3_iterate_rotation3 a x p
      rw [htrace, iterate_affineRotation_two_prime
        p Fact.out hpTwo a.a1 a.a2 x.x3 (movingCoordinates3 x)] at hpair
      exact congrArg Prod.fst hpair
    · have hpair := movingCoordinates3_iterate_rotation3 a x p
      rw [htrace, iterate_affineRotation_two_prime
        p Fact.out hpTwo a.a1 a.a2 x.x3 (movingCoordinates3 x)] at hpair
      exact congrArg Prod.snd hpair
    · exact iterate_rotation3_thirdCoordinate a x p
  · exact rotation3_ne_self_of_trace_eq_two a x hA hC htrace hx

/-- Negative-parabolic period classification for the third rotation. -/
theorem minimalPeriod_rotation3_eq_prime_of_trace_eq_neg_two
    (p : ℕ) [Fact p.Prime] [CharP R p] (hpTwo : p ≠ 2)
    (a : Coefficients R) (x : Point R)
    (hA : a.a3 ^ 2 ≠ 4) (hC : a.a2 ^ 2 ≠ 4)
    (htrace : orderedTrace a.multiplier a.a3 x.x3 = -2)
    (hx : IsSolution a x) :
    Function.minimalPeriod (rotation3 a) x = p := by
  apply Function.minimalPeriod_eq_prime
  · apply Point.ext
    · have hpair := movingCoordinates3_iterate_rotation3 a x p
      rw [htrace, iterate_affineRotation_neg_two_prime
        p Fact.out hpTwo a.a1 a.a2 x.x3 (movingCoordinates3 x)] at hpair
      exact congrArg Prod.fst hpair
    · have hpair := movingCoordinates3_iterate_rotation3 a x p
      rw [htrace, iterate_affineRotation_neg_two_prime
        p Fact.out hpTwo a.a1 a.a2 x.x3 (movingCoordinates3 x)] at hpair
      exact congrArg Prod.snd hpair
    · exact iterate_rotation3_thirdCoordinate a x p
  · exact rotation3_ne_self_of_trace_eq_neg_two a x hA hC htrace hx

end PrimeCharacteristic

end GenMarkoff.General
