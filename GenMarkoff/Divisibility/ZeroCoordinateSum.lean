import GenMarkoff.Divisibility.RegularAngles

/-!
# Sums of raw angles on zero-coordinate fibers

The generalized Martin argument does not require a pointwise extension of the
three raw angle functions across a zero coordinate.  On a finite family
preserved by the corresponding two-Vieta rotation, the central raw angle has
zero sum.  The proof reindexes twice and uses the quadratic equation satisfied
by the squared coordinate ratio.

The first theorem below isolates the finite-permutation argument.  The three
subsequent theorems apply it to arbitrary finite models of the three
zero-coordinate fibers.  This form lets a caller use a filtered Vieta-orbit
subtype without introducing a global choice of cycle representatives.
-/

namespace GenMarkoff

universe u v

/-- Let `d` scale by `q` under a permutation and let `q` be invariant.  If
`q` satisfies a monic reciprocal quadratic `q^2 + c*q + 1 = 0`, then the sum
of `d` is zero whenever `c + 2` is nonzero.

Indeed, reindexing once identifies `sum d` with `sum q*d`, and reindexing a
second time identifies that sum with `sum q^2*d`. -/
theorem sum_eq_zero_of_invariant_scale_quadratic
    {X : Type u} {F : Type v} [Fintype X] [Field F]
    (rho : Equiv.Perm X) (d q : X → F) (c : F)
    (hq_invariant : ∀ x, q (rho x) = q x)
    (hd_scale : ∀ x, d (rho x) = q x * d x)
    (hq_quadratic : ∀ x, q x ^ 2 + c * q x + 1 = 0)
    (hc : c + 2 ≠ 0) :
    (∑ x, d x) = 0 := by
  have hreindex_d : (∑ x, d (rho x)) = ∑ x, d x :=
    Equiv.sum_comp rho d
  have hreindex_qd : (∑ x, q (rho x) * d (rho x)) = ∑ x, q x * d x :=
    Equiv.sum_comp rho (fun x ↦ q x * d x)
  have hsum_qd : (∑ x, q x * d x) = ∑ x, d x := by
    calc
      (∑ x, q x * d x) = ∑ x, d (rho x) := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact (hd_scale x).symm
      _ = ∑ x, d x := hreindex_d
  have hsum_qsq_d : (∑ x, q x ^ 2 * d x) = ∑ x, q x * d x := by
    calc
      (∑ x, q x ^ 2 * d x) = ∑ x, q (rho x) * d (rho x) := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [hq_invariant, hd_scale]
        ring
      _ = ∑ x, q x * d x := hreindex_qd
  have hquadratic_sum :
      (∑ x, q x ^ 2 * d x) + c * (∑ x, q x * d x) + (∑ x, d x) = 0 := by
    calc
      (∑ x, q x ^ 2 * d x) + c * (∑ x, q x * d x) + (∑ x, d x) =
          (∑ x, q x ^ 2 * d x) + (∑ x, c * (q x * d x)) + (∑ x, d x) := by
            rw [Finset.mul_sum]
      _ = ∑ x, (q x ^ 2 + c * q x + 1) * d x := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _hx
        ring
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro x _hx
        rw [hq_quadratic x, zero_mul]
  have hfactor : (c + 2) * (∑ x, d x) = 0 := by
    rw [hsum_qsq_d, hsum_qd] at hquadratic_sum
    linear_combination hquadratic_sum
  exact (mul_eq_zero.mp hfactor).resolve_left hc

section ZeroCoordinateGeometry

variable {K : Type u} [Field K]

private theorem square_ratio_quadratic
    (r b : K) (hr : r ^ 2 + b * r + 1 = 0) :
    (r ^ 2) ^ 2 + (2 - b ^ 2) * r ^ 2 + 1 = 0 := by
  calc
    (r ^ 2) ^ 2 + (2 - b ^ 2) * r ^ 2 + 1 =
        (r ^ 2 + b * r + 1) * (r ^ 2 - b * r + 1) := by ring
    _ = 0 := by rw [hr, zero_mul]

private theorem two_sub_sq_add_two_ne_zero
    (b : K) (hb : b ^ 2 ≠ 4) :
    (2 - b ^ 2) + 2 ≠ 0 := by
  intro h
  apply hb
  linear_combination -h

/-- On the first zero-coordinate fiber, the ratio `x₂/x₃` is preserved
by `rotation1`. -/
theorem ratio_rotation1_eq_of_x1_eq_zero
    (a : Coefficients K) (x : Point K)
    (hx1 : x.x1 = 0) (hx2 : x.x2 ≠ 0) (hx3 : x.x3 ≠ 0)
    (hratio : (x.x2 / x.x3) ^ 2 + a.a1 * (x.x2 / x.x3) + 1 = 0) :
    (rotation1 a x).x2 / (rotation1 a x).x3 = x.x2 / x.x3 := by
  have hquad : x.x2 ^ 2 + a.a1 * x.x2 * x.x3 + x.x3 ^ 2 = 0 := by
    field_simp [hx3] at hratio
    linear_combination hratio
  have hrot2 : (rotation1 a x).x2 = x.x3 ^ 2 / x.x2 := by
    unfold rotation1 vieta3 vieta2
    dsimp
    rw [hx1]
    field_simp [hx2]
    linear_combination -hquad
  have hrot3 : (rotation1 a x).x3 = x.x3 ^ 3 / x.x2 ^ 2 := by
    have hformula :
        (rotation1 a x).x3 = -x.x3 - a.a1 * (rotation1 a x).x2 := by
      simp [rotation1, vieta3, vieta2, hx1]
    rw [hformula, hrot2]
    field_simp [hx2]
    linear_combination -hquad
  rw [hrot2, hrot3]
  field_simp [hx2, hx3]

/-- On the second zero-coordinate fiber, the ratio `x₃/x₁` is preserved
by `rotation2`. -/
theorem ratio_rotation2_eq_of_x2_eq_zero
    (a : Coefficients K) (x : Point K)
    (hx2 : x.x2 = 0) (hx1 : x.x1 ≠ 0) (hx3 : x.x3 ≠ 0)
    (hratio : (x.x3 / x.x1) ^ 2 + a.a2 * (x.x3 / x.x1) + 1 = 0) :
    (rotation2 a x).x3 / (rotation2 a x).x1 = x.x3 / x.x1 := by
  have hquad : x.x3 ^ 2 + a.a2 * x.x3 * x.x1 + x.x1 ^ 2 = 0 := by
    field_simp [hx1] at hratio
    linear_combination hratio
  have hrot3 : (rotation2 a x).x3 = x.x1 ^ 2 / x.x3 := by
    unfold rotation2 vieta1 vieta3
    dsimp
    rw [hx2]
    field_simp [hx3]
    linear_combination -hquad
  have hrot1 : (rotation2 a x).x1 = x.x1 ^ 3 / x.x3 ^ 2 := by
    have hformula :
        (rotation2 a x).x1 = -x.x1 - a.a2 * (rotation2 a x).x3 := by
      simp [rotation2, vieta1, vieta3, hx2]
    rw [hformula, hrot3]
    field_simp [hx3]
    linear_combination -hquad
  rw [hrot3, hrot1]
  field_simp [hx1, hx3]

/-- On the third zero-coordinate fiber, the ratio `x₁/x₂` is preserved
by `rotation3`. -/
theorem ratio_rotation3_eq_of_x3_eq_zero
    (a : Coefficients K) (x : Point K)
    (hx3 : x.x3 = 0) (hx1 : x.x1 ≠ 0) (hx2 : x.x2 ≠ 0)
    (hratio : (x.x1 / x.x2) ^ 2 + a.a3 * (x.x1 / x.x2) + 1 = 0) :
    (rotation3 a x).x1 / (rotation3 a x).x2 = x.x1 / x.x2 := by
  have hquad : x.x1 ^ 2 + a.a3 * x.x1 * x.x2 + x.x2 ^ 2 = 0 := by
    field_simp [hx2] at hratio
    linear_combination hratio
  have hrot1 : (rotation3 a x).x1 = x.x2 ^ 2 / x.x1 := by
    unfold rotation3 vieta2 vieta1
    dsimp
    rw [hx3]
    field_simp [hx1]
    linear_combination -hquad
  have hrot2 : (rotation3 a x).x2 = x.x2 ^ 3 / x.x1 ^ 2 := by
    have hformula :
        (rotation3 a x).x2 = -x.x2 - a.a3 * (rotation3 a x).x1 := by
      simp [rotation3, vieta2, vieta1, hx3]
    rw [hformula, hrot1]
    field_simp [hx1]
    linear_combination -hquad
  rw [hrot1, hrot2]
  field_simp [hx1, hx2]

/-- The first raw angle sums to zero on any finite model of a punctured
`x₁ = 0` family on which the model permutation realizes `rotation1`. -/
theorem sum_rawAngle1_eq_zero_of_zero_rotation_model
    {X : Type v} [Fintype X]
    (a : Coefficients K) (rho : Equiv.Perm X) (point : X → Point K)
    (ha1 : a.a1 ^ 2 ≠ 4)
    (hrotation : ∀ x, point (rho x) = rotation1 a (point x))
    (hsolution : ∀ x, IsSolution a (point x))
    (hpunctured : ∀ x, point x ≠ origin)
    (hzero : ∀ x, (point x).x1 = 0) :
    (∑ x, rawAngle1 a (point x)) = 0 := by
  let q : X → K := fun x ↦ ((point x).x2 / (point x).x3) ^ 2
  apply sum_eq_zero_of_invariant_scale_quadratic rho
      (fun x ↦ rawAngle1 a (point x)) q (2 - a.a1 ^ 2)
  · intro x
    have hne := coordinates_ne_zero_of_x1_eq_zero a (point x)
      (hsolution x) (hpunctured x) (hzero x)
    have hratio := ratio_quadratic_of_x1_eq_zero a (point x)
      (hsolution x) (hpunctured x) (hzero x)
    simp only [q, hrotation]
    rw [ratio_rotation1_eq_of_x1_eq_zero a (point x) (hzero x) hne.1 hne.2 hratio]
  · intro x
    have hne := coordinates_ne_zero_of_x1_eq_zero a (point x)
      (hsolution x) (hpunctured x) (hzero x)
    have hratio := ratio_quadratic_of_x1_eq_zero a (point x)
      (hsolution x) (hpunctured x) (hzero x)
    rw [hrotation]
    exact rawAngle1_rotation1_scale_of_x1_eq_zero a (point x)
      (hzero x) hne.1 hne.2 hratio
  · intro x
    exact square_ratio_quadratic _ _
      (ratio_quadratic_of_x1_eq_zero a (point x)
        (hsolution x) (hpunctured x) (hzero x))
  · exact two_sub_sq_add_two_ne_zero a.a1 ha1

/-- The second raw angle sums to zero on any finite model of a punctured
`x₂ = 0` family on which the model permutation realizes `rotation2`. -/
theorem sum_rawAngle2_eq_zero_of_zero_rotation_model
    {X : Type v} [Fintype X]
    (a : Coefficients K) (rho : Equiv.Perm X) (point : X → Point K)
    (ha2 : a.a2 ^ 2 ≠ 4)
    (hrotation : ∀ x, point (rho x) = rotation2 a (point x))
    (hsolution : ∀ x, IsSolution a (point x))
    (hpunctured : ∀ x, point x ≠ origin)
    (hzero : ∀ x, (point x).x2 = 0) :
    (∑ x, rawAngle2 a (point x)) = 0 := by
  let q : X → K := fun x ↦ ((point x).x3 / (point x).x1) ^ 2
  apply sum_eq_zero_of_invariant_scale_quadratic rho
      (fun x ↦ rawAngle2 a (point x)) q (2 - a.a2 ^ 2)
  · intro x
    have hne := coordinates_ne_zero_of_x2_eq_zero a (point x)
      (hsolution x) (hpunctured x) (hzero x)
    have hratio := ratio_quadratic_of_x2_eq_zero a (point x)
      (hsolution x) (hpunctured x) (hzero x)
    simp only [q, hrotation]
    rw [ratio_rotation2_eq_of_x2_eq_zero a (point x) (hzero x) hne.1 hne.2 hratio]
  · intro x
    have hne := coordinates_ne_zero_of_x2_eq_zero a (point x)
      (hsolution x) (hpunctured x) (hzero x)
    have hratio := ratio_quadratic_of_x2_eq_zero a (point x)
      (hsolution x) (hpunctured x) (hzero x)
    rw [hrotation]
    exact rawAngle2_rotation2_scale_of_x2_eq_zero a (point x)
      (hzero x) hne.1 hne.2 hratio
  · intro x
    exact square_ratio_quadratic _ _
      (ratio_quadratic_of_x2_eq_zero a (point x)
        (hsolution x) (hpunctured x) (hzero x))
  · exact two_sub_sq_add_two_ne_zero a.a2 ha2

/-- The third raw angle sums to zero on any finite model of a punctured
`x₃ = 0` family on which the model permutation realizes `rotation3`. -/
theorem sum_rawAngle3_eq_zero_of_zero_rotation_model
    {X : Type v} [Fintype X]
    (a : Coefficients K) (rho : Equiv.Perm X) (point : X → Point K)
    (ha3 : a.a3 ^ 2 ≠ 4)
    (hrotation : ∀ x, point (rho x) = rotation3 a (point x))
    (hsolution : ∀ x, IsSolution a (point x))
    (hpunctured : ∀ x, point x ≠ origin)
    (hzero : ∀ x, (point x).x3 = 0) :
    (∑ x, rawAngle3 a (point x)) = 0 := by
  let q : X → K := fun x ↦ ((point x).x1 / (point x).x2) ^ 2
  apply sum_eq_zero_of_invariant_scale_quadratic rho
      (fun x ↦ rawAngle3 a (point x)) q (2 - a.a3 ^ 2)
  · intro x
    have hne := coordinates_ne_zero_of_x3_eq_zero a (point x)
      (hsolution x) (hpunctured x) (hzero x)
    have hratio := ratio_quadratic_of_x3_eq_zero a (point x)
      (hsolution x) (hpunctured x) (hzero x)
    simp only [q, hrotation]
    rw [ratio_rotation3_eq_of_x3_eq_zero a (point x) (hzero x) hne.1 hne.2 hratio]
  · intro x
    have hne := coordinates_ne_zero_of_x3_eq_zero a (point x)
      (hsolution x) (hpunctured x) (hzero x)
    have hratio := ratio_quadratic_of_x3_eq_zero a (point x)
      (hsolution x) (hpunctured x) (hzero x)
    rw [hrotation]
    exact rawAngle3_rotation3_scale_of_x3_eq_zero a (point x)
      (hzero x) hne.1 hne.2 hratio
  · intro x
    exact square_ratio_quadratic _ _
      (ratio_quadratic_of_x3_eq_zero a (point x)
        (hsolution x) (hpunctured x) (hzero x))
  · exact two_sub_sq_add_two_ne_zero a.a3 ha3

end ZeroCoordinateGeometry

end GenMarkoff
