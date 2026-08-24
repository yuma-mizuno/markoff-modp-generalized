import GenMarkoff.Core.Action

/-!
# Common fixed points of the general rotations

The integral nondegeneracy conditions are designed to remove the most
immediate punctured-orbit obstruction.  Over a field, if the multiplier and
the three determinants `4 - aᵢ²` are nonzero, a surface point fixed by the
rotation generators is the origin.

The proof first recovers fixedness under all three Vieta involutions.  Their
fixed-point equations are the three partial-derivative equations.  Euler's
identity together with the surface equation forces one coordinate to vanish;
the corresponding `2 × 2` determinant then forces the other two to vanish.
-/

namespace GenMarkoff.General

universe u

section

variable {K : Type u} [Field K]

/-- Fixedness under `μ₁` gives the first partial-derivative equation. -/
theorem firstGradient_eq_zero_of_vieta1_eq
    (a : Coefficients K) (x : Point K)
    (h : vieta1 a x = x) :
    2 * x.x1 + a.a3 * x.x2 + a.a2 * x.x3 -
        a.multiplier * x.x2 * x.x3 = 0 := by
  have hx := congrArg Point.x1 h
  simp only [vieta1] at hx
  linear_combination -hx

/-- Fixedness under `μ₂` gives the second partial-derivative equation. -/
theorem secondGradient_eq_zero_of_vieta2_eq
    (a : Coefficients K) (x : Point K)
    (h : vieta2 a x = x) :
    2 * x.x2 + a.a1 * x.x3 + a.a3 * x.x1 -
        a.multiplier * x.x3 * x.x1 = 0 := by
  have hx := congrArg Point.x2 h
  simp only [vieta2] at hx
  linear_combination -hx

/-- Fixedness under `μ₃` gives the third partial-derivative equation. -/
theorem thirdGradient_eq_zero_of_vieta3_eq
    (a : Coefficients K) (x : Point K)
    (h : vieta3 a x = x) :
    2 * x.x3 + a.a2 * x.x1 + a.a1 * x.x2 -
        a.multiplier * x.x1 * x.x2 = 0 := by
  have hx := congrArg Point.x3 h
  simp only [vieta3] at hx
  linear_combination -hx

/-- A point fixed by the first two rotations is fixed by all three Vieta
involutions. -/
theorem vieta_fixed_of_rotation1_rotation2_fixed
    (a : Coefficients K) (x : Point K)
    (h1 : rotation1 a x = x) (h2 : rotation2 a x = x) :
    vieta1 a x = x ∧ vieta2 a x = x ∧ vieta3 a x = x := by
  have hx2 := congrArg Point.x2 h1
  have hv2 : vieta2 a x = x := by
    apply Point.ext
    · rfl
    · simpa [rotation1, vieta2, vieta3] using hx2
    · rfl
  have hv3 : vieta3 a x = x := by
    rw [rotation1, hv2] at h1
    exact h1
  have hv1 : vieta1 a x = x := by
    rw [rotation2, hv3] at h2
    exact h2
  exact ⟨hv1, hv2, hv3⟩

/-- Under the general nondegeneracy conditions, the origin is the only
surface point fixed by the first two rotations (and hence by all three). -/
theorem eq_origin_of_isSolution_of_rotation1_rotation2_fixed
    (a : Coefficients K) (x : Point K)
    (hmultiplier : a.multiplier ≠ 0)
    (ha1 : a.a1 ^ 2 ≠ 4) (ha2 : a.a2 ^ 2 ≠ 4)
    (ha3 : a.a3 ^ 2 ≠ 4)
    (hsolution : IsSolution a x)
    (h1 : rotation1 a x = x) (h2 : rotation2 a x = x) :
    x = origin := by
  obtain ⟨hv1, hv2, hv3⟩ :=
    vieta_fixed_of_rotation1_rotation2_fixed a x h1 h2
  have hg1 := firstGradient_eq_zero_of_vieta1_eq a x hv1
  have hg2 := secondGradient_eq_zero_of_vieta2_eq a x hv2
  have hg3 := thirdGradient_eq_zero_of_vieta3_eq a x hv3
  have hp := hsolution
  rw [IsSolution, polynomial] at hp
  have hproduct :
      a.multiplier * x.x1 * x.x2 * x.x3 = 0 := by
    linear_combination
      2 * hp - x.x1 * hg1 - x.x2 * hg2 - x.x3 * hg3
  have hproduct' :
      a.multiplier * (x.x1 * x.x2 * x.x3) = 0 := by
    simpa only [mul_assoc] using hproduct
  have hxyz : x.x1 * x.x2 * x.x3 = 0 :=
    (mul_eq_zero.mp hproduct').resolve_left hmultiplier
  rcases mul_eq_zero.mp hxyz with h12 | hx3
  · rcases mul_eq_zero.mp h12 with hx1 | hx2
    · have hdet : 4 - a.a1 ^ 2 ≠ 0 :=
        sub_ne_zero.mpr ha1.symm
      have hsecond : (4 - a.a1 ^ 2) * x.x2 = 0 := by
        rw [hx1] at hg2 hg3
        linear_combination 2 * hg2 - a.a1 * hg3
      have hthird : (4 - a.a1 ^ 2) * x.x3 = 0 := by
        rw [hx1] at hg2 hg3
        linear_combination 2 * hg3 - a.a1 * hg2
      have hx2 : x.x2 = 0 :=
        (mul_eq_zero.mp hsecond).resolve_left hdet
      have hx3 : x.x3 = 0 :=
        (mul_eq_zero.mp hthird).resolve_left hdet
      ext <;> simp [origin, hx1, hx2, hx3]
    · have hdet : 4 - a.a2 ^ 2 ≠ 0 :=
        sub_ne_zero.mpr ha2.symm
      have hfirst : (4 - a.a2 ^ 2) * x.x1 = 0 := by
        rw [hx2] at hg1 hg3
        linear_combination 2 * hg1 - a.a2 * hg3
      have hthird : (4 - a.a2 ^ 2) * x.x3 = 0 := by
        rw [hx2] at hg1 hg3
        linear_combination 2 * hg3 - a.a2 * hg1
      have hx1 : x.x1 = 0 :=
        (mul_eq_zero.mp hfirst).resolve_left hdet
      have hx3 : x.x3 = 0 :=
        (mul_eq_zero.mp hthird).resolve_left hdet
      ext <;> simp [origin, hx1, hx2, hx3]
  · have hdet : 4 - a.a3 ^ 2 ≠ 0 :=
      sub_ne_zero.mpr ha3.symm
    have hfirst : (4 - a.a3 ^ 2) * x.x1 = 0 := by
      rw [hx3] at hg1 hg2
      linear_combination 2 * hg1 - a.a3 * hg2
    have hsecond : (4 - a.a3 ^ 2) * x.x2 = 0 := by
      rw [hx3] at hg1 hg2
      linear_combination 2 * hg2 - a.a3 * hg1
    have hx1 : x.x1 = 0 :=
      (mul_eq_zero.mp hfirst).resolve_left hdet
    have hx2 : x.x2 = 0 :=
      (mul_eq_zero.mp hsecond).resolve_left hdet
    ext <;> simp [origin, hx1, hx2, hx3]

/-- There is no common fixed point in the punctured surface under the
nondegeneracy conditions. -/
theorem not_rotation1_rotation2_fixed_on_punctured
    (a : Coefficients K)
    (hmultiplier : a.multiplier ≠ 0)
    (ha1 : a.a1 ^ 2 ≠ 4) (ha2 : a.a2 ^ 2 ≠ 4)
    (ha3 : a.a3 ^ 2 ≠ 4)
    (x : PuncturedSolutionSurface a) :
    ¬(rotation1PuncturedPerm a x = x ∧
      rotation2PuncturedPerm a x = x) := by
  rintro ⟨h1, h2⟩
  have h1' : rotation1 a x.1.1 = x.1.1 := by
    exact congrArg (fun y : PuncturedSolutionSurface a => y.1.1) h1
  have h2' : rotation2 a x.1.1 = x.1.1 := by
    exact congrArg (fun y : PuncturedSolutionSurface a => y.1.1) h2
  have horigin :=
    eq_origin_of_isSolution_of_rotation1_rotation2_fixed
      a x.1.1 hmultiplier ha1 ha2 ha3 x.1.2 h1' h2'
  exact x.2 (Subtype.ext horigin)

end

end GenMarkoff.General
