import GenMarkoff.General.Axis

/-!
# Rotation components and punctured orbits

This file records the mechanical interface between the component relation on
the fixed-coefficient solution surface and the orbit relation on the punctured
surface.  No coordinate permutation is used: both sides use the same explicit
coefficient triple and the same `RotationGroup`.
-/

namespace GenMarkoff.General

universe u

/-- Forgetting the puncture proof commutes with the rotation-group action. -/
@[simp]
theorem coe_rotationGroup_smul_punctured
    {R : Type u} [CommRing R] {a : Coefficients R}
    (g : RotationGroup a) (x : PuncturedSolutionSurface a) :
    (g • x).1 = g • x.1 :=
  rfl

/-- Membership in a punctured rotation orbit is exactly membership in the
corresponding rotation component on the underlying fixed-coefficient
solution surface. -/
theorem mem_puncturedRotationOrbit_iff_sameRotationComponent
    {R : Type u} [CommRing R] {a : Coefficients R}
    (x y : PuncturedSolutionSurface a) :
    y ∈ puncturedRotationOrbit x ↔
      SameRotationComponent x.1 y.1 := by
  constructor
  · intro hy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
    refine ⟨g, ?_⟩
    exact congrArg Subtype.val hg
  · rintro ⟨g, hg⟩
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact hg

/-- Direct component connectivity from one punctured base point implies
rotation strong approximation at the given prime. -/
theorem rotationStrongApproximationAt_of_sameRotationComponent_base
    (a : Coefficients ℤ) (p : ℕ) (hp : p.Prime)
    (base : PuncturedSolutionSurface (modCoefficients a p))
    (hconnected :
      ∀ x : PuncturedSolutionSurface (modCoefficients a p),
        SameRotationComponent base.1 x.1) :
    RotationStrongApproximationAt a p hp := by
  letI : Fact p.Prime := ⟨hp⟩
  intro x y
  obtain ⟨g, hg⟩ :=
    sameRotationComponent_trans
      (sameRotationComponent_symm (hconnected x)) (hconnected y)
  refine ⟨g, ?_⟩
  apply Subtype.ext
  exact hg

end GenMarkoff.General
