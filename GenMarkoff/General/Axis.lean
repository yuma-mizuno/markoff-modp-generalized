import GenMarkoff.General.FiberDynamics

/-!
# Explicit axes for the fixed-coefficient general surface

The argument must distinguish all coordinate directions without using a
coordinate permutation as a surface symmetry.  This file provides a small
axis-indexed API, keeping every map attached to the original coefficient
triple: the type `Axis`, the coordinate, coefficient and affine trace
`traceAt` selected by an axis, the rotation `rotationSurfacePermAt` fixing
that coordinate together with the order `rotationLinearOrderAt` of its linear
part, and the equivalence relation `SameRotationComponent` of lying in one
rotation-group orbit.
-/

namespace GenMarkoff.General

universe u

/-- The three coordinate axes of the fixed generalized surface. -/
inductive Axis
  | first
  | second
  | third
deriving DecidableEq, Repr

instance : Fintype Axis :=
  ⟨{.first, .second, .third}, fun x ↦ by cases x <;> simp⟩

/-- Coordinate selected by an axis. -/
def coordinateAt {R : Type u} (axis : Axis) (x : Point R) : R :=
  match axis with
  | .first => x.x1
  | .second => x.x2
  | .third => x.x3

/-- Coefficient attached to the selected coordinate. -/
def coefficientAt {R : Type u} (axis : Axis) (a : Coefficients R) : R :=
  match axis with
  | .first => a.a1
  | .second => a.a2
  | .third => a.a3

/-- The affine trace `s * xᵢ - aᵢ` attached to the selected coordinate. -/
def traceAt {R : Type u} [CommRing R]
    (a : Coefficients R) (axis : Axis) (x : Point R) : R :=
  orderedTrace a.multiplier (coefficientAt axis a) (coordinateAt axis x)

@[simp]
theorem traceAt_first {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    traceAt a .first x = a.multiplier * x.x1 - a.a1 :=
  rfl

@[simp]
theorem traceAt_second {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    traceAt a .second x = a.multiplier * x.x2 - a.a2 :=
  rfl

@[simp]
theorem traceAt_third {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    traceAt a .third x = a.multiplier * x.x3 - a.a3 :=
  rfl

/-- The two-Vieta rotation of the surface that fixes the coordinate selected by
an axis. -/
def rotationSurfacePermAt {R : Type u} [CommRing R]
    (a : Coefficients R) : Axis → Equiv.Perm (SolutionSurface a)
  | .first => rotation1SurfacePerm a
  | .second => rotation2SurfacePerm a
  | .third => rotation3SurfacePerm a

theorem rotationSurfacePermAt_mem_RotationGroup
    {R : Type u} [CommRing R] (a : Coefficients R) (axis : Axis) :
    rotationSurfacePermAt a axis ∈ RotationGroup a := by
  cases axis with
  | first => exact rotation1SurfacePerm_mem_RotationGroup a
  | second => exact rotation2SurfacePerm_mem_RotationGroup a
  | third => exact rotation3SurfacePerm_mem_RotationGroup a

/-- The order of the linear part of the rotation fixing the selected
coordinate, as a function of the trace `traceAt a axis x`. -/
noncomputable def rotationLinearOrderAt
    {R : Type u} [CommRing R]
    (a : Coefficients R) (axis : Axis) (x : Point R) : ℕ :=
  rotationLinearOrder (traceAt a axis x)

/-- Two surface points lie in the same orbit of the fixed-coefficient
rotation group. -/
def SameRotationComponent
    {R : Type u} [CommRing R] {a : Coefficients R}
    (x y : SolutionSurface a) : Prop :=
  ∃ g : RotationGroup a, g • x = y

theorem sameRotationComponent_refl
    {R : Type u} [CommRing R] {a : Coefficients R}
    (x : SolutionSurface a) :
    SameRotationComponent x x :=
  ⟨1, one_smul _ _⟩

theorem sameRotationComponent_symm
    {R : Type u} [CommRing R] {a : Coefficients R}
    {x y : SolutionSurface a}
    (h : SameRotationComponent x y) :
    SameRotationComponent y x := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨g⁻¹, inv_smul_smul g x⟩

theorem sameRotationComponent_trans
    {R : Type u} [CommRing R] {a : Coefficients R}
    {x y z : SolutionSurface a}
    (hxy : SameRotationComponent x y)
    (hyz : SameRotationComponent y z) :
    SameRotationComponent x z := by
  obtain ⟨g, rfl⟩ := hxy
  obtain ⟨h, rfl⟩ := hyz
  exact ⟨h * g, mul_smul h g x⟩

/-- Every iterate of a selected rotation stays in the same component. -/
theorem sameRotationComponent_iterate_rotationSurfacePermAt
    {R : Type u} [CommRing R] (a : Coefficients R)
    (axis : Axis) (x : SolutionSurface a) (n : ℕ) :
    SameRotationComponent x
      ((rotationSurfacePermAt a axis)^[n] x) := by
  let g : RotationGroup a :=
    ⟨rotationSurfacePermAt a axis ^ n,
      (RotationGroup a).pow_mem
        (rotationSurfacePermAt_mem_RotationGroup a axis) n⟩
  refine ⟨g, ?_⟩
  -- `g • x` is the underlying permutation `rotationSurfacePermAt a axis ^ n`
  -- applied to `x`; restate so that `Equiv.Perm.coe_pow` turns it into the iterate.
  change (rotationSurfacePermAt a axis ^ n) x =
    ((rotationSurfacePermAt a axis)^[n] x)
  rw [Equiv.Perm.coe_pow]

end GenMarkoff.General
