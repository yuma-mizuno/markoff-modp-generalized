import GenMarkoff.General.FiberDynamics

/-!
# Explicit axes for the fixed-coefficient general surface

The general proof must distinguish all coordinate directions without using a
coordinate permutation as a surface symmetry.  This file provides a small
axis-indexed API while keeping every map attached to the original coefficient
triple.
-/

namespace GenMarkoff.General

universe u

/-- The three coordinate axes of the fixed generalized surface. -/
inductive Axis
  | first
  | second
  | third
deriving DecidableEq, Fintype, Repr

/-- The cyclic successor axis. -/
def Axis.next : Axis → Axis
  | .first => .second
  | .second => .third
  | .third => .first

/-- The cyclic predecessor axis. -/
def Axis.previous : Axis → Axis
  | .first => .third
  | .second => .first
  | .third => .second

@[simp]
theorem Axis.next_previous (axis : Axis) :
    axis.previous.next = axis := by
  cases axis <;> rfl

@[simp]
theorem Axis.previous_next (axis : Axis) :
    axis.next.previous = axis := by
  cases axis <;> rfl

@[simp]
theorem Axis.next_ne (axis : Axis) : axis.next ≠ axis := by
  cases axis <;> decide

@[simp]
theorem Axis.previous_ne (axis : Axis) : axis.previous ≠ axis := by
  cases axis <;> decide

/-- One of the six directed choices of a fixed axis and a distinct target
axis.  Keeping these choices explicit prevents accidental use of a coordinate
permutation as a symmetry of the fixed surface. -/
inductive DirectedAxes
  | firstSecond
  | firstThird
  | secondFirst
  | secondThird
  | thirdFirst
  | thirdSecond
deriving DecidableEq, Fintype, Repr

/-- Fixed axis of a directed choice. -/
def DirectedAxes.fixed : DirectedAxes → Axis
  | .firstSecond | .firstThird => .first
  | .secondFirst | .secondThird => .second
  | .thirdFirst | .thirdSecond => .third

/-- Target axis of a directed choice. -/
def DirectedAxes.target : DirectedAxes → Axis
  | .firstSecond => .second
  | .firstThird => .third
  | .secondFirst => .first
  | .secondThird => .third
  | .thirdFirst => .first
  | .thirdSecond => .second

/-- The third axis in a directed choice. -/
def DirectedAxes.remaining : DirectedAxes → Axis
  | .firstSecond | .secondFirst => .third
  | .firstThird | .thirdFirst => .second
  | .secondThird | .thirdSecond => .first

/-- Reverse the directed choice. -/
def DirectedAxes.reverse : DirectedAxes → DirectedAxes
  | .firstSecond => .secondFirst
  | .firstThird => .thirdFirst
  | .secondFirst => .firstSecond
  | .secondThird => .thirdSecond
  | .thirdFirst => .firstThird
  | .thirdSecond => .secondThird

@[simp]
theorem DirectedAxes.reverse_reverse (axes : DirectedAxes) :
    axes.reverse.reverse = axes := by
  cases axes <;> rfl

@[simp]
theorem DirectedAxes.fixed_reverse (axes : DirectedAxes) :
    axes.reverse.fixed = axes.target := by
  cases axes <;> rfl

@[simp]
theorem DirectedAxes.target_reverse (axes : DirectedAxes) :
    axes.reverse.target = axes.fixed := by
  cases axes <;> rfl

@[simp]
theorem DirectedAxes.fixed_ne_target (axes : DirectedAxes) :
    axes.fixed ≠ axes.target := by
  cases axes <;> decide

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

/-- The ordered coefficient frame `(A,B,C)` attached to a directed axis
choice.  This is parameter bookkeeping only; it does not act on points or
assert a symmetry of the surface. -/
def directedCoefficients {R : Type u}
    (a : Coefficients R) (axes : DirectedAxes) : Coefficients R :=
  ⟨coefficientAt axes.fixed a, coefficientAt axes.target a,
    coefficientAt axes.remaining a⟩

/-- The affine trace attached to a selected coordinate. -/
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

/-- Point-level rotation selected by an axis. -/
def rotationAt {R : Type u} [CommRing R]
    (a : Coefficients R) : Axis → Point R → Point R
  | .first => rotation1 a
  | .second => rotation2 a
  | .third => rotation3 a

/-- Surface permutation selected by an axis. -/
def rotationSurfacePermAt {R : Type u} [CommRing R]
    (a : Coefficients R) : Axis → Equiv.Perm (SolutionSurface a)
  | .first => rotation1SurfacePerm a
  | .second => rotation2SurfacePerm a
  | .third => rotation3SurfacePerm a

/-- Punctured-surface permutation selected by an axis. -/
def rotationPuncturedPermAt {R : Type u} [CommRing R]
    (a : Coefficients R) : Axis → Equiv.Perm (PuncturedSolutionSurface a)
  | .first => rotation1PuncturedPerm a
  | .second => rotation2PuncturedPerm a
  | .third => rotation3PuncturedPerm a

theorem rotationSurfacePermAt_mem_RotationGroup
    {R : Type u} [CommRing R] (a : Coefficients R) (axis : Axis) :
    rotationSurfacePermAt a axis ∈ RotationGroup a := by
  cases axis with
  | first => exact rotation1SurfacePerm_mem_RotationGroup a
  | second => exact rotation2SurfacePerm_mem_RotationGroup a
  | third => exact rotation3SurfacePerm_mem_RotationGroup a

/-- The order of the selected actual rotation linear part. -/
noncomputable def rotationLinearOrderAt
    {R : Type u} [CommRing R]
    (a : Coefficients R) (axis : Axis) (x : Point R) : ℕ :=
  rotationLinearOrder (traceAt a axis x)

/-- Two surface points lie in the same component of the fixed-coefficient
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

/-- One application of a selected rotation stays in the same rotation
component. -/
theorem sameRotationComponent_rotationSurfacePermAt
    {R : Type u} [CommRing R] (a : Coefficients R)
    (axis : Axis) (x : SolutionSurface a) :
    SameRotationComponent x (rotationSurfacePermAt a axis x) := by
  let g : RotationGroup a :=
    ⟨rotationSurfacePermAt a axis,
      rotationSurfacePermAt_mem_RotationGroup a axis⟩
  exact ⟨g, rfl⟩

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
  change (rotationSurfacePermAt a axis ^ n) x =
    ((rotationSurfacePermAt a axis)^[n] x)
  rw [Equiv.Perm.coe_pow]

end GenMarkoff.General
