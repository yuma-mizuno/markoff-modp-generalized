import GenMarkoff.Symmetric.Cage.RegularSplitFiber
import GenMarkoff.Symmetric.Opening.ReturnExponentBound

/-!
# One-step connectivity on every regular split-maximal fiber

The diagonalization argument in `RegularSplitFiber` is stated on the first
axis.  Equal coefficients allow cyclic transport to the other two axes.
This module packages those three concrete iterate statements as membership
in one component of the actual `OneStepGroup`.
-/

namespace GenMarkoff.Symmetric.Cage

noncomputable section

/-- The three coordinate axes of the symmetric surface. -/
inductive Axis
  | first
  | second
  | third
deriving DecidableEq, Fintype

/-- Coordinate selected by a cage axis. -/
def coordinateAt {R : Type*} (axis : Axis) (x : Point R) : R :=
  match axis with
  | .first => x.x1
  | .second => x.x2
  | .third => x.x3

/-- Affine trace selected by a cage axis. -/
def traceAt {R : Type*} [CommRing R]
    (c : R) (axis : Axis) (x : Point R) : R :=
  trace c (coordinateAt axis x)

/-- Membership in the selected regular split-maximal cage. -/
def IsInRegularSplitCage
    (p : ℕ) [Fact p.Prime] (c : ZMod p)
    (x : SolutionSurface (coefficients c)) : Prop :=
  ∃ axis : Axis,
    IsRegularSplitMaximalTrace p c (traceAt c axis x.1)

/-- Two surface points lie in the same component of the actual one-step
group. -/
def SameOneStepComponent
    {R : Type*} [CommRing R] (c : R)
    (x y : SolutionSurface (coefficients c)) : Prop :=
  ∃ g : OneStepGroup c, g • x = y

theorem sameOneStepComponent_refl
    {R : Type*} [CommRing R] (c : R)
    (x : SolutionSurface (coefficients c)) :
    SameOneStepComponent c x x :=
  ⟨1, one_smul _ _⟩

theorem sameOneStepComponent_symm
    {R : Type*} [CommRing R] {c : R}
    {x y : SolutionSurface (coefficients c)}
    (h : SameOneStepComponent c x y) :
    SameOneStepComponent c y x := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  exact inv_smul_smul g x

theorem sameOneStepComponent_trans
    {R : Type*} [CommRing R] {c : R}
    {x y z : SolutionSurface (coefficients c)}
    (hxy : SameOneStepComponent c x y)
    (hyz : SameOneStepComponent c y z) :
    SameOneStepComponent c x z := by
  obtain ⟨g, rfl⟩ := hxy
  obtain ⟨h, rfl⟩ := hyz
  refine ⟨h * g, ?_⟩
  exact mul_smul h g x

/-- Cyclic transport of regular split-maximal transitivity to the second
coordinate fiber. -/
theorem exists_iterate_oneStep2_eq_of_same_regularSplitMaximalFiber
    (p : ℕ) [Fact p.Prime]
    (c u t : ZMod p)
    (htrace : t = trace c u)
    (hmaximal : IsRegularSplitMaximalTrace p c t)
    (x y : Point (ZMod p))
    (hx : IsSolution (coefficients c) x) (hx2 : x.x2 = u)
    (hy : IsSolution (coefficients c) y) (hy2 : y.x2 = u) :
    ∃ n : ℕ, ((oneStep2 c)^[n]) x = y := by
  have hx' : IsSolution (coefficients c) (cycleLeftEquiv x) := by
    exact (isSolution_cycleLeftEquiv c x).2 hx
  have hy' : IsSolution (coefficients c) (cycleLeftEquiv y) := by
    exact (isSolution_cycleLeftEquiv c y).2 hy
  obtain ⟨n, hn⟩ :=
    exists_iterate_oneStep1_eq_of_same_regularSplitMaximalFiber
      p c u t htrace hmaximal (cycleLeftEquiv x) (cycleLeftEquiv y)
        hx' (by simpa using hx2) hy' (by simpa using hy2)
  refine ⟨n, ?_⟩
  apply cycleLeftEquiv.injective
  rw [cycleLeftEquiv_iterate_oneStep2]
  exact hn

/-- Cyclic transport of regular split-maximal transitivity to the third
coordinate fiber. -/
theorem exists_iterate_oneStep3_eq_of_same_regularSplitMaximalFiber
    (p : ℕ) [Fact p.Prime]
    (c u t : ZMod p)
    (htrace : t = trace c u)
    (hmaximal : IsRegularSplitMaximalTrace p c t)
    (x y : Point (ZMod p))
    (hx : IsSolution (coefficients c) x) (hx3 : x.x3 = u)
    (hy : IsSolution (coefficients c) y) (hy3 : y.x3 = u) :
    ∃ n : ℕ, ((oneStep3 c)^[n]) x = y := by
  have hx' : IsSolution (coefficients c) (cycleRightEquiv x) := by
    exact (isSolution_cycleRightEquiv c x).2 hx
  have hy' : IsSolution (coefficients c) (cycleRightEquiv y) := by
    exact (isSolution_cycleRightEquiv c y).2 hy
  obtain ⟨n, hn⟩ :=
    exists_iterate_oneStep1_eq_of_same_regularSplitMaximalFiber
      p c u t htrace hmaximal (cycleRightEquiv x) (cycleRightEquiv y)
        hx' (by simpa using hx3) hy' (by simpa using hy3)
  refine ⟨n, ?_⟩
  apply cycleRightEquiv.injective
  rw [cycleRightEquiv_iterate_oneStep3]
  exact hn

private theorem sameOneStepComponent_of_oneStep1_iterate
    {R : Type*} [CommRing R] (c : R)
    (x y : SolutionSurface (coefficients c)) (n : ℕ)
    (hxy : ((oneStep1 c)^[n]) x.1 = y.1) :
    SameOneStepComponent c x y := by
  let g : OneStepGroup c :=
    ⟨oneStep1SurfacePerm c ^ n,
      (OneStepGroup c).pow_mem
        (oneStep1SurfacePerm_mem_OneStepGroup c) n⟩
  refine ⟨g, ?_⟩
  change (g : Equiv.Perm (SolutionSurface (coefficients c))) x = y
  dsimp [g]
  rw [Equiv.Perm.coe_pow]
  apply Subtype.ext
  rw [Opening.coe_iterate_oneStep1SurfacePerm]
  exact hxy

private theorem sameOneStepComponent_of_oneStep2_iterate
    {R : Type*} [CommRing R] (c : R)
    (x y : SolutionSurface (coefficients c)) (n : ℕ)
    (hxy : ((oneStep2 c)^[n]) x.1 = y.1) :
    SameOneStepComponent c x y := by
  let g : OneStepGroup c :=
    ⟨oneStep2SurfacePerm c ^ n,
      (OneStepGroup c).pow_mem
        (oneStep2SurfacePerm_mem_OneStepGroup c) n⟩
  refine ⟨g, ?_⟩
  change (g : Equiv.Perm (SolutionSurface (coefficients c))) x = y
  dsimp [g]
  rw [Equiv.Perm.coe_pow]
  apply Subtype.ext
  rw [Opening.coe_iterate_oneStep2SurfacePerm]
  exact hxy

private theorem sameOneStepComponent_of_oneStep3_iterate
    {R : Type*} [CommRing R] (c : R)
    (x y : SolutionSurface (coefficients c)) (n : ℕ)
    (hxy : ((oneStep3 c)^[n]) x.1 = y.1) :
    SameOneStepComponent c x y := by
  let g : OneStepGroup c :=
    ⟨oneStep3SurfacePerm c ^ n,
      (OneStepGroup c).pow_mem
        (oneStep3SurfacePerm_mem_OneStepGroup c) n⟩
  refine ⟨g, ?_⟩
  change (g : Equiv.Perm (SolutionSurface (coefficients c))) x = y
  dsimp [g]
  rw [Equiv.Perm.coe_pow]
  apply Subtype.ext
  rw [Opening.coe_iterate_oneStep3SurfacePerm]
  exact hxy

/-- Any two actual surface points in the same regular split-maximal fiber,
on any coordinate axis, lie in the same one-step component. -/
theorem sameOneStepComponent_of_same_regularSplitMaximalFiber
    (p : ℕ) [Fact p.Prime]
    (c u t : ZMod p)
    (htrace : t = trace c u)
    (hmaximal : IsRegularSplitMaximalTrace p c t)
    (axis : Axis)
    (x y : SolutionSurface (coefficients c))
    (hx : coordinateAt axis x.1 = u)
    (hy : coordinateAt axis y.1 = u) :
    SameOneStepComponent c x y := by
  cases axis with
  | first =>
      obtain ⟨n, hn⟩ :=
        exists_iterate_oneStep1_eq_of_same_regularSplitMaximalFiber
          p c u t htrace hmaximal x.1 y.1 x.property hx
            y.property hy
      exact sameOneStepComponent_of_oneStep1_iterate c x y n hn
  | second =>
      obtain ⟨n, hn⟩ :=
        exists_iterate_oneStep2_eq_of_same_regularSplitMaximalFiber
          p c u t htrace hmaximal x.1 y.1 x.property hx
            y.property hy
      exact sameOneStepComponent_of_oneStep2_iterate c x y n hn
  | third =>
      obtain ⟨n, hn⟩ :=
        exists_iterate_oneStep3_eq_of_same_regularSplitMaximalFiber
          p c u t htrace hmaximal x.1 y.1 x.property hx
            y.property hy
      exact sameOneStepComponent_of_oneStep3_iterate c x y n hn

end

end GenMarkoff.Symmetric.Cage
