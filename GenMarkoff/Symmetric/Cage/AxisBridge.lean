import GenMarkoff.Symmetric.Cage.FiberConnectivity

/-!
# Axis transport for symmetric cage bridges

Equal coefficients permit coordinate relabeling of the two concrete
trace-incidence points.  The relabeling is used only to place their prescribed
outer and middle coordinates; connectivity still comes from actual
`oneStep1`, `oneStep2`, and `oneStep3` iterates.
-/

namespace GenMarkoff.Symmetric.Cage

noncomputable section

/-- Choose a middle axis different from both prescribed outer axes. -/
def bridgeAxis : Axis → Axis → Axis
  | .first, .first => .second
  | .first, .second => .third
  | .first, .third => .second
  | .second, .first => .third
  | .second, .second => .first
  | .second, .third => .first
  | .third, .first => .second
  | .third, .second => .first
  | .third, .third => .first

theorem bridgeAxis_ne_left (axis other : Axis) :
    bridgeAxis axis other ≠ axis := by
  cases axis <;> cases other <;> decide

theorem bridgeAxis_ne_right (axis other : Axis) :
    bridgeAxis axis other ≠ other := by
  cases axis <;> cases other <;> decide

/-- Place the first and second coordinates of a point on any ordered pair of
distinct axes.  Values on the unused diagonal cases are irrelevant. -/
def placeFirstSecond {R : Type*}
    (outer middle : Axis) (x : Point R) : Point R :=
  match outer, middle with
  | .first, .first => x
  | .first, .second => x
  | .first, .third => swap23 x
  | .second, .first => swap12 x
  | .second, .second => x
  | .second, .third => cycleRightEquiv x
  | .third, .first => cycleLeftEquiv x
  | .third, .second => swap13 x
  | .third, .third => x

theorem coordinateAt_placeFirstSecond_outer
    {R : Type*} (outer middle : Axis) (x : Point R)
    (hne : outer ≠ middle) :
    coordinateAt outer (placeFirstSecond outer middle x) = x.x1 := by
  cases outer <;> cases middle <;>
    simp [placeFirstSecond, coordinateAt, swap23, swap12, swap13] at hne ⊢

theorem coordinateAt_placeFirstSecond_middle
    {R : Type*} (outer middle : Axis) (x : Point R)
    (hne : outer ≠ middle) :
    coordinateAt middle (placeFirstSecond outer middle x) = x.x2 := by
  cases outer <;> cases middle <;>
    simp [placeFirstSecond, coordinateAt, swap23, swap12, swap13] at hne ⊢

theorem isSolution_placeFirstSecond
    {R : Type*} [CommRing R] (c : R)
    (outer middle : Axis) (x : Point R)
    (hne : outer ≠ middle)
    (hx : IsSolution (coefficients c) x) :
    IsSolution (coefficients c) (placeFirstSecond outer middle x) := by
  cases outer <;> cases middle
  · exact (hne rfl).elim
  · exact hx
  · exact (isSolution_swap23 c x).2 hx
  · exact (isSolution_swap12 c x).2 hx
  · exact (hne rfl).elim
  · exact (isSolution_cycleRightEquiv c x).2 hx
  · exact (isSolution_cycleLeftEquiv c x).2 hx
  · exact (isSolution_swap13 c x).2 hx
  · exact (hne rfl).elim

/-- Coordinate placement lifted to the actual symmetric solution surface. -/
def placeFirstSecondSurface
    {R : Type*} [CommRing R] (c : R)
    (outer middle : Axis) (hne : outer ≠ middle)
    (x : SolutionSurface (coefficients c)) :
    SolutionSurface (coefficients c) :=
  ⟨placeFirstSecond outer middle x.1,
    isSolution_placeFirstSecond c outer middle x.1 hne x.property⟩

@[simp]
theorem coordinateAt_placeFirstSecondSurface_outer
    {R : Type*} [CommRing R] (c : R)
    (outer middle : Axis) (hne : outer ≠ middle)
    (x : SolutionSurface (coefficients c)) :
    coordinateAt outer (placeFirstSecondSurface c outer middle hne x).1 =
      x.1.x1 :=
  coordinateAt_placeFirstSecond_outer outer middle x.1 hne

@[simp]
theorem coordinateAt_placeFirstSecondSurface_middle
    {R : Type*} [CommRing R] (c : R)
    (outer middle : Axis) (hne : outer ≠ middle)
    (x : SolutionSurface (coefficients c)) :
    coordinateAt middle (placeFirstSecondSurface c outer middle hne x).1 =
      x.1.x2 :=
  coordinateAt_placeFirstSecond_middle outer middle x.1 hne

end

end GenMarkoff.Symmetric.Cage
