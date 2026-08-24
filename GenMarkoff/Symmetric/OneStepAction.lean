import GenMarkoff.Symmetric.FiberDynamics

/-!
# The symmetry-enabled one-step action

When all three coefficients are equal, coordinate transpositions preserve the
fixed generalized Markoff surface.  Composing a Vieta involution with the
appropriate transposition gives the affine half-step on a conic fiber.  Its
square is the two-Vieta rotation used by the general fixed-coefficient action.
-/

namespace GenMarkoff.Symmetric

universe u

section PointAction

variable {R : Type u}

/-- Transpose the second and third coordinates. -/
def swap23 (x : Point R) : Point R :=
  ⟨x.x1, x.x3, x.x2⟩

/-- Transpose the first and third coordinates. -/
def swap13 (x : Point R) : Point R :=
  ⟨x.x3, x.x2, x.x1⟩

/-- Transpose the first and second coordinates. -/
def swap12 (x : Point R) : Point R :=
  ⟨x.x2, x.x1, x.x3⟩

@[simp]
theorem swap23_involutive (x : Point R) : swap23 (swap23 x) = x := by
  rfl

@[simp]
theorem swap13_involutive (x : Point R) : swap13 (swap13 x) = x := by
  rfl

@[simp]
theorem swap12_involutive (x : Point R) : swap12 (swap12 x) = x := by
  rfl

/-- The transposition of the second and third coordinates. -/
def swap23Equiv : Equiv.Perm (Point R) where
  toFun := swap23
  invFun := swap23
  left_inv := swap23_involutive
  right_inv := swap23_involutive

/-- The transposition of the first and third coordinates. -/
def swap13Equiv : Equiv.Perm (Point R) where
  toFun := swap13
  invFun := swap13
  left_inv := swap13_involutive
  right_inv := swap13_involutive

/-- The transposition of the first and second coordinates. -/
def swap12Equiv : Equiv.Perm (Point R) where
  toFun := swap12
  invFun := swap12
  left_inv := swap12_involutive
  right_inv := swap12_involutive

variable [CommRing R]

theorem polynomial_swap23 (c : R) (x : Point R) :
    polynomial (coefficients c) (swap23 x) =
      polynomial (coefficients c) x := by
  simp [polynomial, coefficients, swap23, Coefficients.multiplier]
  ring

theorem polynomial_swap13 (c : R) (x : Point R) :
    polynomial (coefficients c) (swap13 x) =
      polynomial (coefficients c) x := by
  simp [polynomial, coefficients, swap13, Coefficients.multiplier]
  ring

theorem polynomial_swap12 (c : R) (x : Point R) :
    polynomial (coefficients c) (swap12 x) =
      polynomial (coefficients c) x := by
  simp [polynomial, coefficients, swap12, Coefficients.multiplier]
  ring

@[simp]
theorem isSolution_swap23 (c : R) (x : Point R) :
    IsSolution (coefficients c) (swap23 x) ↔
      IsSolution (coefficients c) x := by
  simp only [IsSolution, polynomial_swap23]

@[simp]
theorem isSolution_swap13 (c : R) (x : Point R) :
    IsSolution (coefficients c) (swap13 x) ↔
      IsSolution (coefficients c) x := by
  simp only [IsSolution, polynomial_swap13]

@[simp]
theorem isSolution_swap12 (c : R) (x : Point R) :
    IsSolution (coefficients c) (swap12 x) ↔
      IsSolution (coefficients c) x := by
  simp only [IsSolution, polynomial_swap12]

/-- The one-step generator fixing the first coordinate. -/
def oneStep1 (c : R) (x : Point R) : Point R :=
  swap23 (vieta2 (coefficients c) x)

/-- The one-step generator fixing the second coordinate. -/
def oneStep2 (c : R) (x : Point R) : Point R :=
  swap13 (vieta3 (coefficients c) x)

/-- The one-step generator fixing the third coordinate. -/
def oneStep3 (c : R) (x : Point R) : Point R :=
  swap12 (vieta1 (coefficients c) x)

theorem polynomial_oneStep1 (c : R) (x : Point R) :
    polynomial (coefficients c) (oneStep1 c x) =
      polynomial (coefficients c) x := by
  rw [oneStep1, polynomial_swap23, polynomial_vieta2]

theorem polynomial_oneStep2 (c : R) (x : Point R) :
    polynomial (coefficients c) (oneStep2 c x) =
      polynomial (coefficients c) x := by
  rw [oneStep2, polynomial_swap13, polynomial_vieta3]

theorem polynomial_oneStep3 (c : R) (x : Point R) :
    polynomial (coefficients c) (oneStep3 c x) =
      polynomial (coefficients c) x := by
  rw [oneStep3, polynomial_swap12, polynomial_vieta1]

@[simp]
theorem isSolution_oneStep1 (c : R) (x : Point R) :
    IsSolution (coefficients c) (oneStep1 c x) ↔
      IsSolution (coefficients c) x := by
  simp only [IsSolution, polynomial_oneStep1]

@[simp]
theorem isSolution_oneStep2 (c : R) (x : Point R) :
    IsSolution (coefficients c) (oneStep2 c x) ↔
      IsSolution (coefficients c) x := by
  simp only [IsSolution, polynomial_oneStep2]

@[simp]
theorem isSolution_oneStep3 (c : R) (x : Point R) :
    IsSolution (coefficients c) (oneStep3 c x) ↔
      IsSolution (coefficients c) x := by
  simp only [IsSolution, polynomial_oneStep3]

/-- The first one-step point permutation. -/
def oneStep1Equiv (c : R) : Equiv.Perm (Point R) :=
  (vieta2Equiv R (coefficients c)).trans swap23Equiv

/-- The second one-step point permutation. -/
def oneStep2Equiv (c : R) : Equiv.Perm (Point R) :=
  (vieta3Equiv R (coefficients c)).trans swap13Equiv

/-- The third one-step point permutation. -/
def oneStep3Equiv (c : R) : Equiv.Perm (Point R) :=
  (vieta1Equiv R (coefficients c)).trans swap12Equiv

@[simp]
theorem coe_oneStep1Equiv (c : R) (x : Point R) :
    oneStep1Equiv c x = oneStep1 c x :=
  rfl

@[simp]
theorem coe_oneStep2Equiv (c : R) (x : Point R) :
    oneStep2Equiv c x = oneStep2 c x :=
  rfl

@[simp]
theorem coe_oneStep3Equiv (c : R) (x : Point R) :
    oneStep3Equiv c x = oneStep3 c x :=
  rfl

/-- The first one-step map is exactly the affine fiber step. -/
theorem movingCoordinates1_oneStep1 (c : R) (x : Point R) :
    movingCoordinates1 (oneStep1 c x) =
      fiberStep c x.x1 (movingCoordinates1 x) := by
  ext
  all_goals
    simp [movingCoordinates1, oneStep1, swap23, vieta2, fiberStep,
      affineStep, trace, multiplier, coefficients, Coefficients.multiplier] <;>
      ring

/-- The second one-step map is exactly the affine fiber step. -/
theorem movingCoordinates2_oneStep2 (c : R) (x : Point R) :
    movingCoordinates2 (oneStep2 c x) =
      fiberStep c x.x2 (movingCoordinates2 x) := by
  ext
  all_goals
    simp [movingCoordinates2, oneStep2, swap13, vieta3, fiberStep,
      affineStep, trace, multiplier, coefficients, Coefficients.multiplier] <;>
      ring

/-- The third one-step map is exactly the affine fiber step. -/
theorem movingCoordinates3_oneStep3 (c : R) (x : Point R) :
    movingCoordinates3 (oneStep3 c x) =
      fiberStep c x.x3 (movingCoordinates3 x) := by
  ext
  all_goals
    simp [movingCoordinates3, oneStep3, swap12, vieta1, fiberStep,
      affineStep, trace, multiplier, coefficients, Coefficients.multiplier] <;>
      ring

/-- Squaring the first one-step map gives the original first rotation. -/
theorem oneStep1_sq (c : R) (x : Point R) :
    oneStep1 c (oneStep1 c x) = rotation1 (coefficients c) x := by
  ext
  all_goals
    simp [oneStep1, swap23, rotation1, vieta2, vieta3, coefficients,
      Coefficients.multiplier] <;>
      ring

/-- Squaring the second one-step map gives the original second rotation. -/
theorem oneStep2_sq (c : R) (x : Point R) :
    oneStep2 c (oneStep2 c x) = rotation2 (coefficients c) x := by
  ext
  all_goals
    simp [oneStep2, swap13, rotation2, vieta1, vieta3, coefficients,
      Coefficients.multiplier] <;>
      ring

/-- Squaring the third one-step map gives the original third rotation. -/
theorem oneStep3_sq (c : R) (x : Point R) :
    oneStep3 c (oneStep3 c x) = rotation3 (coefficients c) x := by
  ext
  all_goals
    simp [oneStep3, swap12, rotation3, vieta1, vieta2, coefficients,
      Coefficients.multiplier] <;>
      ring

end PointAction

section SurfaceAction

variable {R : Type u} [CommRing R]

/-- The first one-step permutation restricted to the symmetric surface. -/
def oneStep1SurfacePerm (c : R) :
    Equiv.Perm (SolutionSurface (coefficients c)) where
  __ := (oneStep1Equiv c).subtypeEquiv fun x =>
    (isSolution_oneStep1 c x).symm

/-- The second one-step permutation restricted to the symmetric surface. -/
def oneStep2SurfacePerm (c : R) :
    Equiv.Perm (SolutionSurface (coefficients c)) where
  __ := (oneStep2Equiv c).subtypeEquiv fun x =>
    (isSolution_oneStep2 c x).symm

/-- The third one-step permutation restricted to the symmetric surface. -/
def oneStep3SurfacePerm (c : R) :
    Equiv.Perm (SolutionSurface (coefficients c)) where
  __ := (oneStep3Equiv c).subtypeEquiv fun x =>
    (isSolution_oneStep3 c x).symm

@[simp]
theorem coe_oneStep1SurfacePerm (c : R)
    (x : SolutionSurface (coefficients c)) :
    ((oneStep1SurfacePerm c x : SolutionSurface (coefficients c)) : Point R) =
      oneStep1 c x :=
  rfl

@[simp]
theorem coe_oneStep2SurfacePerm (c : R)
    (x : SolutionSurface (coefficients c)) :
    ((oneStep2SurfacePerm c x : SolutionSurface (coefficients c)) : Point R) =
      oneStep2 c x :=
  rfl

@[simp]
theorem coe_oneStep3SurfacePerm (c : R)
    (x : SolutionSurface (coefficients c)) :
    ((oneStep3SurfacePerm c x : SolutionSurface (coefficients c)) : Point R) =
      oneStep3 c x :=
  rfl

theorem oneStep1SurfacePerm_sq (c : R) :
    oneStep1SurfacePerm c ^ 2 =
      rotation1SurfacePerm (coefficients c) := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change oneStep1 c (oneStep1 c x.1) = rotation1 (coefficients c) x.1
  exact oneStep1_sq c x

theorem oneStep2SurfacePerm_sq (c : R) :
    oneStep2SurfacePerm c ^ 2 =
      rotation2SurfacePerm (coefficients c) := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change oneStep2 c (oneStep2 c x.1) = rotation2 (coefficients c) x.1
  exact oneStep2_sq c x

theorem oneStep3SurfacePerm_sq (c : R) :
    oneStep3SurfacePerm c ^ 2 =
      rotation3SurfacePerm (coefficients c) := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change oneStep3 c (oneStep3 c x.1) = rotation3 (coefficients c) x.1
  exact oneStep3_sq c x

/-- The three symmetry-enabled one-step generators. -/
def oneStepGenerators (c : R) :
    Set (Equiv.Perm (SolutionSurface (coefficients c))) :=
  {oneStep1SurfacePerm c, oneStep2SurfacePerm c, oneStep3SurfacePerm c}

/-- The group generated by the three one-step fiber maps. -/
def OneStepGroup (c : R) :
    Subgroup (Equiv.Perm (SolutionSurface (coefficients c))) :=
  Subgroup.closure (oneStepGenerators c)

theorem oneStep1SurfacePerm_mem_OneStepGroup (c : R) :
    oneStep1SurfacePerm c ∈ OneStepGroup c :=
  Subgroup.subset_closure (by simp [oneStepGenerators])

theorem oneStep2SurfacePerm_mem_OneStepGroup (c : R) :
    oneStep2SurfacePerm c ∈ OneStepGroup c :=
  Subgroup.subset_closure (by simp [oneStepGenerators])

theorem oneStep3SurfacePerm_mem_OneStepGroup (c : R) :
    oneStep3SurfacePerm c ∈ OneStepGroup c :=
  Subgroup.subset_closure (by simp [oneStepGenerators])

theorem rotation1SurfacePerm_mem_OneStepGroup (c : R) :
    rotation1SurfacePerm (coefficients c) ∈ OneStepGroup c := by
  rw [← oneStep1SurfacePerm_sq]
  exact (OneStepGroup c).pow_mem (oneStep1SurfacePerm_mem_OneStepGroup c) 2

theorem rotation2SurfacePerm_mem_OneStepGroup (c : R) :
    rotation2SurfacePerm (coefficients c) ∈ OneStepGroup c := by
  rw [← oneStep2SurfacePerm_sq]
  exact (OneStepGroup c).pow_mem (oneStep2SurfacePerm_mem_OneStepGroup c) 2

theorem rotation3SurfacePerm_mem_OneStepGroup (c : R) :
    rotation3SurfacePerm (coefficients c) ∈ OneStepGroup c := by
  rw [← oneStep3SurfacePerm_sq]
  exact (OneStepGroup c).pow_mem (oneStep3SurfacePerm_mem_OneStepGroup c) 2

/-- The original two-Vieta rotation group is contained in the one-step group. -/
theorem RotationGroup_le_OneStepGroup (c : R) :
    RotationGroup (coefficients c) ≤ OneStepGroup c := by
  refine (Subgroup.closure_le _).2 ?_
  intro g hg
  simp only [rotationGenerators, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact rotation1SurfacePerm_mem_OneStepGroup c
  · exact rotation2SurfacePerm_mem_OneStepGroup c
  · exact rotation3SurfacePerm_mem_OneStepGroup c

@[simp]
theorem oneStep1SurfacePerm_surfaceOrigin (c : R) :
    oneStep1SurfacePerm c (surfaceOrigin (coefficients c)) =
      surfaceOrigin (coefficients c) := by
  apply Subtype.ext
  change oneStep1 c (origin : Point R) = origin
  ext <;> simp [oneStep1, swap23, vieta2, origin]

@[simp]
theorem oneStep2SurfacePerm_surfaceOrigin (c : R) :
    oneStep2SurfacePerm c (surfaceOrigin (coefficients c)) =
      surfaceOrigin (coefficients c) := by
  apply Subtype.ext
  change oneStep2 c (origin : Point R) = origin
  ext <;> simp [oneStep2, swap13, vieta3, origin]

@[simp]
theorem oneStep3SurfacePerm_surfaceOrigin (c : R) :
    oneStep3SurfacePerm c (surfaceOrigin (coefficients c)) =
      surfaceOrigin (coefficients c) := by
  apply Subtype.ext
  change oneStep3 c (origin : Point R) = origin
  ext <;> simp [oneStep3, swap12, vieta1, origin]

theorem oneStepGenerator_fixes_origin (c : R)
    {g : Equiv.Perm (SolutionSurface (coefficients c))}
    (hg : g ∈ oneStepGenerators c) :
    g (surfaceOrigin (coefficients c)) =
      surfaceOrigin (coefficients c) := by
  simp only [oneStepGenerators, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl <;> simp

theorem OneStepGroup_le_origin_stabilizer (c : R) :
    OneStepGroup c ≤
      MulAction.stabilizer
        (Equiv.Perm (SolutionSurface (coefficients c)))
        (surfaceOrigin (coefficients c)) :=
  (Subgroup.closure_le _).2 fun _ hg => oneStepGenerator_fixes_origin c hg

@[simp]
theorem OneStepGroup_fixes_surfaceOrigin (c : R) (g : OneStepGroup c) :
    g • surfaceOrigin (coefficients c) =
      surfaceOrigin (coefficients c) :=
  OneStepGroup_le_origin_stabilizer c g.2

/-- The one-step action restricted to the punctured symmetric surface. -/
instance {c : R} :
    MulAction (OneStepGroup c)
      (PuncturedSolutionSurface (coefficients c)) where
  smul g x :=
    ⟨g • x.1, fun hgx => x.2 <| by
      calc
        x.1 = g⁻¹ • (g • x.1) := (inv_smul_smul g x.1).symm
        _ = g⁻¹ • surfaceOrigin (coefficients c) :=
          congrArg (g⁻¹ • ·) hgx
        _ = surfaceOrigin (coefficients c) :=
          OneStepGroup_fixes_surfaceOrigin c g⁻¹⟩
  one_smul x := Subtype.ext (one_smul (OneStepGroup c) x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

/-- The orbit of a punctured symmetric point under the one-step group. -/
def puncturedOneStepOrbit {c : R}
    (x : PuncturedSolutionSurface (coefficients c)) :
    Set (PuncturedSolutionSurface (coefficients c)) :=
  MulAction.orbit (OneStepGroup c) x

end SurfaceAction

end GenMarkoff.Symmetric
