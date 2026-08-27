import GenMarkoff.Core.Basic

/-!
# Vieta and rotation-group actions

The rotation graph uses the even words `Rᵢ = μᵢ₋₁ ∘ μᵢ₊₁`, while
arXiv:2509.02187v3 proves divisibility for orbits of the individual Vieta
moves.  Both actions are therefore kept as distinct objects.
-/

namespace GenMarkoff

universe u

/-- The generalized Markoff surface as a subtype. -/
abbrev SolutionSurface {R : Type u} [CommRing R] (a : Coefficients R) :=
  {x : Point R // IsSolution a x}

/-- The origin as a point of the generalized Markoff surface. -/
def surfaceOrigin {R : Type u} [CommRing R] (a : Coefficients R) : SolutionSurface a :=
  ⟨origin, isSolution_origin a⟩

/-- `(1,1,1)` as a point of the generalized Markoff surface. -/
def surfaceUnit {R : Type u} [CommRing R] (a : Coefficients R) : SolutionSurface a :=
  ⟨unitPoint, isSolution_unitPoint a⟩

theorem surfaceUnit_ne_surfaceOrigin {R : Type u} [CommRing R] [Nontrivial R]
    (a : Coefficients R) : surfaceUnit a ≠ surfaceOrigin a := by
  intro h
  exact unitPoint_ne_origin (congrArg Subtype.val h)

/-- The first Vieta involution restricted to the surface. -/
def vieta1SurfacePerm {R : Type u} [CommRing R] (a : Coefficients R) :
    Equiv.Perm (SolutionSurface a) where
  __ := (vieta1Equiv R a).subtypeEquiv fun x => (isSolution_vieta1 a x).symm

/-- The second Vieta involution restricted to the surface. -/
def vieta2SurfacePerm {R : Type u} [CommRing R] (a : Coefficients R) :
    Equiv.Perm (SolutionSurface a) where
  __ := (vieta2Equiv R a).subtypeEquiv fun x => (isSolution_vieta2 a x).symm

/-- The third Vieta involution restricted to the surface. -/
def vieta3SurfacePerm {R : Type u} [CommRing R] (a : Coefficients R) :
    Equiv.Perm (SolutionSurface a) where
  __ := (vieta3Equiv R a).subtypeEquiv fun x => (isSolution_vieta3 a x).symm

/-- The first two-Vieta rotation restricted to the surface. -/
def rotation1SurfacePerm {R : Type u} [CommRing R] (a : Coefficients R) :
    Equiv.Perm (SolutionSurface a) where
  __ := (rotation1Equiv R a).subtypeEquiv fun x => (isSolution_rotation1 a x).symm

/-- The second two-Vieta rotation restricted to the surface. -/
def rotation2SurfacePerm {R : Type u} [CommRing R] (a : Coefficients R) :
    Equiv.Perm (SolutionSurface a) where
  __ := (rotation2Equiv R a).subtypeEquiv fun x => (isSolution_rotation2 a x).symm

/-- The third two-Vieta rotation restricted to the surface. -/
def rotation3SurfacePerm {R : Type u} [CommRing R] (a : Coefficients R) :
    Equiv.Perm (SolutionSurface a) where
  __ := (rotation3Equiv R a).subtypeEquiv fun x => (isSolution_rotation3 a x).symm

@[simp]
theorem coe_vieta1SurfacePerm {R : Type u} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) :
    ((vieta1SurfacePerm a x : SolutionSurface a) : Point R) = vieta1 a x := rfl

@[simp]
theorem coe_vieta2SurfacePerm {R : Type u} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) :
    ((vieta2SurfacePerm a x : SolutionSurface a) : Point R) = vieta2 a x := rfl

@[simp]
theorem coe_vieta3SurfacePerm {R : Type u} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) :
    ((vieta3SurfacePerm a x : SolutionSurface a) : Point R) = vieta3 a x := rfl

@[simp]
theorem coe_rotation1SurfacePerm {R : Type u} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) :
    ((rotation1SurfacePerm a x : SolutionSurface a) : Point R) = rotation1 a x := rfl

@[simp]
theorem coe_rotation2SurfacePerm {R : Type u} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) :
    ((rotation2SurfacePerm a x : SolutionSurface a) : Point R) = rotation2 a x := rfl

@[simp]
theorem coe_rotation3SurfacePerm {R : Type u} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) :
    ((rotation3SurfacePerm a x : SolutionSurface a) : Point R) = rotation3 a x := rfl

@[simp]
theorem vieta1SurfacePerm_surfaceOrigin {R : Type u} [CommRing R]
    (a : Coefficients R) : vieta1SurfacePerm a (surfaceOrigin a) = surfaceOrigin a := by
  ext <;> simp [vieta1SurfacePerm, vieta1Equiv, surfaceOrigin, vieta1, origin]

@[simp]
theorem vieta2SurfacePerm_surfaceOrigin {R : Type u} [CommRing R]
    (a : Coefficients R) : vieta2SurfacePerm a (surfaceOrigin a) = surfaceOrigin a := by
  ext <;> simp [vieta2SurfacePerm, vieta2Equiv, surfaceOrigin, vieta2, origin]

@[simp]
theorem vieta3SurfacePerm_surfaceOrigin {R : Type u} [CommRing R]
    (a : Coefficients R) : vieta3SurfacePerm a (surfaceOrigin a) = surfaceOrigin a := by
  ext <;> simp [vieta3SurfacePerm, vieta3Equiv, surfaceOrigin, vieta3, origin]

@[simp]
theorem rotation1SurfacePerm_surfaceOrigin {R : Type u} [CommRing R]
    (a : Coefficients R) : rotation1SurfacePerm a (surfaceOrigin a) = surfaceOrigin a := by
  apply Subtype.ext
  change rotation1 a (origin : Point R) = origin
  ext <;> simp [rotation1, vieta2, vieta3, origin]

@[simp]
theorem rotation2SurfacePerm_surfaceOrigin {R : Type u} [CommRing R]
    (a : Coefficients R) : rotation2SurfacePerm a (surfaceOrigin a) = surfaceOrigin a := by
  apply Subtype.ext
  change rotation2 a (origin : Point R) = origin
  ext <;> simp [rotation2, vieta1, vieta3, origin]

@[simp]
theorem rotation3SurfacePerm_surfaceOrigin {R : Type u} [CommRing R]
    (a : Coefficients R) : rotation3SurfacePerm a (surfaceOrigin a) = surfaceOrigin a := by
  apply Subtype.ext
  change rotation3 a (origin : Point R) = origin
  ext <;> simp [rotation3, vieta1, vieta2, origin]

/-- The three individual Vieta generators. -/
def vietaGenerators {R : Type u} [CommRing R] (a : Coefficients R) :
    Set (Equiv.Perm (SolutionSurface a)) :=
  {vieta1SurfacePerm a, vieta2SurfacePerm a, vieta3SurfacePerm a}

/-- The group generated by the three individual Vieta involutions. -/
def VietaGroup {R : Type u} [CommRing R] (a : Coefficients R) :
    Subgroup (Equiv.Perm (SolutionSurface a)) :=
  Subgroup.closure (vietaGenerators a)

/-- The three even-word rotations used as graph edges. -/
def rotationGenerators {R : Type u} [CommRing R] (a : Coefficients R) :
    Set (Equiv.Perm (SolutionSurface a)) :=
  {rotation1SurfacePerm a, rotation2SurfacePerm a, rotation3SurfacePerm a}

/-- The subgroup generated by the three two-Vieta rotations. -/
def RotationGroup {R : Type u} [CommRing R] (a : Coefficients R) :
    Subgroup (Equiv.Perm (SolutionSurface a)) :=
  Subgroup.closure (rotationGenerators a)

/-- The first Vieta involution belongs to the fixed-coefficient Vieta group. -/
theorem vieta1SurfacePerm_mem_VietaGroup {R : Type u} [CommRing R]
    (a : Coefficients R) : vieta1SurfacePerm a ∈ VietaGroup a :=
  Subgroup.subset_closure (by simp [vietaGenerators])

/-- The second Vieta involution belongs to the fixed-coefficient Vieta group. -/
theorem vieta2SurfacePerm_mem_VietaGroup {R : Type u} [CommRing R]
    (a : Coefficients R) : vieta2SurfacePerm a ∈ VietaGroup a :=
  Subgroup.subset_closure (by simp [vietaGenerators])

/-- The third Vieta involution belongs to the fixed-coefficient Vieta group. -/
theorem vieta3SurfacePerm_mem_VietaGroup {R : Type u} [CommRing R]
    (a : Coefficients R) : vieta3SurfacePerm a ∈ VietaGroup a :=
  Subgroup.subset_closure (by simp [vietaGenerators])

/-- The first rotation belongs to the fixed-coefficient rotation group. -/
theorem rotation1SurfacePerm_mem_RotationGroup {R : Type u} [CommRing R]
    (a : Coefficients R) : rotation1SurfacePerm a ∈ RotationGroup a :=
  Subgroup.subset_closure (by simp [rotationGenerators])

/-- The second rotation belongs to the fixed-coefficient rotation group. -/
theorem rotation2SurfacePerm_mem_RotationGroup {R : Type u} [CommRing R]
    (a : Coefficients R) : rotation2SurfacePerm a ∈ RotationGroup a :=
  Subgroup.subset_closure (by simp [rotationGenerators])

/-- The third rotation belongs to the fixed-coefficient rotation group. -/
theorem rotation3SurfacePerm_mem_RotationGroup {R : Type u} [CommRing R]
    (a : Coefficients R) : rotation3SurfacePerm a ∈ RotationGroup a :=
  Subgroup.subset_closure (by simp [rotationGenerators])

/-- The first Vieta involution as an element of the fixed-coefficient Vieta group. -/
def vieta1InVietaGroup {R : Type u} [CommRing R] (a : Coefficients R) :
    VietaGroup a :=
  ⟨vieta1SurfacePerm a, vieta1SurfacePerm_mem_VietaGroup a⟩

/-- The second Vieta involution as an element of the fixed-coefficient Vieta group. -/
def vieta2InVietaGroup {R : Type u} [CommRing R] (a : Coefficients R) :
    VietaGroup a :=
  ⟨vieta2SurfacePerm a, vieta2SurfacePerm_mem_VietaGroup a⟩

/-- The third Vieta involution as an element of the fixed-coefficient Vieta group. -/
def vieta3InVietaGroup {R : Type u} [CommRing R] (a : Coefficients R) :
    VietaGroup a :=
  ⟨vieta3SurfacePerm a, vieta3SurfacePerm_mem_VietaGroup a⟩

theorem vietaGenerator_fixes_origin {R : Type u} [CommRing R] (a : Coefficients R)
    {g : Equiv.Perm (SolutionSurface a)} (hg : g ∈ vietaGenerators a) :
    g (surfaceOrigin a) = surfaceOrigin a := by
  simp only [vietaGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl <;> simp

theorem rotationGenerator_fixes_origin {R : Type u} [CommRing R] (a : Coefficients R)
    {g : Equiv.Perm (SolutionSurface a)} (hg : g ∈ rotationGenerators a) :
    g (surfaceOrigin a) = surfaceOrigin a := by
  simp only [rotationGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl <;> simp

theorem VietaGroup_le_origin_stabilizer {R : Type u} [CommRing R] (a : Coefficients R) :
    VietaGroup a ≤ MulAction.stabilizer (Equiv.Perm (SolutionSurface a)) (surfaceOrigin a) :=
  (Subgroup.closure_le _).2 fun _ hg => vietaGenerator_fixes_origin a hg

theorem RotationGroup_le_origin_stabilizer {R : Type u} [CommRing R]
    (a : Coefficients R) :
    RotationGroup a ≤ MulAction.stabilizer (Equiv.Perm (SolutionSurface a)) (surfaceOrigin a) :=
  (Subgroup.closure_le _).2 fun _ hg => rotationGenerator_fixes_origin a hg

@[simp]
theorem VietaGroup_fixes_surfaceOrigin {R : Type u} [CommRing R]
    (a : Coefficients R) (g : VietaGroup a) :
    g • surfaceOrigin a = surfaceOrigin a :=
  VietaGroup_le_origin_stabilizer a g.2

@[simp]
theorem RotationGroup_fixes_surfaceOrigin {R : Type u} [CommRing R]
    (a : Coefficients R) (g : RotationGroup a) :
    g • surfaceOrigin a = surfaceOrigin a :=
  RotationGroup_le_origin_stabilizer a g.2

@[simp]
theorem vieta1InVietaGroup_smul_surface {R : Type u} [CommRing R]
    (a : Coefficients R) (x : SolutionSurface a) :
    vieta1InVietaGroup a • x = vieta1SurfacePerm a x := rfl

@[simp]
theorem vieta2InVietaGroup_smul_surface {R : Type u} [CommRing R]
    (a : Coefficients R) (x : SolutionSurface a) :
    vieta2InVietaGroup a • x = vieta2SurfacePerm a x := rfl

@[simp]
theorem vieta3InVietaGroup_smul_surface {R : Type u} [CommRing R]
    (a : Coefficients R) (x : SolutionSurface a) :
    vieta3InVietaGroup a • x = vieta3SurfacePerm a x := rfl

/-- The punctured surface means removal of the origin only. -/
abbrev PuncturedSolutionSurface {R : Type u} [CommRing R] (a : Coefficients R) :=
  {x : SolutionSurface a // x ≠ surfaceOrigin a}

/-- Restrict a permutation to the complement of one of its fixed points. -/
def restrictPermNe {A : Type*} (e : Equiv.Perm A) (x₀ : A) (h : e x₀ = x₀) :
    Equiv.Perm {x : A // x ≠ x₀} where
  toFun x :=
    ⟨e x, fun hex => x.2 (e.injective (hex.trans h.symm))⟩
  invFun x :=
    ⟨e.symm x, fun hex => by
      apply x.2
      calc
        x.1 = e (e.symm x.1) := (e.apply_symm_apply x.1).symm
        _ = e x₀ := congrArg e hex
        _ = x₀ := h⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)

/-- The first Vieta involution on the punctured fixed-coefficient surface. -/
def vieta1PuncturedPerm {R : Type u} [CommRing R] (a : Coefficients R) :
    Equiv.Perm (PuncturedSolutionSurface a) :=
  restrictPermNe (vieta1SurfacePerm a) (surfaceOrigin a)
    (vieta1SurfacePerm_surfaceOrigin a)

/-- The second Vieta involution on the punctured fixed-coefficient surface. -/
def vieta2PuncturedPerm {R : Type u} [CommRing R] (a : Coefficients R) :
    Equiv.Perm (PuncturedSolutionSurface a) :=
  restrictPermNe (vieta2SurfacePerm a) (surfaceOrigin a)
    (vieta2SurfacePerm_surfaceOrigin a)

/-- The third Vieta involution on the punctured fixed-coefficient surface. -/
def vieta3PuncturedPerm {R : Type u} [CommRing R] (a : Coefficients R) :
    Equiv.Perm (PuncturedSolutionSurface a) :=
  restrictPermNe (vieta3SurfacePerm a) (surfaceOrigin a)
    (vieta3SurfacePerm_surfaceOrigin a)

/-- The first two-Vieta rotation on the punctured fixed-coefficient surface. -/
def rotation1PuncturedPerm {R : Type u} [CommRing R] (a : Coefficients R) :
    Equiv.Perm (PuncturedSolutionSurface a) :=
  restrictPermNe (rotation1SurfacePerm a) (surfaceOrigin a)
    (rotation1SurfacePerm_surfaceOrigin a)

/-- The second two-Vieta rotation on the punctured fixed-coefficient surface. -/
def rotation2PuncturedPerm {R : Type u} [CommRing R] (a : Coefficients R) :
    Equiv.Perm (PuncturedSolutionSurface a) :=
  restrictPermNe (rotation2SurfacePerm a) (surfaceOrigin a)
    (rotation2SurfacePerm_surfaceOrigin a)

/-- The third two-Vieta rotation on the punctured fixed-coefficient surface. -/
def rotation3PuncturedPerm {R : Type u} [CommRing R] (a : Coefficients R) :
    Equiv.Perm (PuncturedSolutionSurface a) :=
  restrictPermNe (rotation3SurfacePerm a) (surfaceOrigin a)
    (rotation3SurfacePerm_surfaceOrigin a)

@[simp]
theorem coe_vieta1PuncturedPerm {R : Type u} [CommRing R] (a : Coefficients R)
    (x : PuncturedSolutionSurface a) :
    (vieta1PuncturedPerm a x).1 = vieta1SurfacePerm a x.1 := rfl

@[simp]
theorem coe_vieta2PuncturedPerm {R : Type u} [CommRing R] (a : Coefficients R)
    (x : PuncturedSolutionSurface a) :
    (vieta2PuncturedPerm a x).1 = vieta2SurfacePerm a x.1 := rfl

@[simp]
theorem coe_vieta3PuncturedPerm {R : Type u} [CommRing R] (a : Coefficients R)
    (x : PuncturedSolutionSurface a) :
    (vieta3PuncturedPerm a x).1 = vieta3SurfacePerm a x.1 := rfl

@[simp]
theorem coe_rotation1PuncturedPerm {R : Type u} [CommRing R] (a : Coefficients R)
    (x : PuncturedSolutionSurface a) :
    (rotation1PuncturedPerm a x).1 = rotation1SurfacePerm a x.1 := rfl

@[simp]
theorem coe_rotation2PuncturedPerm {R : Type u} [CommRing R] (a : Coefficients R)
    (x : PuncturedSolutionSurface a) :
    (rotation2PuncturedPerm a x).1 = rotation2SurfacePerm a x.1 := rfl

@[simp]
theorem coe_rotation3PuncturedPerm {R : Type u} [CommRing R] (a : Coefficients R)
    (x : PuncturedSolutionSurface a) :
    (rotation3PuncturedPerm a x).1 = rotation3SurfacePerm a x.1 := rfl

/-- The Vieta-group action restricted to the punctured surface. -/
instance {R : Type u} [CommRing R] {a : Coefficients R} :
    MulAction (VietaGroup a) (PuncturedSolutionSurface a) where
  smul g x :=
    ⟨g • x.1, fun hgx => x.2 <| by
      calc
        x.1 = g⁻¹ • (g • x.1) := (inv_smul_smul g x.1).symm
        _ = g⁻¹ • surfaceOrigin a := congrArg (g⁻¹ • ·) hgx
        _ = surfaceOrigin a := VietaGroup_fixes_surfaceOrigin a g⁻¹⟩
  one_smul x := Subtype.ext (one_smul (VietaGroup a) x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

@[simp]
theorem vieta1InVietaGroup_smul_punctured {R : Type u} [CommRing R]
    (a : Coefficients R) (x : PuncturedSolutionSurface a) :
    vieta1InVietaGroup a • x = vieta1PuncturedPerm a x := by
  apply Subtype.ext
  rfl

@[simp]
theorem vieta2InVietaGroup_smul_punctured {R : Type u} [CommRing R]
    (a : Coefficients R) (x : PuncturedSolutionSurface a) :
    vieta2InVietaGroup a • x = vieta2PuncturedPerm a x := by
  apply Subtype.ext
  rfl

@[simp]
theorem vieta3InVietaGroup_smul_punctured {R : Type u} [CommRing R]
    (a : Coefficients R) (x : PuncturedSolutionSurface a) :
    vieta3InVietaGroup a • x = vieta3PuncturedPerm a x := by
  apply Subtype.ext
  rfl

/-- The rotation-group action restricted to the punctured surface. -/
instance {R : Type u} [CommRing R] {a : Coefficients R} :
    MulAction (RotationGroup a) (PuncturedSolutionSurface a) where
  smul g x :=
    ⟨g • x.1, fun hgx => x.2 <| by
      calc
        x.1 = g⁻¹ • (g • x.1) := (inv_smul_smul g x.1).symm
        _ = g⁻¹ • surfaceOrigin a := congrArg (g⁻¹ • ·) hgx
        _ = surfaceOrigin a := RotationGroup_fixes_surfaceOrigin a g⁻¹⟩
  one_smul x := Subtype.ext (one_smul (RotationGroup a) x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

/-- The orbit of a punctured point under all three Vieta moves. -/
def puncturedVietaOrbit {R : Type u} [CommRing R] {a : Coefficients R}
    (x : PuncturedSolutionSurface a) : Set (PuncturedSolutionSurface a) :=
  MulAction.orbit (VietaGroup a) x

/-- The orbit of a punctured point under the three two-Vieta rotations. -/
def puncturedRotationOrbit {R : Type u} [CommRing R] {a : Coefficients R}
    (x : PuncturedSolutionSurface a) : Set (PuncturedSolutionSurface a) :=
  MulAction.orbit (RotationGroup a) x

/-- The all-solution surface is never transitive under the Vieta group. -/
theorem not_vieta_transitive_on_unpunctured {R : Type u} [CommRing R] [Nontrivial R]
    (a : Coefficients R) :
    ¬ ∀ x y : SolutionSurface a, ∃ g : VietaGroup a, g • x = y := by
  intro h
  obtain ⟨g, hg⟩ := h (surfaceOrigin a) (surfaceUnit a)
  apply surfaceUnit_ne_surfaceOrigin a
  exact hg.symm.trans (VietaGroup_fixes_surfaceOrigin a g)

/-- The all-solution graph is never transitive under the rotation group. -/
theorem not_rotation_transitive_on_unpunctured {R : Type u} [CommRing R] [Nontrivial R]
    (a : Coefficients R) :
    ¬ ∀ x y : SolutionSurface a, ∃ g : RotationGroup a, g • x = y := by
  intro h
  obtain ⟨g, hg⟩ := h (surfaceOrigin a) (surfaceUnit a)
  apply surfaceUnit_ne_surfaceOrigin a
  exact hg.symm.trans (RotationGroup_fixes_surfaceOrigin a g)

end GenMarkoff
