import GenMarkoff.General.Cage.ConnectingDirectedRelay

/-!
# Cyclic transport of full-Vieta strong approximation

The unequal connecting cage is most economical in a coefficient ordering
whose first coefficient is nonzero.  This file records that changing the
ordering by a cyclic permutation does not change the mathematical content:
coefficients and coordinates are cycled simultaneously, and the Vieta words
are transported through the explicit intertwining proved in
`ConnectingDirectedRelay`.

No coordinate permutation is asserted to preserve a fixed unequal
coefficient triple.
-/

namespace GenMarkoff.General.Assembly

open GenMarkoff.General.Cage

universe u

noncomputable section

@[simp]
theorem directedCycleLeftSurfaceEquiv_surfaceOrigin
    {R : Type u} [CommRing R] (a : Coefficients R) :
    directedCycleLeftSurfaceEquiv a (surfaceOrigin a) =
      surfaceOrigin (directedCycleLeftCoefficients a) := by
  apply Subtype.ext
  rfl

@[simp]
theorem directedCycleRightSurfaceEquiv_surfaceOrigin
    {R : Type u} [CommRing R] (a : Coefficients R) :
    directedCycleRightSurfaceEquiv a (surfaceOrigin a) =
      surfaceOrigin (directedCycleRightCoefficients a) := by
  apply Subtype.ext
  rfl

/-- Simultaneous left cycling restricts to the punctured surfaces. -/
def directedCycleLeftPuncturedSurfaceEquiv
    {R : Type u} [CommRing R] (a : Coefficients R) :
    PuncturedSolutionSurface a ≃
      PuncturedSolutionSurface (directedCycleLeftCoefficients a) where
  toFun x :=
    ⟨directedCycleLeftSurfaceEquiv a x.1, by
      intro h
      apply x.2
      apply (directedCycleLeftSurfaceEquiv a).injective
      simpa using h⟩
  invFun x :=
    ⟨(directedCycleLeftSurfaceEquiv a).symm x.1, by
      intro h
      apply x.2
      have h' := congrArg (directedCycleLeftSurfaceEquiv a) h
      simpa using h'⟩
  left_inv x := by
    apply Subtype.ext
    exact (directedCycleLeftSurfaceEquiv a).left_inv x.1
  right_inv x := by
    apply Subtype.ext
    exact (directedCycleLeftSurfaceEquiv a).right_inv x.1

/-- Simultaneous right cycling restricts to the punctured surfaces. -/
def directedCycleRightPuncturedSurfaceEquiv
    {R : Type u} [CommRing R] (a : Coefficients R) :
    PuncturedSolutionSurface a ≃
      PuncturedSolutionSurface (directedCycleRightCoefficients a) where
  toFun x :=
    ⟨directedCycleRightSurfaceEquiv a x.1, by
      intro h
      apply x.2
      apply (directedCycleRightSurfaceEquiv a).injective
      simpa using h⟩
  invFun x :=
    ⟨(directedCycleRightSurfaceEquiv a).symm x.1, by
      intro h
      apply x.2
      have h' := congrArg (directedCycleRightSurfaceEquiv a) h
      simpa using h'⟩
  left_inv x := by
    apply Subtype.ext
    exact (directedCycleRightSurfaceEquiv a).left_inv x.1
  right_inv x := by
    apply Subtype.ext
    exact (directedCycleRightSurfaceEquiv a).right_inv x.1

/-- Full-Vieta transitivity for the left-cycled coefficient surface pulls
back to the original coefficient surface. -/
theorem vietaTransitive_of_directedCycleLeft
    {R : Type u} [CommRing R] (a : Coefficients R)
    (h :
      ∀ x y :
          PuncturedSolutionSurface (directedCycleLeftCoefficients a),
        ∃ g : VietaGroup (directedCycleLeftCoefficients a), g • x = y) :
    ∀ x y : PuncturedSolutionSurface a,
      ∃ g : VietaGroup a, g • x = y := by
  intro x y
  obtain ⟨g, hg⟩ :=
    h (directedCycleLeftPuncturedSurfaceEquiv a x)
      (directedCycleLeftPuncturedSurfaceEquiv a y)
  have hcycled :
      SameVietaComponent
        (directedCycleLeftSurfaceEquiv a x.1)
        (directedCycleLeftSurfaceEquiv a y.1) := by
    refine ⟨g, ?_⟩
    exact congrArg Subtype.val hg
  obtain ⟨g', hg'⟩ :=
    sameVietaComponent_of_directedCycleLeft a hcycled
  refine ⟨g', ?_⟩
  apply Subtype.ext
  exact hg'

/-- Full-Vieta transitivity for the right-cycled coefficient surface pulls
back to the original coefficient surface. -/
theorem vietaTransitive_of_directedCycleRight
    {R : Type u} [CommRing R] (a : Coefficients R)
    (h :
      ∀ x y :
          PuncturedSolutionSurface (directedCycleRightCoefficients a),
        ∃ g : VietaGroup (directedCycleRightCoefficients a), g • x = y) :
    ∀ x y : PuncturedSolutionSurface a,
      ∃ g : VietaGroup a, g • x = y := by
  intro x y
  obtain ⟨g, hg⟩ :=
    h (directedCycleRightPuncturedSurfaceEquiv a x)
      (directedCycleRightPuncturedSurfaceEquiv a y)
  have hcycled :
      SameVietaComponent
        (directedCycleRightSurfaceEquiv a x.1)
        (directedCycleRightSurfaceEquiv a y.1) := by
    refine ⟨g, ?_⟩
    exact congrArg Subtype.val hg
  obtain ⟨g', hg'⟩ :=
    sameVietaComponent_of_directedCycleRight a hcycled
  refine ⟨g', ?_⟩
  apply Subtype.ext
  exact hg'

@[simp]
theorem modCoefficients_directedCycleLeftCoefficients
    (a : Coefficients ℤ) (p : ℕ) :
    modCoefficients (directedCycleLeftCoefficients a) p =
      directedCycleLeftCoefficients (modCoefficients a p) := by
  ext <;>
    simp [modCoefficients, Coefficients.intCast,
      directedCycleLeftCoefficients]

@[simp]
theorem modCoefficients_directedCycleRightCoefficients
    (a : Coefficients ℤ) (p : ℕ) :
    modCoefficients (directedCycleRightCoefficients a) p =
      directedCycleRightCoefficients (modCoefficients a p) := by
  ext <;>
    simp [modCoefficients, Coefficients.intCast,
      directedCycleRightCoefficients]

/-- Vieta strong approximation at a fixed prime for the left-cycled
coefficient triple pulls back to the original triple. -/
theorem vietaStrongApproximationAt_of_directedCycleLeft
    (a : Coefficients ℤ) (p : ℕ) (hp : p.Prime)
    (h :
      VietaStrongApproximationAt
        (directedCycleLeftCoefficients a) p hp) :
    VietaStrongApproximationAt a p hp := by
  letI : Fact p.Prime := ⟨hp⟩
  change
    ∀ x y :
        PuncturedSolutionSurface
          (modCoefficients (directedCycleLeftCoefficients a) p),
      ∃ g :
          VietaGroup
            (modCoefficients (directedCycleLeftCoefficients a) p),
        g • x = y at h
  rw [modCoefficients_directedCycleLeftCoefficients] at h
  change
    ∀ x y : PuncturedSolutionSurface (modCoefficients a p),
      ∃ g : VietaGroup (modCoefficients a p), g • x = y
  exact
    vietaTransitive_of_directedCycleLeft
      (modCoefficients a p) h

/-- Vieta strong approximation at a fixed prime for the right-cycled
coefficient triple pulls back to the original triple. -/
theorem vietaStrongApproximationAt_of_directedCycleRight
    (a : Coefficients ℤ) (p : ℕ) (hp : p.Prime)
    (h :
      VietaStrongApproximationAt
        (directedCycleRightCoefficients a) p hp) :
    VietaStrongApproximationAt a p hp := by
  letI : Fact p.Prime := ⟨hp⟩
  change
    ∀ x y :
        PuncturedSolutionSurface
          (modCoefficients (directedCycleRightCoefficients a) p),
      ∃ g :
          VietaGroup
            (modCoefficients (directedCycleRightCoefficients a) p),
        g • x = y at h
  rw [modCoefficients_directedCycleRightCoefficients] at h
  change
    ∀ x y : PuncturedSolutionSurface (modCoefficients a p),
      ∃ g : VietaGroup (modCoefficients a p), g • x = y
  exact
    vietaTransitive_of_directedCycleRight
      (modCoefficients a p) h

/-- Eventual Vieta strong approximation for the left-cycled integral
coefficient triple pulls back to the original triple. -/
theorem eventuallyVietaStrongApproximation_of_directedCycleLeft
    (a : Coefficients ℤ)
    (h :
      EventuallyVietaStrongApproximation
        (directedCycleLeftCoefficients a)) :
    EventuallyVietaStrongApproximation a := by
  obtain ⟨threshold, hthreshold⟩ := h
  refine ⟨threshold, ?_⟩
  intro p hp hpLarge
  letI : Fact p.Prime := ⟨hp⟩
  have hcycled := hthreshold p hp hpLarge
  change
    ∀ x y :
        PuncturedSolutionSurface
          (modCoefficients (directedCycleLeftCoefficients a) p),
      ∃ g :
          VietaGroup
            (modCoefficients (directedCycleLeftCoefficients a) p),
        g • x = y at hcycled
  rw [modCoefficients_directedCycleLeftCoefficients] at hcycled
  change
    ∀ x y : PuncturedSolutionSurface (modCoefficients a p),
      ∃ g : VietaGroup (modCoefficients a p), g • x = y
  exact
    vietaTransitive_of_directedCycleLeft
      (modCoefficients a p) hcycled

/-- Eventual Vieta strong approximation for the right-cycled integral
coefficient triple pulls back to the original triple. -/
theorem eventuallyVietaStrongApproximation_of_directedCycleRight
    (a : Coefficients ℤ)
    (h :
      EventuallyVietaStrongApproximation
        (directedCycleRightCoefficients a)) :
    EventuallyVietaStrongApproximation a := by
  obtain ⟨threshold, hthreshold⟩ := h
  refine ⟨threshold, ?_⟩
  intro p hp hpLarge
  letI : Fact p.Prime := ⟨hp⟩
  have hcycled := hthreshold p hp hpLarge
  change
    ∀ x y :
        PuncturedSolutionSurface
          (modCoefficients (directedCycleRightCoefficients a) p),
      ∃ g :
          VietaGroup
            (modCoefficients (directedCycleRightCoefficients a) p),
        g • x = y at hcycled
  rw [modCoefficients_directedCycleRightCoefficients] at hcycled
  change
    ∀ x y : PuncturedSolutionSurface (modCoefficients a p),
      ∃ g : VietaGroup (modCoefficients a p), g • x = y
  exact
    vietaTransitive_of_directedCycleRight
      (modCoefficients a p) hcycled

/-- Integral nondegeneracy is invariant under left cycling. -/
theorem integrallyNondegenerate_directedCycleLeft_iff
    (a : Coefficients ℤ) :
    IntegrallyNondegenerate (directedCycleLeftCoefficients a) ↔
      IntegrallyNondegenerate a := by
  rw [IntegrallyNondegenerate, IntegrallyNondegenerate,
    directedCycleLeftCoefficients_multiplier]
  simp only [directedCycleLeftCoefficients]
  tauto

/-- Integral nondegeneracy is invariant under right cycling. -/
theorem integrallyNondegenerate_directedCycleRight_iff
    (a : Coefficients ℤ) :
    IntegrallyNondegenerate (directedCycleRightCoefficients a) ↔
      IntegrallyNondegenerate a := by
  rw [IntegrallyNondegenerate, IntegrallyNondegenerate,
    directedCycleRightCoefficients_multiplier]
  simp only [directedCycleRightCoefficients]
  tauto

/-- A cutoff after which a fixed nonzero first integral coefficient remains
nonzero modulo every prime (indeed, modulo every larger positive modulus). -/
def firstCoefficientNonzeroCutoff (a : Coefficients ℤ) : ℕ :=
  a.a1.natAbs + 1

/-- Above `firstCoefficientNonzeroCutoff`, reduction preserves nonvanishing
of the first coefficient. -/
theorem modCoefficients_a1_ne_zero_of_firstCoefficientNonzeroCutoff_le
    {a : Coefficients ℤ} (ha1 : a.a1 ≠ 0)
    {p : ℕ} (hp : firstCoefficientNonzeroCutoff a ≤ p) :
    (modCoefficients a p).a1 ≠ 0 := by
  intro hzero
  have hcast : (a.a1 : ZMod p) = 0 := by
    simpa [modCoefficients, Coefficients.intCast] using hzero
  have hdvd : (p : ℤ) ∣ a.a1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd a.a1 p).mp hcast
  have hle : p ≤ a.a1.natAbs := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hdvd ha1
  have hlt : a.a1.natAbs < p := by
    simpa [firstCoefficientNonzeroCutoff] using hp
  omega

end

end GenMarkoff.General.Assembly
