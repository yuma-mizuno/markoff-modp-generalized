import GenMarkoff.General.Cage.ConnectingRelay

/-!
# Directed connecting relays

The first-axis connecting relay is transported to the other two directed
axes by simultaneously cycling the coefficient triple and the coordinates.
This is not a coordinate symmetry of a fixed unequal-coefficient surface:
the coefficient triple changes together with the point, and the full Vieta
group action is transported explicitly.
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff
open GenMarkoff.General.Assembly

universe u

noncomputable section

/-- The coefficient frame obtained by moving the second coefficient to the
first position.  It accompanies the same cyclic permutation of coordinates. -/
def directedCycleLeftCoefficients {R : Type u} (a : Coefficients R) :
    Coefficients R :=
  ⟨a.a2, a.a3, a.a1⟩

/-- The coefficient frame obtained by moving the third coefficient to the
first position.  It accompanies the inverse cyclic permutation of coordinates. -/
def directedCycleRightCoefficients {R : Type u} (a : Coefficients R) :
    Coefficients R :=
  ⟨a.a3, a.a1, a.a2⟩

/-- Cyclically move the second coordinate to the first position. -/
def directedCycleLeftPointEquiv {R : Type u} : Point R ≃ Point R where
  toFun x := ⟨x.x2, x.x3, x.x1⟩
  invFun x := ⟨x.x3, x.x1, x.x2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- Cyclically move the third coordinate to the first position. -/
def directedCycleRightPointEquiv {R : Type u} : Point R ≃ Point R :=
  directedCycleLeftPointEquiv.symm

@[simp]
theorem directedCycleLeftPointEquiv_apply
    {R : Type u} (x : Point R) :
    directedCycleLeftPointEquiv x = ⟨x.x2, x.x3, x.x1⟩ :=
  rfl

@[simp]
theorem directedCycleRightPointEquiv_apply
    {R : Type u} (x : Point R) :
    directedCycleRightPointEquiv x = ⟨x.x3, x.x1, x.x2⟩ :=
  rfl

@[simp]
theorem directedCycleLeftCoefficients_multiplier
    {R : Type u} [CommRing R] (a : Coefficients R) :
    (directedCycleLeftCoefficients a).multiplier = a.multiplier := by
  simp [directedCycleLeftCoefficients, Coefficients.multiplier]
  ring

@[simp]
theorem directedCycleRightCoefficients_multiplier
    {R : Type u} [CommRing R] (a : Coefficients R) :
    (directedCycleRightCoefficients a).multiplier = a.multiplier := by
  simp [directedCycleRightCoefficients, Coefficients.multiplier]
  ring

/-- Simultaneously cycling coefficients and coordinates preserves the
generalized Markoff polynomial. -/
theorem polynomial_directedCycleLeft
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    polynomial (directedCycleLeftCoefficients a)
        (directedCycleLeftPointEquiv x) =
      polynomial a x := by
  simp [polynomial, directedCycleLeftCoefficients,
    directedCycleLeftPointEquiv, Coefficients.multiplier]
  ring

/-- The inverse simultaneous cycle also preserves the polynomial. -/
theorem polynomial_directedCycleRight
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    polynomial (directedCycleRightCoefficients a)
        (directedCycleRightPointEquiv x) =
      polynomial a x := by
  simp [polynomial, directedCycleRightCoefficients,
    directedCycleRightPointEquiv, directedCycleLeftPointEquiv,
    Coefficients.multiplier]
  ring

/-- Simultaneous left cycling is an equivalence between the two explicitly
different coefficient-labelled solution surfaces. -/
def directedCycleLeftSurfaceEquiv
    {R : Type u} [CommRing R] (a : Coefficients R) :
    SolutionSurface a ≃
      SolutionSurface (directedCycleLeftCoefficients a) where
  toFun x :=
    ⟨directedCycleLeftPointEquiv x.1, by
      rw [IsSolution, polynomial_directedCycleLeft]
      exact x.2⟩
  invFun x :=
    ⟨directedCycleRightPointEquiv x.1, by
      rw [IsSolution]
      have hx :
          polynomial (directedCycleLeftCoefficients a) x.1 = 0 :=
        x.2
      have hcycle :=
        polynomial_directedCycleRight
          (directedCycleLeftCoefficients a) x.1
      simpa [directedCycleLeftCoefficients,
        directedCycleRightCoefficients] using hcycle.trans hx⟩
  left_inv x := by
    apply Subtype.ext
    exact directedCycleLeftPointEquiv.left_inv x.1
  right_inv x := by
    apply Subtype.ext
    exact directedCycleLeftPointEquiv.right_inv x.1

/-- Simultaneous right cycling is an equivalence between the two explicitly
different coefficient-labelled solution surfaces. -/
def directedCycleRightSurfaceEquiv
    {R : Type u} [CommRing R] (a : Coefficients R) :
    SolutionSurface a ≃
      SolutionSurface (directedCycleRightCoefficients a) where
  toFun x :=
    ⟨directedCycleRightPointEquiv x.1, by
      rw [IsSolution, polynomial_directedCycleRight]
      exact x.2⟩
  invFun x :=
    ⟨directedCycleLeftPointEquiv x.1, by
      rw [IsSolution]
      have hx :
          polynomial (directedCycleRightCoefficients a) x.1 = 0 :=
        x.2
      have hcycle :=
        polynomial_directedCycleLeft
          (directedCycleRightCoefficients a) x.1
      simpa [directedCycleLeftCoefficients,
        directedCycleRightCoefficients] using hcycle.trans hx⟩
  left_inv x := by
    apply Subtype.ext
    exact directedCycleLeftPointEquiv.right_inv x.1
  right_inv x := by
    apply Subtype.ext
    exact directedCycleLeftPointEquiv.left_inv x.1

@[simp]
theorem coe_directedCycleLeftSurfaceEquiv
    {R : Type u} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) :
    (directedCycleLeftSurfaceEquiv a x).1 =
      directedCycleLeftPointEquiv x.1 :=
  rfl

@[simp]
theorem coe_directedCycleRightSurfaceEquiv
    {R : Type u} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) :
    (directedCycleRightSurfaceEquiv a x).1 =
      directedCycleRightPointEquiv x.1 :=
  rfl

@[simp]
theorem traceAt_directedCycleLeft_first
    {R : Type u} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) :
    traceAt (directedCycleLeftCoefficients a) .first
        (directedCycleLeftSurfaceEquiv a x).1 =
      traceAt a .second x.1 := by
  change
    (directedCycleLeftCoefficients a).multiplier * x.1.x2 - a.a2 =
      a.multiplier * x.1.x2 - a.a2
  rw [directedCycleLeftCoefficients_multiplier]

@[simp]
theorem traceAt_directedCycleRight_first
    {R : Type u} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) :
    traceAt (directedCycleRightCoefficients a) .first
        (directedCycleRightSurfaceEquiv a x).1 =
      traceAt a .third x.1 := by
  change
    (directedCycleRightCoefficients a).multiplier * x.1.x3 - a.a3 =
      a.multiplier * x.1.x3 - a.a3
  rw [directedCycleRightCoefficients_multiplier]

/-- Under the simultaneous left cycle, the first Vieta move becomes the
third Vieta move for the cycled coefficient frame. -/
theorem directedCycleLeftPointEquiv_vieta1
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    directedCycleLeftPointEquiv (vieta1 a x) =
      vieta3 (directedCycleLeftCoefficients a)
        (directedCycleLeftPointEquiv x) := by
  ext <;>
    simp [directedCycleLeftPointEquiv, directedCycleLeftCoefficients,
      vieta1, vieta3, Coefficients.multiplier] ;
    ring

/-- Under the simultaneous left cycle, the second Vieta move becomes the
first Vieta move for the cycled coefficient frame. -/
theorem directedCycleLeftPointEquiv_vieta2
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    directedCycleLeftPointEquiv (vieta2 a x) =
      vieta1 (directedCycleLeftCoefficients a)
        (directedCycleLeftPointEquiv x) := by
  ext <;>
    simp [directedCycleLeftPointEquiv, directedCycleLeftCoefficients,
      vieta1, vieta2, Coefficients.multiplier] ;
    ring

/-- Under the simultaneous left cycle, the third Vieta move becomes the
second Vieta move for the cycled coefficient frame. -/
theorem directedCycleLeftPointEquiv_vieta3
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    directedCycleLeftPointEquiv (vieta3 a x) =
      vieta2 (directedCycleLeftCoefficients a)
        (directedCycleLeftPointEquiv x) := by
  ext <;>
    simp [directedCycleLeftPointEquiv, directedCycleLeftCoefficients,
      vieta2, vieta3, Coefficients.multiplier] ;
    ring

/-- Under the simultaneous right cycle, the first Vieta move becomes the
second Vieta move for the cycled coefficient frame. -/
theorem directedCycleRightPointEquiv_vieta1
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    directedCycleRightPointEquiv (vieta1 a x) =
      vieta2 (directedCycleRightCoefficients a)
        (directedCycleRightPointEquiv x) := by
  ext <;>
    simp [directedCycleRightPointEquiv, directedCycleLeftPointEquiv,
      directedCycleRightCoefficients, vieta1, vieta2,
      Coefficients.multiplier] ;
    ring

/-- Under the simultaneous right cycle, the second Vieta move becomes the
third Vieta move for the cycled coefficient frame. -/
theorem directedCycleRightPointEquiv_vieta2
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    directedCycleRightPointEquiv (vieta2 a x) =
      vieta3 (directedCycleRightCoefficients a)
        (directedCycleRightPointEquiv x) := by
  ext <;>
    simp [directedCycleRightPointEquiv, directedCycleLeftPointEquiv,
      directedCycleRightCoefficients, vieta2, vieta3,
      Coefficients.multiplier] ;
    ring

/-- Under the simultaneous right cycle, the third Vieta move becomes the
first Vieta move for the cycled coefficient frame. -/
theorem directedCycleRightPointEquiv_vieta3
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    directedCycleRightPointEquiv (vieta3 a x) =
      vieta1 (directedCycleRightCoefficients a)
        (directedCycleRightPointEquiv x) := by
  ext <;>
    simp [directedCycleRightPointEquiv, directedCycleLeftPointEquiv,
      directedCycleRightCoefficients, vieta1, vieta3,
      Coefficients.multiplier] ;
    ring

@[simp]
theorem directedCycleLeftSurfaceEquiv_vieta1
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : SolutionSurface a) :
    directedCycleLeftSurfaceEquiv a (vieta1SurfacePerm a x) =
      vieta3SurfacePerm (directedCycleLeftCoefficients a)
        (directedCycleLeftSurfaceEquiv a x) := by
  apply Subtype.ext
  exact directedCycleLeftPointEquiv_vieta1 a x.1

@[simp]
theorem directedCycleLeftSurfaceEquiv_vieta2
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : SolutionSurface a) :
    directedCycleLeftSurfaceEquiv a (vieta2SurfacePerm a x) =
      vieta1SurfacePerm (directedCycleLeftCoefficients a)
        (directedCycleLeftSurfaceEquiv a x) := by
  apply Subtype.ext
  exact directedCycleLeftPointEquiv_vieta2 a x.1

@[simp]
theorem directedCycleLeftSurfaceEquiv_vieta3
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : SolutionSurface a) :
    directedCycleLeftSurfaceEquiv a (vieta3SurfacePerm a x) =
      vieta2SurfacePerm (directedCycleLeftCoefficients a)
        (directedCycleLeftSurfaceEquiv a x) := by
  apply Subtype.ext
  exact directedCycleLeftPointEquiv_vieta3 a x.1

@[simp]
theorem directedCycleRightSurfaceEquiv_vieta1
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : SolutionSurface a) :
    directedCycleRightSurfaceEquiv a (vieta1SurfacePerm a x) =
      vieta2SurfacePerm (directedCycleRightCoefficients a)
        (directedCycleRightSurfaceEquiv a x) := by
  apply Subtype.ext
  exact directedCycleRightPointEquiv_vieta1 a x.1

@[simp]
theorem directedCycleRightSurfaceEquiv_vieta2
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : SolutionSurface a) :
    directedCycleRightSurfaceEquiv a (vieta2SurfacePerm a x) =
      vieta3SurfacePerm (directedCycleRightCoefficients a)
        (directedCycleRightSurfaceEquiv a x) := by
  apply Subtype.ext
  exact directedCycleRightPointEquiv_vieta2 a x.1

@[simp]
theorem directedCycleRightSurfaceEquiv_vieta3
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : SolutionSurface a) :
    directedCycleRightSurfaceEquiv a (vieta3SurfacePerm a x) =
      vieta1SurfacePerm (directedCycleRightCoefficients a)
        (directedCycleRightSurfaceEquiv a x) := by
  apply Subtype.ext
  exact directedCycleRightPointEquiv_vieta3 a x.1

/-- Every full-Vieta word on the left-cycled coefficient surface has a
word on the original fixed-coefficient surface whose action is intertwined
by the simultaneous coefficient-coordinate cycle. -/
theorem exists_VietaGroup_descend_directedCycleLeft
    {R : Type u} [CommRing R] (a : Coefficients R)
    (g : VietaGroup (directedCycleLeftCoefficients a)) :
    ∃ h : VietaGroup a,
      ∀ x : SolutionSurface a,
        directedCycleLeftSurfaceEquiv a (h • x) =
          g • directedCycleLeftSurfaceEquiv a x := by
  let motive :
      ∀ q :
          Equiv.Perm
            (SolutionSurface (directedCycleLeftCoefficients a)),
        q ∈ Subgroup.closure
            (vietaGenerators (directedCycleLeftCoefficients a)) →
          Prop :=
    fun q hq =>
      ∃ h : VietaGroup a,
        ∀ x : SolutionSurface a,
          directedCycleLeftSurfaceEquiv a (h • x) =
            (⟨q, hq⟩ :
              VietaGroup (directedCycleLeftCoefficients a)) •
                directedCycleLeftSurfaceEquiv a x
  apply Subgroup.closure_induction (p := motive)
  · intro q hq
    simp only [vietaGenerators, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · refine ⟨vieta2InVietaGroup a, fun x => ?_⟩
      exact directedCycleLeftSurfaceEquiv_vieta2 a x
    · refine ⟨vieta3InVietaGroup a, fun x => ?_⟩
      exact directedCycleLeftSurfaceEquiv_vieta3 a x
    · refine ⟨vieta1InVietaGroup a, fun x => ?_⟩
      exact directedCycleLeftSurfaceEquiv_vieta1 a x
  · refine ⟨1, fun x => ?_⟩
    change
      directedCycleLeftSurfaceEquiv a
          ((1 : VietaGroup a) • x) =
        (1 : VietaGroup (directedCycleLeftCoefficients a)) •
          directedCycleLeftSurfaceEquiv a x
    simp
  · intro q r hq hr hqLift hrLift
    obtain ⟨qA, hqA⟩ := hqLift
    obtain ⟨rA, hrA⟩ := hrLift
    refine ⟨qA * rA, fun x => ?_⟩
    change
      directedCycleLeftSurfaceEquiv a ((qA * rA) • x) =
        ((⟨q, hq⟩ :
            VietaGroup (directedCycleLeftCoefficients a)) *
          (⟨r, hr⟩ :
            VietaGroup (directedCycleLeftCoefficients a))) •
              directedCycleLeftSurfaceEquiv a x
    rw [mul_smul, mul_smul, hqA, hrA]
  · intro q hq hqLift
    obtain ⟨qA, hqA⟩ := hqLift
    refine ⟨qA⁻¹, fun x => ?_⟩
    change
      directedCycleLeftSurfaceEquiv a (qA⁻¹ • x) =
        (⟨q, hq⟩ :
          VietaGroup (directedCycleLeftCoefficients a))⁻¹ •
            directedCycleLeftSurfaceEquiv a x
    have h := congrArg
      (fun y =>
        (⟨q, hq⟩ :
          VietaGroup (directedCycleLeftCoefficients a))⁻¹ • y)
      (hqA (qA⁻¹ • x))
    simpa [mul_smul] using h.symm

/-- Full-Vieta connectivity on the left-cycled coefficient surface pulls
back to connectivity on the original fixed-coefficient surface. -/
theorem sameVietaComponent_of_directedCycleLeft
    {R : Type u} [CommRing R] (a : Coefficients R)
    {x y : SolutionSurface a}
    (hxy :
      SameVietaComponent
        (directedCycleLeftSurfaceEquiv a x)
        (directedCycleLeftSurfaceEquiv a y)) :
    SameVietaComponent x y := by
  obtain ⟨g, hg⟩ := hxy
  obtain ⟨h, hh⟩ :=
    exists_VietaGroup_descend_directedCycleLeft a g
  refine ⟨h, ?_⟩
  apply (directedCycleLeftSurfaceEquiv a).injective
  exact (hh x).trans hg

/-- Every full-Vieta word on the right-cycled coefficient surface has a
word on the original fixed-coefficient surface whose action is intertwined
by the simultaneous coefficient-coordinate cycle. -/
theorem exists_VietaGroup_descend_directedCycleRight
    {R : Type u} [CommRing R] (a : Coefficients R)
    (g : VietaGroup (directedCycleRightCoefficients a)) :
    ∃ h : VietaGroup a,
      ∀ x : SolutionSurface a,
        directedCycleRightSurfaceEquiv a (h • x) =
          g • directedCycleRightSurfaceEquiv a x := by
  let motive :
      ∀ q :
          Equiv.Perm
            (SolutionSurface (directedCycleRightCoefficients a)),
        q ∈ Subgroup.closure
            (vietaGenerators (directedCycleRightCoefficients a)) →
          Prop :=
    fun q hq =>
      ∃ h : VietaGroup a,
        ∀ x : SolutionSurface a,
          directedCycleRightSurfaceEquiv a (h • x) =
            (⟨q, hq⟩ :
              VietaGroup (directedCycleRightCoefficients a)) •
                directedCycleRightSurfaceEquiv a x
  apply Subgroup.closure_induction (p := motive)
  · intro q hq
    simp only [vietaGenerators, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · refine ⟨vieta3InVietaGroup a, fun x => ?_⟩
      exact directedCycleRightSurfaceEquiv_vieta3 a x
    · refine ⟨vieta1InVietaGroup a, fun x => ?_⟩
      exact directedCycleRightSurfaceEquiv_vieta1 a x
    · refine ⟨vieta2InVietaGroup a, fun x => ?_⟩
      exact directedCycleRightSurfaceEquiv_vieta2 a x
  · refine ⟨1, fun x => ?_⟩
    change
      directedCycleRightSurfaceEquiv a
          ((1 : VietaGroup a) • x) =
        (1 : VietaGroup (directedCycleRightCoefficients a)) •
          directedCycleRightSurfaceEquiv a x
    simp
  · intro q r hq hr hqLift hrLift
    obtain ⟨qA, hqA⟩ := hqLift
    obtain ⟨rA, hrA⟩ := hrLift
    refine ⟨qA * rA, fun x => ?_⟩
    change
      directedCycleRightSurfaceEquiv a ((qA * rA) • x) =
        ((⟨q, hq⟩ :
            VietaGroup (directedCycleRightCoefficients a)) *
          (⟨r, hr⟩ :
            VietaGroup (directedCycleRightCoefficients a))) •
              directedCycleRightSurfaceEquiv a x
    rw [mul_smul, mul_smul, hqA, hrA]
  · intro q hq hqLift
    obtain ⟨qA, hqA⟩ := hqLift
    refine ⟨qA⁻¹, fun x => ?_⟩
    change
      directedCycleRightSurfaceEquiv a (qA⁻¹ • x) =
        (⟨q, hq⟩ :
          VietaGroup (directedCycleRightCoefficients a))⁻¹ •
            directedCycleRightSurfaceEquiv a x
    have h := congrArg
      (fun y =>
        (⟨q, hq⟩ :
          VietaGroup (directedCycleRightCoefficients a))⁻¹ • y)
      (hqA (qA⁻¹ • x))
    simpa [mul_smul] using h.symm

/-- Full-Vieta connectivity on the right-cycled coefficient surface pulls
back to connectivity on the original fixed-coefficient surface. -/
theorem sameVietaComponent_of_directedCycleRight
    {R : Type u} [CommRing R] (a : Coefficients R)
    {x y : SolutionSurface a}
    (hxy :
      SameVietaComponent
        (directedCycleRightSurfaceEquiv a x)
        (directedCycleRightSurfaceEquiv a y)) :
    SameVietaComponent x y := by
  obtain ⟨g, hg⟩ := hxy
  obtain ⟨h, hh⟩ :=
    exists_VietaGroup_descend_directedCycleRight a g
  refine ⟨h, ?_⟩
  apply (directedCycleRightSurfaceEquiv a).injective
  exact (hh x).trans hg

/-- A good three-root witness in the explicit cyclic frame
`(a₂,a₃,a₁)` joins two primitive connecting second-axis fibers on the
original surface.  The middle fiber is the original third axis. -/
theorem sameVietaComponent_of_connectingSecondAxisThreeRootWitness
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (x y : SolutionSurface a)
    (xi eta omegaInv : ZMod p)
    (htraceX : traceAt a .second x.1 = xi)
    (htraceY : traceAt a .second y.1 = eta)
    (qx qy qm : (ZMod p)ˣ)
    (heigenX : xi = splitTorusTrace qx)
    (heigenY : eta = splitTorusTrace qy)
    (hprimitiveX : orderOf qx = Nat.card (ZMod p)ˣ)
    (hprimitiveY : orderOf qy = Nat.card (ZMod p)ˣ)
    (hregularX :
      OrderedTraceCandidateRegular a.a2 a.a3 a.a1 xi)
    (hregularY :
      OrderedTraceCandidateRegular a.a2 a.a3 a.a1 eta)
    (hconnectingX : ¬ IsSquare (centeredNorm a.a3 a.a1 xi))
    (hconnectingY : ¬ IsSquare (centeredNorm a.a3 a.a1 eta))
    (homegaInv : ¬ IsSquare omegaInv)
    (w :
      ConnectingGoodThreeRootWitness
        (directedCycleLeftCoefficients a) xi eta omegaInv)
    (heigenMiddle : w.1.middle = splitTorusTrace qm)
    (hprimitiveMiddle : orderOf qm = Nat.card (ZMod p)ˣ)
    (hregularMiddle :
      OrderedTraceCandidateRegular a.a3 a.a1 a.a2 w.1.middle) :
    SameVietaComponent x y := by
  apply sameVietaComponent_of_directedCycleLeft a
  exact
    sameVietaComponent_of_connectingThreeRootWitness
      p hpTwo (directedCycleLeftCoefficients a)
      (by simpa using hmultiplier)
      (directedCycleLeftSurfaceEquiv a x)
      (directedCycleLeftSurfaceEquiv a y)
      xi eta omegaInv
      ((traceAt_directedCycleLeft_first a x).trans htraceX)
      ((traceAt_directedCycleLeft_first a y).trans htraceY)
      qx qy qm
      heigenX heigenY
      hprimitiveX hprimitiveY
      (by
        simpa [directedCycleLeftCoefficients] using hregularX)
      (by
        simpa [directedCycleLeftCoefficients] using hregularY)
      (by
        simpa [directedCycleLeftCoefficients] using hconnectingX)
      (by
        simpa [directedCycleLeftCoefficients] using hconnectingY)
      homegaInv w heigenMiddle hprimitiveMiddle
      (by
        simpa [directedCycleLeftCoefficients] using hregularMiddle)

/-- A good three-root witness in the explicit cyclic frame
`(a₃,a₁,a₂)` joins two primitive connecting third-axis fibers on the
original surface.  The middle fiber is the original first axis. -/
theorem sameVietaComponent_of_connectingThirdAxisThreeRootWitness
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (x y : SolutionSurface a)
    (xi eta omegaInv : ZMod p)
    (htraceX : traceAt a .third x.1 = xi)
    (htraceY : traceAt a .third y.1 = eta)
    (qx qy qm : (ZMod p)ˣ)
    (heigenX : xi = splitTorusTrace qx)
    (heigenY : eta = splitTorusTrace qy)
    (hprimitiveX : orderOf qx = Nat.card (ZMod p)ˣ)
    (hprimitiveY : orderOf qy = Nat.card (ZMod p)ˣ)
    (hregularX :
      OrderedTraceCandidateRegular a.a3 a.a1 a.a2 xi)
    (hregularY :
      OrderedTraceCandidateRegular a.a3 a.a1 a.a2 eta)
    (hconnectingX : ¬ IsSquare (centeredNorm a.a1 a.a2 xi))
    (hconnectingY : ¬ IsSquare (centeredNorm a.a1 a.a2 eta))
    (homegaInv : ¬ IsSquare omegaInv)
    (w :
      ConnectingGoodThreeRootWitness
        (directedCycleRightCoefficients a) xi eta omegaInv)
    (heigenMiddle : w.1.middle = splitTorusTrace qm)
    (hprimitiveMiddle : orderOf qm = Nat.card (ZMod p)ˣ)
    (hregularMiddle :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 w.1.middle) :
    SameVietaComponent x y := by
  apply sameVietaComponent_of_directedCycleRight a
  exact
    sameVietaComponent_of_connectingThreeRootWitness
      p hpTwo (directedCycleRightCoefficients a)
      (by simpa using hmultiplier)
      (directedCycleRightSurfaceEquiv a x)
      (directedCycleRightSurfaceEquiv a y)
      xi eta omegaInv
      ((traceAt_directedCycleRight_first a x).trans htraceX)
      ((traceAt_directedCycleRight_first a y).trans htraceY)
      qx qy qm
      heigenX heigenY
      hprimitiveX hprimitiveY
      (by
        simpa [directedCycleRightCoefficients] using hregularX)
      (by
        simpa [directedCycleRightCoefficients] using hregularY)
      (by
        simpa [directedCycleRightCoefficients] using hconnectingX)
      (by
        simpa [directedCycleRightCoefficients] using hconnectingY)
      homegaInv w heigenMiddle hprimitiveMiddle
      (by
        simpa [directedCycleRightCoefficients] using hregularMiddle)

end

end GenMarkoff.General.Cage
