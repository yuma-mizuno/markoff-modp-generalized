import Mathlib

/-!
# The generalized Markoff surface

This file formalizes the equation and Vieta involutions from
`Paper/Modp/markov_modp.tex`.  The coefficient triple is kept explicit because
coordinate permutations do not preserve a fixed generalized surface in
general.
-/

namespace GenMarkoff

universe u

/-- The three coefficients in the generalized Markoff equation. -/
@[ext]
structure Coefficients (R : Type u) where
  /-- The coefficient of `x₂x₃`. -/
  a1 : R
  /-- The coefficient of `x₃x₁`. -/
  a2 : R
  /-- The coefficient of `x₁x₂`. -/
  a3 : R
deriving DecidableEq, Repr, Fintype

/-- The cubic multiplier `s = 3 + a₁ + a₂ + a₃`. -/
def Coefficients.multiplier {R : Type u} [OfNat R 3] [Add R]
    (a : Coefficients R) : R :=
  3 + a.a1 + a.a2 + a.a3

/-- Reduce a fixed integral coefficient triple into a commutative ring. -/
def Coefficients.intCast (a : Coefficients ℤ) (R : Type u) [CommRing R] :
    Coefficients R :=
  ⟨(a.a1 : R), (a.a2 : R), (a.a3 : R)⟩

/-- A point of affine three-space. -/
@[ext]
structure Point (R : Type u) where
  /-- The first coordinate. -/
  x1 : R
  /-- The second coordinate. -/
  x2 : R
  /-- The third coordinate. -/
  x3 : R
deriving DecidableEq, Repr, Fintype

/-- The origin in affine three-space. -/
def origin {R : Type u} [Zero R] : Point R :=
  ⟨0, 0, 0⟩

/-- The point `(1, 1, 1)`, which lies on every generalized Markoff surface. -/
def unitPoint {R : Type u} [One R] : Point R :=
  ⟨1, 1, 1⟩

/-- The polynomial whose zero locus is the generalized Markoff surface. -/
def polynomial {R : Type u} [CommRing R] (a : Coefficients R) (x : Point R) : R :=
  x.x1 ^ 2 + x.x2 ^ 2 + x.x3 ^ 2
    + a.a1 * x.x2 * x.x3 + a.a2 * x.x3 * x.x1 + a.a3 * x.x1 * x.x2
    - a.multiplier * x.x1 * x.x2 * x.x3

/-- A point satisfies the generalized Markoff equation. -/
def IsSolution {R : Type u} [CommRing R] (a : Coefficients R) (x : Point R) : Prop :=
  polynomial a x = 0

/-- The generalized Markoff surface as a set. -/
def surface (R : Type u) [CommRing R] (a : Coefficients R) : Set (Point R) :=
  {x | IsSolution a x}

/-- The generalized Markoff surface with only the origin removed. -/
def puncturedSurface (R : Type u) [CommRing R] (a : Coefficients R) : Set (Point R) :=
  surface R a \ {origin}

/-- The first Vieta involution. -/
def vieta1 {R : Type u} [CommRing R] (a : Coefficients R) (x : Point R) : Point R :=
  ⟨a.multiplier * x.x2 * x.x3 - x.x1 - a.a3 * x.x2 - a.a2 * x.x3,
    x.x2, x.x3⟩

/-- The second Vieta involution. -/
def vieta2 {R : Type u} [CommRing R] (a : Coefficients R) (x : Point R) : Point R :=
  ⟨x.x1,
    a.multiplier * x.x3 * x.x1 - x.x2 - a.a1 * x.x3 - a.a3 * x.x1,
    x.x3⟩

/-- The third Vieta involution. -/
def vieta3 {R : Type u} [CommRing R] (a : Coefficients R) (x : Point R) : Point R :=
  ⟨x.x1, x.x2,
    a.multiplier * x.x1 * x.x2 - x.x3 - a.a2 * x.x1 - a.a1 * x.x2⟩

/-- The rotation `R₁ = μ₃ ∘ μ₂` from the source note. -/
def rotation1 {R : Type u} [CommRing R] (a : Coefficients R) (x : Point R) : Point R :=
  vieta3 a (vieta2 a x)

/-- The rotation `R₂ = μ₁ ∘ μ₃` from the source note. -/
def rotation2 {R : Type u} [CommRing R] (a : Coefficients R) (x : Point R) : Point R :=
  vieta1 a (vieta3 a x)

/-- The rotation `R₃ = μ₂ ∘ μ₁` from the source note. -/
def rotation3 {R : Type u} [CommRing R] (a : Coefficients R) (x : Point R) : Point R :=
  vieta2 a (vieta1 a x)

@[simp]
theorem polynomial_origin {R : Type u} [CommRing R] (a : Coefficients R) :
    polynomial a (origin : Point R) = 0 := by
  simp [polynomial, origin]

@[simp]
theorem isSolution_origin {R : Type u} [CommRing R] (a : Coefficients R) :
    IsSolution a (origin : Point R) := by
  simp [IsSolution]

@[simp]
theorem polynomial_unitPoint {R : Type u} [CommRing R] (a : Coefficients R) :
    polynomial a (unitPoint : Point R) = 0 := by
  simp [polynomial, unitPoint, Coefficients.multiplier]
  ring

@[simp]
theorem isSolution_unitPoint {R : Type u} [CommRing R] (a : Coefficients R) :
    IsSolution a (unitPoint : Point R) := by
  simp [IsSolution]

theorem unitPoint_ne_origin {R : Type u} [CommRing R] [Nontrivial R] :
    (unitPoint : Point R) ≠ origin := by
  intro h
  have h1 := congrArg Point.x1 h
  change (1 : R) = 0 at h1
  exact (one_ne_zero : (1 : R) ≠ 0) h1

theorem polynomial_vieta1 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    polynomial a (vieta1 a x) = polynomial a x := by
  simp [polynomial, vieta1]
  ring

theorem polynomial_vieta2 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    polynomial a (vieta2 a x) = polynomial a x := by
  simp [polynomial, vieta2]
  ring

theorem polynomial_vieta3 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    polynomial a (vieta3 a x) = polynomial a x := by
  simp [polynomial, vieta3]
  ring

@[simp]
theorem isSolution_vieta1 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    IsSolution a (vieta1 a x) ↔ IsSolution a x := by
  simp only [IsSolution, polynomial_vieta1]

@[simp]
theorem isSolution_vieta2 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    IsSolution a (vieta2 a x) ↔ IsSolution a x := by
  simp only [IsSolution, polynomial_vieta2]

@[simp]
theorem isSolution_vieta3 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    IsSolution a (vieta3 a x) ↔ IsSolution a x := by
  simp only [IsSolution, polynomial_vieta3]

@[simp]
theorem vieta1_involutive {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    vieta1 a (vieta1 a x) = x := by
  ext
  · simp [vieta1]
    ring
  · rfl
  · rfl

@[simp]
theorem vieta2_involutive {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    vieta2 a (vieta2 a x) = x := by
  ext
  · rfl
  · simp [vieta2]
    ring
  · rfl

@[simp]
theorem vieta3_involutive {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    vieta3 a (vieta3 a x) = x := by
  ext
  · rfl
  · rfl
  · simp [vieta3]
    ring

/-- The first Vieta move as a permutation of affine three-space. -/
def vieta1Equiv (R : Type u) [CommRing R] (a : Coefficients R) : Equiv.Perm (Point R) where
  toFun := vieta1 a
  invFun := vieta1 a
  left_inv := vieta1_involutive a
  right_inv := vieta1_involutive a

/-- The second Vieta move as a permutation of affine three-space. -/
def vieta2Equiv (R : Type u) [CommRing R] (a : Coefficients R) : Equiv.Perm (Point R) where
  toFun := vieta2 a
  invFun := vieta2 a
  left_inv := vieta2_involutive a
  right_inv := vieta2_involutive a

/-- The third Vieta move as a permutation of affine three-space. -/
def vieta3Equiv (R : Type u) [CommRing R] (a : Coefficients R) : Equiv.Perm (Point R) where
  toFun := vieta3 a
  invFun := vieta3 a
  left_inv := vieta3_involutive a
  right_inv := vieta3_involutive a

/-- The source rotation `R₁` as a permutation. -/
def rotation1Equiv (R : Type u) [CommRing R] (a : Coefficients R) : Equiv.Perm (Point R) :=
  (vieta2Equiv R a).trans (vieta3Equiv R a)

/-- The source rotation `R₂` as a permutation. -/
def rotation2Equiv (R : Type u) [CommRing R] (a : Coefficients R) : Equiv.Perm (Point R) :=
  (vieta3Equiv R a).trans (vieta1Equiv R a)

/-- The source rotation `R₃` as a permutation. -/
def rotation3Equiv (R : Type u) [CommRing R] (a : Coefficients R) : Equiv.Perm (Point R) :=
  (vieta1Equiv R a).trans (vieta2Equiv R a)

theorem polynomial_rotation1 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    polynomial a (rotation1 a x) = polynomial a x := by
  unfold rotation1
  rw [polynomial_vieta3, polynomial_vieta2]

theorem polynomial_rotation2 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    polynomial a (rotation2 a x) = polynomial a x := by
  unfold rotation2
  rw [polynomial_vieta1, polynomial_vieta3]

theorem polynomial_rotation3 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    polynomial a (rotation3 a x) = polynomial a x := by
  unfold rotation3
  rw [polynomial_vieta2, polynomial_vieta1]

@[simp]
theorem isSolution_rotation1 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    IsSolution a (rotation1 a x) ↔ IsSolution a x := by
  simp only [IsSolution, polynomial_rotation1]

@[simp]
theorem isSolution_rotation2 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    IsSolution a (rotation2 a x) ↔ IsSolution a x := by
  simp only [IsSolution, polynomial_rotation2]

@[simp]
theorem isSolution_rotation3 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    IsSolution a (rotation3 a x) ↔ IsSolution a x := by
  simp only [IsSolution, polynomial_rotation3]

end GenMarkoff
