import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# The generalized Markoff surface

This file defines, over a commutative ring, the generalized Markoff polynomial
`x₁² + x₂² + x₃² + a₁x₂x₃ + a₂x₃x₁ + a₃x₁x₂ - (3 + a₁ + a₂ + a₃)x₁x₂x₃`,
the points `origin` and `unitPoint` that lie on every such surface, the three
Vieta involutions `vieta1`, `vieta2`, `vieta3` and the two-Vieta rotations
`rotation1`, `rotation2`, `rotation3`, all of which preserve the polynomial.
It also defines coordinatewise base change `Point.map` and `Coefficients.map`
and shows that it commutes with the rotations.

The coefficient triple is kept explicit because coordinate permutations do
not preserve a fixed generalized surface in general.
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

/-- The first two-Vieta rotation `R₁ = μ₃ ∘ μ₂`. -/
def rotation1 {R : Type u} [CommRing R] (a : Coefficients R) (x : Point R) : Point R :=
  vieta3 a (vieta2 a x)

/-- The second two-Vieta rotation `R₂ = μ₁ ∘ μ₃`. -/
def rotation2 {R : Type u} [CommRing R] (a : Coefficients R) (x : Point R) : Point R :=
  vieta1 a (vieta3 a x)

/-- The third two-Vieta rotation `R₃ = μ₂ ∘ μ₁`. -/
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
  -- `unitPoint.x1` and `origin.x1` unfold to `1` and `0`; restate so that
  -- `one_ne_zero` applies.
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

/-- The two-Vieta rotation `R₁` as a permutation. -/
def rotation1Equiv (R : Type u) [CommRing R] (a : Coefficients R) : Equiv.Perm (Point R) :=
  (vieta2Equiv R a).trans (vieta3Equiv R a)

/-- The two-Vieta rotation `R₂` as a permutation. -/
def rotation2Equiv (R : Type u) [CommRing R] (a : Coefficients R) : Equiv.Perm (Point R) :=
  (vieta3Equiv R a).trans (vieta1Equiv R a)

/-- The two-Vieta rotation `R₃` as a permutation. -/
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

@[simp]
theorem isSolution_iterate_rotation1 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) (n : ℕ) :
    IsSolution a (((rotation1 a)^[n]) x) ↔ IsSolution a x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', isSolution_rotation1, ih]

@[simp]
theorem isSolution_iterate_rotation2 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) (n : ℕ) :
    IsSolution a (((rotation2 a)^[n]) x) ↔ IsSolution a x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', isSolution_rotation2, ih]

@[simp]
theorem isSolution_iterate_rotation3 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) (n : ℕ) :
    IsSolution a (((rotation3 a)^[n]) x) ↔ IsSolution a x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', isSolution_rotation3, ih]

/-- `R₁` fixes the first coordinate. -/
@[simp]
theorem rotation1_firstCoordinate {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    (rotation1 a x).x1 = x.x1 :=
  rfl

@[simp]
theorem iterate_rotation1_firstCoordinate {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) (n : ℕ) :
    (((rotation1 a)^[n]) x).x1 = x.x1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', rotation1_firstCoordinate, ih]

/-- `R₂` fixes the second coordinate. -/
@[simp]
theorem rotation2_secondCoordinate {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    (rotation2 a x).x2 = x.x2 :=
  rfl

@[simp]
theorem iterate_rotation2_secondCoordinate {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) (n : ℕ) :
    (((rotation2 a)^[n]) x).x2 = x.x2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', rotation2_secondCoordinate, ih]

/-- `R₃` fixes the third coordinate. -/
@[simp]
theorem rotation3_thirdCoordinate {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    (rotation3 a x).x3 = x.x3 :=
  rfl

@[simp]
theorem iterate_rotation3_thirdCoordinate {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) (n : ℕ) :
    (((rotation3 a)^[n]) x).x3 = x.x3 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', rotation3_thirdCoordinate, ih]

/-- Apply a ring homomorphism coordinatewise to a point. -/
def Point.map
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (x : Point R) : Point S :=
  ⟨f x.x1, f x.x2, f x.x3⟩

@[simp]
theorem Point.map_x1 {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (x : Point R) : (Point.map f x).x1 = f x.x1 :=
  rfl

@[simp]
theorem Point.map_x2 {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (x : Point R) : (Point.map f x).x2 = f x.x2 :=
  rfl

@[simp]
theorem Point.map_x3 {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (x : Point R) : (Point.map f x).x3 = f x.x3 :=
  rfl

/-- Apply a ring homomorphism coefficientwise. -/
def Coefficients.map
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (a : Coefficients R) : Coefficients S :=
  ⟨f a.a1, f a.a2, f a.a3⟩

@[simp]
theorem Coefficients.map_a1
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (a : Coefficients R) :
    (Coefficients.map f a).a1 = f a.a1 :=
  rfl

@[simp]
theorem Coefficients.map_a2
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (a : Coefficients R) :
    (Coefficients.map f a).a2 = f a.a2 :=
  rfl

@[simp]
theorem Coefficients.map_a3
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (a : Coefficients R) :
    (Coefficients.map f a).a3 = f a.a3 :=
  rfl

@[simp]
theorem Coefficients.map_multiplier
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (a : Coefficients R) :
    (Coefficients.map f a).multiplier = f a.multiplier := by
  simp [Coefficients.map, Coefficients.multiplier, map_ofNat]

/-- Scalar extension commutes with the first two-Vieta rotation. -/
theorem Point.map_rotation1
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Coefficients R) (x : Point R) :
    Point.map f (rotation1 a x) = rotation1 (Coefficients.map f a) (Point.map f x) := by
  ext <;>
    simp [Point.map, rotation1, vieta2, vieta3, Coefficients.map,
      Coefficients.multiplier, map_ofNat]

/-- Scalar extension commutes with the second two-Vieta rotation. -/
theorem Point.map_rotation2
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Coefficients R) (x : Point R) :
    Point.map f (rotation2 a x) = rotation2 (Coefficients.map f a) (Point.map f x) := by
  ext <;>
    simp [Point.map, rotation2, vieta1, vieta3, Coefficients.map,
      Coefficients.multiplier, map_ofNat]

/-- Scalar extension commutes with the third two-Vieta rotation. -/
theorem Point.map_rotation3
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Coefficients R) (x : Point R) :
    Point.map f (rotation3 a x) = rotation3 (Coefficients.map f a) (Point.map f x) := by
  ext <;>
    simp [Point.map, rotation3, vieta1, vieta2, Coefficients.map,
      Coefficients.multiplier, map_ofNat]

theorem Point.map_iterate_rotation1
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Coefficients R) (x : Point R) (n : ℕ) :
    Point.map f (((rotation1 a)^[n]) x) =
      ((rotation1 (Coefficients.map f a))^[n]) (Point.map f x) :=
  Function.Semiconj.iterate_right (Point.map_rotation1 f a) n x

theorem Point.map_iterate_rotation2
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Coefficients R) (x : Point R) (n : ℕ) :
    Point.map f (((rotation2 a)^[n]) x) =
      ((rotation2 (Coefficients.map f a))^[n]) (Point.map f x) :=
  Function.Semiconj.iterate_right (Point.map_rotation2 f a) n x

theorem Point.map_iterate_rotation3
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Coefficients R) (x : Point R) (n : ℕ) :
    Point.map f (((rotation3 a)^[n]) x) =
      ((rotation3 (Coefficients.map f a))^[n]) (Point.map f x) :=
  Function.Semiconj.iterate_right (Point.map_rotation3 f a) n x

end GenMarkoff
