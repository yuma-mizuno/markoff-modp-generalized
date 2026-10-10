import GenMarkoff.Core.Statements
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Category.Ring.Basic

/-!
# Reduction surjectivity from Vieta connectedness

For a fixed integral coefficient triple, the generalized Markoff surface is
functorial under homomorphisms of commutative rings.  This module proves that
punctured transitivity of the full Vieta group modulo a prime implies
surjectivity of coordinatewise reduction from integral solutions.

The origin is handled separately because every Vieta move fixes it.  Every
other residue solution is reached from `(1, 1, 1)` by a Vieta word.  The same
word is defined over the integers and commutes with reduction, so applying it
to the integral point `(1, 1, 1)` supplies the required lift.
-/

open CategoryTheory

namespace GenMarkoff.General.Assembly

universe u v

/-- The generalized Markoff surface with a fixed integral coefficient triple,
viewed functorially over commutative rings. -/
def fixedIntegralCoefficientSurfaceFunctor
    (a : Coefficients ℤ) : CommRingCat ⥤ Type where
  obj R := {⟨x₁, x₂, x₃⟩ : R × R × R |
    x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2
      + (a.a1 : R) * x₂ * x₃
      + (a.a2 : R) * x₃ * x₁
      + (a.a3 : R) * x₁ * x₂
      - (3 + (a.a1 : R) + (a.a2 : R) + (a.a3 : R)) * x₁ * x₂ * x₃ = 0}
  map f := ↾fun ⟨⟨x₁, x₂, x₃⟩, hx⟩ ↦
    ⟨⟨f.hom x₁, f.hom x₂, f.hom x₃⟩, by
      simpa only [Set.mem_setOf_eq, map_add, map_sub, map_mul, map_pow,
        map_zero, map_ofNat, map_intCast] using congrArg f.hom hx⟩

/-- The triple presentation `fixedIntegralCoefficientSurfaceFunctor` of the
fixed integral surface agrees with the structured solution surface used by
the Vieta action. -/
def fixedIntegralCoefficientSurfaceEquivSolutionSurface
    (a : Coefficients ℤ) (R : Type) [CommRing R] :
    (fixedIntegralCoefficientSurfaceFunctor a).obj (CommRingCat.of R) ≃
      SolutionSurface (a.intCast R) where
  toFun x :=
    ⟨⟨x.1.1, x.1.2.1, x.1.2.2⟩, by
      simpa only [Set.mem_setOf_eq, IsSolution, polynomial,
        Coefficients.intCast, Coefficients.multiplier] using x.2⟩
  invFun x :=
    ⟨⟨x.1.x1, x.1.x2, x.1.x3⟩, by
      rcases x with ⟨⟨x₁, x₂, x₃⟩, hx⟩
      simpa only [Set.mem_setOf_eq, IsSolution, polynomial,
        Coefficients.intCast, Coefficients.multiplier] using hx⟩
  left_inv x := by
    apply Subtype.ext
    cases x.1
    rfl
  right_inv x := by
    apply Subtype.ext
    cases x.1
    rfl

/-- Coordinatewise base change on the structured surface attached to a fixed
integral coefficient triple. -/
def fixedIntegralCoefficientSurfaceMap
    (a : Coefficients ℤ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) :
    SolutionSurface (a.intCast R) → SolutionSurface (a.intCast S) :=
  fun x ↦
    ⟨Point.map f x.1, by
      -- `IsSolution` unfolds to `polynomial _ _ = 0`; state the equation so
      -- that `simpa` can match it with the image of `x.2` under `f`.
      change polynomial (a.intCast S) (Point.map f x.1) = 0
      have hmap := congrArg f x.2
      simpa [IsSolution, polynomial, Point.map,
        Coefficients.intCast, Coefficients.multiplier, map_ofNat] using hmap⟩

@[simp]
theorem fixedIntegralCoefficientSurfaceEquivSolutionSurface_map
    (a : Coefficients ℤ) {R S : Type}
    [CommRing R] [CommRing S] (f : R →+* S)
    (x :
      (fixedIntegralCoefficientSurfaceFunctor a).obj (CommRingCat.of R)) :
    fixedIntegralCoefficientSurfaceEquivSolutionSurface a S
        ((fixedIntegralCoefficientSurfaceFunctor a).map
          (CommRingCat.ofHom f) x) =
      fixedIntegralCoefficientSurfaceMap a f
        (fixedIntegralCoefficientSurfaceEquivSolutionSurface a R x) := by
  apply Subtype.ext
  ext <;> rfl

@[simp]
theorem fixedIntegralCoefficientSurfaceMap_origin
    (a : Coefficients ℤ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) :
    fixedIntegralCoefficientSurfaceMap a f
        (surfaceOrigin (a.intCast R)) =
      surfaceOrigin (a.intCast S) := by
  apply Subtype.ext
  ext <;>
    simp [fixedIntegralCoefficientSurfaceMap, Point.map,
      surfaceOrigin, origin]

@[simp]
theorem fixedIntegralCoefficientSurfaceMap_unit
    (a : Coefficients ℤ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) :
    fixedIntegralCoefficientSurfaceMap a f
        (surfaceUnit (a.intCast R)) =
      surfaceUnit (a.intCast S) := by
  apply Subtype.ext
  ext <;>
    simp [fixedIntegralCoefficientSurfaceMap, Point.map,
      surfaceUnit, unitPoint]

@[simp]
theorem fixedIntegralCoefficientSurfaceMap_vieta1
    (a : Coefficients ℤ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S)
    (x : SolutionSurface (a.intCast R)) :
    fixedIntegralCoefficientSurfaceMap a f
        (vieta1SurfacePerm (a.intCast R) x) =
      vieta1SurfacePerm (a.intCast S)
        (fixedIntegralCoefficientSurfaceMap a f x) := by
  apply Subtype.ext
  -- `fixedIntegralCoefficientSurfaceMap` is `Point.map f` on values and
  -- `vieta1SurfacePerm` is `vieta1`; restate on points so `ext; simp` applies.
  change Point.map f (vieta1 (a.intCast R) x.1) =
    vieta1 (a.intCast S) (Point.map f x.1)
  ext <;>
    simp [Point.map, vieta1, Coefficients.intCast,
      Coefficients.multiplier, map_ofNat]

@[simp]
theorem fixedIntegralCoefficientSurfaceMap_vieta2
    (a : Coefficients ℤ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S)
    (x : SolutionSurface (a.intCast R)) :
    fixedIntegralCoefficientSurfaceMap a f
        (vieta2SurfacePerm (a.intCast R) x) =
      vieta2SurfacePerm (a.intCast S)
        (fixedIntegralCoefficientSurfaceMap a f x) := by
  apply Subtype.ext
  -- `fixedIntegralCoefficientSurfaceMap` is `Point.map f` on values and
  -- `vieta2SurfacePerm` is `vieta2`; restate on points so `ext; simp` applies.
  change Point.map f (vieta2 (a.intCast R) x.1) =
    vieta2 (a.intCast S) (Point.map f x.1)
  ext <;>
    simp [Point.map, vieta2, Coefficients.intCast,
      Coefficients.multiplier, map_ofNat]

@[simp]
theorem fixedIntegralCoefficientSurfaceMap_vieta3
    (a : Coefficients ℤ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S)
    (x : SolutionSurface (a.intCast R)) :
    fixedIntegralCoefficientSurfaceMap a f
        (vieta3SurfacePerm (a.intCast R) x) =
      vieta3SurfacePerm (a.intCast S)
        (fixedIntegralCoefficientSurfaceMap a f x) := by
  apply Subtype.ext
  -- `fixedIntegralCoefficientSurfaceMap` is `Point.map f` on values and
  -- `vieta3SurfacePerm` is `vieta3`; restate on points so `ext; simp` applies.
  change Point.map f (vieta3 (a.intCast R) x.1) =
    vieta3 (a.intCast S) (Point.map f x.1)
  ext <;>
    simp [Point.map, vieta3, Coefficients.intCast,
      Coefficients.multiplier, map_ofNat]

/-- Every Vieta word over the target ring lifts to the same word over the
source ring, and the two actions commute with base change. -/
theorem exists_fixedIntegralVietaGroup_lift
    (a : Coefficients ℤ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S)
    (g : VietaGroup (a.intCast S)) :
    ∃ h : VietaGroup (a.intCast R),
      ∀ x : SolutionSurface (a.intCast R),
        fixedIntegralCoefficientSurfaceMap a f (h • x) =
          g • fixedIntegralCoefficientSurfaceMap a f x := by
  let motive :
      ∀ q : Equiv.Perm (SolutionSurface (a.intCast S)),
        q ∈ Subgroup.closure (vietaGenerators (a.intCast S)) → Prop :=
    fun q hq ↦
      ∃ h : VietaGroup (a.intCast R),
        ∀ x : SolutionSurface (a.intCast R),
          fixedIntegralCoefficientSurfaceMap a f (h • x) =
            (⟨q, hq⟩ : VietaGroup (a.intCast S)) •
              fixedIntegralCoefficientSurfaceMap a f x
  -- Closure induction: the three generators, `1`, products and inverses.
  apply Subgroup.closure_induction (p := motive)
  · intro q hq
    simp only [vietaGenerators, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · refine
        ⟨⟨vieta1SurfacePerm (a.intCast R),
            vieta1SurfacePerm_mem_VietaGroup (a.intCast R)⟩, fun x ↦ ?_⟩
      exact fixedIntegralCoefficientSurfaceMap_vieta1 a f x
    · refine
        ⟨⟨vieta2SurfacePerm (a.intCast R),
            vieta2SurfacePerm_mem_VietaGroup (a.intCast R)⟩, fun x ↦ ?_⟩
      exact fixedIntegralCoefficientSurfaceMap_vieta2 a f x
    · refine
        ⟨⟨vieta3SurfacePerm (a.intCast R),
            vieta3SurfacePerm_mem_VietaGroup (a.intCast R)⟩, fun x ↦ ?_⟩
      exact fixedIntegralCoefficientSurfaceMap_vieta3 a f x
  · refine ⟨1, fun x ↦ ?_⟩
    -- The subgroup element `⟨1, _⟩` is `(1 : VietaGroup _)` by definition;
    -- restate with `1` so that `simp` can use `one_smul`.
    change fixedIntegralCoefficientSurfaceMap a f
        ((1 : VietaGroup (a.intCast R)) • x) =
      (1 : VietaGroup (a.intCast S)) •
        fixedIntegralCoefficientSurfaceMap a f x
    simp
  · intro q r hq hr hqLift hrLift
    obtain ⟨qR, hqR⟩ := hqLift
    obtain ⟨rR, hrR⟩ := hrLift
    refine ⟨qR * rR, fun x ↦ ?_⟩
    -- The subgroup element `⟨q * r, _⟩` is the product `⟨q, hq⟩ * ⟨r, hr⟩` by
    -- definition; restate as a product so that `mul_smul` rewrites it.
    change fixedIntegralCoefficientSurfaceMap a f ((qR * rR) • x) =
      ((⟨q, hq⟩ : VietaGroup (a.intCast S)) *
        (⟨r, hr⟩ : VietaGroup (a.intCast S))) •
          fixedIntegralCoefficientSurfaceMap a f x
    rw [mul_smul, mul_smul, hqR, hrR]
  · intro q hq hqLift
    obtain ⟨qR, hqR⟩ := hqLift
    refine ⟨qR⁻¹, fun x ↦ ?_⟩
    -- The subgroup element `⟨q⁻¹, _⟩` is the inverse `⟨q, hq⟩⁻¹` by
    -- definition; restate as an inverse so that `hqR` and `mul_smul` apply.
    change fixedIntegralCoefficientSurfaceMap a f (qR⁻¹ • x) =
      (⟨q, hq⟩ : VietaGroup (a.intCast S))⁻¹ •
        fixedIntegralCoefficientSurfaceMap a f x
    have h := congrArg
      (fun y ↦ (⟨q, hq⟩ : VietaGroup (a.intCast S))⁻¹ • y)
      (hqR (qR⁻¹ • x))
    simpa [mul_smul] using h.symm

/-- Punctured Vieta transitivity modulo a prime implies surjectivity of
coordinatewise reduction from the fixed integral generalized surface. -/
theorem reduction_surjective_of_vietaStrongApproximationAt
    (a : Coefficients ℤ) (p : ℕ) (hp : p.Prime)
    (htransitive : VietaStrongApproximationAt a p hp) :
    Function.Surjective
      ((fixedIntegralCoefficientSurfaceFunctor a).map
        (CommRingCat.ofHom (Int.castRingHom (ZMod p)))) := by
  letI : Fact p.Prime := ⟨hp⟩
  -- `VietaStrongApproximationAt` unfolds, through
  -- `modCoefficients a p = a.intCast (ZMod p)`, to punctured transitivity;
  -- restate it with `a.intCast`, the coefficients used below.
  change
    ∀ x y : PuncturedSolutionSurface (a.intCast (ZMod p)),
      ∃ g : VietaGroup (a.intCast (ZMod p)), g • x = y
    at htransitive
  have hsurface :
      Function.Surjective
        (fixedIntegralCoefficientSurfaceMap a
          (Int.castRingHom (ZMod p))) := by
    intro y
    -- The origin lifts to the origin; any other point is the image of
    -- `(1, 1, 1)` under a Vieta word, which lifts to the integers.
    by_cases hy : y = surfaceOrigin (a.intCast (ZMod p))
    · refine ⟨surfaceOrigin (a.intCast ℤ), ?_⟩
      simp [hy]
    · let root :
          PuncturedSolutionSurface (a.intCast (ZMod p)) :=
        ⟨surfaceUnit (a.intCast (ZMod p)),
          surfaceUnit_ne_surfaceOrigin (a.intCast (ZMod p))⟩
      let target :
          PuncturedSolutionSurface (a.intCast (ZMod p)) :=
        ⟨y, hy⟩
      obtain ⟨g, hg⟩ := htransitive root target
      obtain ⟨h, hh⟩ :=
        exists_fixedIntegralVietaGroup_lift a
          (Int.castRingHom (ZMod p)) g
      refine ⟨h • surfaceUnit (a.intCast ℤ), ?_⟩
      calc
        fixedIntegralCoefficientSurfaceMap a
            (Int.castRingHom (ZMod p))
            (h • surfaceUnit (a.intCast ℤ)) =
            g • fixedIntegralCoefficientSurfaceMap a
              (Int.castRingHom (ZMod p))
              (surfaceUnit (a.intCast ℤ)) := hh _
        _ = g • surfaceUnit (a.intCast (ZMod p)) := by
          exact congrArg (fun z ↦ g • z)
            (fixedIntegralCoefficientSurfaceMap_unit
              (R := ℤ) (S := ZMod p) a
              (Int.castRingHom (ZMod p)))
        _ = y := by
          have hval := congrArg Subtype.val hg
          -- The punctured action is `g • _` on values, `root.1` is
          -- `surfaceUnit _` and `target.1` is `y`; restate `hval` accordingly.
          change g • surfaceUnit (a.intCast (ZMod p)) = y at hval
          exact hval
  -- Transfer surjectivity to the triple presentation of the functor.
  intro y
  obtain ⟨x, hx⟩ :=
    hsurface
      (fixedIntegralCoefficientSurfaceEquivSolutionSurface a (ZMod p) y)
  refine
    ⟨(fixedIntegralCoefficientSurfaceEquivSolutionSurface a ℤ).symm x, ?_⟩
  apply
    (fixedIntegralCoefficientSurfaceEquivSolutionSurface a (ZMod p)).injective
  simpa using hx

end GenMarkoff.General.Assembly
