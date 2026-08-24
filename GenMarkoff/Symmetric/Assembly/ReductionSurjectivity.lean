import GenMarkoff.Symmetric.Assembly.StrongApproximation
import GenMarkoff.Symmetric.Opening.ReturnExponentBound

/-!
# Reduction surjectivity for the symmetric family

This module turns the completed finite-field one-step transitivity theorem
into the short arithmetic endpoint used by Comparator: every solution modulo
a sufficiently large prime lifts to an integral solution.
-/

open CategoryTheory

namespace GenMarkoff.Symmetric

universe u v

/-- The equal-coefficient generalized Markoff surface as a functor on
commutative rings. -/
def Markoff (c : ℤ) : CommRingCat ⥤ Type where
  obj R := {⟨x, y, z⟩ : R × R × R |
    x ^ 2 + y ^ 2 + z ^ 2 + (c : R) * (y * z + z * x + x * y) -
      3 * (1 + (c : R)) * x * y * z = 0}
  map f := ↾fun ⟨⟨x, y, z⟩, h⟩ ↦ ⟨⟨f.hom x, f.hom y, f.hom z⟩, by
    simpa only [Set.mem_setOf_eq, map_add, map_sub, map_mul, map_pow,
      map_zero, map_one, map_ofNat, map_intCast] using congrArg f.hom h⟩

/-- The public triple presentation agrees with the structured surface used by
the one-step dynamical development. -/
def markoffEquivSolutionSurface (c : ℤ) (R : Type) [CommRing R] :
    (Markoff c).obj (CommRingCat.of R) ≃
      SolutionSurface (coefficients (c : R)) where
  toFun x :=
    ⟨⟨x.1.1, x.1.2.1, x.1.2.2⟩, by
      simpa only [Set.mem_setOf_eq, IsSolution, polynomial_mk, multiplier]
        using x.2⟩
  invFun x :=
    ⟨⟨x.1.x1, x.1.x2, x.1.x3⟩, by
      rcases x with ⟨⟨x₁, x₂, x₃⟩, hx⟩
      simpa only [Set.mem_setOf_eq, IsSolution, polynomial_mk, multiplier]
        using hx⟩
  left_inv x := by
    apply Subtype.ext
    cases x.1
    rfl
  right_inv x := by
    apply Subtype.ext
    cases x.1
    rfl

/-- Coordinatewise transport of the fixed integral symmetric surface. -/
def surfaceMap (c : ℤ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) :
    SolutionSurface (coefficients (c : R)) →
      SolutionSurface (coefficients (c : S)) :=
  fun x ↦
    ⟨Opening.mapPoint f x.1, by
      simpa using
        Opening.isSolution_mapPoint_symmetric f (c : R) x.1 x.2⟩

@[simp]
theorem markoffEquivSolutionSurface_map
    (c : ℤ) {R S : Type}
    [CommRing R] [CommRing S] (f : R →+* S)
    (x : (Markoff c).obj (CommRingCat.of R)) :
    markoffEquivSolutionSurface c S
        ((Markoff c).map (CommRingCat.ofHom f) x) =
      surfaceMap c f (markoffEquivSolutionSurface c R x) := by
  apply Subtype.ext
  ext <;> rfl

@[simp]
theorem surfaceMap_origin
    (c : ℤ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) :
    surfaceMap c f (surfaceOrigin (coefficients (c : R))) =
      surfaceOrigin (coefficients (c : S)) := by
  apply Subtype.ext
  ext <;> simp [surfaceMap, Opening.mapPoint, surfaceOrigin, origin]

@[simp]
theorem surfaceMap_unit
    (c : ℤ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) :
    surfaceMap c f (surfaceUnit (coefficients (c : R))) =
      surfaceUnit (coefficients (c : S)) := by
  apply Subtype.ext
  ext <;> simp [surfaceMap, Opening.mapPoint, surfaceUnit, unitPoint]

@[simp]
theorem surfaceMap_oneStep1
    (c : ℤ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S)
    (x : SolutionSurface (coefficients (c : R))) :
    surfaceMap c f (oneStep1SurfacePerm (c : R) x) =
      oneStep1SurfacePerm (c : S) (surfaceMap c f x) := by
  apply Subtype.ext
  change Opening.mapPoint f (oneStep1 (c : R) x.1) =
    oneStep1 (c : S) (Opening.mapPoint f x.1)
  ext <;>
    simp [Opening.mapPoint, oneStep1, swap23, vieta2, coefficients,
      Coefficients.multiplier, map_ofNat]

@[simp]
theorem surfaceMap_oneStep2
    (c : ℤ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S)
    (x : SolutionSurface (coefficients (c : R))) :
    surfaceMap c f (oneStep2SurfacePerm (c : R) x) =
      oneStep2SurfacePerm (c : S) (surfaceMap c f x) := by
  apply Subtype.ext
  change Opening.mapPoint f (oneStep2 (c : R) x.1) =
    oneStep2 (c : S) (Opening.mapPoint f x.1)
  ext <;>
    simp [Opening.mapPoint, oneStep2, swap13, vieta3, coefficients,
      Coefficients.multiplier, map_ofNat]

@[simp]
theorem surfaceMap_oneStep3
    (c : ℤ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S)
    (x : SolutionSurface (coefficients (c : R))) :
    surfaceMap c f (oneStep3SurfacePerm (c : R) x) =
      oneStep3SurfacePerm (c : S) (surfaceMap c f x) := by
  apply Subtype.ext
  change Opening.mapPoint f (oneStep3 (c : R) x.1) =
    oneStep3 (c : S) (Opening.mapPoint f x.1)
  ext <;>
    simp [Opening.mapPoint, oneStep3, swap12, vieta1, coefficients,
      Coefficients.multiplier, map_ofNat]

/-- Every one-step word over the target ring lifts to the same word over the
source ring, and the two actions commute with the surface map. -/
theorem exists_oneStepGroup_lift
    (c : ℤ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S)
    (g : OneStepGroup (c : S)) :
    ∃ h : OneStepGroup (c : R),
      ∀ x : SolutionSurface (coefficients (c : R)),
        surfaceMap c f (h • x) = g • surfaceMap c f x := by
  let motive :
      ∀ q : Equiv.Perm (SolutionSurface (coefficients (c : S))),
        q ∈ Subgroup.closure (oneStepGenerators (c : S)) → Prop :=
    fun q hq ↦
      ∃ h : OneStepGroup (c : R),
        ∀ x : SolutionSurface (coefficients (c : R)),
          surfaceMap c f (h • x) =
            (⟨q, hq⟩ : OneStepGroup (c : S)) • surfaceMap c f x
  apply Subgroup.closure_induction (p := motive)
  · intro q hq
    simp only [oneStepGenerators, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · refine
        ⟨⟨oneStep1SurfacePerm (c : R),
            oneStep1SurfacePerm_mem_OneStepGroup (c : R)⟩, fun x ↦ ?_⟩
      exact surfaceMap_oneStep1 c f x
    · refine
        ⟨⟨oneStep2SurfacePerm (c : R),
            oneStep2SurfacePerm_mem_OneStepGroup (c : R)⟩, fun x ↦ ?_⟩
      exact surfaceMap_oneStep2 c f x
    · refine
        ⟨⟨oneStep3SurfacePerm (c : R),
            oneStep3SurfacePerm_mem_OneStepGroup (c : R)⟩, fun x ↦ ?_⟩
      exact surfaceMap_oneStep3 c f x
  · refine ⟨1, fun x ↦ ?_⟩
    change surfaceMap c f ((1 : OneStepGroup (c : R)) • x) =
      (1 : OneStepGroup (c : S)) • surfaceMap c f x
    simp
  · intro q r hq hr hqLift hrLift
    obtain ⟨qR, hqR⟩ := hqLift
    obtain ⟨rR, hrR⟩ := hrLift
    refine ⟨qR * rR, fun x ↦ ?_⟩
    change surfaceMap c f ((qR * rR) • x) =
      ((⟨q, hq⟩ : OneStepGroup (c : S)) *
        (⟨r, hr⟩ : OneStepGroup (c : S))) • surfaceMap c f x
    rw [mul_smul, mul_smul, hqR, hrR]
  · intro q hq hqLift
    obtain ⟨qR, hqR⟩ := hqLift
    refine ⟨qR⁻¹, fun x ↦ ?_⟩
    change surfaceMap c f (qR⁻¹ • x) =
      (⟨q, hq⟩ : OneStepGroup (c : S))⁻¹ • surfaceMap c f x
    have h := congrArg
      (fun y ↦ (⟨q, hq⟩ : OneStepGroup (c : S))⁻¹ • y)
      (hqR (qR⁻¹ • x))
    simpa [mul_smul] using h.symm

/-- One-step transitivity on the punctured surface implies surjectivity of
coordinatewise reduction from integral solutions. -/
theorem reduction_surjective_of_oneStepStrongApproximationAt
    (c : ℤ) (p : ℕ) (hp : p.Prime)
    (htransitive : OneStepStrongApproximationAt c p hp) :
    Function.Surjective
      ((Markoff c).map
        (CommRingCat.ofHom (Int.castRingHom (ZMod p)))) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hsurface :
      Function.Surjective
        (surfaceMap c (Int.castRingHom (ZMod p))) := by
    intro y
    by_cases hy : y = surfaceOrigin (coefficients (c : ZMod p))
    · refine ⟨surfaceOrigin (coefficients c), ?_⟩
      simpa [hy] using
        surfaceMap_origin c (Int.castRingHom (ZMod p))
    · let root :
          PuncturedSolutionSurface (coefficients (c : ZMod p)) :=
        ⟨surfaceUnit (coefficients (c : ZMod p)),
          surfaceUnit_ne_surfaceOrigin (coefficients (c : ZMod p))⟩
      let target :
          PuncturedSolutionSurface (coefficients (c : ZMod p)) :=
        ⟨y, hy⟩
      obtain ⟨g, hg⟩ := htransitive root target
      obtain ⟨h, hh⟩ :=
        exists_oneStepGroup_lift c (Int.castRingHom (ZMod p)) g
      refine ⟨h • surfaceUnit (coefficients c), ?_⟩
      calc
        surfaceMap c (Int.castRingHom (ZMod p))
            (h • surfaceUnit (coefficients c)) =
            g • surfaceMap c (Int.castRingHom (ZMod p))
              (surfaceUnit (coefficients c)) := hh _
        _ = g • surfaceUnit (coefficients (c : ZMod p)) := by
          exact congrArg (fun z ↦ g • z)
            (surfaceMap_unit (R := ℤ) (S := ZMod p)
              c (Int.castRingHom (ZMod p)))
        _ = y := by
          have hval := congrArg Subtype.val hg
          change g • surfaceUnit (coefficients (c : ZMod p)) = y at hval
          exact hval
  intro y
  obtain ⟨x, hx⟩ :=
    hsurface (markoffEquivSolutionSurface c (ZMod p) y)
  refine ⟨(markoffEquivSolutionSurface c ℤ).symm x, ?_⟩
  apply (markoffEquivSolutionSurface c (ZMod p)).injective
  simpa using hx

namespace Markoff

/-- For every admissible integral equal coefficient, reduction of integral
solutions is surjective modulo every sufficiently large prime. -/
theorem eventual_reduction_surjective :
    ∀ c : ℤ, 3 * (1 + c) ≠ 0 → c ^ 2 ≠ 4 →
      ∃ p₀ : ℕ, ∀ (p : ℕ), p.Prime → p₀ ≤ p →
        Function.Surjective
          ((Markoff c).map
            (CommRingCat.ofHom (Int.castRingHom (ZMod p)))) := by
  intro c hs hc
  obtain ⟨p₀, hp₀⟩ :=
    Assembly.eventualOneStepStrongApproximationStatement c hs hc
  refine ⟨p₀, ?_⟩
  intro p hp hpLarge
  exact reduction_surjective_of_oneStepStrongApproximationAt
    c p hp (hp₀ p hp hpLarge)

end Markoff
end GenMarkoff.Symmetric
