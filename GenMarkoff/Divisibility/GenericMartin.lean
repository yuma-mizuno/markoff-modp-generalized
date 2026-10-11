module

public import GenMarkoff.Divisibility.RawAngle.Orbit
public import GenMarkoff.Divisibility.ZeroCoordinateSum
public import GenMarkoff.Core.Statements
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-!
# Generic generalized Martin divisibility

This file proves the generic branch of Theorem 1.1 of arXiv:2509.02187v3:
over `ZMod p` with `p ≥ 5`, if the multiplier is nonzero and no coefficient
square is `4`, every punctured Vieta orbit has cardinality divisible by `p`.

The key step, `multiplier_mul_card_cast_eq_zero_of_generic_vieta_invariant`,
shows that `s · #C = 0` for every finite Vieta-invariant set `C` of punctured
solutions over a field of characteristic not `2`.  At zero-coordinate points
it uses the totalized raw-angle defect identity from
`GenMarkoff.Divisibility.RawAngle.Orbit` together with the vanishing of the
raw-angle sums on zero-coordinate fibers from
`GenMarkoff.Divisibility.ZeroCoordinateSum`, in place of the paper's
pointwise propagation construction.

## Main results

* `prime_dvd_puncturedVietaOrbit_ncard_of_generic`: orbit divisibility for one
  punctured Vieta orbit.
* `generalizedMartinGenericDivisibility`: the statement
  `GeneralizedMartinGenericDivisibilityStatement`.
-/

namespace GenMarkoff

universe u

section FiniteInvariantSet

variable {K : Type u} [Field K]

/-- A finite punctured solution set invariant under the three Vieta moves has
multiplier times cardinality zero, provided all three coefficient squares are
different from `4`. -/
theorem multiplier_mul_card_cast_eq_zero_of_generic_vieta_invariant
    (a : Coefficients K) (h2 : (2 : K) ≠ 0)
    (ha1 : a.a1 ^ 2 ≠ 4) (ha2 : a.a2 ^ 2 ≠ 4) (ha3 : a.a3 ^ 2 ≠ 4)
    (C : Finset (PuncturedSolutionSurface a))
    (hC1 : ∀ x, vieta1PuncturedPerm a x ∈ C ↔ x ∈ C)
    (hC2 : ∀ x, vieta2PuncturedPerm a x ∈ C ↔ x ∈ C)
    (hC3 : ∀ x, vieta3PuncturedPerm a x ∈ C ↔ x ∈ C) :
    a.multiplier * (C.card : K) = 0 := by
  classical
  -- Step 1: `C` is also invariant under the three two-Vieta rotations.
  have hrotation1_eq (x : PuncturedSolutionSurface a) :
      rotation1PuncturedPerm a x =
        vieta3PuncturedPerm a (vieta2PuncturedPerm a x) := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hrotation2_eq (x : PuncturedSolutionSurface a) :
      rotation2PuncturedPerm a x =
        vieta1PuncturedPerm a (vieta3PuncturedPerm a x) := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hrotation3_eq (x : PuncturedSolutionSurface a) :
      rotation3PuncturedPerm a x =
        vieta2PuncturedPerm a (vieta1PuncturedPerm a x) := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hCrotation1 : ∀ x, rotation1PuncturedPerm a x ∈ C ↔ x ∈ C := by
    intro x
    rw [hrotation1_eq, hC3, hC2]
  have hCrotation2 : ∀ x, rotation2PuncturedPerm a x ∈ C ↔ x ∈ C := by
    intro x
    rw [hrotation2_eq, hC1, hC3]
  have hCrotation3 : ∀ x, rotation3PuncturedPerm a x ∈ C ↔ x ∈ C := by
    intro x
    rw [hrotation3_eq, hC2, hC1]
  -- Step 2: restrict the rotation `Rᵢ` to `C` and then to the points of `C`
  -- with `xᵢ = 0`, which `Rᵢ` preserves.
  let rhoC1 : Equiv.Perm C :=
    (rotation1PuncturedPerm a).subtypePerm hCrotation1
  let rhoC2 : Equiv.Perm C :=
    (rotation2PuncturedPerm a).subtypePerm hCrotation2
  let rhoC3 : Equiv.Perm C :=
    (rotation3PuncturedPerm a).subtypePerm hCrotation3
  have hzero1 : ∀ x : C,
      ((rhoC1 x).1.1.1 : Point K).x1 = 0 ↔ (x.1.1 : Point K).x1 = 0 := by
    intro x
    -- The point of `rhoC1 x` is `rotation1 a` of the point of `x`, through
    -- `subtypePerm`, `rotation1PuncturedPerm` and `rotation1SurfacePerm`;
    -- restate on points so `simp` computes the first coordinate.
    change (rotation1 a (x.1.1 : Point K)).x1 = 0 ↔ (x.1.1 : Point K).x1 = 0
    simp [rotation1, vieta2, vieta3]
  have hzero2 : ∀ x : C,
      ((rhoC2 x).1.1.1 : Point K).x2 = 0 ↔ (x.1.1 : Point K).x2 = 0 := by
    intro x
    -- The point of `rhoC2 x` is `rotation2 a` of the point of `x`, through
    -- `subtypePerm`, `rotation2PuncturedPerm` and `rotation2SurfacePerm`;
    -- restate on points so `simp` computes the second coordinate.
    change (rotation2 a (x.1.1 : Point K)).x2 = 0 ↔ (x.1.1 : Point K).x2 = 0
    simp [rotation2, vieta1, vieta3]
  have hzero3 : ∀ x : C,
      ((rhoC3 x).1.1.1 : Point K).x3 = 0 ↔ (x.1.1 : Point K).x3 = 0 := by
    intro x
    -- The point of `rhoC3 x` is `rotation3 a` of the point of `x`, through
    -- `subtypePerm`, `rotation3PuncturedPerm` and `rotation3SurfacePerm`;
    -- restate on points so `simp` computes the third coordinate.
    change (rotation3 a (x.1.1 : Point K)).x3 = 0 ↔ (x.1.1 : Point K).x3 = 0
    simp [rotation3, vieta1, vieta2]
  let rho1 : Equiv.Perm {x : C // (x.1.1 : Point K).x1 = 0} :=
    rhoC1.subtypePerm hzero1
  let rho2 : Equiv.Perm {x : C // (x.1.1 : Point K).x2 = 0} :=
    rhoC2.subtypePerm hzero2
  let rho3 : Equiv.Perm {x : C // (x.1.1 : Point K).x3 = 0} :=
    rhoC3.subtypePerm hzero3
  -- Step 3: on each zero-coordinate slice of `C`, the corresponding raw angle
  -- sums to zero (`sum_rawAngle*_eq_zero_of_zero_rotation_model`).
  have hsum1subtype :
      (∑ x : {x : C // (x.1.1 : Point K).x1 = 0},
        rawAngle1 a (x.1.1.1 : Point K)) = 0 := by
    apply sum_rawAngle1_eq_zero_of_zero_rotation_model a rho1
        (fun x ↦ (x.1.1.1 : Point K)) ha1
    · intro x
      -- By the definitions of `rho1`, `rhoC1` and `rotation1PuncturedPerm`, the
      -- point of `rho1 x` is `rotation1 a` of the point of `x`; state this on
      -- points and close it by `rfl`.
      change ((rho1 x).1.1.1.1 : Point K) = rotation1 a (x.1.1.1 : Point K)
      rfl
    · intro x
      exact x.1.1.1.2
    · intro x hpoint
      apply x.1.1.2
      apply Subtype.ext
      exact hpoint
    · intro x
      exact x.2
  have hsum2subtype :
      (∑ x : {x : C // (x.1.1 : Point K).x2 = 0},
        rawAngle2 a (x.1.1.1 : Point K)) = 0 := by
    apply sum_rawAngle2_eq_zero_of_zero_rotation_model a rho2
        (fun x ↦ (x.1.1.1 : Point K)) ha2
    · intro x
      -- By the definitions of `rho2`, `rhoC2` and `rotation2PuncturedPerm`, the
      -- point of `rho2 x` is `rotation2 a` of the point of `x`; state this on
      -- points and close it by `rfl`.
      change ((rho2 x).1.1.1.1 : Point K) = rotation2 a (x.1.1.1 : Point K)
      rfl
    · intro x
      exact x.1.1.1.2
    · intro x hpoint
      apply x.1.1.2
      apply Subtype.ext
      exact hpoint
    · intro x
      exact x.2
  have hsum3subtype :
      (∑ x : {x : C // (x.1.1 : Point K).x3 = 0},
        rawAngle3 a (x.1.1.1 : Point K)) = 0 := by
    apply sum_rawAngle3_eq_zero_of_zero_rotation_model a rho3
        (fun x ↦ (x.1.1.1 : Point K)) ha3
    · intro x
      -- By the definitions of `rho3`, `rhoC3` and `rotation3PuncturedPerm`, the
      -- point of `rho3 x` is `rotation3 a` of the point of `x`; state this on
      -- points and close it by `rfl`.
      change ((rho3 x).1.1.1.1 : Point K) = rotation3 a (x.1.1.1 : Point K)
      rfl
    · intro x
      exact x.1.1.1.2
    · intro x hpoint
      apply x.1.1.2
      apply Subtype.ext
      exact hpoint
    · intro x
      exact x.2
  -- Step 4: rewrite each slice sum as an indicator sum over all of `C`.
  have hsum1 :
      (∑ x : C, if (x.1.1 : Point K).x1 = 0 then rawAngle1 a x.1.1 else 0) = 0 := by
    calc
      (∑ x : C, if (x.1.1 : Point K).x1 = 0 then rawAngle1 a x.1.1 else 0) =
          ∑ x ∈ Finset.univ.filter (fun x : C ↦ (x.1.1 : Point K).x1 = 0),
            rawAngle1 a x.1.1 := by
              rw [Finset.sum_ite]
              simp
      _ = ∑ x : {x : C // (x.1.1 : Point K).x1 = 0},
          rawAngle1 a (x.1.1.1 : Point K) := by
            apply Finset.sum_subtype
            intro x
            simp
      _ = 0 := hsum1subtype
  have hsum2 :
      (∑ x : C, if (x.1.1 : Point K).x2 = 0 then rawAngle2 a x.1.1 else 0) = 0 := by
    calc
      (∑ x : C, if (x.1.1 : Point K).x2 = 0 then rawAngle2 a x.1.1 else 0) =
          ∑ x ∈ Finset.univ.filter (fun x : C ↦ (x.1.1 : Point K).x2 = 0),
            rawAngle2 a x.1.1 := by
              rw [Finset.sum_ite]
              simp
      _ = ∑ x : {x : C // (x.1.1 : Point K).x2 = 0},
          rawAngle2 a (x.1.1.1 : Point K) := by
            apply Finset.sum_subtype
            intro x
            simp
      _ = 0 := hsum2subtype
  have hsum3 :
      (∑ x : C, if (x.1.1 : Point K).x3 = 0 then rawAngle3 a x.1.1 else 0) = 0 := by
    calc
      (∑ x : C, if (x.1.1 : Point K).x3 = 0 then rawAngle3 a x.1.1 else 0) =
          ∑ x ∈ Finset.univ.filter (fun x : C ↦ (x.1.1 : Point K).x3 = 0),
            rawAngle3 a x.1.1 := by
              rw [Finset.sum_ite]
              simp
      _ = ∑ x : {x : C // (x.1.1 : Point K).x3 = 0},
          rawAngle3 a (x.1.1.1 : Point K) := by
            apply Finset.sum_subtype
            intro x
            simp
      _ = 0 := hsum3subtype
  -- Step 5: the zero-coordinate correction therefore sums to zero, and the
  -- defect identity gives `s · #C = 2 · 0`.
  have hcorrection : (∑ x : C, zeroRawAngleCorrection a x.1.1) = 0 := by
    simp_rw [zeroRawAngleCorrection, Finset.sum_add_distrib]
    rw [hsum1, hsum2, hsum3]
    ring
  rw [multiplier_mul_card_cast_eq_two_mul_sum_zeroRawAngleCorrection_of_vieta_invariant
    a h2 C hC1 hC2 hC3, hcorrection, mul_zero]

end FiniteInvariantSet

section ResidueFieldOrbit

/-- Every punctured Vieta orbit over `ZMod p` has cardinality divisible by
`p` under the generic coefficient hypotheses. -/
theorem prime_dvd_puncturedVietaOrbit_ncard_of_generic
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (a : Coefficients (ZMod p)) (ha : GenericAdmissible a)
    (x : PuncturedSolutionSurface a) :
    p ∣ (puncturedVietaOrbit x).ncard := by
  classical
  have htwo : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
  rcases ha with ⟨hmultiplier, ha1, ha2, ha3⟩
  let S := puncturedVietaOrbit x
  have hS : S.Finite := Set.toFinite S
  let C : Finset (PuncturedSolutionSurface a) := hS.toFinset
  have hC1 : ∀ y, vieta1PuncturedPerm a y ∈ C ↔ y ∈ C := by
    intro y
    simp only [C, Set.Finite.mem_toFinset]
    -- `S` is `puncturedVietaOrbit x`, i.e. `MulAction.orbit (VietaGroup a) x`;
    -- restate so that `MulAction.mapsTo_smul_orbit` applies.
    change vieta1PuncturedPerm a y ∈ MulAction.orbit (VietaGroup a) x ↔
      y ∈ MulAction.orbit (VietaGroup a) x
    rw [← vieta1InVietaGroup_smul_punctured]
    constructor
    · intro hy
      have h := MulAction.mapsTo_smul_orbit (vieta1InVietaGroup a)⁻¹ x hy
      simpa only [inv_smul_smul] using h
    · intro hy
      exact MulAction.mapsTo_smul_orbit (vieta1InVietaGroup a) x hy
  have hC2 : ∀ y, vieta2PuncturedPerm a y ∈ C ↔ y ∈ C := by
    intro y
    simp only [C, Set.Finite.mem_toFinset]
    -- `S` is `puncturedVietaOrbit x`, i.e. `MulAction.orbit (VietaGroup a) x`;
    -- restate so that `MulAction.mapsTo_smul_orbit` applies.
    change vieta2PuncturedPerm a y ∈ MulAction.orbit (VietaGroup a) x ↔
      y ∈ MulAction.orbit (VietaGroup a) x
    rw [← vieta2InVietaGroup_smul_punctured]
    constructor
    · intro hy
      have h := MulAction.mapsTo_smul_orbit (vieta2InVietaGroup a)⁻¹ x hy
      simpa only [inv_smul_smul] using h
    · intro hy
      exact MulAction.mapsTo_smul_orbit (vieta2InVietaGroup a) x hy
  have hC3 : ∀ y, vieta3PuncturedPerm a y ∈ C ↔ y ∈ C := by
    intro y
    simp only [C, Set.Finite.mem_toFinset]
    -- `S` is `puncturedVietaOrbit x`, i.e. `MulAction.orbit (VietaGroup a) x`;
    -- restate so that `MulAction.mapsTo_smul_orbit` applies.
    change vieta3PuncturedPerm a y ∈ MulAction.orbit (VietaGroup a) x ↔
      y ∈ MulAction.orbit (VietaGroup a) x
    rw [← vieta3InVietaGroup_smul_punctured]
    constructor
    · intro hy
      have h := MulAction.mapsTo_smul_orbit (vieta3InVietaGroup a)⁻¹ x hy
      simpa only [inv_smul_smul] using h
    · intro hy
      exact MulAction.mapsTo_smul_orbit (vieta3InVietaGroup a) x hy
  have hmulZero : a.multiplier * (C.card : ZMod p) = 0 :=
    multiplier_mul_card_cast_eq_zero_of_generic_vieta_invariant
      a htwo ha1 ha2 ha3 C hC1 hC2 hC3
  have hcardZero : (C.card : ZMod p) = 0 :=
    (mul_eq_zero.mp hmulZero).resolve_left hmultiplier
  -- The goal `p ∣ (puncturedVietaOrbit x).ncard` is `p ∣ S.ncard` for the local
  -- `S`; restate so that `Set.ncard_eq_toFinset_card S hS` rewrites it.
  change p ∣ S.ncard
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Set.ncard_eq_toFinset_card S hS]
  simpa [C] using hcardZero

/-- The generic branch of generalized Martin divisibility
(arXiv:2509.02187v3, Theorem 1.1): for `p ≥ 5` and generically admissible
coefficients over `ZMod p`, every punctured Vieta orbit has cardinality
divisible by `p`. -/
theorem generalizedMartinGenericDivisibility :
    GeneralizedMartinGenericDivisibilityStatement := by
  intro p hp a hpFive ha
  letI : Fact p.Prime := ⟨hp⟩
  intro x
  exact prime_dvd_puncturedVietaOrbit_ncard_of_generic p hpFive a ha x

end ResidueFieldOrbit

end GenMarkoff
