import GenMarkoff.Divisibility.RawAngleOrbit
import GenMarkoff.Divisibility.ZeroCoordinateSum
import GenMarkoff.Core.Statements

/-!
# Exceptional-compatible generalized Martin divisibility

This file extends the raw-angle defect proof to the exceptional coefficient
fibers.  If `aᵢ² = 4`, the corresponding compatibility equation makes the
central raw angle vanish pointwise on `xᵢ = 0`; otherwise the existing
rotation-reindexing argument makes its sum vanish.
-/

namespace GenMarkoff

universe u v

section ExceptionalRawAngles

variable {K : Type u} [Field K]

theorem rawAngle1_eq_zero_of_exceptional_compatible
    (a : Coefficients K) (x : Point K)
    (h2 : (2 : K) ≠ 0) (hx : IsSolution a x) (hx1 : x.x1 = 0)
    (hx2 : x.x2 ≠ 0) (hx3 : x.x3 ≠ 0)
    (ha1 : a.a1 ^ 2 = 4) (hcompat : 2 * a.a3 = a.a2 * a.a1) :
    rawAngle1 a x = 0 := by
  have hsurface : x.x2 ^ 2 + x.x3 ^ 2 + a.a1 * x.x2 * x.x3 = 0 := by
    rw [IsSolution, polynomial] at hx
    simpa [hx1] using hx
  have hlinear : a.a1 * x.x2 + 2 * x.x3 = 0 := by
    have hsquare : (a.a1 * x.x2 + 2 * x.x3) ^ 2 = 0 := by
      calc
        (a.a1 * x.x2 + 2 * x.x3) ^ 2 =
            4 * (x.x2 ^ 2 + x.x3 ^ 2 + a.a1 * x.x2 * x.x3) := by
              linear_combination x.x2 ^ 2 * ha1
        _ = 0 := by rw [hsurface, mul_zero]
    exact sq_eq_zero_iff.mp hsquare
  have hnum : a.a3 * x.x2 + a.a2 * x.x3 = 0 := by
    have htwice : 2 * (a.a3 * x.x2 + a.a2 * x.x3) = 0 := by
      linear_combination x.x2 * hcompat + a.a2 * hlinear
    exact (mul_eq_zero.mp htwice).resolve_left h2
  have hfrac : a.a3 / x.x3 + a.a2 / x.x2 = 0 := by
    field_simp [hx2, hx3]
    simpa [mul_comm] using hnum
  unfold rawAngle1
  rw [hx1]
  simp [hfrac]

theorem rawAngle2_eq_zero_of_exceptional_compatible
    (a : Coefficients K) (x : Point K)
    (h2 : (2 : K) ≠ 0) (hx : IsSolution a x) (hx2 : x.x2 = 0)
    (hx1 : x.x1 ≠ 0) (hx3 : x.x3 ≠ 0)
    (ha2 : a.a2 ^ 2 = 4) (hcompat : 2 * a.a1 = a.a3 * a.a2) :
    rawAngle2 a x = 0 := by
  have hsurface : x.x1 ^ 2 + x.x3 ^ 2 + a.a2 * x.x3 * x.x1 = 0 := by
    rw [IsSolution, polynomial] at hx
    simpa [hx2] using hx
  have hlinear : a.a2 * x.x3 + 2 * x.x1 = 0 := by
    have hsquare : (a.a2 * x.x3 + 2 * x.x1) ^ 2 = 0 := by
      calc
        (a.a2 * x.x3 + 2 * x.x1) ^ 2 =
            4 * (x.x1 ^ 2 + x.x3 ^ 2 + a.a2 * x.x3 * x.x1) := by
              linear_combination x.x3 ^ 2 * ha2
        _ = 0 := by rw [hsurface, mul_zero]
    exact sq_eq_zero_iff.mp hsquare
  have hnum : a.a1 * x.x3 + a.a3 * x.x1 = 0 := by
    have htwice : 2 * (a.a1 * x.x3 + a.a3 * x.x1) = 0 := by
      linear_combination x.x3 * hcompat + a.a3 * hlinear
    exact (mul_eq_zero.mp htwice).resolve_left h2
  have hfrac : a.a1 / x.x1 + a.a3 / x.x3 = 0 := by
    field_simp [hx1, hx3]
    simpa [mul_comm] using hnum
  unfold rawAngle2
  rw [hx2]
  simp [hfrac]

theorem rawAngle3_eq_zero_of_exceptional_compatible
    (a : Coefficients K) (x : Point K)
    (h2 : (2 : K) ≠ 0) (hx : IsSolution a x) (hx3 : x.x3 = 0)
    (hx1 : x.x1 ≠ 0) (hx2 : x.x2 ≠ 0)
    (ha3 : a.a3 ^ 2 = 4) (hcompat : 2 * a.a2 = a.a1 * a.a3) :
    rawAngle3 a x = 0 := by
  have hsurface : x.x1 ^ 2 + x.x2 ^ 2 + a.a3 * x.x1 * x.x2 = 0 := by
    rw [IsSolution, polynomial] at hx
    simpa [hx3] using hx
  have hlinear : a.a3 * x.x1 + 2 * x.x2 = 0 := by
    have hsquare : (a.a3 * x.x1 + 2 * x.x2) ^ 2 = 0 := by
      calc
        (a.a3 * x.x1 + 2 * x.x2) ^ 2 =
            4 * (x.x1 ^ 2 + x.x2 ^ 2 + a.a3 * x.x1 * x.x2) := by
              linear_combination x.x1 ^ 2 * ha3
        _ = 0 := by rw [hsurface, mul_zero]
    exact sq_eq_zero_iff.mp hsquare
  have hnum : a.a2 * x.x1 + a.a1 * x.x2 = 0 := by
    have htwice : 2 * (a.a2 * x.x1 + a.a1 * x.x2) = 0 := by
      linear_combination x.x1 * hcompat + a.a1 * hlinear
    exact (mul_eq_zero.mp htwice).resolve_left h2
  have hfrac : a.a2 / x.x2 + a.a1 / x.x1 = 0 := by
    field_simp [hx1, hx2]
    simpa [mul_comm] using hnum
  unfold rawAngle3
  rw [hx3]
  simp [hfrac]

end ExceptionalRawAngles

section CompatibleZeroFiberSums

variable {K : Type u} [Field K]

theorem sum_rawAngle1_eq_zero_of_zero_rotation_model_of_compatible
    {X : Type v} [Fintype X]
    (a : Coefficients K) (rho : Equiv.Perm X) (point : X → Point K)
    (h2 : (2 : K) ≠ 0)
    (hcompat : a.a1 ^ 2 = 4 → 2 * a.a3 = a.a2 * a.a1)
    (hrotation : ∀ x, point (rho x) = rotation1 a (point x))
    (hsolution : ∀ x, IsSolution a (point x))
    (hpunctured : ∀ x, point x ≠ origin)
    (hzero : ∀ x, (point x).x1 = 0) :
    (∑ x, rawAngle1 a (point x)) = 0 := by
  by_cases ha1 : a.a1 ^ 2 = 4
  · apply Finset.sum_eq_zero
    intro x _hx
    have hne := coordinates_ne_zero_of_x1_eq_zero a (point x)
      (hsolution x) (hpunctured x) (hzero x)
    exact rawAngle1_eq_zero_of_exceptional_compatible a (point x) h2
      (hsolution x) (hzero x) hne.1 hne.2 ha1 (hcompat ha1)
  · exact sum_rawAngle1_eq_zero_of_zero_rotation_model a rho point ha1
      hrotation hsolution hpunctured hzero

theorem sum_rawAngle2_eq_zero_of_zero_rotation_model_of_compatible
    {X : Type v} [Fintype X]
    (a : Coefficients K) (rho : Equiv.Perm X) (point : X → Point K)
    (h2 : (2 : K) ≠ 0)
    (hcompat : a.a2 ^ 2 = 4 → 2 * a.a1 = a.a3 * a.a2)
    (hrotation : ∀ x, point (rho x) = rotation2 a (point x))
    (hsolution : ∀ x, IsSolution a (point x))
    (hpunctured : ∀ x, point x ≠ origin)
    (hzero : ∀ x, (point x).x2 = 0) :
    (∑ x, rawAngle2 a (point x)) = 0 := by
  by_cases ha2 : a.a2 ^ 2 = 4
  · apply Finset.sum_eq_zero
    intro x _hx
    have hne := coordinates_ne_zero_of_x2_eq_zero a (point x)
      (hsolution x) (hpunctured x) (hzero x)
    exact rawAngle2_eq_zero_of_exceptional_compatible a (point x) h2
      (hsolution x) (hzero x) hne.1 hne.2 ha2 (hcompat ha2)
  · exact sum_rawAngle2_eq_zero_of_zero_rotation_model a rho point ha2
      hrotation hsolution hpunctured hzero

theorem sum_rawAngle3_eq_zero_of_zero_rotation_model_of_compatible
    {X : Type v} [Fintype X]
    (a : Coefficients K) (rho : Equiv.Perm X) (point : X → Point K)
    (h2 : (2 : K) ≠ 0)
    (hcompat : a.a3 ^ 2 = 4 → 2 * a.a2 = a.a1 * a.a3)
    (hrotation : ∀ x, point (rho x) = rotation3 a (point x))
    (hsolution : ∀ x, IsSolution a (point x))
    (hpunctured : ∀ x, point x ≠ origin)
    (hzero : ∀ x, (point x).x3 = 0) :
    (∑ x, rawAngle3 a (point x)) = 0 := by
  by_cases ha3 : a.a3 ^ 2 = 4
  · apply Finset.sum_eq_zero
    intro x _hx
    have hne := coordinates_ne_zero_of_x3_eq_zero a (point x)
      (hsolution x) (hpunctured x) (hzero x)
    exact rawAngle3_eq_zero_of_exceptional_compatible a (point x) h2
      (hsolution x) (hzero x) hne.1 hne.2 ha3 (hcompat ha3)
  · exact sum_rawAngle3_eq_zero_of_zero_rotation_model a rho point ha3
      hrotation hsolution hpunctured hzero

end CompatibleZeroFiberSums

section FiniteInvariantSet

variable {K : Type u} [Field K]

/-- A finite punctured solution set invariant under the three Vieta moves has
multiplier times cardinality zero under the exceptional compatibility
conditions. -/
theorem multiplier_mul_card_cast_eq_zero_of_compatible_vieta_invariant
    (a : Coefficients K) (h2 : (2 : K) ≠ 0)
    (hcompat1 : a.a1 ^ 2 = 4 → 2 * a.a3 = a.a2 * a.a1)
    (hcompat2 : a.a2 ^ 2 = 4 → 2 * a.a1 = a.a3 * a.a2)
    (hcompat3 : a.a3 ^ 2 = 4 → 2 * a.a2 = a.a1 * a.a3)
    (C : Finset (PuncturedSolutionSurface a))
    (hC1 : ∀ x, vieta1PuncturedPerm a x ∈ C ↔ x ∈ C)
    (hC2 : ∀ x, vieta2PuncturedPerm a x ∈ C ↔ x ∈ C)
    (hC3 : ∀ x, vieta3PuncturedPerm a x ∈ C ↔ x ∈ C) :
    a.multiplier * (C.card : K) = 0 := by
  classical
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
  let rhoC1 : Equiv.Perm C :=
    (rotation1PuncturedPerm a).subtypePerm hCrotation1
  let rhoC2 : Equiv.Perm C :=
    (rotation2PuncturedPerm a).subtypePerm hCrotation2
  let rhoC3 : Equiv.Perm C :=
    (rotation3PuncturedPerm a).subtypePerm hCrotation3
  have hzero1 : ∀ x : C,
      ((rhoC1 x).1.1.1 : Point K).x1 = 0 ↔ (x.1.1 : Point K).x1 = 0 := by
    intro x
    change (rotation1 a (x.1.1 : Point K)).x1 = 0 ↔ (x.1.1 : Point K).x1 = 0
    simp [rotation1, vieta2, vieta3]
  have hzero2 : ∀ x : C,
      ((rhoC2 x).1.1.1 : Point K).x2 = 0 ↔ (x.1.1 : Point K).x2 = 0 := by
    intro x
    change (rotation2 a (x.1.1 : Point K)).x2 = 0 ↔ (x.1.1 : Point K).x2 = 0
    simp [rotation2, vieta1, vieta3]
  have hzero3 : ∀ x : C,
      ((rhoC3 x).1.1.1 : Point K).x3 = 0 ↔ (x.1.1 : Point K).x3 = 0 := by
    intro x
    change (rotation3 a (x.1.1 : Point K)).x3 = 0 ↔ (x.1.1 : Point K).x3 = 0
    simp [rotation3, vieta1, vieta2]
  let rho1 : Equiv.Perm {x : C // (x.1.1 : Point K).x1 = 0} :=
    rhoC1.subtypePerm hzero1
  let rho2 : Equiv.Perm {x : C // (x.1.1 : Point K).x2 = 0} :=
    rhoC2.subtypePerm hzero2
  let rho3 : Equiv.Perm {x : C // (x.1.1 : Point K).x3 = 0} :=
    rhoC3.subtypePerm hzero3
  have hsum1subtype :
      (∑ x : {x : C // (x.1.1 : Point K).x1 = 0},
        rawAngle1 a (x.1.1.1 : Point K)) = 0 := by
    apply sum_rawAngle1_eq_zero_of_zero_rotation_model_of_compatible a rho1
        (fun x ↦ (x.1.1.1 : Point K)) h2 hcompat1
    · intro x
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
    apply sum_rawAngle2_eq_zero_of_zero_rotation_model_of_compatible a rho2
        (fun x ↦ (x.1.1.1 : Point K)) h2 hcompat2
    · intro x
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
    apply sum_rawAngle3_eq_zero_of_zero_rotation_model_of_compatible a rho3
        (fun x ↦ (x.1.1.1 : Point K)) h2 hcompat3
    · intro x
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
  have hcorrection : (∑ x : C, zeroRawAngleCorrection a x.1.1) = 0 := by
    simp_rw [zeroRawAngleCorrection, Finset.sum_add_distrib]
    rw [hsum1, hsum2, hsum3]
    ring
  rw [multiplier_mul_card_cast_eq_two_mul_sum_zeroRawAngleCorrection_of_vieta_invariant
    a h2 C hC1 hC2 hC3, hcorrection, mul_zero]

end FiniteInvariantSet

section ResidueFieldOrbit

/-- Every punctured Vieta orbit over `ZMod p` has cardinality divisible by
`p` under the full exceptional-compatible coefficient hypotheses. -/
theorem prime_dvd_puncturedVietaOrbit_ncard_of_compatible
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (a : Coefficients (ZMod p)) (ha : DivisibilityAdmissible a)
    (x : PuncturedSolutionSurface a) :
    p ∣ (puncturedVietaOrbit x).ncard := by
  classical
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hpDvd
  rcases ha with ⟨hmultiplier, hcompat1, hcompat2, hcompat3⟩
  let S := puncturedVietaOrbit x
  have hS : S.Finite := Set.toFinite S
  let C : Finset (PuncturedSolutionSurface a) := hS.toFinset
  have hC1 : ∀ y, vieta1PuncturedPerm a y ∈ C ↔ y ∈ C := by
    intro y
    simp only [C, Set.Finite.mem_toFinset]
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
    multiplier_mul_card_cast_eq_zero_of_compatible_vieta_invariant
      a htwo hcompat1 hcompat2 hcompat3 C hC1 hC2 hC3
  have hcardZero : (C.card : ZMod p) = 0 :=
    (mul_eq_zero.mp hmulZero).resolve_left hmultiplier
  change p ∣ S.ncard
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Set.ncard_eq_toFinset_card S hS]
  simpa [C] using hcardZero

/-- The full exceptional-compatible generalized Martin divisibility theorem. -/
theorem generalizedMartinDivisibility :
    GeneralizedMartinDivisibilityStatement := by
  intro p hp a hpFive ha
  letI : Fact p.Prime := ⟨hp⟩
  intro x
  exact prime_dvd_puncturedVietaOrbit_ncard_of_compatible p hpFive a ha x

end ResidueFieldOrbit

end GenMarkoff
