import GenMarkoff.General.Cage.FirstAxisTorusVieta

/-!
# Exponent parity inside a first-axis rotation coset

`FirstAxisTorusVieta` identifies the exact odd reflection of the actual
rotation coset:

`h * zpowers (q ^ 2) ↦ (P * h⁻¹) * zpowers (q ^ 2)`.

This file extracts the remaining exponent-parity consequence.  If

`P * (h ^ 2)⁻¹ = (q ^ 2) ^ n`,

then an even witness `n = 2k` gives a third-Vieta fixed parameter
`(q ^ 2) ^ k * h`, while an odd witness `n = 2k + 1` gives a second-Vieta
fixed parameter with the same formula.

## New consideration in the unequal-coefficient generalization

Membership in `zpowers (q ^ 2)` supplies an integer exponent, but that
exponent need not have an intrinsic parity when `q` is nonprimitive: the
same group element can have both even and odd witnesses if the cyclic
parameter map has an odd-period relation.  Accordingly the production
statements below are witness-sensitive.  They do not replace the exact
stability condition by squarehood of `P`, and they do not claim uniqueness
of the fixed-point type.
-/

namespace GenMarkoff.General.Cage

universe u

noncomputable section

open scoped Pointwise

section AbstractRotationCoset

variable {G : Type u} [CommGroup G]

/-- The third torus reflection fixes exactly the square roots of `P`. -/
theorem torusReflection3_fixed_iff (P x : G) :
    torusReflection3 P x = x ↔ x ^ 2 = P := by
  constructor
  · intro hfix
    change P * x⁻¹ = x at hfix
    have hmul := congrArg (fun y ↦ y * x) hfix
    calc
      x ^ 2 = x * x := pow_two x
      _ = (P * x⁻¹) * x := hmul.symm
      _ = P := by group
  · intro hsq
    calc
      torusReflection3 P x = P * x⁻¹ := rfl
      _ = x ^ 2 * x⁻¹ := by rw [hsq]
      _ = x := by group

/-- The second torus reflection fixes exactly the parameters satisfying
`q²x² = P`. -/
theorem torusReflection2_fixed_iff (q P x : G) :
    torusReflection2 q P x = x ↔ q ^ 2 * x ^ 2 = P := by
  constructor
  · intro hfix
    change P * (q ^ 2 * x)⁻¹ = x at hfix
    have hmul := congrArg (fun y ↦ y * (q ^ 2 * x)) hfix
    calc
      q ^ 2 * x ^ 2 = x * (q ^ 2 * x) := by
        simp only [pow_two]
        ac_rfl
      _ = (P * (q ^ 2 * x)⁻¹) * (q ^ 2 * x) := hmul.symm
      _ = P := by group
  · intro hsq
    calc
      torusReflection2 q P x = P * (q ^ 2 * x)⁻¹ := rfl
      _ = (q ^ 2 * x ^ 2) * (q ^ 2 * x)⁻¹ := by rw [hsq]
      _ = (x * (q ^ 2 * x)) * (q ^ 2 * x)⁻¹ := by
        congr 1
        simp only [pow_two]
        ac_rfl
      _ = x := by
        simp only [pow_two, mul_inv_rev]
        group

/-- A parameter obtained by an arbitrary integer power of `q²` lies in the
actual rotation coset. -/
theorem zpow_sq_mul_mem_rotationCoset (q h : G) (k : ℤ) :
    (q ^ 2) ^ k * h ∈
      h • (Subgroup.zpowers (q ^ 2) : Set G) := by
  refine ⟨(q ^ 2) ^ k, ?_, ?_⟩
  · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers (q ^ 2)) k
  · simp only [smul_eq_mul]
    ac_rfl

/-- An even exponent witness for rotation-coset stability produces a
third-Vieta fixed parameter in that coset. -/
theorem exists_torusReflection3_fixed_in_rotationCoset_of_even_exponent
    (q P h : G) (k : ℤ)
    (hexponent :
      P * (h ^ 2)⁻¹ = (q ^ 2) ^ (2 * k)) :
    ∃ x ∈ h • (Subgroup.zpowers (q ^ 2) : Set G),
      torusReflection3 P x = x := by
  refine ⟨(q ^ 2) ^ k * h,
    zpow_sq_mul_mem_rotationCoset q h k, ?_⟩
  rw [torusReflection3_fixed_iff]
  have hP :
      P = (q ^ 2) ^ (2 * k) * h ^ 2 := by
    calc
      P = (P * (h ^ 2)⁻¹) * h ^ 2 := by group
      _ = (q ^ 2) ^ (2 * k) * h ^ 2 := by rw [hexponent]
  rw [hP]
  rw [show (2 : ℤ) * k = k * 2 by ring]
  simp only [zpow_mul, zpow_ofNat, mul_pow]

/-- An odd exponent witness for rotation-coset stability produces a
second-Vieta fixed parameter in that coset. -/
theorem exists_torusReflection2_fixed_in_rotationCoset_of_odd_exponent
    (q P h : G) (k : ℤ)
    (hexponent :
      P * (h ^ 2)⁻¹ = (q ^ 2) ^ (2 * k + 1)) :
    ∃ x ∈ h • (Subgroup.zpowers (q ^ 2) : Set G),
      torusReflection2 q P x = x := by
  refine ⟨(q ^ 2) ^ k * h,
    zpow_sq_mul_mem_rotationCoset q h k, ?_⟩
  rw [torusReflection2_fixed_iff]
  have hP :
      P = (q ^ 2) ^ (2 * k + 1) * h ^ 2 := by
    calc
      P = (P * (h ^ 2)⁻¹) * h ^ 2 := by group
      _ = (q ^ 2) ^ (2 * k + 1) * h ^ 2 := by rw [hexponent]
  rw [hP]
  rw [show (2 : ℤ) * k + 1 = k * 2 + 1 by ring]
  simp only [zpow_add, zpow_mul, zpow_ofNat, mul_pow, pow_one]
  simp only [mul_left_comm, mul_comm]

/-- The exact stability criterion yields a fixed parameter of one of the
two adjacent reflection types.  The disjunction records the parity of the
chosen integer exponent witness and makes no primitivity assumption on
`q`. -/
theorem exists_adjacentTorusReflection_fixed_in_rotationCoset_of_stable
    (q P h : G)
    (hstable :
      P * (h ^ 2)⁻¹ ∈ Subgroup.zpowers (q ^ 2)) :
    (∃ x ∈ h • (Subgroup.zpowers (q ^ 2) : Set G),
        torusReflection3 P x = x) ∨
      (∃ x ∈ h • (Subgroup.zpowers (q ^ 2) : Set G),
        torusReflection2 q P x = x) := by
  rw [Subgroup.mem_zpowers_iff] at hstable
  obtain ⟨n, hn⟩ := hstable
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    apply
      exists_torusReflection3_fixed_in_rotationCoset_of_even_exponent
        q P h k
    simpa only [hk] using hn.symm
  · right
    apply
      exists_torusReflection2_fixed_in_rotationCoset_of_odd_exponent
        q P h k
    simpa only [hk] using hn.symm

/-- Reflection-stability of the actual `q²` coset therefore produces a
fixed parameter for one of the two adjacent reflections. -/
theorem
    exists_adjacentTorusReflection_fixed_in_rotationCoset_of_coset_eq
    (q P h : G)
    (hcoset :
      h • (Subgroup.zpowers (q ^ 2) : Set G) =
        (P * h⁻¹) • (Subgroup.zpowers (q ^ 2) : Set G)) :
    (∃ x ∈ h • (Subgroup.zpowers (q ^ 2) : Set G),
        torusReflection3 P x = x) ∨
      (∃ x ∈ h • (Subgroup.zpowers (q ^ 2) : Set G),
        torusReflection2 q P x = x) := by
  apply
    exists_adjacentTorusReflection_fixed_in_rotationCoset_of_stable
      q P h
  exact (rotationCoset_eq_reflectedCoset_iff q P h).mp hcoset

end AbstractRotationCoset

end

end GenMarkoff.General.Cage
