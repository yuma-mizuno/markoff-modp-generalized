import GenMarkoff.General.Cage.DirectedConnectingFiber

/-!
# Directed-axis dispatch for connecting split fibers

The centered norm on an axis uses the two coefficients attached to the
moving coordinates.  If both vanish, every split trace has square centered
norm, so that axis cannot provide the nonsquare connecting fibers used by the
full-Vieta cage.

This file isolates that exceptional case without permuting a fixed
coefficient triple.  Unless the whole triple is zero, at least one of the
three explicitly ordered axes has a nonzero moving pair.
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff

universe u

noncomputable section

/-- The coefficient pair attached to the moving coordinates of an actual
fixed axis, in the same cyclic order used by the three fiber charts. -/
def movingCoefficientPairAt
    {R : Type u} (a : Coefficients R) : Axis → R × R
  | .first => (a.a2, a.a3)
  | .second => (a.a3, a.a1)
  | .third => (a.a1, a.a2)

/-- An axis is usable for the connecting split-fiber count when its two
moving coefficients are not both zero. -/
def HasNonzeroMovingCoefficientPair
    {R : Type u} [Zero R] (a : Coefficients R) (axis : Axis) : Prop :=
  movingCoefficientPairAt a axis ≠ (0, 0)

private theorem prod_ne_zero_pair_iff
    {R : Type u} [Zero R] (x y : R) :
    (x, y) ≠ (0, 0) ↔ x ≠ 0 ∨ y ≠ 0 := by
  constructor
  · intro h
    by_cases hx : x = 0
    · right
      intro hy
      exact h (by simp [hx, hy])
    · exact Or.inl hx
  · rintro (hx | hy) hpair
    · exact hx (congrArg Prod.fst hpair)
    · exact hy (congrArg Prod.snd hpair)

theorem hasNonzeroMovingCoefficientPair_first_iff
    {R : Type u} [Zero R] (a : Coefficients R) :
    HasNonzeroMovingCoefficientPair a .first ↔
      a.a2 ≠ 0 ∨ a.a3 ≠ 0 := by
  exact prod_ne_zero_pair_iff a.a2 a.a3

theorem hasNonzeroMovingCoefficientPair_second_iff
    {R : Type u} [Zero R] (a : Coefficients R) :
    HasNonzeroMovingCoefficientPair a .second ↔
      a.a3 ≠ 0 ∨ a.a1 ≠ 0 := by
  exact prod_ne_zero_pair_iff a.a3 a.a1

theorem hasNonzeroMovingCoefficientPair_third_iff
    {R : Type u} [Zero R] (a : Coefficients R) :
    HasNonzeroMovingCoefficientPair a .third ↔
      a.a1 ≠ 0 ∨ a.a2 ≠ 0 := by
  exact prod_ne_zero_pair_iff a.a1 a.a2

/-- Every nonzero coefficient triple admits a concrete ordered axis with a
nonzero moving pair. -/
theorem exists_axis_hasNonzeroMovingCoefficientPair
    {R : Type u} [Zero R] (a : Coefficients R)
    (ha : a.a1 ≠ 0 ∨ a.a2 ≠ 0 ∨ a.a3 ≠ 0) :
    ∃ axis : Axis, HasNonzeroMovingCoefficientPair a axis := by
  rcases ha with h1 | h2 | h3
  · exact ⟨.second,
      (hasNonzeroMovingCoefficientPair_second_iff a).2 (Or.inr h1)⟩
  · exact ⟨.first,
      (hasNonzeroMovingCoefficientPair_first_iff a).2 (Or.inl h2)⟩
  · exact ⟨.first,
      (hasNonzeroMovingCoefficientPair_first_iff a).2 (Or.inr h3)⟩

/-- Exact split-trace square identity in the exceptional zero-pair frame. -/
theorem centeredNorm_zero_zero_splitTorusTrace
    {K : Type u} [Field K] (q : Kˣ) :
    centeredNorm 0 0 (splitTorusTrace q) =
      ((q : K) - (q : K)⁻¹) ^ 2 := by
  simp only [centeredNorm, discriminant, splitTorusTrace,
    Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero q]
  ring

/-- Consequently no split trace on a zero-pair axis can satisfy the
nonsquare connecting condition. -/
theorem isSquare_centeredNorm_zero_zero_splitTorusTrace
    {K : Type u} [Field K] (q : Kˣ) :
    IsSquare (centeredNorm 0 0 (splitTorusTrace q)) := by
  rw [centeredNorm_zero_zero_splitTorusTrace]
  refine ⟨(q : K) - (q : K)⁻¹, ?_⟩
  simp only [pow_two]

end

end GenMarkoff.General.Cage
