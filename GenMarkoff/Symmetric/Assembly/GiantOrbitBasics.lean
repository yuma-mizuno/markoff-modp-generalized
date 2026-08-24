import GenMarkoff.Symmetric.OneStepStrongApproximation
import BGS.Markoff.Assembly.Asymptotics
import BGS.Markoff.MiddleGame.DivisorRange

/-!
# Finite-set and asymptotic helpers for the symmetric one-step giant orbit

The geometric routing argument naturally produces a finite set of underlying
surface points containing the complement of a chosen one-step component.
This file transports such a set to the punctured subtype and records the
small-order polynomial bound with room for three exceptional centered points.
-/

namespace GenMarkoff.Symmetric.Assembly

open BGS.Markoff Filter

noncomputable section

/-- Punctured solution-surface points whose underlying point lies in `S`. -/
def puncturedPointsIn
    {p : ℕ} [NeZero p] {c : ZMod p} (S : Finset (Point (ZMod p))) :
    Finset (PuncturedSolutionSurface (coefficients c)) := by
  classical
  exact Finset.univ.filter fun x => x.1.1 ∈ S

@[simp]
theorem mem_puncturedPointsIn_iff
    {p : ℕ} [NeZero p] {c : ZMod p} {S : Finset (Point (ZMod p))}
    {x : PuncturedSolutionSurface (coefficients c)} :
    x ∈ puncturedPointsIn S ↔ x.1.1 ∈ S := by
  classical
  simp [puncturedPointsIn]

/-- Forgetting the solution and puncture proofs injects punctured surface
points into their underlying point type. -/
theorem puncturedPoint_forget_injective
    {p : ℕ} [NeZero p] {c : ZMod p} :
    Function.Injective
      (fun x : PuncturedSolutionSurface (coefficients c) => x.1.1) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

/-- Restricting a point finset to punctured solutions cannot increase its
cardinality. -/
theorem puncturedPointsIn_card_le
    {p : ℕ} [NeZero p] {c : ZMod p} (S : Finset (Point (ZMod p))) :
    (puncturedPointsIn (c := c) S).card ≤ S.card := by
  classical
  let f :
      PuncturedSolutionSurface (coefficients c) → Point (ZMod p) :=
    fun x => x.1.1
  calc
    (puncturedPointsIn (c := c) S).card =
        ((puncturedPointsIn (c := c) S).image f).card := by
      exact
        (Finset.card_image_of_injective _
          (puncturedPoint_forget_injective (p := p) (c := c))).symm
    _ ≤ S.card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact mem_puncturedPointsIn_iff.mp hx

/-- A finite set containing a one-step orbit complement bounds that
complement's cardinality. -/
theorem oneStepOrbitComplementCard_le_finset_of_subset
    {p : ℕ} [Fact p.Prime] {c : ZMod p}
    (x : PuncturedSolutionSurface (coefficients c))
    (bad : Finset (PuncturedSolutionSurface (coefficients c)))
    (hbad : Set.univ \ puncturedOneStepOrbit x ⊆ (bad : Set _)) :
    oneStepOrbitComplementCard x ≤ bad.card := by
  rw [oneStepOrbitComplementCard, ← Set.ncard_coe_finset bad]
  exact Set.ncard_le_ncard hbad

/-- Final one-prime giant-orbit conclusion once the complement has been put
inside a counted punctured finset. -/
theorem hasGiantOneStepOrbitAt_of_complement_subset_finset
    (c : ℤ) (p : ℕ) (hp : p.Prime) (epsilon : ℝ)
    (x : PuncturedSolutionSurface (coefficients (c : ZMod p)))
    (bad :
      Finset (PuncturedSolutionSurface (coefficients (c : ZMod p))))
    (hbad : Set.univ \ puncturedOneStepOrbit x ⊆ (bad : Set _))
    (hcard : (bad.card : ℝ) ≤ Real.rpow p epsilon) :
    HasGiantOneStepOrbitAt c p hp epsilon := by
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨x, ?_⟩
  have hnat :=
    oneStepOrbitComplementCard_le_finset_of_subset x bad hbad
  have hreal : (oneStepOrbitComplementCard x : ℝ) ≤ bad.card := by
    exact_mod_cast hnat
  exact hreal.trans hcard

/-- The usual small-order polynomial, together with three exceptional
points, is eventually absorbed by `p ^ epsilon` when the order cutoff is at
most `p ^ (epsilon / 10)`. -/
theorem eventually_smallOrderPointBound_add_three_le_rpow
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ p : ℕ in atTop, ∀ bound : ℕ,
      (bound : ℝ) ≤ (p : ℝ) ^ (epsilon / 10) →
        ((2 * (2 + 2 * bound ^ 2) ^ 2 + 3 : ℕ) : ℝ) ≤
          (p : ℝ) ^ epsilon := by
  have hhalf : 0 < epsilon / 2 := div_pos hepsilon (by norm_num)
  have hsmall :
      ∀ᶠ p : ℕ in atTop, ∀ bound : ℕ,
        (bound : ℝ) ≤ (p : ℝ) ^ ((epsilon / 2) / 5) →
          ((2 * (2 + 2 * bound ^ 2) ^ 2 : ℕ) : ℝ) ≤
            (p : ℝ) ^ (epsilon / 2) :=
    BGS.Markoff.eventually_smallOrderPointBound_le_rpow hhalf
  have hthree :
      ∀ᶠ p : ℕ in atTop, (3 : ℝ) ≤ (p : ℝ) ^ (epsilon / 2) := by
    exact
      ((tendsto_rpow_atTop hhalf).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop 3)
  have hdouble :
      ∀ᶠ p : ℕ in atTop,
        (2 : ℝ) * (p : ℝ) ^ (epsilon / 2) <
          (p : ℝ) ^ epsilon := by
    exact BGS.Markoff.eventually_const_mul_rpow_lt_rpow
      (C := (2 : ℝ)) (a := epsilon / 2) (b := epsilon) (by linarith)
  filter_upwards [hsmall, hthree, hdouble] with p hpSmall hpThree hpDouble
  intro bound hbound
  have hbound' :
      (bound : ℝ) ≤ (p : ℝ) ^ ((epsilon / 2) / 5) := by
    convert hbound using 1 <;> ring_nf
  have hpolynomial := hpSmall bound hbound'
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  calc
    ((2 * (2 + 2 * bound ^ 2) ^ 2 : ℕ) : ℝ) + 3 ≤
        (p : ℝ) ^ (epsilon / 2) + (p : ℝ) ^ (epsilon / 2) :=
      add_le_add hpolynomial hpThree
    _ = 2 * (p : ℝ) ^ (epsilon / 2) := by ring
    _ ≤ (p : ℝ) ^ epsilon := le_of_lt hpDouble

end

end GenMarkoff.Symmetric.Assembly
