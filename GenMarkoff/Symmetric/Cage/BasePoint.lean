import GenMarkoff.Symmetric.Cage.PairRelay
import GenMarkoff.Symmetric.MiddleGame.ActualParameters

/-!
# A punctured base point in the regular split cage

The eventual five-label theorem supplies a regular primitive split trace.
Inverting the affine trace change and evaluating the explicit torus
parametrization at parameter `1` gives an honest punctured surface point on
that cage fiber.
-/

namespace GenMarkoff.Symmetric.Cage

open BGS.Markoff

noncomputable section

/-- A regular split-maximal trace gives a punctured point on its first-axis
fiber whenever the symmetric multiplier is nonzero. -/
theorem exists_puncturedPoint_in_regularSplitCage_of_trace
    (p : ℕ) [Fact p.Prime]
    (c t : ZMod p) (hmultiplier : multiplier c ≠ 0)
    (ht : IsRegularSplitMaximalTrace p c t) :
    ∃ x : PuncturedSolutionSurface (coefficients c),
      IsInRegularSplitCage p c x.1 := by
  rcases ht with ⟨hregular, q, htraceQ, horder⟩
  let u := (t + c) / multiplier c
  have htraceU : t = trace c u := by
    dsimp [u, trace]
    field_simp [hmultiplier]
    ring
  have hu : u ≠ 0 := by
    dsimp [u]
    exact div_ne_zero hregular.2.1 hmultiplier
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have htraceEigen :
      t = (q : ZMod p) + (q : ZMod p)⁻¹ := by
    simpa only [splitTorusTrace, Units.val_inv_eq_inv_val] using htraceQ
  let point : Point (ZMod p) :=
    fiberPoint c u t (q : ZMod p) 1
  have hpointSolution : IsSolution (coefficients c) point := by
    exact fiberPoint_isSolution c u t (q : ZMod p) 1
      (Units.ne_zero q) one_ne_zero htraceEigen htraceU hD
  have hpointNe : point ≠ origin := by
    intro hzero
    apply hu
    have hfirst := congrArg Point.x1 hzero
    simpa [point, origin] using hfirst
  let surfacePoint : SolutionSurface (coefficients c) :=
    ⟨point, hpointSolution⟩
  let puncturedPoint : PuncturedSolutionSurface (coefficients c) :=
    ⟨surfacePoint, by
      intro hsurface
      apply hpointNe
      exact congrArg Subtype.val hsurface⟩
  refine ⟨puncturedPoint, Axis.first, ?_⟩
  change IsRegularSplitMaximalTrace p c (trace c point.x1)
  rw [fiberPoint_x1, ← htraceU]
  exact ⟨hregular, q, htraceQ, horder⟩

/-- For every sufficiently large prime and every admissible residue
coefficient, the regular split cage contains a punctured point. -/
theorem exists_threshold_puncturedPoint_in_regularSplitCage :
    ∃ threshold : ℕ,
      ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
        ∀ c : ZMod p, c ^ 2 ≠ 4 → multiplier c ≠ 0 →
          ∃ x : PuncturedSolutionSurface (coefficients c),
            IsInRegularSplitCage p c x.1 := by
  obtain ⟨threshold, hcard⟩ :=
    exists_threshold_four_lt_regularSplitMaximalTraceFinset_card
  refine ⟨threshold, ?_⟩
  intro p hp _ c hc hmultiplier
  have hpositive :
      0 < (regularSplitMaximalTraceFinset p c).card :=
    lt_trans (by omega) (hcard p hp c hc)
  obtain ⟨t, ht⟩ :=
    Finset.card_pos.mp hpositive
  have htRegular :
      IsRegularSplitMaximalTrace p c t :=
    mem_regularSplitMaximalTraceFinset_iff.mp ht
  exact exists_puncturedPoint_in_regularSplitCage_of_trace
    p c t hmultiplier htRegular

end

end GenMarkoff.Symmetric.Cage
