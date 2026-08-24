import GenMarkoff.Symmetric.Assembly.RegularMiddleIteration
import GenMarkoff.Symmetric.Assembly.RegularEndgame

/-!
# Candidate-regular middle game followed by the symmetric endgame

The middle-game iteration raises the maximal candidate-regular coordinate
order to the endgame scale.  The split/nonsplit endgame is then applied on
whichever of the three symmetric axes attains that maximum.
-/

namespace GenMarkoff.Symmetric.Assembly

open BGS.Markoff

noncomputable section

/-- Every point whose maximal candidate-regular coordinate order exceeds
`p ^ delta` reaches the regular split-maximal cage. -/
theorem exists_threshold_regularMiddleGame_to_regularSplitCage
    (splitCoefficient : ℕ)
    (hSplit :
      WeightedShiftedTraceWeilBoundAssumption splitCoefficient)
    (nonsplitCoefficient : ℕ)
    (hNonsplit :
      Endgame.Nonsplit.ShiftedSeededNonsplitTraceWeilBoundAssumption
        nonsplitCoefficient)
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaQuarter : delta ≤ (1 : ℝ) / 4) :
    ∃ threshold : ℕ,
      ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
        ∀ (c : ZMod p) (x : SolutionSurface (coefficients c)),
          c ^ 2 ≠ 4 →
          (p : ℝ) ^ delta <
            maximalCandidateRegularHalfStepOrder c x.1 →
          ∃ y : SolutionSurface (coefficients c),
            Cage.SameOneStepComponent c x y ∧
              Cage.IsInRegularSplitCage p c y := by
  obtain ⟨middleThreshold, hmiddle⟩ :=
    exists_threshold_regularMiddleGame_reaches_endgame
      hdelta hdeltaQuarter
  obtain ⟨firstThreshold, hfirst⟩ :=
    exists_threshold_regularFirstOrder_to_regularSplitCage
      splitCoefficient hSplit nonsplitCoefficient hNonsplit hdelta
  obtain ⟨secondThreshold, hsecond⟩ :=
    exists_threshold_regularSecondOrder_to_regularSplitCage
      splitCoefficient hSplit nonsplitCoefficient hNonsplit hdelta
  obtain ⟨thirdThreshold, hthird⟩ :=
    exists_threshold_regularThirdOrder_to_regularSplitCage
      splitCoefficient hSplit nonsplitCoefficient hNonsplit hdelta
  refine
    ⟨max middleThreshold
      (max firstThreshold (max secondThreshold thirdThreshold)), ?_⟩
  intro p hp _ c x hc hlarge
  have hpMiddle : middleThreshold ≤ p := by omega
  have hpFirst : firstThreshold ≤ p := by omega
  have hpSecond : secondThreshold ≤ p := by omega
  have hpThird : thirdThreshold ≤ p := by omega
  obtain ⟨z, hxz, hzLarge⟩ :=
    hmiddle p hpMiddle c hc x hlarge
  have hpPositive : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hzPositiveReal :
      (0 : ℝ) <
        maximalCandidateRegularHalfStepOrder c z.1 := by
    exact
      (Real.rpow_pos_of_pos hpPositive ((1 : ℝ) / 2 + delta)).trans_le
        hzLarge
  have hzPositive :
      0 < maximalCandidateRegularHalfStepOrder c z.1 := by
    exact_mod_cast hzPositiveReal
  obtain ⟨axis, hregular, horder⟩ :=
    exists_candidateRegular_axis_eq_maximal c z.1 hzPositive
  cases axis with
  | first =>
      have haxisLarge :
          (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
            halfStepOrder (trace c z.1.x1) := by
        have horder' :
            halfStepOrder (trace c z.1.x1) =
              maximalCandidateRegularHalfStepOrder c z.1 := by
          simpa [Cage.traceAt, Cage.coordinateAt] using horder
        calc
          (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
              (maximalCandidateRegularHalfStepOrder c z.1 : ℝ) :=
            hzLarge
          _ = (halfStepOrder (trace c z.1.x1) : ℝ) := by
            exact_mod_cast horder'.symm
      obtain ⟨y, hzy, hyCage⟩ :=
        hfirst p hpFirst c z hc
          (by simpa [Cage.traceAt, Cage.coordinateAt] using hregular)
          haxisLarge
      exact
        ⟨y, Cage.sameOneStepComponent_trans hxz hzy, hyCage⟩
  | second =>
      have haxisLarge :
          (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
            halfStepOrder (trace c z.1.x2) := by
        have horder' :
            halfStepOrder (trace c z.1.x2) =
              maximalCandidateRegularHalfStepOrder c z.1 := by
          simpa [Cage.traceAt, Cage.coordinateAt] using horder
        calc
          (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
              (maximalCandidateRegularHalfStepOrder c z.1 : ℝ) :=
            hzLarge
          _ = (halfStepOrder (trace c z.1.x2) : ℝ) := by
            exact_mod_cast horder'.symm
      obtain ⟨y, hzy, hyCage⟩ :=
        hsecond p hpSecond c z hc
          (by simpa [Cage.traceAt, Cage.coordinateAt] using hregular)
          haxisLarge
      exact
        ⟨y, Cage.sameOneStepComponent_trans hxz hzy, hyCage⟩
  | third =>
      have haxisLarge :
          (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
            halfStepOrder (trace c z.1.x3) := by
        have horder' :
            halfStepOrder (trace c z.1.x3) =
              maximalCandidateRegularHalfStepOrder c z.1 := by
          simpa [Cage.traceAt, Cage.coordinateAt] using horder
        calc
          (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
              (maximalCandidateRegularHalfStepOrder c z.1 : ℝ) :=
            hzLarge
          _ = (halfStepOrder (trace c z.1.x3) : ℝ) := by
            exact_mod_cast horder'.symm
      obtain ⟨y, hzy, hyCage⟩ :=
        hthird p hpThird c z hc
          (by simpa [Cage.traceAt, Cage.coordinateAt] using hregular)
          haxisLarge
      exact
        ⟨y, Cage.sameOneStepComponent_trans hxz hzy, hyCage⟩

end

end GenMarkoff.Symmetric.Assembly
