module

public import GenMarkoff.General.Assembly.RegularSplitEndgame
public import GenMarkoff.General.Endgame.Nonsplit.ActualRotation

@[expose] public section

/-!
# Canonical first-axis split point from a regular nonsplit source

An alternating regular state whose fixed trace comes from an element `w` of
the quadratic norm-one torus with `orderOf (w ^ 2)` large reaches a canonical
primitive split first-axis point (`IsCanonicalFirstAxisPrimitiveSplit`) in
its rotation component.  The nonsplit-source endgame move produces a
primitive split eigenvalue `v : (ZMod p)ˣ`, so the target is split.  A
`.secondFirst` source needs one `rotation2` segment; a `.firstSecond` source
uses a `rotation1` segment and then the split endgame move along `rotation2`.
The coefficient triple stays fixed throughout.
-/

namespace GenMarkoff.General.Assembly

open BGS.Markoff
open GenMarkoff.General.Endgame
open GenMarkoff.General.Endgame.Nonsplit
open GenMarkoff.ShiftedTrace.Endgame.Nonsplit

noncomputable section

/-- Beyond `reasonableAnalyticCutoff`, with `a₁ ^ 2 ≠ 4` and `a₂ ^ 2 ≠ 4`, an
alternating regular state whose fixed trace is the trace of
`w : quadraticNormOneTorus p` with `p ^ (1/2 + delta) ≤ orderOf (w ^ 2)` for
some `delta ≥ 1/4` reaches a canonical primitive split first-axis point in
its rotation component.  The nonsplit and split affine point-count estimates
enter through `hNonsplit` and `hSplit`. -/
theorem alternatingRegularNonsplitState_reaches_canonicalFirstAxisPrimitiveSplit_of_reasonableCutoff
    (coefficient : ℕ)
    (hNonsplit :
      ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient)
    (hSplit : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : (1 : ℝ) / 4 ≤ delta)
    (hcoefficient : coefficient + 40 ≤ 1032)
    (p : ℕ)
    (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (state : AlternatingRegularState a)
    (w : quadraticNormOneTorus p)
    (heigen :
      traceAt a state.direction.fixed state.point.1 =
        quadraticNormOneTrace p w)
    (hlarge :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (w ^ 2)) :
    ∃ finish : SolutionSurface a,
      SameRotationComponent state.point finish ∧
        IsCanonicalFirstAxisPrimitiveSplit p a finish := by
  have hpTwo : p ≠ 2 := by
    have hpFive :=
      GenMarkoff.General.Explicit.five_le_reasonableAnalyticCutoff.trans hp
    omega
  exact
    alternatingRegularState_reaches_canonicalFirstAxisPrimitiveSplit
      p hpTwo a state
      (alternatingRegularState_actualNonsplitSourcePrimitiveSplitEndgame_of_reasonableCutoff
        coefficient hNonsplit hdelta hcoefficient p hp
          a hA1 hA2 state w heigen hlarge)
      (fun next v hnext hnextLarge =>
        alternatingRegularState_actualSplitPrimitiveEndgame_of_reasonableCutoff
          coefficient hSplit (delta := (1 : ℝ) / 4) (by norm_num)
            hcoefficient p hp a hA1 hA2 next v hnext hnextLarge)
      (threeQuarter_le_half_sub_one_of_reasonableCutoff hp)

end

end GenMarkoff.General.Assembly
