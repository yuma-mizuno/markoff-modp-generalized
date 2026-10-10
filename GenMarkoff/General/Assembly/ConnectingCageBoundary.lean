import GenMarkoff.General.Assembly.ReductionSurjectivity
import GenMarkoff.General.Assembly.UnifiedRegularEndgame
import GenMarkoff.General.Assembly.Vieta.RotationEquivalence
import GenMarkoff.General.Cage.Connecting.Fiber

/-!
# Vieta transitivity from a connecting cage

The startup, middle game and endgame stay inside a rotation component and
end at a canonical first-axis primitive split point
(`IsCanonicalFirstAxisPrimitiveSplit`).  The connecting-cage argument joins
such points by Vieta words of either parity.  This file defines
`CanonicalFirstAxisPrimitiveSplitVietaCage`, the statement that all canonical
points lie in one component of the full Vieta group, and proves
`vietaStrongApproximationAt_of_componentwise_canonicalFirstAxisPrimitiveSplit`:
if every punctured rotation component contains a canonical point and the
cage statement holds, then the Vieta group acts transitively on the punctured
surface modulo `p`.
-/

namespace GenMarkoff.General.Assembly

open GenMarkoff.General.Cage

noncomputable section

/-- At one prime, all canonical first-axis primitive split points lie in
one component of the full Vieta group. -/
def CanonicalFirstAxisPrimitiveSplitVietaCage
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p)) : Prop :=
  ∀ x y : SolutionSurface a,
    IsCanonicalFirstAxisPrimitiveSplit p a x →
      IsCanonicalFirstAxisPrimitiveSplit p a y →
        SameVietaComponent x y

/-- If every punctured rotation component modulo `p` contains a canonical
first-axis primitive split point and all such points are Vieta-connected,
then the Vieta group acts transitively on the punctured surface modulo `p`. -/
theorem vietaStrongApproximationAt_of_componentwise_canonicalFirstAxisPrimitiveSplit
    (a : Coefficients ℤ) (p : ℕ) (hp : p.Prime)
    (hroute :
      letI : Fact p.Prime := ⟨hp⟩
      ∀ x : PuncturedSolutionSurface (modCoefficients a p),
        ∃ finish : SolutionSurface (modCoefficients a p),
          SameRotationComponent x.1 finish ∧
            IsCanonicalFirstAxisPrimitiveSplit
              p (modCoefficients a p) finish)
    (hcage :
      letI : Fact p.Prime := ⟨hp⟩
      CanonicalFirstAxisPrimitiveSplitVietaCage
        p (modCoefficients a p)) :
    VietaStrongApproximationAt a p hp := by
  letI : Fact p.Prime := ⟨hp⟩
  intro x y
  obtain ⟨finishX, hxFinish, hcanonicalX⟩ := hroute x
  obtain ⟨finishY, hyFinish, hcanonicalY⟩ := hroute y
  have hxFinishVieta :
      SameVietaComponent x.1 finishX :=
    sameVietaComponent_of_sameRotationComponent hxFinish
  have hyFinishVieta :
      SameVietaComponent y.1 finishY :=
    sameVietaComponent_of_sameRotationComponent hyFinish
  have hfinish :
      SameVietaComponent finishX finishY :=
    hcage finishX finishY hcanonicalX hcanonicalY
  have hxy :
      SameVietaComponent x.1 y.1 :=
    sameVietaComponent_trans hxFinishVieta
      (sameVietaComponent_trans hfinish
        (sameVietaComponent_symm hyFinishVieta))
  obtain ⟨g, hg⟩ := hxy
  refine ⟨g, ?_⟩
  apply Subtype.ext
  exact hg

end

end GenMarkoff.General.Assembly
