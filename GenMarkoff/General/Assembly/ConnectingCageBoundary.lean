import GenMarkoff.General.Assembly.ReductionSurjectivity
import GenMarkoff.General.Assembly.UnifiedRegularEndgame
import GenMarkoff.General.Assembly.VietaRotationEquivalence
import GenMarkoff.General.Cage.ConnectingFiber

/-!
# Exact full-Vieta connecting-cage boundary

The compiled startup--middle--endgame route stays inside a rotation component
and ends at a canonical first-axis primitive split point.  The connecting
fiber argument naturally joins such endpoints by individual Vieta
involutions, rather than by an even Vieta word.  This file records the exact
interface needed by that route and proves that it is sufficient for:

* eventual full-Vieta strong approximation;
* eventual rotation strong approximation at generic large primes; and
* eventual surjectivity of reduction on the fixed integral surface.

Thus the remaining geometric work may target full-Vieta connectivity of the
canonical endpoints directly; no prescribed rotation parity classes are
needed in the connecting-cage proof.
-/

namespace GenMarkoff.General.Assembly

open GenMarkoff.General.Cage

noncomputable section

/-- At one prime, all canonical first-axis primitive split endpoints lie in
one component of the full Vieta group. -/
def CanonicalFirstAxisPrimitiveSplitVietaCage
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p)) : Prop :=
  ∀ x y : SolutionSurface a,
    IsCanonicalFirstAxisPrimitiveSplit p a x →
      IsCanonicalFirstAxisPrimitiveSplit p a y →
        SameVietaComponent x y

/-- Eventual full-Vieta connecting-cage input for a fixed integral
coefficient triple. -/
def EventuallyCanonicalFirstAxisPrimitiveSplitVietaCage
    (a : Coefficients ℤ) : Prop :=
  ∃ threshold : ℕ,
    ∀ (p : ℕ) (hp : p.Prime), threshold ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      CanonicalFirstAxisPrimitiveSplitVietaCage
        p (modCoefficients a p)

/-- Componentwise rotation reachability of canonical endpoints, together
with a full-Vieta connecting cage, gives Vieta transitivity at one prime. -/
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

/-- The compiled startup--middle--endgame route leaves exactly the eventual
full-Vieta connecting cage as input for eventual Vieta strong
approximation. -/
theorem
    IntegrallyNondegenerate.eventuallyVietaStrongApproximation_of_canonicalFirstAxisPrimitiveSplitVietaCage
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (hcage : EventuallyCanonicalFirstAxisPrimitiveSplitVietaCage a) :
    EventuallyVietaStrongApproximation a := by
  obtain ⟨routeThreshold, hroute⟩ :=
    GenMarkoff.General.Assembly.IntegrallyNondegenerate.exists_threshold_every_puncturedRotationComponent_reaches_canonicalFirstAxisPrimitiveSplit_of_generalHasseWeil
      ha
  obtain ⟨cageThreshold, hcage⟩ := hcage
  refine ⟨max routeThreshold cageThreshold, ?_⟩
  intro p hp hpLarge
  have hpRoute : routeThreshold ≤ p :=
    (Nat.le_max_left routeThreshold cageThreshold).trans hpLarge
  have hpCage : cageThreshold ≤ p :=
    (Nat.le_max_right routeThreshold cageThreshold).trans hpLarge
  exact
    vietaStrongApproximationAt_of_componentwise_canonicalFirstAxisPrimitiveSplit
      a p hp (hroute p hp hpRoute) (hcage p hp hpCage)

/-- The same full-Vieta connecting cage implies the project's eventual
rotation-group strong approximation statement. -/
theorem
    IntegrallyNondegenerate.eventuallyRotationStrongApproximation_of_canonicalFirstAxisPrimitiveSplitVietaCage
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (hcage : EventuallyCanonicalFirstAxisPrimitiveSplitVietaCage a) :
    EventuallyRotationStrongApproximation a :=
  (GenMarkoff.General.Assembly.IntegrallyNondegenerate.eventuallyRotationStrongApproximation_iff_eventuallyVietaStrongApproximation
    ha).mpr
    (GenMarkoff.General.Assembly.IntegrallyNondegenerate.eventuallyVietaStrongApproximation_of_canonicalFirstAxisPrimitiveSplitVietaCage
      ha hcage)

/-- The full-Vieta connecting cage also implies eventual surjectivity of
coordinatewise reduction from the fixed integral surface. -/
theorem
    IntegrallyNondegenerate.eventuallyReductionSurjective_of_canonicalFirstAxisPrimitiveSplitVietaCage
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (hcage : EventuallyCanonicalFirstAxisPrimitiveSplitVietaCage a) :
    ∃ p0 : ℕ, ∀ (p : ℕ) (_hp : p.Prime), p0 ≤ p →
      Function.Surjective
        ((fixedIntegralCoefficientSurfaceFunctor a).map
          (CommRingCat.ofHom (Int.castRingHom (ZMod p)))) :=
  eventually_reduction_surjective_of_eventuallyVietaStrongApproximation a
    (GenMarkoff.General.Assembly.IntegrallyNondegenerate.eventuallyVietaStrongApproximation_of_canonicalFirstAxisPrimitiveSplitVietaCage
      ha hcage)

end

end GenMarkoff.General.Assembly
