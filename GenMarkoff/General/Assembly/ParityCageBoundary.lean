import GenMarkoff.General.Assembly.UnifiedRegularEndgame

/-!
# Exact parity-cage boundary for the unequal-coefficient route

The startup, middle game, and split/nonsplit endgames show that every
punctured rotation component reaches a canonical first-axis primitive split
point.  For the direct pre-transitivity route, the final cage input is stated
only on those canonical points: any two of them must lie in the same
fixed-coefficient rotation component.

## New consideration in the unequal-coefficient generalization

The cage predicate uses `SameRotationComponent`, not full-Vieta connectivity
and not connectivity of an unsplit conic fiber.  Thus a direct
parity-incidence proof must retain the three prescribed square-coset classes
identified by the first-axis incidence analysis.  The theorem below proves
mechanically that this precise parity-aware cage input, together with the
compiled componentwise route, implies eventual rotation strong approximation.
The selected connecting-fiber proof does not use this route; after global
transitivity is known, the predicate follows as a downstream corollary.
-/

namespace GenMarkoff.General.Assembly

noncomputable section

/-- The exact direct-route cage statement at one prime: all canonical
first-axis primitive split endpoints lie in one rotation component. -/
def CanonicalFirstAxisPrimitiveSplitCage
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p)) : Prop :=
  ∀ x y : SolutionSurface a,
    IsCanonicalFirstAxisPrimitiveSplit p a x →
      IsCanonicalFirstAxisPrimitiveSplit p a y →
        SameRotationComponent x y

/-- The eventual parity-aware cage interface for a fixed integral coefficient
triple. -/
def EventuallyCanonicalFirstAxisPrimitiveSplitCage
    (a : Coefficients ℤ) : Prop :=
  ∃ threshold : ℕ,
    ∀ (p : ℕ) (hp : p.Prime), threshold ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      CanonicalFirstAxisPrimitiveSplitCage p (modCoefficients a p)

/-- At one prime, componentwise reachability of canonical endpoints plus the
canonical parity cage gives transitivity of the actual rotation group. -/
theorem rotationStrongApproximationAt_of_componentwise_canonicalFirstAxisPrimitiveSplit
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
      CanonicalFirstAxisPrimitiveSplitCage
        p (modCoefficients a p)) :
    RotationStrongApproximationAt a p hp := by
  letI : Fact p.Prime := ⟨hp⟩
  intro x y
  obtain ⟨finishX, hxFinish, hcanonicalX⟩ := hroute x
  obtain ⟨finishY, hyFinish, hcanonicalY⟩ := hroute y
  have hfinish :
      SameRotationComponent finishX finishY :=
    hcage finishX finishY hcanonicalX hcanonicalY
  have hxy :
      SameRotationComponent x.1 y.1 :=
    sameRotationComponent_trans hxFinish
      (sameRotationComponent_trans hfinish
        (sameRotationComponent_symm hyFinish))
  obtain ⟨g, hg⟩ := hxy
  refine ⟨g, ?_⟩
  apply Subtype.ext
  exact hg

/-- The compiled startup--middle--endgame theorem leaves exactly the eventual
canonical parity cage as the mathematical input for eventual rotation strong
approximation. -/
theorem
    IntegrallyNondegenerate.eventuallyRotationStrongApproximation_of_canonicalFirstAxisPrimitiveSplitCage
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (hcage : EventuallyCanonicalFirstAxisPrimitiveSplitCage a) :
    EventuallyRotationStrongApproximation a := by
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
    rotationStrongApproximationAt_of_componentwise_canonicalFirstAxisPrimitiveSplit
      a p hp (hroute p hp hpRoute) (hcage p hp hpCage)

end

end GenMarkoff.General.Assembly
