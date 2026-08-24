import GenMarkoff.General.Assembly.RegularSplitEndgame
import GenMarkoff.General.Endgame.Nonsplit.ActualRotation

/-!
# Canonical first-axis assembly from a regular nonsplit source

This module assembles the two fixed-coefficient nonsplit-source directions.
No coordinate or coefficient permutation is used.

## New nonsplit considerations

* A primitive element of the quadratic norm-one torus has square order
  `(p + 1) / 2`, rather than the split value `(p - 1) / 2`.  The exact
  norm-one formula is proved below.
* The currently formalized descended nonsplit count does **not** return such
  a primitive norm-one element.  Its right-hand trace parameter is a
  primitive `v : (ZMod p)ˣ`; consequently its proved target is split.
  Claiming a canonical primitive nonsplit endpoint from that theorem would
  change the torus and is therefore invalid.
* The maximal sound assembly from the available count reaches a canonical
  first-axis primitive split endpoint in at most two directed rotation
  segments.  A `.secondFirst` source needs one `rotation2` segment.  A
  `.firstSecond` source first uses `rotation1`, then the split dispatcher
  uses `rotation2`.  The coefficient triple remains fixed throughout.

A genuine canonical primitive nonsplit target requires a new descended
count-and-wiring theorem whose target trace is parametrized by
`quadraticNormOneTorus p`; it is not hidden behind an assumption here.
-/

namespace GenMarkoff.General.Assembly

open BGS.Markoff
open GenMarkoff.General.Endgame
open GenMarkoff.General.Endgame.Nonsplit
open GenMarkoff.Symmetric.Endgame.Nonsplit

noncomputable section

/-- The intended canonical nonsplit endpoint.  This definition records the
missing target exactly; the available descended count does not yet produce
it. -/
def IsCanonicalFirstAxisPrimitiveNonsplit
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (x : SolutionSurface a) : Prop :=
  ∃ w : quadraticNormOneTorus p,
    traceAt a .first x.1 = quadraticNormOneTrace p w ∧
      orderOf w = Nat.card (quadraticNormOneTorus p) ∧
        OrderedTraceCandidateRegular a.a1 a.a2 a.a3
          (traceAt a .first x.1)

/-- A primitive quadratic norm-one eigenvalue has square order exactly half
of `p + 1`.  This is the numerical bridge a future genuine nonsplit-target
dispatcher must use. -/
theorem orderOf_sq_eq_half_add_one_of_primitiveNormOne
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (w : quadraticNormOneTorus p)
    (hprimitive : orderOf w = Nat.card (quadraticNormOneTorus p)) :
    orderOf (w ^ 2) = (p + 1) / 2 := by
  rw [orderOf_pow, hprimitive, quadraticNormOneTorus_natCard]
  rw [Nat.gcd_eq_right
    (Nat.even_add_one.mpr
      (Nat.not_even_iff_odd.mpr
        ((Fact.out : p.Prime).odd_of_ne_two hpTwo))).two_dvd]

private theorem coe_iterate_rotation1SurfacePerm
    {R : Type*} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) (n : ℕ) :
    ((((rotation1SurfacePerm a)^[n]) x :
      SolutionSurface a) : Point R) =
        ((rotation1 a)^[n]) x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        coe_rotation1SurfacePerm, ih]

private theorem coe_iterate_rotation2SurfacePerm
    {R : Type*} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) (n : ℕ) :
    ((((rotation2SurfacePerm a)^[n]) x :
      SolutionSurface a) : Point R) =
        ((rotation2 a)^[n]) x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        coe_rotation2SurfacePerm, ih]

/-- Every sufficiently large regular nonsplit-source alternating state
reaches a canonical primitive **split** point on the first axis in the same
fixed-coefficient rotation component.

This theorem deliberately names the proved target torus.  The
`.secondFirst` branch uses one actual `rotation2` segment.  The
`.firstSecond` branch uses one actual `rotation1` segment to reach a
primitive split second-axis state and then invokes the split dispatcher for
one actual `rotation2` segment. -/
private theorem
    alternatingRegularNonsplitState_reaches_canonicalFirstAxisPrimitiveSplit_of_dispatchers
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (state : AlternatingRegularState a)
    (hstart :
      alternatingPrimitiveSplitEndgameResultFromNonsplitSource
        p a state.direction state.point.1)
    (hprimitive :
      ∀ (next : AlternatingRegularState a) (v : (ZMod p)ˣ),
        traceAt a next.direction.fixed next.point.1 = splitTorusTrace v →
        (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤ orderOf (v ^ 2) →
        alternatingPrimitiveSplitEndgameResult
          p a next.direction next.point.1)
    (hsquare :
      (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
        (((p - 1) / 2 : ℕ) : ℝ)) :
    ∃ finish : SolutionSurface a,
      SameRotationComponent state.point finish ∧
        IsCanonicalFirstAxisPrimitiveSplit p a finish := by
  have hfirstResult := hstart
  cases state with
  | mk direction point hregular =>
      cases direction with
      | secondFirst =>
          change
            ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
              orderedTrace a.multiplier a.a1
                  (((rotation2 a)^[n]) point.1).x1 =
                splitTorusTrace v ∧
              orderOf v = Nat.card (ZMod p)ˣ ∧
                OrderedTraceCandidateRegular
                  a.a1 a.a2 a.a3 (splitTorusTrace v)
            at hfirstResult
          obtain ⟨n, v, hn, hvOrder, hvRegular⟩ :=
            hfirstResult
          let finish : SolutionSurface a :=
            ((rotation2SurfacePerm a)^[n]) point
          have hfinishPoint :
              finish.1 = ((rotation2 a)^[n]) point.1 := by
            simpa [finish] using
              coe_iterate_rotation2SurfacePerm a point n
          have hfinishTrace :
              traceAt a .first finish.1 = splitTorusTrace v := by
            change
              orderedTrace a.multiplier a.a1 finish.1.x1 =
                splitTorusTrace v
            rw [hfinishPoint]
            exact hn
          have hcomponent :
              SameRotationComponent point finish := by
            simpa [finish, rotationSurfacePermAt] using
              sameRotationComponent_iterate_rotationSurfacePermAt
                a .second point n
          refine ⟨finish, hcomponent, v, hfinishTrace, hvOrder, ?_⟩
          rw [hfinishTrace]
          exact hvRegular
      | firstSecond =>
          change
            ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
              orderedTrace a.multiplier a.a2
                  (((rotation1 a)^[n]) point.1).x2 =
                splitTorusTrace v ∧
              orderOf v = Nat.card (ZMod p)ˣ ∧
                OrderedTraceCandidateRegular
                  a.a2 a.a1 a.a3 (splitTorusTrace v)
            at hfirstResult
          obtain ⟨n₁, v₁, hn₁, hv₁Order, hv₁Regular⟩ :=
            hfirstResult
          let middle : SolutionSurface a :=
            ((rotation1SurfacePerm a)^[n₁]) point
          have hmiddlePoint :
              middle.1 = ((rotation1 a)^[n₁]) point.1 := by
            simpa [middle] using
              coe_iterate_rotation1SurfacePerm a point n₁
          have hmiddleTrace :
              traceAt a .second middle.1 = splitTorusTrace v₁ := by
            change
              orderedTrace a.multiplier a.a2 middle.1.x2 =
                splitTorusTrace v₁
            rw [hmiddlePoint]
            exact hn₁
          have hmiddleRegular :
              OrderedTraceCandidateRegular a.a2 a.a1 a.a3
                (traceAt a .second middle.1) := by
            rw [hmiddleTrace]
            exact hv₁Regular
          let middleState : AlternatingRegularState a :=
            ⟨.secondFirst, middle, hmiddleRegular⟩
          have hmiddleComponent :
              SameRotationComponent point middle := by
            simpa [middle, rotationSurfacePermAt] using
              sameRotationComponent_iterate_rotationSurfacePermAt
                a .first point n₁
          have hv₁SquareOrder :
              orderOf (v₁ ^ 2) = (p - 1) / 2 :=
            orderOf_sq_eq_half_sub_one_of_primitive
              p hpTwo v₁ hv₁Order
          have hv₁Large :
              (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
                orderOf (v₁ ^ 2) := by
            rw [hv₁SquareOrder]
            exact hsquare
          have hmiddleEigen :
              traceAt a middleState.direction.fixed middleState.point.1 =
                splitTorusTrace v₁ := by
            simpa [middleState, AlternatingDirectedAxis.fixed] using
              hmiddleTrace
          have hsecondResult :=
            hprimitive middleState v₁ hmiddleEigen hv₁Large
          change
            ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
              orderedTrace a.multiplier a.a1
                  (((rotation2 a)^[n]) middle.1).x1 =
                splitTorusTrace v ∧
              orderOf v = Nat.card (ZMod p)ˣ ∧
                OrderedTraceCandidateRegular
                  a.a1 a.a2 a.a3 (splitTorusTrace v)
            at hsecondResult
          obtain ⟨n₂, v₂, hn₂, hv₂Order, hv₂Regular⟩ :=
            hsecondResult
          let finish : SolutionSurface a :=
            ((rotation2SurfacePerm a)^[n₂]) middle
          have hfinishPoint :
              finish.1 = ((rotation2 a)^[n₂]) middle.1 := by
            simpa [finish] using
              coe_iterate_rotation2SurfacePerm a middle n₂
          have hfinishTrace :
              traceAt a .first finish.1 = splitTorusTrace v₂ := by
            change
              orderedTrace a.multiplier a.a1 finish.1.x1 =
                splitTorusTrace v₂
            rw [hfinishPoint]
            exact hn₂
          have hfinishComponent :
              SameRotationComponent middle finish := by
            simpa [finish, rotationSurfacePermAt] using
              sameRotationComponent_iterate_rotationSurfacePermAt
                a .second middle n₂
          refine
            ⟨finish,
              sameRotationComponent_trans
                hmiddleComponent hfinishComponent,
              v₂, hfinishTrace, hv₂Order, ?_⟩
          rw [hfinishTrace]
          exact hv₂Regular

/-- Existential-threshold wrapper preserving the general coefficient and
positive-exponent API. -/
theorem
    exists_threshold_alternatingRegularNonsplitState_reaches_canonicalFirstAxisPrimitiveSplit
    (coefficient : ℕ)
    (hNonsplit :
      ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient)
    (hSplit : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      [Fact p.Prime] →
      ∀ (a : Coefficients (ZMod p)),
        a.a1 ^ 2 ≠ 4 →
        a.a2 ^ 2 ≠ 4 →
        ∀ (state : AlternatingRegularState a)
            (w : quadraticNormOneTorus p),
          traceAt a state.direction.fixed state.point.1 =
              quadraticNormOneTrace p w →
          (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (w ^ 2) →
          ∃ finish : SolutionSurface a,
            SameRotationComponent state.point finish ∧
              IsCanonicalFirstAxisPrimitiveSplit p a finish := by
  obtain ⟨startThreshold, hstart⟩ :=
    exists_threshold_alternatingRegularState_actualNonsplitSourcePrimitiveSplitEndgame
      coefficient hNonsplit hdelta
  obtain ⟨primitiveThreshold, hprimitive⟩ :=
    exists_threshold_alternatingRegularState_actualSplitPrimitiveEndgame
      coefficient hSplit
        (delta := (1 : ℝ) / 4) (by norm_num)
  obtain ⟨squareThreshold, hsquare⟩ :=
    exists_threshold_threeQuarter_le_half_sub_one
  refine
    ⟨max (max startThreshold primitiveThreshold)
        (max squareThreshold 3), ?_⟩
  intro p hp _ a hA1 hA2 state w heigen hlarge
  have hpStart : startThreshold ≤ p :=
    (Nat.le_max_left startThreshold primitiveThreshold).trans
      ((Nat.le_max_left
        (max startThreshold primitiveThreshold)
        (max squareThreshold 3)).trans hp)
  have hpPrimitive : primitiveThreshold ≤ p :=
    (Nat.le_max_right startThreshold primitiveThreshold).trans
      ((Nat.le_max_left
        (max startThreshold primitiveThreshold)
        (max squareThreshold 3)).trans hp)
  have hpSquare : squareThreshold ≤ p :=
    (Nat.le_max_left squareThreshold 3).trans
      ((Nat.le_max_right
        (max startThreshold primitiveThreshold)
        (max squareThreshold 3)).trans hp)
  have hpThree : 3 ≤ p :=
    (Nat.le_max_right squareThreshold 3).trans
      ((Nat.le_max_right
        (max startThreshold primitiveThreshold)
        (max squareThreshold 3)).trans hp)
  exact
    alternatingRegularNonsplitState_reaches_canonicalFirstAxisPrimitiveSplit_of_dispatchers
      p (by omega) a state
      (hstart p hpStart a hA1 hA2 state w heigen hlarge)
      (fun next v hnext hnextLarge =>
        hprimitive p hpPrimitive a hA1 hA2 next v hnext hnextLarge)
      (hsquare p hpSquare)

/-- Closed-cutoff nonsplit-source assembly. -/
theorem alternatingRegularNonsplitState_reaches_canonicalFirstAxisPrimitiveSplit_of_analyticCutoff
    (coefficient : ℕ)
    (hNonsplit :
      ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient)
    (hSplit : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : (1 : ℝ) / 32 ≤ delta)
    (hcoefficient : coefficient + 40 ≤ 1032)
    (p : ℕ) (hp : GenMarkoff.General.Explicit.analyticCutoff ≤ p)
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
      GenMarkoff.General.Explicit.five_le_analyticCutoff.trans hp
    omega
  exact
    alternatingRegularNonsplitState_reaches_canonicalFirstAxisPrimitiveSplit_of_dispatchers
      p hpTwo a state
      (alternatingRegularState_actualNonsplitSourcePrimitiveSplitEndgame_of_analyticCutoff
        coefficient hNonsplit hdelta hcoefficient p hp
          a hA1 hA2 state w heigen hlarge)
      (fun next v hnext hnextLarge =>
        alternatingRegularState_actualSplitPrimitiveEndgame_of_analyticCutoff
          coefficient hSplit (delta := (1 : ℝ) / 4) (by norm_num)
            hcoefficient p hp a hA1 hA2 next v hnext hnextLarge)
      (threeQuarter_le_half_sub_one_of_analyticCutoff hp)

/-- Reasonable-cutoff nonsplit-source assembly.  The nonsplit source step and
the possible split return step both run at exponent `1/4`. -/
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
    alternatingRegularNonsplitState_reaches_canonicalFirstAxisPrimitiveSplit_of_dispatchers
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
