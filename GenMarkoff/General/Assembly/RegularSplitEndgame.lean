import GenMarkoff.General.Endgame.ActualSplitRotation
import GenMarkoff.General.Arithmetic.ReasonableCutoff

/-!
# Canonical first-axis regular split endgame

This module assembles the two fixed-coefficient alternating split directions
into a single canonical first-axis endpoint.  No coordinate or coefficient
permutation is used.

## New two-step consideration

If an alternating state starts in direction `.firstSecond`, the first split
endgame move produces a primitive second-axis eigenvalue `v`; a second move is
needed to return to the canonical first axis.  The actual rotation generator
is `v ^ 2`, not `v`.  Since a primitive `v : (ZMod p)ˣ` has order `p - 1`,
its square has order `(p - 1) / 2`.  This still dominates the fixed
three-quarter endgame scale for all sufficiently large `p`, which supplies
the second dispatcher's large-order hypothesis.

The output predicate packages a genuine solution-surface point, the primitive
split eigenvalue of its first-axis trace, and candidate regularity in the exact
ordered frame `(a.a1, a.a2, a.a3)`.
-/

namespace GenMarkoff.General.Assembly

open BGS.Markoff
open Filter
open GenMarkoff.General.Endgame

noncomputable section

/-- Canonical split endgame target on the first axis.  The subtype `x`
contains the proof that the point lies on the fixed-coefficient surface. -/
def IsCanonicalFirstAxisPrimitiveSplit
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (x : SolutionSurface a) : Prop :=
  ∃ v : (ZMod p)ˣ,
    traceAt a .first x.1 = splitTorusTrace v ∧
      orderOf v = Nat.card (ZMod p)ˣ ∧
        OrderedTraceCandidateRegular a.a1 a.a2 a.a3
          (traceAt a .first x.1)

/-- A primitive split eigenvalue has square order exactly half the size of
the prime-field unit group. -/
theorem orderOf_sq_eq_half_sub_one_of_primitive
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (v : (ZMod p)ˣ)
    (hprimitive : orderOf v = Nat.card (ZMod p)ˣ) :
    orderOf (v ^ 2) = (p - 1) / 2 := by
  rw [orderOf_pow, hprimitive, Nat.card_units, Nat.card_zmod]
  rw [Nat.gcd_eq_right
    ((Fact.out : p.Prime).even_sub_one hpTwo).two_dvd]

/-- Uniform numerical bridge used only for the second alternating move:
the three-quarter scale is eventually at most half of `p - 1`. -/
theorem exists_threshold_threeQuarter_le_half_sub_one :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
        (((p - 1) / 2 : ℕ) : ℝ) := by
  have hexponents :
      (1 : ℝ) / 2 + (1 : ℝ) / 4 < 1 := by
    norm_num
  have habsorb :
      ∀ᶠ p : ℕ in atTop,
        (4 : ℝ) * (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) <
          (p : ℝ) ^ (1 : ℝ) :=
    BGS.Markoff.eventually_const_mul_rpow_lt_rpow
      (C := (4 : ℝ)) hexponents
  obtain ⟨absorbThreshold, hAbsorbThreshold⟩ :=
    Filter.eventually_atTop.mp habsorb
  refine ⟨max absorbThreshold 4, ?_⟩
  intro p hp
  have hpAbsorb : absorbThreshold ≤ p :=
    (Nat.le_max_left absorbThreshold 4).trans hp
  have hpFour : 4 ≤ p :=
    (Nat.le_max_right absorbThreshold 4).trans hp
  have hrealAbsorb :
      (4 : ℝ) * (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) <
        (p : ℝ) := by
    simpa using hAbsorbThreshold p hpAbsorb
  have hnat : p ≤ 4 * ((p - 1) / 2) := by
    omega
  have hcast :
      (p : ℝ) ≤
        (4 : ℝ) * (((p - 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- Closed-cutoff form of the numerical bridge for the second alternating
move. -/
theorem threeQuarter_le_half_sub_one_of_analyticCutoff
    {p : ℕ} (hp : GenMarkoff.General.Explicit.analyticCutoff ≤ p) :
    (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
      (((p - 1) / 2 : ℕ) : ℝ) := by
  have hpFive : 5 ≤ p :=
    GenMarkoff.General.Explicit.five_le_analyticCutoff.trans hp
  have hpFour : 4 ≤ p := by omega
  have hpRealOne : (1 : ℝ) < p := by
    exact_mod_cast GenMarkoff.General.Explicit.analyticCutoff_gt_one.trans_le hp
  have hpRealPos : (0 : ℝ) < p := zero_lt_one.trans hpRealOne
  have hfour :
      (4 : ℝ) < (p : ℝ) ^ (1 / 256 : ℝ) :=
    GenMarkoff.General.Explicit.small_fixed_lt_rpow_one_div_twoHundredFiftySix
      hp (by norm_num)
  have habsorb :
      (4 : ℝ) * (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) <
        (p : ℝ) := by
    calc
      (4 : ℝ) * (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) <
          (p : ℝ) ^ (1 / 256 : ℝ) *
            (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) := by
        exact mul_lt_mul_of_pos_right hfour
          (Real.rpow_pos_of_pos hpRealPos _)
      _ = (p : ℝ) ^ (193 / 256 : ℝ) := by
        rw [← Real.rpow_add hpRealPos]
        congr 1
        norm_num
      _ < (p : ℝ) := by
        simpa only [Real.rpow_one] using
          Real.rpow_lt_rpow_of_exponent_lt hpRealOne
            (show (193 / 256 : ℝ) < 1 by norm_num)
  have hnat : p ≤ 4 * ((p - 1) / 2) := by omega
  have hcast :
      (p : ℝ) ≤ (4 : ℝ) * (((p - 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- The reasonable closed cutoff gives the same bridge using the much weaker
estimate `4 < p^(1/8)`.  Thus the exponent bookkeeping is `1/8 + 3/4 =
7/8 < 1`, instead of the old `1/256 + 3/4` calculation. -/
theorem threeQuarter_le_half_sub_one_of_reasonableCutoff
    {p : ℕ} (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p) :
    (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
      (((p - 1) / 2 : ℕ) : ℝ) := by
  have hpFive : 5 ≤ p :=
    GenMarkoff.General.Explicit.five_le_reasonableAnalyticCutoff.trans hp
  have hpRealOne : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hpRealPos : (0 : ℝ) < p := zero_lt_one.trans hpRealOne
  have hfour :
      (4 : ℝ) < (p : ℝ) ^ (1 / 8 : ℝ) :=
    GenMarkoff.General.Explicit.reasonable_small_fixed_lt_rpow_one_div_eight
      hp (by norm_num)
  have habsorb :
      (4 : ℝ) * (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) <
        (p : ℝ) := by
    calc
      (4 : ℝ) * (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) <
          (p : ℝ) ^ (1 / 8 : ℝ) *
            (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) := by
        exact mul_lt_mul_of_pos_right hfour
          (Real.rpow_pos_of_pos hpRealPos _)
      _ = (p : ℝ) ^ (7 / 8 : ℝ) := by
        rw [← Real.rpow_add hpRealPos]
        congr 1
        norm_num
      _ < (p : ℝ) := by
        simpa only [Real.rpow_one] using
          Real.rpow_lt_rpow_of_exponent_lt hpRealOne
            (show (7 / 8 : ℝ) < 1 by norm_num)
  have hnat : p ≤ 4 * ((p - 1) / 2) := by omega
  have hcast :
      (p : ℝ) ≤ (4 : ℝ) * (((p - 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  linarith

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

/-- Every sufficiently large split alternating endgame state reaches a
canonical primitive split point on the first axis in the same
fixed-coefficient rotation component.

The `.secondFirst` branch uses one actual `rotation2` segment.  The
`.firstSecond` branch first uses an actual `rotation1` segment to obtain a
primitive second-axis state, then applies the dispatcher once more and uses
an actual `rotation2` segment to return to the first axis. -/
private theorem
    alternatingRegularState_reaches_canonicalFirstAxisPrimitiveSplit_of_dispatchers
    (p : ℕ) [Fact p.Prime]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (state : AlternatingRegularState a)
    (hstart :
      alternatingPrimitiveSplitEndgameResult
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

/-- Every sufficiently large split alternating endgame state reaches the
canonical first-axis target. -/
theorem
    exists_threshold_alternatingRegularState_reaches_canonicalFirstAxisPrimitiveSplit
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      [Fact p.Prime] →
      ∀ (a : Coefficients (ZMod p)),
        a.a1 ^ 2 ≠ 4 →
        a.a2 ^ 2 ≠ 4 →
        ∀ (state : AlternatingRegularState a) (q : (ZMod p)ˣ),
          traceAt a state.direction.fixed state.point.1 =
              splitTorusTrace q →
          (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (q ^ 2) →
          ∃ finish : SolutionSurface a,
            SameRotationComponent state.point finish ∧
              IsCanonicalFirstAxisPrimitiveSplit p a finish := by
  obtain ⟨startThreshold, hstart⟩ :=
    exists_threshold_alternatingRegularState_actualSplitPrimitiveEndgame
      coefficient hWeil hdelta
  obtain ⟨primitiveThreshold, hprimitive⟩ :=
    exists_threshold_alternatingRegularState_actualSplitPrimitiveEndgame
      coefficient hWeil
        (delta := (1 : ℝ) / 4) (by norm_num)
  obtain ⟨squareThreshold, hsquare⟩ :=
    exists_threshold_threeQuarter_le_half_sub_one
  refine
    ⟨max (max startThreshold primitiveThreshold)
        (max squareThreshold 3), ?_⟩
  intro p hp _ a hA1 hA2 state q heigen hlarge
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
    alternatingRegularState_reaches_canonicalFirstAxisPrimitiveSplit_of_dispatchers
      p (by omega) a state
      (hstart p hpStart a hA1 hA2 state q heigen hlarge)
      (fun next v hnext hnextLarge =>
        hprimitive p hpPrimitive a hA1 hA2 next v hnext hnextLarge)
      (hsquare p hpSquare)

/-- The closed analytic cutoff suffices for the split assembly whenever the
initial exponent is at least `1/32` and the augmented coefficient is at most
`1032`. -/
theorem alternatingRegularState_reaches_canonicalFirstAxisPrimitiveSplit_of_analyticCutoff
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : (1 : ℝ) / 32 ≤ delta)
    (hcoefficient : coefficient + 40 ≤ 1032)
    (p : ℕ) (hp : GenMarkoff.General.Explicit.analyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (state : AlternatingRegularState a) (q : (ZMod p)ˣ)
    (heigen :
      traceAt a state.direction.fixed state.point.1 = splitTorusTrace q)
    (hlarge :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (q ^ 2)) :
    ∃ finish : SolutionSurface a,
      SameRotationComponent state.point finish ∧
        IsCanonicalFirstAxisPrimitiveSplit p a finish := by
  have hpTwo : p ≠ 2 := by
    have hpFive :=
      GenMarkoff.General.Explicit.five_le_analyticCutoff.trans hp
    omega
  exact
    alternatingRegularState_reaches_canonicalFirstAxisPrimitiveSplit_of_dispatchers
      p hpTwo a state
      (alternatingRegularState_actualSplitPrimitiveEndgame_of_analyticCutoff
        coefficient hWeil hdelta hcoefficient p hp
          a hA1 hA2 state q heigen hlarge)
      (fun next v hnext hnextLarge =>
        alternatingRegularState_actualSplitPrimitiveEndgame_of_analyticCutoff
          coefficient hWeil (delta := (1 : ℝ) / 4) (by norm_num)
            hcoefficient p hp a hA1 hA2 next v hnext hnextLarge)
      (threeQuarter_le_half_sub_one_of_analyticCutoff hp)

/-- The reasonable cutoff version of the canonical split assembly.  The
initial and return steps both use the divisor-moment primitive trace
inequality at exponent `1/4`. -/
theorem alternatingRegularState_reaches_canonicalFirstAxisPrimitiveSplit_of_reasonableCutoff
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : (1 : ℝ) / 4 ≤ delta)
    (hcoefficient : coefficient + 40 ≤ 1032)
    (p : ℕ)
    (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (state : AlternatingRegularState a) (q : (ZMod p)ˣ)
    (heigen :
      traceAt a state.direction.fixed state.point.1 = splitTorusTrace q)
    (hlarge :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (q ^ 2)) :
    ∃ finish : SolutionSurface a,
      SameRotationComponent state.point finish ∧
        IsCanonicalFirstAxisPrimitiveSplit p a finish := by
  have hpTwo : p ≠ 2 := by
    have hpFive :=
      GenMarkoff.General.Explicit.five_le_reasonableAnalyticCutoff.trans hp
    omega
  exact
    alternatingRegularState_reaches_canonicalFirstAxisPrimitiveSplit_of_dispatchers
      p hpTwo a state
      (alternatingRegularState_actualSplitPrimitiveEndgame_of_reasonableCutoff
        coefficient hWeil hdelta hcoefficient p hp
          a hA1 hA2 state q heigen hlarge)
      (fun next v hnext hnextLarge =>
        alternatingRegularState_actualSplitPrimitiveEndgame_of_reasonableCutoff
          coefficient hWeil (delta := (1 : ℝ) / 4) (by norm_num)
            hcoefficient p hp a hA1 hA2 next v hnext hnextLarge)
      (threeQuarter_le_half_sub_one_of_reasonableCutoff hp)

end

end GenMarkoff.General.Assembly
